//Vytenis Sakalinskas

class {:autocontracts} CarPark
{
    var weekend: bool;
    var carPark: set<nat>;
    var privatePark: set<nat>;
    var parkSize: nat;
    var privateParkSize: nat;
    var parkIndicator: nat;
    var privateParkIndicator: nat;
    var carsWithSubscriptions: set<nat>;

    constructor(regSize: nat, privateSize: nat)
    requires regSize - 5 > 0 && privateSize - 5 > 0 
    //the park is full when there are still 5 slots remaining
    ensures carPark == {} && privatePark == {} && carsWithSubscriptions == {} 
    //ensuring that parks are created empty
    {
        carPark, privatePark, carsWithSubscriptions := {}, {}, {};
        parkSize, privateParkSize := regSize - 5, privateSize - 5;
        weekend := false;
        parkIndicator, privateParkIndicator := 1, 2;
    }

    predicate Valid()
    {
        parkSize > 0 && privateParkSize > 0
        //ensuring that none of the sizes ever get changed
    }


    method enterCarPark(entry: nat) returns(res: bool)
    ensures entry in carPark || entry in privatePark ==> carPark == old(carPark) && privatePark == old(privatePark) ==> res == false
    //ensuring that the entry is not in either of the parks already
    ensures |carPark| < parkSize ==> |carPark| > old(|carPark|) ==> res == true
    //ensuring that we only allow a car in if there's a free space inside of the carPark
    ensures |carPark| >= parkSize ==> carPark == old(carPark) ==> res == false
    //ensuring that if the car park is full we do not change the carPark and return false
    {
        //checking if the car already exists in either of the parks
        if entry in carPark || entry in privatePark
        {
            print entry, " is already in the park.", "\n";
            res := false;
        }
        //checking if there's space for the cars to be added into and if so we perform set addition
        else if |carPark| < parkSize
        {
            var temp := {entry};
            carPark := carPark + temp;
            print entry, " has entered the regular park.", "\n";
            res := true;
        }
        //returning false if the carpark is full
        else
        {
            print "Regular park is full.", "\n";
            res := false;
        }
    }

    method leaveCarPark(entry: nat, park: nat) returns(res: bool)
    ensures park == 1 && entry in carPark ==> carPark < old(carPark) && res == true
    //ensuring that if the entry we're trying to remove does exist and it exists in the correct park it has been removed
    ensures park == 2 && entry in privatePark ==> privatePark < old(privatePark) && res == true
    //ensuring that if the entry we're trying to remove does exist and it exists in the correct park it has been removed
    ensures park == 1 && entry !in carPark ==> res == false ==> carPark == old(carPark)
    //ensuring that if the entry we're trying to remove doesn't exist we do not change the car park
    ensures park == 2 && entry !in privatePark ==> res == false ==> privatePark == old(privatePark)
    //ensuring that if the entry we're trying to remove doesn't exist we do not change the private park
    {
        //If the park to remove from is the regular park and the car is inside of the regualr park
        //Perform set subtraction and return true as the result
        if park == 1 && entry in carPark
        {
            carPark := carPark - {entry};
            print entry, " left the car Park.", "\n";
            res := true;
        }
        //If the park to remove from is the private park and the car is inside of the private park
        //Perform set subtraction and return true as the result
        else if park == 2 && entry in privatePark
        {
            privatePark := privatePark - {entry};
            print entry, " left the private Park.", "\n";
            res := true;
        }
        //If the car is not in the corresponding parks return false
        else
        {
            print "Car with this id is not parked here.", "\n";
            res := false;
        }
    }


    method enterReservedCarPark(entry: nat) returns(res: bool)
    ensures weekend == true ==> |privatePark| < privateParkSize && entry !in carPark ==> |privatePark| > old(|privatePark|)  ==> res == true
    //ensuring that during the weekend if the private park has slots and the car doesn't exist in the regular car park already we add it in 
    ensures weekend == true ==> |privatePark| >= privateParkSize && entry in carPark ==> res == false
    //ensuring that during the weekend if the private park has no slots or the car already exists in the regular car park that the car doesn't get added to the park
    ensures weekend == false && entry in carsWithSubscriptions && |privatePark| < privateParkSize ==> |privatePark| > old(|privatePark|) ==> entry !in privatePark && entry !in carPark ==> res == true
    //ensuring that if it's not the weekend, that the car has a subscription and that the park isn't full we add the car to the private park and return true
    ensures weekend == false ==> entry in carsWithSubscriptions ==> |privatePark| >= privateParkSize ==> privatePark == old(privatePark) ==> res == false
    //ensuring that if it's not the weekend, that the car has a subscription and that the park isn full we do not add the car to the private park and return false
    ensures weekend == false ==> entry !in carsWithSubscriptions ==> res == false
    //ensuring that if it's not the weekend and the car does not have a subscription we return false
    ensures weekend == false && entry in carsWithSubscriptions && |privatePark| < privateParkSize ==> entry in privatePark || entry in carPark ==> privatePark == old(privatePark) ==> res == false
    //ensuring that if it's not the weekend and the car does have a subscription and there are slots for cars and that the car does exist in a different park already we return false
    {
        //checking if the weekend boolean is active
        if !weekend
        {
            //checking if the car has subscribeed
            if entry in carsWithSubscriptions
            {
                //checking if there are spaces to place the car in
                if |privatePark| < privateParkSize
                {
                    if  entry in privatePark || entry in carPark
                    {
                        //if there are, use string addition to add the new car to the park
                        print entry, " already exists in a car park", "\n";
                        res := false;
                    }
                    else
                    {
                        privatePark := privatePark + {entry};
                        print entry, " has entered the private park.", "\n";
                        res := true;
                    }
                }
                //if there are no slots return false and return false
                else
                {
                    print entry, " did not enter. The private car park is full", "\n";
                    res := false;
                }
            }
            //if the car does not have a subscription return false
            else 
            {
                print entry, " tried to enter the private park without a subscription.", "\n";
                res := false;
            }
        }
        else
        {
            //if it's the weekend and the car isn't already in a car park, use set addition to add it to the park and return true
            if |privatePark| < privateParkSize && entry !in carPark
            {
                privatePark := privatePark + {entry};
                print entry, " has entered the private park.", "\n";
                res := true;
            }
            //if it's the weekend and the park is full return false
            else
            {
                print entry, " could not enter the park. The private park is full", "\n";
                res := false;
            }
        }
    }

    method makeSubscription(id: nat) returns(res: bool)
    ensures privateParkSize > |carsWithSubscriptions| ==> privateParkSize - |privatePark| == 0 ==> res == false && carsWithSubscriptions == old(carsWithSubscriptions)
    //ensures that if the privatePark is full and there are no more possible subscriptions that the carswithsubscriptions hasn't been changed
    ensures privateParkSize > |carsWithSubscriptions| ==> privateParkSize - |privatePark| != 0 ==> |carsWithSubscriptions| > old(|carsWithSubscriptions|) && id !in carsWithSubscriptions ==> res == true && |carsWithSubscriptions| > old(|carsWithSubscriptions|)
    //ensures that if the privatePark is not full and there are available subscriptions and that the car doesn't already have a subscription, that carsWithSubscriptions has been changed
    ensures privateParkSize > |carsWithSubscriptions| ==> privateParkSize - |privatePark| != 0 ==> id in carsWithSubscriptions ==> carsWithSubscriptions == old(carsWithSubscriptions) ==> res == false
    //ensures that if the car park has spaces and that there are subscriptions to give out but the car already is subscribed that a new subscription is not added to the set
    {
        //checking if there are still cars that can be added to the privatePark and if so we add a new entry
        if (privateParkSize - |privatePark| != 0)
        {
            if id !in carsWithSubscriptions
            {
                carsWithSubscriptions := carsWithSubscriptions + {id};
                print id, " has subscribed", "\n";
                res := true;
            }
            else
            {
                print id, " has already subscribed", "\n";
                res := false;
            }
        }
        //if there are no more cars that can be added we return false and change nothing
        else
        {
            print "Out of parking spaces. Can't subscribe to private parking.", "\n";
            res := false;
        }
    }

    method closeCarPark()
    ensures |carPark| > 0 ==> carPark == {}
    //ensuring that we cleared out the carPark if there was anything in it
    ensures |privatePark| > 0 ==> privatePark == {}
    //ensuring that we cleared out the privatePark if there was anything in it
    {
        //if the carPark is not empty, set it to an empty set
        if |carPark| > 0
        {
            carPark := {};
        }
        //if the privatePark is not empty, set it to an empty set
        if |privatePark| > 0 
        {
            privatePark := {};
        }
        print "Parks have been cleared: ", "\n";
    }

    method openReservedArea()
    ensures weekend == false ==> weekend == true
    //ensuring that if the weekend was false we set it to true
    {
        //if it isn't the weekend before the function was called, set weekend to true
        if weekend == false
        {
            weekend := true;
        }
        else 
        {
            print "It's already weekend.", "\n";
        }
    }

    method printParkingPlan()
    {
        //Used for visualising the program
        print "Regular park: ", carPark, " | Spaces remaining: ", parkSize - |carPark| ,"\n";
        print "Private park: ", privatePark, " | Spaces remaining: ", privateParkSize - |privatePark|, "\n";
    }

    method checkAvailability(parkToCheck: nat) returns(res: bool)
    ensures parkSize == old(parkSize) && privateParkSize == old(privateParkSize) && carPark == old(carPark) && privatePark == old(privatePark)
    //making sure that neither of the variables used in the operation are changed in any way
    ensures parkSize - |carPark| != 0 && parkToCheck == 1 ==> res == true
    ensures privateParkSize - |privatePark| != 0 && parkToCheck == 2 ==> res == true
    //making sure that if the amount of spaces available are more than 0 we return true
    ensures parkSize - |carPark| == 0 && parkToCheck == 1 ==> res == false
    ensures privateParkSize - |privatePark| == 0 && parkToCheck == 2 ==> res == false
    //making sure if that the amount of spaces available is 0 we return false
    {
        var tempPark: set<nat>;
        var tempSize: nat;
        //making the method applicable to multiple car parks by storing temp values of parks
        if parkToCheck == 1
        {
            tempPark := carPark;
            tempSize := parkSize;
        }
        else if parkToCheck == 2
        {
            tempPark := privatePark;
            tempSize := privateParkSize;
        }
        //checking if the park is full and if not, we return true
        if tempSize - |tempPark| != 0
        {
            print tempSize - |tempPark|, " spaces remaining.", "\n";
            return true;
        }
        //if it is full we return false
        else
        {
            print "Park is full", "\n";
            return false;
        }
    }
}

method Main()
{
    var park := new CarPark(10, 10);
    var e: bool;
    print "\n", "Testing: car being in the park already, adding cars when the park isn't full, adding cars when the park is full:", "\n";
    park.printParkingPlan();
    e := park.enterCarPark(10);
    e := park.enterCarPark(10);
    e := park.enterCarPark(11);
    e := park.enterCarPark(12);
    e := park.enterCarPark(13);
    e := park.enterCarPark(14);
    e := park.enterCarPark(15);
    park.printParkingPlan();

    print "\n", "Testing: the park having slots and subs to give, park being full, park being already subscribed", "\n";
    park.printParkingPlan();
    e := park.makeSubscription(16);
    e := park.makeSubscription(17);
    e := park.makeSubscription(17);
    e := park.makeSubscription(18);
    e := park.makeSubscription(19);
    e := park.makeSubscription(20);
    e := park.makeSubscription(21);
    e := park.makeSubscription(22);
    park.printParkingPlan();

    print "\n", "Testing: non-weekend enter when the car has a subscription, non-weekend enter when the car has no subscription, non-weekend enter when car has a subscription but no space, weekend when park has slots, weekend when park is full, making a subscription when the private parking is full", "\n";

    park.printParkingPlan();
    e := park.enterReservedCarPark(10);
    e := park.enterReservedCarPark(16);
    e := park.enterReservedCarPark(16);
    e := park.enterReservedCarPark(17);
    e := park.enterReservedCarPark(18);
    e := park.enterReservedCarPark(19);
    e := park.enterReservedCarPark(20);
    e := park.enterReservedCarPark(21);
    e := park.makeSubscription(22);
        park.printParkingPlan();

    print "\n", "Testing: removing car in carPark, car in privatePark, car does not exist in either car park:", "\n";
    park.printParkingPlan();
    e := park.leaveCarPark(10, 1);
    e := park.leaveCarPark(10, 2);
    e := park.leaveCarPark(10, 3);
    e := park.leaveCarPark(16, 2);
    park.printParkingPlan();
    e := park.checkAvailability(1);
    print "\n", "Testing closing the park and starting weekend.", "\n";
    park.closeCarPark();

    park.openReservedArea();

    print "\n", "Testing entering the park without a subscription on the weekend", "\n";
    e := park.enterReservedCarPark(10);
}