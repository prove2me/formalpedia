-- Prove2me | solution 1 for syracuse_descends_range_1707054_1709054
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:27:06.294631+00:00
-- url     : https://prove2.me/submissions/29e77da2-eed9-4ba8-bf6a-f7e045821af1

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B2883613 : Blo 1707054 2883613 := bbase (se 3 (by rfl) ⟨540677, by rfl⟩ : syracuseStep 2883613 = 1081355) (by norm_num)
theorem B3842117 : Blo 1707054 3842117 := bbase (se 4 (by rfl) ⟨360198, by rfl⟩ : syracuseStep 3842117 = 720397) (by norm_num)
theorem B5767253 : Blo 1707054 5767253 := bbase (se 8 (by rfl) ⟨33792, by rfl⟩ : syracuseStep 5767253 = 67585) (by norm_num)
theorem B3244141 : Blo 1707054 3244141 := bbase (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) (by norm_num)
theorem B2162801 : Blo 1707054 2162801 := bbase (se 2 (by rfl) ⟨811050, by rfl⟩ : syracuseStep 2162801 = 1622101) (by norm_num)
theorem B2736245 : Blo 1707054 2736245 := bbase (se 5 (by rfl) ⟨128261, by rfl⟩ : syracuseStep 2736245 = 256523) (by norm_num)
theorem B2883701 : Blo 1707054 2883701 := bbase (se 5 (by rfl) ⟨135173, by rfl⟩ : syracuseStep 2883701 = 270347) (by norm_num)
theorem B4325501 : Blo 1707054 4325501 := bbase (se 3 (by rfl) ⟨811031, by rfl⟩ : syracuseStep 4325501 = 1622063) (by norm_num)
theorem B3842189 : Blo 1707054 3842189 := bbase (se 3 (by rfl) ⟨720410, by rfl⟩ : syracuseStep 3842189 = 1440821) (by norm_num)
theorem B9863317 : Blo 1707054 9863317 := bbase (se 6 (by rfl) ⟨231171, by rfl⟩ : syracuseStep 9863317 = 462343) (by norm_num)
theorem B2162857 : Blo 1707054 2162857 := bbase (se 2 (by rfl) ⟨811071, by rfl⟩ : syracuseStep 2162857 = 1622143) (by norm_num)
theorem B2433197 : Blo 1707054 2433197 := bbase (se 3 (by rfl) ⟨456224, by rfl⟩ : syracuseStep 2433197 = 912449) (by norm_num)
theorem B3842261 : Blo 1707054 3842261 := bbase (se 7 (by rfl) ⟨45026, by rfl⟩ : syracuseStep 3842261 = 90053) (by norm_num)
theorem B6004949 : Blo 1707054 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B2883829 : Blo 1707054 2883829 := bbase (se 5 (by rfl) ⟨135179, by rfl⟩ : syracuseStep 2883829 = 270359) (by norm_num)
theorem B4104445 : Blo 1707054 4104445 := bbase (se 3 (by rfl) ⟨769583, by rfl⟩ : syracuseStep 4104445 = 1539167) (by norm_num)
theorem B2433277 : Blo 1707054 2433277 := bbase (se 3 (by rfl) ⟨456239, by rfl⟩ : syracuseStep 2433277 = 912479) (by norm_num)
theorem B4382981 : Blo 1707054 4382981 := bbase (se 4 (by rfl) ⟨410904, by rfl⟩ : syracuseStep 4382981 = 821809) (by norm_num)
theorem B2162953 : Blo 1707054 2162953 := bbase (se 2 (by rfl) ⟨811107, by rfl⟩ : syracuseStep 2162953 = 1622215) (by norm_num)
theorem B3842333 : Blo 1707054 3842333 := bbase (se 3 (by rfl) ⟨720437, by rfl⟩ : syracuseStep 3842333 = 1440875) (by norm_num)
theorem B2883917 : Blo 1707054 2883917 := bbase (se 3 (by rfl) ⟨540734, by rfl⟩ : syracuseStep 2883917 = 1081469) (by norm_num)
theorem B6570341 : Blo 1707054 6570341 := bbase (se 4 (by rfl) ⟨615969, by rfl⟩ : syracuseStep 6570341 = 1231939) (by norm_num)
theorem B3842405 : Blo 1707054 3842405 := bbase (se 4 (by rfl) ⟨360225, by rfl⟩ : syracuseStep 3842405 = 720451) (by norm_num)
theorem B2433397 : Blo 1707054 2433397 := bbase (se 5 (by rfl) ⟨114065, by rfl⟩ : syracuseStep 2433397 = 228131) (by norm_num)
theorem B4104589 : Blo 1707054 4104589 := bbase (se 3 (by rfl) ⟨769610, by rfl⟩ : syracuseStep 4104589 = 1539221) (by norm_num)
theorem B3244445 : Blo 1707054 3244445 := bbase (se 3 (by rfl) ⟨608333, by rfl⟩ : syracuseStep 3244445 = 1216667) (by norm_num)
theorem B3842477 : Blo 1707054 3842477 := bbase (se 3 (by rfl) ⟨720464, by rfl⟩ : syracuseStep 3842477 = 1440929) (by norm_num)
theorem B4325845 : Blo 1707054 4325845 := bbase (se 7 (by rfl) ⟨50693, by rfl⟩ : syracuseStep 4325845 = 101387) (by norm_num)
theorem B3842549 : Blo 1707054 3842549 := bbase (se 5 (by rfl) ⟨180119, by rfl⟩ : syracuseStep 3842549 = 360239) (by norm_num)
theorem B5767685 : Blo 1707054 5767685 := bbase (se 4 (by rfl) ⟨540720, by rfl⟩ : syracuseStep 5767685 = 1081441) (by norm_num)
theorem B8651285 : Blo 1707054 8651285 := bbase (se 6 (by rfl) ⟨202764, by rfl⟩ : syracuseStep 8651285 = 405529) (by norm_num)
theorem B7791157 : Blo 1707054 7791157 := bbase (se 5 (by rfl) ⟨365210, by rfl⟩ : syracuseStep 7791157 = 730421) (by norm_num)
theorem B3842621 : Blo 1707054 3842621 := bbase (se 3 (by rfl) ⟨720491, by rfl⟩ : syracuseStep 3842621 = 1440983) (by norm_num)
theorem B8208965 : Blo 1707054 8208965 := bbase (se 4 (by rfl) ⟨769590, by rfl⟩ : syracuseStep 8208965 = 1539181) (by norm_num)
theorem B4325957 : Blo 1707054 4325957 := bbase (se 4 (by rfl) ⟨405558, by rfl⟩ : syracuseStep 4325957 = 811117) (by norm_num)
theorem B39428693 : Blo 1707054 39428693 := bbase (se 8 (by rfl) ⟨231027, by rfl⟩ : syracuseStep 39428693 = 462055) (by norm_num)
theorem B6488693 : Blo 1707054 6488693 := bbase (se 5 (by rfl) ⟨304157, by rfl⟩ : syracuseStep 6488693 = 608315) (by norm_num)
theorem B3842693 : Blo 1707054 3842693 := bbase (se 4 (by rfl) ⟨360252, by rfl⟩ : syracuseStep 3842693 = 720505) (by norm_num)
theorem B3842765 : Blo 1707054 3842765 := bbase (se 3 (by rfl) ⟨720518, by rfl⟩ : syracuseStep 3842765 = 1441037) (by norm_num)
theorem B9855701 : Blo 1707054 9855701 := bbase (se 7 (by rfl) ⟨115496, by rfl⟩ : syracuseStep 9855701 = 230993) (by norm_num)
theorem B10535669 : Blo 1707054 10535669 := bbase (se 5 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 10535669 = 987719) (by norm_num)
theorem B3842837 : Blo 1707054 3842837 := bbase (se 6 (by rfl) ⟨90066, by rfl⟩ : syracuseStep 3842837 = 180133) (by norm_num)
theorem B1975105 : Blo 1707054 1975105 := bbase (se 2 (by rfl) ⟨740664, by rfl⟩ : syracuseStep 1975105 = 1481329) (by norm_num)
theorem B3842909 : Blo 1707054 3842909 := bbase (se 3 (by rfl) ⟨720545, by rfl⟩ : syracuseStep 3842909 = 1441091) (by norm_num)
theorem B6488981 : Blo 1707054 6488981 := bbase (se 6 (by rfl) ⟨152085, by rfl⟩ : syracuseStep 6488981 = 304171) (by norm_num)
theorem B3842981 : Blo 1707054 3842981 := bbase (se 4 (by rfl) ⟨360279, by rfl⟩ : syracuseStep 3842981 = 720559) (by norm_num)
theorem B8643509 : Blo 1707054 8643509 := bbase (se 5 (by rfl) ⟨405164, by rfl⟩ : syracuseStep 8643509 = 810329) (by norm_num)
theorem B3843053 : Blo 1707054 3843053 := bbase (se 3 (by rfl) ⟨720572, by rfl⟩ : syracuseStep 3843053 = 1441145) (by norm_num)
theorem B4105205 : Blo 1707054 4105205 := bbase (se 5 (by rfl) ⟨192431, by rfl⟩ : syracuseStep 4105205 = 384863) (by norm_num)
theorem B3843125 : Blo 1707054 3843125 := bbase (se 5 (by rfl) ⟨180146, by rfl⟩ : syracuseStep 3843125 = 360293) (by norm_num)
theorem B4932677 : Blo 1707054 4932677 := bbase (se 4 (by rfl) ⟨462438, by rfl⟩ : syracuseStep 4932677 = 924877) (by norm_num)
theorem B3646549 : Blo 1707054 3646549 := bbase (se 8 (by rfl) ⟨21366, by rfl⟩ : syracuseStep 3646549 = 42733) (by norm_num)
theorem B3843197 : Blo 1707054 3843197 := bbase (se 3 (by rfl) ⟨720599, by rfl⟩ : syracuseStep 3843197 = 1441199) (by norm_num)
theorem B3843269 : Blo 1707054 3843269 := bbase (se 4 (by rfl) ⟨360306, by rfl⟩ : syracuseStep 3843269 = 720613) (by norm_num)
theorem B5842165 : Blo 1707054 5842165 := bbase (se 5 (by rfl) ⟨273851, by rfl⟩ : syracuseStep 5842165 = 547703) (by norm_num)
theorem B3843341 : Blo 1707054 3843341 := bbase (se 3 (by rfl) ⟨720626, by rfl⟩ : syracuseStep 3843341 = 1441253) (by norm_num)
theorem B4105541 : Blo 1707054 4105541 := bbase (se 4 (by rfl) ⟨384894, by rfl⟩ : syracuseStep 4105541 = 769789) (by norm_num)
theorem B3843413 : Blo 1707054 3843413 := bbase (se 12 (by rfl) ⟨1407, by rfl⟩ : syracuseStep 3843413 = 2815) (by norm_num)
theorem B5473669 : Blo 1707054 5473669 := bbase (se 4 (by rfl) ⟨513156, by rfl⟩ : syracuseStep 5473669 = 1026313) (by norm_num)
theorem B3843485 : Blo 1707054 3843485 := bbase (se 3 (by rfl) ⟨720653, by rfl⟩ : syracuseStep 3843485 = 1441307) (by norm_num)
theorem B4105637 : Blo 1707054 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B4056493 : Blo 1707054 4056493 := bbase (se 3 (by rfl) ⟨760592, by rfl⟩ : syracuseStep 4056493 = 1521185) (by norm_num)
theorem B3843557 : Blo 1707054 3843557 := bbase (se 4 (by rfl) ⟨360333, by rfl⟩ : syracuseStep 3843557 = 720667) (by norm_num)
theorem B1754605 : Blo 1707054 1754605 := bbase (se 3 (by rfl) ⟨328988, by rfl⟩ : syracuseStep 1754605 = 657977) (by norm_num)
theorem B3843629 : Blo 1707054 3843629 := bbase (se 3 (by rfl) ⟨720680, by rfl⟩ : syracuseStep 3843629 = 1441361) (by norm_num)
theorem B3647045 : Blo 1707054 3647045 := bbase (se 4 (by rfl) ⟨341910, by rfl⟩ : syracuseStep 3647045 = 683821) (by norm_num)
theorem B4105829 : Blo 1707054 4105829 := bbase (se 4 (by rfl) ⟨384921, by rfl⟩ : syracuseStep 4105829 = 769843) (by norm_num)
theorem B3843701 : Blo 1707054 3843701 := bbase (se 5 (by rfl) ⟨180173, by rfl⟩ : syracuseStep 3843701 = 360347) (by norm_num)
theorem B4384373 : Blo 1707054 4384373 := bbase (se 5 (by rfl) ⟨205517, by rfl⟩ : syracuseStep 4384373 = 411035) (by norm_num)
theorem B3843773 : Blo 1707054 3843773 := bbase (se 3 (by rfl) ⟨720707, by rfl⟩ : syracuseStep 3843773 = 1441415) (by norm_num)
theorem B24610517 : Blo 1707054 24610517 := bbase (se 7 (by rfl) ⟨288404, by rfl⟩ : syracuseStep 24610517 = 576809) (by norm_num)
theorem B3843845 : Blo 1707054 3843845 := bbase (se 4 (by rfl) ⟨360360, by rfl⟩ : syracuseStep 3843845 = 720721) (by norm_num)
theorem B3843917 : Blo 1707054 3843917 := bbase (se 3 (by rfl) ⟨720734, by rfl⟩ : syracuseStep 3843917 = 1441469) (by norm_num)
theorem B3843989 : Blo 1707054 3843989 := bbase (se 6 (by rfl) ⟨90093, by rfl⟩ : syracuseStep 3843989 = 180187) (by norm_num)
theorem B3844061 : Blo 1707054 3844061 := bbase (se 3 (by rfl) ⟨720761, by rfl⟩ : syracuseStep 3844061 = 1441523) (by norm_num)
theorem B1730557 : Blo 1707054 1730557 := bbase (se 3 (by rfl) ⟨324479, by rfl⟩ : syracuseStep 1730557 = 648959) (by norm_num)
theorem B3844133 : Blo 1707054 3844133 := bbase (se 4 (by rfl) ⟨360387, by rfl⟩ : syracuseStep 3844133 = 720775) (by norm_num)
theorem B3844205 : Blo 1707054 3844205 := bbase (se 3 (by rfl) ⟨720788, by rfl⟩ : syracuseStep 3844205 = 1441577) (by norm_num)
theorem B6924437 : Blo 1707054 6924437 := bbase (se 6 (by rfl) ⟨162291, by rfl⟩ : syracuseStep 6924437 = 324583) (by norm_num)
theorem B3844277 : Blo 1707054 3844277 := bbase (se 5 (by rfl) ⟨180200, by rfl⟩ : syracuseStep 3844277 = 360401) (by norm_num)
theorem B8644805 : Blo 1707054 8644805 := bbase (se 4 (by rfl) ⟨810450, by rfl⟩ : syracuseStep 8644805 = 1620901) (by norm_num)
theorem B3844349 : Blo 1707054 3844349 := bbase (se 3 (by rfl) ⟨720815, by rfl⟩ : syracuseStep 3844349 = 1441631) (by norm_num)
theorem B3746117 : Blo 1707054 3746117 := bbase (se 4 (by rfl) ⟨351198, by rfl⟩ : syracuseStep 3746117 = 702397) (by norm_num)
theorem B3844421 : Blo 1707054 3844421 := bbase (se 4 (by rfl) ⟨360414, by rfl⟩ : syracuseStep 3844421 = 720829) (by norm_num)
theorem B1755517 : Blo 1707054 1755517 := bbase (se 3 (by rfl) ⟨329159, by rfl⟩ : syracuseStep 1755517 = 658319) (by norm_num)
theorem B3844493 : Blo 1707054 3844493 := bbase (se 3 (by rfl) ⟨720842, by rfl⟩ : syracuseStep 3844493 = 1441685) (by norm_num)
theorem B3647909 : Blo 1707054 3647909 := bbase (se 4 (by rfl) ⟨341991, by rfl⟩ : syracuseStep 3647909 = 683983) (by norm_num)
theorem B3893717 : Blo 1707054 3893717 := bbase (se 7 (by rfl) ⟨45629, by rfl⟩ : syracuseStep 3893717 = 91259) (by norm_num)
theorem B6482389 : Blo 1707054 6482389 := bbase (se 7 (by rfl) ⟨75965, by rfl⟩ : syracuseStep 6482389 = 151931) (by norm_num)
theorem B3844565 : Blo 1707054 3844565 := bbase (se 7 (by rfl) ⟨45053, by rfl⟩ : syracuseStep 3844565 = 90107) (by norm_num)
theorem B3844637 : Blo 1707054 3844637 := bbase (se 3 (by rfl) ⟨720869, by rfl⟩ : syracuseStep 3844637 = 1441739) (by norm_num)
theorem B3648053 : Blo 1707054 3648053 := bbase (se 5 (by rfl) ⟨171002, by rfl⟩ : syracuseStep 3648053 = 342005) (by norm_num)
theorem B7293509 : Blo 1707054 7293509 := bbase (se 4 (by rfl) ⟨683766, by rfl⟩ : syracuseStep 7293509 = 1367533) (by norm_num)
theorem B5761637 : Blo 1707054 5761637 := bbase (se 4 (by rfl) ⟨540153, by rfl⟩ : syracuseStep 5761637 = 1080307) (by norm_num)
theorem B3844709 : Blo 1707054 3844709 := bbase (se 4 (by rfl) ⟨360441, by rfl⟩ : syracuseStep 3844709 = 720883) (by norm_num)
theorem B3844781 : Blo 1707054 3844781 := bbase (se 3 (by rfl) ⟨720896, by rfl⟩ : syracuseStep 3844781 = 1441793) (by norm_num)
theorem B14592757 : Blo 1707054 14592757 := bbase (se 5 (by rfl) ⟨684035, by rfl⟩ : syracuseStep 14592757 = 1368071) (by norm_num)
theorem B3844853 : Blo 1707054 3844853 := bbase (se 5 (by rfl) ⟨180227, by rfl⟩ : syracuseStep 3844853 = 360455) (by norm_num)
theorem B6482693 : Blo 1707054 6482693 := bbase (se 4 (by rfl) ⟨607752, by rfl⟩ : syracuseStep 6482693 = 1215505) (by norm_num)
theorem B2190109 : Blo 1707054 2190109 := bbase (se 3 (by rfl) ⟨410645, by rfl⟩ : syracuseStep 2190109 = 821291) (by norm_num)
theorem B1731385 : Blo 1707054 1731385 := bbase (se 2 (by rfl) ⟨649269, by rfl⟩ : syracuseStep 1731385 = 1298539) (by norm_num)
theorem B3844925 : Blo 1707054 3844925 := bbase (se 3 (by rfl) ⟨720923, by rfl⟩ : syracuseStep 3844925 = 1441847) (by norm_num)
theorem B2050925 : Blo 1707054 2050925 := bbase (se 3 (by rfl) ⟨384548, by rfl⟩ : syracuseStep 2050925 = 769097) (by norm_num)
theorem B3844997 : Blo 1707054 3844997 := bbase (se 4 (by rfl) ⟨360468, by rfl⟩ : syracuseStep 3844997 = 720937) (by norm_num)
theorem B2960285 : Blo 1707054 2960285 := bbase (se 3 (by rfl) ⟨555053, by rfl⟩ : syracuseStep 2960285 = 1110107) (by norm_num)
theorem B3845069 : Blo 1707054 3845069 := bbase (se 3 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 3845069 = 1441901) (by norm_num)
theorem B5762069 : Blo 1707054 5762069 := bbase (se 6 (by rfl) ⟨135048, by rfl⟩ : syracuseStep 5762069 = 270097) (by norm_num)
theorem B3845141 : Blo 1707054 3845141 := bbase (se 6 (by rfl) ⟨90120, by rfl⟩ : syracuseStep 3845141 = 180241) (by norm_num)
theorem B3894301 : Blo 1707054 3894301 := bbase (se 3 (by rfl) ⟨730181, by rfl⟩ : syracuseStep 3894301 = 1460363) (by norm_num)
theorem B3845213 : Blo 1707054 3845213 := bbase (se 3 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 3845213 = 1441955) (by norm_num)
theorem B3845285 : Blo 1707054 3845285 := bbase (se 4 (by rfl) ⟨360495, by rfl⟩ : syracuseStep 3845285 = 720991) (by norm_num)
theorem B4861109 : Blo 1707054 4861109 := bbase (se 5 (by rfl) ⟨227864, by rfl⟩ : syracuseStep 4861109 = 455729) (by norm_num)
theorem B2051281 : Blo 1707054 2051281 := bbase (se 2 (by rfl) ⟨769230, by rfl⟩ : syracuseStep 2051281 = 1538461) (by norm_num)
theorem B3845357 : Blo 1707054 3845357 := bbase (se 3 (by rfl) ⟨721004, by rfl⟩ : syracuseStep 3845357 = 1442009) (by norm_num)
theorem B3648797 : Blo 1707054 3648797 := bbase (se 3 (by rfl) ⟨684149, by rfl⟩ : syracuseStep 3648797 = 1368299) (by norm_num)
theorem B6925637 : Blo 1707054 6925637 := bbase (se 4 (by rfl) ⟨649278, by rfl⟩ : syracuseStep 6925637 = 1298557) (by norm_num)
theorem B2051473 : Blo 1707054 2051473 := bbase (se 2 (by rfl) ⟨769302, by rfl⟩ : syracuseStep 2051473 = 1538605) (by norm_num)
theorem B10390933 : Blo 1707054 10390933 := bbase (se 6 (by rfl) ⟨243537, by rfl⟩ : syracuseStep 10390933 = 487075) (by norm_num)
theorem B5762501 : Blo 1707054 5762501 := bbase (se 4 (by rfl) ⟨540234, by rfl⟩ : syracuseStep 5762501 = 1080469) (by norm_num)
theorem B1920469 : Blo 1707054 1920469 := bbase (se 7 (by rfl) ⟨22505, by rfl⟩ : syracuseStep 1920469 = 45011) (by norm_num)
theorem B8646101 : Blo 1707054 8646101 := bbase (se 7 (by rfl) ⟨101321, by rfl⟩ : syracuseStep 8646101 = 202643) (by norm_num)
theorem B1920505 : Blo 1707054 1920505 := bbase (se 2 (by rfl) ⟨720189, by rfl⟩ : syracuseStep 1920505 = 1440379) (by norm_num)
theorem B1920541 : Blo 1707054 1920541 := bbase (se 3 (by rfl) ⟨360101, by rfl⟩ : syracuseStep 1920541 = 720203) (by norm_num)
theorem B2051617 : Blo 1707054 2051617 := bbase (se 2 (by rfl) ⟨769356, by rfl⟩ : syracuseStep 2051617 = 1538713) (by norm_num)
theorem B1920577 : Blo 1707054 1920577 := bbase (se 2 (by rfl) ⟨720216, by rfl⟩ : syracuseStep 1920577 = 1440433) (by norm_num)
theorem B1920613 : Blo 1707054 1920613 := bbase (se 4 (by rfl) ⟨180057, by rfl⟩ : syracuseStep 1920613 = 360115) (by norm_num)
theorem B1920649 : Blo 1707054 1920649 := bbase (se 2 (by rfl) ⟨720243, by rfl⟩ : syracuseStep 1920649 = 1440487) (by norm_num)
theorem B8212117 : Blo 1707054 8212117 := bbase (se 6 (by rfl) ⟨192471, by rfl⟩ : syracuseStep 8212117 = 384943) (by norm_num)
theorem B1920685 : Blo 1707054 1920685 := bbase (se 3 (by rfl) ⟨360128, by rfl⟩ : syracuseStep 1920685 = 720257) (by norm_num)
theorem B1920721 : Blo 1707054 1920721 := bbase (se 2 (by rfl) ⟨720270, by rfl⟩ : syracuseStep 1920721 = 1440541) (by norm_num)
theorem B1920757 : Blo 1707054 1920757 := bbase (se 5 (by rfl) ⟨90035, by rfl⟩ : syracuseStep 1920757 = 180071) (by norm_num)
theorem B1920793 : Blo 1707054 1920793 := bbase (se 2 (by rfl) ⟨720297, by rfl⟩ : syracuseStep 1920793 = 1440595) (by norm_num)
theorem B2772773 : Blo 1707054 2772773 := bbase (se 4 (by rfl) ⟨259947, by rfl⟩ : syracuseStep 2772773 = 519895) (by norm_num)
theorem B1920829 : Blo 1707054 1920829 := bbase (se 3 (by rfl) ⟨360155, by rfl⟩ : syracuseStep 1920829 = 720311) (by norm_num)
theorem B19459925 : Blo 1707054 19459925 := bbase (se 9 (by rfl) ⟨57011, by rfl⟩ : syracuseStep 19459925 = 114023) (by norm_num)
theorem B1920865 : Blo 1707054 1920865 := bbase (se 2 (by rfl) ⟨720324, by rfl⟩ : syracuseStep 1920865 = 1440649) (by norm_num)
theorem B5762933 : Blo 1707054 5762933 := bbase (se 5 (by rfl) ⟨270137, by rfl⟩ : syracuseStep 5762933 = 540275) (by norm_num)
theorem B1920901 : Blo 1707054 1920901 := bbase (se 4 (by rfl) ⟨180084, by rfl⟩ : syracuseStep 1920901 = 360169) (by norm_num)
theorem B1920937 : Blo 1707054 1920937 := bbase (se 2 (by rfl) ⟨720351, by rfl⟩ : syracuseStep 1920937 = 1440703) (by norm_num)
theorem B1920973 : Blo 1707054 1920973 := bbase (se 3 (by rfl) ⟨360182, by rfl⟩ : syracuseStep 1920973 = 720365) (by norm_num)
theorem B1921009 : Blo 1707054 1921009 := bbase (se 2 (by rfl) ⟨720378, by rfl⟩ : syracuseStep 1921009 = 1440757) (by norm_num)
theorem B3649549 : Blo 1707054 3649549 := bbase (se 3 (by rfl) ⟨684290, by rfl⟩ : syracuseStep 3649549 = 1368581) (by norm_num)
theorem B1921045 : Blo 1707054 1921045 := bbase (se 6 (by rfl) ⟨45024, by rfl⟩ : syracuseStep 1921045 = 90049) (by norm_num)
theorem B4321309 : Blo 1707054 4321309 := bbase (se 3 (by rfl) ⟨810245, by rfl⟩ : syracuseStep 4321309 = 1620491) (by norm_num)
theorem B1921081 : Blo 1707054 1921081 := bbase (se 2 (by rfl) ⟨720405, by rfl⟩ : syracuseStep 1921081 = 1440811) (by norm_num)
theorem B3461213 : Blo 1707054 3461213 := bbase (se 3 (by rfl) ⟨648977, by rfl⟩ : syracuseStep 3461213 = 1297955) (by norm_num)
theorem B1921117 : Blo 1707054 1921117 := bbase (se 3 (by rfl) ⟨360209, by rfl⟩ : syracuseStep 1921117 = 720419) (by norm_num)
theorem B1921153 : Blo 1707054 1921153 := bbase (se 2 (by rfl) ⟨720432, by rfl⟩ : syracuseStep 1921153 = 1440865) (by norm_num)
theorem B4321421 : Blo 1707054 4321421 := bbase (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) (by norm_num)
theorem B3649693 : Blo 1707054 3649693 := bbase (se 3 (by rfl) ⟨684317, by rfl⟩ : syracuseStep 3649693 = 1368635) (by norm_num)
theorem B1921189 : Blo 1707054 1921189 := bbase (se 4 (by rfl) ⟨180111, by rfl⟩ : syracuseStep 1921189 = 360223) (by norm_num)
theorem B1921225 : Blo 1707054 1921225 := bbase (se 2 (by rfl) ⟨720459, by rfl⟩ : syracuseStep 1921225 = 1440919) (by norm_num)
theorem B1822933 : Blo 1707054 1822933 := bbase (se 7 (by rfl) ⟨21362, by rfl⟩ : syracuseStep 1822933 = 42725) (by norm_num)
theorem B1921261 : Blo 1707054 1921261 := bbase (se 3 (by rfl) ⟨360236, by rfl⟩ : syracuseStep 1921261 = 720473) (by norm_num)
theorem B4616453 : Blo 1707054 4616453 := bbase (se 4 (by rfl) ⟨432792, by rfl⟩ : syracuseStep 4616453 = 865585) (by norm_num)
theorem B1921297 : Blo 1707054 1921297 := bbase (se 2 (by rfl) ⟨720486, by rfl⟩ : syracuseStep 1921297 = 1440973) (by norm_num)
theorem B5763365 : Blo 1707054 5763365 := bbase (se 4 (by rfl) ⟨540315, by rfl⟩ : syracuseStep 5763365 = 1080631) (by norm_num)
theorem B1921333 : Blo 1707054 1921333 := bbase (se 5 (by rfl) ⟨90062, by rfl⟩ : syracuseStep 1921333 = 180125) (by norm_num)
theorem B7295285 : Blo 1707054 7295285 := bbase (se 5 (by rfl) ⟨341966, by rfl⟩ : syracuseStep 7295285 = 683933) (by norm_num)
theorem B4321613 : Blo 1707054 4321613 := bbase (se 3 (by rfl) ⟨810302, by rfl⟩ : syracuseStep 4321613 = 1620605) (by norm_num)
theorem B7016789 : Blo 1707054 7016789 := bbase (se 10 (by rfl) ⟨10278, by rfl⟩ : syracuseStep 7016789 = 20557) (by norm_num)
theorem B1921369 : Blo 1707054 1921369 := bbase (se 2 (by rfl) ⟨720513, by rfl⟩ : syracuseStep 1921369 = 1441027) (by norm_num)
theorem B7786853 : Blo 1707054 7786853 := bbase (se 4 (by rfl) ⟨730017, by rfl⟩ : syracuseStep 7786853 = 1460035) (by norm_num)
theorem B1921405 : Blo 1707054 1921405 := bbase (se 3 (by rfl) ⟨360263, by rfl⟩ : syracuseStep 1921405 = 720527) (by norm_num)
theorem B1921441 : Blo 1707054 1921441 := bbase (se 2 (by rfl) ⟨720540, by rfl⟩ : syracuseStep 1921441 = 1441081) (by norm_num)
theorem B3699133 : Blo 1707054 3699133 := bbase (se 3 (by rfl) ⟨693587, by rfl⟩ : syracuseStep 3699133 = 1387175) (by norm_num)
theorem B1921477 : Blo 1707054 1921477 := bbase (se 4 (by rfl) ⟨180138, by rfl⟩ : syracuseStep 1921477 = 360277) (by norm_num)
theorem B1921513 : Blo 1707054 1921513 := bbase (se 2 (by rfl) ⟨720567, by rfl⟩ : syracuseStep 1921513 = 1441135) (by norm_num)
theorem B1921549 : Blo 1707054 1921549 := bbase (se 3 (by rfl) ⟨360290, by rfl⟩ : syracuseStep 1921549 = 720581) (by norm_num)
theorem B18469397 : Blo 1707054 18469397 := bbase (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) (by norm_num)
theorem B3650069 : Blo 1707054 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B1921585 : Blo 1707054 1921585 := bbase (se 2 (by rfl) ⟨720594, by rfl⟩ : syracuseStep 1921585 = 1441189) (by norm_num)
theorem B3076661 : Blo 1707054 3076661 := bbase (se 5 (by rfl) ⟨144218, by rfl⟩ : syracuseStep 3076661 = 288437) (by norm_num)
theorem B1823305 : Blo 1707054 1823305 := bbase (se 2 (by rfl) ⟨683739, by rfl⟩ : syracuseStep 1823305 = 1367479) (by norm_num)
theorem B2560589 : Blo 1707054 2560589 := bbase (se 3 (by rfl) ⟨480110, by rfl⟩ : syracuseStep 2560589 = 960221) (by norm_num)
theorem B1921621 : Blo 1707054 1921621 := bbase (se 8 (by rfl) ⟨11259, by rfl⟩ : syracuseStep 1921621 = 22519) (by norm_num)
theorem B2560613 : Blo 1707054 2560613 := bbase (se 4 (by rfl) ⟨240057, by rfl⟩ : syracuseStep 2560613 = 480115) (by norm_num)
theorem B1921657 : Blo 1707054 1921657 := bbase (se 2 (by rfl) ⟨720621, by rfl⟩ : syracuseStep 1921657 = 1441243) (by norm_num)
theorem B2560637 : Blo 1707054 2560637 := bbase (se 3 (by rfl) ⟨480119, by rfl⟩ : syracuseStep 2560637 = 960239) (by norm_num)
theorem B2560661 : Blo 1707054 2560661 := bbase (se 6 (by rfl) ⟨60015, by rfl⟩ : syracuseStep 2560661 = 120031) (by norm_num)
theorem B16642709 : Blo 1707054 16642709 := bbase (se 6 (by rfl) ⟨390063, by rfl⟩ : syracuseStep 16642709 = 780127) (by norm_num)
theorem B1921693 : Blo 1707054 1921693 := bbase (se 3 (by rfl) ⟨360317, by rfl⟩ : syracuseStep 1921693 = 720635) (by norm_num)
theorem B4321957 : Blo 1707054 4321957 := bbase (se 4 (by rfl) ⟨405183, by rfl⟩ : syracuseStep 4321957 = 810367) (by norm_num)
theorem B2560685 : Blo 1707054 2560685 := bbase (se 3 (by rfl) ⟨480128, by rfl⟩ : syracuseStep 2560685 = 960257) (by norm_num)
theorem B14594741 : Blo 1707054 14594741 := bbase (se 5 (by rfl) ⟨684128, by rfl⟩ : syracuseStep 14594741 = 1368257) (by norm_num)
theorem B6927029 : Blo 1707054 6927029 := bbase (se 5 (by rfl) ⟨324704, by rfl⟩ : syracuseStep 6927029 = 649409) (by norm_num)
theorem B1921729 : Blo 1707054 1921729 := bbase (se 2 (by rfl) ⟨720648, by rfl⟩ : syracuseStep 1921729 = 1441297) (by norm_num)
theorem B2560709 : Blo 1707054 2560709 := bbase (se 4 (by rfl) ⟨240066, by rfl⟩ : syracuseStep 2560709 = 480133) (by norm_num)
theorem B5763797 : Blo 1707054 5763797 := bbase (se 7 (by rfl) ⟨67544, by rfl⟩ : syracuseStep 5763797 = 135089) (by norm_num)
theorem B2560733 : Blo 1707054 2560733 := bbase (se 3 (by rfl) ⟨480137, by rfl⟩ : syracuseStep 2560733 = 960275) (by norm_num)
theorem B4862693 : Blo 1707054 4862693 := bbase (se 4 (by rfl) ⟨455877, by rfl⟩ : syracuseStep 4862693 = 911755) (by norm_num)
theorem B8647397 : Blo 1707054 8647397 := bbase (se 4 (by rfl) ⟨810693, by rfl⟩ : syracuseStep 8647397 = 1621387) (by norm_num)
theorem B1921765 : Blo 1707054 1921765 := bbase (se 4 (by rfl) ⟨180165, by rfl⟩ : syracuseStep 1921765 = 360331) (by norm_num)
theorem B2560757 : Blo 1707054 2560757 := bbase (se 5 (by rfl) ⟨120035, by rfl⟩ : syracuseStep 2560757 = 240071) (by norm_num)
theorem B1921801 : Blo 1707054 1921801 := bbase (se 2 (by rfl) ⟨720675, by rfl⟩ : syracuseStep 1921801 = 1441351) (by norm_num)
theorem B2560781 : Blo 1707054 2560781 := bbase (se 3 (by rfl) ⟨480146, by rfl⟩ : syracuseStep 2560781 = 960293) (by norm_num)
theorem B4322069 : Blo 1707054 4322069 := bbase (se 6 (by rfl) ⟨101298, by rfl⟩ : syracuseStep 4322069 = 202597) (by norm_num)
theorem B27693845 : Blo 1707054 27693845 := bbase (se 6 (by rfl) ⟨649074, by rfl⟩ : syracuseStep 27693845 = 1298149) (by norm_num)
theorem B2560805 : Blo 1707054 2560805 := bbase (se 4 (by rfl) ⟨240075, by rfl⟩ : syracuseStep 2560805 = 480151) (by norm_num)
theorem B1921837 : Blo 1707054 1921837 := bbase (se 3 (by rfl) ⟨360344, by rfl⟩ : syracuseStep 1921837 = 720689) (by norm_num)
theorem B2560829 : Blo 1707054 2560829 := bbase (se 3 (by rfl) ⟨480155, by rfl⟩ : syracuseStep 2560829 = 960311) (by norm_num)
theorem B6484805 : Blo 1707054 6484805 := bbase (se 4 (by rfl) ⟨607950, by rfl⟩ : syracuseStep 6484805 = 1215901) (by norm_num)
theorem B1921873 : Blo 1707054 1921873 := bbase (se 2 (by rfl) ⟨720702, by rfl⟩ : syracuseStep 1921873 = 1441405) (by norm_num)
theorem B2560853 : Blo 1707054 2560853 := bbase (se 9 (by rfl) ⟨7502, by rfl⟩ : syracuseStep 2560853 = 15005) (by norm_num)
theorem B2560877 : Blo 1707054 2560877 := bbase (se 3 (by rfl) ⟨480164, by rfl⟩ : syracuseStep 2560877 = 960329) (by norm_num)
theorem B1921909 : Blo 1707054 1921909 := bbase (se 5 (by rfl) ⟨90089, by rfl⟩ : syracuseStep 1921909 = 180179) (by norm_num)
theorem B2560901 : Blo 1707054 2560901 := bbase (se 4 (by rfl) ⟨240084, by rfl⟩ : syracuseStep 2560901 = 480169) (by norm_num)
theorem B1921945 : Blo 1707054 1921945 := bbase (se 2 (by rfl) ⟨720729, by rfl⟩ : syracuseStep 1921945 = 1441459) (by norm_num)
theorem B2560925 : Blo 1707054 2560925 := bbase (se 3 (by rfl) ⟨480173, by rfl⟩ : syracuseStep 2560925 = 960347) (by norm_num)
theorem B2560949 : Blo 1707054 2560949 := bbase (se 5 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 2560949 = 240089) (by norm_num)
theorem B1921981 : Blo 1707054 1921981 := bbase (se 3 (by rfl) ⟨360371, by rfl⟩ : syracuseStep 1921981 = 720743) (by norm_num)
theorem B1823681 : Blo 1707054 1823681 := bbase (se 2 (by rfl) ⟨683880, by rfl⟩ : syracuseStep 1823681 = 1367761) (by norm_num)
theorem B2560973 : Blo 1707054 2560973 := bbase (se 3 (by rfl) ⟨480182, by rfl⟩ : syracuseStep 2560973 = 960365) (by norm_num)
theorem B4322261 : Blo 1707054 4322261 := bbase (se 7 (by rfl) ⟨50651, by rfl⟩ : syracuseStep 4322261 = 101303) (by norm_num)
theorem B1922017 : Blo 1707054 1922017 := bbase (se 2 (by rfl) ⟨720756, by rfl⟩ : syracuseStep 1922017 = 1441513) (by norm_num)
theorem B2560997 : Blo 1707054 2560997 := bbase (se 4 (by rfl) ⟨240093, by rfl⟩ : syracuseStep 2560997 = 480187) (by norm_num)
theorem B2339813 : Blo 1707054 2339813 := bbase (se 4 (by rfl) ⟨219357, by rfl⟩ : syracuseStep 2339813 = 438715) (by norm_num)
theorem B2561021 : Blo 1707054 2561021 := bbase (se 3 (by rfl) ⟨480191, by rfl⟩ : syracuseStep 2561021 = 960383) (by norm_num)
theorem B1922053 : Blo 1707054 1922053 := bbase (se 4 (by rfl) ⟨180192, by rfl⟩ : syracuseStep 1922053 = 360385) (by norm_num)
theorem B1823753 : Blo 1707054 1823753 := bbase (se 2 (by rfl) ⟨683907, by rfl⟩ : syracuseStep 1823753 = 1367815) (by norm_num)
theorem B2561045 : Blo 1707054 2561045 := bbase (se 6 (by rfl) ⟨60024, by rfl⟩ : syracuseStep 2561045 = 120049) (by norm_num)
theorem B2053145 : Blo 1707054 2053145 := bbase (se 2 (by rfl) ⟨769929, by rfl⟩ : syracuseStep 2053145 = 1539859) (by norm_num)
theorem B1922089 : Blo 1707054 1922089 := bbase (se 2 (by rfl) ⟨720783, by rfl⟩ : syracuseStep 1922089 = 1441567) (by norm_num)
theorem B2561069 : Blo 1707054 2561069 := bbase (se 3 (by rfl) ⟨480200, by rfl⟩ : syracuseStep 2561069 = 960401) (by norm_num)
theorem B10941493 : Blo 1707054 10941493 := bbase (se 5 (by rfl) ⟨512882, by rfl⟩ : syracuseStep 10941493 = 1025765) (by norm_num)
theorem B2561093 : Blo 1707054 2561093 := bbase (se 4 (by rfl) ⟨240102, by rfl⟩ : syracuseStep 2561093 = 480205) (by norm_num)
theorem B1922125 : Blo 1707054 1922125 := bbase (se 3 (by rfl) ⟨360398, by rfl⟩ : syracuseStep 1922125 = 720797) (by norm_num)
theorem B8008789 : Blo 1707054 8008789 := bbase (se 8 (by rfl) ⟨46926, by rfl⟩ : syracuseStep 8008789 = 93853) (by norm_num)
theorem B2561117 : Blo 1707054 2561117 := bbase (se 3 (by rfl) ⟨480209, by rfl⟩ : syracuseStep 2561117 = 960419) (by norm_num)
theorem B6485093 : Blo 1707054 6485093 := bbase (se 4 (by rfl) ⟨607977, by rfl⟩ : syracuseStep 6485093 = 1215955) (by norm_num)
theorem B1922161 : Blo 1707054 1922161 := bbase (se 2 (by rfl) ⟨720810, by rfl⟩ : syracuseStep 1922161 = 1441621) (by norm_num)
theorem B2561141 : Blo 1707054 2561141 := bbase (se 5 (by rfl) ⟨120053, by rfl⟩ : syracuseStep 2561141 = 240107) (by norm_num)
theorem B5764229 : Blo 1707054 5764229 := bbase (se 4 (by rfl) ⟨540396, by rfl⟩ : syracuseStep 5764229 = 1080793) (by norm_num)
theorem B2561165 : Blo 1707054 2561165 := bbase (se 3 (by rfl) ⟨480218, by rfl⟩ : syracuseStep 2561165 = 960437) (by norm_num)
theorem B1922197 : Blo 1707054 1922197 := bbase (se 6 (by rfl) ⟨45051, by rfl⟩ : syracuseStep 1922197 = 90103) (by norm_num)
theorem B2880677 : Blo 1707054 2880677 := bbase (se 4 (by rfl) ⟨270063, by rfl⟩ : syracuseStep 2880677 = 540127) (by norm_num)
theorem B2561189 : Blo 1707054 2561189 := bbase (se 4 (by rfl) ⟨240111, by rfl⟩ : syracuseStep 2561189 = 480223) (by norm_num)
theorem B1922233 : Blo 1707054 1922233 := bbase (se 2 (by rfl) ⟨720837, by rfl⟩ : syracuseStep 1922233 = 1441675) (by norm_num)
theorem B2561213 : Blo 1707054 2561213 := bbase (se 3 (by rfl) ⟨480227, by rfl⟩ : syracuseStep 2561213 = 960455) (by norm_num)
theorem B1823941 : Blo 1707054 1823941 := bbase (se 4 (by rfl) ⟨170994, by rfl⟩ : syracuseStep 1823941 = 341989) (by norm_num)
theorem B2561237 : Blo 1707054 2561237 := bbase (se 7 (by rfl) ⟨30014, by rfl⟩ : syracuseStep 2561237 = 60029) (by norm_num)
theorem B1922269 : Blo 1707054 1922269 := bbase (se 3 (by rfl) ⟨360425, by rfl⟩ : syracuseStep 1922269 = 720851) (by norm_num)
theorem B2561261 : Blo 1707054 2561261 := bbase (se 3 (by rfl) ⟨480236, by rfl⟩ : syracuseStep 2561261 = 960473) (by norm_num)
theorem B1946873 : Blo 1707054 1946873 := bbase (se 2 (by rfl) ⟨730077, by rfl⟩ : syracuseStep 1946873 = 1460155) (by norm_num)
theorem B1922305 : Blo 1707054 1922305 := bbase (se 2 (by rfl) ⟨720864, by rfl⟩ : syracuseStep 1922305 = 1441729) (by norm_num)
theorem B2561285 : Blo 1707054 2561285 := bbase (se 4 (by rfl) ⟨240120, by rfl⟩ : syracuseStep 2561285 = 480241) (by norm_num)
theorem B7296277 : Blo 1707054 7296277 := bbase (se 6 (by rfl) ⟨171006, by rfl⟩ : syracuseStep 7296277 = 342013) (by norm_num)
theorem B2561309 : Blo 1707054 2561309 := bbase (se 3 (by rfl) ⟨480245, by rfl⟩ : syracuseStep 2561309 = 960491) (by norm_num)
theorem B2880805 : Blo 1707054 2880805 := bbase (se 4 (by rfl) ⟨270075, by rfl⟩ : syracuseStep 2880805 = 540151) (by norm_num)
theorem B1922341 : Blo 1707054 1922341 := bbase (se 4 (by rfl) ⟨180219, by rfl⟩ : syracuseStep 1922341 = 360439) (by norm_num)
theorem B4322605 : Blo 1707054 4322605 := bbase (se 3 (by rfl) ⟨810488, by rfl⟩ : syracuseStep 4322605 = 1620977) (by norm_num)
theorem B2561333 : Blo 1707054 2561333 := bbase (se 5 (by rfl) ⟨120062, by rfl⟩ : syracuseStep 2561333 = 240125) (by norm_num)
theorem B1922377 : Blo 1707054 1922377 := bbase (se 2 (by rfl) ⟨720891, by rfl⟩ : syracuseStep 1922377 = 1441783) (by norm_num)
theorem B2561357 : Blo 1707054 2561357 := bbase (se 3 (by rfl) ⟨480254, by rfl⟩ : syracuseStep 2561357 = 960509) (by norm_num)
theorem B3241309 : Blo 1707054 3241309 := bbase (se 3 (by rfl) ⟨607745, by rfl⟩ : syracuseStep 3241309 = 1215491) (by norm_num)
theorem B2561381 : Blo 1707054 2561381 := bbase (se 4 (by rfl) ⟨240129, by rfl⟩ : syracuseStep 2561381 = 480259) (by norm_num)
theorem B1922413 : Blo 1707054 1922413 := bbase (se 3 (by rfl) ⟨360452, by rfl⟩ : syracuseStep 1922413 = 720905) (by norm_num)
theorem B2880893 : Blo 1707054 2880893 := bbase (se 3 (by rfl) ⟨540167, by rfl⟩ : syracuseStep 2880893 = 1080335) (by norm_num)
theorem B2561405 : Blo 1707054 2561405 := bbase (se 3 (by rfl) ⟨480263, by rfl⟩ : syracuseStep 2561405 = 960527) (by norm_num)
theorem B1824125 : Blo 1707054 1824125 := bbase (se 3 (by rfl) ⟨342023, by rfl⟩ : syracuseStep 1824125 = 684047) (by norm_num)
theorem B4863365 : Blo 1707054 4863365 := bbase (se 4 (by rfl) ⟨455940, by rfl⟩ : syracuseStep 4863365 = 911881) (by norm_num)
theorem B1922449 : Blo 1707054 1922449 := bbase (se 2 (by rfl) ⟨720918, by rfl⟩ : syracuseStep 1922449 = 1441837) (by norm_num)
theorem B2561429 : Blo 1707054 2561429 := bbase (se 6 (by rfl) ⟨60033, by rfl⟩ : syracuseStep 2561429 = 120067) (by norm_num)
theorem B4322717 : Blo 1707054 4322717 := bbase (se 3 (by rfl) ⟨810509, by rfl⟩ : syracuseStep 4322717 = 1621019) (by norm_num)
theorem B2561453 : Blo 1707054 2561453 := bbase (se 3 (by rfl) ⟨480272, by rfl⟩ : syracuseStep 2561453 = 960545) (by norm_num)
theorem B1922485 : Blo 1707054 1922485 := bbase (se 5 (by rfl) ⟨90116, by rfl⟩ : syracuseStep 1922485 = 180233) (by norm_num)
theorem B2561477 : Blo 1707054 2561477 := bbase (se 4 (by rfl) ⟨240138, by rfl⟩ : syracuseStep 2561477 = 480277) (by norm_num)
theorem B4216277 : Blo 1707054 4216277 := bbase (se 7 (by rfl) ⟨49409, by rfl⟩ : syracuseStep 4216277 = 98819) (by norm_num)
theorem B1922521 : Blo 1707054 1922521 := bbase (se 2 (by rfl) ⟨720945, by rfl⟩ : syracuseStep 1922521 = 1441891) (by norm_num)
theorem B2561501 : Blo 1707054 2561501 := bbase (se 3 (by rfl) ⟨480281, by rfl⟩ : syracuseStep 2561501 = 960563) (by norm_num)
theorem B3241453 : Blo 1707054 3241453 := bbase (se 3 (by rfl) ⟨607772, by rfl⟩ : syracuseStep 3241453 = 1215545) (by norm_num)
theorem B2561525 : Blo 1707054 2561525 := bbase (se 5 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 2561525 = 240143) (by norm_num)
theorem B16422389 : Blo 1707054 16422389 := bbase (se 5 (by rfl) ⟨769799, by rfl⟩ : syracuseStep 16422389 = 1539599) (by norm_num)
theorem B2881021 : Blo 1707054 2881021 := bbase (se 3 (by rfl) ⟨540191, by rfl⟩ : syracuseStep 2881021 = 1080383) (by norm_num)
theorem B1922557 : Blo 1707054 1922557 := bbase (se 3 (by rfl) ⟨360479, by rfl⟩ : syracuseStep 1922557 = 720959) (by norm_num)
theorem B2561549 : Blo 1707054 2561549 := bbase (se 3 (by rfl) ⟨480290, by rfl⟩ : syracuseStep 2561549 = 960581) (by norm_num)
theorem B1947169 : Blo 1707054 1947169 := bbase (se 2 (by rfl) ⟨730188, by rfl⟩ : syracuseStep 1947169 = 1460377) (by norm_num)
theorem B1922593 : Blo 1707054 1922593 := bbase (se 2 (by rfl) ⟨720972, by rfl⟩ : syracuseStep 1922593 = 1441945) (by norm_num)
theorem B2561573 : Blo 1707054 2561573 := bbase (se 4 (by rfl) ⟨240147, by rfl⟩ : syracuseStep 2561573 = 480295) (by norm_num)
theorem B5764661 : Blo 1707054 5764661 := bbase (se 5 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 5764661 = 540437) (by norm_num)
theorem B3896885 : Blo 1707054 3896885 := bbase (se 5 (by rfl) ⟨182666, by rfl⟩ : syracuseStep 3896885 = 365333) (by norm_num)
theorem B2561597 : Blo 1707054 2561597 := bbase (se 3 (by rfl) ⟨480299, by rfl⟩ : syracuseStep 2561597 = 960599) (by norm_num)
theorem B1922629 : Blo 1707054 1922629 := bbase (se 4 (by rfl) ⟨180246, by rfl⟩ : syracuseStep 1922629 = 360493) (by norm_num)
theorem B2881109 : Blo 1707054 2881109 := bbase (se 8 (by rfl) ⟨16881, by rfl⟩ : syracuseStep 2881109 = 33763) (by norm_num)
theorem B2561621 : Blo 1707054 2561621 := bbase (se 8 (by rfl) ⟨15009, by rfl⟩ : syracuseStep 2561621 = 30019) (by norm_num)
theorem B4322909 : Blo 1707054 4322909 := bbase (se 3 (by rfl) ⟨810545, by rfl⟩ : syracuseStep 4322909 = 1621091) (by norm_num)
theorem B1922665 : Blo 1707054 1922665 := bbase (se 2 (by rfl) ⟨720999, by rfl⟩ : syracuseStep 1922665 = 1441999) (by norm_num)
theorem B2561645 : Blo 1707054 2561645 := bbase (se 3 (by rfl) ⟨480308, by rfl⟩ : syracuseStep 2561645 = 960617) (by norm_num)
theorem B2430589 : Blo 1707054 2430589 := bbase (se 3 (by rfl) ⟨455735, by rfl⟩ : syracuseStep 2430589 = 911471) (by norm_num)
theorem B2561669 : Blo 1707054 2561669 := bbase (se 4 (by rfl) ⟨240156, by rfl⟩ : syracuseStep 2561669 = 480313) (by norm_num)
theorem B1848965 : Blo 1707054 1848965 := bbase (se 4 (by rfl) ⟨173340, by rfl⟩ : syracuseStep 1848965 = 346681) (by norm_num)
theorem B3241613 : Blo 1707054 3241613 := bbase (se 3 (by rfl) ⟨607802, by rfl⟩ : syracuseStep 3241613 = 1215605) (by norm_num)
theorem B2561693 : Blo 1707054 2561693 := bbase (se 3 (by rfl) ⟨480317, by rfl⟩ : syracuseStep 2561693 = 960635) (by norm_num)
theorem B2561717 : Blo 1707054 2561717 := bbase (se 5 (by rfl) ⟨120080, by rfl⟩ : syracuseStep 2561717 = 240161) (by norm_num)
theorem B2561741 : Blo 1707054 2561741 := bbase (se 3 (by rfl) ⟨480326, by rfl⟩ : syracuseStep 2561741 = 960653) (by norm_num)
theorem B2881237 : Blo 1707054 2881237 := bbase (se 7 (by rfl) ⟨33764, by rfl⟩ : syracuseStep 2881237 = 67529) (by norm_num)
theorem B2561765 : Blo 1707054 2561765 := bbase (se 4 (by rfl) ⟨240165, by rfl⟩ : syracuseStep 2561765 = 480331) (by norm_num)
theorem B2561789 : Blo 1707054 2561789 := bbase (se 3 (by rfl) ⟨480335, by rfl⟩ : syracuseStep 2561789 = 960671) (by norm_num)
theorem B2561813 : Blo 1707054 2561813 := bbase (se 6 (by rfl) ⟨60042, by rfl⟩ : syracuseStep 2561813 = 120085) (by norm_num)
theorem B3241757 : Blo 1707054 3241757 := bbase (se 3 (by rfl) ⟨607829, by rfl⟩ : syracuseStep 3241757 = 1215659) (by norm_num)
theorem B2881325 : Blo 1707054 2881325 := bbase (se 3 (by rfl) ⟨540248, by rfl⟩ : syracuseStep 2881325 = 1080497) (by norm_num)
theorem B2561837 : Blo 1707054 2561837 := bbase (se 3 (by rfl) ⟨480344, by rfl⟩ : syracuseStep 2561837 = 960689) (by norm_num)
theorem B4863797 : Blo 1707054 4863797 := bbase (se 5 (by rfl) ⟨227990, by rfl⟩ : syracuseStep 4863797 = 455981) (by norm_num)
theorem B2561861 : Blo 1707054 2561861 := bbase (se 4 (by rfl) ⟨240174, by rfl⟩ : syracuseStep 2561861 = 480349) (by norm_num)
theorem B2430805 : Blo 1707054 2430805 := bbase (se 9 (by rfl) ⟨7121, by rfl⟩ : syracuseStep 2430805 = 14243) (by norm_num)
theorem B6158165 : Blo 1707054 6158165 := bbase (se 9 (by rfl) ⟨18041, by rfl⟩ : syracuseStep 6158165 = 36083) (by norm_num)
theorem B2561885 : Blo 1707054 2561885 := bbase (se 3 (by rfl) ⟨480353, by rfl⟩ : syracuseStep 2561885 = 960707) (by norm_num)
theorem B3077981 : Blo 1707054 3077981 := bbase (se 3 (by rfl) ⟨577121, by rfl⟩ : syracuseStep 3077981 = 1154243) (by norm_num)
theorem B1947493 : Blo 1707054 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B2561909 : Blo 1707054 2561909 := bbase (se 5 (by rfl) ⟨120089, by rfl⟩ : syracuseStep 2561909 = 240179) (by norm_num)
theorem B2561933 : Blo 1707054 2561933 := bbase (se 3 (by rfl) ⟨480362, by rfl⟩ : syracuseStep 2561933 = 960725) (by norm_num)
theorem B2160533 : Blo 1707054 2160533 := bbase (se 6 (by rfl) ⟨50637, by rfl⟩ : syracuseStep 2160533 = 101275) (by norm_num)
theorem B2561957 : Blo 1707054 2561957 := bbase (se 4 (by rfl) ⟨240183, by rfl⟩ : syracuseStep 2561957 = 480367) (by norm_num)
theorem B2881453 : Blo 1707054 2881453 := bbase (se 3 (by rfl) ⟨540272, by rfl⟩ : syracuseStep 2881453 = 1080545) (by norm_num)
theorem B4323253 : Blo 1707054 4323253 := bbase (se 5 (by rfl) ⟨202652, by rfl⟩ : syracuseStep 4323253 = 405305) (by norm_num)
theorem B2561981 : Blo 1707054 2561981 := bbase (se 3 (by rfl) ⟨480371, by rfl⟩ : syracuseStep 2561981 = 960743) (by norm_num)
theorem B2160589 : Blo 1707054 2160589 := bbase (se 3 (by rfl) ⟨405110, by rfl⟩ : syracuseStep 2160589 = 810221) (by norm_num)
theorem B2562005 : Blo 1707054 2562005 := bbase (se 7 (by rfl) ⟨30023, by rfl⟩ : syracuseStep 2562005 = 60047) (by norm_num)
theorem B41564117 : Blo 1707054 41564117 := bbase (se 7 (by rfl) ⟨487079, by rfl⟩ : syracuseStep 41564117 = 974159) (by norm_num)
theorem B4929509 : Blo 1707054 4929509 := bbase (se 4 (by rfl) ⟨462141, by rfl⟩ : syracuseStep 4929509 = 924283) (by norm_num)
theorem B5765093 : Blo 1707054 5765093 := bbase (se 4 (by rfl) ⟨540477, by rfl⟩ : syracuseStep 5765093 = 1080955) (by norm_num)
theorem B2562029 : Blo 1707054 2562029 := bbase (se 3 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 2562029 = 960761) (by norm_num)
theorem B8648693 : Blo 1707054 8648693 := bbase (se 5 (by rfl) ⟨405407, by rfl⟩ : syracuseStep 8648693 = 810815) (by norm_num)
theorem B2881541 : Blo 1707054 2881541 := bbase (se 4 (by rfl) ⟨270144, by rfl⟩ : syracuseStep 2881541 = 540289) (by norm_num)
theorem B2562053 : Blo 1707054 2562053 := bbase (se 4 (by rfl) ⟨240192, by rfl⟩ : syracuseStep 2562053 = 480385) (by norm_num)
theorem B2562077 : Blo 1707054 2562077 := bbase (se 3 (by rfl) ⟨480389, by rfl⟩ : syracuseStep 2562077 = 960779) (by norm_num)
theorem B4323365 : Blo 1707054 4323365 := bbase (se 4 (by rfl) ⟨405315, by rfl⟩ : syracuseStep 4323365 = 810631) (by norm_num)
theorem B2160685 : Blo 1707054 2160685 := bbase (se 3 (by rfl) ⟨405128, by rfl⟩ : syracuseStep 2160685 = 810257) (by norm_num)
theorem B2562101 : Blo 1707054 2562101 := bbase (se 5 (by rfl) ⟨120098, by rfl⟩ : syracuseStep 2562101 = 240197) (by norm_num)
theorem B3242045 : Blo 1707054 3242045 := bbase (se 3 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 3242045 = 1215767) (by norm_num)
theorem B2562125 : Blo 1707054 2562125 := bbase (se 3 (by rfl) ⟨480398, by rfl⟩ : syracuseStep 2562125 = 960797) (by norm_num)
theorem B2562149 : Blo 1707054 2562149 := bbase (se 4 (by rfl) ⟨240201, by rfl⟩ : syracuseStep 2562149 = 480403) (by norm_num)
theorem B1824877 : Blo 1707054 1824877 := bbase (se 3 (by rfl) ⟨342164, by rfl⟩ : syracuseStep 1824877 = 684329) (by norm_num)
theorem B5470325 : Blo 1707054 5470325 := bbase (se 5 (by rfl) ⟨256421, by rfl⟩ : syracuseStep 5470325 = 512843) (by norm_num)
theorem B3119221 : Blo 1707054 3119221 := bbase (se 5 (by rfl) ⟨146213, by rfl⟩ : syracuseStep 3119221 = 292427) (by norm_num)
theorem B2562173 : Blo 1707054 2562173 := bbase (se 3 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 2562173 = 960815) (by norm_num)
theorem B2881669 : Blo 1707054 2881669 := bbase (se 4 (by rfl) ⟨270156, by rfl⟩ : syracuseStep 2881669 = 540313) (by norm_num)
theorem B2562197 : Blo 1707054 2562197 := bbase (se 6 (by rfl) ⟨60051, by rfl⟩ : syracuseStep 2562197 = 120103) (by norm_num)
theorem B2562221 : Blo 1707054 2562221 := bbase (se 3 (by rfl) ⟨480416, by rfl⟩ : syracuseStep 2562221 = 960833) (by norm_num)
theorem B1824949 : Blo 1707054 1824949 := bbase (se 5 (by rfl) ⟨85544, by rfl⟩ : syracuseStep 1824949 = 171089) (by norm_num)
theorem B2562245 : Blo 1707054 2562245 := bbase (se 4 (by rfl) ⟨240210, by rfl⟩ : syracuseStep 2562245 = 480421) (by norm_num)
theorem B2431181 : Blo 1707054 2431181 := bbase (se 3 (by rfl) ⟨455846, by rfl⟩ : syracuseStep 2431181 = 911693) (by norm_num)
theorem B3242197 : Blo 1707054 3242197 := bbase (se 7 (by rfl) ⟨37994, by rfl⟩ : syracuseStep 3242197 = 75989) (by norm_num)
theorem B2160857 : Blo 1707054 2160857 := bbase (se 2 (by rfl) ⟨810321, by rfl⟩ : syracuseStep 2160857 = 1620643) (by norm_num)
theorem B2881757 : Blo 1707054 2881757 := bbase (se 3 (by rfl) ⟨540329, by rfl⟩ : syracuseStep 2881757 = 1080659) (by norm_num)
theorem B2562269 : Blo 1707054 2562269 := bbase (se 3 (by rfl) ⟨480425, by rfl⟩ : syracuseStep 2562269 = 960851) (by norm_num)
theorem B4323557 : Blo 1707054 4323557 := bbase (se 4 (by rfl) ⟨405333, by rfl⟩ : syracuseStep 4323557 = 810667) (by norm_num)
theorem B2562293 : Blo 1707054 2562293 := bbase (se 5 (by rfl) ⟨120107, by rfl⟩ : syracuseStep 2562293 = 240215) (by norm_num)
theorem B6486277 : Blo 1707054 6486277 := bbase (se 4 (by rfl) ⟨608088, by rfl⟩ : syracuseStep 6486277 = 1216177) (by norm_num)
theorem B8321285 : Blo 1707054 8321285 := bbase (se 4 (by rfl) ⟨780120, by rfl⟩ : syracuseStep 8321285 = 1560241) (by norm_num)
theorem B2562317 : Blo 1707054 2562317 := bbase (se 3 (by rfl) ⟨480434, by rfl⟩ : syracuseStep 2562317 = 960869) (by norm_num)
theorem B2160913 : Blo 1707054 2160913 := bbase (se 2 (by rfl) ⟨810342, by rfl⟩ : syracuseStep 2160913 = 1620685) (by norm_num)
theorem B2562341 : Blo 1707054 2562341 := bbase (se 4 (by rfl) ⟨240219, by rfl⟩ : syracuseStep 2562341 = 480439) (by norm_num)
theorem B4102445 : Blo 1707054 4102445 := bbase (se 3 (by rfl) ⟨769208, by rfl⟩ : syracuseStep 4102445 = 1538417) (by norm_num)
theorem B11688245 : Blo 1707054 11688245 := bbase (se 5 (by rfl) ⟨547886, by rfl⟩ : syracuseStep 11688245 = 1095773) (by norm_num)
theorem B2562365 : Blo 1707054 2562365 := bbase (se 3 (by rfl) ⟨480443, by rfl⟩ : syracuseStep 2562365 = 960887) (by norm_num)
theorem B2562389 : Blo 1707054 2562389 := bbase (se 10 (by rfl) ⟨3753, by rfl⟩ : syracuseStep 2562389 = 7507) (by norm_num)
theorem B41564501 : Blo 1707054 41564501 := bbase (se 10 (by rfl) ⟨60885, by rfl⟩ : syracuseStep 41564501 = 121771) (by norm_num)
theorem B2881885 : Blo 1707054 2881885 := bbase (se 3 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 2881885 = 1080707) (by norm_num)
theorem B2734445 : Blo 1707054 2734445 := bbase (se 3 (by rfl) ⟨512708, by rfl⟩ : syracuseStep 2734445 = 1025417) (by norm_num)
theorem B2562413 : Blo 1707054 2562413 := bbase (se 3 (by rfl) ⟨480452, by rfl⟩ : syracuseStep 2562413 = 960905) (by norm_num)
theorem B2161009 : Blo 1707054 2161009 := bbase (se 2 (by rfl) ⟨810378, by rfl⟩ : syracuseStep 2161009 = 1620757) (by norm_num)
theorem B2562437 : Blo 1707054 2562437 := bbase (se 4 (by rfl) ⟨240228, by rfl⟩ : syracuseStep 2562437 = 480457) (by norm_num)
theorem B1948045 : Blo 1707054 1948045 := bbase (se 3 (by rfl) ⟨365258, by rfl⟩ : syracuseStep 1948045 = 730517) (by norm_num)
theorem B5765525 : Blo 1707054 5765525 := bbase (se 6 (by rfl) ⟨135129, by rfl⟩ : syracuseStep 5765525 = 270259) (by norm_num)
theorem B2562461 : Blo 1707054 2562461 := bbase (se 3 (by rfl) ⟨480461, by rfl⟩ : syracuseStep 2562461 = 960923) (by norm_num)
theorem B2881973 : Blo 1707054 2881973 := bbase (se 5 (by rfl) ⟨135092, by rfl⟩ : syracuseStep 2881973 = 270185) (by norm_num)
theorem B2562485 : Blo 1707054 2562485 := bbase (se 5 (by rfl) ⟨120116, by rfl⟩ : syracuseStep 2562485 = 240233) (by norm_num)
theorem B2562509 : Blo 1707054 2562509 := bbase (se 3 (by rfl) ⟨480470, by rfl⟩ : syracuseStep 2562509 = 960941) (by norm_num)
theorem B2562533 : Blo 1707054 2562533 := bbase (se 4 (by rfl) ⟨240237, by rfl⟩ : syracuseStep 2562533 = 480475) (by norm_num)
theorem B2562557 : Blo 1707054 2562557 := bbase (se 3 (by rfl) ⟨480479, by rfl⟩ : syracuseStep 2562557 = 960959) (by norm_num)
theorem B3242501 : Blo 1707054 3242501 := bbase (se 4 (by rfl) ⟨303984, by rfl⟩ : syracuseStep 3242501 = 607969) (by norm_num)
theorem B2562581 : Blo 1707054 2562581 := bbase (se 6 (by rfl) ⟨60060, by rfl⟩ : syracuseStep 2562581 = 120121) (by norm_num)
theorem B2161181 : Blo 1707054 2161181 := bbase (se 3 (by rfl) ⟨405221, by rfl⟩ : syracuseStep 2161181 = 810443) (by norm_num)
theorem B4864549 : Blo 1707054 4864549 := bbase (se 4 (by rfl) ⟨456051, by rfl⟩ : syracuseStep 4864549 = 912103) (by norm_num)
theorem B2562605 : Blo 1707054 2562605 := bbase (se 3 (by rfl) ⟨480488, by rfl⟩ : syracuseStep 2562605 = 960977) (by norm_num)
theorem B2882101 : Blo 1707054 2882101 := bbase (se 5 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 2882101 = 270197) (by norm_num)
theorem B6486581 : Blo 1707054 6486581 := bbase (se 5 (by rfl) ⟨304058, by rfl⟩ : syracuseStep 6486581 = 608117) (by norm_num)
theorem B4323901 : Blo 1707054 4323901 := bbase (se 3 (by rfl) ⟨810731, by rfl⟩ : syracuseStep 4323901 = 1621463) (by norm_num)
theorem B2562629 : Blo 1707054 2562629 := bbase (se 4 (by rfl) ⟨240246, by rfl⟩ : syracuseStep 2562629 = 480493) (by norm_num)
theorem B2734669 : Blo 1707054 2734669 := bbase (se 3 (by rfl) ⟨512750, by rfl⟩ : syracuseStep 2734669 = 1025501) (by norm_num)
theorem B2161237 : Blo 1707054 2161237 := bbase (se 8 (by rfl) ⟨12663, by rfl⟩ : syracuseStep 2161237 = 25327) (by norm_num)
theorem B2562653 : Blo 1707054 2562653 := bbase (se 3 (by rfl) ⟨480497, by rfl⟩ : syracuseStep 2562653 = 960995) (by norm_num)
theorem B2562677 : Blo 1707054 2562677 := bbase (se 5 (by rfl) ⟨120125, by rfl⟩ : syracuseStep 2562677 = 240251) (by norm_num)
theorem B2882189 : Blo 1707054 2882189 := bbase (se 3 (by rfl) ⟨540410, by rfl⟩ : syracuseStep 2882189 = 1080821) (by norm_num)
theorem B2562701 : Blo 1707054 2562701 := bbase (se 3 (by rfl) ⟨480506, by rfl⟩ : syracuseStep 2562701 = 961013) (by norm_num)
theorem B12974741 : Blo 1707054 12974741 := bbase (se 6 (by rfl) ⟨304095, by rfl⟩ : syracuseStep 12974741 = 608191) (by norm_num)
theorem B2562725 : Blo 1707054 2562725 := bbase (se 4 (by rfl) ⟨240255, by rfl⟩ : syracuseStep 2562725 = 480511) (by norm_num)
theorem B4324013 : Blo 1707054 4324013 := bbase (se 3 (by rfl) ⟨810752, by rfl⟩ : syracuseStep 4324013 = 1621505) (by norm_num)
theorem B2161333 : Blo 1707054 2161333 := bbase (se 5 (by rfl) ⟨101312, by rfl⟩ : syracuseStep 2161333 = 202625) (by norm_num)
theorem B2562749 : Blo 1707054 2562749 := bbase (se 3 (by rfl) ⟨480515, by rfl⟩ : syracuseStep 2562749 = 961031) (by norm_num)
theorem B2562773 : Blo 1707054 2562773 := bbase (se 7 (by rfl) ⟨30032, by rfl⟩ : syracuseStep 2562773 = 60065) (by norm_num)
theorem B7396069 : Blo 1707054 7396069 := bbase (se 4 (by rfl) ⟨693381, by rfl⟩ : syracuseStep 7396069 = 1386763) (by norm_num)
theorem B2562797 : Blo 1707054 2562797 := bbase (se 3 (by rfl) ⟨480524, by rfl⟩ : syracuseStep 2562797 = 961049) (by norm_num)
theorem B2562821 : Blo 1707054 2562821 := bbase (se 4 (by rfl) ⟨240264, by rfl⟩ : syracuseStep 2562821 = 480529) (by norm_num)
theorem B2882317 : Blo 1707054 2882317 := bbase (se 3 (by rfl) ⟨540434, by rfl⟩ : syracuseStep 2882317 = 1080869) (by norm_num)
theorem B2079517 : Blo 1707054 2079517 := bbase (se 3 (by rfl) ⟨389909, by rfl⟩ : syracuseStep 2079517 = 779819) (by norm_num)
theorem B2562845 : Blo 1707054 2562845 := bbase (se 3 (by rfl) ⟨480533, by rfl⟩ : syracuseStep 2562845 = 961067) (by norm_num)
theorem B1948465 : Blo 1707054 1948465 := bbase (se 2 (by rfl) ⟨730674, by rfl⟩ : syracuseStep 1948465 = 1461349) (by norm_num)
theorem B2562869 : Blo 1707054 2562869 := bbase (se 5 (by rfl) ⟨120134, by rfl⟩ : syracuseStep 2562869 = 240269) (by norm_num)
theorem B5765957 : Blo 1707054 5765957 := bbase (se 4 (by rfl) ⟨540558, by rfl⟩ : syracuseStep 5765957 = 1081117) (by norm_num)
theorem B2562893 : Blo 1707054 2562893 := bbase (se 3 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 2562893 = 961085) (by norm_num)
theorem B2161505 : Blo 1707054 2161505 := bbase (se 2 (by rfl) ⟨810564, by rfl⟩ : syracuseStep 2161505 = 1621129) (by norm_num)
theorem B5192549 : Blo 1707054 5192549 := bbase (se 4 (by rfl) ⟨486801, by rfl⟩ : syracuseStep 5192549 = 973603) (by norm_num)
theorem B2882405 : Blo 1707054 2882405 := bbase (se 4 (by rfl) ⟨270225, by rfl⟩ : syracuseStep 2882405 = 540451) (by norm_num)
theorem B2562917 : Blo 1707054 2562917 := bbase (se 4 (by rfl) ⟨240273, by rfl⟩ : syracuseStep 2562917 = 480547) (by norm_num)
theorem B4324205 : Blo 1707054 4324205 := bbase (se 3 (by rfl) ⟨810788, by rfl⟩ : syracuseStep 4324205 = 1621577) (by norm_num)
theorem B3840893 : Blo 1707054 3840893 := bbase (se 3 (by rfl) ⟨720167, by rfl⟩ : syracuseStep 3840893 = 1440335) (by norm_num)
theorem B2562941 : Blo 1707054 2562941 := bbase (se 3 (by rfl) ⟨480551, by rfl⟩ : syracuseStep 2562941 = 961103) (by norm_num)
theorem B2562965 : Blo 1707054 2562965 := bbase (se 6 (by rfl) ⟨60069, by rfl⟩ : syracuseStep 2562965 = 120139) (by norm_num)
theorem B2161561 : Blo 1707054 2161561 := bbase (se 2 (by rfl) ⟨810585, by rfl⟩ : syracuseStep 2161561 = 1621171) (by norm_num)
theorem B2562989 : Blo 1707054 2562989 := bbase (se 3 (by rfl) ⟨480560, by rfl⟩ : syracuseStep 2562989 = 961121) (by norm_num)
theorem B2309053 : Blo 1707054 2309053 := bbase (se 3 (by rfl) ⟨432947, by rfl⟩ : syracuseStep 2309053 = 865895) (by norm_num)
theorem B3840965 : Blo 1707054 3840965 := bbase (se 4 (by rfl) ⟨360090, by rfl⟩ : syracuseStep 3840965 = 720181) (by norm_num)
theorem B2563013 : Blo 1707054 2563013 := bbase (se 4 (by rfl) ⟨240282, by rfl⟩ : syracuseStep 2563013 = 480565) (by norm_num)
theorem B2563037 : Blo 1707054 2563037 := bbase (se 3 (by rfl) ⟨480569, by rfl⟩ : syracuseStep 2563037 = 961139) (by norm_num)
theorem B2882533 : Blo 1707054 2882533 := bbase (se 4 (by rfl) ⟨270237, by rfl⟩ : syracuseStep 2882533 = 540475) (by norm_num)
theorem B2563061 : Blo 1707054 2563061 := bbase (se 5 (by rfl) ⟨120143, by rfl⟩ : syracuseStep 2563061 = 240287) (by norm_num)
theorem B2161657 : Blo 1707054 2161657 := bbase (se 2 (by rfl) ⟨810621, by rfl⟩ : syracuseStep 2161657 = 1621243) (by norm_num)
theorem B3841037 : Blo 1707054 3841037 := bbase (se 3 (by rfl) ⟨720194, by rfl⟩ : syracuseStep 3841037 = 1440389) (by norm_num)
theorem B2563085 : Blo 1707054 2563085 := bbase (se 3 (by rfl) ⟨480578, by rfl⟩ : syracuseStep 2563085 = 961157) (by norm_num)
theorem B2563109 : Blo 1707054 2563109 := bbase (se 4 (by rfl) ⟨240291, by rfl⟩ : syracuseStep 2563109 = 480583) (by norm_num)
theorem B12966965 : Blo 1707054 12966965 := bbase (se 5 (by rfl) ⟨607826, by rfl⟩ : syracuseStep 12966965 = 1215653) (by norm_num)
theorem B2882621 : Blo 1707054 2882621 := bbase (se 3 (by rfl) ⟨540491, by rfl⟩ : syracuseStep 2882621 = 1080983) (by norm_num)
theorem B2563133 : Blo 1707054 2563133 := bbase (se 3 (by rfl) ⟨480587, by rfl⟩ : syracuseStep 2563133 = 961175) (by norm_num)
theorem B3841109 : Blo 1707054 3841109 := bbase (se 8 (by rfl) ⟨22506, by rfl⟩ : syracuseStep 3841109 = 45013) (by norm_num)
theorem B2563157 : Blo 1707054 2563157 := bbase (se 8 (by rfl) ⟨15018, by rfl⟩ : syracuseStep 2563157 = 30037) (by norm_num)
theorem B2563181 : Blo 1707054 2563181 := bbase (se 3 (by rfl) ⟨480596, by rfl⟩ : syracuseStep 2563181 = 961193) (by norm_num)
theorem B2563205 : Blo 1707054 2563205 := bbase (se 4 (by rfl) ⟨240300, by rfl⟩ : syracuseStep 2563205 = 480601) (by norm_num)
theorem B3841181 : Blo 1707054 3841181 := bbase (se 3 (by rfl) ⟨720221, by rfl⟩ : syracuseStep 3841181 = 1440443) (by norm_num)
theorem B2563229 : Blo 1707054 2563229 := bbase (se 3 (by rfl) ⟨480605, by rfl⟩ : syracuseStep 2563229 = 961211) (by norm_num)
theorem B2161829 : Blo 1707054 2161829 := bbase (se 4 (by rfl) ⟨202671, by rfl⟩ : syracuseStep 2161829 = 405343) (by norm_num)
theorem B3161261 : Blo 1707054 3161261 := bbase (se 3 (by rfl) ⟨592736, by rfl⟩ : syracuseStep 3161261 = 1185473) (by norm_num)
theorem B2563253 : Blo 1707054 2563253 := bbase (se 5 (by rfl) ⟨120152, by rfl⟩ : syracuseStep 2563253 = 240305) (by norm_num)
theorem B2882749 : Blo 1707054 2882749 := bbase (se 3 (by rfl) ⟨540515, by rfl⟩ : syracuseStep 2882749 = 1081031) (by norm_num)
theorem B4324549 : Blo 1707054 4324549 := bbase (se 4 (by rfl) ⟨405426, by rfl⟩ : syracuseStep 4324549 = 810853) (by norm_num)
theorem B2563277 : Blo 1707054 2563277 := bbase (se 3 (by rfl) ⟨480614, by rfl⟩ : syracuseStep 2563277 = 961229) (by norm_num)
theorem B9731285 : Blo 1707054 9731285 := bbase (se 7 (by rfl) ⟨114038, by rfl⟩ : syracuseStep 9731285 = 228077) (by norm_num)
theorem B2161885 : Blo 1707054 2161885 := bbase (se 3 (by rfl) ⟨405353, by rfl⟩ : syracuseStep 2161885 = 810707) (by norm_num)
theorem B3841253 : Blo 1707054 3841253 := bbase (se 4 (by rfl) ⟨360117, by rfl⟩ : syracuseStep 3841253 = 720235) (by norm_num)
theorem B2563301 : Blo 1707054 2563301 := bbase (se 4 (by rfl) ⟨240309, by rfl⟩ : syracuseStep 2563301 = 480619) (by norm_num)
theorem B3243253 : Blo 1707054 3243253 := bbase (se 5 (by rfl) ⟨152027, by rfl⟩ : syracuseStep 3243253 = 304055) (by norm_num)
theorem B5766389 : Blo 1707054 5766389 := bbase (se 5 (by rfl) ⟨270299, by rfl⟩ : syracuseStep 5766389 = 540599) (by norm_num)
theorem B2563325 : Blo 1707054 2563325 := bbase (se 3 (by rfl) ⟨480623, by rfl⟩ : syracuseStep 2563325 = 961247) (by norm_num)
theorem B8649989 : Blo 1707054 8649989 := bbase (se 4 (by rfl) ⟨810936, by rfl⟩ : syracuseStep 8649989 = 1621873) (by norm_num)
theorem B2882837 : Blo 1707054 2882837 := bbase (se 6 (by rfl) ⟨67566, by rfl⟩ : syracuseStep 2882837 = 135133) (by norm_num)
theorem B2563349 : Blo 1707054 2563349 := bbase (se 6 (by rfl) ⟨60078, by rfl⟩ : syracuseStep 2563349 = 120157) (by norm_num)
theorem B3841325 : Blo 1707054 3841325 := bbase (se 3 (by rfl) ⟨720248, by rfl⟩ : syracuseStep 3841325 = 1440497) (by norm_num)
theorem B2563373 : Blo 1707054 2563373 := bbase (se 3 (by rfl) ⟨480632, by rfl⟩ : syracuseStep 2563373 = 961265) (by norm_num)
theorem B4324661 : Blo 1707054 4324661 := bbase (se 5 (by rfl) ⟨202718, by rfl⟩ : syracuseStep 4324661 = 405437) (by norm_num)
theorem B2161981 : Blo 1707054 2161981 := bbase (se 3 (by rfl) ⟨405371, by rfl⟩ : syracuseStep 2161981 = 810743) (by norm_num)
theorem B2563397 : Blo 1707054 2563397 := bbase (se 4 (by rfl) ⟨240318, by rfl⟩ : syracuseStep 2563397 = 480637) (by norm_num)
theorem B3079501 : Blo 1707054 3079501 := bbase (se 3 (by rfl) ⟨577406, by rfl⟩ : syracuseStep 3079501 = 1154813) (by norm_num)
theorem B2563421 : Blo 1707054 2563421 := bbase (se 3 (by rfl) ⟨480641, by rfl⟩ : syracuseStep 2563421 = 961283) (by norm_num)
theorem B3841397 : Blo 1707054 3841397 := bbase (se 5 (by rfl) ⟨180065, by rfl⟩ : syracuseStep 3841397 = 360131) (by norm_num)
theorem B2563445 : Blo 1707054 2563445 := bbase (se 5 (by rfl) ⟨120161, by rfl⟩ : syracuseStep 2563445 = 240323) (by norm_num)
theorem B3243397 : Blo 1707054 3243397 := bbase (se 4 (by rfl) ⟨304068, by rfl⟩ : syracuseStep 3243397 = 608137) (by norm_num)
theorem B2563469 : Blo 1707054 2563469 := bbase (se 3 (by rfl) ⟨480650, by rfl⟩ : syracuseStep 2563469 = 961301) (by norm_num)
theorem B2882965 : Blo 1707054 2882965 := bbase (se 6 (by rfl) ⟨67569, by rfl⟩ : syracuseStep 2882965 = 135139) (by norm_num)
theorem B2563493 : Blo 1707054 2563493 := bbase (se 4 (by rfl) ⟨240327, by rfl⟩ : syracuseStep 2563493 = 480655) (by norm_num)
theorem B5471669 : Blo 1707054 5471669 := bbase (se 5 (by rfl) ⟨256484, by rfl⟩ : syracuseStep 5471669 = 512969) (by norm_num)
theorem B3841469 : Blo 1707054 3841469 := bbase (se 3 (by rfl) ⟨720275, by rfl⟩ : syracuseStep 3841469 = 1440551) (by norm_num)
theorem B2563517 : Blo 1707054 2563517 := bbase (se 3 (by rfl) ⟨480659, by rfl⟩ : syracuseStep 2563517 = 961319) (by norm_num)
theorem B8764885 : Blo 1707054 8764885 := bbase (se 7 (by rfl) ⟨102713, by rfl⟩ : syracuseStep 8764885 = 205427) (by norm_num)
theorem B2563541 : Blo 1707054 2563541 := bbase (se 7 (by rfl) ⟨30041, by rfl⟩ : syracuseStep 2563541 = 60083) (by norm_num)
theorem B2162153 : Blo 1707054 2162153 := bbase (se 2 (by rfl) ⟨810807, by rfl⟩ : syracuseStep 2162153 = 1621615) (by norm_num)
theorem B2883053 : Blo 1707054 2883053 := bbase (se 3 (by rfl) ⟨540572, by rfl⟩ : syracuseStep 2883053 = 1081145) (by norm_num)
theorem B2563565 : Blo 1707054 2563565 := bbase (se 3 (by rfl) ⟨480668, by rfl⟩ : syracuseStep 2563565 = 961337) (by norm_num)
theorem B4324853 : Blo 1707054 4324853 := bbase (se 5 (by rfl) ⟨202727, by rfl⟩ : syracuseStep 4324853 = 405455) (by norm_num)
theorem B3841541 : Blo 1707054 3841541 := bbase (se 4 (by rfl) ⟨360144, by rfl⟩ : syracuseStep 3841541 = 720289) (by norm_num)
theorem B2162209 : Blo 1707054 2162209 := bbase (se 2 (by rfl) ⟨810828, by rfl⟩ : syracuseStep 2162209 = 1621657) (by norm_num)
theorem B3243557 : Blo 1707054 3243557 := bbase (se 4 (by rfl) ⟨304083, by rfl⟩ : syracuseStep 3243557 = 608167) (by norm_num)
theorem B3841613 : Blo 1707054 3841613 := bbase (se 3 (by rfl) ⟨720302, by rfl⟩ : syracuseStep 3841613 = 1440605) (by norm_num)
theorem B2432605 : Blo 1707054 2432605 := bbase (se 3 (by rfl) ⟨456113, by rfl⟩ : syracuseStep 2432605 = 912227) (by norm_num)
theorem B2883181 : Blo 1707054 2883181 := bbase (se 3 (by rfl) ⟨540596, by rfl⟩ : syracuseStep 2883181 = 1081193) (by norm_num)
theorem B4218493 : Blo 1707054 4218493 := bbase (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) (by norm_num)
theorem B2162305 : Blo 1707054 2162305 := bbase (se 2 (by rfl) ⟨810864, by rfl⟩ : syracuseStep 2162305 = 1621729) (by norm_num)
theorem B3841685 : Blo 1707054 3841685 := bbase (se 6 (by rfl) ⟨90039, by rfl⟩ : syracuseStep 3841685 = 180079) (by norm_num)
theorem B8642213 : Blo 1707054 8642213 := bbase (se 4 (by rfl) ⟨810207, by rfl⟩ : syracuseStep 8642213 = 1620415) (by norm_num)
theorem B5766821 : Blo 1707054 5766821 := bbase (se 4 (by rfl) ⟨540639, by rfl⟩ : syracuseStep 5766821 = 1081279) (by norm_num)
theorem B2735797 : Blo 1707054 2735797 := bbase (se 5 (by rfl) ⟨128240, by rfl⟩ : syracuseStep 2735797 = 256481) (by norm_num)
theorem B3243701 : Blo 1707054 3243701 := bbase (se 5 (by rfl) ⟨152048, by rfl⟩ : syracuseStep 3243701 = 304097) (by norm_num)
theorem B2883269 : Blo 1707054 2883269 := bbase (se 4 (by rfl) ⟨270306, by rfl⟩ : syracuseStep 2883269 = 540613) (by norm_num)
theorem B3841757 : Blo 1707054 3841757 := bbase (se 3 (by rfl) ⟨720329, by rfl⟩ : syracuseStep 3841757 = 1440659) (by norm_num)
theorem B7790357 : Blo 1707054 7790357 := bbase (se 6 (by rfl) ⟨182586, by rfl⟩ : syracuseStep 7790357 = 365173) (by norm_num)
theorem B3841829 : Blo 1707054 3841829 := bbase (se 4 (by rfl) ⟨360171, by rfl⟩ : syracuseStep 3841829 = 720343) (by norm_num)
theorem B2162477 : Blo 1707054 2162477 := bbase (se 3 (by rfl) ⟨405464, by rfl⟩ : syracuseStep 2162477 = 810929) (by norm_num)
theorem B6922037 : Blo 1707054 6922037 := bbase (se 5 (by rfl) ⟨324470, by rfl⟩ : syracuseStep 6922037 = 648941) (by norm_num)
theorem B2883397 : Blo 1707054 2883397 := bbase (se 4 (by rfl) ⟨270318, by rfl⟩ : syracuseStep 2883397 = 540637) (by norm_num)
theorem B4325197 : Blo 1707054 4325197 := bbase (se 3 (by rfl) ⟨810974, by rfl⟩ : syracuseStep 4325197 = 1621949) (by norm_num)
theorem B10944341 : Blo 1707054 10944341 := bbase (se 9 (by rfl) ⟨32063, by rfl⟩ : syracuseStep 10944341 = 64127) (by norm_num)
theorem B2162533 : Blo 1707054 2162533 := bbase (se 4 (by rfl) ⟨202737, by rfl⟩ : syracuseStep 2162533 = 405475) (by norm_num)
theorem B3841901 : Blo 1707054 3841901 := bbase (se 3 (by rfl) ⟨720356, by rfl⟩ : syracuseStep 3841901 = 1440713) (by norm_num)
theorem B3800981 : Blo 1707054 3800981 := bbase (se 6 (by rfl) ⟨89085, by rfl⟩ : syracuseStep 3800981 = 178171) (by norm_num)
theorem B2883485 : Blo 1707054 2883485 := bbase (se 3 (by rfl) ⟨540653, by rfl⟩ : syracuseStep 2883485 = 1081307) (by norm_num)
theorem B3841973 : Blo 1707054 3841973 := bbase (se 5 (by rfl) ⟨180092, by rfl⟩ : syracuseStep 3841973 = 360185) (by norm_num)
theorem B4325309 : Blo 1707054 4325309 := bbase (se 3 (by rfl) ⟨810995, by rfl⟩ : syracuseStep 4325309 = 1621991) (by norm_num)
theorem B2162629 : Blo 1707054 2162629 := bbase (se 4 (by rfl) ⟨202746, by rfl⟩ : syracuseStep 2162629 = 405493) (by norm_num)
theorem B3243989 : Blo 1707054 3243989 := bbase (se 7 (by rfl) ⟨38015, by rfl⟩ : syracuseStep 3243989 = 76031) (by norm_num)
theorem B3842045 : Blo 1707054 3842045 := bbase (se 3 (by rfl) ⟨720383, by rfl⟩ : syracuseStep 3842045 = 1440767) (by norm_num)
theorem B4866065 : Blo 1707054 4866065 := bstep (se 2 (by rfl) ⟨1824774, by rfl⟩ : syracuseStep 4866065 = 3649549) B3649549
theorem B2883667 : Blo 1707054 2883667 := bstep (se 1 (by rfl) ⟨2162750, by rfl⟩ : syracuseStep 2883667 = 4325501) B4325501
theorem B4325521 : Blo 1707054 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B2433169 : Blo 1707054 2433169 := bstep (se 2 (by rfl) ⟨912438, by rfl⟩ : syracuseStep 2433169 = 1824877) B1824877
theorem B3842225 : Blo 1707054 3842225 := bstep (se 2 (by rfl) ⟨1440834, by rfl⟩ : syracuseStep 3842225 = 2881669) B2881669
theorem B3842243 : Blo 1707054 3842243 := bstep (se 1 (by rfl) ⟨2881682, by rfl⟩ : syracuseStep 3842243 = 5763365) B5763365
theorem B4866257 : Blo 1707054 4866257 := bstep (se 2 (by rfl) ⟨1824846, by rfl⟩ : syracuseStep 4866257 = 3649693) B3649693
theorem B2883809 : Blo 1707054 2883809 := bstep (se 2 (by rfl) ⟨1081428, by rfl⟩ : syracuseStep 2883809 = 2162857) B2162857
theorem B4677859 : Blo 1707054 4677859 := bstep (se 1 (by rfl) ⟨3508394, by rfl⟩ : syracuseStep 4677859 = 7016789) B7016789
theorem B2162963 : Blo 1707054 2162963 := bstep (se 1 (by rfl) ⟨1622222, by rfl⟩ : syracuseStep 2162963 = 3244445) B3244445
theorem B5767469 : Blo 1707054 5767469 := bstep (se 3 (by rfl) ⟨1081400, by rfl⟩ : syracuseStep 5767469 = 2162801) B2162801
theorem B5472593 : Blo 1707054 5472593 := bstep (se 2 (by rfl) ⟨2052222, by rfl⟩ : syracuseStep 5472593 = 4104445) B4104445
theorem B3244369 : Blo 1707054 3244369 := bstep (se 2 (by rfl) ⟨1216638, by rfl⟩ : syracuseStep 3244369 = 2433277) B2433277
theorem B2883937 : Blo 1707054 2883937 := bstep (se 2 (by rfl) ⟨1081476, by rfl⟩ : syracuseStep 2883937 = 2162953) B2162953
theorem B12312931 : Blo 1707054 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B5767523 : Blo 1707054 5767523 := bstep (se 1 (by rfl) ⟨4325642, by rfl⟩ : syracuseStep 5767523 = 8651285) B8651285
theorem B2883971 : Blo 1707054 2883971 := bstep (se 1 (by rfl) ⟨2162978, by rfl⟩ : syracuseStep 2883971 = 4325957) B4325957
theorem B4325795 : Blo 1707054 4325795 := bstep (se 1 (by rfl) ⟨3244346, by rfl⟩ : syracuseStep 4325795 = 6488693) B6488693
theorem B19448261 : Blo 1707054 19448261 := bstep (se 4 (by rfl) ⟨1823274, by rfl⟩ : syracuseStep 19448261 = 3646549) B3646549
theorem B6488525 : Blo 1707054 6488525 := bstep (se 3 (by rfl) ⟨1216598, by rfl⟩ : syracuseStep 6488525 = 2433197) B2433197
theorem B3842513 : Blo 1707054 3842513 := bstep (se 2 (by rfl) ⟨1440942, by rfl⟩ : syracuseStep 3842513 = 2881885) B2881885
theorem B6570467 : Blo 1707054 6570467 := bstep (se 1 (by rfl) ⟨4927850, by rfl⟩ : syracuseStep 6570467 = 9855701) B9855701
theorem B3842531 : Blo 1707054 3842531 := bstep (se 1 (by rfl) ⟨2881898, by rfl⟩ : syracuseStep 3842531 = 5763797) B5763797
theorem B3244529 : Blo 1707054 3244529 := bstep (se 2 (by rfl) ⟨1216698, by rfl⟩ : syracuseStep 3244529 = 2433397) B2433397
theorem B2597393 : Blo 1707054 2597393 := bstep (se 2 (by rfl) ⟨974022, by rfl⟩ : syracuseStep 2597393 = 1948045) B1948045
theorem B5472785 : Blo 1707054 5472785 := bstep (se 2 (by rfl) ⟨2052294, by rfl⟩ : syracuseStep 5472785 = 4104589) B4104589
theorem B4325987 : Blo 1707054 4325987 := bstep (se 1 (by rfl) ⟨3244490, by rfl⟩ : syracuseStep 4325987 = 6488981) B6488981
theorem B8643185 : Blo 1707054 8643185 := bstep (se 2 (by rfl) ⟨3241194, by rfl⟩ : syracuseStep 8643185 = 6482389) B6482389
theorem B5767793 : Blo 1707054 5767793 := bstep (se 2 (by rfl) ⟨2162922, by rfl⟩ : syracuseStep 5767793 = 4325845) B4325845
theorem B2736803 : Blo 1707054 2736803 := bstep (se 1 (by rfl) ⟨2052602, by rfl⟩ : syracuseStep 2736803 = 4105205) B4105205
theorem B3842801 : Blo 1707054 3842801 := bstep (se 2 (by rfl) ⟨1441050, by rfl⟩ : syracuseStep 3842801 = 2882101) B2882101
theorem B10388209 : Blo 1707054 10388209 := bstep (se 2 (by rfl) ⟨3895578, by rfl⟩ : syracuseStep 10388209 = 7791157) B7791157
theorem B3842819 : Blo 1707054 3842819 := bstep (se 1 (by rfl) ⟨2882114, by rfl⟩ : syracuseStep 3842819 = 5764229) B5764229
theorem B3646225 : Blo 1707054 3646225 := bstep (se 2 (by rfl) ⟨1367334, by rfl⟩ : syracuseStep 3646225 = 2734669) B2734669
theorem B2737027 : Blo 1707054 2737027 := bstep (se 1 (by rfl) ⟨2052770, by rfl⟩ : syracuseStep 2737027 = 4105541) B4105541
theorem B2737091 : Blo 1707054 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B9733061 : Blo 1707054 9733061 := bstep (se 4 (by rfl) ⟨912474, by rfl⟩ : syracuseStep 9733061 = 1824949) B1824949
theorem B7291853 : Blo 1707054 7291853 := bstep (se 3 (by rfl) ⟨1367222, by rfl⟩ : syracuseStep 7291853 = 2734445) B2734445
theorem B19457009 : Blo 1707054 19457009 := bstep (se 2 (by rfl) ⟨7296378, by rfl⟩ : syracuseStep 19457009 = 14592757) B14592757
theorem B3843089 : Blo 1707054 3843089 := bstep (se 2 (by rfl) ⟨1441158, by rfl⟩ : syracuseStep 3843089 = 2882317) B2882317
theorem B3843107 : Blo 1707054 3843107 := bstep (se 1 (by rfl) ⟨2882330, by rfl⟩ : syracuseStep 3843107 = 5764661) B5764661
theorem B2597923 : Blo 1707054 2597923 := bstep (se 1 (by rfl) ⟨1948442, by rfl⟩ : syracuseStep 2597923 = 3896885) B3896885
theorem B2737219 : Blo 1707054 2737219 := bstep (se 1 (by rfl) ⟨2052914, by rfl⟩ : syracuseStep 2737219 = 4105829) B4105829
theorem B14591117 : Blo 1707054 14591117 := bstep (se 3 (by rfl) ⟨2735834, by rfl⟩ : syracuseStep 14591117 = 5471669) B5471669
theorem B78914837 : Blo 1707054 78914837 := bstep (se 6 (by rfl) ⟨1849566, by rfl⟩ : syracuseStep 78914837 = 3699133) B3699133
theorem B3843377 : Blo 1707054 3843377 := bstep (se 2 (by rfl) ⟨1441266, by rfl⟩ : syracuseStep 3843377 = 2882533) B2882533
theorem B3843395 : Blo 1707054 3843395 := bstep (se 1 (by rfl) ⟨2882546, by rfl⟩ : syracuseStep 3843395 = 5765093) B5765093
theorem B9733517 : Blo 1707054 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B3646883 : Blo 1707054 3646883 := bstep (se 1 (by rfl) ⟨2735162, by rfl⟩ : syracuseStep 3646883 = 5470325) B5470325
theorem B5547523 : Blo 1707054 5547523 := bstep (se 1 (by rfl) ⟨4160642, by rfl⟩ : syracuseStep 5547523 = 8321285) B8321285
theorem B9725453 : Blo 1707054 9725453 := bstep (se 3 (by rfl) ⟨1823522, by rfl⟩ : syracuseStep 9725453 = 3647045) B3647045
theorem B21890573 : Blo 1707054 21890573 := bstep (se 3 (by rfl) ⟨4104482, by rfl⟩ : syracuseStep 21890573 = 8208965) B8208965
theorem B7792163 : Blo 1707054 7792163 := bstep (se 1 (by rfl) ⟨5844122, by rfl⟩ : syracuseStep 7792163 = 11688245) B11688245
theorem B3843665 : Blo 1707054 3843665 := bstep (se 2 (by rfl) ⟨1441374, by rfl⟩ : syracuseStep 3843665 = 2882749) B2882749
theorem B3843683 : Blo 1707054 3843683 := bstep (se 1 (by rfl) ⟨2882762, by rfl⟩ : syracuseStep 3843683 = 5765525) B5765525
theorem B11691661 : Blo 1707054 11691661 := bstep (se 3 (by rfl) ⟨2192186, by rfl⟩ : syracuseStep 11691661 = 4384373) B4384373
theorem B3843953 : Blo 1707054 3843953 := bstep (se 2 (by rfl) ⟨1441482, by rfl⟩ : syracuseStep 3843953 = 2882965) B2882965
theorem B13854577 : Blo 1707054 13854577 := bstep (se 2 (by rfl) ⟨5195466, by rfl⟩ : syracuseStep 13854577 = 10390933) B10390933
theorem B3843971 : Blo 1707054 3843971 := bstep (se 1 (by rfl) ⟨2882978, by rfl⟩ : syracuseStep 3843971 = 5765957) B5765957
theorem B5408657 : Blo 1707054 5408657 := bstep (se 2 (by rfl) ⟨2028246, by rfl⟩ : syracuseStep 5408657 = 4056493) B4056493
theorem B8644643 : Blo 1707054 8644643 := bstep (se 1 (by rfl) ⟨6483482, by rfl⟩ : syracuseStep 8644643 = 12966965) B12966965
theorem B2107507 : Blo 1707054 2107507 := bstep (se 1 (by rfl) ⟨1580630, by rfl⟩ : syracuseStep 2107507 = 3161261) B3161261
theorem B3844241 : Blo 1707054 3844241 := bstep (se 2 (by rfl) ⟨1441590, by rfl⟩ : syracuseStep 3844241 = 2883181) B2883181
theorem B3844259 : Blo 1707054 3844259 := bstep (se 1 (by rfl) ⟨2883194, by rfl⟩ : syracuseStep 3844259 = 5766389) B5766389
theorem B3647729 : Blo 1707054 3647729 := bstep (se 2 (by rfl) ⟨1367898, by rfl⟩ : syracuseStep 3647729 = 2735797) B2735797
theorem B5761421 : Blo 1707054 5761421 := bstep (se 3 (by rfl) ⟨1080266, by rfl⟩ : syracuseStep 5761421 = 2160533) B2160533
theorem B3844529 : Blo 1707054 3844529 := bstep (se 2 (by rfl) ⟨1441698, by rfl⟩ : syracuseStep 3844529 = 2883397) B2883397
theorem B5761475 : Blo 1707054 5761475 := bstep (se 1 (by rfl) ⟨4321106, by rfl⟩ : syracuseStep 5761475 = 8642213) B8642213
theorem B3844547 : Blo 1707054 3844547 := bstep (se 1 (by rfl) ⟨2883410, by rfl⟩ : syracuseStep 3844547 = 5766821) B5766821
theorem B4614691 : Blo 1707054 4614691 := bstep (se 1 (by rfl) ⟨3461018, by rfl⟩ : syracuseStep 4614691 = 6922037) B6922037
theorem B9357893 : Blo 1707054 9357893 := bstep (se 4 (by rfl) ⟨877302, by rfl⟩ : syracuseStep 9357893 = 1754605) B1754605
theorem B2533987 : Blo 1707054 2533987 := bstep (se 1 (by rfl) ⟨1900490, by rfl⟩ : syracuseStep 2533987 = 3800981) B3800981
theorem B5761745 : Blo 1707054 5761745 := bstep (se 2 (by rfl) ⟨2160654, by rfl⟩ : syracuseStep 5761745 = 4321309) B4321309
theorem B3844817 : Blo 1707054 3844817 := bstep (se 2 (by rfl) ⟨1441806, by rfl⟩ : syracuseStep 3844817 = 2883613) B2883613
theorem B3844835 : Blo 1707054 3844835 := bstep (se 1 (by rfl) ⟨2883626, by rfl⟩ : syracuseStep 3844835 = 5767253) B5767253
theorem B5475053 : Blo 1707054 5475053 := bstep (se 3 (by rfl) ⟨1026572, by rfl⟩ : syracuseStep 5475053 = 2053145) B2053145
theorem B20769605 : Blo 1707054 20769605 := bstep (se 4 (by rfl) ⟨1947150, by rfl⟩ : syracuseStep 20769605 = 3894301) B3894301
theorem B8645453 : Blo 1707054 8645453 := bstep (se 3 (by rfl) ⟨1621022, by rfl⟩ : syracuseStep 8645453 = 3242045) B3242045
theorem B13151089 : Blo 1707054 13151089 := bstep (se 2 (by rfl) ⟨4931658, by rfl⟩ : syracuseStep 13151089 = 9863317) B9863317
theorem B3845105 : Blo 1707054 3845105 := bstep (se 2 (by rfl) ⟨1441914, by rfl⟩ : syracuseStep 3845105 = 2883829) B2883829
theorem B3845123 : Blo 1707054 3845123 := bstep (se 1 (by rfl) ⟨2883842, by rfl⟩ : syracuseStep 3845123 = 5767685) B5767685
theorem B1707059 : Blo 1707054 1707059 := bstep (se 1 (by rfl) ⟨1280294, by rfl⟩ : syracuseStep 1707059 = 2560589) B2560589
theorem B1707075 : Blo 1707054 1707075 := bstep (se 1 (by rfl) ⟨1280306, by rfl⟩ : syracuseStep 1707075 = 2560613) B2560613
theorem B1707091 : Blo 1707054 1707091 := bstep (se 1 (by rfl) ⟨1280318, by rfl⟩ : syracuseStep 1707091 = 2560637) B2560637
theorem B1707107 : Blo 1707054 1707107 := bstep (se 1 (by rfl) ⟨1280330, by rfl⟩ : syracuseStep 1707107 = 2560661) B2560661
theorem B11095139 : Blo 1707054 11095139 := bstep (se 1 (by rfl) ⟨8321354, by rfl⟩ : syracuseStep 11095139 = 16642709) B16642709
theorem B1707123 : Blo 1707054 1707123 := bstep (se 1 (by rfl) ⟨1280342, by rfl⟩ : syracuseStep 1707123 = 2560685) B2560685
theorem B1707139 : Blo 1707054 1707139 := bstep (se 1 (by rfl) ⟨1280354, by rfl⟩ : syracuseStep 1707139 = 2560709) B2560709
theorem B1707155 : Blo 1707054 1707155 := bstep (se 1 (by rfl) ⟨1280366, by rfl⟩ : syracuseStep 1707155 = 2560733) B2560733
theorem B1707171 : Blo 1707054 1707171 := bstep (se 1 (by rfl) ⟨1280378, by rfl⟩ : syracuseStep 1707171 = 2560757) B2560757
theorem B7023779 : Blo 1707054 7023779 := bstep (se 1 (by rfl) ⟨5267834, by rfl⟩ : syracuseStep 7023779 = 10535669) B10535669
theorem B1707187 : Blo 1707054 1707187 := bstep (se 1 (by rfl) ⟨1280390, by rfl⟩ : syracuseStep 1707187 = 2560781) B2560781
theorem B1707203 : Blo 1707054 1707203 := bstep (se 1 (by rfl) ⟨1280402, by rfl⟩ : syracuseStep 1707203 = 2560805) B2560805
theorem B6483149 : Blo 1707054 6483149 := bstep (se 3 (by rfl) ⟨1215590, by rfl⟩ : syracuseStep 6483149 = 2431181) B2431181
theorem B1707219 : Blo 1707054 1707219 := bstep (se 1 (by rfl) ⟨1280414, by rfl⟩ : syracuseStep 1707219 = 2560829) B2560829
theorem B1707235 : Blo 1707054 1707235 := bstep (se 1 (by rfl) ⟨1280426, by rfl⟩ : syracuseStep 1707235 = 2560853) B2560853
theorem B5762285 : Blo 1707054 5762285 := bstep (se 3 (by rfl) ⟨1080428, by rfl⟩ : syracuseStep 5762285 = 2160857) B2160857
theorem B1707251 : Blo 1707054 1707251 := bstep (se 1 (by rfl) ⟨1280438, by rfl⟩ : syracuseStep 1707251 = 2560877) B2560877
theorem B1707267 : Blo 1707054 1707267 := bstep (se 1 (by rfl) ⟨1280450, by rfl⟩ : syracuseStep 1707267 = 2560901) B2560901
theorem B1707283 : Blo 1707054 1707283 := bstep (se 1 (by rfl) ⟨1280462, by rfl⟩ : syracuseStep 1707283 = 2560925) B2560925
theorem B1707299 : Blo 1707054 1707299 := bstep (se 1 (by rfl) ⟨1280474, by rfl⟩ : syracuseStep 1707299 = 2560949) B2560949
theorem B5762339 : Blo 1707054 5762339 := bstep (se 1 (by rfl) ⟨4321754, by rfl⟩ : syracuseStep 5762339 = 8643509) B8643509
theorem B1707315 : Blo 1707054 1707315 := bstep (se 1 (by rfl) ⟨1280486, by rfl⟩ : syracuseStep 1707315 = 2560973) B2560973
theorem B1707331 : Blo 1707054 1707331 := bstep (se 1 (by rfl) ⟨1280498, by rfl⟩ : syracuseStep 1707331 = 2560997) B2560997
theorem B1707347 : Blo 1707054 1707347 := bstep (se 1 (by rfl) ⟨1280510, by rfl⟩ : syracuseStep 1707347 = 2561021) B2561021
theorem B1707363 : Blo 1707054 1707363 := bstep (se 1 (by rfl) ⟨1280522, by rfl⟩ : syracuseStep 1707363 = 2561045) B2561045
theorem B1707379 : Blo 1707054 1707379 := bstep (se 1 (by rfl) ⟨1280534, by rfl⟩ : syracuseStep 1707379 = 2561069) B2561069
theorem B1707395 : Blo 1707054 1707395 := bstep (se 1 (by rfl) ⟨1280546, by rfl⟩ : syracuseStep 1707395 = 2561093) B2561093
theorem B3288451 : Blo 1707054 3288451 := bstep (se 1 (by rfl) ⟨2466338, by rfl⟩ : syracuseStep 3288451 = 4932677) B4932677
theorem B1707411 : Blo 1707054 1707411 := bstep (se 1 (by rfl) ⟨1280558, by rfl⟩ : syracuseStep 1707411 = 2561117) B2561117
theorem B1707427 : Blo 1707054 1707427 := bstep (se 1 (by rfl) ⟨1280570, by rfl⟩ : syracuseStep 1707427 = 2561141) B2561141
theorem B1707443 : Blo 1707054 1707443 := bstep (se 1 (by rfl) ⟨1280582, by rfl⟩ : syracuseStep 1707443 = 2561165) B2561165
theorem B1920451 : Blo 1707054 1920451 := bstep (se 1 (by rfl) ⟨1440338, by rfl⟩ : syracuseStep 1920451 = 2880677) B2880677
theorem B1707459 : Blo 1707054 1707459 := bstep (se 1 (by rfl) ⟨1280594, by rfl⟩ : syracuseStep 1707459 = 2561189) B2561189
theorem B10939853 : Blo 1707054 10939853 := bstep (se 3 (by rfl) ⟨2051222, by rfl⟩ : syracuseStep 10939853 = 4102445) B4102445
theorem B1707475 : Blo 1707054 1707475 := bstep (se 1 (by rfl) ⟨1280606, by rfl⟩ : syracuseStep 1707475 = 2561213) B2561213
theorem B1707491 : Blo 1707054 1707491 := bstep (se 1 (by rfl) ⟨1280618, by rfl⟩ : syracuseStep 1707491 = 2561237) B2561237
theorem B1707507 : Blo 1707054 1707507 := bstep (se 1 (by rfl) ⟨1280630, by rfl⟩ : syracuseStep 1707507 = 2561261) B2561261
theorem B1707523 : Blo 1707054 1707523 := bstep (se 1 (by rfl) ⟨1280642, by rfl⟩ : syracuseStep 1707523 = 2561285) B2561285
theorem B1707539 : Blo 1707054 1707539 := bstep (se 1 (by rfl) ⟨1280654, by rfl⟩ : syracuseStep 1707539 = 2561309) B2561309
theorem B1707555 : Blo 1707054 1707555 := bstep (se 1 (by rfl) ⟨1280666, by rfl⟩ : syracuseStep 1707555 = 2561333) B2561333
theorem B5762609 : Blo 1707054 5762609 := bstep (se 2 (by rfl) ⟨2160978, by rfl⟩ : syracuseStep 5762609 = 4321957) B4321957
theorem B1707571 : Blo 1707054 1707571 := bstep (se 1 (by rfl) ⟨1280678, by rfl⟩ : syracuseStep 1707571 = 2561357) B2561357
theorem B1707587 : Blo 1707054 1707587 := bstep (se 1 (by rfl) ⟨1280690, by rfl⟩ : syracuseStep 1707587 = 2561381) B2561381
theorem B1920595 : Blo 1707054 1920595 := bstep (se 1 (by rfl) ⟨1440446, by rfl⟩ : syracuseStep 1920595 = 2880893) B2880893
theorem B1707603 : Blo 1707054 1707603 := bstep (se 1 (by rfl) ⟨1280702, by rfl⟩ : syracuseStep 1707603 = 2561405) B2561405
theorem B1707619 : Blo 1707054 1707619 := bstep (se 1 (by rfl) ⟨1280714, by rfl⟩ : syracuseStep 1707619 = 2561429) B2561429
theorem B1707635 : Blo 1707054 1707635 := bstep (se 1 (by rfl) ⟨1280726, by rfl⟩ : syracuseStep 1707635 = 2561453) B2561453
theorem B1707651 : Blo 1707054 1707651 := bstep (se 1 (by rfl) ⟨1280738, by rfl⟩ : syracuseStep 1707651 = 2561477) B2561477
theorem B1707667 : Blo 1707054 1707667 := bstep (se 1 (by rfl) ⟨1280750, by rfl⟩ : syracuseStep 1707667 = 2561501) B2561501
theorem B1707683 : Blo 1707054 1707683 := bstep (se 1 (by rfl) ⟨1280762, by rfl⟩ : syracuseStep 1707683 = 2561525) B2561525
theorem B10948259 : Blo 1707054 10948259 := bstep (se 1 (by rfl) ⟨8211194, by rfl⟩ : syracuseStep 10948259 = 16422389) B16422389
theorem B1707699 : Blo 1707054 1707699 := bstep (se 1 (by rfl) ⟨1280774, by rfl⟩ : syracuseStep 1707699 = 2561549) B2561549
theorem B1707715 : Blo 1707054 1707715 := bstep (se 1 (by rfl) ⟨1280786, by rfl⟩ : syracuseStep 1707715 = 2561573) B2561573
theorem B9727685 : Blo 1707054 9727685 := bstep (se 4 (by rfl) ⟨911970, by rfl⟩ : syracuseStep 9727685 = 1823941) B1823941
theorem B2772689 : Blo 1707054 2772689 := bstep (se 2 (by rfl) ⟨1039758, by rfl⟩ : syracuseStep 2772689 = 2079517) B2079517
theorem B1707731 : Blo 1707054 1707731 := bstep (se 1 (by rfl) ⟨1280798, by rfl⟩ : syracuseStep 1707731 = 2561597) B2561597
theorem B2920145 : Blo 1707054 2920145 := bstep (se 2 (by rfl) ⟨1095054, by rfl⟩ : syracuseStep 2920145 = 2190109) B2190109
theorem B1920739 : Blo 1707054 1920739 := bstep (se 1 (by rfl) ⟨1440554, by rfl⟩ : syracuseStep 1920739 = 2881109) B2881109
theorem B1707747 : Blo 1707054 1707747 := bstep (se 1 (by rfl) ⟨1280810, by rfl⟩ : syracuseStep 1707747 = 2561621) B2561621
theorem B1707763 : Blo 1707054 1707763 := bstep (se 1 (by rfl) ⟨1280822, by rfl⟩ : syracuseStep 1707763 = 2561645) B2561645
theorem B2633473 : Blo 1707054 2633473 := bstep (se 2 (by rfl) ⟨987552, by rfl⟩ : syracuseStep 2633473 = 1975105) B1975105
theorem B1707779 : Blo 1707054 1707779 := bstep (se 1 (by rfl) ⟨1280834, by rfl⟩ : syracuseStep 1707779 = 2561669) B2561669
theorem B1707795 : Blo 1707054 1707795 := bstep (se 1 (by rfl) ⟨1280846, by rfl⟩ : syracuseStep 1707795 = 2561693) B2561693
theorem B1707811 : Blo 1707054 1707811 := bstep (se 1 (by rfl) ⟨1280858, by rfl⟩ : syracuseStep 1707811 = 2561717) B2561717
theorem B1707827 : Blo 1707054 1707827 := bstep (se 1 (by rfl) ⟨1280870, by rfl⟩ : syracuseStep 1707827 = 2561741) B2561741
theorem B1707843 : Blo 1707054 1707843 := bstep (se 1 (by rfl) ⟨1280882, by rfl⟩ : syracuseStep 1707843 = 2561765) B2561765
theorem B1707859 : Blo 1707054 1707859 := bstep (se 1 (by rfl) ⟨1280894, by rfl⟩ : syracuseStep 1707859 = 2561789) B2561789
theorem B1707875 : Blo 1707054 1707875 := bstep (se 1 (by rfl) ⟨1280906, by rfl⟩ : syracuseStep 1707875 = 2561813) B2561813
theorem B1920883 : Blo 1707054 1920883 := bstep (se 1 (by rfl) ⟨1440662, by rfl⟩ : syracuseStep 1920883 = 2881325) B2881325
theorem B1707891 : Blo 1707054 1707891 := bstep (se 1 (by rfl) ⟨1280918, by rfl⟩ : syracuseStep 1707891 = 2561837) B2561837
theorem B1707907 : Blo 1707054 1707907 := bstep (se 1 (by rfl) ⟨1280930, by rfl⟩ : syracuseStep 1707907 = 2561861) B2561861
theorem B10383245 : Blo 1707054 10383245 := bstep (se 3 (by rfl) ⟨1946858, by rfl⟩ : syracuseStep 10383245 = 3893717) B3893717
theorem B11243405 : Blo 1707054 11243405 := bstep (se 3 (by rfl) ⟨2108138, by rfl⟩ : syracuseStep 11243405 = 4216277) B4216277
theorem B1707923 : Blo 1707054 1707923 := bstep (se 1 (by rfl) ⟨1280942, by rfl⟩ : syracuseStep 1707923 = 2561885) B2561885
theorem B2051987 : Blo 1707054 2051987 := bstep (se 1 (by rfl) ⟨1538990, by rfl⟩ : syracuseStep 2051987 = 3077981) B3077981
theorem B1707939 : Blo 1707054 1707939 := bstep (se 1 (by rfl) ⟨1280954, by rfl⟩ : syracuseStep 1707939 = 2561909) B2561909
theorem B1707955 : Blo 1707054 1707955 := bstep (se 1 (by rfl) ⟨1280966, by rfl⟩ : syracuseStep 1707955 = 2561933) B2561933
theorem B1707971 : Blo 1707054 1707971 := bstep (se 1 (by rfl) ⟨1280978, by rfl⟩ : syracuseStep 1707971 = 2561957) B2561957
theorem B1707987 : Blo 1707054 1707987 := bstep (se 1 (by rfl) ⟨1280990, by rfl⟩ : syracuseStep 1707987 = 2561981) B2561981
theorem B1708003 : Blo 1707054 1708003 := bstep (se 1 (by rfl) ⟨1281002, by rfl⟩ : syracuseStep 1708003 = 2562005) B2562005
theorem B27709411 : Blo 1707054 27709411 := bstep (se 1 (by rfl) ⟨20782058, by rfl⟩ : syracuseStep 27709411 = 41564117) B41564117
theorem B1708019 : Blo 1707054 1708019 := bstep (se 1 (by rfl) ⟨1281014, by rfl⟩ : syracuseStep 1708019 = 2562029) B2562029
theorem B1921027 : Blo 1707054 1921027 := bstep (se 1 (by rfl) ⟨1440770, by rfl⟩ : syracuseStep 1921027 = 2881541) B2881541
theorem B1708035 : Blo 1707054 1708035 := bstep (se 1 (by rfl) ⟨1281026, by rfl⟩ : syracuseStep 1708035 = 2562053) B2562053
theorem B1708051 : Blo 1707054 1708051 := bstep (se 1 (by rfl) ⟨1281038, by rfl⟩ : syracuseStep 1708051 = 2562077) B2562077
theorem B1708067 : Blo 1707054 1708067 := bstep (se 1 (by rfl) ⟨1281050, by rfl⟩ : syracuseStep 1708067 = 2562101) B2562101
theorem B1708083 : Blo 1707054 1708083 := bstep (se 1 (by rfl) ⟨1281062, by rfl⟩ : syracuseStep 1708083 = 2562125) B2562125
theorem B1708099 : Blo 1707054 1708099 := bstep (se 1 (by rfl) ⟨1281074, by rfl⟩ : syracuseStep 1708099 = 2562149) B2562149
theorem B5763149 : Blo 1707054 5763149 := bstep (se 3 (by rfl) ⟨1080590, by rfl⟩ : syracuseStep 5763149 = 2161181) B2161181
theorem B1708115 : Blo 1707054 1708115 := bstep (se 1 (by rfl) ⟨1281086, by rfl⟩ : syracuseStep 1708115 = 2562173) B2562173
theorem B4616291 : Blo 1707054 4616291 := bstep (se 1 (by rfl) ⟨3462218, by rfl⟩ : syracuseStep 4616291 = 6924437) B6924437
theorem B1708131 : Blo 1707054 1708131 := bstep (se 1 (by rfl) ⟨1281098, by rfl⟩ : syracuseStep 1708131 = 2562197) B2562197
theorem B10678385 : Blo 1707054 10678385 := bstep (se 2 (by rfl) ⟨4004394, by rfl⟩ : syracuseStep 10678385 = 8008789) B8008789
theorem B1708147 : Blo 1707054 1708147 := bstep (se 1 (by rfl) ⟨1281110, by rfl⟩ : syracuseStep 1708147 = 2562221) B2562221
theorem B5763203 : Blo 1707054 5763203 := bstep (se 1 (by rfl) ⟨4322402, by rfl⟩ : syracuseStep 5763203 = 8644805) B8644805
theorem B1708163 : Blo 1707054 1708163 := bstep (se 1 (by rfl) ⟨1281122, by rfl⟩ : syracuseStep 1708163 = 2562245) B2562245
theorem B8204429 : Blo 1707054 8204429 := bstep (se 3 (by rfl) ⟨1538330, by rfl⟩ : syracuseStep 8204429 = 3076661) B3076661
theorem B1921171 : Blo 1707054 1921171 := bstep (se 1 (by rfl) ⟨1440878, by rfl⟩ : syracuseStep 1921171 = 2881757) B2881757
theorem B1708179 : Blo 1707054 1708179 := bstep (se 1 (by rfl) ⟨1281134, by rfl⟩ : syracuseStep 1708179 = 2562269) B2562269
theorem B1708195 : Blo 1707054 1708195 := bstep (se 1 (by rfl) ⟨1281146, by rfl⟩ : syracuseStep 1708195 = 2562293) B2562293
theorem B1708211 : Blo 1707054 1708211 := bstep (se 1 (by rfl) ⟨1281158, by rfl⟩ : syracuseStep 1708211 = 2562317) B2562317
theorem B1708227 : Blo 1707054 1708227 := bstep (se 1 (by rfl) ⟨1281170, by rfl⟩ : syracuseStep 1708227 = 2562341) B2562341
theorem B1708243 : Blo 1707054 1708243 := bstep (se 1 (by rfl) ⟨1281182, by rfl⟩ : syracuseStep 1708243 = 2562365) B2562365
theorem B1708259 : Blo 1707054 1708259 := bstep (se 1 (by rfl) ⟨1281194, by rfl⟩ : syracuseStep 1708259 = 2562389) B2562389
theorem B27709667 : Blo 1707054 27709667 := bstep (se 1 (by rfl) ⟨20782250, by rfl⟩ : syracuseStep 27709667 = 41564501) B41564501
theorem B1708275 : Blo 1707054 1708275 := bstep (se 1 (by rfl) ⟨1281206, by rfl⟩ : syracuseStep 1708275 = 2562413) B2562413
theorem B1708291 : Blo 1707054 1708291 := bstep (se 1 (by rfl) ⟨1281218, by rfl⟩ : syracuseStep 1708291 = 2562437) B2562437
theorem B10391813 : Blo 1707054 10391813 := bstep (se 4 (by rfl) ⟨974232, by rfl⟩ : syracuseStep 10391813 = 1948465) B1948465
theorem B1708307 : Blo 1707054 1708307 := bstep (se 1 (by rfl) ⟨1281230, by rfl⟩ : syracuseStep 1708307 = 2562461) B2562461
theorem B1921315 : Blo 1707054 1921315 := bstep (se 1 (by rfl) ⟨1440986, by rfl⟩ : syracuseStep 1921315 = 2881973) B2881973
theorem B1708323 : Blo 1707054 1708323 := bstep (se 1 (by rfl) ⟨1281242, by rfl⟩ : syracuseStep 1708323 = 2562485) B2562485
theorem B1708339 : Blo 1707054 1708339 := bstep (se 1 (by rfl) ⟨1281254, by rfl⟩ : syracuseStep 1708339 = 2562509) B2562509
theorem B1708355 : Blo 1707054 1708355 := bstep (se 1 (by rfl) ⟨1281266, by rfl⟩ : syracuseStep 1708355 = 2562533) B2562533
theorem B1708371 : Blo 1707054 1708371 := bstep (se 1 (by rfl) ⟨1281278, by rfl⟩ : syracuseStep 1708371 = 2562557) B2562557
theorem B1708387 : Blo 1707054 1708387 := bstep (se 1 (by rfl) ⟨1281290, by rfl⟩ : syracuseStep 1708387 = 2562581) B2562581
theorem B9728369 : Blo 1707054 9728369 := bstep (se 2 (by rfl) ⟨3648138, by rfl⟩ : syracuseStep 9728369 = 7296277) B7296277
theorem B1708403 : Blo 1707054 1708403 := bstep (se 1 (by rfl) ⟨1281302, by rfl⟩ : syracuseStep 1708403 = 2562605) B2562605
theorem B4862339 : Blo 1707054 4862339 := bstep (se 1 (by rfl) ⟨3646754, by rfl⟩ : syracuseStep 4862339 = 7293509) B7293509
theorem B1708419 : Blo 1707054 1708419 := bstep (se 1 (by rfl) ⟨1281314, by rfl⟩ : syracuseStep 1708419 = 2562629) B2562629
theorem B5763473 : Blo 1707054 5763473 := bstep (se 2 (by rfl) ⟨2161302, by rfl⟩ : syracuseStep 5763473 = 4322605) B4322605
theorem B1708435 : Blo 1707054 1708435 := bstep (se 1 (by rfl) ⟨1281326, by rfl⟩ : syracuseStep 1708435 = 2562653) B2562653
theorem B1708451 : Blo 1707054 1708451 := bstep (se 1 (by rfl) ⟨1281338, by rfl⟩ : syracuseStep 1708451 = 2562677) B2562677
theorem B1921459 : Blo 1707054 1921459 := bstep (se 1 (by rfl) ⟨1441094, by rfl⟩ : syracuseStep 1921459 = 2882189) B2882189
theorem B1708467 : Blo 1707054 1708467 := bstep (se 1 (by rfl) ⟨1281350, by rfl⟩ : syracuseStep 1708467 = 2562701) B2562701
theorem B1708483 : Blo 1707054 1708483 := bstep (se 1 (by rfl) ⟨1281362, by rfl⟩ : syracuseStep 1708483 = 2562725) B2562725
theorem B4321745 : Blo 1707054 4321745 := bstep (se 2 (by rfl) ⟨1620654, by rfl⟩ : syracuseStep 4321745 = 3241309) B3241309
theorem B1708499 : Blo 1707054 1708499 := bstep (se 1 (by rfl) ⟨1281374, by rfl⟩ : syracuseStep 1708499 = 2562749) B2562749
theorem B1708515 : Blo 1707054 1708515 := bstep (se 1 (by rfl) ⟨1281386, by rfl⟩ : syracuseStep 1708515 = 2562773) B2562773
theorem B1708531 : Blo 1707054 1708531 := bstep (se 1 (by rfl) ⟨1281398, by rfl⟩ : syracuseStep 1708531 = 2562797) B2562797
theorem B4321795 : Blo 1707054 4321795 := bstep (se 1 (by rfl) ⟨3241346, by rfl⟩ : syracuseStep 4321795 = 6482693) B6482693
theorem B1708547 : Blo 1707054 1708547 := bstep (se 1 (by rfl) ⟨1281410, by rfl⟩ : syracuseStep 1708547 = 2562821) B2562821
theorem B1708563 : Blo 1707054 1708563 := bstep (se 1 (by rfl) ⟨1281422, by rfl⟩ : syracuseStep 1708563 = 2562845) B2562845
theorem B1708579 : Blo 1707054 1708579 := bstep (se 1 (by rfl) ⟨1281434, by rfl⟩ : syracuseStep 1708579 = 2562869) B2562869
theorem B1708595 : Blo 1707054 1708595 := bstep (se 1 (by rfl) ⟨1281446, by rfl⟩ : syracuseStep 1708595 = 2562893) B2562893
theorem B3461699 : Blo 1707054 3461699 := bstep (se 1 (by rfl) ⟨2596274, by rfl⟩ : syracuseStep 3461699 = 5192549) B5192549
theorem B1921603 : Blo 1707054 1921603 := bstep (se 1 (by rfl) ⟨1441202, by rfl⟩ : syracuseStep 1921603 = 2882405) B2882405
theorem B1708611 : Blo 1707054 1708611 := bstep (se 1 (by rfl) ⟨1281458, by rfl⟩ : syracuseStep 1708611 = 2562917) B2562917
theorem B2560595 : Blo 1707054 2560595 := bstep (se 1 (by rfl) ⟨1920446, by rfl⟩ : syracuseStep 2560595 = 3840893) B3840893
theorem B1708627 : Blo 1707054 1708627 := bstep (se 1 (by rfl) ⟨1281470, by rfl⟩ : syracuseStep 1708627 = 2562941) B2562941
theorem B1708643 : Blo 1707054 1708643 := bstep (se 1 (by rfl) ⟨1281482, by rfl⟩ : syracuseStep 1708643 = 2562965) B2562965
theorem B2560625 : Blo 1707054 2560625 := bstep (se 2 (by rfl) ⟨960234, by rfl⟩ : syracuseStep 2560625 = 1920469) B1920469
theorem B11686513 : Blo 1707054 11686513 := bstep (se 2 (by rfl) ⟨4382442, by rfl⟩ : syracuseStep 11686513 = 8764885) B8764885
theorem B1708659 : Blo 1707054 1708659 := bstep (se 1 (by rfl) ⟨1281494, by rfl⟩ : syracuseStep 1708659 = 2562989) B2562989
theorem B2560643 : Blo 1707054 2560643 := bstep (se 1 (by rfl) ⟨1920482, by rfl⟩ : syracuseStep 2560643 = 3840965) B3840965
theorem B1708675 : Blo 1707054 1708675 := bstep (se 1 (by rfl) ⟨1281506, by rfl⟩ : syracuseStep 1708675 = 2563013) B2563013
theorem B4321937 : Blo 1707054 4321937 := bstep (se 2 (by rfl) ⟨1620726, by rfl⟩ : syracuseStep 4321937 = 3241453) B3241453
theorem B1708691 : Blo 1707054 1708691 := bstep (se 1 (by rfl) ⟨1281518, by rfl⟩ : syracuseStep 1708691 = 2563037) B2563037
theorem B2560673 : Blo 1707054 2560673 := bstep (se 2 (by rfl) ⟨960252, by rfl⟩ : syracuseStep 2560673 = 1920505) B1920505
theorem B1708707 : Blo 1707054 1708707 := bstep (se 1 (by rfl) ⟨1281530, by rfl⟩ : syracuseStep 1708707 = 2563061) B2563061
theorem B2560691 : Blo 1707054 2560691 := bstep (se 1 (by rfl) ⟨1920518, by rfl⟩ : syracuseStep 2560691 = 3841037) B3841037
theorem B1708723 : Blo 1707054 1708723 := bstep (se 1 (by rfl) ⟨1281542, by rfl⟩ : syracuseStep 1708723 = 2563085) B2563085
theorem B1708739 : Blo 1707054 1708739 := bstep (se 1 (by rfl) ⟨1281554, by rfl⟩ : syracuseStep 1708739 = 2563109) B2563109
theorem B2560721 : Blo 1707054 2560721 := bstep (se 2 (by rfl) ⟨960270, by rfl⟩ : syracuseStep 2560721 = 1920541) B1920541
theorem B1921747 : Blo 1707054 1921747 := bstep (se 1 (by rfl) ⟨1441310, by rfl⟩ : syracuseStep 1921747 = 2882621) B2882621
theorem B1708755 : Blo 1707054 1708755 := bstep (se 1 (by rfl) ⟨1281566, by rfl⟩ : syracuseStep 1708755 = 2563133) B2563133
theorem B2560739 : Blo 1707054 2560739 := bstep (se 1 (by rfl) ⟨1920554, by rfl⟩ : syracuseStep 2560739 = 3841109) B3841109
theorem B1708771 : Blo 1707054 1708771 := bstep (se 1 (by rfl) ⟨1281578, by rfl⟩ : syracuseStep 1708771 = 2563157) B2563157
theorem B1708787 : Blo 1707054 1708787 := bstep (se 1 (by rfl) ⟨1281590, by rfl⟩ : syracuseStep 1708787 = 2563181) B2563181
theorem B2560769 : Blo 1707054 2560769 := bstep (se 2 (by rfl) ⟨960288, by rfl⟩ : syracuseStep 2560769 = 1920577) B1920577
theorem B1708803 : Blo 1707054 1708803 := bstep (se 1 (by rfl) ⟨1281602, by rfl⟩ : syracuseStep 1708803 = 2563205) B2563205
theorem B2560787 : Blo 1707054 2560787 := bstep (se 1 (by rfl) ⟨1920590, by rfl⟩ : syracuseStep 2560787 = 3841181) B3841181
theorem B1708819 : Blo 1707054 1708819 := bstep (se 1 (by rfl) ⟨1281614, by rfl⟩ : syracuseStep 1708819 = 2563229) B2563229
theorem B3240739 : Blo 1707054 3240739 := bstep (se 1 (by rfl) ⟨2430554, by rfl⟩ : syracuseStep 3240739 = 4861109) B4861109
theorem B1708835 : Blo 1707054 1708835 := bstep (se 1 (by rfl) ⟨1281626, by rfl⟩ : syracuseStep 1708835 = 2563253) B2563253
theorem B2560817 : Blo 1707054 2560817 := bstep (se 2 (by rfl) ⟨960306, by rfl⟩ : syracuseStep 2560817 = 1920613) B1920613
theorem B1708851 : Blo 1707054 1708851 := bstep (se 1 (by rfl) ⟨1281638, by rfl⟩ : syracuseStep 1708851 = 2563277) B2563277
theorem B2560835 : Blo 1707054 2560835 := bstep (se 1 (by rfl) ⟨1920626, by rfl⟩ : syracuseStep 2560835 = 3841253) B3841253
theorem B1708867 : Blo 1707054 1708867 := bstep (se 1 (by rfl) ⟨1281650, by rfl⟩ : syracuseStep 1708867 = 2563301) B2563301
theorem B3240785 : Blo 1707054 3240785 := bstep (se 2 (by rfl) ⟨1215294, by rfl⟩ : syracuseStep 3240785 = 2430589) B2430589
theorem B5624657 : Blo 1707054 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B1708883 : Blo 1707054 1708883 := bstep (se 1 (by rfl) ⟨1281662, by rfl⟩ : syracuseStep 1708883 = 2563325) B2563325
theorem B2560865 : Blo 1707054 2560865 := bstep (se 2 (by rfl) ⟨960324, by rfl⟩ : syracuseStep 2560865 = 1920649) B1920649
theorem B1921891 : Blo 1707054 1921891 := bstep (se 1 (by rfl) ⟨1441418, by rfl⟩ : syracuseStep 1921891 = 2882837) B2882837
theorem B1708899 : Blo 1707054 1708899 := bstep (se 1 (by rfl) ⟨1281674, by rfl⟩ : syracuseStep 1708899 = 2563349) B2563349
theorem B10949489 : Blo 1707054 10949489 := bstep (se 2 (by rfl) ⟨4106058, by rfl⟩ : syracuseStep 10949489 = 8212117) B8212117
theorem B2560883 : Blo 1707054 2560883 := bstep (se 1 (by rfl) ⟨1920662, by rfl⟩ : syracuseStep 2560883 = 3841325) B3841325
theorem B1708915 : Blo 1707054 1708915 := bstep (se 1 (by rfl) ⟨1281686, by rfl⟩ : syracuseStep 1708915 = 2563373) B2563373
theorem B4617091 : Blo 1707054 4617091 := bstep (se 1 (by rfl) ⟨3462818, by rfl⟩ : syracuseStep 4617091 = 6925637) B6925637
theorem B1708931 : Blo 1707054 1708931 := bstep (se 1 (by rfl) ⟨1281698, by rfl⟩ : syracuseStep 1708931 = 2563397) B2563397
theorem B16421773 : Blo 1707054 16421773 := bstep (se 3 (by rfl) ⟨3079082, by rfl⟩ : syracuseStep 16421773 = 6158165) B6158165
theorem B2560913 : Blo 1707054 2560913 := bstep (se 2 (by rfl) ⟨960342, by rfl⟩ : syracuseStep 2560913 = 1920685) B1920685
theorem B1708947 : Blo 1707054 1708947 := bstep (se 1 (by rfl) ⟨1281710, by rfl⟩ : syracuseStep 1708947 = 2563421) B2563421
theorem B2560931 : Blo 1707054 2560931 := bstep (se 1 (by rfl) ⟨1920698, by rfl⟩ : syracuseStep 2560931 = 3841397) B3841397
theorem B1708963 : Blo 1707054 1708963 := bstep (se 1 (by rfl) ⟨1281722, by rfl⟩ : syracuseStep 1708963 = 2563445) B2563445
theorem B5764013 : Blo 1707054 5764013 := bstep (se 3 (by rfl) ⟨1080752, by rfl⟩ : syracuseStep 5764013 = 2161505) B2161505
theorem B1708979 : Blo 1707054 1708979 := bstep (se 1 (by rfl) ⟨1281734, by rfl⟩ : syracuseStep 1708979 = 2563469) B2563469
theorem B2560961 : Blo 1707054 2560961 := bstep (se 2 (by rfl) ⟨960360, by rfl⟩ : syracuseStep 2560961 = 1920721) B1920721
theorem B1708995 : Blo 1707054 1708995 := bstep (se 1 (by rfl) ⟨1281746, by rfl⟩ : syracuseStep 1708995 = 2563493) B2563493
theorem B5469133 : Blo 1707054 5469133 := bstep (se 3 (by rfl) ⟨1025462, by rfl⟩ : syracuseStep 5469133 = 2050925) B2050925
theorem B2560979 : Blo 1707054 2560979 := bstep (se 1 (by rfl) ⟨1920734, by rfl⟩ : syracuseStep 2560979 = 3841469) B3841469
theorem B1709011 : Blo 1707054 1709011 := bstep (se 1 (by rfl) ⟨1281758, by rfl⟩ : syracuseStep 1709011 = 2563517) B2563517
theorem B5764067 : Blo 1707054 5764067 := bstep (se 1 (by rfl) ⟨4323050, by rfl⟩ : syracuseStep 5764067 = 8646101) B8646101
theorem B1709027 : Blo 1707054 1709027 := bstep (se 1 (by rfl) ⟨1281770, by rfl⟩ : syracuseStep 1709027 = 2563541) B2563541
theorem B2561009 : Blo 1707054 2561009 := bstep (se 2 (by rfl) ⟨960378, by rfl⟩ : syracuseStep 2561009 = 1920757) B1920757
theorem B1922035 : Blo 1707054 1922035 := bstep (se 1 (by rfl) ⟨1441526, by rfl⟩ : syracuseStep 1922035 = 2883053) B2883053
theorem B1709043 : Blo 1707054 1709043 := bstep (se 1 (by rfl) ⟨1281782, by rfl⟩ : syracuseStep 1709043 = 2563565) B2563565
theorem B2561027 : Blo 1707054 2561027 := bstep (se 1 (by rfl) ⟨1920770, by rfl⟩ : syracuseStep 2561027 = 3841541) B3841541
theorem B2561057 : Blo 1707054 2561057 := bstep (se 2 (by rfl) ⟨960396, by rfl⟩ : syracuseStep 2561057 = 1920793) B1920793
theorem B2561075 : Blo 1707054 2561075 := bstep (se 1 (by rfl) ⟨1920806, by rfl⟩ : syracuseStep 2561075 = 3841613) B3841613
theorem B7894093 : Blo 1707054 7894093 := bstep (se 3 (by rfl) ⟨1480142, by rfl⟩ : syracuseStep 7894093 = 2960285) B2960285
theorem B2561105 : Blo 1707054 2561105 := bstep (se 2 (by rfl) ⟨960414, by rfl⟩ : syracuseStep 2561105 = 1920829) B1920829
theorem B2561123 : Blo 1707054 2561123 := bstep (se 1 (by rfl) ⟨1920842, by rfl⟩ : syracuseStep 2561123 = 3841685) B3841685
theorem B3241073 : Blo 1707054 3241073 := bstep (se 2 (by rfl) ⟨1215402, by rfl⟩ : syracuseStep 3241073 = 2430805) B2430805
theorem B2561153 : Blo 1707054 2561153 := bstep (se 2 (by rfl) ⟨960432, by rfl⟩ : syracuseStep 2561153 = 1920865) B1920865
theorem B1922179 : Blo 1707054 1922179 := bstep (se 1 (by rfl) ⟨1441634, by rfl⟩ : syracuseStep 1922179 = 2883269) B2883269
theorem B2561171 : Blo 1707054 2561171 := bstep (se 1 (by rfl) ⟨1920878, by rfl⟩ : syracuseStep 2561171 = 3841757) B3841757
theorem B4863149 : Blo 1707054 4863149 := bstep (se 3 (by rfl) ⟨911840, by rfl⟩ : syracuseStep 4863149 = 1823681) B1823681
theorem B2561201 : Blo 1707054 2561201 := bstep (se 2 (by rfl) ⟨960450, by rfl⟩ : syracuseStep 2561201 = 1920901) B1920901
theorem B2561219 : Blo 1707054 2561219 := bstep (se 1 (by rfl) ⟨1920914, by rfl⟩ : syracuseStep 2561219 = 3841829) B3841829
theorem B1848515 : Blo 1707054 1848515 := bstep (se 1 (by rfl) ⟨1386386, by rfl⟩ : syracuseStep 1848515 = 2772773) B2772773
theorem B2561249 : Blo 1707054 2561249 := bstep (se 2 (by rfl) ⟨960468, by rfl⟩ : syracuseStep 2561249 = 1920937) B1920937
theorem B7296227 : Blo 1707054 7296227 := bstep (se 1 (by rfl) ⟨5472170, by rfl⟩ : syracuseStep 7296227 = 10944341) B10944341
theorem B12973283 : Blo 1707054 12973283 := bstep (se 1 (by rfl) ⟨9729962, by rfl⟩ : syracuseStep 12973283 = 19459925) B19459925
theorem B5764337 : Blo 1707054 5764337 := bstep (se 2 (by rfl) ⟨2161626, by rfl⟩ : syracuseStep 5764337 = 4323253) B4323253
theorem B2561267 : Blo 1707054 2561267 := bstep (se 1 (by rfl) ⟨1920950, by rfl⟩ : syracuseStep 2561267 = 3841901) B3841901
theorem B13145357 : Blo 1707054 13145357 := bstep (se 3 (by rfl) ⟨2464754, by rfl⟩ : syracuseStep 13145357 = 4929509) B4929509
theorem B6239501 : Blo 1707054 6239501 := bstep (se 3 (by rfl) ⟨1169906, by rfl⟩ : syracuseStep 6239501 = 2339813) B2339813
theorem B2880785 : Blo 1707054 2880785 := bstep (se 2 (by rfl) ⟨1080294, by rfl⟩ : syracuseStep 2880785 = 2160589) B2160589
theorem B2561297 : Blo 1707054 2561297 := bstep (se 2 (by rfl) ⟨960486, by rfl⟩ : syracuseStep 2561297 = 1920973) B1920973
theorem B1922323 : Blo 1707054 1922323 := bstep (se 1 (by rfl) ⟨1441742, by rfl⟩ : syracuseStep 1922323 = 2883485) B2883485
theorem B2561315 : Blo 1707054 2561315 := bstep (se 1 (by rfl) ⟨1920986, by rfl⟩ : syracuseStep 2561315 = 3841973) B3841973
theorem B2561345 : Blo 1707054 2561345 := bstep (se 2 (by rfl) ⟨960504, by rfl⟩ : syracuseStep 2561345 = 1921009) B1921009
theorem B2307409 : Blo 1707054 2307409 := bstep (se 2 (by rfl) ⟨865278, by rfl⟩ : syracuseStep 2307409 = 1730557) B1730557
theorem B2561363 : Blo 1707054 2561363 := bstep (se 1 (by rfl) ⟨1921022, by rfl⟩ : syracuseStep 2561363 = 3842045) B3842045
theorem B4863341 : Blo 1707054 4863341 := bstep (se 3 (by rfl) ⟨911876, by rfl⟩ : syracuseStep 4863341 = 1823753) B1823753
theorem B2561393 : Blo 1707054 2561393 := bstep (se 2 (by rfl) ⟨960522, by rfl⟩ : syracuseStep 2561393 = 1921045) B1921045
theorem B2561411 : Blo 1707054 2561411 := bstep (se 1 (by rfl) ⟨1921058, by rfl⟩ : syracuseStep 2561411 = 3842117) B3842117
theorem B2880913 : Blo 1707054 2880913 := bstep (se 2 (by rfl) ⟨1080342, by rfl⟩ : syracuseStep 2880913 = 2160685) B2160685
theorem B2307475 : Blo 1707054 2307475 := bstep (se 1 (by rfl) ⟨1730606, by rfl⟩ : syracuseStep 2307475 = 3461213) B3461213
theorem B2561441 : Blo 1707054 2561441 := bstep (se 2 (by rfl) ⟨960540, by rfl⟩ : syracuseStep 2561441 = 1921081) B1921081
theorem B1824163 : Blo 1707054 1824163 := bstep (se 1 (by rfl) ⟨1368122, by rfl⟩ : syracuseStep 1824163 = 2736245) B2736245
theorem B1922467 : Blo 1707054 1922467 := bstep (se 1 (by rfl) ⟨1441850, by rfl⟩ : syracuseStep 1922467 = 2883701) B2883701
theorem B2880947 : Blo 1707054 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B2561459 : Blo 1707054 2561459 := bstep (se 1 (by rfl) ⟨1921094, by rfl⟩ : syracuseStep 2561459 = 3842189) B3842189
theorem B2561489 : Blo 1707054 2561489 := bstep (se 2 (by rfl) ⟨960558, by rfl⟩ : syracuseStep 2561489 = 1921117) B1921117
theorem B2561507 : Blo 1707054 2561507 := bstep (se 1 (by rfl) ⟨1921130, by rfl⟩ : syracuseStep 2561507 = 3842261) B3842261
theorem B2561537 : Blo 1707054 2561537 := bstep (se 2 (by rfl) ⟨960576, by rfl⟩ : syracuseStep 2561537 = 1921153) B1921153
theorem B2921987 : Blo 1707054 2921987 := bstep (se 1 (by rfl) ⟨2191490, by rfl⟩ : syracuseStep 2921987 = 4382981) B4382981
theorem B2561555 : Blo 1707054 2561555 := bstep (se 1 (by rfl) ⟨1921166, by rfl⟩ : syracuseStep 2561555 = 3842333) B3842333
theorem B2561585 : Blo 1707054 2561585 := bstep (se 2 (by rfl) ⟨960594, by rfl⟩ : syracuseStep 2561585 = 1921189) B1921189
theorem B2881075 : Blo 1707054 2881075 := bstep (se 1 (by rfl) ⟨2160806, by rfl⟩ : syracuseStep 2881075 = 4321613) B4321613
theorem B1922611 : Blo 1707054 1922611 := bstep (se 1 (by rfl) ⟨1441958, by rfl⟩ : syracuseStep 1922611 = 2883917) B2883917
theorem B5191235 : Blo 1707054 5191235 := bstep (se 1 (by rfl) ⟨3893426, by rfl⟩ : syracuseStep 5191235 = 7786853) B7786853
theorem B4380227 : Blo 1707054 4380227 := bstep (se 1 (by rfl) ⟨3285170, by rfl⟩ : syracuseStep 4380227 = 6570341) B6570341
theorem B2561603 : Blo 1707054 2561603 := bstep (se 1 (by rfl) ⟨1921202, by rfl⟩ : syracuseStep 2561603 = 3842405) B3842405
theorem B2561633 : Blo 1707054 2561633 := bstep (se 2 (by rfl) ⟨960612, by rfl⟩ : syracuseStep 2561633 = 1921225) B1921225
theorem B2430577 : Blo 1707054 2430577 := bstep (se 2 (by rfl) ⟨911466, by rfl⟩ : syracuseStep 2430577 = 1822933) B1822933
theorem B4322929 : Blo 1707054 4322929 := bstep (se 2 (by rfl) ⟨1621098, by rfl⟩ : syracuseStep 4322929 = 3242197) B3242197
theorem B2561651 : Blo 1707054 2561651 := bstep (se 1 (by rfl) ⟨1921238, by rfl⟩ : syracuseStep 2561651 = 3842477) B3842477
theorem B2561681 : Blo 1707054 2561681 := bstep (se 2 (by rfl) ⟨960630, by rfl⟩ : syracuseStep 2561681 = 1921261) B1921261
theorem B2561699 : Blo 1707054 2561699 := bstep (se 1 (by rfl) ⟨1921274, by rfl⟩ : syracuseStep 2561699 = 3842549) B3842549
theorem B8648369 : Blo 1707054 8648369 := bstep (se 2 (by rfl) ⟨3243138, by rfl⟩ : syracuseStep 8648369 = 6486277) B6486277
theorem B2881217 : Blo 1707054 2881217 := bstep (se 2 (by rfl) ⟨1080456, by rfl⟩ : syracuseStep 2881217 = 2160913) B2160913
theorem B2561729 : Blo 1707054 2561729 := bstep (se 2 (by rfl) ⟨960648, by rfl⟩ : syracuseStep 2561729 = 1921297) B1921297
theorem B2561747 : Blo 1707054 2561747 := bstep (se 1 (by rfl) ⟨1921310, by rfl⟩ : syracuseStep 2561747 = 3842621) B3842621
theorem B26285795 : Blo 1707054 26285795 := bstep (se 1 (by rfl) ⟨19714346, by rfl⟩ : syracuseStep 26285795 = 39428693) B39428693
theorem B2561777 : Blo 1707054 2561777 := bstep (se 2 (by rfl) ⟨960666, by rfl⟩ : syracuseStep 2561777 = 1921333) B1921333
theorem B2561795 : Blo 1707054 2561795 := bstep (se 1 (by rfl) ⟨1921346, by rfl⟩ : syracuseStep 2561795 = 3842693) B3842693
theorem B5764877 : Blo 1707054 5764877 := bstep (se 3 (by rfl) ⟨1080914, by rfl⟩ : syracuseStep 5764877 = 2161829) B2161829
theorem B2561825 : Blo 1707054 2561825 := bstep (se 2 (by rfl) ⟨960684, by rfl⟩ : syracuseStep 2561825 = 1921369) B1921369
theorem B9729827 : Blo 1707054 9729827 := bstep (se 1 (by rfl) ⟨7297370, by rfl⟩ : syracuseStep 9729827 = 14594741) B14594741
theorem B4618019 : Blo 1707054 4618019 := bstep (se 1 (by rfl) ⟨3463514, by rfl⟩ : syracuseStep 4618019 = 6927029) B6927029
theorem B2561843 : Blo 1707054 2561843 := bstep (se 1 (by rfl) ⟨1921382, by rfl⟩ : syracuseStep 2561843 = 3842765) B3842765
theorem B2881345 : Blo 1707054 2881345 := bstep (se 2 (by rfl) ⟨1080504, by rfl⟩ : syracuseStep 2881345 = 2161009) B2161009
theorem B3241795 : Blo 1707054 3241795 := bstep (se 1 (by rfl) ⟨2431346, by rfl⟩ : syracuseStep 3241795 = 4862693) B4862693
theorem B5764931 : Blo 1707054 5764931 := bstep (se 1 (by rfl) ⟨4323698, by rfl⟩ : syracuseStep 5764931 = 8647397) B8647397
theorem B2561873 : Blo 1707054 2561873 := bstep (se 2 (by rfl) ⟨960702, by rfl⟩ : syracuseStep 2561873 = 1921405) B1921405
theorem B2340689 : Blo 1707054 2340689 := bstep (se 2 (by rfl) ⟨877758, by rfl⟩ : syracuseStep 2340689 = 1755517) B1755517
theorem B2881379 : Blo 1707054 2881379 := bstep (se 1 (by rfl) ⟨2161034, by rfl⟩ : syracuseStep 2881379 = 4322069) B4322069
theorem B18462563 : Blo 1707054 18462563 := bstep (se 1 (by rfl) ⟨13846922, by rfl⟩ : syracuseStep 18462563 = 27693845) B27693845
theorem B2561891 : Blo 1707054 2561891 := bstep (se 1 (by rfl) ⟨1921418, by rfl⟩ : syracuseStep 2561891 = 3842837) B3842837
theorem B2561921 : Blo 1707054 2561921 := bstep (se 2 (by rfl) ⟨960720, by rfl⟩ : syracuseStep 2561921 = 1921441) B1921441
theorem B4323203 : Blo 1707054 4323203 := bstep (se 1 (by rfl) ⟨3242402, by rfl⟩ : syracuseStep 4323203 = 6484805) B6484805
theorem B16013197 : Blo 1707054 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B2561939 : Blo 1707054 2561939 := bstep (se 1 (by rfl) ⟨1921454, by rfl⟩ : syracuseStep 2561939 = 3842909) B3842909
theorem B2561969 : Blo 1707054 2561969 := bstep (se 2 (by rfl) ⟨960738, by rfl⟩ : syracuseStep 2561969 = 1921477) B1921477
theorem B2561987 : Blo 1707054 2561987 := bstep (se 1 (by rfl) ⟨1921490, by rfl⟩ : syracuseStep 2561987 = 3842981) B3842981
theorem B16635845 : Blo 1707054 16635845 := bstep (se 4 (by rfl) ⟨1559610, by rfl⟩ : syracuseStep 16635845 = 3119221) B3119221
theorem B2562017 : Blo 1707054 2562017 := bstep (se 2 (by rfl) ⟨960756, by rfl⟩ : syracuseStep 2562017 = 1921513) B1921513
theorem B2881507 : Blo 1707054 2881507 := bstep (se 1 (by rfl) ⟨2161130, by rfl⟩ : syracuseStep 2881507 = 4322261) B4322261
theorem B5191661 : Blo 1707054 5191661 := bstep (se 3 (by rfl) ⟨973436, by rfl⟩ : syracuseStep 5191661 = 1946873) B1946873
theorem B2562035 : Blo 1707054 2562035 := bstep (se 1 (by rfl) ⟨1921526, by rfl⟩ : syracuseStep 2562035 = 3843053) B3843053
theorem B12310541 : Blo 1707054 12310541 := bstep (se 3 (by rfl) ⟨2308226, by rfl⟩ : syracuseStep 12310541 = 4616453) B4616453
theorem B2562065 : Blo 1707054 2562065 := bstep (se 2 (by rfl) ⟨960774, by rfl⟩ : syracuseStep 2562065 = 1921549) B1921549
theorem B2562083 : Blo 1707054 2562083 := bstep (se 1 (by rfl) ⟨1921562, by rfl⟩ : syracuseStep 2562083 = 3843125) B3843125
theorem B6486065 : Blo 1707054 6486065 := bstep (se 2 (by rfl) ⟨2432274, by rfl⟩ : syracuseStep 6486065 = 4864549) B4864549
theorem B2562113 : Blo 1707054 2562113 := bstep (se 2 (by rfl) ⟨960792, by rfl⟩ : syracuseStep 2562113 = 1921585) B1921585
theorem B4323395 : Blo 1707054 4323395 := bstep (se 1 (by rfl) ⟨3242546, by rfl⟩ : syracuseStep 4323395 = 6485093) B6485093
theorem B5765201 : Blo 1707054 5765201 := bstep (se 2 (by rfl) ⟨2161950, by rfl⟩ : syracuseStep 5765201 = 4323901) B4323901
theorem B2562131 : Blo 1707054 2562131 := bstep (se 1 (by rfl) ⟨1921598, by rfl⟩ : syracuseStep 2562131 = 3843197) B3843197
theorem B2431073 : Blo 1707054 2431073 := bstep (se 2 (by rfl) ⟨911652, by rfl⟩ : syracuseStep 2431073 = 1823305) B1823305
theorem B2881649 : Blo 1707054 2881649 := bstep (se 2 (by rfl) ⟨1080618, by rfl⟩ : syracuseStep 2881649 = 2161237) B2161237
theorem B2562161 : Blo 1707054 2562161 := bstep (se 2 (by rfl) ⟨960810, by rfl⟩ : syracuseStep 2562161 = 1921621) B1921621
theorem B2562179 : Blo 1707054 2562179 := bstep (se 1 (by rfl) ⟨1921634, by rfl⟩ : syracuseStep 2562179 = 3843269) B3843269
theorem B19454093 : Blo 1707054 19454093 := bstep (se 3 (by rfl) ⟨3647642, by rfl⟩ : syracuseStep 19454093 = 7295285) B7295285
theorem B2562209 : Blo 1707054 2562209 := bstep (se 2 (by rfl) ⟨960828, by rfl⟩ : syracuseStep 2562209 = 1921657) B1921657
theorem B2562227 : Blo 1707054 2562227 := bstep (se 1 (by rfl) ⟨1921670, by rfl⟩ : syracuseStep 2562227 = 3843341) B3843341
theorem B2562257 : Blo 1707054 2562257 := bstep (se 2 (by rfl) ⟨960846, by rfl⟩ : syracuseStep 2562257 = 1921693) B1921693
theorem B2562275 : Blo 1707054 2562275 := bstep (se 1 (by rfl) ⟨1921706, by rfl⟩ : syracuseStep 2562275 = 3843413) B3843413
theorem B2881777 : Blo 1707054 2881777 := bstep (se 2 (by rfl) ⟨1080666, by rfl⟩ : syracuseStep 2881777 = 2161333) B2161333
theorem B2562305 : Blo 1707054 2562305 := bstep (se 2 (by rfl) ⟨960864, by rfl⟩ : syracuseStep 2562305 = 1921729) B1921729
theorem B3242243 : Blo 1707054 3242243 := bstep (se 1 (by rfl) ⟨2431682, by rfl⟩ : syracuseStep 3242243 = 4863365) B4863365
theorem B2881811 : Blo 1707054 2881811 := bstep (se 1 (by rfl) ⟨2161358, by rfl⟩ : syracuseStep 2881811 = 4322717) B4322717
theorem B2562323 : Blo 1707054 2562323 := bstep (se 1 (by rfl) ⟨1921742, by rfl⟩ : syracuseStep 2562323 = 3843485) B3843485
theorem B9861425 : Blo 1707054 9861425 := bstep (se 2 (by rfl) ⟨3698034, by rfl⟩ : syracuseStep 9861425 = 7396069) B7396069
theorem B2562353 : Blo 1707054 2562353 := bstep (se 2 (by rfl) ⟨960882, by rfl⟩ : syracuseStep 2562353 = 1921765) B1921765
theorem B2562371 : Blo 1707054 2562371 := bstep (se 1 (by rfl) ⟨1921778, by rfl⟩ : syracuseStep 2562371 = 3843557) B3843557
theorem B4864333 : Blo 1707054 4864333 := bstep (se 3 (by rfl) ⟨912062, by rfl⟩ : syracuseStep 4864333 = 1824125) B1824125
theorem B2562401 : Blo 1707054 2562401 := bstep (se 2 (by rfl) ⟨960900, by rfl⟩ : syracuseStep 2562401 = 1921801) B1921801
theorem B2562419 : Blo 1707054 2562419 := bstep (se 1 (by rfl) ⟨1921814, by rfl⟩ : syracuseStep 2562419 = 3843629) B3843629
theorem B2562449 : Blo 1707054 2562449 := bstep (se 2 (by rfl) ⟨960918, by rfl⟩ : syracuseStep 2562449 = 1921837) B1921837
theorem B2881939 : Blo 1707054 2881939 := bstep (se 1 (by rfl) ⟨2161454, by rfl⟩ : syracuseStep 2881939 = 4322909) B4322909
theorem B2308513 : Blo 1707054 2308513 := bstep (se 2 (by rfl) ⟨865692, by rfl⟩ : syracuseStep 2308513 = 1731385) B1731385
theorem B2562467 : Blo 1707054 2562467 := bstep (se 1 (by rfl) ⟨1921850, by rfl⟩ : syracuseStep 2562467 = 3843701) B3843701
theorem B2161075 : Blo 1707054 2161075 := bstep (se 1 (by rfl) ⟨1620806, by rfl⟩ : syracuseStep 2161075 = 3241613) B3241613
theorem B2562497 : Blo 1707054 2562497 := bstep (se 2 (by rfl) ⟨960936, by rfl⟩ : syracuseStep 2562497 = 1921873) B1921873
theorem B2562515 : Blo 1707054 2562515 := bstep (se 1 (by rfl) ⟨1921886, by rfl⟩ : syracuseStep 2562515 = 3843773) B3843773
theorem B16407011 : Blo 1707054 16407011 := bstep (se 1 (by rfl) ⟨12305258, by rfl⟩ : syracuseStep 16407011 = 24610517) B24610517
theorem B2562545 : Blo 1707054 2562545 := bstep (se 2 (by rfl) ⟨960954, by rfl⟩ : syracuseStep 2562545 = 1921909) B1921909
theorem B2562563 : Blo 1707054 2562563 := bstep (se 1 (by rfl) ⟨1921922, by rfl⟩ : syracuseStep 2562563 = 3843845) B3843845
theorem B2161171 : Blo 1707054 2161171 := bstep (se 1 (by rfl) ⟨1620878, by rfl⟩ : syracuseStep 2161171 = 3241757) B3241757
theorem B2882081 : Blo 1707054 2882081 := bstep (se 2 (by rfl) ⟨1080780, by rfl⟩ : syracuseStep 2882081 = 2161561) B2161561
theorem B2562593 : Blo 1707054 2562593 := bstep (se 2 (by rfl) ⟨960972, by rfl⟩ : syracuseStep 2562593 = 1921945) B1921945
theorem B3242531 : Blo 1707054 3242531 := bstep (se 1 (by rfl) ⟨2431898, by rfl⟩ : syracuseStep 3242531 = 4863797) B4863797
theorem B2562611 : Blo 1707054 2562611 := bstep (se 1 (by rfl) ⟨1921958, by rfl⟩ : syracuseStep 2562611 = 3843917) B3843917
theorem B2562641 : Blo 1707054 2562641 := bstep (se 2 (by rfl) ⟨960990, by rfl⟩ : syracuseStep 2562641 = 1921981) B1921981
theorem B3078737 : Blo 1707054 3078737 := bstep (se 2 (by rfl) ⟨1154526, by rfl⟩ : syracuseStep 3078737 = 2309053) B2309053
theorem B2562659 : Blo 1707054 2562659 := bstep (se 1 (by rfl) ⟨1921994, by rfl⟩ : syracuseStep 2562659 = 3843989) B3843989
theorem B5765741 : Blo 1707054 5765741 := bstep (se 3 (by rfl) ⟨1081076, by rfl⟩ : syracuseStep 5765741 = 2162153) B2162153
theorem B2562689 : Blo 1707054 2562689 := bstep (se 2 (by rfl) ⟨961008, by rfl⟩ : syracuseStep 2562689 = 1922017) B1922017
theorem B2562707 : Blo 1707054 2562707 := bstep (se 1 (by rfl) ⟨1922030, by rfl⟩ : syracuseStep 2562707 = 3844061) B3844061
theorem B2882209 : Blo 1707054 2882209 := bstep (se 2 (by rfl) ⟨1080828, by rfl⟩ : syracuseStep 2882209 = 2161657) B2161657
theorem B5765795 : Blo 1707054 5765795 := bstep (se 1 (by rfl) ⟨4324346, by rfl⟩ : syracuseStep 5765795 = 8648693) B8648693
theorem B2562737 : Blo 1707054 2562737 := bstep (se 2 (by rfl) ⟨961026, by rfl⟩ : syracuseStep 2562737 = 1922053) B1922053
theorem B2882243 : Blo 1707054 2882243 := bstep (se 1 (by rfl) ⟨2161682, by rfl⟩ : syracuseStep 2882243 = 4323365) B4323365
theorem B2562755 : Blo 1707054 2562755 := bstep (se 1 (by rfl) ⟨1922066, by rfl⟩ : syracuseStep 2562755 = 3844133) B3844133
theorem B2562785 : Blo 1707054 2562785 := bstep (se 2 (by rfl) ⟨961044, by rfl⟩ : syracuseStep 2562785 = 1922089) B1922089
theorem B14588657 : Blo 1707054 14588657 := bstep (se 2 (by rfl) ⟨5470746, by rfl⟩ : syracuseStep 14588657 = 10941493) B10941493
theorem B2562803 : Blo 1707054 2562803 := bstep (se 1 (by rfl) ⟨1922102, by rfl⟩ : syracuseStep 2562803 = 3844205) B3844205
theorem B2562833 : Blo 1707054 2562833 := bstep (se 2 (by rfl) ⟨961062, by rfl⟩ : syracuseStep 2562833 = 1922125) B1922125
theorem B2562851 : Blo 1707054 2562851 := bstep (se 1 (by rfl) ⟨1922138, by rfl⟩ : syracuseStep 2562851 = 3844277) B3844277
theorem B2562881 : Blo 1707054 2562881 := bstep (se 2 (by rfl) ⟨961080, by rfl⟩ : syracuseStep 2562881 = 1922161) B1922161
theorem B2882371 : Blo 1707054 2882371 := bstep (se 1 (by rfl) ⟨2161778, by rfl⟩ : syracuseStep 2882371 = 4323557) B4323557
theorem B2562899 : Blo 1707054 2562899 := bstep (se 1 (by rfl) ⟨1922174, by rfl⟩ : syracuseStep 2562899 = 3844349) B3844349
theorem B2562929 : Blo 1707054 2562929 := bstep (se 2 (by rfl) ⟨961098, by rfl⟩ : syracuseStep 2562929 = 1922197) B1922197
theorem B2497411 : Blo 1707054 2497411 := bstep (se 1 (by rfl) ⟨1873058, by rfl⟩ : syracuseStep 2497411 = 3746117) B3746117
theorem B2562947 : Blo 1707054 2562947 := bstep (se 1 (by rfl) ⟨1922210, by rfl⟩ : syracuseStep 2562947 = 3844421) B3844421
theorem B2562977 : Blo 1707054 2562977 := bstep (se 2 (by rfl) ⟨961116, by rfl⟩ : syracuseStep 2562977 = 1922233) B1922233
theorem B5766065 : Blo 1707054 5766065 := bstep (se 2 (by rfl) ⟨2162274, by rfl⟩ : syracuseStep 5766065 = 4324549) B4324549
theorem B2562995 : Blo 1707054 2562995 := bstep (se 1 (by rfl) ⟨1922246, by rfl⟩ : syracuseStep 2562995 = 3844493) B3844493
theorem B2735041 : Blo 1707054 2735041 := bstep (se 2 (by rfl) ⟨1025640, by rfl⟩ : syracuseStep 2735041 = 2051281) B2051281
theorem B2431939 : Blo 1707054 2431939 := bstep (se 1 (by rfl) ⟨1823954, by rfl⟩ : syracuseStep 2431939 = 3647909) B3647909
theorem B2882513 : Blo 1707054 2882513 := bstep (se 2 (by rfl) ⟨1080942, by rfl⟩ : syracuseStep 2882513 = 2161885) B2161885
theorem B2563025 : Blo 1707054 2563025 := bstep (se 2 (by rfl) ⟨961134, by rfl⟩ : syracuseStep 2563025 = 1922269) B1922269
theorem B2563043 : Blo 1707054 2563043 := bstep (se 1 (by rfl) ⟨1922282, by rfl⟩ : syracuseStep 2563043 = 3844565) B3844565
theorem B7789553 : Blo 1707054 7789553 := bstep (se 2 (by rfl) ⟨2921082, by rfl⟩ : syracuseStep 7789553 = 5842165) B5842165
theorem B4324337 : Blo 1707054 4324337 := bstep (se 2 (by rfl) ⟨1621626, by rfl⟩ : syracuseStep 4324337 = 3243253) B3243253
theorem B2563073 : Blo 1707054 2563073 := bstep (se 2 (by rfl) ⟨961152, by rfl⟩ : syracuseStep 2563073 = 1922305) B1922305
theorem B2161667 : Blo 1707054 2161667 := bstep (se 1 (by rfl) ⟨1621250, by rfl⟩ : syracuseStep 2161667 = 3242501) B3242501
theorem B4930573 : Blo 1707054 4930573 := bstep (se 3 (by rfl) ⟨924482, by rfl⟩ : syracuseStep 4930573 = 1848965) B1848965
theorem B2563091 : Blo 1707054 2563091 := bstep (se 1 (by rfl) ⟨1922318, by rfl⟩ : syracuseStep 2563091 = 3844637) B3844637
theorem B2432035 : Blo 1707054 2432035 := bstep (se 1 (by rfl) ⟨1824026, by rfl⟩ : syracuseStep 2432035 = 3648053) B3648053
theorem B4324387 : Blo 1707054 4324387 := bstep (se 1 (by rfl) ⟨3243290, by rfl⟩ : syracuseStep 4324387 = 6486581) B6486581
theorem B3841073 : Blo 1707054 3841073 := bstep (se 2 (by rfl) ⟨1440402, by rfl⟩ : syracuseStep 3841073 = 2880805) B2880805
theorem B2563121 : Blo 1707054 2563121 := bstep (se 2 (by rfl) ⟨961170, by rfl⟩ : syracuseStep 2563121 = 1922341) B1922341
theorem B3841091 : Blo 1707054 3841091 := bstep (se 1 (by rfl) ⟨2880818, by rfl⟩ : syracuseStep 3841091 = 5761637) B5761637
theorem B2563139 : Blo 1707054 2563139 := bstep (se 1 (by rfl) ⟨1922354, by rfl⟩ : syracuseStep 2563139 = 3844709) B3844709
theorem B16424005 : Blo 1707054 16424005 := bstep (se 4 (by rfl) ⟨1539750, by rfl⟩ : syracuseStep 16424005 = 3079501) B3079501
theorem B2882641 : Blo 1707054 2882641 := bstep (se 2 (by rfl) ⟨1080990, by rfl⟩ : syracuseStep 2882641 = 2161981) B2161981
theorem B2563169 : Blo 1707054 2563169 := bstep (se 2 (by rfl) ⟨961188, by rfl⟩ : syracuseStep 2563169 = 1922377) B1922377
theorem B8649827 : Blo 1707054 8649827 := bstep (se 1 (by rfl) ⟨6487370, by rfl⟩ : syracuseStep 8649827 = 12974741) B12974741
theorem B2882675 : Blo 1707054 2882675 := bstep (se 1 (by rfl) ⟨2162006, by rfl⟩ : syracuseStep 2882675 = 4324013) B4324013
theorem B2563187 : Blo 1707054 2563187 := bstep (se 1 (by rfl) ⟨1922390, by rfl⟩ : syracuseStep 2563187 = 3844781) B3844781
theorem B2563217 : Blo 1707054 2563217 := bstep (se 2 (by rfl) ⟨961206, by rfl⟩ : syracuseStep 2563217 = 1922413) B1922413
theorem B2563235 : Blo 1707054 2563235 := bstep (se 1 (by rfl) ⟨1922426, by rfl⟩ : syracuseStep 2563235 = 3844853) B3844853
theorem B4324529 : Blo 1707054 4324529 := bstep (se 2 (by rfl) ⟨1621698, by rfl⟩ : syracuseStep 4324529 = 3243397) B3243397
theorem B7298225 : Blo 1707054 7298225 := bstep (se 2 (by rfl) ⟨2736834, by rfl⟩ : syracuseStep 7298225 = 5473669) B5473669
theorem B2735297 : Blo 1707054 2735297 := bstep (se 2 (by rfl) ⟨1025736, by rfl⟩ : syracuseStep 2735297 = 2051473) B2051473
theorem B10386629 : Blo 1707054 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B2563265 : Blo 1707054 2563265 := bstep (se 2 (by rfl) ⟨961224, by rfl⟩ : syracuseStep 2563265 = 1922449) B1922449
theorem B2563283 : Blo 1707054 2563283 := bstep (se 1 (by rfl) ⟨1922462, by rfl⟩ : syracuseStep 2563283 = 3844925) B3844925
theorem B2563313 : Blo 1707054 2563313 := bstep (se 2 (by rfl) ⟨961242, by rfl⟩ : syracuseStep 2563313 = 1922485) B1922485
theorem B2882803 : Blo 1707054 2882803 := bstep (se 1 (by rfl) ⟨2162102, by rfl⟩ : syracuseStep 2882803 = 4324205) B4324205
theorem B2563331 : Blo 1707054 2563331 := bstep (se 1 (by rfl) ⟨1922498, by rfl⟩ : syracuseStep 2563331 = 3844997) B3844997
theorem B2563361 : Blo 1707054 2563361 := bstep (se 2 (by rfl) ⟨961260, by rfl⟩ : syracuseStep 2563361 = 1922521) B1922521
theorem B2563379 : Blo 1707054 2563379 := bstep (se 1 (by rfl) ⟨1922534, by rfl⟩ : syracuseStep 2563379 = 3845069) B3845069
theorem B3841361 : Blo 1707054 3841361 := bstep (se 2 (by rfl) ⟨1440510, by rfl⟩ : syracuseStep 3841361 = 2881021) B2881021
theorem B2563409 : Blo 1707054 2563409 := bstep (se 2 (by rfl) ⟨961278, by rfl⟩ : syracuseStep 2563409 = 1922557) B1922557
theorem B3841379 : Blo 1707054 3841379 := bstep (se 1 (by rfl) ⟨2881034, by rfl⟩ : syracuseStep 3841379 = 5762069) B5762069
theorem B2563427 : Blo 1707054 2563427 := bstep (se 1 (by rfl) ⟨1922570, by rfl⟩ : syracuseStep 2563427 = 3845141) B3845141
theorem B2596225 : Blo 1707054 2596225 := bstep (se 2 (by rfl) ⟨973584, by rfl⟩ : syracuseStep 2596225 = 1947169) B1947169
theorem B2735489 : Blo 1707054 2735489 := bstep (se 2 (by rfl) ⟨1025808, by rfl⟩ : syracuseStep 2735489 = 2051617) B2051617
theorem B2882945 : Blo 1707054 2882945 := bstep (se 2 (by rfl) ⟨1081104, by rfl⟩ : syracuseStep 2882945 = 2162209) B2162209
theorem B2563457 : Blo 1707054 2563457 := bstep (se 2 (by rfl) ⟨961296, by rfl⟩ : syracuseStep 2563457 = 1922593) B1922593
theorem B2563475 : Blo 1707054 2563475 := bstep (se 1 (by rfl) ⟨1922606, by rfl⟩ : syracuseStep 2563475 = 3845213) B3845213
theorem B2563505 : Blo 1707054 2563505 := bstep (se 2 (by rfl) ⟨961314, by rfl⟩ : syracuseStep 2563505 = 1922629) B1922629
theorem B2563523 : Blo 1707054 2563523 := bstep (se 1 (by rfl) ⟨1922642, by rfl⟩ : syracuseStep 2563523 = 3845285) B3845285
theorem B5766605 : Blo 1707054 5766605 := bstep (se 3 (by rfl) ⟨1081238, by rfl⟩ : syracuseStep 5766605 = 2162477) B2162477
theorem B3243473 : Blo 1707054 3243473 := bstep (se 2 (by rfl) ⟨1216302, by rfl⟩ : syracuseStep 3243473 = 2432605) B2432605
theorem B2563553 : Blo 1707054 2563553 := bstep (se 2 (by rfl) ⟨961332, by rfl⟩ : syracuseStep 2563553 = 1922665) B1922665
theorem B6487523 : Blo 1707054 6487523 := bstep (se 1 (by rfl) ⟨4865642, by rfl⟩ : syracuseStep 6487523 = 9731285) B9731285
theorem B2563571 : Blo 1707054 2563571 := bstep (se 1 (by rfl) ⟨1922678, by rfl⟩ : syracuseStep 2563571 = 3845357) B3845357
theorem B2883073 : Blo 1707054 2883073 := bstep (se 2 (by rfl) ⟨1081152, by rfl⟩ : syracuseStep 2883073 = 2162305) B2162305
theorem B5766659 : Blo 1707054 5766659 := bstep (se 1 (by rfl) ⟨4324994, by rfl⟩ : syracuseStep 5766659 = 8649989) B8649989
theorem B2432531 : Blo 1707054 2432531 := bstep (se 1 (by rfl) ⟨1824398, by rfl⟩ : syracuseStep 2432531 = 3648797) B3648797
theorem B2883107 : Blo 1707054 2883107 := bstep (se 1 (by rfl) ⟨2162330, by rfl⟩ : syracuseStep 2883107 = 4324661) B4324661
theorem B3841649 : Blo 1707054 3841649 := bstep (se 2 (by rfl) ⟨1440618, by rfl⟩ : syracuseStep 3841649 = 2881237) B2881237
theorem B3841667 : Blo 1707054 3841667 := bstep (se 1 (by rfl) ⟨2881250, by rfl⟩ : syracuseStep 3841667 = 5762501) B5762501
theorem B2883235 : Blo 1707054 2883235 := bstep (se 1 (by rfl) ⟨2162426, by rfl⟩ : syracuseStep 2883235 = 4324853) B4324853
theorem B2162371 : Blo 1707054 2162371 := bstep (se 1 (by rfl) ⟨1621778, by rfl⟩ : syracuseStep 2162371 = 3243557) B3243557
theorem B5766929 : Blo 1707054 5766929 := bstep (se 2 (by rfl) ⟨2162598, by rfl⟩ : syracuseStep 5766929 = 4325197) B4325197
theorem B2162467 : Blo 1707054 2162467 := bstep (se 1 (by rfl) ⟨1621850, by rfl⟩ : syracuseStep 2162467 = 3243701) B3243701
theorem B2883377 : Blo 1707054 2883377 := bstep (se 2 (by rfl) ⟨1081266, by rfl⟩ : syracuseStep 2883377 = 2162533) B2162533
theorem B5193571 : Blo 1707054 5193571 := bstep (se 1 (by rfl) ⟨3895178, by rfl⟩ : syracuseStep 5193571 = 7790357) B7790357
theorem B8650637 : Blo 1707054 8650637 := bstep (se 3 (by rfl) ⟨1621994, by rfl⟩ : syracuseStep 8650637 = 3243989) B3243989
theorem B3841937 : Blo 1707054 3841937 := bstep (se 2 (by rfl) ⟨1440726, by rfl⟩ : syracuseStep 3841937 = 2881453) B2881453
theorem B3841955 : Blo 1707054 3841955 := bstep (se 1 (by rfl) ⟨2881466, by rfl⟩ : syracuseStep 3841955 = 5762933) B5762933
theorem B2883505 : Blo 1707054 2883505 := bstep (se 2 (by rfl) ⟨1081314, by rfl⟩ : syracuseStep 2883505 = 2162629) B2162629
theorem B2883539 : Blo 1707054 2883539 := bstep (se 1 (by rfl) ⟨2162654, by rfl⟩ : syracuseStep 2883539 = 4325309) B4325309
theorem B3244043 : Blo 1707054 3244043 := bstep (se 1 (by rfl) ⟨2433032, by rfl⟩ : syracuseStep 3244043 = 4866065) B4866065
theorem B3842099 : Blo 1707054 3842099 := bstep (se 1 (by rfl) ⟨2881574, by rfl⟩ : syracuseStep 3842099 = 5763149) B5763149
theorem B7118923 : Blo 1707054 7118923 := bstep (se 1 (by rfl) ⟨5339192, by rfl⟩ : syracuseStep 7118923 = 10678385) B10678385
theorem B3842135 : Blo 1707054 3842135 := bstep (se 1 (by rfl) ⟨2881601, by rfl⟩ : syracuseStep 3842135 = 5763203) B5763203
theorem B18473111 : Blo 1707054 18473111 := bstep (se 1 (by rfl) ⟨13854833, by rfl⟩ : syracuseStep 18473111 = 27709667) B27709667
theorem B2810009 : Blo 1707054 2810009 := bstep (se 2 (by rfl) ⟨1053753, by rfl⟩ : syracuseStep 2810009 = 2107507) B2107507
theorem B5767361 : Blo 1707054 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B3244225 : Blo 1707054 3244225 := bstep (se 2 (by rfl) ⟨1216584, by rfl⟩ : syracuseStep 3244225 = 2433169) B2433169
theorem B3842315 : Blo 1707054 3842315 := bstep (se 1 (by rfl) ⟨2881736, by rfl⟩ : syracuseStep 3842315 = 5763473) B5763473
theorem B2883863 : Blo 1707054 2883863 := bstep (se 1 (by rfl) ⟨2162897, by rfl⟩ : syracuseStep 2883863 = 4325795) B4325795
theorem B8642861 : Blo 1707054 8642861 := bstep (se 3 (by rfl) ⟨1620536, by rfl⟩ : syracuseStep 8642861 = 3241073) B3241073
theorem B4325683 : Blo 1707054 4325683 := bstep (se 1 (by rfl) ⟨3244262, by rfl⟩ : syracuseStep 4325683 = 6488525) B6488525
theorem B3842369 : Blo 1707054 3842369 := bstep (se 2 (by rfl) ⟨1440888, by rfl⟩ : syracuseStep 3842369 = 2881777) B2881777
theorem B2163019 : Blo 1707054 2163019 := bstep (se 1 (by rfl) ⟨1622264, by rfl⟩ : syracuseStep 2163019 = 3244529) B3244529
theorem B2883991 : Blo 1707054 2883991 := bstep (se 1 (by rfl) ⟨2162993, by rfl⟩ : syracuseStep 2883991 = 4325987) B4325987
theorem B4325825 : Blo 1707054 4325825 := bstep (se 2 (by rfl) ⟨1622184, by rfl⟩ : syracuseStep 4325825 = 3244369) B3244369
theorem B16417241 : Blo 1707054 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B3842585 : Blo 1707054 3842585 := bstep (se 2 (by rfl) ⟨1440969, by rfl⟩ : syracuseStep 3842585 = 2881939) B2881939
theorem B12976685 : Blo 1707054 12976685 := bstep (se 3 (by rfl) ⟨2433128, by rfl⟩ : syracuseStep 12976685 = 4866257) B4866257
theorem B7299659 : Blo 1707054 7299659 := bstep (se 1 (by rfl) ⟨5474744, by rfl⟩ : syracuseStep 7299659 = 10949489) B10949489
theorem B3842675 : Blo 1707054 3842675 := bstep (se 1 (by rfl) ⟨2882006, by rfl⟩ : syracuseStep 3842675 = 5764013) B5764013
theorem B6488707 : Blo 1707054 6488707 := bstep (se 1 (by rfl) ⟨4866530, by rfl⟩ : syracuseStep 6488707 = 9733061) B9733061
theorem B3842711 : Blo 1707054 3842711 := bstep (se 1 (by rfl) ⟨2882033, by rfl⟩ : syracuseStep 3842711 = 5764067) B5764067
theorem B6152921 : Blo 1707054 6152921 := bstep (se 2 (by rfl) ⟨2307345, by rfl⟩ : syracuseStep 6152921 = 4614691) B4614691
theorem B5767901 : Blo 1707054 5767901 := bstep (se 3 (by rfl) ⟨1081481, by rfl⟩ : syracuseStep 5767901 = 2162963) B2162963
theorem B15582017 : Blo 1707054 15582017 := bstep (se 2 (by rfl) ⟨5843256, by rfl⟩ : syracuseStep 15582017 = 11686513) B11686513
theorem B3842891 : Blo 1707054 3842891 := bstep (se 1 (by rfl) ⟨2882168, by rfl⟩ : syracuseStep 3842891 = 5764337) B5764337
theorem B3842945 : Blo 1707054 3842945 := bstep (se 2 (by rfl) ⟨1441104, by rfl⟩ : syracuseStep 3842945 = 2882209) B2882209
theorem B6489011 : Blo 1707054 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B12968909 : Blo 1707054 12968909 := bstep (se 3 (by rfl) ⟨2431670, by rfl⟩ : syracuseStep 12968909 = 4863341) B4863341
theorem B5194775 : Blo 1707054 5194775 := bstep (se 1 (by rfl) ⟨3896081, by rfl⟩ : syracuseStep 5194775 = 7792163) B7792163
theorem B3843161 : Blo 1707054 3843161 := bstep (se 2 (by rfl) ⟨1441185, by rfl⟩ : syracuseStep 3843161 = 2882371) B2882371
theorem B9725021 : Blo 1707054 9725021 := bstep (se 3 (by rfl) ⟨1823441, by rfl⟩ : syracuseStep 9725021 = 3646883) B3646883
theorem B17523863 : Blo 1707054 17523863 := bstep (se 1 (by rfl) ⟨13142897, by rfl⟩ : syracuseStep 17523863 = 26285795) B26285795
theorem B3843251 : Blo 1707054 3843251 := bstep (se 1 (by rfl) ⟨2882438, by rfl⟩ : syracuseStep 3843251 = 5764877) B5764877
theorem B3843287 : Blo 1707054 3843287 := bstep (se 1 (by rfl) ⟨2882465, by rfl⟩ : syracuseStep 3843287 = 5764931) B5764931
theorem B3646721 : Blo 1707054 3646721 := bstep (se 2 (by rfl) ⟨1367520, by rfl⟩ : syracuseStep 3646721 = 2735041) B2735041
theorem B3605771 : Blo 1707054 3605771 := bstep (se 1 (by rfl) ⟨2704328, by rfl⟩ : syracuseStep 3605771 = 5408657) B5408657
theorem B7292177 : Blo 1707054 7292177 := bstep (se 2 (by rfl) ⟨2734566, by rfl⟩ : syracuseStep 7292177 = 5469133) B5469133
theorem B3843467 : Blo 1707054 3843467 := bstep (se 1 (by rfl) ⟨2882600, by rfl⟩ : syracuseStep 3843467 = 5765201) B5765201
theorem B21898673 : Blo 1707054 21898673 := bstep (se 2 (by rfl) ⟨8212002, by rfl⟩ : syracuseStep 21898673 = 16424005) B16424005
theorem B12969395 : Blo 1707054 12969395 := bstep (se 1 (by rfl) ⟨9727046, by rfl⟩ : syracuseStep 12969395 = 19454093) B19454093
theorem B3843521 : Blo 1707054 3843521 := bstep (se 2 (by rfl) ⟨1441320, by rfl⟩ : syracuseStep 3843521 = 2882641) B2882641
theorem B10938007 : Blo 1707054 10938007 := bstep (se 1 (by rfl) ⟨8203505, by rfl⟩ : syracuseStep 10938007 = 16407011) B16407011
theorem B3843737 : Blo 1707054 3843737 := bstep (se 2 (by rfl) ⟨1441401, by rfl⟩ : syracuseStep 3843737 = 2882803) B2882803
theorem B3843827 : Blo 1707054 3843827 := bstep (se 1 (by rfl) ⟨2882870, by rfl⟩ : syracuseStep 3843827 = 5765741) B5765741
theorem B12306181 : Blo 1707054 12306181 := bstep (se 4 (by rfl) ⟨1153704, by rfl⟩ : syracuseStep 12306181 = 2307409) B2307409
theorem B3843863 : Blo 1707054 3843863 := bstep (se 1 (by rfl) ⟨2882897, by rfl⟩ : syracuseStep 3843863 = 5765795) B5765795
theorem B9725771 : Blo 1707054 9725771 := bstep (se 1 (by rfl) ⟨7294328, by rfl⟩ : syracuseStep 9725771 = 14588657) B14588657
theorem B4384601 : Blo 1707054 4384601 := bstep (se 2 (by rfl) ⟨1644225, by rfl⟩ : syracuseStep 4384601 = 3288451) B3288451
theorem B13846403 : Blo 1707054 13846403 := bstep (se 1 (by rfl) ⟨10384802, by rfl⟩ : syracuseStep 13846403 = 20769605) B20769605
theorem B3844043 : Blo 1707054 3844043 := bstep (se 1 (by rfl) ⟨2883032, by rfl⟩ : syracuseStep 3844043 = 5766065) B5766065
theorem B3844097 : Blo 1707054 3844097 := bstep (se 2 (by rfl) ⟨1441536, by rfl⟩ : syracuseStep 3844097 = 2883073) B2883073
theorem B85403717 : Blo 1707054 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B12314717 : Blo 1707054 12314717 := bstep (se 3 (by rfl) ⟨2309009, by rfl⟩ : syracuseStep 12314717 = 4618019) B4618019
theorem B6924419 : Blo 1707054 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B3844313 : Blo 1707054 3844313 := bstep (se 2 (by rfl) ⟨1441617, by rfl⟩ : syracuseStep 3844313 = 2883235) B2883235
theorem B7293235 : Blo 1707054 7293235 := bstep (se 1 (by rfl) ⟨5469926, by rfl⟩ : syracuseStep 7293235 = 10939853) B10939853
theorem B3844403 : Blo 1707054 3844403 := bstep (se 1 (by rfl) ⟨2883302, by rfl⟩ : syracuseStep 3844403 = 5766605) B5766605
theorem B3844439 : Blo 1707054 3844439 := bstep (se 1 (by rfl) ⟨2883329, by rfl⟩ : syracuseStep 3844439 = 5766659) B5766659
theorem B6924761 : Blo 1707054 6924761 := bstep (se 2 (by rfl) ⟨2596785, by rfl⟩ : syracuseStep 6924761 = 5193571) B5193571
theorem B3844619 : Blo 1707054 3844619 := bstep (se 1 (by rfl) ⟨2883464, by rfl⟩ : syracuseStep 3844619 = 5766929) B5766929
theorem B44362253 : Blo 1707054 44362253 := bstep (se 3 (by rfl) ⟨8317922, by rfl⟩ : syracuseStep 44362253 = 16635845) B16635845
theorem B3844673 : Blo 1707054 3844673 := bstep (se 2 (by rfl) ⟨1441752, by rfl⟩ : syracuseStep 3844673 = 2883505) B2883505
theorem B3844889 : Blo 1707054 3844889 := bstep (se 2 (by rfl) ⟨1441833, by rfl⟩ : syracuseStep 3844889 = 2883667) B2883667
theorem B12970853 : Blo 1707054 12970853 := bstep (se 4 (by rfl) ⟨1216017, by rfl⟩ : syracuseStep 12970853 = 2432035) B2432035
theorem B3844979 : Blo 1707054 3844979 := bstep (se 1 (by rfl) ⟨2883734, by rfl⟩ : syracuseStep 3844979 = 5767469) B5767469
theorem B3648395 : Blo 1707054 3648395 := bstep (se 1 (by rfl) ⟨2736296, by rfl⟩ : syracuseStep 3648395 = 5472593) B5472593
theorem B3845015 : Blo 1707054 3845015 := bstep (se 1 (by rfl) ⟨2883761, by rfl⟩ : syracuseStep 3845015 = 5767523) B5767523
theorem B6482861 : Blo 1707054 6482861 := bstep (se 3 (by rfl) ⟨1215536, by rfl⟩ : syracuseStep 6482861 = 2431073) B2431073
theorem B6237145 : Blo 1707054 6237145 := bstep (se 2 (by rfl) ⟨2338929, by rfl⟩ : syracuseStep 6237145 = 4677859) B4677859
theorem B1707063 : Blo 1707054 1707063 := bstep (se 1 (by rfl) ⟨1280297, by rfl⟩ : syracuseStep 1707063 = 2560595) B2560595
theorem B1707083 : Blo 1707054 1707083 := bstep (se 1 (by rfl) ⟨1280312, by rfl⟩ : syracuseStep 1707083 = 2560625) B2560625
theorem B5762123 : Blo 1707054 5762123 := bstep (se 1 (by rfl) ⟨4321592, by rfl⟩ : syracuseStep 5762123 = 8643185) B8643185
theorem B3845195 : Blo 1707054 3845195 := bstep (se 1 (by rfl) ⟨2883896, by rfl⟩ : syracuseStep 3845195 = 5767793) B5767793
theorem B1707095 : Blo 1707054 1707095 := bstep (se 1 (by rfl) ⟨1280321, by rfl⟩ : syracuseStep 1707095 = 2560643) B2560643
theorem B1707115 : Blo 1707054 1707115 := bstep (se 1 (by rfl) ⟨1280336, by rfl⟩ : syracuseStep 1707115 = 2560673) B2560673
theorem B1707127 : Blo 1707054 1707127 := bstep (se 1 (by rfl) ⟨1280345, by rfl⟩ : syracuseStep 1707127 = 2560691) B2560691
theorem B3845249 : Blo 1707054 3845249 := bstep (se 2 (by rfl) ⟨1441968, by rfl⟩ : syracuseStep 3845249 = 2883937) B2883937
theorem B1707147 : Blo 1707054 1707147 := bstep (se 1 (by rfl) ⟨1280360, by rfl⟩ : syracuseStep 1707147 = 2560721) B2560721
theorem B1707159 : Blo 1707054 1707159 := bstep (se 1 (by rfl) ⟨1280369, by rfl⟩ : syracuseStep 1707159 = 2560739) B2560739
theorem B1707179 : Blo 1707054 1707179 := bstep (se 1 (by rfl) ⟨1280384, by rfl⟩ : syracuseStep 1707179 = 2560769) B2560769
theorem B1707191 : Blo 1707054 1707191 := bstep (se 1 (by rfl) ⟨1280393, by rfl⟩ : syracuseStep 1707191 = 2560787) B2560787
theorem B1707211 : Blo 1707054 1707211 := bstep (se 1 (by rfl) ⟨1280408, by rfl⟩ : syracuseStep 1707211 = 2560817) B2560817
theorem B1707223 : Blo 1707054 1707223 := bstep (se 1 (by rfl) ⟨1280417, by rfl⟩ : syracuseStep 1707223 = 2560835) B2560835
theorem B1707243 : Blo 1707054 1707243 := bstep (se 1 (by rfl) ⟨1280432, by rfl⟩ : syracuseStep 1707243 = 2560865) B2560865
theorem B1707255 : Blo 1707054 1707255 := bstep (se 1 (by rfl) ⟨1280441, by rfl⟩ : syracuseStep 1707255 = 2560883) B2560883
theorem B12963077 : Blo 1707054 12963077 := bstep (se 4 (by rfl) ⟨1215288, by rfl⟩ : syracuseStep 12963077 = 2430577) B2430577
theorem B1707275 : Blo 1707054 1707275 := bstep (se 1 (by rfl) ⟨1280456, by rfl⟩ : syracuseStep 1707275 = 2560913) B2560913
theorem B1707287 : Blo 1707054 1707287 := bstep (se 1 (by rfl) ⟨1280465, by rfl⟩ : syracuseStep 1707287 = 2560931) B2560931
theorem B1707307 : Blo 1707054 1707307 := bstep (se 1 (by rfl) ⟨1280480, by rfl⟩ : syracuseStep 1707307 = 2560961) B2560961
theorem B4861235 : Blo 1707054 4861235 := bstep (se 1 (by rfl) ⟨3645926, by rfl⟩ : syracuseStep 4861235 = 7291853) B7291853
theorem B1707319 : Blo 1707054 1707319 := bstep (se 1 (by rfl) ⟨1280489, by rfl⟩ : syracuseStep 1707319 = 2560979) B2560979
theorem B1707339 : Blo 1707054 1707339 := bstep (se 1 (by rfl) ⟨1280504, by rfl⟩ : syracuseStep 1707339 = 2561009) B2561009
theorem B12971339 : Blo 1707054 12971339 := bstep (se 1 (by rfl) ⟨9728504, by rfl⟩ : syracuseStep 12971339 = 19457009) B19457009
theorem B1707351 : Blo 1707054 1707351 := bstep (se 1 (by rfl) ⟨1280513, by rfl⟩ : syracuseStep 1707351 = 2561027) B2561027
theorem B5762393 : Blo 1707054 5762393 := bstep (se 2 (by rfl) ⟨2160897, by rfl⟩ : syracuseStep 5762393 = 4321795) B4321795
theorem B1707371 : Blo 1707054 1707371 := bstep (se 1 (by rfl) ⟨1280528, by rfl⟩ : syracuseStep 1707371 = 2561057) B2561057
theorem B1707383 : Blo 1707054 1707383 := bstep (se 1 (by rfl) ⟨1280537, by rfl⟩ : syracuseStep 1707383 = 2561075) B2561075
theorem B1707403 : Blo 1707054 1707403 := bstep (se 1 (by rfl) ⟨1280552, by rfl⟩ : syracuseStep 1707403 = 2561105) B2561105
theorem B210439565 : Blo 1707054 210439565 := bstep (se 3 (by rfl) ⟨39457418, by rfl⟩ : syracuseStep 210439565 = 78914837) B78914837
theorem B1707415 : Blo 1707054 1707415 := bstep (se 1 (by rfl) ⟨1280561, by rfl⟩ : syracuseStep 1707415 = 2561123) B2561123
theorem B1707435 : Blo 1707054 1707435 := bstep (se 1 (by rfl) ⟨1280576, by rfl⟩ : syracuseStep 1707435 = 2561153) B2561153
theorem B9727411 : Blo 1707054 9727411 := bstep (se 1 (by rfl) ⟨7295558, by rfl⟩ : syracuseStep 9727411 = 14591117) B14591117
theorem B1707447 : Blo 1707054 1707447 := bstep (se 1 (by rfl) ⟨1280585, by rfl⟩ : syracuseStep 1707447 = 2561171) B2561171
theorem B1707467 : Blo 1707054 1707467 := bstep (se 1 (by rfl) ⟨1280600, by rfl⟩ : syracuseStep 1707467 = 2561201) B2561201
theorem B1707479 : Blo 1707054 1707479 := bstep (se 1 (by rfl) ⟨1280609, by rfl⟩ : syracuseStep 1707479 = 2561219) B2561219
theorem B3378649 : Blo 1707054 3378649 := bstep (se 2 (by rfl) ⟨1266993, by rfl⟩ : syracuseStep 3378649 = 2533987) B2533987
theorem B1707499 : Blo 1707054 1707499 := bstep (se 1 (by rfl) ⟨1280624, by rfl⟩ : syracuseStep 1707499 = 2561249) B2561249
theorem B1707511 : Blo 1707054 1707511 := bstep (se 1 (by rfl) ⟨1280633, by rfl⟩ : syracuseStep 1707511 = 2561267) B2561267
theorem B1920523 : Blo 1707054 1920523 := bstep (se 1 (by rfl) ⟨1440392, by rfl⟩ : syracuseStep 1920523 = 2880785) B2880785
theorem B1707531 : Blo 1707054 1707531 := bstep (se 1 (by rfl) ⟨1280648, by rfl⟩ : syracuseStep 1707531 = 2561297) B2561297
theorem B1707543 : Blo 1707054 1707543 := bstep (se 1 (by rfl) ⟨1280657, by rfl⟩ : syracuseStep 1707543 = 2561315) B2561315
theorem B1707563 : Blo 1707054 1707563 := bstep (se 1 (by rfl) ⟨1280672, by rfl⟩ : syracuseStep 1707563 = 2561345) B2561345
theorem B1707575 : Blo 1707054 1707575 := bstep (se 1 (by rfl) ⟨1280681, by rfl⟩ : syracuseStep 1707575 = 2561363) B2561363
theorem B1707595 : Blo 1707054 1707595 := bstep (se 1 (by rfl) ⟨1280696, by rfl⟩ : syracuseStep 1707595 = 2561393) B2561393
theorem B1707607 : Blo 1707054 1707607 := bstep (se 1 (by rfl) ⟨1280705, by rfl⟩ : syracuseStep 1707607 = 2561411) B2561411
theorem B1707627 : Blo 1707054 1707627 := bstep (se 1 (by rfl) ⟨1280720, by rfl⟩ : syracuseStep 1707627 = 2561441) B2561441
theorem B1920631 : Blo 1707054 1920631 := bstep (se 1 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 1920631 = 2880947) B2880947
theorem B1707639 : Blo 1707054 1707639 := bstep (se 1 (by rfl) ⟨1280729, by rfl⟩ : syracuseStep 1707639 = 2561459) B2561459
theorem B1707659 : Blo 1707054 1707659 := bstep (se 1 (by rfl) ⟨1280744, by rfl⟩ : syracuseStep 1707659 = 2561489) B2561489
theorem B1707671 : Blo 1707054 1707671 := bstep (se 1 (by rfl) ⟨1280753, by rfl⟩ : syracuseStep 1707671 = 2561507) B2561507
theorem B1707691 : Blo 1707054 1707691 := bstep (se 1 (by rfl) ⟨1280768, by rfl⟩ : syracuseStep 1707691 = 2561537) B2561537
theorem B7294637 : Blo 1707054 7294637 := bstep (se 3 (by rfl) ⟨1367744, by rfl⟩ : syracuseStep 7294637 = 2735489) B2735489
theorem B6483635 : Blo 1707054 6483635 := bstep (se 1 (by rfl) ⟨4862726, by rfl⟩ : syracuseStep 6483635 = 9725453) B9725453
theorem B14593715 : Blo 1707054 14593715 := bstep (se 1 (by rfl) ⟨10945286, by rfl⟩ : syracuseStep 14593715 = 21890573) B21890573
theorem B1707703 : Blo 1707054 1707703 := bstep (se 1 (by rfl) ⟨1280777, by rfl⟩ : syracuseStep 1707703 = 2561555) B2561555
theorem B4861633 : Blo 1707054 4861633 := bstep (se 2 (by rfl) ⟨1823112, by rfl⟩ : syracuseStep 4861633 = 3646225) B3646225
theorem B1707723 : Blo 1707054 1707723 := bstep (se 1 (by rfl) ⟨1280792, by rfl⟩ : syracuseStep 1707723 = 2561585) B2561585
theorem B3460823 : Blo 1707054 3460823 := bstep (se 1 (by rfl) ⟨2595617, by rfl⟩ : syracuseStep 3460823 = 5191235) B5191235
theorem B2920151 : Blo 1707054 2920151 := bstep (se 1 (by rfl) ⟨2190113, by rfl⟩ : syracuseStep 2920151 = 4380227) B4380227
theorem B4320985 : Blo 1707054 4320985 := bstep (se 2 (by rfl) ⟨1620369, by rfl⟩ : syracuseStep 4320985 = 3240739) B3240739
theorem B1707735 : Blo 1707054 1707735 := bstep (se 1 (by rfl) ⟨1280801, by rfl⟩ : syracuseStep 1707735 = 2561603) B2561603
theorem B1707755 : Blo 1707054 1707755 := bstep (se 1 (by rfl) ⟨1280816, by rfl⟩ : syracuseStep 1707755 = 2561633) B2561633
theorem B1707767 : Blo 1707054 1707767 := bstep (se 1 (by rfl) ⟨1280825, by rfl⟩ : syracuseStep 1707767 = 2561651) B2561651
theorem B1707787 : Blo 1707054 1707787 := bstep (se 1 (by rfl) ⟨1280840, by rfl⟩ : syracuseStep 1707787 = 2561681) B2561681
theorem B1707799 : Blo 1707054 1707799 := bstep (se 1 (by rfl) ⟨1280849, by rfl⟩ : syracuseStep 1707799 = 2561699) B2561699
theorem B1920811 : Blo 1707054 1920811 := bstep (se 1 (by rfl) ⟨1440608, by rfl⟩ : syracuseStep 1920811 = 2881217) B2881217
theorem B1707819 : Blo 1707054 1707819 := bstep (se 1 (by rfl) ⟨1280864, by rfl⟩ : syracuseStep 1707819 = 2561729) B2561729
theorem B1707831 : Blo 1707054 1707831 := bstep (se 1 (by rfl) ⟨1280873, by rfl⟩ : syracuseStep 1707831 = 2561747) B2561747
theorem B1707851 : Blo 1707054 1707851 := bstep (se 1 (by rfl) ⟨1280888, by rfl⟩ : syracuseStep 1707851 = 2561777) B2561777
theorem B1707863 : Blo 1707054 1707863 := bstep (se 1 (by rfl) ⟨1280897, by rfl⟩ : syracuseStep 1707863 = 2561795) B2561795
theorem B6156121 : Blo 1707054 6156121 := bstep (se 2 (by rfl) ⟨2308545, by rfl⟩ : syracuseStep 6156121 = 4617091) B4617091
theorem B3649369 : Blo 1707054 3649369 := bstep (se 2 (by rfl) ⟨1368513, by rfl⟩ : syracuseStep 3649369 = 2737027) B2737027
theorem B1707883 : Blo 1707054 1707883 := bstep (se 1 (by rfl) ⟨1280912, by rfl⟩ : syracuseStep 1707883 = 2561825) B2561825
theorem B1707895 : Blo 1707054 1707895 := bstep (se 1 (by rfl) ⟨1280921, by rfl⟩ : syracuseStep 1707895 = 2561843) B2561843
theorem B1707915 : Blo 1707054 1707915 := bstep (se 1 (by rfl) ⟨1280936, by rfl⟩ : syracuseStep 1707915 = 2561873) B2561873
theorem B1920919 : Blo 1707054 1920919 := bstep (se 1 (by rfl) ⟨1440689, by rfl⟩ : syracuseStep 1920919 = 2881379) B2881379
theorem B12308375 : Blo 1707054 12308375 := bstep (se 1 (by rfl) ⟨9231281, by rfl⟩ : syracuseStep 12308375 = 18462563) B18462563
theorem B1707927 : Blo 1707054 1707927 := bstep (se 1 (by rfl) ⟨1280945, by rfl⟩ : syracuseStep 1707927 = 2561891) B2561891
theorem B1707947 : Blo 1707054 1707947 := bstep (se 1 (by rfl) ⟨1280960, by rfl⟩ : syracuseStep 1707947 = 2561921) B2561921
theorem B1707959 : Blo 1707054 1707959 := bstep (se 1 (by rfl) ⟨1280969, by rfl⟩ : syracuseStep 1707959 = 2561939) B2561939
theorem B1707979 : Blo 1707054 1707979 := bstep (se 1 (by rfl) ⟨1280984, by rfl⟩ : syracuseStep 1707979 = 2561969) B2561969
theorem B1707991 : Blo 1707054 1707991 := bstep (se 1 (by rfl) ⟨1280993, by rfl⟩ : syracuseStep 1707991 = 2561987) B2561987
theorem B1708011 : Blo 1707054 1708011 := bstep (se 1 (by rfl) ⟨1281008, by rfl⟩ : syracuseStep 1708011 = 2562017) B2562017
theorem B1708023 : Blo 1707054 1708023 := bstep (se 1 (by rfl) ⟨1281017, by rfl⟩ : syracuseStep 1708023 = 2562035) B2562035
theorem B1708043 : Blo 1707054 1708043 := bstep (se 1 (by rfl) ⟨1281032, by rfl⟩ : syracuseStep 1708043 = 2562065) B2562065
theorem B6574097 : Blo 1707054 6574097 := bstep (se 2 (by rfl) ⟨2465286, by rfl⟩ : syracuseStep 6574097 = 4930573) B4930573
theorem B5763095 : Blo 1707054 5763095 := bstep (se 1 (by rfl) ⟨4322321, by rfl⟩ : syracuseStep 5763095 = 8644643) B8644643
theorem B1708055 : Blo 1707054 1708055 := bstep (se 1 (by rfl) ⟨1281041, by rfl⟩ : syracuseStep 1708055 = 2562083) B2562083
theorem B1708075 : Blo 1707054 1708075 := bstep (se 1 (by rfl) ⟨1281056, by rfl⟩ : syracuseStep 1708075 = 2562113) B2562113
theorem B6926381 : Blo 1707054 6926381 := bstep (se 3 (by rfl) ⟨1298696, by rfl⟩ : syracuseStep 6926381 = 2597393) B2597393
theorem B14594093 : Blo 1707054 14594093 := bstep (se 3 (by rfl) ⟨2736392, by rfl⟩ : syracuseStep 14594093 = 5472785) B5472785
theorem B1708087 : Blo 1707054 1708087 := bstep (se 1 (by rfl) ⟨1281065, by rfl⟩ : syracuseStep 1708087 = 2562131) B2562131
theorem B1921099 : Blo 1707054 1921099 := bstep (se 1 (by rfl) ⟨1440824, by rfl⟩ : syracuseStep 1921099 = 2881649) B2881649
theorem B1708107 : Blo 1707054 1708107 := bstep (se 1 (by rfl) ⟨1281080, by rfl⟩ : syracuseStep 1708107 = 2562161) B2562161
theorem B1708119 : Blo 1707054 1708119 := bstep (se 1 (by rfl) ⟨1281089, by rfl⟩ : syracuseStep 1708119 = 2562179) B2562179
theorem B3649625 : Blo 1707054 3649625 := bstep (se 2 (by rfl) ⟨1368609, by rfl⟩ : syracuseStep 3649625 = 2737219) B2737219
theorem B8646749 : Blo 1707054 8646749 := bstep (se 3 (by rfl) ⟨1621265, by rfl⟩ : syracuseStep 8646749 = 3242531) B3242531
theorem B1708139 : Blo 1707054 1708139 := bstep (se 1 (by rfl) ⟨1281104, by rfl⟩ : syracuseStep 1708139 = 2562209) B2562209
theorem B1708151 : Blo 1707054 1708151 := bstep (se 1 (by rfl) ⟨1281113, by rfl⟩ : syracuseStep 1708151 = 2562227) B2562227
theorem B1708171 : Blo 1707054 1708171 := bstep (se 1 (by rfl) ⟨1281128, by rfl⟩ : syracuseStep 1708171 = 2562257) B2562257
theorem B1708183 : Blo 1707054 1708183 := bstep (se 1 (by rfl) ⟨1281137, by rfl⟩ : syracuseStep 1708183 = 2562275) B2562275
theorem B1708203 : Blo 1707054 1708203 := bstep (se 1 (by rfl) ⟨1281152, by rfl⟩ : syracuseStep 1708203 = 2562305) B2562305
theorem B1921207 : Blo 1707054 1921207 := bstep (se 1 (by rfl) ⟨1440905, by rfl⟩ : syracuseStep 1921207 = 2881811) B2881811
theorem B1708215 : Blo 1707054 1708215 := bstep (se 1 (by rfl) ⟨1281161, by rfl⟩ : syracuseStep 1708215 = 2562323) B2562323
theorem B6574283 : Blo 1707054 6574283 := bstep (se 1 (by rfl) ⟨4930712, by rfl⟩ : syracuseStep 6574283 = 9861425) B9861425
theorem B1708235 : Blo 1707054 1708235 := bstep (se 1 (by rfl) ⟨1281176, by rfl⟩ : syracuseStep 1708235 = 2562353) B2562353
theorem B1708247 : Blo 1707054 1708247 := bstep (se 1 (by rfl) ⟨1281185, by rfl⟩ : syracuseStep 1708247 = 2562371) B2562371
theorem B1708267 : Blo 1707054 1708267 := bstep (se 1 (by rfl) ⟨1281200, by rfl⟩ : syracuseStep 1708267 = 2562401) B2562401
theorem B1708279 : Blo 1707054 1708279 := bstep (se 1 (by rfl) ⟨1281209, by rfl⟩ : syracuseStep 1708279 = 2562419) B2562419
theorem B1708299 : Blo 1707054 1708299 := bstep (se 1 (by rfl) ⟨1281224, by rfl⟩ : syracuseStep 1708299 = 2562449) B2562449
theorem B1708311 : Blo 1707054 1708311 := bstep (se 1 (by rfl) ⟨1281233, by rfl⟩ : syracuseStep 1708311 = 2562467) B2562467
theorem B1708331 : Blo 1707054 1708331 := bstep (se 1 (by rfl) ⟨1281248, by rfl⟩ : syracuseStep 1708331 = 2562497) B2562497
theorem B1708343 : Blo 1707054 1708343 := bstep (se 1 (by rfl) ⟨1281257, by rfl⟩ : syracuseStep 1708343 = 2562515) B2562515
theorem B1708363 : Blo 1707054 1708363 := bstep (se 1 (by rfl) ⟨1281272, by rfl⟩ : syracuseStep 1708363 = 2562545) B2562545
theorem B1708375 : Blo 1707054 1708375 := bstep (se 1 (by rfl) ⟨1281281, by rfl⟩ : syracuseStep 1708375 = 2562563) B2562563
theorem B1921387 : Blo 1707054 1921387 := bstep (se 1 (by rfl) ⟨1441040, by rfl⟩ : syracuseStep 1921387 = 2882081) B2882081
theorem B1708395 : Blo 1707054 1708395 := bstep (se 1 (by rfl) ⟨1281296, by rfl⟩ : syracuseStep 1708395 = 2562593) B2562593
theorem B1708407 : Blo 1707054 1708407 := bstep (se 1 (by rfl) ⟨1281305, by rfl⟩ : syracuseStep 1708407 = 2562611) B2562611
theorem B6238595 : Blo 1707054 6238595 := bstep (se 1 (by rfl) ⟨4678946, by rfl⟩ : syracuseStep 6238595 = 9357893) B9357893
theorem B1708427 : Blo 1707054 1708427 := bstep (se 1 (by rfl) ⟨1281320, by rfl⟩ : syracuseStep 1708427 = 2562641) B2562641
theorem B2052491 : Blo 1707054 2052491 := bstep (se 1 (by rfl) ⟨1539368, by rfl⟩ : syracuseStep 2052491 = 3078737) B3078737
theorem B1708439 : Blo 1707054 1708439 := bstep (se 1 (by rfl) ⟨1281329, by rfl⟩ : syracuseStep 1708439 = 2562659) B2562659
theorem B1708459 : Blo 1707054 1708459 := bstep (se 1 (by rfl) ⟨1281344, by rfl⟩ : syracuseStep 1708459 = 2562689) B2562689
theorem B1708471 : Blo 1707054 1708471 := bstep (se 1 (by rfl) ⟨1281353, by rfl⟩ : syracuseStep 1708471 = 2562707) B2562707
theorem B1708491 : Blo 1707054 1708491 := bstep (se 1 (by rfl) ⟨1281368, by rfl⟩ : syracuseStep 1708491 = 2562737) B2562737
theorem B1921495 : Blo 1707054 1921495 := bstep (se 1 (by rfl) ⟨1441121, by rfl⟩ : syracuseStep 1921495 = 2882243) B2882243
theorem B1708503 : Blo 1707054 1708503 := bstep (se 1 (by rfl) ⟨1281377, by rfl⟩ : syracuseStep 1708503 = 2562755) B2562755
theorem B1708523 : Blo 1707054 1708523 := bstep (se 1 (by rfl) ⟨1281392, by rfl⟩ : syracuseStep 1708523 = 2562785) B2562785
theorem B3650035 : Blo 1707054 3650035 := bstep (se 1 (by rfl) ⟨2737526, by rfl⟩ : syracuseStep 3650035 = 5475053) B5475053
theorem B1708535 : Blo 1707054 1708535 := bstep (se 1 (by rfl) ⟨1281401, by rfl⟩ : syracuseStep 1708535 = 2562803) B2562803
theorem B3461633 : Blo 1707054 3461633 := bstep (se 2 (by rfl) ⟨1298112, by rfl⟩ : syracuseStep 3461633 = 2596225) B2596225
theorem B1708555 : Blo 1707054 1708555 := bstep (se 1 (by rfl) ⟨1281416, by rfl⟩ : syracuseStep 1708555 = 2562833) B2562833
theorem B1708567 : Blo 1707054 1708567 := bstep (se 1 (by rfl) ⟨1281425, by rfl⟩ : syracuseStep 1708567 = 2562851) B2562851
theorem B3076633 : Blo 1707054 3076633 := bstep (se 2 (by rfl) ⟨1153737, by rfl⟩ : syracuseStep 3076633 = 2307475) B2307475
theorem B1708587 : Blo 1707054 1708587 := bstep (se 1 (by rfl) ⟨1281440, by rfl⟩ : syracuseStep 1708587 = 2562881) B2562881
theorem B7787053 : Blo 1707054 7787053 := bstep (se 3 (by rfl) ⟨1460072, by rfl⟩ : syracuseStep 7787053 = 2920145) B2920145
theorem B7393837 : Blo 1707054 7393837 := bstep (se 3 (by rfl) ⟨1386344, by rfl⟩ : syracuseStep 7393837 = 2772689) B2772689
theorem B5763635 : Blo 1707054 5763635 := bstep (se 1 (by rfl) ⟨4322726, by rfl⟩ : syracuseStep 5763635 = 8645453) B8645453
theorem B1708599 : Blo 1707054 1708599 := bstep (se 1 (by rfl) ⟨1281449, by rfl⟩ : syracuseStep 1708599 = 2562899) B2562899
theorem B1708619 : Blo 1707054 1708619 := bstep (se 1 (by rfl) ⟨1281464, by rfl⟩ : syracuseStep 1708619 = 2562929) B2562929
theorem B1708631 : Blo 1707054 1708631 := bstep (se 1 (by rfl) ⟨1281473, by rfl⟩ : syracuseStep 1708631 = 2562947) B2562947
theorem B2560601 : Blo 1707054 2560601 := bstep (se 2 (by rfl) ⟨960225, by rfl⟩ : syracuseStep 2560601 = 1920451) B1920451
theorem B1708651 : Blo 1707054 1708651 := bstep (se 1 (by rfl) ⟨1281488, by rfl⟩ : syracuseStep 1708651 = 2562977) B2562977
theorem B1708663 : Blo 1707054 1708663 := bstep (se 1 (by rfl) ⟨1281497, by rfl⟩ : syracuseStep 1708663 = 2562995) B2562995
theorem B1921675 : Blo 1707054 1921675 := bstep (se 1 (by rfl) ⟨1441256, by rfl⟩ : syracuseStep 1921675 = 2882513) B2882513
theorem B1708683 : Blo 1707054 1708683 := bstep (se 1 (by rfl) ⟨1281512, by rfl⟩ : syracuseStep 1708683 = 2563025) B2563025
theorem B1708695 : Blo 1707054 1708695 := bstep (se 1 (by rfl) ⟨1281521, by rfl⟩ : syracuseStep 1708695 = 2563043) B2563043
theorem B1708715 : Blo 1707054 1708715 := bstep (se 1 (by rfl) ⟨1281536, by rfl⟩ : syracuseStep 1708715 = 2563073) B2563073
theorem B1708727 : Blo 1707054 1708727 := bstep (se 1 (by rfl) ⟨1281545, by rfl⟩ : syracuseStep 1708727 = 2563091) B2563091
theorem B2560715 : Blo 1707054 2560715 := bstep (se 1 (by rfl) ⟨1920536, by rfl⟩ : syracuseStep 2560715 = 3841073) B3841073
theorem B1708747 : Blo 1707054 1708747 := bstep (se 1 (by rfl) ⟨1281560, by rfl⟩ : syracuseStep 1708747 = 2563121) B2563121
theorem B2560727 : Blo 1707054 2560727 := bstep (se 1 (by rfl) ⟨1920545, by rfl⟩ : syracuseStep 2560727 = 3841091) B3841091
theorem B1708759 : Blo 1707054 1708759 := bstep (se 1 (by rfl) ⟨1281569, by rfl⟩ : syracuseStep 1708759 = 2563139) B2563139
theorem B1708779 : Blo 1707054 1708779 := bstep (se 1 (by rfl) ⟨1281584, by rfl⟩ : syracuseStep 1708779 = 2563169) B2563169
theorem B1921783 : Blo 1707054 1921783 := bstep (se 1 (by rfl) ⟨1441337, by rfl⟩ : syracuseStep 1921783 = 2882675) B2882675
theorem B1708791 : Blo 1707054 1708791 := bstep (se 1 (by rfl) ⟨1281593, by rfl⟩ : syracuseStep 1708791 = 2563187) B2563187
theorem B1708811 : Blo 1707054 1708811 := bstep (se 1 (by rfl) ⟨1281608, by rfl⟩ : syracuseStep 1708811 = 2563217) B2563217
theorem B1708823 : Blo 1707054 1708823 := bstep (se 1 (by rfl) ⟨1281617, by rfl⟩ : syracuseStep 1708823 = 2563235) B2563235
theorem B4682519 : Blo 1707054 4682519 := bstep (se 1 (by rfl) ⟨3511889, by rfl⟩ : syracuseStep 4682519 = 7023779) B7023779
theorem B2560793 : Blo 1707054 2560793 := bstep (se 2 (by rfl) ⟨960297, by rfl⟩ : syracuseStep 2560793 = 1920595) B1920595
theorem B1823531 : Blo 1707054 1823531 := bstep (se 1 (by rfl) ⟨1367648, by rfl⟩ : syracuseStep 1823531 = 2735297) B2735297
theorem B1708843 : Blo 1707054 1708843 := bstep (se 1 (by rfl) ⟨1281632, by rfl⟩ : syracuseStep 1708843 = 2563265) B2563265
theorem B4322099 : Blo 1707054 4322099 := bstep (se 1 (by rfl) ⟨3241574, by rfl⟩ : syracuseStep 4322099 = 6483149) B6483149
theorem B1708855 : Blo 1707054 1708855 := bstep (se 1 (by rfl) ⟨1281641, by rfl⟩ : syracuseStep 1708855 = 2563283) B2563283
theorem B5763905 : Blo 1707054 5763905 := bstep (se 2 (by rfl) ⟨2161464, by rfl⟩ : syracuseStep 5763905 = 4322929) B4322929
theorem B1708875 : Blo 1707054 1708875 := bstep (se 1 (by rfl) ⟨1281656, by rfl⟩ : syracuseStep 1708875 = 2563313) B2563313
theorem B1708887 : Blo 1707054 1708887 := bstep (se 1 (by rfl) ⟨1281665, by rfl⟩ : syracuseStep 1708887 = 2563331) B2563331
theorem B9728869 : Blo 1707054 9728869 := bstep (se 4 (by rfl) ⟨912081, by rfl⟩ : syracuseStep 9728869 = 1824163) B1824163
theorem B1708907 : Blo 1707054 1708907 := bstep (se 1 (by rfl) ⟨1281680, by rfl⟩ : syracuseStep 1708907 = 2563361) B2563361
theorem B1708919 : Blo 1707054 1708919 := bstep (se 1 (by rfl) ⟨1281689, by rfl⟩ : syracuseStep 1708919 = 2563379) B2563379
theorem B2560907 : Blo 1707054 2560907 := bstep (se 1 (by rfl) ⟨1920680, by rfl⟩ : syracuseStep 2560907 = 3841361) B3841361
theorem B1708939 : Blo 1707054 1708939 := bstep (se 1 (by rfl) ⟨1281704, by rfl⟩ : syracuseStep 1708939 = 2563409) B2563409
theorem B2560919 : Blo 1707054 2560919 := bstep (se 1 (by rfl) ⟨1920689, by rfl⟩ : syracuseStep 2560919 = 3841379) B3841379
theorem B1708951 : Blo 1707054 1708951 := bstep (se 1 (by rfl) ⟨1281713, by rfl⟩ : syracuseStep 1708951 = 2563427) B2563427
theorem B1921963 : Blo 1707054 1921963 := bstep (se 1 (by rfl) ⟨1441472, by rfl⟩ : syracuseStep 1921963 = 2882945) B2882945
theorem B1708971 : Blo 1707054 1708971 := bstep (se 1 (by rfl) ⟨1281728, by rfl⟩ : syracuseStep 1708971 = 2563457) B2563457
theorem B1708983 : Blo 1707054 1708983 := bstep (se 1 (by rfl) ⟨1281737, by rfl⟩ : syracuseStep 1708983 = 2563475) B2563475
theorem B1709003 : Blo 1707054 1709003 := bstep (se 1 (by rfl) ⟨1281752, by rfl⟩ : syracuseStep 1709003 = 2563505) B2563505
theorem B1709015 : Blo 1707054 1709015 := bstep (se 1 (by rfl) ⟨1281761, by rfl⟩ : syracuseStep 1709015 = 2563523) B2563523
theorem B2560985 : Blo 1707054 2560985 := bstep (se 2 (by rfl) ⟨960369, by rfl⟩ : syracuseStep 2560985 = 1920739) B1920739
theorem B1709035 : Blo 1707054 1709035 := bstep (se 1 (by rfl) ⟨1281776, by rfl⟩ : syracuseStep 1709035 = 2563553) B2563553
theorem B1709047 : Blo 1707054 1709047 := bstep (se 1 (by rfl) ⟨1281785, by rfl⟩ : syracuseStep 1709047 = 2563571) B2563571
theorem B3511297 : Blo 1707054 3511297 := bstep (se 2 (by rfl) ⟨1316736, by rfl⟩ : syracuseStep 3511297 = 2633473) B2633473
theorem B1922071 : Blo 1707054 1922071 := bstep (se 1 (by rfl) ⟨1441553, by rfl⟩ : syracuseStep 1922071 = 2883107) B2883107
theorem B2561099 : Blo 1707054 2561099 := bstep (se 1 (by rfl) ⟨1920824, by rfl⟩ : syracuseStep 2561099 = 3841649) B3841649
theorem B2561111 : Blo 1707054 2561111 := bstep (se 1 (by rfl) ⟨1920833, by rfl⟩ : syracuseStep 2561111 = 3841667) B3841667
theorem B4322393 : Blo 1707054 4322393 := bstep (se 2 (by rfl) ⟨1620897, by rfl⟩ : syracuseStep 4322393 = 3241795) B3241795
theorem B6485123 : Blo 1707054 6485123 := bstep (se 1 (by rfl) ⟨4863842, by rfl⟩ : syracuseStep 6485123 = 9727685) B9727685
theorem B2561177 : Blo 1707054 2561177 := bstep (se 2 (by rfl) ⟨960441, by rfl⟩ : syracuseStep 2561177 = 1920883) B1920883
theorem B1922251 : Blo 1707054 1922251 := bstep (se 1 (by rfl) ⟨1441688, by rfl⟩ : syracuseStep 1922251 = 2883377) B2883377
theorem B2561291 : Blo 1707054 2561291 := bstep (se 1 (by rfl) ⟨1920968, by rfl⟩ : syracuseStep 2561291 = 3841937) B3841937
theorem B2561303 : Blo 1707054 2561303 := bstep (se 1 (by rfl) ⟨1920977, by rfl⟩ : syracuseStep 2561303 = 3841955) B3841955
theorem B1922359 : Blo 1707054 1922359 := bstep (se 1 (by rfl) ⟨1441769, by rfl⟩ : syracuseStep 1922359 = 2883539) B2883539
theorem B2561369 : Blo 1707054 2561369 := bstep (se 2 (by rfl) ⟨960513, by rfl⟩ : syracuseStep 2561369 = 1921027) B1921027
theorem B5764445 : Blo 1707054 5764445 := bstep (se 3 (by rfl) ⟨1080833, by rfl⟩ : syracuseStep 5764445 = 2161667) B2161667
theorem B3077527 : Blo 1707054 3077527 := bstep (se 1 (by rfl) ⟨2308145, by rfl⟩ : syracuseStep 3077527 = 4616291) B4616291
theorem B5469619 : Blo 1707054 5469619 := bstep (se 1 (by rfl) ⟨4102214, by rfl⟩ : syracuseStep 5469619 = 8204429) B8204429
theorem B2561483 : Blo 1707054 2561483 := bstep (se 1 (by rfl) ⟨1921112, by rfl⟩ : syracuseStep 2561483 = 3842225) B3842225
theorem B2561495 : Blo 1707054 2561495 := bstep (se 1 (by rfl) ⟨1921121, by rfl⟩ : syracuseStep 2561495 = 3842243) B3842243
theorem B1922539 : Blo 1707054 1922539 := bstep (se 1 (by rfl) ⟨1441904, by rfl⟩ : syracuseStep 1922539 = 2883809) B2883809
theorem B6927875 : Blo 1707054 6927875 := bstep (se 1 (by rfl) ⟨5195906, by rfl⟩ : syracuseStep 6927875 = 10391813) B10391813
theorem B2561561 : Blo 1707054 2561561 := bstep (se 2 (by rfl) ⟨960585, by rfl⟩ : syracuseStep 2561561 = 1921171) B1921171
theorem B6485579 : Blo 1707054 6485579 := bstep (se 1 (by rfl) ⟨4864184, by rfl⟩ : syracuseStep 6485579 = 9728369) B9728369
theorem B3241559 : Blo 1707054 3241559 := bstep (se 1 (by rfl) ⟨2431169, by rfl⟩ : syracuseStep 3241559 = 4862339) B4862339
theorem B1922647 : Blo 1707054 1922647 := bstep (se 1 (by rfl) ⟨1441985, by rfl⟩ : syracuseStep 1922647 = 2883971) B2883971
theorem B12965507 : Blo 1707054 12965507 := bstep (se 1 (by rfl) ⟨9724130, by rfl⟩ : syracuseStep 12965507 = 19448261) B19448261
theorem B2881163 : Blo 1707054 2881163 := bstep (se 1 (by rfl) ⟨2160872, by rfl⟩ : syracuseStep 2881163 = 4321745) B4321745
theorem B2561675 : Blo 1707054 2561675 := bstep (se 1 (by rfl) ⟨1921256, by rfl⟩ : syracuseStep 2561675 = 3842513) B3842513
theorem B2561687 : Blo 1707054 2561687 := bstep (se 1 (by rfl) ⟨1921265, by rfl⟩ : syracuseStep 2561687 = 3842531) B3842531
theorem B4380311 : Blo 1707054 4380311 := bstep (se 1 (by rfl) ⟨3285233, by rfl⟩ : syracuseStep 4380311 = 6570467) B6570467
theorem B2307799 : Blo 1707054 2307799 := bstep (se 1 (by rfl) ⟨1730849, by rfl⟩ : syracuseStep 2307799 = 3461699) B3461699
theorem B2561753 : Blo 1707054 2561753 := bstep (se 2 (by rfl) ⟨960657, by rfl⟩ : syracuseStep 2561753 = 1921315) B1921315
theorem B2881291 : Blo 1707054 2881291 := bstep (se 1 (by rfl) ⟨2160968, by rfl⟩ : syracuseStep 2881291 = 4321937) B4321937
theorem B6485777 : Blo 1707054 6485777 := bstep (se 2 (by rfl) ⟨2432166, by rfl⟩ : syracuseStep 6485777 = 4864333) B4864333
theorem B1824535 : Blo 1707054 1824535 := bstep (se 1 (by rfl) ⟨1368401, by rfl⟩ : syracuseStep 1824535 = 2736803) B2736803
theorem B2561867 : Blo 1707054 2561867 := bstep (se 1 (by rfl) ⟨1921400, by rfl⟩ : syracuseStep 2561867 = 3842801) B3842801
theorem B2561879 : Blo 1707054 2561879 := bstep (se 1 (by rfl) ⟨1921409, by rfl⟩ : syracuseStep 2561879 = 3842819) B3842819
theorem B4929373 : Blo 1707054 4929373 := bstep (se 3 (by rfl) ⟨924257, by rfl⟩ : syracuseStep 4929373 = 1848515) B1848515
theorem B3078017 : Blo 1707054 3078017 := bstep (se 2 (by rfl) ⟨1154256, by rfl⟩ : syracuseStep 3078017 = 2308513) B2308513
theorem B2160523 : Blo 1707054 2160523 := bstep (se 1 (by rfl) ⟨1620392, by rfl⟩ : syracuseStep 2160523 = 3240785) B3240785
theorem B3749771 : Blo 1707054 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B2881433 : Blo 1707054 2881433 := bstep (se 2 (by rfl) ⟨1080537, by rfl⟩ : syracuseStep 2881433 = 2161075) B2161075
theorem B2561945 : Blo 1707054 2561945 := bstep (se 2 (by rfl) ⟨960729, by rfl⟩ : syracuseStep 2561945 = 1921459) B1921459
theorem B2562059 : Blo 1707054 2562059 := bstep (se 1 (by rfl) ⟨1921544, by rfl⟩ : syracuseStep 2562059 = 3843089) B3843089
theorem B2562071 : Blo 1707054 2562071 := bstep (se 1 (by rfl) ⟨1921553, by rfl⟩ : syracuseStep 2562071 = 3843107) B3843107
theorem B2881561 : Blo 1707054 2881561 := bstep (se 2 (by rfl) ⟨1080585, by rfl⟩ : syracuseStep 2881561 = 2161171) B2161171
theorem B2562137 : Blo 1707054 2562137 := bstep (se 2 (by rfl) ⟨960801, by rfl⟩ : syracuseStep 2562137 = 1921603) B1921603
theorem B3242099 : Blo 1707054 3242099 := bstep (se 1 (by rfl) ⟨2431574, by rfl⟩ : syracuseStep 3242099 = 4863149) B4863149
theorem B4864151 : Blo 1707054 4864151 := bstep (se 1 (by rfl) ⟨3648113, by rfl⟩ : syracuseStep 4864151 = 7296227) B7296227
theorem B8648855 : Blo 1707054 8648855 := bstep (se 1 (by rfl) ⟨6486641, by rfl⟩ : syracuseStep 8648855 = 12973283) B12973283
theorem B8763571 : Blo 1707054 8763571 := bstep (se 1 (by rfl) ⟨6572678, by rfl⟩ : syracuseStep 8763571 = 13145357) B13145357
theorem B4159667 : Blo 1707054 4159667 := bstep (se 1 (by rfl) ⟨3119750, by rfl⟩ : syracuseStep 4159667 = 6239501) B6239501
theorem B24967349 : Blo 1707054 24967349 := bstep (se 5 (by rfl) ⟨1170344, by rfl⟩ : syracuseStep 24967349 = 2340689) B2340689
theorem B2562251 : Blo 1707054 2562251 := bstep (se 1 (by rfl) ⟨1921688, by rfl⟩ : syracuseStep 2562251 = 3843377) B3843377
theorem B2562263 : Blo 1707054 2562263 := bstep (se 1 (by rfl) ⟨1921697, by rfl⟩ : syracuseStep 2562263 = 3843395) B3843395
theorem B2562329 : Blo 1707054 2562329 := bstep (se 2 (by rfl) ⟨960873, by rfl⟩ : syracuseStep 2562329 = 1921747) B1921747
theorem B13850945 : Blo 1707054 13850945 := bstep (se 2 (by rfl) ⟨5194104, by rfl⟩ : syracuseStep 13850945 = 10388209) B10388209
theorem B1947991 : Blo 1707054 1947991 := bstep (se 1 (by rfl) ⟨1460993, by rfl⟩ : syracuseStep 1947991 = 2921987) B2921987
theorem B2562443 : Blo 1707054 2562443 := bstep (se 1 (by rfl) ⟨1921832, by rfl⟩ : syracuseStep 2562443 = 3843665) B3843665
theorem B2562455 : Blo 1707054 2562455 := bstep (se 1 (by rfl) ⟨1921841, by rfl⟩ : syracuseStep 2562455 = 3843683) B3843683
theorem B5765579 : Blo 1707054 5765579 := bstep (se 1 (by rfl) ⟨4324184, by rfl⟩ : syracuseStep 5765579 = 8648369) B8648369
theorem B2562521 : Blo 1707054 2562521 := bstep (se 2 (by rfl) ⟨960945, by rfl⟩ : syracuseStep 2562521 = 1921891) B1921891
theorem B21895697 : Blo 1707054 21895697 := bstep (se 2 (by rfl) ⟨8210886, by rfl⟩ : syracuseStep 21895697 = 16421773) B16421773
theorem B6486551 : Blo 1707054 6486551 := bstep (se 1 (by rfl) ⟨4864913, by rfl⟩ : syracuseStep 6486551 = 9729827) B9729827
theorem B2562635 : Blo 1707054 2562635 := bstep (se 1 (by rfl) ⟨1921976, by rfl⟩ : syracuseStep 2562635 = 3843953) B3843953
theorem B2882135 : Blo 1707054 2882135 := bstep (se 1 (by rfl) ⟨2161601, by rfl⟩ : syracuseStep 2882135 = 4323203) B4323203
theorem B3242585 : Blo 1707054 3242585 := bstep (se 2 (by rfl) ⟨1215969, by rfl⟩ : syracuseStep 3242585 = 2431939) B2431939
theorem B2562647 : Blo 1707054 2562647 := bstep (se 1 (by rfl) ⟨1921985, by rfl⟩ : syracuseStep 2562647 = 3843971) B3843971
theorem B2562713 : Blo 1707054 2562713 := bstep (se 2 (by rfl) ⟨961017, by rfl⟩ : syracuseStep 2562713 = 1922035) B1922035
theorem B8207027 : Blo 1707054 8207027 := bstep (se 1 (by rfl) ⟨6155270, by rfl⟩ : syracuseStep 8207027 = 12310541) B12310541
theorem B4324043 : Blo 1707054 4324043 := bstep (se 1 (by rfl) ⟨3243032, by rfl⟩ : syracuseStep 4324043 = 6486065) B6486065
theorem B2882263 : Blo 1707054 2882263 := bstep (se 1 (by rfl) ⟨2161697, by rfl⟩ : syracuseStep 2882263 = 4323395) B4323395
theorem B5765849 : Blo 1707054 5765849 := bstep (se 2 (by rfl) ⟨2162193, by rfl⟩ : syracuseStep 5765849 = 4324387) B4324387
theorem B3463897 : Blo 1707054 3463897 := bstep (se 2 (by rfl) ⟨1298961, by rfl⟩ : syracuseStep 3463897 = 2597923) B2597923
theorem B6486749 : Blo 1707054 6486749 := bstep (se 3 (by rfl) ⟨1216265, by rfl⟩ : syracuseStep 6486749 = 2432531) B2432531
theorem B2562827 : Blo 1707054 2562827 := bstep (se 1 (by rfl) ⟨1922120, by rfl⟩ : syracuseStep 2562827 = 3844241) B3844241
theorem B10525457 : Blo 1707054 10525457 := bstep (se 2 (by rfl) ⟨3947046, by rfl⟩ : syracuseStep 10525457 = 7894093) B7894093
theorem B2562839 : Blo 1707054 2562839 := bstep (se 1 (by rfl) ⟨1922129, by rfl⟩ : syracuseStep 2562839 = 3844259) B3844259
theorem B2431819 : Blo 1707054 2431819 := bstep (se 1 (by rfl) ⟨1823864, by rfl⟩ : syracuseStep 2431819 = 3647729) B3647729
theorem B2161495 : Blo 1707054 2161495 := bstep (se 1 (by rfl) ⟨1621121, by rfl⟩ : syracuseStep 2161495 = 3242243) B3242243
theorem B2562905 : Blo 1707054 2562905 := bstep (se 2 (by rfl) ⟨961089, by rfl⟩ : syracuseStep 2562905 = 1922179) B1922179
theorem B3840947 : Blo 1707054 3840947 := bstep (se 1 (by rfl) ⟨2880710, by rfl⟩ : syracuseStep 3840947 = 5761421) B5761421
theorem B2563019 : Blo 1707054 2563019 := bstep (se 1 (by rfl) ⟨1922264, by rfl⟩ : syracuseStep 2563019 = 3844529) B3844529
theorem B3840983 : Blo 1707054 3840983 := bstep (se 1 (by rfl) ⟨2880737, by rfl⟩ : syracuseStep 3840983 = 5761475) B5761475
theorem B2563031 : Blo 1707054 2563031 := bstep (se 1 (by rfl) ⟨1922273, by rfl⟩ : syracuseStep 2563031 = 3844547) B3844547
theorem B2563097 : Blo 1707054 2563097 := bstep (se 2 (by rfl) ⟨961161, by rfl⟩ : syracuseStep 2563097 = 1922323) B1922323
theorem B3841163 : Blo 1707054 3841163 := bstep (se 1 (by rfl) ⟨2880872, by rfl⟩ : syracuseStep 3841163 = 5761745) B5761745
theorem B2563211 : Blo 1707054 2563211 := bstep (se 1 (by rfl) ⟨1922408, by rfl⟩ : syracuseStep 2563211 = 3844817) B3844817
theorem B2563223 : Blo 1707054 2563223 := bstep (se 1 (by rfl) ⟨1922417, by rfl⟩ : syracuseStep 2563223 = 3844835) B3844835
theorem B3841217 : Blo 1707054 3841217 := bstep (se 2 (by rfl) ⟨1440456, by rfl⟩ : syracuseStep 3841217 = 2880913) B2880913
theorem B2563289 : Blo 1707054 2563289 := bstep (se 2 (by rfl) ⟨961233, by rfl⟩ : syracuseStep 2563289 = 1922467) B1922467
theorem B70139141 : Blo 1707054 70139141 := bstep (se 4 (by rfl) ⟨6575544, by rfl⟩ : syracuseStep 70139141 = 13151089) B13151089
theorem B5193035 : Blo 1707054 5193035 := bstep (se 1 (by rfl) ⟨3894776, by rfl⟩ : syracuseStep 5193035 = 7789553) B7789553
theorem B2882891 : Blo 1707054 2882891 := bstep (se 1 (by rfl) ⟨2162168, by rfl⟩ : syracuseStep 2882891 = 4324337) B4324337
theorem B2563403 : Blo 1707054 2563403 := bstep (se 1 (by rfl) ⟨1922552, by rfl⟩ : syracuseStep 2563403 = 3845105) B3845105
theorem B2563415 : Blo 1707054 2563415 := bstep (se 1 (by rfl) ⟨1922561, by rfl⟩ : syracuseStep 2563415 = 3845123) B3845123
theorem B7396697 : Blo 1707054 7396697 := bstep (se 2 (by rfl) ⟨2773761, by rfl⟩ : syracuseStep 7396697 = 5547523) B5547523
theorem B13319525 : Blo 1707054 13319525 := bstep (se 4 (by rfl) ⟨1248705, by rfl⟩ : syracuseStep 13319525 = 2497411) B2497411
theorem B7396759 : Blo 1707054 7396759 := bstep (se 1 (by rfl) ⟨5547569, by rfl⟩ : syracuseStep 7396759 = 11095139) B11095139
theorem B5766551 : Blo 1707054 5766551 := bstep (se 1 (by rfl) ⟨4324913, by rfl⟩ : syracuseStep 5766551 = 8649827) B8649827
theorem B3841433 : Blo 1707054 3841433 := bstep (se 2 (by rfl) ⟨1440537, by rfl⟩ : syracuseStep 3841433 = 2881075) B2881075
theorem B2563481 : Blo 1707054 2563481 := bstep (se 2 (by rfl) ⟨961305, by rfl⟩ : syracuseStep 2563481 = 1922611) B1922611
theorem B2883019 : Blo 1707054 2883019 := bstep (se 1 (by rfl) ⟨2162264, by rfl⟩ : syracuseStep 2883019 = 4324529) B4324529
theorem B4865483 : Blo 1707054 4865483 := bstep (se 1 (by rfl) ⟨3649112, by rfl⟩ : syracuseStep 4865483 = 7298225) B7298225
theorem B3841523 : Blo 1707054 3841523 := bstep (se 1 (by rfl) ⟨2881142, by rfl⟩ : syracuseStep 3841523 = 5762285) B5762285
theorem B15588881 : Blo 1707054 15588881 := bstep (se 2 (by rfl) ⟨5845830, by rfl⟩ : syracuseStep 15588881 = 11691661) B11691661
theorem B3841559 : Blo 1707054 3841559 := bstep (se 1 (by rfl) ⟨2881169, by rfl⟩ : syracuseStep 3841559 = 5762339) B5762339
theorem B2883161 : Blo 1707054 2883161 := bstep (se 2 (by rfl) ⟨1081185, by rfl⟩ : syracuseStep 2883161 = 2162371) B2162371
theorem B2162315 : Blo 1707054 2162315 := bstep (se 1 (by rfl) ⟨1621736, by rfl⟩ : syracuseStep 2162315 = 3243473) B3243473
theorem B4325015 : Blo 1707054 4325015 := bstep (se 1 (by rfl) ⟨3243761, by rfl⟩ : syracuseStep 4325015 = 6487523) B6487523
theorem B3841739 : Blo 1707054 3841739 := bstep (se 1 (by rfl) ⟨2881304, by rfl⟩ : syracuseStep 3841739 = 5762609) B5762609
theorem B29982413 : Blo 1707054 29982413 := bstep (se 3 (by rfl) ⟨5621702, by rfl⟩ : syracuseStep 29982413 = 11243405) B11243405
theorem B2883289 : Blo 1707054 2883289 := bstep (se 2 (by rfl) ⟨1081233, by rfl⟩ : syracuseStep 2883289 = 2162467) B2162467
theorem B5471965 : Blo 1707054 5471965 := bstep (se 3 (by rfl) ⟨1025993, by rfl⟩ : syracuseStep 5471965 = 2051987) B2051987
theorem B3841793 : Blo 1707054 3841793 := bstep (se 2 (by rfl) ⟨1440672, by rfl⟩ : syracuseStep 3841793 = 2881345) B2881345
theorem B7298839 : Blo 1707054 7298839 := bstep (se 1 (by rfl) ⟨5474129, by rfl⟩ : syracuseStep 7298839 = 10948259) B10948259
theorem B18472769 : Blo 1707054 18472769 := bstep (se 2 (by rfl) ⟨6927288, by rfl⟩ : syracuseStep 18472769 = 13854577) B13854577
theorem B7298909 : Blo 1707054 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B6922163 : Blo 1707054 6922163 := bstep (se 1 (by rfl) ⟨5191622, by rfl⟩ : syracuseStep 6922163 = 10383245) B10383245
theorem B5767091 : Blo 1707054 5767091 := bstep (se 1 (by rfl) ⟨4325318, by rfl⟩ : syracuseStep 5767091 = 8650637) B8650637
theorem B13844429 : Blo 1707054 13844429 := bstep (se 3 (by rfl) ⟨2595830, by rfl⟩ : syracuseStep 13844429 = 5191661) B5191661
theorem B3842009 : Blo 1707054 3842009 := bstep (se 2 (by rfl) ⟨1440753, by rfl⟩ : syracuseStep 3842009 = 2881507) B2881507
theorem B36945881 : Blo 1707054 36945881 := bstep (se 2 (by rfl) ⟨13854705, by rfl⟩ : syracuseStep 36945881 = 27709411) B27709411
theorem B2162695 : Blo 1707054 2162695 := bstep (se 1 (by rfl) ⟨1622021, by rfl⟩ : syracuseStep 2162695 = 3244043) B3244043
theorem B4382731 : Blo 1707054 4382731 := bstep (se 1 (by rfl) ⟨3287048, by rfl⟩ : syracuseStep 4382731 = 6574097) B6574097
theorem B3842063 : Blo 1707054 3842063 := bstep (se 1 (by rfl) ⟨2881547, by rfl⟩ : syracuseStep 3842063 = 5763095) B5763095
theorem B3842081 : Blo 1707054 3842081 := bstep (se 2 (by rfl) ⟨1440780, by rfl⟩ : syracuseStep 3842081 = 2881561) B2881561
theorem B2433083 : Blo 1707054 2433083 := bstep (se 1 (by rfl) ⟨1824812, by rfl⟩ : syracuseStep 2433083 = 3649625) B3649625
theorem B4382855 : Blo 1707054 4382855 := bstep (se 1 (by rfl) ⟨3287141, by rfl⟩ : syracuseStep 4382855 = 6574283) B6574283
theorem B4325633 : Blo 1707054 4325633 := bstep (se 2 (by rfl) ⟨1622112, by rfl⟩ : syracuseStep 4325633 = 3244225) B3244225
theorem B2883883 : Blo 1707054 2883883 := bstep (se 1 (by rfl) ⟨2162912, by rfl⟩ : syracuseStep 2883883 = 4325825) B4325825
theorem B10944827 : Blo 1707054 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B8651123 : Blo 1707054 8651123 := bstep (se 1 (by rfl) ⟨6488342, by rfl⟩ : syracuseStep 8651123 = 12976685) B12976685
theorem B3842423 : Blo 1707054 3842423 := bstep (se 1 (by rfl) ⟨2881817, by rfl⟩ : syracuseStep 3842423 = 5763635) B5763635
theorem B9724313 : Blo 1707054 9724313 := bstep (se 2 (by rfl) ⟨3646617, by rfl⟩ : syracuseStep 9724313 = 7293235) B7293235
theorem B5767577 : Blo 1707054 5767577 := bstep (se 2 (by rfl) ⟨2162841, by rfl⟩ : syracuseStep 5767577 = 4325683) B4325683
theorem B2884025 : Blo 1707054 2884025 := bstep (se 2 (by rfl) ⟨1081509, by rfl⟩ : syracuseStep 2884025 = 2163019) B2163019
theorem B2597321 : Blo 1707054 2597321 := bstep (se 2 (by rfl) ⟨973995, by rfl⟩ : syracuseStep 2597321 = 1947991) B1947991
theorem B3121679 : Blo 1707054 3121679 := bstep (se 1 (by rfl) ⟨2341259, by rfl⟩ : syracuseStep 3121679 = 4682519) B4682519
theorem B3842603 : Blo 1707054 3842603 := bstep (se 1 (by rfl) ⟨2881952, by rfl⟩ : syracuseStep 3842603 = 5763905) B5763905
theorem B10388011 : Blo 1707054 10388011 := bstep (se 1 (by rfl) ⟨7791008, by rfl⟩ : syracuseStep 10388011 = 15582017) B15582017
theorem B4326007 : Blo 1707054 4326007 := bstep (se 1 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 4326007 = 6489011) B6489011
theorem B4866713 : Blo 1707054 4866713 := bstep (se 2 (by rfl) ⟨1825017, by rfl⟩ : syracuseStep 4866713 = 3650035) B3650035
theorem B11682575 : Blo 1707054 11682575 := bstep (se 1 (by rfl) ⟨8761931, by rfl⟩ : syracuseStep 11682575 = 17523863) B17523863
theorem B8651609 : Blo 1707054 8651609 := bstep (se 2 (by rfl) ⟨3244353, by rfl⟩ : syracuseStep 8651609 = 6488707) B6488707
theorem B3842963 : Blo 1707054 3842963 := bstep (se 1 (by rfl) ⟨2882222, by rfl⟩ : syracuseStep 3842963 = 5764445) B5764445
theorem B3843017 : Blo 1707054 3843017 := bstep (se 2 (by rfl) ⟨1441131, by rfl⟩ : syracuseStep 3843017 = 2882263) B2882263
theorem B14599115 : Blo 1707054 14599115 := bstep (se 1 (by rfl) ⟨10949336, by rfl⟩ : syracuseStep 14599115 = 21898673) B21898673
theorem B8643671 : Blo 1707054 8643671 := bstep (se 1 (by rfl) ⟨6482753, by rfl⟩ : syracuseStep 8643671 = 12965507) B12965507
theorem B8316193 : Blo 1707054 8316193 := bstep (se 2 (by rfl) ⟨3118572, by rfl⟩ : syracuseStep 8316193 = 6237145) B6237145
theorem B56935811 : Blo 1707054 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B8209811 : Blo 1707054 8209811 := bstep (se 1 (by rfl) ⟨6157358, by rfl⟩ : syracuseStep 8209811 = 12314717) B12314717
theorem B19465757 : Blo 1707054 19465757 := bstep (se 3 (by rfl) ⟨3649829, by rfl⟩ : syracuseStep 19465757 = 7299659) B7299659
theorem B9233963 : Blo 1707054 9233963 := bstep (se 1 (by rfl) ⟨6925472, by rfl⟩ : syracuseStep 9233963 = 13850945) B13850945
theorem B8644157 : Blo 1707054 8644157 := bstep (se 3 (by rfl) ⟨1620779, by rfl⟩ : syracuseStep 8644157 = 3241559) B3241559
theorem B3843719 : Blo 1707054 3843719 := bstep (se 1 (by rfl) ⟨2882789, by rfl⟩ : syracuseStep 3843719 = 5765579) B5765579
theorem B3843899 : Blo 1707054 3843899 := bstep (se 1 (by rfl) ⟨2882924, by rfl⟩ : syracuseStep 3843899 = 5765849) B5765849
theorem B7292825 : Blo 1707054 7292825 := bstep (se 2 (by rfl) ⟨2734809, by rfl⟩ : syracuseStep 7292825 = 5469619) B5469619
theorem B12969881 : Blo 1707054 12969881 := bstep (se 2 (by rfl) ⟨4863705, by rfl⟩ : syracuseStep 12969881 = 9727411) B9727411
theorem B3844025 : Blo 1707054 3844025 := bstep (se 2 (by rfl) ⟨1441509, by rfl⟩ : syracuseStep 3844025 = 2883019) B2883019
theorem B14584009 : Blo 1707054 14584009 := bstep (se 2 (by rfl) ⟨5469003, by rfl⟩ : syracuseStep 14584009 = 10938007) B10938007
theorem B6482177 : Blo 1707054 6482177 := bstep (se 2 (by rfl) ⟨2430816, by rfl⟩ : syracuseStep 6482177 = 4861633) B4861633
theorem B3844367 : Blo 1707054 3844367 := bstep (se 1 (by rfl) ⟨2883275, by rfl⟩ : syracuseStep 3844367 = 5766551) B5766551
theorem B5761313 : Blo 1707054 5761313 := bstep (se 2 (by rfl) ⟨2160492, by rfl⟩ : syracuseStep 5761313 = 4320985) B4320985
theorem B3844385 : Blo 1707054 3844385 := bstep (se 2 (by rfl) ⟨1441644, by rfl⟩ : syracuseStep 3844385 = 2883289) B2883289
theorem B6572497 : Blo 1707054 6572497 := bstep (se 2 (by rfl) ⟨2464686, by rfl⟩ : syracuseStep 6572497 = 4929373) B4929373
theorem B12315179 : Blo 1707054 12315179 := bstep (se 1 (by rfl) ⟨9236384, by rfl⟩ : syracuseStep 12315179 = 18472769) B18472769
theorem B4614775 : Blo 1707054 4614775 := bstep (se 1 (by rfl) ⟨3461081, by rfl⟩ : syracuseStep 4614775 = 6922163) B6922163
theorem B3844727 : Blo 1707054 3844727 := bstep (se 1 (by rfl) ⟨2883545, by rfl⟩ : syracuseStep 3844727 = 5767091) B5767091
theorem B12315407 : Blo 1707054 12315407 := bstep (se 1 (by rfl) ⟨9236555, by rfl⟩ : syracuseStep 12315407 = 18473111) B18473111
theorem B3844907 : Blo 1707054 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B5761907 : Blo 1707054 5761907 := bstep (se 1 (by rfl) ⟨4321430, by rfl⟩ : syracuseStep 5761907 = 8642861) B8642861
theorem B1707067 : Blo 1707054 1707067 := bstep (se 1 (by rfl) ⟨1280300, by rfl⟩ : syracuseStep 1707067 = 2560601) B2560601
theorem B1707143 : Blo 1707054 1707143 := bstep (se 1 (by rfl) ⟨1280357, by rfl⟩ : syracuseStep 1707143 = 2560715) B2560715
theorem B1707151 : Blo 1707054 1707151 := bstep (se 1 (by rfl) ⟨1280363, by rfl⟩ : syracuseStep 1707151 = 2560727) B2560727
theorem B3845267 : Blo 1707054 3845267 := bstep (se 1 (by rfl) ⟨2883950, by rfl⟩ : syracuseStep 3845267 = 5767901) B5767901
theorem B1707195 : Blo 1707054 1707195 := bstep (se 1 (by rfl) ⟨1280396, by rfl⟩ : syracuseStep 1707195 = 2560793) B2560793
theorem B3845321 : Blo 1707054 3845321 := bstep (se 2 (by rfl) ⟨1441995, by rfl⟩ : syracuseStep 3845321 = 2883991) B2883991
theorem B1707271 : Blo 1707054 1707271 := bstep (se 1 (by rfl) ⟨1280453, by rfl⟩ : syracuseStep 1707271 = 2560907) B2560907
theorem B1707279 : Blo 1707054 1707279 := bstep (se 1 (by rfl) ⟨1280459, by rfl⟩ : syracuseStep 1707279 = 2560919) B2560919
theorem B8645939 : Blo 1707054 8645939 := bstep (se 1 (by rfl) ⟨6484454, by rfl⟩ : syracuseStep 8645939 = 12968909) B12968909
theorem B1707323 : Blo 1707054 1707323 := bstep (se 1 (by rfl) ⟨1280492, by rfl⟩ : syracuseStep 1707323 = 2560985) B2560985
theorem B1707399 : Blo 1707054 1707399 := bstep (se 1 (by rfl) ⟨1280549, by rfl⟩ : syracuseStep 1707399 = 2561099) B2561099
theorem B1707407 : Blo 1707054 1707407 := bstep (se 1 (by rfl) ⟨1280555, by rfl⟩ : syracuseStep 1707407 = 2561111) B2561111
theorem B10382737 : Blo 1707054 10382737 := bstep (se 2 (by rfl) ⟨3893526, by rfl⟩ : syracuseStep 10382737 = 7787053) B7787053
theorem B6483347 : Blo 1707054 6483347 := bstep (se 1 (by rfl) ⟨4862510, by rfl⟩ : syracuseStep 6483347 = 9725021) B9725021
theorem B9858449 : Blo 1707054 9858449 := bstep (se 2 (by rfl) ⟨3696918, by rfl⟩ : syracuseStep 9858449 = 7393837) B7393837
theorem B1707451 : Blo 1707054 1707451 := bstep (se 1 (by rfl) ⟨1280588, by rfl⟩ : syracuseStep 1707451 = 2561177) B2561177
theorem B2403847 : Blo 1707054 2403847 := bstep (se 1 (by rfl) ⟨1802885, by rfl⟩ : syracuseStep 2403847 = 3605771) B3605771
theorem B1707527 : Blo 1707054 1707527 := bstep (se 1 (by rfl) ⟨1280645, by rfl⟩ : syracuseStep 1707527 = 2561291) B2561291
theorem B4861451 : Blo 1707054 4861451 := bstep (se 1 (by rfl) ⟨3646088, by rfl⟩ : syracuseStep 4861451 = 7292177) B7292177
theorem B1707535 : Blo 1707054 1707535 := bstep (se 1 (by rfl) ⟨1280651, by rfl⟩ : syracuseStep 1707535 = 2561303) B2561303
theorem B1707579 : Blo 1707054 1707579 := bstep (se 1 (by rfl) ⟨1280684, by rfl⟩ : syracuseStep 1707579 = 2561369) B2561369
theorem B46739045 : Blo 1707054 46739045 := bstep (se 4 (by rfl) ⟨4381785, by rfl⟩ : syracuseStep 46739045 = 8763571) B8763571
theorem B8646263 : Blo 1707054 8646263 := bstep (se 1 (by rfl) ⟨6484697, by rfl⟩ : syracuseStep 8646263 = 12969395) B12969395
theorem B1707655 : Blo 1707054 1707655 := bstep (se 1 (by rfl) ⟨1280741, by rfl⟩ : syracuseStep 1707655 = 2561483) B2561483
theorem B1707663 : Blo 1707054 1707663 := bstep (se 1 (by rfl) ⟨1280747, by rfl⟩ : syracuseStep 1707663 = 2561495) B2561495
theorem B1707707 : Blo 1707054 1707707 := bstep (se 1 (by rfl) ⟨1280780, by rfl⟩ : syracuseStep 1707707 = 2561561) B2561561
theorem B1920775 : Blo 1707054 1920775 := bstep (se 1 (by rfl) ⟨1440581, by rfl⟩ : syracuseStep 1920775 = 2881163) B2881163
theorem B1707783 : Blo 1707054 1707783 := bstep (se 1 (by rfl) ⟨1280837, by rfl⟩ : syracuseStep 1707783 = 2561675) B2561675
theorem B2920207 : Blo 1707054 2920207 := bstep (se 1 (by rfl) ⟨2190155, by rfl⟩ : syracuseStep 2920207 = 4380311) B4380311
theorem B1707791 : Blo 1707054 1707791 := bstep (se 1 (by rfl) ⟨1280843, by rfl⟩ : syracuseStep 1707791 = 2561687) B2561687
theorem B12971825 : Blo 1707054 12971825 := bstep (se 2 (by rfl) ⟨4864434, by rfl⟩ : syracuseStep 12971825 = 9728869) B9728869
theorem B1707835 : Blo 1707054 1707835 := bstep (se 1 (by rfl) ⟨1280876, by rfl⟩ : syracuseStep 1707835 = 2561753) B2561753
theorem B6483847 : Blo 1707054 6483847 := bstep (se 1 (by rfl) ⟨4862885, by rfl⟩ : syracuseStep 6483847 = 9725771) B9725771
theorem B1707911 : Blo 1707054 1707911 := bstep (se 1 (by rfl) ⟨1280933, by rfl⟩ : syracuseStep 1707911 = 2561867) B2561867
theorem B1707919 : Blo 1707054 1707919 := bstep (se 1 (by rfl) ⟨1280939, by rfl⟩ : syracuseStep 1707919 = 2561879) B2561879
theorem B2052011 : Blo 1707054 2052011 := bstep (se 1 (by rfl) ⟨1539008, by rfl⟩ : syracuseStep 2052011 = 3078017) B3078017
theorem B1920955 : Blo 1707054 1920955 := bstep (se 1 (by rfl) ⟨1440716, by rfl⟩ : syracuseStep 1920955 = 2881433) B2881433
theorem B1707963 : Blo 1707054 1707963 := bstep (se 1 (by rfl) ⟨1280972, by rfl⟩ : syracuseStep 1707963 = 2561945) B2561945
theorem B4681729 : Blo 1707054 4681729 := bstep (se 2 (by rfl) ⟨1755648, by rfl⟩ : syracuseStep 4681729 = 3511297) B3511297
theorem B1708039 : Blo 1707054 1708039 := bstep (se 1 (by rfl) ⟨1281029, by rfl⟩ : syracuseStep 1708039 = 2562059) B2562059
theorem B1708047 : Blo 1707054 1708047 := bstep (se 1 (by rfl) ⟨1281035, by rfl⟩ : syracuseStep 1708047 = 2562071) B2562071
theorem B1708091 : Blo 1707054 1708091 := bstep (se 1 (by rfl) ⟨1281068, by rfl⟩ : syracuseStep 1708091 = 2562137) B2562137
theorem B4616279 : Blo 1707054 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B21893237 : Blo 1707054 21893237 := bstep (se 5 (by rfl) ⟨1026245, by rfl⟩ : syracuseStep 21893237 = 2052491) B2052491
theorem B2773111 : Blo 1707054 2773111 := bstep (se 1 (by rfl) ⟨2079833, by rfl⟩ : syracuseStep 2773111 = 4159667) B4159667
theorem B1708167 : Blo 1707054 1708167 := bstep (se 1 (by rfl) ⟨1281125, by rfl⟩ : syracuseStep 1708167 = 2562251) B2562251
theorem B1708175 : Blo 1707054 1708175 := bstep (se 1 (by rfl) ⟨1281131, by rfl⟩ : syracuseStep 1708175 = 2562263) B2562263
theorem B1708219 : Blo 1707054 1708219 := bstep (se 1 (by rfl) ⟨1281164, by rfl⟩ : syracuseStep 1708219 = 2562329) B2562329
theorem B1708295 : Blo 1707054 1708295 := bstep (se 1 (by rfl) ⟨1281221, by rfl⟩ : syracuseStep 1708295 = 2562443) B2562443
theorem B1708303 : Blo 1707054 1708303 := bstep (se 1 (by rfl) ⟨1281227, by rfl⟩ : syracuseStep 1708303 = 2562455) B2562455
theorem B4616507 : Blo 1707054 4616507 := bstep (se 1 (by rfl) ⟨3462380, by rfl⟩ : syracuseStep 4616507 = 6924761) B6924761
theorem B1708347 : Blo 1707054 1708347 := bstep (se 1 (by rfl) ⟨1281260, by rfl⟩ : syracuseStep 1708347 = 2562521) B2562521
theorem B1708423 : Blo 1707054 1708423 := bstep (se 1 (by rfl) ⟨1281317, by rfl⟩ : syracuseStep 1708423 = 2562635) B2562635
theorem B1921423 : Blo 1707054 1921423 := bstep (se 1 (by rfl) ⟨1441067, by rfl⟩ : syracuseStep 1921423 = 2882135) B2882135
theorem B1708431 : Blo 1707054 1708431 := bstep (se 1 (by rfl) ⟨1281323, by rfl⟩ : syracuseStep 1708431 = 2562647) B2562647
theorem B1708475 : Blo 1707054 1708475 := bstep (se 1 (by rfl) ⟨1281356, by rfl⟩ : syracuseStep 1708475 = 2562713) B2562713
theorem B1708551 : Blo 1707054 1708551 := bstep (se 1 (by rfl) ⟨1281413, by rfl⟩ : syracuseStep 1708551 = 2562827) B2562827
theorem B7016971 : Blo 1707054 7016971 := bstep (se 1 (by rfl) ⟨5262728, by rfl⟩ : syracuseStep 7016971 = 10525457) B10525457
theorem B1708559 : Blo 1707054 1708559 := bstep (se 1 (by rfl) ⟨1281419, by rfl⟩ : syracuseStep 1708559 = 2562839) B2562839
theorem B1708603 : Blo 1707054 1708603 := bstep (se 1 (by rfl) ⟨1281452, by rfl⟩ : syracuseStep 1708603 = 2562905) B2562905
theorem B7787069 : Blo 1707054 7787069 := bstep (se 3 (by rfl) ⟨1460075, by rfl⟩ : syracuseStep 7787069 = 2920151) B2920151
theorem B8647235 : Blo 1707054 8647235 := bstep (se 1 (by rfl) ⟨6485426, by rfl⟩ : syracuseStep 8647235 = 12970853) B12970853
theorem B4321907 : Blo 1707054 4321907 := bstep (se 1 (by rfl) ⟨3241430, by rfl⟩ : syracuseStep 4321907 = 6482861) B6482861
theorem B2560631 : Blo 1707054 2560631 := bstep (se 1 (by rfl) ⟨1920473, by rfl⟩ : syracuseStep 2560631 = 3840947) B3840947
theorem B1708679 : Blo 1707054 1708679 := bstep (se 1 (by rfl) ⟨1281509, by rfl⟩ : syracuseStep 1708679 = 2563019) B2563019
theorem B2560655 : Blo 1707054 2560655 := bstep (se 1 (by rfl) ⟨1920491, by rfl⟩ : syracuseStep 2560655 = 3840983) B3840983
theorem B1708687 : Blo 1707054 1708687 := bstep (se 1 (by rfl) ⟨1281515, by rfl⟩ : syracuseStep 1708687 = 2563031) B2563031
theorem B2560697 : Blo 1707054 2560697 := bstep (se 2 (by rfl) ⟨960261, by rfl⟩ : syracuseStep 2560697 = 1920523) B1920523
theorem B1708731 : Blo 1707054 1708731 := bstep (se 1 (by rfl) ⟨1281548, by rfl⟩ : syracuseStep 1708731 = 2563097) B2563097
theorem B2560775 : Blo 1707054 2560775 := bstep (se 1 (by rfl) ⟨1920581, by rfl⟩ : syracuseStep 2560775 = 3841163) B3841163
theorem B1708807 : Blo 1707054 1708807 := bstep (se 1 (by rfl) ⟨1281605, by rfl⟩ : syracuseStep 1708807 = 2563211) B2563211
theorem B1708815 : Blo 1707054 1708815 := bstep (se 1 (by rfl) ⟨1281611, by rfl⟩ : syracuseStep 1708815 = 2563223) B2563223
theorem B4862749 : Blo 1707054 4862749 := bstep (se 3 (by rfl) ⟨911765, by rfl⟩ : syracuseStep 4862749 = 1823531) B1823531
theorem B2560811 : Blo 1707054 2560811 := bstep (se 1 (by rfl) ⟨1920608, by rfl⟩ : syracuseStep 2560811 = 3841217) B3841217
theorem B1708859 : Blo 1707054 1708859 := bstep (se 1 (by rfl) ⟨1281644, by rfl⟩ : syracuseStep 1708859 = 2563289) B2563289
theorem B2560841 : Blo 1707054 2560841 := bstep (se 2 (by rfl) ⟨960315, by rfl⟩ : syracuseStep 2560841 = 1920631) B1920631
theorem B3240823 : Blo 1707054 3240823 := bstep (se 1 (by rfl) ⟨2430617, by rfl⟩ : syracuseStep 3240823 = 4861235) B4861235
theorem B3462023 : Blo 1707054 3462023 := bstep (se 1 (by rfl) ⟨2596517, by rfl⟩ : syracuseStep 3462023 = 5193035) B5193035
theorem B8647559 : Blo 1707054 8647559 := bstep (se 1 (by rfl) ⟨6485669, by rfl⟩ : syracuseStep 8647559 = 12971339) B12971339
theorem B1921927 : Blo 1707054 1921927 := bstep (se 1 (by rfl) ⟨1441445, by rfl⟩ : syracuseStep 1921927 = 2882891) B2882891
theorem B1708935 : Blo 1707054 1708935 := bstep (se 1 (by rfl) ⟨1281701, by rfl⟩ : syracuseStep 1708935 = 2563403) B2563403
theorem B1708943 : Blo 1707054 1708943 := bstep (se 1 (by rfl) ⟨1281707, by rfl⟩ : syracuseStep 1708943 = 2563415) B2563415
theorem B140293043 : Blo 1707054 140293043 := bstep (se 1 (by rfl) ⟨105219782, by rfl⟩ : syracuseStep 140293043 = 210439565) B210439565
theorem B2560955 : Blo 1707054 2560955 := bstep (se 1 (by rfl) ⟨1920716, by rfl⟩ : syracuseStep 2560955 = 3841433) B3841433
theorem B1708987 : Blo 1707054 1708987 := bstep (se 1 (by rfl) ⟨1281740, by rfl⟩ : syracuseStep 1708987 = 2563481) B2563481
theorem B3077065 : Blo 1707054 3077065 := bstep (se 2 (by rfl) ⟨1153899, by rfl⟩ : syracuseStep 3077065 = 2307799) B2307799
theorem B7295953 : Blo 1707054 7295953 := bstep (se 2 (by rfl) ⟨2735982, by rfl⟩ : syracuseStep 7295953 = 5471965) B5471965
theorem B2561015 : Blo 1707054 2561015 := bstep (se 1 (by rfl) ⟨1920761, by rfl⟩ : syracuseStep 2561015 = 3841523) B3841523
theorem B10392587 : Blo 1707054 10392587 := bstep (se 1 (by rfl) ⟨7794440, by rfl⟩ : syracuseStep 10392587 = 15588881) B15588881
theorem B2561039 : Blo 1707054 2561039 := bstep (se 1 (by rfl) ⟨1920779, by rfl⟩ : syracuseStep 2561039 = 3841559) B3841559
theorem B9999389 : Blo 1707054 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B2561081 : Blo 1707054 2561081 := bstep (se 2 (by rfl) ⟨960405, by rfl⟩ : syracuseStep 2561081 = 1920811) B1920811
theorem B1922107 : Blo 1707054 1922107 := bstep (se 1 (by rfl) ⟨1441580, by rfl⟩ : syracuseStep 1922107 = 2883161) B2883161
theorem B4863091 : Blo 1707054 4863091 := bstep (se 1 (by rfl) ⟨3647318, by rfl⟩ : syracuseStep 4863091 = 7294637) B7294637
theorem B4322423 : Blo 1707054 4322423 := bstep (se 1 (by rfl) ⟨3241817, by rfl⟩ : syracuseStep 4322423 = 6483635) B6483635
theorem B9729143 : Blo 1707054 9729143 := bstep (se 1 (by rfl) ⟨7296857, by rfl⟩ : syracuseStep 9729143 = 14593715) B14593715
theorem B2561159 : Blo 1707054 2561159 := bstep (se 1 (by rfl) ⟨1920869, by rfl⟩ : syracuseStep 2561159 = 3841739) B3841739
theorem B2307215 : Blo 1707054 2307215 := bstep (se 1 (by rfl) ⟨1730411, by rfl⟩ : syracuseStep 2307215 = 3460823) B3460823
theorem B2561195 : Blo 1707054 2561195 := bstep (se 1 (by rfl) ⟨1920896, by rfl⟩ : syracuseStep 2561195 = 3841793) B3841793
theorem B2880697 : Blo 1707054 2880697 := bstep (se 2 (by rfl) ⟨1080261, by rfl⟩ : syracuseStep 2880697 = 2160523) B2160523
theorem B2561225 : Blo 1707054 2561225 := bstep (se 2 (by rfl) ⟨960459, by rfl⟩ : syracuseStep 2561225 = 1920919) B1920919
theorem B8205583 : Blo 1707054 8205583 := bstep (se 1 (by rfl) ⟨6154187, by rfl⟩ : syracuseStep 8205583 = 12308375) B12308375
theorem B9229619 : Blo 1707054 9229619 := bstep (se 1 (by rfl) ⟨6922214, by rfl⟩ : syracuseStep 9229619 = 13844429) B13844429
theorem B2561339 : Blo 1707054 2561339 := bstep (se 1 (by rfl) ⟨1921004, by rfl⟩ : syracuseStep 2561339 = 3842009) B3842009
theorem B24630587 : Blo 1707054 24630587 := bstep (se 1 (by rfl) ⟨18472940, by rfl⟩ : syracuseStep 24630587 = 36945881) B36945881
theorem B4617587 : Blo 1707054 4617587 := bstep (se 1 (by rfl) ⟨3463190, by rfl⟩ : syracuseStep 4617587 = 6926381) B6926381
theorem B9729395 : Blo 1707054 9729395 := bstep (se 1 (by rfl) ⟨7297046, by rfl⟩ : syracuseStep 9729395 = 14594093) B14594093
theorem B2561399 : Blo 1707054 2561399 := bstep (se 1 (by rfl) ⟨1921049, by rfl⟩ : syracuseStep 2561399 = 3842099) B3842099
theorem B2561423 : Blo 1707054 2561423 := bstep (se 1 (by rfl) ⟨1921067, by rfl⟩ : syracuseStep 2561423 = 3842135) B3842135
theorem B5764499 : Blo 1707054 5764499 := bstep (se 1 (by rfl) ⟨4323374, by rfl⟩ : syracuseStep 5764499 = 8646749) B8646749
theorem B2561465 : Blo 1707054 2561465 := bstep (se 2 (by rfl) ⟨960549, by rfl⟩ : syracuseStep 2561465 = 1921099) B1921099
theorem B9491897 : Blo 1707054 9491897 := bstep (se 2 (by rfl) ⟨3559461, by rfl⟩ : syracuseStep 9491897 = 7118923) B7118923
theorem B2561543 : Blo 1707054 2561543 := bstep (se 1 (by rfl) ⟨1921157, by rfl⟩ : syracuseStep 2561543 = 3842315) B3842315
theorem B1922575 : Blo 1707054 1922575 := bstep (se 1 (by rfl) ⟨1441931, by rfl⟩ : syracuseStep 1922575 = 2883863) B2883863
theorem B2561579 : Blo 1707054 2561579 := bstep (se 1 (by rfl) ⟨1921184, by rfl⟩ : syracuseStep 2561579 = 3842369) B3842369
theorem B2561609 : Blo 1707054 2561609 := bstep (se 2 (by rfl) ⟨960603, by rfl⟩ : syracuseStep 2561609 = 1921207) B1921207
theorem B4159063 : Blo 1707054 4159063 := bstep (se 1 (by rfl) ⟨3119297, by rfl⟩ : syracuseStep 4159063 = 6238595) B6238595
theorem B2307755 : Blo 1707054 2307755 := bstep (se 1 (by rfl) ⟨1730816, by rfl⟩ : syracuseStep 2307755 = 3461633) B3461633
theorem B2561723 : Blo 1707054 2561723 := bstep (se 1 (by rfl) ⟨1921292, by rfl⟩ : syracuseStep 2561723 = 3842585) B3842585
theorem B7493357 : Blo 1707054 7493357 := bstep (se 3 (by rfl) ⟨1405004, by rfl⟩ : syracuseStep 7493357 = 2810009) B2810009
theorem B2561783 : Blo 1707054 2561783 := bstep (se 1 (by rfl) ⟨1921337, by rfl⟩ : syracuseStep 2561783 = 3842675) B3842675
theorem B2561807 : Blo 1707054 2561807 := bstep (se 1 (by rfl) ⟨1921355, by rfl⟩ : syracuseStep 2561807 = 3842711) B3842711
theorem B2561849 : Blo 1707054 2561849 := bstep (se 2 (by rfl) ⟨960693, by rfl⟩ : syracuseStep 2561849 = 1921387) B1921387
theorem B4101947 : Blo 1707054 4101947 := bstep (se 1 (by rfl) ⟨3076460, by rfl⟩ : syracuseStep 4101947 = 6152921) B6152921
theorem B2881399 : Blo 1707054 2881399 := bstep (se 1 (by rfl) ⟨2161049, by rfl⟩ : syracuseStep 2881399 = 4322099) B4322099
theorem B2561927 : Blo 1707054 2561927 := bstep (se 1 (by rfl) ⟨1921445, by rfl⟩ : syracuseStep 2561927 = 3842891) B3842891
theorem B2561963 : Blo 1707054 2561963 := bstep (se 1 (by rfl) ⟨1921472, by rfl⟩ : syracuseStep 2561963 = 3842945) B3842945
theorem B2561993 : Blo 1707054 2561993 := bstep (se 2 (by rfl) ⟨960747, by rfl⟩ : syracuseStep 2561993 = 1921495) B1921495
theorem B3463183 : Blo 1707054 3463183 := bstep (se 1 (by rfl) ⟨2597387, by rfl⟩ : syracuseStep 3463183 = 5194775) B5194775
theorem B4102177 : Blo 1707054 4102177 := bstep (se 2 (by rfl) ⟨1538316, by rfl⟩ : syracuseStep 4102177 = 3076633) B3076633
theorem B2881595 : Blo 1707054 2881595 := bstep (se 1 (by rfl) ⟨2161196, by rfl⟩ : syracuseStep 2881595 = 4322393) B4322393
theorem B2562107 : Blo 1707054 2562107 := bstep (se 1 (by rfl) ⟨1921580, by rfl⟩ : syracuseStep 2562107 = 3843161) B3843161
theorem B4323415 : Blo 1707054 4323415 := bstep (se 1 (by rfl) ⟨3242561, by rfl⟩ : syracuseStep 4323415 = 6485123) B6485123
theorem B2562167 : Blo 1707054 2562167 := bstep (se 1 (by rfl) ⟨1921625, by rfl⟩ : syracuseStep 2562167 = 3843251) B3843251
theorem B2562191 : Blo 1707054 2562191 := bstep (se 1 (by rfl) ⟨1921643, by rfl⟩ : syracuseStep 2562191 = 3843287) B3843287
theorem B2431147 : Blo 1707054 2431147 := bstep (se 1 (by rfl) ⟨1823360, by rfl⟩ : syracuseStep 2431147 = 3646721) B3646721
theorem B2562233 : Blo 1707054 2562233 := bstep (se 2 (by rfl) ⟨960837, by rfl⟩ : syracuseStep 2562233 = 1921675) B1921675
theorem B2562311 : Blo 1707054 2562311 := bstep (se 1 (by rfl) ⟨1921733, by rfl⟩ : syracuseStep 2562311 = 3843467) B3843467
theorem B4618529 : Blo 1707054 4618529 := bstep (se 2 (by rfl) ⟨1731948, by rfl⟩ : syracuseStep 4618529 = 3463897) B3463897
theorem B2562347 : Blo 1707054 2562347 := bstep (se 1 (by rfl) ⟨1921760, by rfl⟩ : syracuseStep 2562347 = 3843521) B3843521
theorem B2562377 : Blo 1707054 2562377 := bstep (se 2 (by rfl) ⟨960891, by rfl⟩ : syracuseStep 2562377 = 1921783) B1921783
theorem B4618583 : Blo 1707054 4618583 := bstep (se 1 (by rfl) ⟨3463937, by rfl⟩ : syracuseStep 4618583 = 6927875) B6927875
theorem B4323719 : Blo 1707054 4323719 := bstep (se 1 (by rfl) ⟨3242789, by rfl⟩ : syracuseStep 4323719 = 6485579) B6485579
theorem B3242425 : Blo 1707054 3242425 := bstep (se 2 (by rfl) ⟨1215909, by rfl⟩ : syracuseStep 3242425 = 2431819) B2431819
theorem B2562491 : Blo 1707054 2562491 := bstep (se 1 (by rfl) ⟨1921868, by rfl⟩ : syracuseStep 2562491 = 3843737) B3843737
theorem B2881993 : Blo 1707054 2881993 := bstep (se 2 (by rfl) ⟨1080747, by rfl⟩ : syracuseStep 2881993 = 2161495) B2161495
theorem B2562551 : Blo 1707054 2562551 := bstep (se 1 (by rfl) ⟨1921913, by rfl⟩ : syracuseStep 2562551 = 3843827) B3843827
theorem B4323851 : Blo 1707054 4323851 := bstep (se 1 (by rfl) ⟨3242888, by rfl⟩ : syracuseStep 4323851 = 6485777) B6485777
theorem B2562575 : Blo 1707054 2562575 := bstep (se 1 (by rfl) ⟨1921931, by rfl⟩ : syracuseStep 2562575 = 3843863) B3843863
theorem B2562617 : Blo 1707054 2562617 := bstep (se 2 (by rfl) ⟨960981, by rfl⟩ : syracuseStep 2562617 = 1921963) B1921963
theorem B2923067 : Blo 1707054 2923067 := bstep (se 1 (by rfl) ⟨2192300, by rfl⟩ : syracuseStep 2923067 = 4384601) B4384601
theorem B9230935 : Blo 1707054 9230935 := bstep (se 1 (by rfl) ⟨6923201, by rfl⟩ : syracuseStep 9230935 = 13846403) B13846403
theorem B2562695 : Blo 1707054 2562695 := bstep (se 1 (by rfl) ⟨1922021, by rfl⟩ : syracuseStep 2562695 = 3844043) B3844043
theorem B2562731 : Blo 1707054 2562731 := bstep (se 1 (by rfl) ⟨1922048, by rfl⟩ : syracuseStep 2562731 = 3844097) B3844097
theorem B2562761 : Blo 1707054 2562761 := bstep (se 2 (by rfl) ⟨961035, by rfl⟩ : syracuseStep 2562761 = 1922071) B1922071
theorem B118299341 : Blo 1707054 118299341 := bstep (se 3 (by rfl) ⟨22181126, by rfl⟩ : syracuseStep 118299341 = 44362253) B44362253
theorem B2161399 : Blo 1707054 2161399 := bstep (se 1 (by rfl) ⟨1621049, by rfl⟩ : syracuseStep 2161399 = 3242099) B3242099
theorem B3242767 : Blo 1707054 3242767 := bstep (se 1 (by rfl) ⟨2432075, by rfl⟩ : syracuseStep 3242767 = 4864151) B4864151
theorem B5765903 : Blo 1707054 5765903 := bstep (se 1 (by rfl) ⟨4324427, by rfl⟩ : syracuseStep 5765903 = 8648855) B8648855
theorem B16644899 : Blo 1707054 16644899 := bstep (se 1 (by rfl) ⟨12483674, by rfl⟩ : syracuseStep 16644899 = 24967349) B24967349
theorem B9730853 : Blo 1707054 9730853 := bstep (se 4 (by rfl) ⟨912267, by rfl⟩ : syracuseStep 9730853 = 1824535) B1824535
theorem B2562875 : Blo 1707054 2562875 := bstep (se 1 (by rfl) ⟨1922156, by rfl⟩ : syracuseStep 2562875 = 3844313) B3844313
theorem B2562935 : Blo 1707054 2562935 := bstep (se 1 (by rfl) ⟨1922201, by rfl⟩ : syracuseStep 2562935 = 3844403) B3844403
theorem B2562959 : Blo 1707054 2562959 := bstep (se 1 (by rfl) ⟨1922219, by rfl⟩ : syracuseStep 2562959 = 3844439) B3844439
theorem B2563001 : Blo 1707054 2563001 := bstep (se 2 (by rfl) ⟨961125, by rfl⟩ : syracuseStep 2563001 = 1922251) B1922251
theorem B2563079 : Blo 1707054 2563079 := bstep (se 1 (by rfl) ⟨1922309, by rfl⟩ : syracuseStep 2563079 = 3844619) B3844619
theorem B14597131 : Blo 1707054 14597131 := bstep (se 1 (by rfl) ⟨10947848, by rfl⟩ : syracuseStep 14597131 = 21895697) B21895697
theorem B4324367 : Blo 1707054 4324367 := bstep (se 1 (by rfl) ⟨3243275, by rfl⟩ : syracuseStep 4324367 = 6486551) B6486551
theorem B5766173 : Blo 1707054 5766173 := bstep (se 3 (by rfl) ⟨1081157, by rfl⟩ : syracuseStep 5766173 = 2162315) B2162315
theorem B2563115 : Blo 1707054 2563115 := bstep (se 1 (by rfl) ⟨1922336, by rfl⟩ : syracuseStep 2563115 = 3844673) B3844673
theorem B2161723 : Blo 1707054 2161723 := bstep (se 1 (by rfl) ⟨1621292, by rfl⟩ : syracuseStep 2161723 = 3242585) B3242585
theorem B2563145 : Blo 1707054 2563145 := bstep (se 2 (by rfl) ⟨961179, by rfl⟩ : syracuseStep 2563145 = 1922359) B1922359
theorem B5471351 : Blo 1707054 5471351 := bstep (se 1 (by rfl) ⟨4103513, by rfl⟩ : syracuseStep 5471351 = 8207027) B8207027
theorem B2882695 : Blo 1707054 2882695 := bstep (se 1 (by rfl) ⟨2162021, by rfl⟩ : syracuseStep 2882695 = 4324043) B4324043
theorem B4324499 : Blo 1707054 4324499 := bstep (se 1 (by rfl) ⟨3243374, by rfl⟩ : syracuseStep 4324499 = 6486749) B6486749
theorem B2563259 : Blo 1707054 2563259 := bstep (se 1 (by rfl) ⟨1922444, by rfl⟩ : syracuseStep 2563259 = 3844889) B3844889
theorem B4103369 : Blo 1707054 4103369 := bstep (se 2 (by rfl) ⟨1538763, by rfl⟩ : syracuseStep 4103369 = 3077527) B3077527
theorem B9862345 : Blo 1707054 9862345 := bstep (se 2 (by rfl) ⟨3698379, by rfl⟩ : syracuseStep 9862345 = 7396759) B7396759
theorem B2563319 : Blo 1707054 2563319 := bstep (se 1 (by rfl) ⟨1922489, by rfl⟩ : syracuseStep 2563319 = 3844979) B3844979
theorem B2432263 : Blo 1707054 2432263 := bstep (se 1 (by rfl) ⟨1824197, by rfl⟩ : syracuseStep 2432263 = 3648395) B3648395
theorem B2563343 : Blo 1707054 2563343 := bstep (se 1 (by rfl) ⟨1922507, by rfl⟩ : syracuseStep 2563343 = 3845015) B3845015
theorem B4504865 : Blo 1707054 4504865 := bstep (se 2 (by rfl) ⟨1689324, by rfl⟩ : syracuseStep 4504865 = 3378649) B3378649
theorem B2563385 : Blo 1707054 2563385 := bstep (se 2 (by rfl) ⟨961269, by rfl⟩ : syracuseStep 2563385 = 1922539) B1922539
theorem B3841415 : Blo 1707054 3841415 := bstep (se 1 (by rfl) ⟨2881061, by rfl⟩ : syracuseStep 3841415 = 5762123) B5762123
theorem B2563463 : Blo 1707054 2563463 := bstep (se 1 (by rfl) ⟨1922597, by rfl⟩ : syracuseStep 2563463 = 3845195) B3845195
theorem B2563499 : Blo 1707054 2563499 := bstep (se 1 (by rfl) ⟨1922624, by rfl⟩ : syracuseStep 2563499 = 3845249) B3845249
theorem B2563529 : Blo 1707054 2563529 := bstep (se 2 (by rfl) ⟨961323, by rfl⟩ : syracuseStep 2563529 = 1922647) B1922647
theorem B8642051 : Blo 1707054 8642051 := bstep (se 1 (by rfl) ⟨6481538, by rfl⟩ : syracuseStep 8642051 = 12963077) B12963077
theorem B46759427 : Blo 1707054 46759427 := bstep (se 1 (by rfl) ⟨35069570, by rfl⟩ : syracuseStep 46759427 = 70139141) B70139141
theorem B3841595 : Blo 1707054 3841595 := bstep (se 1 (by rfl) ⟨2881196, by rfl⟩ : syracuseStep 3841595 = 5762393) B5762393
theorem B4931131 : Blo 1707054 4931131 := bstep (se 1 (by rfl) ⟨3698348, by rfl⟩ : syracuseStep 4931131 = 7396697) B7396697
theorem B8879683 : Blo 1707054 8879683 := bstep (se 1 (by rfl) ⟨6659762, by rfl⟩ : syracuseStep 8879683 = 13319525) B13319525
theorem B3243655 : Blo 1707054 3243655 := bstep (se 1 (by rfl) ⟨2432741, by rfl⟩ : syracuseStep 3243655 = 4865483) B4865483
theorem B16408241 : Blo 1707054 16408241 := bstep (se 2 (by rfl) ⟨6153090, by rfl⟩ : syracuseStep 16408241 = 12306181) B12306181
theorem B3841721 : Blo 1707054 3841721 := bstep (se 2 (by rfl) ⟨1440645, by rfl⟩ : syracuseStep 3841721 = 2881291) B2881291
theorem B9731785 : Blo 1707054 9731785 := bstep (se 2 (by rfl) ⟨3649419, by rfl⟩ : syracuseStep 9731785 = 7298839) B7298839
theorem B2883343 : Blo 1707054 2883343 := bstep (se 1 (by rfl) ⟨2162507, by rfl⟩ : syracuseStep 2883343 = 4325015) B4325015
theorem B8208161 : Blo 1707054 8208161 := bstep (se 2 (by rfl) ⟨3078060, by rfl⟩ : syracuseStep 8208161 = 6156121) B6156121
theorem B4865825 : Blo 1707054 4865825 := bstep (se 2 (by rfl) ⟨1824684, by rfl⟩ : syracuseStep 4865825 = 3649369) B3649369
theorem B19988275 : Blo 1707054 19988275 := bstep (se 1 (by rfl) ⟨14991206, by rfl⟩ : syracuseStep 19988275 = 29982413) B29982413
theorem B4865939 : Blo 1707054 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B24969221 : Blo 1707054 24969221 := bstep (se 4 (by rfl) ⟨2340864, by rfl⟩ : syracuseStep 24969221 = 4681729) B4681729
theorem B2883593 : Blo 1707054 2883593 := bstep (se 2 (by rfl) ⟨1081347, by rfl⟩ : syracuseStep 2883593 = 2162695) B2162695
theorem B6488221 : Blo 1707054 6488221 := bstep (se 3 (by rfl) ⟨1216541, by rfl⟩ : syracuseStep 6488221 = 2433083) B2433083
theorem B2883755 : Blo 1707054 2883755 := bstep (se 1 (by rfl) ⟨2162816, by rfl⟩ : syracuseStep 2883755 = 4325633) B4325633
theorem B5767415 : Blo 1707054 5767415 := bstep (se 1 (by rfl) ⟨4325561, by rfl⟩ : syracuseStep 5767415 = 8651123) B8651123
theorem B2081119 : Blo 1707054 2081119 := bstep (se 1 (by rfl) ⟨1560839, by rfl⟩ : syracuseStep 2081119 = 3121679) B3121679
theorem B6152573 : Blo 1707054 6152573 := bstep (se 3 (by rfl) ⟨1153607, by rfl⟩ : syracuseStep 6152573 = 2307215) B2307215
theorem B3244475 : Blo 1707054 3244475 := bstep (se 1 (by rfl) ⟨2433356, by rfl⟩ : syracuseStep 3244475 = 4866713) B4866713
theorem B5767739 : Blo 1707054 5767739 := bstep (se 1 (by rfl) ⟨4325804, by rfl⟩ : syracuseStep 5767739 = 8651609) B8651609
theorem B3842657 : Blo 1707054 3842657 := bstep (se 2 (by rfl) ⟨1440996, by rfl⟩ : syracuseStep 3842657 = 2881993) B2881993
theorem B93528695 : Blo 1707054 93528695 := bstep (se 1 (by rfl) ⟨70146521, by rfl⟩ : syracuseStep 93528695 = 140293043) B140293043
theorem B9732743 : Blo 1707054 9732743 := bstep (se 1 (by rfl) ⟨7299557, by rfl⟩ : syracuseStep 9732743 = 14599115) B14599115
theorem B9355961 : Blo 1707054 9355961 := bstep (se 2 (by rfl) ⟨3508485, by rfl⟩ : syracuseStep 9355961 = 7016971) B7016971
theorem B5768009 : Blo 1707054 5768009 := bstep (se 2 (by rfl) ⟨2163003, by rfl⟩ : syracuseStep 5768009 = 4326007) B4326007
theorem B6153079 : Blo 1707054 6153079 := bstep (se 1 (by rfl) ⟨4614809, by rfl⟩ : syracuseStep 6153079 = 9229619) B9229619
theorem B3842999 : Blo 1707054 3842999 := bstep (se 1 (by rfl) ⟨2882249, by rfl⟩ : syracuseStep 3842999 = 5764499) B5764499
theorem B5473207 : Blo 1707054 5473207 := bstep (se 1 (by rfl) ⟨4104905, by rfl⟩ : syracuseStep 5473207 = 8209811) B8209811
theorem B12977171 : Blo 1707054 12977171 := bstep (se 1 (by rfl) ⟨9732878, by rfl⟩ : syracuseStep 12977171 = 19465757) B19465757
theorem B3843593 : Blo 1707054 3843593 := bstep (se 2 (by rfl) ⟨1441347, by rfl⟩ : syracuseStep 3843593 = 2882695) B2882695
theorem B13149793 : Blo 1707054 13149793 := bstep (se 2 (by rfl) ⟨4931172, by rfl⟩ : syracuseStep 13149793 = 9862345) B9862345
theorem B8210119 : Blo 1707054 8210119 := bstep (se 1 (by rfl) ⟨6157589, by rfl⟩ : syracuseStep 8210119 = 12315179) B12315179
theorem B6154013 : Blo 1707054 6154013 := bstep (se 3 (by rfl) ⟨1153877, by rfl⟩ : syracuseStep 6154013 = 2307755) B2307755
theorem B78866227 : Blo 1707054 78866227 := bstep (se 1 (by rfl) ⟨59149670, by rfl⟩ : syracuseStep 78866227 = 118299341) B118299341
theorem B3843935 : Blo 1707054 3843935 := bstep (se 1 (by rfl) ⟨2882951, by rfl⟩ : syracuseStep 3843935 = 5765903) B5765903
theorem B3205129 : Blo 1707054 3205129 := bstep (se 2 (by rfl) ⟨1201923, by rfl⟩ : syracuseStep 3205129 = 2403847) B2403847
theorem B3844115 : Blo 1707054 3844115 := bstep (se 1 (by rfl) ⟨2883086, by rfl⟩ : syracuseStep 3844115 = 5766173) B5766173
theorem B3647567 : Blo 1707054 3647567 := bstep (se 1 (by rfl) ⟨2735675, by rfl⟩ : syracuseStep 3647567 = 5471351) B5471351
theorem B11839577 : Blo 1707054 11839577 := bstep (se 2 (by rfl) ⟨4439841, by rfl⟩ : syracuseStep 11839577 = 8879683) B8879683
theorem B6572299 : Blo 1707054 6572299 := bstep (se 1 (by rfl) ⟨4929224, by rfl⟩ : syracuseStep 6572299 = 9858449) B9858449
theorem B5761367 : Blo 1707054 5761367 := bstep (se 1 (by rfl) ⟨4321025, by rfl⟩ : syracuseStep 5761367 = 8642051) B8642051
theorem B31172951 : Blo 1707054 31172951 := bstep (se 1 (by rfl) ⟨23379713, by rfl⟩ : syracuseStep 31172951 = 46759427) B46759427
theorem B3893609 : Blo 1707054 3893609 := bstep (se 2 (by rfl) ⟨1460103, by rfl⟩ : syracuseStep 3893609 = 2920207) B2920207
theorem B3844457 : Blo 1707054 3844457 := bstep (se 2 (by rfl) ⟨1441671, by rfl⟩ : syracuseStep 3844457 = 2883343) B2883343
theorem B26651033 : Blo 1707054 26651033 := bstep (se 2 (by rfl) ⟨9994137, by rfl⟩ : syracuseStep 26651033 = 19988275) B19988275
theorem B10938827 : Blo 1707054 10938827 := bstep (se 1 (by rfl) ⟨8204120, by rfl⟩ : syracuseStep 10938827 = 16408241) B16408241
theorem B8645129 : Blo 1707054 8645129 := bstep (se 2 (by rfl) ⟨3241923, by rfl⟩ : syracuseStep 8645129 = 6483847) B6483847
theorem B23374565 : Blo 1707054 23374565 := bstep (se 4 (by rfl) ⟨2191365, by rfl⟩ : syracuseStep 23374565 = 4382731) B4382731
theorem B3697481 : Blo 1707054 3697481 := bstep (se 2 (by rfl) ⟨1386555, by rfl⟩ : syracuseStep 3697481 = 2773111) B2773111
theorem B6482875 : Blo 1707054 6482875 := bstep (se 1 (by rfl) ⟨4862156, by rfl⟩ : syracuseStep 6482875 = 9724313) B9724313
theorem B3845051 : Blo 1707054 3845051 := bstep (se 1 (by rfl) ⟨2883788, by rfl⟩ : syracuseStep 3845051 = 5767577) B5767577
theorem B1731547 : Blo 1707054 1731547 := bstep (se 1 (by rfl) ⟨1298660, by rfl⟩ : syracuseStep 1731547 = 2597321) B2597321
theorem B3845177 : Blo 1707054 3845177 := bstep (se 2 (by rfl) ⟨1441941, by rfl⟩ : syracuseStep 3845177 = 2883883) B2883883
theorem B1707087 : Blo 1707054 1707087 := bstep (se 1 (by rfl) ⟨1280315, by rfl⟩ : syracuseStep 1707087 = 2560631) B2560631
theorem B1707103 : Blo 1707054 1707103 := bstep (se 1 (by rfl) ⟨1280327, by rfl⟩ : syracuseStep 1707103 = 2560655) B2560655
theorem B1707131 : Blo 1707054 1707131 := bstep (se 1 (by rfl) ⟨1280348, by rfl⟩ : syracuseStep 1707131 = 2560697) B2560697
theorem B1707183 : Blo 1707054 1707183 := bstep (se 1 (by rfl) ⟨1280387, by rfl⟩ : syracuseStep 1707183 = 2560775) B2560775
theorem B1707207 : Blo 1707054 1707207 := bstep (se 1 (by rfl) ⟨1280405, by rfl⟩ : syracuseStep 1707207 = 2560811) B2560811
theorem B1707227 : Blo 1707054 1707227 := bstep (se 1 (by rfl) ⟨1280420, by rfl⟩ : syracuseStep 1707227 = 2560841) B2560841
theorem B24612133 : Blo 1707054 24612133 := bstep (se 4 (by rfl) ⟨2307387, by rfl⟩ : syracuseStep 24612133 = 4614775) B4614775
theorem B1707303 : Blo 1707054 1707303 := bstep (se 1 (by rfl) ⟨1280477, by rfl⟩ : syracuseStep 1707303 = 2560955) B2560955
theorem B1707343 : Blo 1707054 1707343 := bstep (se 1 (by rfl) ⟨1280507, by rfl⟩ : syracuseStep 1707343 = 2561015) B2561015
theorem B1707359 : Blo 1707054 1707359 := bstep (se 1 (by rfl) ⟨1280519, by rfl⟩ : syracuseStep 1707359 = 2561039) B2561039
theorem B1707387 : Blo 1707054 1707387 := bstep (se 1 (by rfl) ⟨1280540, by rfl⟩ : syracuseStep 1707387 = 2561081) B2561081
theorem B5762447 : Blo 1707054 5762447 := bstep (se 1 (by rfl) ⟨4321835, by rfl⟩ : syracuseStep 5762447 = 8643671) B8643671
theorem B1707439 : Blo 1707054 1707439 := bstep (se 1 (by rfl) ⟨1280579, by rfl⟩ : syracuseStep 1707439 = 2561159) B2561159
theorem B1707463 : Blo 1707054 1707463 := bstep (se 1 (by rfl) ⟨1280597, by rfl⟩ : syracuseStep 1707463 = 2561195) B2561195
theorem B12307913 : Blo 1707054 12307913 := bstep (se 2 (by rfl) ⟨4615467, by rfl⟩ : syracuseStep 12307913 = 9230935) B9230935
theorem B1707483 : Blo 1707054 1707483 := bstep (se 1 (by rfl) ⟨1280612, by rfl⟩ : syracuseStep 1707483 = 2561225) B2561225
theorem B1707559 : Blo 1707054 1707559 := bstep (se 1 (by rfl) ⟨1280669, by rfl⟩ : syracuseStep 1707559 = 2561339) B2561339
theorem B16420391 : Blo 1707054 16420391 := bstep (se 1 (by rfl) ⟨12315293, by rfl⟩ : syracuseStep 16420391 = 24630587) B24630587
theorem B1707599 : Blo 1707054 1707599 := bstep (se 1 (by rfl) ⟨1280699, by rfl⟩ : syracuseStep 1707599 = 2561399) B2561399
theorem B37957207 : Blo 1707054 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B1707615 : Blo 1707054 1707615 := bstep (se 1 (by rfl) ⟨1280711, by rfl⟩ : syracuseStep 1707615 = 2561423) B2561423
theorem B1707643 : Blo 1707054 1707643 := bstep (se 1 (by rfl) ⟨1280732, by rfl⟩ : syracuseStep 1707643 = 2561465) B2561465
theorem B6327931 : Blo 1707054 6327931 := bstep (se 1 (by rfl) ⟨4745948, by rfl⟩ : syracuseStep 6327931 = 9491897) B9491897
theorem B1707695 : Blo 1707054 1707695 := bstep (se 1 (by rfl) ⟨1280771, by rfl⟩ : syracuseStep 1707695 = 2561543) B2561543
theorem B1707719 : Blo 1707054 1707719 := bstep (se 1 (by rfl) ⟨1280789, by rfl⟩ : syracuseStep 1707719 = 2561579) B2561579
theorem B6155975 : Blo 1707054 6155975 := bstep (se 1 (by rfl) ⟨4616981, by rfl⟩ : syracuseStep 6155975 = 9233963) B9233963
theorem B6483665 : Blo 1707054 6483665 := bstep (se 2 (by rfl) ⟨2431374, by rfl⟩ : syracuseStep 6483665 = 4862749) B4862749
theorem B5762771 : Blo 1707054 5762771 := bstep (se 1 (by rfl) ⟨4322078, by rfl⟩ : syracuseStep 5762771 = 8644157) B8644157
theorem B1707739 : Blo 1707054 1707739 := bstep (se 1 (by rfl) ⟨1280804, by rfl⟩ : syracuseStep 1707739 = 2561609) B2561609
theorem B1707815 : Blo 1707054 1707815 := bstep (se 1 (by rfl) ⟨1280861, by rfl⟩ : syracuseStep 1707815 = 2561723) B2561723
theorem B4321097 : Blo 1707054 4321097 := bstep (se 2 (by rfl) ⟨1620411, by rfl⟩ : syracuseStep 4321097 = 3240823) B3240823
theorem B1707855 : Blo 1707054 1707855 := bstep (se 1 (by rfl) ⟨1280891, by rfl⟩ : syracuseStep 1707855 = 2561783) B2561783
theorem B1707871 : Blo 1707054 1707871 := bstep (se 1 (by rfl) ⟨1280903, by rfl⟩ : syracuseStep 1707871 = 2561807) B2561807
theorem B1707899 : Blo 1707054 1707899 := bstep (se 1 (by rfl) ⟨1280924, by rfl⟩ : syracuseStep 1707899 = 2561849) B2561849
theorem B1707951 : Blo 1707054 1707951 := bstep (se 1 (by rfl) ⟨1280963, by rfl⟩ : syracuseStep 1707951 = 2561927) B2561927
theorem B4861883 : Blo 1707054 4861883 := bstep (se 1 (by rfl) ⟨3646412, by rfl⟩ : syracuseStep 4861883 = 7292825) B7292825
theorem B8646587 : Blo 1707054 8646587 := bstep (se 1 (by rfl) ⟨6484940, by rfl⟩ : syracuseStep 8646587 = 12969881) B12969881
theorem B9727937 : Blo 1707054 9727937 := bstep (se 2 (by rfl) ⟨3647976, by rfl⟩ : syracuseStep 9727937 = 7295953) B7295953
theorem B1707975 : Blo 1707054 1707975 := bstep (se 1 (by rfl) ⟨1280981, by rfl⟩ : syracuseStep 1707975 = 2561963) B2561963
theorem B1707995 : Blo 1707054 1707995 := bstep (se 1 (by rfl) ⟨1280996, by rfl⟩ : syracuseStep 1707995 = 2561993) B2561993
theorem B1921063 : Blo 1707054 1921063 := bstep (se 1 (by rfl) ⟨1440797, by rfl⟩ : syracuseStep 1921063 = 2881595) B2881595
theorem B1708071 : Blo 1707054 1708071 := bstep (se 1 (by rfl) ⟨1281053, by rfl⟩ : syracuseStep 1708071 = 2562107) B2562107
theorem B1708111 : Blo 1707054 1708111 := bstep (se 1 (by rfl) ⟨1281083, by rfl⟩ : syracuseStep 1708111 = 2562167) B2562167
theorem B1708127 : Blo 1707054 1708127 := bstep (se 1 (by rfl) ⟨1281095, by rfl⟩ : syracuseStep 1708127 = 2562191) B2562191
theorem B1708155 : Blo 1707054 1708155 := bstep (se 1 (by rfl) ⟨1281116, by rfl⟩ : syracuseStep 1708155 = 2562233) B2562233
theorem B6484121 : Blo 1707054 6484121 := bstep (se 2 (by rfl) ⟨2431545, by rfl⟩ : syracuseStep 6484121 = 4863091) B4863091
theorem B7794845 : Blo 1707054 7794845 := bstep (se 3 (by rfl) ⟨1461533, by rfl⟩ : syracuseStep 7794845 = 2923067) B2923067
theorem B4321451 : Blo 1707054 4321451 := bstep (se 1 (by rfl) ⟨3241088, by rfl⟩ : syracuseStep 4321451 = 6482177) B6482177
theorem B1708207 : Blo 1707054 1708207 := bstep (se 1 (by rfl) ⟨1281155, by rfl⟩ : syracuseStep 1708207 = 2562311) B2562311
theorem B1708231 : Blo 1707054 1708231 := bstep (se 1 (by rfl) ⟨1281173, by rfl⟩ : syracuseStep 1708231 = 2562347) B2562347
theorem B1708251 : Blo 1707054 1708251 := bstep (se 1 (by rfl) ⟨1281188, by rfl⟩ : syracuseStep 1708251 = 2562377) B2562377
theorem B1708327 : Blo 1707054 1708327 := bstep (se 1 (by rfl) ⟨1281245, by rfl⟩ : syracuseStep 1708327 = 2562491) B2562491
theorem B1708367 : Blo 1707054 1708367 := bstep (se 1 (by rfl) ⟨1281275, by rfl⟩ : syracuseStep 1708367 = 2562551) B2562551
theorem B1708383 : Blo 1707054 1708383 := bstep (se 1 (by rfl) ⟨1281287, by rfl⟩ : syracuseStep 1708383 = 2562575) B2562575
theorem B10940777 : Blo 1707054 10940777 := bstep (se 2 (by rfl) ⟨4102791, by rfl⟩ : syracuseStep 10940777 = 8205583) B8205583
theorem B1708411 : Blo 1707054 1708411 := bstep (se 1 (by rfl) ⟨1281308, by rfl⟩ : syracuseStep 1708411 = 2562617) B2562617
theorem B11088257 : Blo 1707054 11088257 := bstep (se 2 (by rfl) ⟨4158096, by rfl⟩ : syracuseStep 11088257 = 8316193) B8316193
theorem B1708463 : Blo 1707054 1708463 := bstep (se 1 (by rfl) ⟨1281347, by rfl⟩ : syracuseStep 1708463 = 2562695) B2562695
theorem B1708487 : Blo 1707054 1708487 := bstep (se 1 (by rfl) ⟨1281365, by rfl⟩ : syracuseStep 1708487 = 2562731) B2562731
theorem B1708507 : Blo 1707054 1708507 := bstep (se 1 (by rfl) ⟨1281380, by rfl⟩ : syracuseStep 1708507 = 2562761) B2562761
theorem B11096599 : Blo 1707054 11096599 := bstep (se 1 (by rfl) ⟨8322449, by rfl⟩ : syracuseStep 11096599 = 16644899) B16644899
theorem B1708583 : Blo 1707054 1708583 := bstep (se 1 (by rfl) ⟨1281437, by rfl⟩ : syracuseStep 1708583 = 2562875) B2562875
theorem B1708623 : Blo 1707054 1708623 := bstep (se 1 (by rfl) ⟨1281467, by rfl⟩ : syracuseStep 1708623 = 2562935) B2562935
theorem B1708639 : Blo 1707054 1708639 := bstep (se 1 (by rfl) ⟨1281479, by rfl⟩ : syracuseStep 1708639 = 2562959) B2562959
theorem B1708667 : Blo 1707054 1708667 := bstep (se 1 (by rfl) ⟨1281500, by rfl⟩ : syracuseStep 1708667 = 2563001) B2563001
theorem B1708719 : Blo 1707054 1708719 := bstep (se 1 (by rfl) ⟨1281539, by rfl⟩ : syracuseStep 1708719 = 2563079) B2563079
theorem B1708743 : Blo 1707054 1708743 := bstep (se 1 (by rfl) ⟨1281557, by rfl⟩ : syracuseStep 1708743 = 2563115) B2563115
theorem B1708763 : Blo 1707054 1708763 := bstep (se 1 (by rfl) ⟨1281572, by rfl⟩ : syracuseStep 1708763 = 2563145) B2563145
theorem B6574841 : Blo 1707054 6574841 := bstep (se 2 (by rfl) ⟨2465565, by rfl⟩ : syracuseStep 6574841 = 4931131) B4931131
theorem B1708839 : Blo 1707054 1708839 := bstep (se 1 (by rfl) ⟨1281629, by rfl⟩ : syracuseStep 1708839 = 2563259) B2563259
theorem B1708879 : Blo 1707054 1708879 := bstep (se 1 (by rfl) ⟨1281659, by rfl⟩ : syracuseStep 1708879 = 2563319) B2563319
theorem B1708895 : Blo 1707054 1708895 := bstep (se 1 (by rfl) ⟨1281671, by rfl⟩ : syracuseStep 1708895 = 2563343) B2563343
theorem B5763959 : Blo 1707054 5763959 := bstep (se 1 (by rfl) ⟨4322969, by rfl⟩ : syracuseStep 5763959 = 8645939) B8645939
theorem B1708923 : Blo 1707054 1708923 := bstep (se 1 (by rfl) ⟨1281692, by rfl⟩ : syracuseStep 1708923 = 2563385) B2563385
theorem B2560943 : Blo 1707054 2560943 := bstep (se 1 (by rfl) ⟨1920707, by rfl⟩ : syracuseStep 2560943 = 3841415) B3841415
theorem B1708975 : Blo 1707054 1708975 := bstep (se 1 (by rfl) ⟨1281731, by rfl⟩ : syracuseStep 1708975 = 2563463) B2563463
theorem B4322231 : Blo 1707054 4322231 := bstep (se 1 (by rfl) ⟨3241673, by rfl⟩ : syracuseStep 4322231 = 6483347) B6483347
theorem B1708999 : Blo 1707054 1708999 := bstep (se 1 (by rfl) ⟨1281749, by rfl⟩ : syracuseStep 1708999 = 2563499) B2563499
theorem B1709019 : Blo 1707054 1709019 := bstep (se 1 (by rfl) ⟨1281764, by rfl⟩ : syracuseStep 1709019 = 2563529) B2563529
theorem B3240967 : Blo 1707054 3240967 := bstep (se 1 (by rfl) ⟨2430725, by rfl⟩ : syracuseStep 3240967 = 4861451) B4861451
theorem B2561033 : Blo 1707054 2561033 := bstep (se 2 (by rfl) ⟨960387, by rfl⟩ : syracuseStep 2561033 = 1920775) B1920775
theorem B2561063 : Blo 1707054 2561063 := bstep (se 1 (by rfl) ⟨1920797, by rfl⟩ : syracuseStep 2561063 = 3841595) B3841595
theorem B31159363 : Blo 1707054 31159363 := bstep (se 1 (by rfl) ⟨23369522, by rfl⟩ : syracuseStep 31159363 = 46739045) B46739045
theorem B5764175 : Blo 1707054 5764175 := bstep (se 1 (by rfl) ⟨4323131, by rfl⟩ : syracuseStep 5764175 = 8646263) B8646263
theorem B2561147 : Blo 1707054 2561147 := bstep (se 1 (by rfl) ⟨1920860, by rfl⟩ : syracuseStep 2561147 = 3841721) B3841721
theorem B8647883 : Blo 1707054 8647883 := bstep (se 1 (by rfl) ⟨6485912, by rfl⟩ : syracuseStep 8647883 = 12971825) B12971825
theorem B2561273 : Blo 1707054 2561273 := bstep (se 2 (by rfl) ⟨960477, by rfl⟩ : syracuseStep 2561273 = 1920955) B1920955
theorem B2561375 : Blo 1707054 2561375 := bstep (se 1 (by rfl) ⟨1921031, by rfl⟩ : syracuseStep 2561375 = 3842063) B3842063
theorem B4617577 : Blo 1707054 4617577 := bstep (se 2 (by rfl) ⟨1731591, by rfl⟩ : syracuseStep 4617577 = 3463183) B3463183
theorem B2561387 : Blo 1707054 2561387 := bstep (se 1 (by rfl) ⟨1921040, by rfl⟩ : syracuseStep 2561387 = 3842081) B3842081
theorem B5469569 : Blo 1707054 5469569 := bstep (se 2 (by rfl) ⟨2051088, by rfl⟩ : syracuseStep 5469569 = 4102177) B4102177
theorem B3077519 : Blo 1707054 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B14595491 : Blo 1707054 14595491 := bstep (se 1 (by rfl) ⟨10946618, by rfl⟩ : syracuseStep 14595491 = 21893237) B21893237
theorem B2921903 : Blo 1707054 2921903 := bstep (se 1 (by rfl) ⟨2191427, by rfl⟩ : syracuseStep 2921903 = 4382855) B4382855
theorem B5764553 : Blo 1707054 5764553 := bstep (se 2 (by rfl) ⟨2161707, by rfl⟩ : syracuseStep 5764553 = 4323415) B4323415
theorem B3077671 : Blo 1707054 3077671 := bstep (se 1 (by rfl) ⟨2308253, by rfl⟩ : syracuseStep 3077671 = 4616507) B4616507
theorem B7296551 : Blo 1707054 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B3241529 : Blo 1707054 3241529 := bstep (se 2 (by rfl) ⟨1215573, by rfl⟩ : syracuseStep 3241529 = 2431147) B2431147
theorem B2561615 : Blo 1707054 2561615 := bstep (se 1 (by rfl) ⟨1921211, by rfl⟩ : syracuseStep 2561615 = 3842423) B3842423
theorem B19445345 : Blo 1707054 19445345 := bstep (se 2 (by rfl) ⟨7292004, by rfl⟩ : syracuseStep 19445345 = 14584009) B14584009
theorem B1922683 : Blo 1707054 1922683 := bstep (se 1 (by rfl) ⟨1442012, by rfl⟩ : syracuseStep 1922683 = 2884025) B2884025
theorem B48051893 : Blo 1707054 48051893 := bstep (se 5 (by rfl) ⟨2252432, by rfl⟩ : syracuseStep 48051893 = 4504865) B4504865
theorem B2561735 : Blo 1707054 2561735 := bstep (se 1 (by rfl) ⟨1921301, by rfl⟩ : syracuseStep 2561735 = 3842603) B3842603
theorem B5191379 : Blo 1707054 5191379 := bstep (se 1 (by rfl) ⟨3893534, by rfl⟩ : syracuseStep 5191379 = 7787069) B7787069
theorem B5764823 : Blo 1707054 5764823 := bstep (se 1 (by rfl) ⟨4323617, by rfl⟩ : syracuseStep 5764823 = 8647235) B8647235
theorem B2881271 : Blo 1707054 2881271 := bstep (se 1 (by rfl) ⟨2160953, by rfl⟩ : syracuseStep 2881271 = 4321907) B4321907
theorem B7788383 : Blo 1707054 7788383 := bstep (se 1 (by rfl) ⟨5841287, by rfl⟩ : syracuseStep 7788383 = 11682575) B11682575
theorem B2561897 : Blo 1707054 2561897 := bstep (se 2 (by rfl) ⟨960711, by rfl⟩ : syracuseStep 2561897 = 1921423) B1921423
theorem B4323233 : Blo 1707054 4323233 := bstep (se 2 (by rfl) ⟨1621212, by rfl⟩ : syracuseStep 4323233 = 3242425) B3242425
theorem B2308015 : Blo 1707054 2308015 := bstep (se 1 (by rfl) ⟨1731011, by rfl⟩ : syracuseStep 2308015 = 3462023) B3462023
theorem B5765039 : Blo 1707054 5765039 := bstep (se 1 (by rfl) ⟨4323779, by rfl⟩ : syracuseStep 5765039 = 8647559) B8647559
theorem B2561975 : Blo 1707054 2561975 := bstep (se 1 (by rfl) ⟨1921481, by rfl⟩ : syracuseStep 2561975 = 3842963) B3842963
theorem B8763329 : Blo 1707054 8763329 := bstep (se 2 (by rfl) ⟨3286248, by rfl⟩ : syracuseStep 8763329 = 6572497) B6572497
theorem B2562011 : Blo 1707054 2562011 := bstep (se 1 (by rfl) ⟨1921508, by rfl⟩ : syracuseStep 2562011 = 3843017) B3843017
theorem B6928391 : Blo 1707054 6928391 := bstep (se 1 (by rfl) ⟨5196293, by rfl⟩ : syracuseStep 6928391 = 10392587) B10392587
theorem B6666259 : Blo 1707054 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B13850681 : Blo 1707054 13850681 := bstep (se 2 (by rfl) ⟨5194005, by rfl⟩ : syracuseStep 13850681 = 10388011) B10388011
theorem B2881615 : Blo 1707054 2881615 := bstep (se 1 (by rfl) ⟨2161211, by rfl⟩ : syracuseStep 2881615 = 4322423) B4322423
theorem B6486095 : Blo 1707054 6486095 := bstep (se 1 (by rfl) ⟨4864571, by rfl⟩ : syracuseStep 6486095 = 9729143) B9729143
theorem B3078391 : Blo 1707054 3078391 := bstep (se 1 (by rfl) ⟨2308793, by rfl⟩ : syracuseStep 3078391 = 4617587) B4617587
theorem B6486263 : Blo 1707054 6486263 := bstep (se 1 (by rfl) ⟨4864697, by rfl⟩ : syracuseStep 6486263 = 9729395) B9729395
theorem B2881865 : Blo 1707054 2881865 := bstep (se 2 (by rfl) ⟨1080699, by rfl⟩ : syracuseStep 2881865 = 2161399) B2161399
theorem B4323689 : Blo 1707054 4323689 := bstep (se 2 (by rfl) ⟨1621383, by rfl⟩ : syracuseStep 4323689 = 3242767) B3242767
theorem B2562479 : Blo 1707054 2562479 := bstep (se 1 (by rfl) ⟨1921859, by rfl⟩ : syracuseStep 2562479 = 3843719) B3843719
theorem B4995571 : Blo 1707054 4995571 := bstep (se 1 (by rfl) ⟨3746678, by rfl⟩ : syracuseStep 4995571 = 7493357) B7493357
theorem B2562569 : Blo 1707054 2562569 := bstep (se 2 (by rfl) ⟨960963, by rfl⟩ : syracuseStep 2562569 = 1921927) B1921927
theorem B2734631 : Blo 1707054 2734631 := bstep (se 1 (by rfl) ⟨2050973, by rfl⟩ : syracuseStep 2734631 = 4101947) B4101947
theorem B2562599 : Blo 1707054 2562599 := bstep (se 1 (by rfl) ⟨1921949, by rfl⟩ : syracuseStep 2562599 = 3843899) B3843899
theorem B4102753 : Blo 1707054 4102753 := bstep (se 2 (by rfl) ⟨1538532, by rfl⟩ : syracuseStep 4102753 = 3077065) B3077065
theorem B2562683 : Blo 1707054 2562683 := bstep (se 1 (by rfl) ⟨1922012, by rfl⟩ : syracuseStep 2562683 = 3844025) B3844025
theorem B19462841 : Blo 1707054 19462841 := bstep (se 2 (by rfl) ⟨7298565, by rfl⟩ : syracuseStep 19462841 = 14597131) B14597131
theorem B2882297 : Blo 1707054 2882297 := bstep (se 2 (by rfl) ⟨1080861, by rfl⟩ : syracuseStep 2882297 = 2161723) B2161723
theorem B2562809 : Blo 1707054 2562809 := bstep (se 2 (by rfl) ⟨961053, by rfl⟩ : syracuseStep 2562809 = 1922107) B1922107
theorem B2562911 : Blo 1707054 2562911 := bstep (se 1 (by rfl) ⟨1922183, by rfl⟩ : syracuseStep 2562911 = 3844367) B3844367
theorem B3840875 : Blo 1707054 3840875 := bstep (se 1 (by rfl) ⟨2880656, by rfl⟩ : syracuseStep 3840875 = 5761313) B5761313
theorem B2562923 : Blo 1707054 2562923 := bstep (se 1 (by rfl) ⟨1922192, by rfl⟩ : syracuseStep 2562923 = 3844385) B3844385
theorem B3079019 : Blo 1707054 3079019 := bstep (se 1 (by rfl) ⟨2309264, by rfl⟩ : syracuseStep 3079019 = 4618529) B4618529
theorem B3079055 : Blo 1707054 3079055 := bstep (se 1 (by rfl) ⟨2309291, by rfl⟩ : syracuseStep 3079055 = 4618583) B4618583
theorem B3840929 : Blo 1707054 3840929 := bstep (se 2 (by rfl) ⟨1440348, by rfl⟩ : syracuseStep 3840929 = 2880697) B2880697
theorem B2882479 : Blo 1707054 2882479 := bstep (se 1 (by rfl) ⟨2161859, by rfl⟩ : syracuseStep 2882479 = 4323719) B4323719
theorem B2882567 : Blo 1707054 2882567 := bstep (se 1 (by rfl) ⟨2161925, by rfl⟩ : syracuseStep 2882567 = 4323851) B4323851
theorem B3243017 : Blo 1707054 3243017 := bstep (se 2 (by rfl) ⟨1216131, by rfl⟩ : syracuseStep 3243017 = 2432263) B2432263
theorem B2563151 : Blo 1707054 2563151 := bstep (se 1 (by rfl) ⟨1922363, by rfl⟩ : syracuseStep 2563151 = 3844727) B3844727
theorem B13843649 : Blo 1707054 13843649 := bstep (se 2 (by rfl) ⟨5191368, by rfl⟩ : syracuseStep 13843649 = 10382737) B10382737
theorem B6487235 : Blo 1707054 6487235 := bstep (se 1 (by rfl) ⟨4865426, by rfl⟩ : syracuseStep 6487235 = 9730853) B9730853
theorem B2563271 : Blo 1707054 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B3841271 : Blo 1707054 3841271 := bstep (se 1 (by rfl) ⟨2880953, by rfl⟩ : syracuseStep 3841271 = 5761907) B5761907
theorem B2882911 : Blo 1707054 2882911 := bstep (se 1 (by rfl) ⟨2162183, by rfl⟩ : syracuseStep 2882911 = 4324367) B4324367
theorem B2563433 : Blo 1707054 2563433 := bstep (se 2 (by rfl) ⟨961287, by rfl⟩ : syracuseStep 2563433 = 1922575) B1922575
theorem B32841085 : Blo 1707054 32841085 := bstep (se 3 (by rfl) ⟨6157703, by rfl⟩ : syracuseStep 32841085 = 12315407) B12315407
theorem B2882999 : Blo 1707054 2882999 := bstep (se 1 (by rfl) ⟨2162249, by rfl⟩ : syracuseStep 2882999 = 4324499) B4324499
theorem B2563511 : Blo 1707054 2563511 := bstep (se 1 (by rfl) ⟨1922633, by rfl⟩ : syracuseStep 2563511 = 3845267) B3845267
theorem B5545417 : Blo 1707054 5545417 := bstep (se 2 (by rfl) ⟨2079531, by rfl⟩ : syracuseStep 5545417 = 4159063) B4159063
theorem B2735579 : Blo 1707054 2735579 := bstep (se 1 (by rfl) ⟨2051684, by rfl⟩ : syracuseStep 2735579 = 4103369) B4103369
theorem B2563547 : Blo 1707054 2563547 := bstep (se 1 (by rfl) ⟨1922660, by rfl⟩ : syracuseStep 2563547 = 3845321) B3845321
theorem B4324873 : Blo 1707054 4324873 := bstep (se 2 (by rfl) ⟨1621827, by rfl⟩ : syracuseStep 4324873 = 3243655) B3243655
theorem B12975713 : Blo 1707054 12975713 := bstep (se 2 (by rfl) ⟨4865892, by rfl⟩ : syracuseStep 12975713 = 9731785) B9731785
theorem B5472029 : Blo 1707054 5472029 := bstep (se 3 (by rfl) ⟨1026005, by rfl⟩ : syracuseStep 5472029 = 2052011) B2052011
theorem B3841865 : Blo 1707054 3841865 := bstep (se 2 (by rfl) ⟨1440699, by rfl⟩ : syracuseStep 3841865 = 2881399) B2881399
theorem B5472107 : Blo 1707054 5472107 := bstep (se 1 (by rfl) ⟨4104080, by rfl⟩ : syracuseStep 5472107 = 8208161) B8208161
theorem B3243883 : Blo 1707054 3243883 := bstep (se 1 (by rfl) ⟨2432912, by rfl⟩ : syracuseStep 3243883 = 4865825) B4865825
theorem B3243959 : Blo 1707054 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B16646147 : Blo 1707054 16646147 := bstep (se 1 (by rfl) ⟨12484610, by rfl⟩ : syracuseStep 16646147 = 24969221) B24969221
theorem B8888345 : Blo 1707054 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B3842153 : Blo 1707054 3842153 := bstep (se 2 (by rfl) ⟨1440807, by rfl⟩ : syracuseStep 3842153 = 2881615) B2881615
theorem B8650961 : Blo 1707054 8650961 := bstep (se 2 (by rfl) ⟨3244110, by rfl⟩ : syracuseStep 8650961 = 6488221) B6488221
theorem B4104521 : Blo 1707054 4104521 := bstep (se 2 (by rfl) ⟨1539195, by rfl⟩ : syracuseStep 4104521 = 3078391) B3078391
theorem B6488495 : Blo 1707054 6488495 := bstep (se 1 (by rfl) ⟨4866371, by rfl⟩ : syracuseStep 6488495 = 9732743) B9732743
theorem B4383227 : Blo 1707054 4383227 := bstep (se 1 (by rfl) ⟨3287420, by rfl⟩ : syracuseStep 4383227 = 6574841) B6574841
theorem B3842639 : Blo 1707054 3842639 := bstep (se 1 (by rfl) ⟨2881979, by rfl⟩ : syracuseStep 3842639 = 5763959) B5763959
theorem B6660761 : Blo 1707054 6660761 := bstep (se 2 (by rfl) ⟨2497785, by rfl⟩ : syracuseStep 6660761 = 4995571) B4995571
theorem B8651447 : Blo 1707054 8651447 := bstep (se 1 (by rfl) ⟨6488585, by rfl⟩ : syracuseStep 8651447 = 12977171) B12977171
theorem B14795465 : Blo 1707054 14795465 := bstep (se 2 (by rfl) ⟨5548299, by rfl⟩ : syracuseStep 14795465 = 11096599) B11096599
theorem B3842783 : Blo 1707054 3842783 := bstep (se 1 (by rfl) ⟨2882087, by rfl⟩ : syracuseStep 3842783 = 5764175) B5764175
theorem B3646379 : Blo 1707054 3646379 := bstep (se 1 (by rfl) ⟨2734784, by rfl⟩ : syracuseStep 3646379 = 5469569) B5469569
theorem B126288821 : Blo 1707054 126288821 := bstep (se 5 (by rfl) ⟨5919788, by rfl⟩ : syracuseStep 126288821 = 11839577) B11839577
theorem B3843035 : Blo 1707054 3843035 := bstep (se 1 (by rfl) ⟨2882276, by rfl⟩ : syracuseStep 3843035 = 5764553) B5764553
theorem B3843215 : Blo 1707054 3843215 := bstep (se 1 (by rfl) ⟨2882411, by rfl⟩ : syracuseStep 3843215 = 5764823) B5764823
theorem B8651933 : Blo 1707054 8651933 := bstep (se 3 (by rfl) ⟨1622237, by rfl⟩ : syracuseStep 8651933 = 3244475) B3244475
theorem B3843305 : Blo 1707054 3843305 := bstep (se 2 (by rfl) ⟨1441239, by rfl⟩ : syracuseStep 3843305 = 2882479) B2882479
theorem B8643833 : Blo 1707054 8643833 := bstep (se 2 (by rfl) ⟨3241437, by rfl⟩ : syracuseStep 8643833 = 6482875) B6482875
theorem B3843359 : Blo 1707054 3843359 := bstep (se 1 (by rfl) ⟨2882519, by rfl⟩ : syracuseStep 3843359 = 5765039) B5765039
theorem B5842219 : Blo 1707054 5842219 := bstep (se 1 (by rfl) ⟨4381664, by rfl⟩ : syracuseStep 5842219 = 8763329) B8763329
theorem B32826869 : Blo 1707054 32826869 := bstep (se 5 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 32826869 = 3077519) B3077519
theorem B3843881 : Blo 1707054 3843881 := bstep (se 2 (by rfl) ⟨1441455, by rfl⟩ : syracuseStep 3843881 = 2882911) B2882911
theorem B15583043 : Blo 1707054 15583043 := bstep (se 1 (by rfl) ⟨11687282, by rfl⟩ : syracuseStep 15583043 = 23374565) B23374565
theorem B43788113 : Blo 1707054 43788113 := bstep (se 2 (by rfl) ⟨16420542, by rfl⟩ : syracuseStep 43788113 = 32841085) B32841085
theorem B24627077 : Blo 1707054 24627077 := bstep (se 4 (by rfl) ⟨2308788, by rfl⟩ : syracuseStep 24627077 = 4617577) B4617577
theorem B16410701 : Blo 1707054 16410701 := bstep (se 3 (by rfl) ⟨3077006, by rfl⟩ : syracuseStep 16410701 = 6154013) B6154013
theorem B17533057 : Blo 1707054 17533057 := bstep (se 2 (by rfl) ⟨6574896, by rfl⟩ : syracuseStep 17533057 = 13149793) B13149793
theorem B10946825 : Blo 1707054 10946825 := bstep (se 2 (by rfl) ⟨4105059, by rfl⟩ : syracuseStep 10946825 = 8210119) B8210119
theorem B8210717 : Blo 1707054 8210717 := bstep (se 3 (by rfl) ⟨1539509, by rfl⟩ : syracuseStep 8210717 = 3079019) B3079019
theorem B10946927 : Blo 1707054 10946927 := bstep (se 1 (by rfl) ⟨8210195, by rfl⟩ : syracuseStep 10946927 = 16420391) B16420391
theorem B105154969 : Blo 1707054 105154969 := bstep (se 2 (by rfl) ⟨39433113, by rfl⟩ : syracuseStep 105154969 = 78866227) B78866227
theorem B9234917 : Blo 1707054 9234917 := bstep (se 4 (by rfl) ⟨865773, by rfl⟩ : syracuseStep 9234917 = 1731547) B1731547
theorem B3648019 : Blo 1707054 3648019 := bstep (se 1 (by rfl) ⟨2736014, by rfl⟩ : syracuseStep 3648019 = 5472029) B5472029
theorem B3648071 : Blo 1707054 3648071 := bstep (se 1 (by rfl) ⟨2736053, by rfl⟩ : syracuseStep 3648071 = 5472107) B5472107
theorem B5196563 : Blo 1707054 5196563 := bstep (se 1 (by rfl) ⟨3897422, by rfl⟩ : syracuseStep 5196563 = 7794845) B7794845
theorem B3844943 : Blo 1707054 3844943 := bstep (se 1 (by rfl) ⟨2883707, by rfl⟩ : syracuseStep 3844943 = 5767415) B5767415
theorem B7293851 : Blo 1707054 7293851 := bstep (se 1 (by rfl) ⟨5470388, by rfl⟩ : syracuseStep 7293851 = 10940777) B10940777
theorem B3845159 : Blo 1707054 3845159 := bstep (se 1 (by rfl) ⟨2883869, by rfl⟩ : syracuseStep 3845159 = 5767739) B5767739
theorem B62352463 : Blo 1707054 62352463 := bstep (se 1 (by rfl) ⟨46764347, by rfl⟩ : syracuseStep 62352463 = 93528695) B93528695
theorem B6237307 : Blo 1707054 6237307 := bstep (se 1 (by rfl) ⟨4677980, by rfl⟩ : syracuseStep 6237307 = 9355961) B9355961
theorem B3845339 : Blo 1707054 3845339 := bstep (se 1 (by rfl) ⟨2884004, by rfl⟩ : syracuseStep 3845339 = 5768009) B5768009
theorem B1707295 : Blo 1707054 1707295 := bstep (se 1 (by rfl) ⟨1280471, by rfl⟩ : syracuseStep 1707295 = 2560943) B2560943
theorem B1707355 : Blo 1707054 1707355 := bstep (se 1 (by rfl) ⟨1280516, by rfl⟩ : syracuseStep 1707355 = 2561033) B2561033
theorem B1707375 : Blo 1707054 1707375 := bstep (se 1 (by rfl) ⟨1280531, by rfl⟩ : syracuseStep 1707375 = 2561063) B2561063
theorem B1707431 : Blo 1707054 1707431 := bstep (se 1 (by rfl) ⟨1280573, by rfl⟩ : syracuseStep 1707431 = 2561147) B2561147
theorem B1707515 : Blo 1707054 1707515 := bstep (se 1 (by rfl) ⟨1280636, by rfl⟩ : syracuseStep 1707515 = 2561273) B2561273
theorem B1707583 : Blo 1707054 1707583 := bstep (se 1 (by rfl) ⟨1280687, by rfl⟩ : syracuseStep 1707583 = 2561375) B2561375
theorem B1707591 : Blo 1707054 1707591 := bstep (se 1 (by rfl) ⟨1280693, by rfl⟩ : syracuseStep 1707591 = 2561387) B2561387
theorem B29568685 : Blo 1707054 29568685 := bstep (se 3 (by rfl) ⟨5544128, by rfl⟩ : syracuseStep 29568685 = 11088257) B11088257
theorem B1707743 : Blo 1707054 1707743 := bstep (se 1 (by rfl) ⟨1280807, by rfl⟩ : syracuseStep 1707743 = 2561615) B2561615
theorem B12963563 : Blo 1707054 12963563 := bstep (se 1 (by rfl) ⟨9722672, by rfl⟩ : syracuseStep 12963563 = 19445345) B19445345
theorem B1707823 : Blo 1707054 1707823 := bstep (se 1 (by rfl) ⟨1280867, by rfl⟩ : syracuseStep 1707823 = 2561735) B2561735
theorem B3460919 : Blo 1707054 3460919 := bstep (se 1 (by rfl) ⟨2595689, by rfl⟩ : syracuseStep 3460919 = 5191379) B5191379
theorem B8204105 : Blo 1707054 8204105 := bstep (se 2 (by rfl) ⟨3076539, by rfl⟩ : syracuseStep 8204105 = 6153079) B6153079
theorem B1920847 : Blo 1707054 1920847 := bstep (se 1 (by rfl) ⟨1440635, by rfl⟩ : syracuseStep 1920847 = 2881271) B2881271
theorem B1707931 : Blo 1707054 1707931 := bstep (se 1 (by rfl) ⟨1280948, by rfl⟩ : syracuseStep 1707931 = 2561897) B2561897
theorem B1707983 : Blo 1707054 1707983 := bstep (se 1 (by rfl) ⟨1280987, by rfl⟩ : syracuseStep 1707983 = 2561975) B2561975
theorem B1708007 : Blo 1707054 1708007 := bstep (se 1 (by rfl) ⟨1281005, by rfl⟩ : syracuseStep 1708007 = 2562011) B2562011
theorem B4321289 : Blo 1707054 4321289 := bstep (se 2 (by rfl) ⟨1620483, by rfl⟩ : syracuseStep 4321289 = 3240967) B3240967
theorem B41545817 : Blo 1707054 41545817 := bstep (se 2 (by rfl) ⟨15579681, by rfl⟩ : syracuseStep 41545817 = 31159363) B31159363
theorem B1921243 : Blo 1707054 1921243 := bstep (se 1 (by rfl) ⟨1440932, by rfl⟩ : syracuseStep 1921243 = 2881865) B2881865
theorem B1708319 : Blo 1707054 1708319 := bstep (se 1 (by rfl) ⟨1281239, by rfl⟩ : syracuseStep 1708319 = 2562479) B2562479
theorem B5763419 : Blo 1707054 5763419 := bstep (se 1 (by rfl) ⟨4322564, by rfl⟩ : syracuseStep 5763419 = 8645129) B8645129
theorem B1708379 : Blo 1707054 1708379 := bstep (se 1 (by rfl) ⟨1281284, by rfl⟩ : syracuseStep 1708379 = 2562569) B2562569
theorem B1823087 : Blo 1707054 1823087 := bstep (se 1 (by rfl) ⟨1367315, by rfl⟩ : syracuseStep 1823087 = 2734631) B2734631
theorem B1708399 : Blo 1707054 1708399 := bstep (se 1 (by rfl) ⟨1281299, by rfl⟩ : syracuseStep 1708399 = 2562599) B2562599
theorem B1708455 : Blo 1707054 1708455 := bstep (se 1 (by rfl) ⟨1281341, by rfl⟩ : syracuseStep 1708455 = 2562683) B2562683
theorem B1921531 : Blo 1707054 1921531 := bstep (se 1 (by rfl) ⟨1441148, by rfl⟩ : syracuseStep 1921531 = 2882297) B2882297
theorem B1708539 : Blo 1707054 1708539 := bstep (se 1 (by rfl) ⟨1281404, by rfl⟩ : syracuseStep 1708539 = 2562809) B2562809
theorem B1708607 : Blo 1707054 1708607 := bstep (se 1 (by rfl) ⟨1281455, by rfl⟩ : syracuseStep 1708607 = 2562911) B2562911
theorem B2560583 : Blo 1707054 2560583 := bstep (se 1 (by rfl) ⟨1920437, by rfl⟩ : syracuseStep 2560583 = 3840875) B3840875
theorem B1708615 : Blo 1707054 1708615 := bstep (se 1 (by rfl) ⟨1281461, by rfl⟩ : syracuseStep 1708615 = 2562923) B2562923
theorem B7393889 : Blo 1707054 7393889 := bstep (se 2 (by rfl) ⟨2772708, by rfl⟩ : syracuseStep 7393889 = 5545417) B5545417
theorem B2052703 : Blo 1707054 2052703 := bstep (se 1 (by rfl) ⟨1539527, by rfl⟩ : syracuseStep 2052703 = 3079055) B3079055
theorem B2560619 : Blo 1707054 2560619 := bstep (se 1 (by rfl) ⟨1920464, by rfl⟩ : syracuseStep 2560619 = 3840929) B3840929
theorem B1921711 : Blo 1707054 1921711 := bstep (se 1 (by rfl) ⟨1441283, by rfl⟩ : syracuseStep 1921711 = 2882567) B2882567
theorem B1708767 : Blo 1707054 1708767 := bstep (se 1 (by rfl) ⟨1281575, by rfl⟩ : syracuseStep 1708767 = 2563151) B2563151
theorem B9229099 : Blo 1707054 9229099 := bstep (se 1 (by rfl) ⟨6921824, by rfl⟩ : syracuseStep 9229099 = 13843649) B13843649
theorem B1708847 : Blo 1707054 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B2560847 : Blo 1707054 2560847 := bstep (se 1 (by rfl) ⟨1920635, by rfl⟩ : syracuseStep 2560847 = 3841271) B3841271
theorem B1708955 : Blo 1707054 1708955 := bstep (se 1 (by rfl) ⟨1281716, by rfl⟩ : syracuseStep 1708955 = 2563433) B2563433
theorem B1921999 : Blo 1707054 1921999 := bstep (se 1 (by rfl) ⟨1441499, by rfl⟩ : syracuseStep 1921999 = 2882999) B2882999
theorem B1709007 : Blo 1707054 1709007 := bstep (se 1 (by rfl) ⟨1281755, by rfl⟩ : syracuseStep 1709007 = 2563511) B2563511
theorem B8205275 : Blo 1707054 8205275 := bstep (se 1 (by rfl) ⟨6153956, by rfl⟩ : syracuseStep 8205275 = 12307913) B12307913
theorem B1823719 : Blo 1707054 1823719 := bstep (se 1 (by rfl) ⟨1367789, by rfl⟩ : syracuseStep 1823719 = 2735579) B2735579
theorem B1709031 : Blo 1707054 1709031 := bstep (se 1 (by rfl) ⟨1281773, by rfl⟩ : syracuseStep 1709031 = 2563547) B2563547
theorem B4322443 : Blo 1707054 4322443 := bstep (se 1 (by rfl) ⟨3241832, by rfl⟩ : syracuseStep 4322443 = 6483665) B6483665
theorem B12965021 : Blo 1707054 12965021 := bstep (se 3 (by rfl) ⟨2430941, by rfl⟩ : syracuseStep 12965021 = 4861883) B4861883
theorem B2880731 : Blo 1707054 2880731 := bstep (se 1 (by rfl) ⟨2160548, by rfl⟩ : syracuseStep 2880731 = 4321097) B4321097
theorem B2561243 : Blo 1707054 2561243 := bstep (se 1 (by rfl) ⟨1920932, by rfl⟩ : syracuseStep 2561243 = 3841865) B3841865
theorem B3077353 : Blo 1707054 3077353 := bstep (se 2 (by rfl) ⟨1154007, by rfl⟩ : syracuseStep 3077353 = 2308015) B2308015
theorem B5764391 : Blo 1707054 5764391 := bstep (se 1 (by rfl) ⟨4323293, by rfl⟩ : syracuseStep 5764391 = 8646587) B8646587
theorem B6485291 : Blo 1707054 6485291 := bstep (se 1 (by rfl) ⟨4863968, by rfl⟩ : syracuseStep 6485291 = 9727937) B9727937
theorem B1922395 : Blo 1707054 1922395 := bstep (se 1 (by rfl) ⟨1441796, by rfl⟩ : syracuseStep 1922395 = 2883593) B2883593
theorem B4273505 : Blo 1707054 4273505 := bstep (se 2 (by rfl) ⟨1602564, by rfl⟩ : syracuseStep 4273505 = 3205129) B3205129
theorem B8648045 : Blo 1707054 8648045 := bstep (se 3 (by rfl) ⟨1621508, by rfl⟩ : syracuseStep 8648045 = 3243017) B3243017
theorem B2561417 : Blo 1707054 2561417 := bstep (se 2 (by rfl) ⟨960531, by rfl⟩ : syracuseStep 2561417 = 1921063) B1921063
theorem B4322747 : Blo 1707054 4322747 := bstep (se 1 (by rfl) ⟨3242060, by rfl⟩ : syracuseStep 4322747 = 6484121) B6484121
theorem B2880967 : Blo 1707054 2880967 := bstep (se 1 (by rfl) ⟨2160725, by rfl⟩ : syracuseStep 2880967 = 4321451) B4321451
theorem B1922503 : Blo 1707054 1922503 := bstep (se 1 (by rfl) ⟨1441877, by rfl⟩ : syracuseStep 1922503 = 2883755) B2883755
theorem B4101715 : Blo 1707054 4101715 := bstep (se 1 (by rfl) ⟨3076286, by rfl⟩ : syracuseStep 4101715 = 6152573) B6152573
theorem B8763065 : Blo 1707054 8763065 := bstep (se 2 (by rfl) ⟨3286149, by rfl⟩ : syracuseStep 8763065 = 6572299) B6572299
theorem B2561771 : Blo 1707054 2561771 := bstep (se 1 (by rfl) ⟨1921328, by rfl⟩ : syracuseStep 2561771 = 3842657) B3842657
theorem B2774825 : Blo 1707054 2774825 := bstep (se 2 (by rfl) ⟨1040559, by rfl⟩ : syracuseStep 2774825 = 2081119) B2081119
theorem B147740597 : Blo 1707054 147740597 := bstep (se 5 (by rfl) ⟨6925340, by rfl⟩ : syracuseStep 147740597 = 13850681) B13850681
theorem B2881487 : Blo 1707054 2881487 := bstep (se 1 (by rfl) ⟨2161115, by rfl⟩ : syracuseStep 2881487 = 4322231) B4322231
theorem B2561999 : Blo 1707054 2561999 := bstep (se 1 (by rfl) ⟨1921499, by rfl⟩ : syracuseStep 2561999 = 3842999) B3842999
theorem B5470337 : Blo 1707054 5470337 := bstep (se 2 (by rfl) ⟨2051376, by rfl⟩ : syracuseStep 5470337 = 4102753) B4102753
theorem B5765255 : Blo 1707054 5765255 := bstep (se 1 (by rfl) ⟨4323941, by rfl⟩ : syracuseStep 5765255 = 8647883) B8647883
theorem B9730327 : Blo 1707054 9730327 := bstep (se 1 (by rfl) ⟨7297745, by rfl⟩ : syracuseStep 9730327 = 14595491) B14595491
theorem B1947935 : Blo 1707054 1947935 := bstep (se 1 (by rfl) ⟨1460951, by rfl⟩ : syracuseStep 1947935 = 2921903) B2921903
theorem B2562395 : Blo 1707054 2562395 := bstep (se 1 (by rfl) ⟨1921796, by rfl⟩ : syracuseStep 2562395 = 3843593) B3843593
theorem B4864367 : Blo 1707054 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B2161019 : Blo 1707054 2161019 := bstep (se 1 (by rfl) ⟨1620764, by rfl⟩ : syracuseStep 2161019 = 3241529) B3241529
theorem B29170205 : Blo 1707054 29170205 := bstep (se 3 (by rfl) ⟨5469413, by rfl⟩ : syracuseStep 29170205 = 10938827) B10938827
theorem B5192255 : Blo 1707054 5192255 := bstep (se 1 (by rfl) ⟨3894191, by rfl⟩ : syracuseStep 5192255 = 7788383) B7788383
theorem B2562623 : Blo 1707054 2562623 := bstep (se 1 (by rfl) ⟨1921967, by rfl⟩ : syracuseStep 2562623 = 3843935) B3843935
theorem B7297609 : Blo 1707054 7297609 := bstep (se 2 (by rfl) ⟨2736603, by rfl⟩ : syracuseStep 7297609 = 5473207) B5473207
theorem B2882155 : Blo 1707054 2882155 := bstep (se 1 (by rfl) ⟨2161616, by rfl⟩ : syracuseStep 2882155 = 4323233) B4323233
theorem B4618927 : Blo 1707054 4618927 := bstep (se 1 (by rfl) ⟨3464195, by rfl⟩ : syracuseStep 4618927 = 6928391) B6928391
theorem B2562743 : Blo 1707054 2562743 := bstep (se 1 (by rfl) ⟨1922057, by rfl⟩ : syracuseStep 2562743 = 3844115) B3844115
theorem B2431711 : Blo 1707054 2431711 := bstep (se 1 (by rfl) ⟨1823783, by rfl⟩ : syracuseStep 2431711 = 3647567) B3647567
theorem B4324063 : Blo 1707054 4324063 := bstep (se 1 (by rfl) ⟨3243047, by rfl⟩ : syracuseStep 4324063 = 6486095) B6486095
theorem B4324175 : Blo 1707054 4324175 := bstep (se 1 (by rfl) ⟨3243131, by rfl⟩ : syracuseStep 4324175 = 6486263) B6486263
theorem B3840911 : Blo 1707054 3840911 := bstep (se 1 (by rfl) ⟨2880683, by rfl⟩ : syracuseStep 3840911 = 5761367) B5761367
theorem B20781967 : Blo 1707054 20781967 := bstep (se 1 (by rfl) ⟨15586475, by rfl⟩ : syracuseStep 20781967 = 31172951) B31172951
theorem B2595739 : Blo 1707054 2595739 := bstep (se 1 (by rfl) ⟨1946804, by rfl⟩ : syracuseStep 2595739 = 3893609) B3893609
theorem B2882459 : Blo 1707054 2882459 := bstep (se 1 (by rfl) ⟨2161844, by rfl⟩ : syracuseStep 2882459 = 4323689) B4323689
theorem B2562971 : Blo 1707054 2562971 := bstep (se 1 (by rfl) ⟨1922228, by rfl⟩ : syracuseStep 2562971 = 3844457) B3844457
theorem B17767355 : Blo 1707054 17767355 := bstep (se 1 (by rfl) ⟨13325516, by rfl⟩ : syracuseStep 17767355 = 26651033) B26651033
theorem B32816177 : Blo 1707054 32816177 := bstep (se 2 (by rfl) ⟨12306066, by rfl⟩ : syracuseStep 32816177 = 24612133) B24612133
theorem B12975227 : Blo 1707054 12975227 := bstep (se 1 (by rfl) ⟨9731420, by rfl⟩ : syracuseStep 12975227 = 19462841) B19462841
theorem B128138381 : Blo 1707054 128138381 := bstep (se 3 (by rfl) ⟨24025946, by rfl⟩ : syracuseStep 128138381 = 48051893) B48051893
theorem B2464987 : Blo 1707054 2464987 := bstep (se 1 (by rfl) ⟨1848740, by rfl⟩ : syracuseStep 2464987 = 3697481) B3697481
theorem B2563367 : Blo 1707054 2563367 := bstep (se 1 (by rfl) ⟨1922525, by rfl⟩ : syracuseStep 2563367 = 3845051) B3845051
theorem B5766497 : Blo 1707054 5766497 := bstep (se 2 (by rfl) ⟨2162436, by rfl⟩ : syracuseStep 5766497 = 4324873) B4324873
theorem B2563451 : Blo 1707054 2563451 := bstep (se 1 (by rfl) ⟨1922588, by rfl⟩ : syracuseStep 2563451 = 3845177) B3845177
theorem B4103561 : Blo 1707054 4103561 := bstep (se 2 (by rfl) ⟨1538835, by rfl⟩ : syracuseStep 4103561 = 3077671) B3077671
theorem B50609609 : Blo 1707054 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B4324823 : Blo 1707054 4324823 := bstep (se 1 (by rfl) ⟨3243617, by rfl⟩ : syracuseStep 4324823 = 6487235) B6487235
theorem B8437241 : Blo 1707054 8437241 := bstep (se 2 (by rfl) ⟨3163965, by rfl⟩ : syracuseStep 8437241 = 6327931) B6327931
theorem B2563577 : Blo 1707054 2563577 := bstep (se 2 (by rfl) ⟨961341, by rfl⟩ : syracuseStep 2563577 = 1922683) B1922683
theorem B3841631 : Blo 1707054 3841631 := bstep (se 1 (by rfl) ⟨2881223, by rfl⟩ : syracuseStep 3841631 = 5762447) B5762447
theorem B8650475 : Blo 1707054 8650475 := bstep (se 1 (by rfl) ⟨6487856, by rfl⟩ : syracuseStep 8650475 = 12975713) B12975713
theorem B4103983 : Blo 1707054 4103983 := bstep (se 1 (by rfl) ⟨3077987, by rfl⟩ : syracuseStep 4103983 = 6155975) B6155975
theorem B3841847 : Blo 1707054 3841847 := bstep (se 1 (by rfl) ⟨2881385, by rfl⟩ : syracuseStep 3841847 = 5762771) B5762771
theorem B4325177 : Blo 1707054 4325177 := bstep (se 2 (by rfl) ⟨1621941, by rfl⟩ : syracuseStep 4325177 = 3243883) B3243883
theorem B2162639 : Blo 1707054 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B27697211 : Blo 1707054 27697211 := bstep (se 1 (by rfl) ⟨20772908, by rfl⟩ : syracuseStep 27697211 = 41545817) B41545817
theorem B5767307 : Blo 1707054 5767307 := bstep (se 1 (by rfl) ⟨4325480, by rfl⟩ : syracuseStep 5767307 = 8650961) B8650961
theorem B43761869 : Blo 1707054 43761869 := bstep (se 3 (by rfl) ⟨8205350, by rfl⟩ : syracuseStep 43761869 = 16410701) B16410701
theorem B2736347 : Blo 1707054 2736347 := bstep (se 1 (by rfl) ⟨2052260, by rfl⟩ : syracuseStep 2736347 = 4104521) B4104521
theorem B3842279 : Blo 1707054 3842279 := bstep (se 1 (by rfl) ⟨2881709, by rfl⟩ : syracuseStep 3842279 = 5763419) B5763419
theorem B4325663 : Blo 1707054 4325663 := bstep (se 1 (by rfl) ⟨3244247, by rfl⟩ : syracuseStep 4325663 = 6488495) B6488495
theorem B5767631 : Blo 1707054 5767631 := bstep (se 1 (by rfl) ⟨4325723, by rfl⟩ : syracuseStep 5767631 = 8651447) B8651447
theorem B140206625 : Blo 1707054 140206625 := bstep (se 2 (by rfl) ⟨52577484, by rfl⟩ : syracuseStep 140206625 = 105154969) B105154969
theorem B5194493 : Blo 1707054 5194493 := bstep (se 3 (by rfl) ⟨973967, by rfl⟩ : syracuseStep 5194493 = 1947935) B1947935
theorem B8643347 : Blo 1707054 8643347 := bstep (se 1 (by rfl) ⟨6482510, by rfl⟩ : syracuseStep 8643347 = 12965021) B12965021
theorem B5767955 : Blo 1707054 5767955 := bstep (se 1 (by rfl) ⟨4325966, by rfl⟩ : syracuseStep 5767955 = 8651933) B8651933
theorem B2736937 : Blo 1707054 2736937 := bstep (se 2 (by rfl) ⟨1026351, by rfl⟩ : syracuseStep 2736937 = 2052703) B2052703
theorem B3842873 : Blo 1707054 3842873 := bstep (se 2 (by rfl) ⟨1441077, by rfl⟩ : syracuseStep 3842873 = 2882155) B2882155
theorem B3842927 : Blo 1707054 3842927 := bstep (se 1 (by rfl) ⟨2882195, by rfl⟩ : syracuseStep 3842927 = 5764391) B5764391
theorem B24634277 : Blo 1707054 24634277 := bstep (se 4 (by rfl) ⟨2309463, by rfl⟩ : syracuseStep 24634277 = 4618927) B4618927
theorem B12305465 : Blo 1707054 12305465 := bstep (se 2 (by rfl) ⟨4614549, by rfl⟩ : syracuseStep 12305465 = 9229099) B9229099
theorem B5842043 : Blo 1707054 5842043 := bstep (se 1 (by rfl) ⟨4381532, by rfl⟩ : syracuseStep 5842043 = 8763065) B8763065
theorem B10388695 : Blo 1707054 10388695 := bstep (se 1 (by rfl) ⟨7791521, by rfl⟩ : syracuseStep 10388695 = 15583043) B15583043
theorem B16418051 : Blo 1707054 16418051 := bstep (se 1 (by rfl) ⟨12313538, by rfl⟩ : syracuseStep 16418051 = 24627077) B24627077
theorem B98493731 : Blo 1707054 98493731 := bstep (se 1 (by rfl) ⟨73870298, by rfl⟩ : syracuseStep 98493731 = 147740597) B147740597
theorem B3646891 : Blo 1707054 3646891 := bstep (se 1 (by rfl) ⟨2735168, by rfl⟩ : syracuseStep 3646891 = 5470337) B5470337
theorem B3843503 : Blo 1707054 3843503 := bstep (se 1 (by rfl) ⟨2882627, by rfl⟩ : syracuseStep 3843503 = 5765255) B5765255
theorem B5473811 : Blo 1707054 5473811 := bstep (se 1 (by rfl) ⟨4105358, by rfl⟩ : syracuseStep 5473811 = 8210717) B8210717
theorem B3286649 : Blo 1707054 3286649 := bstep (se 2 (by rfl) ⟨1232493, by rfl⟩ : syracuseStep 3286649 = 2464987) B2464987
theorem B39454573 : Blo 1707054 39454573 := bstep (se 3 (by rfl) ⟨7397732, by rfl⟩ : syracuseStep 39454573 = 14795465) B14795465
theorem B3844331 : Blo 1707054 3844331 := bstep (se 1 (by rfl) ⟨2883248, by rfl⟩ : syracuseStep 3844331 = 5766497) B5766497
theorem B5925563 : Blo 1707054 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B1707055 : Blo 1707054 1707055 := bstep (se 1 (by rfl) ⟨1280291, by rfl⟩ : syracuseStep 1707055 = 2560583) B2560583
theorem B1707079 : Blo 1707054 1707079 := bstep (se 1 (by rfl) ⟨1280309, by rfl⟩ : syracuseStep 1707079 = 2560619) B2560619
theorem B1707231 : Blo 1707054 1707231 := bstep (se 1 (by rfl) ⟨1280423, by rfl⟩ : syracuseStep 1707231 = 2560847) B2560847
theorem B36916469 : Blo 1707054 36916469 := bstep (se 5 (by rfl) ⟨1730459, by rfl⟩ : syracuseStep 36916469 = 3460919) B3460919
theorem B84192547 : Blo 1707054 84192547 := bstep (se 1 (by rfl) ⟨63144410, by rfl⟩ : syracuseStep 84192547 = 126288821) B126288821
theorem B1920487 : Blo 1707054 1920487 := bstep (se 1 (by rfl) ⟨1440365, by rfl⟩ : syracuseStep 1920487 = 2880731) B2880731
theorem B1707495 : Blo 1707054 1707495 := bstep (se 1 (by rfl) ⟨1280621, by rfl⟩ : syracuseStep 1707495 = 2561243) B2561243
theorem B5762555 : Blo 1707054 5762555 := bstep (se 1 (by rfl) ⟨4321916, by rfl⟩ : syracuseStep 5762555 = 8643833) B8643833
theorem B1707611 : Blo 1707054 1707611 := bstep (se 1 (by rfl) ⟨1280708, by rfl⟩ : syracuseStep 1707611 = 2561417) B2561417
theorem B4861565 : Blo 1707054 4861565 := bstep (se 3 (by rfl) ⟨911543, by rfl⟩ : syracuseStep 4861565 = 1823087) B1823087
theorem B5762717 : Blo 1707054 5762717 := bstep (se 3 (by rfl) ⟨1080509, by rfl⟩ : syracuseStep 5762717 = 2161019) B2161019
theorem B21884579 : Blo 1707054 21884579 := bstep (se 1 (by rfl) ⟨16413434, by rfl⟩ : syracuseStep 21884579 = 32826869) B32826869
theorem B1707847 : Blo 1707054 1707847 := bstep (se 1 (by rfl) ⟨1280885, by rfl⟩ : syracuseStep 1707847 = 2561771) B2561771
theorem B27709289 : Blo 1707054 27709289 := bstep (se 2 (by rfl) ⟨10390983, by rfl⟩ : syracuseStep 27709289 = 20781967) B20781967
theorem B3460985 : Blo 1707054 3460985 := bstep (se 2 (by rfl) ⟨1297869, by rfl⟩ : syracuseStep 3460985 = 2595739) B2595739
theorem B29192075 : Blo 1707054 29192075 := bstep (se 1 (by rfl) ⟨21894056, by rfl⟩ : syracuseStep 29192075 = 43788113) B43788113
theorem B1920991 : Blo 1707054 1920991 := bstep (se 1 (by rfl) ⟨1440743, by rfl⟩ : syracuseStep 1920991 = 2881487) B2881487
theorem B1707999 : Blo 1707054 1707999 := bstep (se 1 (by rfl) ⟨1280999, by rfl⟩ : syracuseStep 1707999 = 2561999) B2561999
theorem B22499309 : Blo 1707054 22499309 := bstep (se 3 (by rfl) ⟨4218620, by rfl⟩ : syracuseStep 22499309 = 8437241) B8437241
theorem B83136617 : Blo 1707054 83136617 := bstep (se 2 (by rfl) ⟨31176231, by rfl⟩ : syracuseStep 83136617 = 62352463) B62352463
theorem B5763257 : Blo 1707054 5763257 := bstep (se 2 (by rfl) ⟨2161221, by rfl⟩ : syracuseStep 5763257 = 4322443) B4322443
theorem B1708263 : Blo 1707054 1708263 := bstep (se 1 (by rfl) ⟨1281197, by rfl⟩ : syracuseStep 1708263 = 2562395) B2562395
theorem B6156611 : Blo 1707054 6156611 := bstep (se 1 (by rfl) ⟨4617458, by rfl⟩ : syracuseStep 6156611 = 9234917) B9234917
theorem B3461503 : Blo 1707054 3461503 := bstep (se 1 (by rfl) ⟨2596127, by rfl⟩ : syracuseStep 3461503 = 5192255) B5192255
theorem B1708415 : Blo 1707054 1708415 := bstep (se 1 (by rfl) ⟨1281311, by rfl⟩ : syracuseStep 1708415 = 2562623) B2562623
theorem B1708495 : Blo 1707054 1708495 := bstep (se 1 (by rfl) ⟨1281371, by rfl⟩ : syracuseStep 1708495 = 2562743) B2562743
theorem B2560607 : Blo 1707054 2560607 := bstep (se 1 (by rfl) ⟨1920455, by rfl⟩ : syracuseStep 2560607 = 3840911) B3840911
theorem B4862567 : Blo 1707054 4862567 := bstep (se 1 (by rfl) ⟨3646925, by rfl⟩ : syracuseStep 4862567 = 7293851) B7293851
theorem B1921639 : Blo 1707054 1921639 := bstep (se 1 (by rfl) ⟨1441229, by rfl⟩ : syracuseStep 1921639 = 2882459) B2882459
theorem B1708647 : Blo 1707054 1708647 := bstep (se 1 (by rfl) ⟨1281485, by rfl⟩ : syracuseStep 1708647 = 2562971) B2562971
theorem B21877451 : Blo 1707054 21877451 := bstep (se 1 (by rfl) ⟨16408088, by rfl⟩ : syracuseStep 21877451 = 32816177) B32816177
theorem B5468953 : Blo 1707054 5468953 := bstep (se 2 (by rfl) ⟨2050857, by rfl⟩ : syracuseStep 5468953 = 4101715) B4101715
theorem B1708911 : Blo 1707054 1708911 := bstep (se 1 (by rfl) ⟨1281683, by rfl⟩ : syracuseStep 1708911 = 2563367) B2563367
theorem B39424913 : Blo 1707054 39424913 := bstep (se 2 (by rfl) ⟨14784342, by rfl⟩ : syracuseStep 39424913 = 29568685) B29568685
theorem B1708967 : Blo 1707054 1708967 := bstep (se 1 (by rfl) ⟨1281725, by rfl⟩ : syracuseStep 1708967 = 2563451) B2563451
theorem B33739739 : Blo 1707054 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B1709051 : Blo 1707054 1709051 := bstep (se 1 (by rfl) ⟨1281788, by rfl⟩ : syracuseStep 1709051 = 2563577) B2563577
theorem B2561087 : Blo 1707054 2561087 := bstep (se 1 (by rfl) ⟨1920815, by rfl⟩ : syracuseStep 2561087 = 3841631) B3841631
theorem B2561129 : Blo 1707054 2561129 := bstep (se 2 (by rfl) ⟨960423, by rfl⟩ : syracuseStep 2561129 = 1920847) B1920847
theorem B47379613 : Blo 1707054 47379613 := bstep (se 3 (by rfl) ⟨8883677, by rfl⟩ : syracuseStep 47379613 = 17767355) B17767355
theorem B2561231 : Blo 1707054 2561231 := bstep (se 1 (by rfl) ⟨1920923, by rfl⟩ : syracuseStep 2561231 = 3841847) B3841847
theorem B5469403 : Blo 1707054 5469403 := bstep (se 1 (by rfl) ⟨4102052, by rfl⟩ : syracuseStep 5469403 = 8204105) B8204105
theorem B11097431 : Blo 1707054 11097431 := bstep (se 1 (by rfl) ⟨8323073, by rfl⟩ : syracuseStep 11097431 = 16646147) B16646147
theorem B2880859 : Blo 1707054 2880859 := bstep (se 1 (by rfl) ⟨2160644, by rfl⟩ : syracuseStep 2880859 = 4321289) B4321289
theorem B2561435 : Blo 1707054 2561435 := bstep (se 1 (by rfl) ⟨1921076, by rfl⟩ : syracuseStep 2561435 = 3842153) B3842153
theorem B23377409 : Blo 1707054 23377409 := bstep (se 2 (by rfl) ⟨8766528, by rfl⟩ : syracuseStep 23377409 = 17533057) B17533057
theorem B2561657 : Blo 1707054 2561657 := bstep (se 2 (by rfl) ⟨960621, by rfl⟩ : syracuseStep 2561657 = 1921243) B1921243
theorem B2922151 : Blo 1707054 2922151 := bstep (se 1 (by rfl) ⟨2191613, by rfl⟩ : syracuseStep 2922151 = 4383227) B4383227
theorem B12973769 : Blo 1707054 12973769 := bstep (se 2 (by rfl) ⟨4865163, by rfl⟩ : syracuseStep 12973769 = 9730327) B9730327
theorem B2561759 : Blo 1707054 2561759 := bstep (se 1 (by rfl) ⟨1921319, by rfl⟩ : syracuseStep 2561759 = 3842639) B3842639
theorem B4929259 : Blo 1707054 4929259 := bstep (se 1 (by rfl) ⟨3696944, by rfl⟩ : syracuseStep 4929259 = 7393889) B7393889
theorem B2561855 : Blo 1707054 2561855 := bstep (se 1 (by rfl) ⟨1921391, by rfl⟩ : syracuseStep 2561855 = 3842783) B3842783
theorem B2430919 : Blo 1707054 2430919 := bstep (se 1 (by rfl) ⟨1823189, by rfl⟩ : syracuseStep 2430919 = 3646379) B3646379
theorem B33265637 : Blo 1707054 33265637 := bstep (se 4 (by rfl) ⟨3118653, by rfl⟩ : syracuseStep 33265637 = 6237307) B6237307
theorem B5470183 : Blo 1707054 5470183 := bstep (se 1 (by rfl) ⟨4102637, by rfl⟩ : syracuseStep 5470183 = 8205275) B8205275
theorem B2562023 : Blo 1707054 2562023 := bstep (se 1 (by rfl) ⟨1921517, by rfl⟩ : syracuseStep 2562023 = 3843035) B3843035
theorem B2562041 : Blo 1707054 2562041 := bstep (se 2 (by rfl) ⟨960765, by rfl⟩ : syracuseStep 2562041 = 1921531) B1921531
theorem B4864025 : Blo 1707054 4864025 := bstep (se 2 (by rfl) ⟨1824009, by rfl⟩ : syracuseStep 4864025 = 3648019) B3648019
theorem B2562143 : Blo 1707054 2562143 := bstep (se 1 (by rfl) ⟨1921607, by rfl⟩ : syracuseStep 2562143 = 3843215) B3843215
theorem B9730145 : Blo 1707054 9730145 := bstep (se 2 (by rfl) ⟨3648804, by rfl⟩ : syracuseStep 9730145 = 7297609) B7297609
theorem B2562203 : Blo 1707054 2562203 := bstep (se 1 (by rfl) ⟨1921652, by rfl⟩ : syracuseStep 2562203 = 3843305) B3843305
theorem B2562239 : Blo 1707054 2562239 := bstep (se 1 (by rfl) ⟨1921679, by rfl⟩ : syracuseStep 2562239 = 3843359) B3843359
theorem B4323527 : Blo 1707054 4323527 := bstep (se 1 (by rfl) ⟨3242645, by rfl⟩ : syracuseStep 4323527 = 6485291) B6485291
theorem B2562281 : Blo 1707054 2562281 := bstep (se 2 (by rfl) ⟨960855, by rfl⟩ : syracuseStep 2562281 = 1921711) B1921711
theorem B2849003 : Blo 1707054 2849003 := bstep (se 1 (by rfl) ⟨2136752, by rfl⟩ : syracuseStep 2849003 = 4273505) B4273505
theorem B5765363 : Blo 1707054 5765363 := bstep (se 1 (by rfl) ⟨4324022, by rfl⟩ : syracuseStep 5765363 = 8648045) B8648045
theorem B2881831 : Blo 1707054 2881831 := bstep (se 1 (by rfl) ⟨2161373, by rfl⟩ : syracuseStep 2881831 = 4322747) B4322747
theorem B3242281 : Blo 1707054 3242281 := bstep (se 2 (by rfl) ⟨1215855, by rfl⟩ : syracuseStep 3242281 = 2431711) B2431711
theorem B5765417 : Blo 1707054 5765417 := bstep (se 2 (by rfl) ⟨2162031, by rfl⟩ : syracuseStep 5765417 = 4324063) B4324063
theorem B2562587 : Blo 1707054 2562587 := bstep (se 1 (by rfl) ⟨1921940, by rfl⟩ : syracuseStep 2562587 = 3843881) B3843881
theorem B1849883 : Blo 1707054 1849883 := bstep (se 1 (by rfl) ⟨1387412, by rfl⟩ : syracuseStep 1849883 = 2774825) B2774825
theorem B2562665 : Blo 1707054 2562665 := bstep (se 2 (by rfl) ⟨960999, by rfl⟩ : syracuseStep 2562665 = 1921999) B1921999
theorem B2431625 : Blo 1707054 2431625 := bstep (se 2 (by rfl) ⟨911859, by rfl⟩ : syracuseStep 2431625 = 1823719) B1823719
theorem B7297883 : Blo 1707054 7297883 := bstep (se 1 (by rfl) ⟨5473412, by rfl⟩ : syracuseStep 7297883 = 10946825) B10946825
theorem B3242911 : Blo 1707054 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B7297951 : Blo 1707054 7297951 := bstep (se 1 (by rfl) ⟨5473463, by rfl⟩ : syracuseStep 7297951 = 10946927) B10946927
theorem B71048117 : Blo 1707054 71048117 := bstep (se 5 (by rfl) ⟨3330380, by rfl⟩ : syracuseStep 71048117 = 6660761) B6660761
theorem B4103137 : Blo 1707054 4103137 := bstep (se 2 (by rfl) ⟨1538676, by rfl⟩ : syracuseStep 4103137 = 3077353) B3077353
theorem B19446803 : Blo 1707054 19446803 := bstep (se 1 (by rfl) ⟨14585102, by rfl⟩ : syracuseStep 19446803 = 29170205) B29170205
theorem B2432047 : Blo 1707054 2432047 := bstep (se 1 (by rfl) ⟨1824035, by rfl⟩ : syracuseStep 2432047 = 3648071) B3648071
theorem B7789625 : Blo 1707054 7789625 := bstep (se 2 (by rfl) ⟨2921109, by rfl⟩ : syracuseStep 7789625 = 5842219) B5842219
theorem B2563193 : Blo 1707054 2563193 := bstep (se 2 (by rfl) ⟨961197, by rfl⟩ : syracuseStep 2563193 = 1922395) B1922395
theorem B3464375 : Blo 1707054 3464375 := bstep (se 1 (by rfl) ⟨2598281, by rfl⟩ : syracuseStep 3464375 = 5196563) B5196563
theorem B2882783 : Blo 1707054 2882783 := bstep (se 1 (by rfl) ⟨2162087, by rfl⟩ : syracuseStep 2882783 = 4324175) B4324175
theorem B2563295 : Blo 1707054 2563295 := bstep (se 1 (by rfl) ⟨1922471, by rfl⟩ : syracuseStep 2563295 = 3844943) B3844943
theorem B3841289 : Blo 1707054 3841289 := bstep (se 2 (by rfl) ⟨1440483, by rfl⟩ : syracuseStep 3841289 = 2880967) B2880967
theorem B2563337 : Blo 1707054 2563337 := bstep (se 2 (by rfl) ⟨961251, by rfl⟩ : syracuseStep 2563337 = 1922503) B1922503
theorem B2563439 : Blo 1707054 2563439 := bstep (se 1 (by rfl) ⟨1922579, by rfl⟩ : syracuseStep 2563439 = 3845159) B3845159
theorem B8650151 : Blo 1707054 8650151 := bstep (se 1 (by rfl) ⟨6487613, by rfl⟩ : syracuseStep 8650151 = 12975227) B12975227
theorem B85425587 : Blo 1707054 85425587 := bstep (se 1 (by rfl) ⟨64069190, by rfl⟩ : syracuseStep 85425587 = 128138381) B128138381
theorem B2563559 : Blo 1707054 2563559 := bstep (se 1 (by rfl) ⟨1922669, by rfl⟩ : syracuseStep 2563559 = 3845339) B3845339
theorem B2735707 : Blo 1707054 2735707 := bstep (se 1 (by rfl) ⟨2051780, by rfl⟩ : syracuseStep 2735707 = 4103561) B4103561
theorem B2883215 : Blo 1707054 2883215 := bstep (se 1 (by rfl) ⟨2162411, by rfl⟩ : syracuseStep 2883215 = 4324823) B4324823
theorem B5471977 : Blo 1707054 5471977 := bstep (se 2 (by rfl) ⟨2051991, by rfl⟩ : syracuseStep 5471977 = 4103983) B4103983
theorem B8642375 : Blo 1707054 8642375 := bstep (se 1 (by rfl) ⟨6481781, by rfl⟩ : syracuseStep 8642375 = 12963563) B12963563
theorem B5766983 : Blo 1707054 5766983 := bstep (se 1 (by rfl) ⟨4325237, by rfl⟩ : syracuseStep 5766983 = 8650475) B8650475
theorem B2883451 : Blo 1707054 2883451 := bstep (se 1 (by rfl) ⟨2162588, by rfl⟩ : syracuseStep 2883451 = 4325177) B4325177
theorem B5767037 : Blo 1707054 5767037 := bstep (se 3 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 5767037 = 2162639) B2162639
theorem B18464807 : Blo 1707054 18464807 := bstep (se 1 (by rfl) ⟨13848605, by rfl⟩ : syracuseStep 18464807 = 27697211) B27697211
theorem B3842171 : Blo 1707054 3842171 := bstep (se 1 (by rfl) ⟨2881628, by rfl⟩ : syracuseStep 3842171 = 5763257) B5763257
theorem B2883775 : Blo 1707054 2883775 := bstep (se 1 (by rfl) ⟨2162831, by rfl⟩ : syracuseStep 2883775 = 4325663) B4325663
theorem B4104407 : Blo 1707054 4104407 := bstep (se 1 (by rfl) ⟨3078305, by rfl⟩ : syracuseStep 4104407 = 6156611) B6156611
theorem B93471083 : Blo 1707054 93471083 := bstep (se 1 (by rfl) ⟨70103312, by rfl⟩ : syracuseStep 93471083 = 140206625) B140206625
theorem B3842441 : Blo 1707054 3842441 := bstep (se 2 (by rfl) ⟨1440915, by rfl⟩ : syracuseStep 3842441 = 2881831) B2881831
theorem B10945367 : Blo 1707054 10945367 := bstep (se 1 (by rfl) ⟨8209025, by rfl⟩ : syracuseStep 10945367 = 16418051) B16418051
theorem B7398287 : Blo 1707054 7398287 := bstep (se 1 (by rfl) ⟨5548715, by rfl⟩ : syracuseStep 7398287 = 11097431) B11097431
theorem B7291937 : Blo 1707054 7291937 := bstep (se 2 (by rfl) ⟨2734476, by rfl⟩ : syracuseStep 7291937 = 5468953) B5468953
theorem B22177091 : Blo 1707054 22177091 := bstep (se 1 (by rfl) ⟨16632818, by rfl⟩ : syracuseStep 22177091 = 33265637) B33265637
theorem B3843575 : Blo 1707054 3843575 := bstep (se 1 (by rfl) ⟨2882681, by rfl⟩ : syracuseStep 3843575 = 5765363) B5765363
theorem B3843611 : Blo 1707054 3843611 := bstep (se 1 (by rfl) ⟨2882708, by rfl⟩ : syracuseStep 3843611 = 5765417) B5765417
theorem B7292537 : Blo 1707054 7292537 := bstep (se 2 (by rfl) ⟨2734701, by rfl⟩ : syracuseStep 7292537 = 5469403) B5469403
theorem B112256729 : Blo 1707054 112256729 := bstep (se 2 (by rfl) ⟨42096273, by rfl⟩ : syracuseStep 112256729 = 84192547) B84192547
theorem B3950375 : Blo 1707054 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B3647609 : Blo 1707054 3647609 := bstep (se 2 (by rfl) ⟨1367853, by rfl⟩ : syracuseStep 3647609 = 2735707) B2735707
theorem B24610979 : Blo 1707054 24610979 := bstep (se 1 (by rfl) ⟨18458234, by rfl⟩ : syracuseStep 24610979 = 36916469) B36916469
theorem B6572345 : Blo 1707054 6572345 := bstep (se 2 (by rfl) ⟨2464629, by rfl⟩ : syracuseStep 6572345 = 4929259) B4929259
theorem B3844601 : Blo 1707054 3844601 := bstep (se 2 (by rfl) ⟨1441725, by rfl⟩ : syracuseStep 3844601 = 2883451) B2883451
theorem B5761583 : Blo 1707054 5761583 := bstep (se 1 (by rfl) ⟨4321187, by rfl⟩ : syracuseStep 5761583 = 8642375) B8642375
theorem B3844655 : Blo 1707054 3844655 := bstep (se 1 (by rfl) ⟨2883491, by rfl⟩ : syracuseStep 3844655 = 5766983) B5766983
theorem B3844691 : Blo 1707054 3844691 := bstep (se 1 (by rfl) ⟨2883518, by rfl⟩ : syracuseStep 3844691 = 5767037) B5767037
theorem B7293577 : Blo 1707054 7293577 := bstep (se 2 (by rfl) ⟨2735091, by rfl⟩ : syracuseStep 7293577 = 5470183) B5470183
theorem B3844871 : Blo 1707054 3844871 := bstep (se 1 (by rfl) ⟨2883653, by rfl⟩ : syracuseStep 3844871 = 5767307) B5767307
theorem B29174579 : Blo 1707054 29174579 := bstep (se 1 (by rfl) ⟨21880934, by rfl⟩ : syracuseStep 29174579 = 43761869) B43761869
theorem B3845087 : Blo 1707054 3845087 := bstep (se 1 (by rfl) ⟨2883815, by rfl⟩ : syracuseStep 3845087 = 5767631) B5767631
theorem B1707071 : Blo 1707054 1707071 := bstep (se 1 (by rfl) ⟨1280303, by rfl⟩ : syracuseStep 1707071 = 2560607) B2560607
theorem B14584967 : Blo 1707054 14584967 := bstep (se 1 (by rfl) ⟨10938725, by rfl⟩ : syracuseStep 14584967 = 21877451) B21877451
theorem B4615337 : Blo 1707054 4615337 := bstep (se 2 (by rfl) ⟨1730751, by rfl⟩ : syracuseStep 4615337 = 3461503) B3461503
theorem B5762231 : Blo 1707054 5762231 := bstep (se 1 (by rfl) ⟨4321673, by rfl⟩ : syracuseStep 5762231 = 8643347) B8643347
theorem B3845303 : Blo 1707054 3845303 := bstep (se 1 (by rfl) ⟨2883977, by rfl⟩ : syracuseStep 3845303 = 5767955) B5767955
theorem B26283275 : Blo 1707054 26283275 := bstep (se 1 (by rfl) ⟨19712456, by rfl⟩ : syracuseStep 26283275 = 39424913) B39424913
theorem B8203643 : Blo 1707054 8203643 := bstep (se 1 (by rfl) ⟨6152732, by rfl⟩ : syracuseStep 8203643 = 12305465) B12305465
theorem B1707391 : Blo 1707054 1707391 := bstep (se 1 (by rfl) ⟨1280543, by rfl⟩ : syracuseStep 1707391 = 2561087) B2561087
theorem B1707419 : Blo 1707054 1707419 := bstep (se 1 (by rfl) ⟨1280564, by rfl⟩ : syracuseStep 1707419 = 2561129) B2561129
theorem B3894695 : Blo 1707054 3894695 := bstep (se 1 (by rfl) ⟨2921021, by rfl⟩ : syracuseStep 3894695 = 5842043) B5842043
theorem B1707487 : Blo 1707054 1707487 := bstep (se 1 (by rfl) ⟨1280615, by rfl⟩ : syracuseStep 1707487 = 2561231) B2561231
theorem B65662487 : Blo 1707054 65662487 := bstep (se 1 (by rfl) ⟨49246865, by rfl⟩ : syracuseStep 65662487 = 98493731) B98493731
theorem B1707623 : Blo 1707054 1707623 := bstep (se 1 (by rfl) ⟨1280717, by rfl⟩ : syracuseStep 1707623 = 2561435) B2561435
theorem B15584939 : Blo 1707054 15584939 := bstep (se 1 (by rfl) ⟨11688704, by rfl⟩ : syracuseStep 15584939 = 23377409) B23377409
theorem B3649207 : Blo 1707054 3649207 := bstep (se 1 (by rfl) ⟨2736905, by rfl⟩ : syracuseStep 3649207 = 5473811) B5473811
theorem B3649249 : Blo 1707054 3649249 := bstep (se 2 (by rfl) ⟨1368468, by rfl⟩ : syracuseStep 3649249 = 2736937) B2736937
theorem B1707771 : Blo 1707054 1707771 := bstep (se 1 (by rfl) ⟨1280828, by rfl⟩ : syracuseStep 1707771 = 2561657) B2561657
theorem B2191099 : Blo 1707054 2191099 := bstep (se 1 (by rfl) ⟨1643324, by rfl⟩ : syracuseStep 2191099 = 3286649) B3286649
theorem B1707839 : Blo 1707054 1707839 := bstep (se 1 (by rfl) ⟨1280879, by rfl⟩ : syracuseStep 1707839 = 2561759) B2561759
theorem B1707903 : Blo 1707054 1707903 := bstep (se 1 (by rfl) ⟨1280927, by rfl⟩ : syracuseStep 1707903 = 2561855) B2561855
theorem B1708015 : Blo 1707054 1708015 := bstep (se 1 (by rfl) ⟨1281011, by rfl⟩ : syracuseStep 1708015 = 2562023) B2562023
theorem B1708027 : Blo 1707054 1708027 := bstep (se 1 (by rfl) ⟨1281020, by rfl⟩ : syracuseStep 1708027 = 2562041) B2562041
theorem B1708095 : Blo 1707054 1708095 := bstep (se 1 (by rfl) ⟨1281071, by rfl⟩ : syracuseStep 1708095 = 2562143) B2562143
theorem B1708135 : Blo 1707054 1708135 := bstep (se 1 (by rfl) ⟨1281101, by rfl⟩ : syracuseStep 1708135 = 2562203) B2562203
theorem B1708159 : Blo 1707054 1708159 := bstep (se 1 (by rfl) ⟨1281119, by rfl⟩ : syracuseStep 1708159 = 2562239) B2562239
theorem B1708187 : Blo 1707054 1708187 := bstep (se 1 (by rfl) ⟨1281140, by rfl⟩ : syracuseStep 1708187 = 2562281) B2562281
theorem B63172817 : Blo 1707054 63172817 := bstep (se 2 (by rfl) ⟨23689806, by rfl⟩ : syracuseStep 63172817 = 47379613) B47379613
theorem B1708391 : Blo 1707054 1708391 := bstep (se 1 (by rfl) ⟨1281293, by rfl⟩ : syracuseStep 1708391 = 2562587) B2562587
theorem B6484333 : Blo 1707054 6484333 := bstep (se 3 (by rfl) ⟨1215812, by rfl⟩ : syracuseStep 6484333 = 2431625) B2431625
theorem B1708443 : Blo 1707054 1708443 := bstep (se 1 (by rfl) ⟨1281332, by rfl⟩ : syracuseStep 1708443 = 2562665) B2562665
theorem B4862521 : Blo 1707054 4862521 := bstep (se 2 (by rfl) ⟨1823445, by rfl⟩ : syracuseStep 4862521 = 3646891) B3646891
theorem B2560649 : Blo 1707054 2560649 := bstep (se 2 (by rfl) ⟨960243, by rfl⟩ : syracuseStep 2560649 = 1920487) B1920487
theorem B12964535 : Blo 1707054 12964535 := bstep (se 1 (by rfl) ⟨9723401, by rfl⟩ : syracuseStep 12964535 = 19446803) B19446803
theorem B1708795 : Blo 1707054 1708795 := bstep (se 1 (by rfl) ⟨1281596, by rfl⟩ : syracuseStep 1708795 = 2563193) B2563193
theorem B1921855 : Blo 1707054 1921855 := bstep (se 1 (by rfl) ⟨1441391, by rfl⟩ : syracuseStep 1921855 = 2882783) B2882783
theorem B1708863 : Blo 1707054 1708863 := bstep (se 1 (by rfl) ⟨1281647, by rfl⟩ : syracuseStep 1708863 = 2563295) B2563295
theorem B2560859 : Blo 1707054 2560859 := bstep (se 1 (by rfl) ⟨1920644, by rfl⟩ : syracuseStep 2560859 = 3841289) B3841289
theorem B1708891 : Blo 1707054 1708891 := bstep (se 1 (by rfl) ⟨1281668, by rfl⟩ : syracuseStep 1708891 = 2563337) B2563337
theorem B3896201 : Blo 1707054 3896201 := bstep (se 2 (by rfl) ⟨1461075, by rfl⟩ : syracuseStep 3896201 = 2922151) B2922151
theorem B1708959 : Blo 1707054 1708959 := bstep (se 1 (by rfl) ⟨1281719, by rfl⟩ : syracuseStep 1708959 = 2563439) B2563439
theorem B7295969 : Blo 1707054 7295969 := bstep (se 2 (by rfl) ⟨2735988, by rfl⟩ : syracuseStep 7295969 = 5471977) B5471977
theorem B1709039 : Blo 1707054 1709039 := bstep (se 1 (by rfl) ⟨1281779, by rfl⟩ : syracuseStep 1709039 = 2563559) B2563559
theorem B3241043 : Blo 1707054 3241043 := bstep (se 1 (by rfl) ⟨2430782, by rfl⟩ : syracuseStep 3241043 = 4861565) B4861565
theorem B1922143 : Blo 1707054 1922143 := bstep (se 1 (by rfl) ⟨1441607, by rfl⟩ : syracuseStep 1922143 = 2883215) B2883215
theorem B52606097 : Blo 1707054 52606097 := bstep (se 2 (by rfl) ⟨19727286, by rfl⟩ : syracuseStep 52606097 = 39454573) B39454573
theorem B2307323 : Blo 1707054 2307323 := bstep (se 1 (by rfl) ⟨1730492, by rfl⟩ : syracuseStep 2307323 = 3460985) B3460985
theorem B19461383 : Blo 1707054 19461383 := bstep (se 1 (by rfl) ⟨14596037, by rfl⟩ : syracuseStep 19461383 = 29192075) B29192075
theorem B3241225 : Blo 1707054 3241225 := bstep (se 2 (by rfl) ⟨1215459, by rfl⟩ : syracuseStep 3241225 = 2430919) B2430919
theorem B2561321 : Blo 1707054 2561321 := bstep (se 2 (by rfl) ⟨960495, by rfl⟩ : syracuseStep 2561321 = 1920991) B1920991
theorem B55424411 : Blo 1707054 55424411 := bstep (se 1 (by rfl) ⟨41568308, by rfl⟩ : syracuseStep 55424411 = 83136617) B83136617
theorem B2561519 : Blo 1707054 2561519 := bstep (se 1 (by rfl) ⟨1921139, by rfl⟩ : syracuseStep 2561519 = 3842279) B3842279
theorem B19732085 : Blo 1707054 19732085 := bstep (se 5 (by rfl) ⟨924941, by rfl⟩ : syracuseStep 19732085 = 1849883) B1849883
theorem B4323041 : Blo 1707054 4323041 := bstep (se 2 (by rfl) ⟨1621140, by rfl⟩ : syracuseStep 4323041 = 3242281) B3242281
theorem B3241711 : Blo 1707054 3241711 := bstep (se 1 (by rfl) ⟨2431283, by rfl⟩ : syracuseStep 3241711 = 4862567) B4862567
theorem B9238333 : Blo 1707054 9238333 := bstep (se 3 (by rfl) ⟨1732187, by rfl⟩ : syracuseStep 9238333 = 3464375) B3464375
theorem B3462995 : Blo 1707054 3462995 := bstep (se 1 (by rfl) ⟨2597246, by rfl⟩ : syracuseStep 3462995 = 5194493) B5194493
theorem B2561915 : Blo 1707054 2561915 := bstep (se 1 (by rfl) ⟨1921436, by rfl⟩ : syracuseStep 2561915 = 3842873) B3842873
theorem B2561951 : Blo 1707054 2561951 := bstep (se 1 (by rfl) ⟨1921463, by rfl⟩ : syracuseStep 2561951 = 3842927) B3842927
theorem B16422851 : Blo 1707054 16422851 := bstep (se 1 (by rfl) ⟨12317138, by rfl⟩ : syracuseStep 16422851 = 24634277) B24634277
theorem B22493159 : Blo 1707054 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B2562185 : Blo 1707054 2562185 := bstep (se 2 (by rfl) ⟨960819, by rfl⟩ : syracuseStep 2562185 = 1921639) B1921639
theorem B2562335 : Blo 1707054 2562335 := bstep (se 1 (by rfl) ⟨1921751, by rfl⟩ : syracuseStep 2562335 = 3843503) B3843503
theorem B8649179 : Blo 1707054 8649179 := bstep (se 1 (by rfl) ⟨6486884, by rfl⟩ : syracuseStep 8649179 = 12973769) B12973769
theorem B4323881 : Blo 1707054 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B9730601 : Blo 1707054 9730601 := bstep (se 2 (by rfl) ⟨3648975, by rfl⟩ : syracuseStep 9730601 = 7297951) B7297951
theorem B5470849 : Blo 1707054 5470849 := bstep (se 2 (by rfl) ⟨2051568, by rfl⟩ : syracuseStep 5470849 = 4103137) B4103137
theorem B3242683 : Blo 1707054 3242683 := bstep (se 1 (by rfl) ⟨2432012, by rfl⟩ : syracuseStep 3242683 = 4864025) B4864025
theorem B3242729 : Blo 1707054 3242729 := bstep (se 2 (by rfl) ⟨1216023, by rfl⟩ : syracuseStep 3242729 = 2432047) B2432047
theorem B6486763 : Blo 1707054 6486763 := bstep (se 1 (by rfl) ⟨4865072, by rfl⟩ : syracuseStep 6486763 = 9730145) B9730145
theorem B2882351 : Blo 1707054 2882351 := bstep (se 1 (by rfl) ⟨2161763, by rfl⟩ : syracuseStep 2882351 = 4323527) B4323527
theorem B1899335 : Blo 1707054 1899335 := bstep (se 1 (by rfl) ⟨1424501, by rfl⟩ : syracuseStep 1899335 = 2849003) B2849003
theorem B2562887 : Blo 1707054 2562887 := bstep (se 1 (by rfl) ⟨1922165, by rfl⟩ : syracuseStep 2562887 = 3844331) B3844331
theorem B13851593 : Blo 1707054 13851593 := bstep (se 2 (by rfl) ⟨5194347, by rfl⟩ : syracuseStep 13851593 = 10388695) B10388695
theorem B3841145 : Blo 1707054 3841145 := bstep (se 2 (by rfl) ⟨1440429, by rfl⟩ : syracuseStep 3841145 = 2880859) B2880859
theorem B4865255 : Blo 1707054 4865255 := bstep (se 1 (by rfl) ⟨3648941, by rfl⟩ : syracuseStep 4865255 = 7297883) B7297883
theorem B47365411 : Blo 1707054 47365411 := bstep (se 1 (by rfl) ⟨35524058, by rfl⟩ : syracuseStep 47365411 = 71048117) B71048117
theorem B5193083 : Blo 1707054 5193083 := bstep (se 1 (by rfl) ⟨3894812, by rfl⟩ : syracuseStep 5193083 = 7789625) B7789625
theorem B5766767 : Blo 1707054 5766767 := bstep (se 1 (by rfl) ⟨4325075, by rfl⟩ : syracuseStep 5766767 = 8650151) B8650151
theorem B29187701 : Blo 1707054 29187701 := bstep (se 5 (by rfl) ⟨1368173, by rfl⟩ : syracuseStep 29187701 = 2736347) B2736347
theorem B56950391 : Blo 1707054 56950391 := bstep (se 1 (by rfl) ⟨42712793, by rfl⟩ : syracuseStep 56950391 = 85425587) B85425587
theorem B3841703 : Blo 1707054 3841703 := bstep (se 1 (by rfl) ⟨2881277, by rfl⟩ : syracuseStep 3841703 = 5762555) B5762555
theorem B3841811 : Blo 1707054 3841811 := bstep (se 1 (by rfl) ⟨2881358, by rfl⟩ : syracuseStep 3841811 = 5762717) B5762717
theorem B14589719 : Blo 1707054 14589719 := bstep (se 1 (by rfl) ⟨10942289, by rfl⟩ : syracuseStep 14589719 = 21884579) B21884579
theorem B18472859 : Blo 1707054 18472859 := bstep (se 1 (by rfl) ⟨13854644, by rfl⟩ : syracuseStep 18472859 = 27709289) B27709289
theorem B59998157 : Blo 1707054 59998157 := bstep (se 3 (by rfl) ⟨11249654, by rfl⟩ : syracuseStep 59998157 = 22499309) B22499309
theorem B42115211 : Blo 1707054 42115211 := bstep (se 1 (by rfl) ⟨31586408, by rfl⟩ : syracuseStep 42115211 = 63172817) B63172817
theorem B2736271 : Blo 1707054 2736271 := bstep (se 1 (by rfl) ⟨2052203, by rfl⟩ : syracuseStep 2736271 = 4104407) B4104407
theorem B8643023 : Blo 1707054 8643023 := bstep (se 1 (by rfl) ⟨6482267, by rfl⟩ : syracuseStep 8643023 = 12964535) B12964535
theorem B4932191 : Blo 1707054 4932191 := bstep (se 1 (by rfl) ⟨3699143, by rfl⟩ : syracuseStep 4932191 = 7398287) B7398287
theorem B6152861 : Blo 1707054 6152861 := bstep (se 3 (by rfl) ⟨1153661, by rfl⟩ : syracuseStep 6152861 = 2307323) B2307323
theorem B35070731 : Blo 1707054 35070731 := bstep (se 1 (by rfl) ⟨26303048, by rfl⟩ : syracuseStep 35070731 = 52606097) B52606097
theorem B59138909 : Blo 1707054 59138909 := bstep (se 3 (by rfl) ⟨11088545, by rfl⟩ : syracuseStep 59138909 = 22177091) B22177091
theorem B9724769 : Blo 1707054 9724769 := bstep (se 2 (by rfl) ⟨3646788, by rfl⟩ : syracuseStep 9724769 = 7293577) B7293577
theorem B63153881 : Blo 1707054 63153881 := bstep (se 2 (by rfl) ⟨23682705, by rfl⟩ : syracuseStep 63153881 = 47365411) B47365411
theorem B19449719 : Blo 1707054 19449719 := bstep (se 1 (by rfl) ⟨14587289, by rfl⟩ : syracuseStep 19449719 = 29174579) B29174579
theorem B9234395 : Blo 1707054 9234395 := bstep (se 1 (by rfl) ⟨6925796, by rfl⟩ : syracuseStep 9234395 = 13851593) B13851593
theorem B5064893 : Blo 1707054 5064893 := bstep (se 3 (by rfl) ⟨949667, by rfl⟩ : syracuseStep 5064893 = 1899335) B1899335
theorem B9234653 : Blo 1707054 9234653 := bstep (se 3 (by rfl) ⟨1731497, by rfl⟩ : syracuseStep 9234653 = 3462995) B3462995
theorem B10389869 : Blo 1707054 10389869 := bstep (se 3 (by rfl) ⟨1948100, by rfl⟩ : syracuseStep 10389869 = 3896201) B3896201
theorem B3844511 : Blo 1707054 3844511 := bstep (se 1 (by rfl) ⟨2883383, by rfl⟩ : syracuseStep 3844511 = 5766767) B5766767
theorem B19458467 : Blo 1707054 19458467 := bstep (se 1 (by rfl) ⟨14593850, by rfl⟩ : syracuseStep 19458467 = 29187701) B29187701
theorem B10389959 : Blo 1707054 10389959 := bstep (se 1 (by rfl) ⟨7792469, by rfl⟩ : syracuseStep 10389959 = 15584939) B15584939
theorem B9726479 : Blo 1707054 9726479 := bstep (se 1 (by rfl) ⟨7294859, by rfl⟩ : syracuseStep 9726479 = 14589719) B14589719
theorem B12315239 : Blo 1707054 12315239 := bstep (se 1 (by rfl) ⟨9236429, by rfl⟩ : syracuseStep 12315239 = 18472859) B18472859
theorem B3845033 : Blo 1707054 3845033 := bstep (se 2 (by rfl) ⟨1441887, by rfl⟩ : syracuseStep 3845033 = 2883775) B2883775
theorem B1707099 : Blo 1707054 1707099 := bstep (se 1 (by rfl) ⟨1280324, by rfl⟩ : syracuseStep 1707099 = 2560649) B2560649
theorem B12307565 : Blo 1707054 12307565 := bstep (se 3 (by rfl) ⟨2307668, by rfl⟩ : syracuseStep 12307565 = 4615337) B4615337
theorem B8645777 : Blo 1707054 8645777 := bstep (se 2 (by rfl) ⟨3242166, by rfl⟩ : syracuseStep 8645777 = 6484333) B6484333
theorem B1707239 : Blo 1707054 1707239 := bstep (se 1 (by rfl) ⟨1280429, by rfl⟩ : syracuseStep 1707239 = 2560859) B2560859
theorem B4861291 : Blo 1707054 4861291 := bstep (se 1 (by rfl) ⟨3645968, by rfl⟩ : syracuseStep 4861291 = 7291937) B7291937
theorem B6483361 : Blo 1707054 6483361 := bstep (se 2 (by rfl) ⟨2431260, by rfl⟩ : syracuseStep 6483361 = 4862521) B4862521
theorem B17526253 : Blo 1707054 17526253 := bstep (se 3 (by rfl) ⟨3286172, by rfl⟩ : syracuseStep 17526253 = 6572345) B6572345
theorem B7294465 : Blo 1707054 7294465 := bstep (se 2 (by rfl) ⟨2735424, by rfl⟩ : syracuseStep 7294465 = 5470849) B5470849
theorem B1707547 : Blo 1707054 1707547 := bstep (se 1 (by rfl) ⟨1280660, by rfl⟩ : syracuseStep 1707547 = 2561321) B2561321
theorem B36949607 : Blo 1707054 36949607 := bstep (se 1 (by rfl) ⟨27712205, by rfl⟩ : syracuseStep 36949607 = 55424411) B55424411
theorem B13848221 : Blo 1707054 13848221 := bstep (se 3 (by rfl) ⟨2596541, by rfl⟩ : syracuseStep 13848221 = 5193083) B5193083
theorem B1707679 : Blo 1707054 1707679 := bstep (se 1 (by rfl) ⟨1280759, by rfl⟩ : syracuseStep 1707679 = 2561519) B2561519
theorem B4861691 : Blo 1707054 4861691 := bstep (se 1 (by rfl) ⟨3646268, by rfl⟩ : syracuseStep 4861691 = 7292537) B7292537
theorem B74837819 : Blo 1707054 74837819 := bstep (se 1 (by rfl) ⟨56128364, by rfl⟩ : syracuseStep 74837819 = 112256729) B112256729
theorem B1707943 : Blo 1707054 1707943 := bstep (se 1 (by rfl) ⟨1280957, by rfl⟩ : syracuseStep 1707943 = 2561915) B2561915
theorem B1707967 : Blo 1707054 1707967 := bstep (se 1 (by rfl) ⟨1280975, by rfl⟩ : syracuseStep 1707967 = 2561951) B2561951
theorem B10948567 : Blo 1707054 10948567 := bstep (se 1 (by rfl) ⟨8211425, by rfl⟩ : syracuseStep 10948567 = 16422851) B16422851
theorem B14995439 : Blo 1707054 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B1708123 : Blo 1707054 1708123 := bstep (se 1 (by rfl) ⟨1281092, by rfl⟩ : syracuseStep 1708123 = 2562185) B2562185
theorem B1708223 : Blo 1707054 1708223 := bstep (se 1 (by rfl) ⟨1281167, by rfl⟩ : syracuseStep 1708223 = 2562335) B2562335
theorem B4321633 : Blo 1707054 4321633 := bstep (se 2 (by rfl) ⟨1620612, by rfl⟩ : syracuseStep 4321633 = 3241225) B3241225
theorem B1921567 : Blo 1707054 1921567 := bstep (se 1 (by rfl) ⟨1441175, by rfl⟩ : syracuseStep 1921567 = 2882351) B2882351
theorem B1708591 : Blo 1707054 1708591 := bstep (se 1 (by rfl) ⟨1281443, by rfl⟩ : syracuseStep 1708591 = 2562887) B2562887
theorem B2560763 : Blo 1707054 2560763 := bstep (se 1 (by rfl) ⟨1920572, by rfl⟩ : syracuseStep 2560763 = 3841145) B3841145
theorem B5469095 : Blo 1707054 5469095 := bstep (se 1 (by rfl) ⟨4101821, by rfl⟩ : syracuseStep 5469095 = 8203643) B8203643
theorem B4322281 : Blo 1707054 4322281 := bstep (se 2 (by rfl) ⟨1620855, by rfl⟩ : syracuseStep 4322281 = 3241711) B3241711
theorem B2921465 : Blo 1707054 2921465 := bstep (se 2 (by rfl) ⟨1095549, by rfl⟩ : syracuseStep 2921465 = 2191099) B2191099
theorem B43774991 : Blo 1707054 43774991 := bstep (se 1 (by rfl) ⟨32831243, by rfl⟩ : syracuseStep 43774991 = 65662487) B65662487
theorem B37966927 : Blo 1707054 37966927 := bstep (se 1 (by rfl) ⟨28475195, by rfl⟩ : syracuseStep 37966927 = 56950391) B56950391
theorem B12317777 : Blo 1707054 12317777 := bstep (se 2 (by rfl) ⟨4619166, by rfl⟩ : syracuseStep 12317777 = 9238333) B9238333
theorem B2561135 : Blo 1707054 2561135 := bstep (se 1 (by rfl) ⟨1920851, by rfl⟩ : syracuseStep 2561135 = 3841703) B3841703
theorem B2561207 : Blo 1707054 2561207 := bstep (se 1 (by rfl) ⟨1920905, by rfl⟩ : syracuseStep 2561207 = 3841811) B3841811
theorem B39998771 : Blo 1707054 39998771 := bstep (se 1 (by rfl) ⟨29999078, by rfl⟩ : syracuseStep 39998771 = 59998157) B59998157
theorem B2561447 : Blo 1707054 2561447 := bstep (se 1 (by rfl) ⟨1921085, by rfl⟩ : syracuseStep 2561447 = 3842171) B3842171
theorem B49239485 : Blo 1707054 49239485 := bstep (se 3 (by rfl) ⟨9232403, by rfl⟩ : syracuseStep 49239485 = 18464807) B18464807
theorem B62314055 : Blo 1707054 62314055 := bstep (se 1 (by rfl) ⟨46735541, by rfl⟩ : syracuseStep 62314055 = 93471083) B93471083
theorem B2561627 : Blo 1707054 2561627 := bstep (se 1 (by rfl) ⟨1921220, by rfl⟩ : syracuseStep 2561627 = 3842441) B3842441
theorem B42137333 : Blo 1707054 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B7296911 : Blo 1707054 7296911 := bstep (se 1 (by rfl) ⟨5472683, by rfl⟩ : syracuseStep 7296911 = 10945367) B10945367
theorem B4863979 : Blo 1707054 4863979 := bstep (se 1 (by rfl) ⟨3647984, by rfl⟩ : syracuseStep 4863979 = 7295969) B7295969
theorem B2160695 : Blo 1707054 2160695 := bstep (se 1 (by rfl) ⟨1620521, by rfl⟩ : syracuseStep 2160695 = 3241043) B3241043
theorem B12974255 : Blo 1707054 12974255 := bstep (se 1 (by rfl) ⟨9730691, by rfl⟩ : syracuseStep 12974255 = 19461383) B19461383
theorem B4323577 : Blo 1707054 4323577 := bstep (se 2 (by rfl) ⟨1621341, by rfl⟩ : syracuseStep 4323577 = 3242683) B3242683
theorem B8649017 : Blo 1707054 8649017 := bstep (se 2 (by rfl) ⟨3243381, by rfl⟩ : syracuseStep 8649017 = 6486763) B6486763
theorem B2562383 : Blo 1707054 2562383 := bstep (se 1 (by rfl) ⟨1921787, by rfl⟩ : syracuseStep 2562383 = 3843575) B3843575
theorem B2562407 : Blo 1707054 2562407 := bstep (se 1 (by rfl) ⟨1921805, by rfl⟩ : syracuseStep 2562407 = 3843611) B3843611
theorem B13154723 : Blo 1707054 13154723 := bstep (se 1 (by rfl) ⟨9866042, by rfl⟩ : syracuseStep 13154723 = 19732085) B19732085
theorem B2562473 : Blo 1707054 2562473 := bstep (se 2 (by rfl) ⟨960927, by rfl⟩ : syracuseStep 2562473 = 1921855) B1921855
theorem B2882027 : Blo 1707054 2882027 := bstep (se 1 (by rfl) ⟨2161520, by rfl⟩ : syracuseStep 2882027 = 4323041) B4323041
theorem B2431739 : Blo 1707054 2431739 := bstep (se 1 (by rfl) ⟨1823804, by rfl⟩ : syracuseStep 2431739 = 3647609) B3647609
theorem B16407319 : Blo 1707054 16407319 := bstep (se 1 (by rfl) ⟨12305489, by rfl⟩ : syracuseStep 16407319 = 24610979) B24610979
theorem B2562857 : Blo 1707054 2562857 := bstep (se 2 (by rfl) ⟨961071, by rfl⟩ : syracuseStep 2562857 = 1922143) B1922143
theorem B5766119 : Blo 1707054 5766119 := bstep (se 1 (by rfl) ⟨4324589, by rfl⟩ : syracuseStep 5766119 = 8649179) B8649179
theorem B2563067 : Blo 1707054 2563067 := bstep (se 1 (by rfl) ⟨1922300, by rfl⟩ : syracuseStep 2563067 = 3844601) B3844601
theorem B2882587 : Blo 1707054 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B6487067 : Blo 1707054 6487067 := bstep (se 1 (by rfl) ⟨4865300, by rfl⟩ : syracuseStep 6487067 = 9730601) B9730601
theorem B3841055 : Blo 1707054 3841055 := bstep (se 1 (by rfl) ⟨2880791, by rfl⟩ : syracuseStep 3841055 = 5761583) B5761583
theorem B2563103 : Blo 1707054 2563103 := bstep (se 1 (by rfl) ⟨1922327, by rfl⟩ : syracuseStep 2563103 = 3844655) B3844655
theorem B2563127 : Blo 1707054 2563127 := bstep (se 1 (by rfl) ⟨1922345, by rfl⟩ : syracuseStep 2563127 = 3844691) B3844691
theorem B2161819 : Blo 1707054 2161819 := bstep (se 1 (by rfl) ⟨1621364, by rfl⟩ : syracuseStep 2161819 = 3242729) B3242729
theorem B2563247 : Blo 1707054 2563247 := bstep (se 1 (by rfl) ⟨1922435, by rfl⟩ : syracuseStep 2563247 = 3844871) B3844871
theorem B2563391 : Blo 1707054 2563391 := bstep (se 1 (by rfl) ⟨1922543, by rfl⟩ : syracuseStep 2563391 = 3845087) B3845087
theorem B9723311 : Blo 1707054 9723311 := bstep (se 1 (by rfl) ⟨7292483, by rfl⟩ : syracuseStep 9723311 = 14584967) B14584967
theorem B3841487 : Blo 1707054 3841487 := bstep (se 1 (by rfl) ⟨2881115, by rfl⟩ : syracuseStep 3841487 = 5762231) B5762231
theorem B2563535 : Blo 1707054 2563535 := bstep (se 1 (by rfl) ⟨1922651, by rfl⟩ : syracuseStep 2563535 = 3845303) B3845303
theorem B3243503 : Blo 1707054 3243503 := bstep (se 1 (by rfl) ⟨2432627, by rfl⟩ : syracuseStep 3243503 = 4865255) B4865255
theorem B17522183 : Blo 1707054 17522183 := bstep (se 1 (by rfl) ⟨13141637, by rfl⟩ : syracuseStep 17522183 = 26283275) B26283275
theorem B4865609 : Blo 1707054 4865609 := bstep (se 2 (by rfl) ⟨1824603, by rfl⟩ : syracuseStep 4865609 = 3649207) B3649207
theorem B2596463 : Blo 1707054 2596463 := bstep (se 1 (by rfl) ⟨1947347, by rfl⟩ : syracuseStep 2596463 = 3894695) B3894695
theorem B4865665 : Blo 1707054 4865665 := bstep (se 2 (by rfl) ⟨1824624, by rfl⟩ : syracuseStep 4865665 = 3649249) B3649249
theorem B23380487 : Blo 1707054 23380487 := bstep (se 1 (by rfl) ⟨17535365, by rfl⟩ : syracuseStep 23380487 = 35070731) B35070731
theorem B24625741 : Blo 1707054 24625741 := bstep (se 3 (by rfl) ⟨4617326, by rfl⟩ : syracuseStep 24625741 = 9234653) B9234653
theorem B3646063 : Blo 1707054 3646063 := bstep (se 1 (by rfl) ⟨2734547, by rfl⟩ : syracuseStep 3646063 = 5469095) B5469095
theorem B26665847 : Blo 1707054 26665847 := bstep (se 1 (by rfl) ⟨19999385, by rfl⟩ : syracuseStep 26665847 = 39998771) B39998771
theorem B32826323 : Blo 1707054 32826323 := bstep (se 1 (by rfl) ⟨24619742, by rfl⟩ : syracuseStep 32826323 = 49239485) B49239485
theorem B41542703 : Blo 1707054 41542703 := bstep (se 1 (by rfl) ⟨31157027, by rfl⟩ : syracuseStep 41542703 = 62314055) B62314055
theorem B28091555 : Blo 1707054 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B3843449 : Blo 1707054 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B3376595 : Blo 1707054 3376595 := bstep (se 1 (by rfl) ⟨2532446, by rfl⟩ : syracuseStep 3376595 = 5064893) B5064893
theorem B8210159 : Blo 1707054 8210159 := bstep (se 1 (by rfl) ⟨6157619, by rfl⟩ : syracuseStep 8210159 = 12315239) B12315239
theorem B6481721 : Blo 1707054 6481721 := bstep (se 2 (by rfl) ⟨2430645, by rfl⟩ : syracuseStep 6481721 = 4861291) B4861291
theorem B8644481 : Blo 1707054 8644481 := bstep (se 2 (by rfl) ⟨3241680, by rfl⟩ : syracuseStep 8644481 = 6483361) B6483361
theorem B3844079 : Blo 1707054 3844079 := bstep (se 1 (by rfl) ⟨2883059, by rfl⟩ : syracuseStep 3844079 = 5766119) B5766119
theorem B9725953 : Blo 1707054 9725953 := bstep (se 2 (by rfl) ⟨3647232, by rfl⟩ : syracuseStep 9725953 = 7294465) B7294465
theorem B6482207 : Blo 1707054 6482207 := bstep (se 1 (by rfl) ⟨4861655, by rfl⟩ : syracuseStep 6482207 = 9723311) B9723311
theorem B1730975 : Blo 1707054 1730975 := bstep (se 1 (by rfl) ⟨1298231, by rfl⟩ : syracuseStep 1730975 = 2596463) B2596463
theorem B49891879 : Blo 1707054 49891879 := bstep (se 1 (by rfl) ⟨37418909, by rfl⟩ : syracuseStep 49891879 = 74837819) B74837819
theorem B9996959 : Blo 1707054 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B28076807 : Blo 1707054 28076807 := bstep (se 1 (by rfl) ⟨21057605, by rfl⟩ : syracuseStep 28076807 = 42115211) B42115211
theorem B5761853 : Blo 1707054 5761853 := bstep (se 3 (by rfl) ⟨1080347, by rfl⟩ : syracuseStep 5761853 = 2160695) B2160695
theorem B3648361 : Blo 1707054 3648361 := bstep (se 2 (by rfl) ⟨1368135, by rfl⟩ : syracuseStep 3648361 = 2736271) B2736271
theorem B32820173 : Blo 1707054 32820173 := bstep (se 3 (by rfl) ⟨6153782, by rfl⟩ : syracuseStep 32820173 = 12307565) B12307565
theorem B5762015 : Blo 1707054 5762015 := bstep (se 1 (by rfl) ⟨4321511, by rfl⟩ : syracuseStep 5762015 = 8643023) B8643023
theorem B3288127 : Blo 1707054 3288127 := bstep (se 1 (by rfl) ⟨2466095, by rfl⟩ : syracuseStep 3288127 = 4932191) B4932191
theorem B5762177 : Blo 1707054 5762177 := bstep (se 2 (by rfl) ⟨2160816, by rfl⟩ : syracuseStep 5762177 = 4321633) B4321633
theorem B1707175 : Blo 1707054 1707175 := bstep (se 1 (by rfl) ⟨1280381, by rfl⟩ : syracuseStep 1707175 = 2560763) B2560763
theorem B6483179 : Blo 1707054 6483179 := bstep (se 1 (by rfl) ⟨4862384, by rfl⟩ : syracuseStep 6483179 = 9724769) B9724769
theorem B29183327 : Blo 1707054 29183327 := bstep (se 1 (by rfl) ⟨21887495, by rfl⟩ : syracuseStep 29183327 = 43774991) B43774991
theorem B8211851 : Blo 1707054 8211851 := bstep (se 1 (by rfl) ⟨6158888, by rfl⟩ : syracuseStep 8211851 = 12317777) B12317777
theorem B1707423 : Blo 1707054 1707423 := bstep (se 1 (by rfl) ⟨1280567, by rfl⟩ : syracuseStep 1707423 = 2561135) B2561135
theorem B1707471 : Blo 1707054 1707471 := bstep (se 1 (by rfl) ⟨1280603, by rfl⟩ : syracuseStep 1707471 = 2561207) B2561207
theorem B1707631 : Blo 1707054 1707631 := bstep (se 1 (by rfl) ⟨1280723, by rfl⟩ : syracuseStep 1707631 = 2561447) B2561447
theorem B21876425 : Blo 1707054 21876425 := bstep (se 2 (by rfl) ⟨8203659, by rfl⟩ : syracuseStep 21876425 = 16407319) B16407319
theorem B1707751 : Blo 1707054 1707751 := bstep (se 1 (by rfl) ⟨1280813, by rfl⟩ : syracuseStep 1707751 = 2561627) B2561627
theorem B42102587 : Blo 1707054 42102587 := bstep (se 1 (by rfl) ⟨31576940, by rfl⟩ : syracuseStep 42102587 = 63153881) B63153881
theorem B5763041 : Blo 1707054 5763041 := bstep (se 2 (by rfl) ⟨2161140, by rfl⟩ : syracuseStep 5763041 = 4322281) B4322281
theorem B6156263 : Blo 1707054 6156263 := bstep (se 1 (by rfl) ⟨4617197, by rfl⟩ : syracuseStep 6156263 = 9234395) B9234395
theorem B50622569 : Blo 1707054 50622569 := bstep (se 2 (by rfl) ⟨18983463, by rfl⟩ : syracuseStep 50622569 = 37966927) B37966927
theorem B1708255 : Blo 1707054 1708255 := bstep (se 1 (by rfl) ⟨1281191, by rfl⟩ : syracuseStep 1708255 = 2562383) B2562383
theorem B1708271 : Blo 1707054 1708271 := bstep (se 1 (by rfl) ⟨1281203, by rfl⟩ : syracuseStep 1708271 = 2562407) B2562407
theorem B6926579 : Blo 1707054 6926579 := bstep (se 1 (by rfl) ⟨5194934, by rfl⟩ : syracuseStep 6926579 = 10389869) B10389869
theorem B12972311 : Blo 1707054 12972311 := bstep (se 1 (by rfl) ⟨9729233, by rfl⟩ : syracuseStep 12972311 = 19458467) B19458467
theorem B8769815 : Blo 1707054 8769815 := bstep (se 1 (by rfl) ⟨6577361, by rfl⟩ : syracuseStep 8769815 = 13154723) B13154723
theorem B1708315 : Blo 1707054 1708315 := bstep (se 1 (by rfl) ⟨1281236, by rfl⟩ : syracuseStep 1708315 = 2562473) B2562473
theorem B6926639 : Blo 1707054 6926639 := bstep (se 1 (by rfl) ⟨5194979, by rfl⟩ : syracuseStep 6926639 = 10389959) B10389959
theorem B1921351 : Blo 1707054 1921351 := bstep (se 1 (by rfl) ⟨1441013, by rfl⟩ : syracuseStep 1921351 = 2882027) B2882027
theorem B6484319 : Blo 1707054 6484319 := bstep (se 1 (by rfl) ⟨4863239, by rfl⟩ : syracuseStep 6484319 = 9726479) B9726479
theorem B1708571 : Blo 1707054 1708571 := bstep (se 1 (by rfl) ⟨1281428, by rfl⟩ : syracuseStep 1708571 = 2562857) B2562857
theorem B23368337 : Blo 1707054 23368337 := bstep (se 2 (by rfl) ⟨8763126, by rfl⟩ : syracuseStep 23368337 = 17526253) B17526253
theorem B6484637 : Blo 1707054 6484637 := bstep (se 3 (by rfl) ⟨1215869, by rfl⟩ : syracuseStep 6484637 = 2431739) B2431739
theorem B1708711 : Blo 1707054 1708711 := bstep (se 1 (by rfl) ⟨1281533, by rfl⟩ : syracuseStep 1708711 = 2563067) B2563067
theorem B2560703 : Blo 1707054 2560703 := bstep (se 1 (by rfl) ⟨1920527, by rfl⟩ : syracuseStep 2560703 = 3841055) B3841055
theorem B1708735 : Blo 1707054 1708735 := bstep (se 1 (by rfl) ⟨1281551, by rfl⟩ : syracuseStep 1708735 = 2563103) B2563103
theorem B1708751 : Blo 1707054 1708751 := bstep (se 1 (by rfl) ⟨1281563, by rfl⟩ : syracuseStep 1708751 = 2563127) B2563127
theorem B5763851 : Blo 1707054 5763851 := bstep (se 1 (by rfl) ⟨4322888, by rfl⟩ : syracuseStep 5763851 = 8645777) B8645777
theorem B1708831 : Blo 1707054 1708831 := bstep (se 1 (by rfl) ⟨1281623, by rfl⟩ : syracuseStep 1708831 = 2563247) B2563247
theorem B1708927 : Blo 1707054 1708927 := bstep (se 1 (by rfl) ⟨1281695, by rfl⟩ : syracuseStep 1708927 = 2563391) B2563391
theorem B2560991 : Blo 1707054 2560991 := bstep (se 1 (by rfl) ⟨1920743, by rfl⟩ : syracuseStep 2560991 = 3841487) B3841487
theorem B1709023 : Blo 1707054 1709023 := bstep (se 1 (by rfl) ⟨1281767, by rfl⟩ : syracuseStep 1709023 = 2563535) B2563535
theorem B3241127 : Blo 1707054 3241127 := bstep (se 1 (by rfl) ⟨2430845, by rfl⟩ : syracuseStep 3241127 = 4861691) B4861691
theorem B6485305 : Blo 1707054 6485305 := bstep (se 2 (by rfl) ⟨2431989, by rfl⟩ : syracuseStep 6485305 = 4863979) B4863979
theorem B5764769 : Blo 1707054 5764769 := bstep (se 2 (by rfl) ⟨2161788, by rfl⟩ : syracuseStep 5764769 = 4323577) B4323577
theorem B4101907 : Blo 1707054 4101907 := bstep (se 1 (by rfl) ⟨3076430, by rfl⟩ : syracuseStep 4101907 = 6152861) B6152861
theorem B39425939 : Blo 1707054 39425939 := bstep (se 1 (by rfl) ⟨29569454, by rfl⟩ : syracuseStep 39425939 = 59138909) B59138909
theorem B2562089 : Blo 1707054 2562089 := bstep (se 2 (by rfl) ⟨960783, by rfl⟩ : syracuseStep 2562089 = 1921567) B1921567
theorem B12966479 : Blo 1707054 12966479 := bstep (se 1 (by rfl) ⟨9724859, by rfl⟩ : syracuseStep 12966479 = 19449719) B19449719
theorem B4864607 : Blo 1707054 4864607 := bstep (se 1 (by rfl) ⟨3648455, by rfl⟩ : syracuseStep 4864607 = 7296911) B7296911
theorem B8649341 : Blo 1707054 8649341 := bstep (se 3 (by rfl) ⟨1621751, by rfl⟩ : syracuseStep 8649341 = 3243503) B3243503
theorem B8649503 : Blo 1707054 8649503 := bstep (se 1 (by rfl) ⟨6487127, by rfl⟩ : syracuseStep 8649503 = 12974255) B12974255
theorem B2882425 : Blo 1707054 2882425 := bstep (se 2 (by rfl) ⟨1080909, by rfl⟩ : syracuseStep 2882425 = 2161819) B2161819
theorem B5766011 : Blo 1707054 5766011 := bstep (se 1 (by rfl) ⟨4324508, by rfl⟩ : syracuseStep 5766011 = 8649017) B8649017
theorem B2563007 : Blo 1707054 2563007 := bstep (se 1 (by rfl) ⟨1922255, by rfl⟩ : syracuseStep 2563007 = 3844511) B3844511
theorem B2563355 : Blo 1707054 2563355 := bstep (se 1 (by rfl) ⟨1922516, by rfl⟩ : syracuseStep 2563355 = 3845033) B3845033
theorem B4324711 : Blo 1707054 4324711 := bstep (se 1 (by rfl) ⟨3243533, by rfl⟩ : syracuseStep 4324711 = 6487067) B6487067
theorem B6487553 : Blo 1707054 6487553 := bstep (se 2 (by rfl) ⟨2432832, by rfl⟩ : syracuseStep 6487553 = 4865665) B4865665
theorem B11681455 : Blo 1707054 11681455 := bstep (se 1 (by rfl) ⟨8761091, by rfl⟩ : syracuseStep 11681455 = 17522183) B17522183
theorem B3243739 : Blo 1707054 3243739 := bstep (se 1 (by rfl) ⟨2432804, by rfl⟩ : syracuseStep 3243739 = 4865609) B4865609
theorem B24633071 : Blo 1707054 24633071 := bstep (se 1 (by rfl) ⟨18474803, by rfl⟩ : syracuseStep 24633071 = 36949607) B36949607
theorem B9232147 : Blo 1707054 9232147 := bstep (se 1 (by rfl) ⟨6924110, by rfl⟩ : syracuseStep 9232147 = 13848221) B13848221
theorem B14598089 : Blo 1707054 14598089 := bstep (se 2 (by rfl) ⟨5474283, by rfl⟩ : syracuseStep 14598089 = 10948567) B10948567
theorem B7790573 : Blo 1707054 7790573 := bstep (se 3 (by rfl) ⟨1460732, by rfl⟩ : syracuseStep 7790573 = 2921465) B2921465
theorem B12967937 : Blo 1707054 12967937 := bstep (se 2 (by rfl) ⟨4862976, by rfl⟩ : syracuseStep 12967937 = 9725953) B9725953
theorem B3842567 : Blo 1707054 3842567 := bstep (se 1 (by rfl) ⟨2881925, by rfl⟩ : syracuseStep 3842567 = 5763851) B5763851
theorem B17777231 : Blo 1707054 17777231 := bstep (se 1 (by rfl) ⟨13332923, by rfl⟩ : syracuseStep 17777231 = 26665847) B26665847
theorem B32834321 : Blo 1707054 32834321 := bstep (se 2 (by rfl) ⟨12312870, by rfl⟩ : syracuseStep 32834321 = 24625741) B24625741
theorem B18727703 : Blo 1707054 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B3843179 : Blo 1707054 3843179 := bstep (se 1 (by rfl) ⟨2882384, by rfl⟩ : syracuseStep 3843179 = 5764769) B5764769
theorem B5473439 : Blo 1707054 5473439 := bstep (se 1 (by rfl) ⟨4105079, by rfl⟩ : syracuseStep 5473439 = 8210159) B8210159
theorem B3843233 : Blo 1707054 3843233 := bstep (se 2 (by rfl) ⟨1441212, by rfl⟩ : syracuseStep 3843233 = 2882425) B2882425
theorem B4384169 : Blo 1707054 4384169 := bstep (se 2 (by rfl) ⟨1644063, by rfl⟩ : syracuseStep 4384169 = 3288127) B3288127
theorem B8644319 : Blo 1707054 8644319 := bstep (se 1 (by rfl) ⟨6483239, by rfl⟩ : syracuseStep 8644319 = 12966479) B12966479
theorem B3844007 : Blo 1707054 3844007 := bstep (se 1 (by rfl) ⟨2883005, by rfl⟩ : syracuseStep 3844007 = 5766011) B5766011
theorem B15575273 : Blo 1707054 15575273 := bstep (se 2 (by rfl) ⟨5840727, by rfl⟩ : syracuseStep 15575273 = 11681455) B11681455
theorem B5474567 : Blo 1707054 5474567 := bstep (se 1 (by rfl) ⟨4105925, by rfl⟩ : syracuseStep 5474567 = 8211851) B8211851
theorem B14584283 : Blo 1707054 14584283 := bstep (se 1 (by rfl) ⟨10938212, by rfl⟩ : syracuseStep 14584283 = 21876425) B21876425
theorem B28068391 : Blo 1707054 28068391 := bstep (se 1 (by rfl) ⟨21051293, by rfl⟩ : syracuseStep 28068391 = 42102587) B42102587
theorem B1707135 : Blo 1707054 1707135 := bstep (se 1 (by rfl) ⟨1280351, by rfl⟩ : syracuseStep 1707135 = 2560703) B2560703
theorem B21884215 : Blo 1707054 21884215 := bstep (se 1 (by rfl) ⟨16413161, by rfl⟩ : syracuseStep 21884215 = 32826323) B32826323
theorem B1707327 : Blo 1707054 1707327 := bstep (se 1 (by rfl) ⟨1280495, by rfl⟩ : syracuseStep 1707327 = 2560991) B2560991
theorem B4861417 : Blo 1707054 4861417 := bstep (se 2 (by rfl) ⟨1823031, by rfl⟩ : syracuseStep 4861417 = 3646063) B3646063
theorem B4321147 : Blo 1707054 4321147 := bstep (se 1 (by rfl) ⟨3240860, by rfl⟩ : syracuseStep 4321147 = 6481721) B6481721
theorem B5762987 : Blo 1707054 5762987 := bstep (se 1 (by rfl) ⟨4322240, by rfl⟩ : syracuseStep 5762987 = 8644481) B8644481
theorem B26283959 : Blo 1707054 26283959 := bstep (se 1 (by rfl) ⟨19712969, by rfl⟩ : syracuseStep 26283959 = 39425939) B39425939
theorem B1708059 : Blo 1707054 1708059 := bstep (se 1 (by rfl) ⟨1281044, by rfl⟩ : syracuseStep 1708059 = 2562089) B2562089
theorem B4321471 : Blo 1707054 4321471 := bstep (se 1 (by rfl) ⟨3241103, by rfl⟩ : syracuseStep 4321471 = 6482207) B6482207
theorem B8647073 : Blo 1707054 8647073 := bstep (se 2 (by rfl) ⟨3242652, by rfl⟩ : syracuseStep 8647073 = 6485305) B6485305
theorem B6664639 : Blo 1707054 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B1708671 : Blo 1707054 1708671 := bstep (se 1 (by rfl) ⟨1281503, by rfl⟩ : syracuseStep 1708671 = 2563007) B2563007
theorem B74871485 : Blo 1707054 74871485 := bstep (se 3 (by rfl) ⟨14038403, by rfl⟩ : syracuseStep 74871485 = 28076807) B28076807
theorem B4322119 : Blo 1707054 4322119 := bstep (se 1 (by rfl) ⟨3241589, by rfl⟩ : syracuseStep 4322119 = 6483179) B6483179
theorem B1708903 : Blo 1707054 1708903 := bstep (se 1 (by rfl) ⟨1281677, by rfl⟩ : syracuseStep 1708903 = 2563355) B2563355
theorem B5469209 : Blo 1707054 5469209 := bstep (se 2 (by rfl) ⟨2050953, by rfl⟩ : syracuseStep 5469209 = 4101907) B4101907
theorem B12309529 : Blo 1707054 12309529 := bstep (se 2 (by rfl) ⟨4616073, by rfl⟩ : syracuseStep 12309529 = 9232147) B9232147
theorem B16422047 : Blo 1707054 16422047 := bstep (se 1 (by rfl) ⟨12316535, by rfl⟩ : syracuseStep 16422047 = 24633071) B24633071
theorem B33748379 : Blo 1707054 33748379 := bstep (se 1 (by rfl) ⟨25311284, by rfl⟩ : syracuseStep 33748379 = 50622569) B50622569
theorem B4617719 : Blo 1707054 4617719 := bstep (se 1 (by rfl) ⟨3463289, by rfl⟩ : syracuseStep 4617719 = 6926579) B6926579
theorem B8648207 : Blo 1707054 8648207 := bstep (se 1 (by rfl) ⟨6486155, by rfl⟩ : syracuseStep 8648207 = 12972311) B12972311
theorem B5846543 : Blo 1707054 5846543 := bstep (se 1 (by rfl) ⟨4384907, by rfl⟩ : syracuseStep 5846543 = 8769815) B8769815
theorem B266090021 : Blo 1707054 266090021 := bstep (se 4 (by rfl) ⟨24945939, by rfl⟩ : syracuseStep 266090021 = 49891879) B49891879
theorem B4322879 : Blo 1707054 4322879 := bstep (se 1 (by rfl) ⟨3242159, by rfl⟩ : syracuseStep 4322879 = 6484319) B6484319
theorem B15586991 : Blo 1707054 15586991 := bstep (se 1 (by rfl) ⟨11690243, by rfl⟩ : syracuseStep 15586991 = 23380487) B23380487
theorem B2561801 : Blo 1707054 2561801 := bstep (se 2 (by rfl) ⟨960675, by rfl⟩ : syracuseStep 2561801 = 1921351) B1921351
theorem B15578891 : Blo 1707054 15578891 := bstep (se 1 (by rfl) ⟨11684168, by rfl⟩ : syracuseStep 15578891 = 23368337) B23368337
theorem B4323091 : Blo 1707054 4323091 := bstep (se 1 (by rfl) ⟨3242318, by rfl⟩ : syracuseStep 4323091 = 6484637) B6484637
theorem B27695135 : Blo 1707054 27695135 := bstep (se 1 (by rfl) ⟨20771351, by rfl⟩ : syracuseStep 27695135 = 41542703) B41542703
theorem B2160751 : Blo 1707054 2160751 := bstep (se 1 (by rfl) ⟨1620563, by rfl⟩ : syracuseStep 2160751 = 3241127) B3241127
theorem B18471037 : Blo 1707054 18471037 := bstep (se 3 (by rfl) ⟨3463319, by rfl⟩ : syracuseStep 18471037 = 6926639) B6926639
theorem B2562299 : Blo 1707054 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B2251063 : Blo 1707054 2251063 := bstep (se 1 (by rfl) ⟨1688297, by rfl⟩ : syracuseStep 2251063 = 3376595) B3376595
theorem B4864481 : Blo 1707054 4864481 := bstep (se 2 (by rfl) ⟨1824180, by rfl⟩ : syracuseStep 4864481 = 3648361) B3648361
theorem B2562719 : Blo 1707054 2562719 := bstep (se 1 (by rfl) ⟨1922039, by rfl⟩ : syracuseStep 2562719 = 3844079) B3844079
theorem B18463733 : Blo 1707054 18463733 := bstep (se 5 (by rfl) ⟨865487, by rfl⟩ : syracuseStep 18463733 = 1730975) B1730975
theorem B3243071 : Blo 1707054 3243071 := bstep (se 1 (by rfl) ⟨2432303, by rfl⟩ : syracuseStep 3243071 = 4864607) B4864607
theorem B5766227 : Blo 1707054 5766227 := bstep (se 1 (by rfl) ⟨4324670, by rfl⟩ : syracuseStep 5766227 = 8649341) B8649341
theorem B5766281 : Blo 1707054 5766281 := bstep (se 2 (by rfl) ⟨2162355, by rfl⟩ : syracuseStep 5766281 = 4324711) B4324711
theorem B5766335 : Blo 1707054 5766335 := bstep (se 1 (by rfl) ⟨4324751, by rfl⟩ : syracuseStep 5766335 = 8649503) B8649503
theorem B3841235 : Blo 1707054 3841235 := bstep (se 1 (by rfl) ⟨2880926, by rfl⟩ : syracuseStep 3841235 = 5761853) B5761853
theorem B21880115 : Blo 1707054 21880115 := bstep (se 1 (by rfl) ⟨16410086, by rfl⟩ : syracuseStep 21880115 = 32820173) B32820173
theorem B3841343 : Blo 1707054 3841343 := bstep (se 1 (by rfl) ⟨2881007, by rfl⟩ : syracuseStep 3841343 = 5762015) B5762015
theorem B3841451 : Blo 1707054 3841451 := bstep (se 1 (by rfl) ⟨2881088, by rfl⟩ : syracuseStep 3841451 = 5762177) B5762177
theorem B19455551 : Blo 1707054 19455551 := bstep (se 1 (by rfl) ⟨14591663, by rfl⟩ : syracuseStep 19455551 = 29183327) B29183327
theorem B4324985 : Blo 1707054 4324985 := bstep (se 2 (by rfl) ⟨1621869, by rfl⟩ : syracuseStep 4324985 = 3243739) B3243739
theorem B4325035 : Blo 1707054 4325035 := bstep (se 1 (by rfl) ⟨3243776, by rfl⟩ : syracuseStep 4325035 = 6487553) B6487553
theorem B16416701 : Blo 1707054 16416701 := bstep (se 3 (by rfl) ⟨3078131, by rfl⟩ : syracuseStep 16416701 = 6156263) B6156263
theorem B9732059 : Blo 1707054 9732059 := bstep (se 1 (by rfl) ⟨7299044, by rfl⟩ : syracuseStep 9732059 = 14598089) B14598089
theorem B3842027 : Blo 1707054 3842027 := bstep (se 1 (by rfl) ⟨2881520, by rfl⟩ : syracuseStep 3842027 = 5763041) B5763041
theorem B5193715 : Blo 1707054 5193715 := bstep (se 1 (by rfl) ⟨3895286, by rfl⟩ : syracuseStep 5193715 = 7790573) B7790573
theorem B49914323 : Blo 1707054 49914323 := bstep (se 1 (by rfl) ⟨37435742, by rfl⟩ : syracuseStep 49914323 = 74871485) B74871485
theorem B21889547 : Blo 1707054 21889547 := bstep (se 1 (by rfl) ⟨16417160, by rfl⟩ : syracuseStep 21889547 = 32834321) B32834321
theorem B12485135 : Blo 1707054 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B3646139 : Blo 1707054 3646139 := bstep (se 1 (by rfl) ⟨2734604, by rfl⟩ : syracuseStep 3646139 = 5469209) B5469209
theorem B6481889 : Blo 1707054 6481889 := bstep (se 2 (by rfl) ⟨2430708, by rfl⟩ : syracuseStep 6481889 = 4861417) B4861417
theorem B3844151 : Blo 1707054 3844151 := bstep (se 1 (by rfl) ⟨2883113, by rfl⟩ : syracuseStep 3844151 = 5766227) B5766227
theorem B3844187 : Blo 1707054 3844187 := bstep (se 1 (by rfl) ⟨2883140, by rfl⟩ : syracuseStep 3844187 = 5766281) B5766281
theorem B3844223 : Blo 1707054 3844223 := bstep (se 1 (by rfl) ⟨2883167, by rfl⟩ : syracuseStep 3844223 = 5766335) B5766335
theorem B12970367 : Blo 1707054 12970367 := bstep (se 1 (by rfl) ⟨9727775, by rfl⟩ : syracuseStep 12970367 = 19455551) B19455551
theorem B5761529 : Blo 1707054 5761529 := bstep (se 2 (by rfl) ⟨2160573, by rfl⟩ : syracuseStep 5761529 = 4321147) B4321147
theorem B6924953 : Blo 1707054 6924953 := bstep (se 2 (by rfl) ⟨2596857, by rfl⟩ : syracuseStep 6924953 = 5193715) B5193715
theorem B8645291 : Blo 1707054 8645291 := bstep (se 1 (by rfl) ⟨6483968, by rfl⟩ : syracuseStep 8645291 = 12967937) B12967937
theorem B73853693 : Blo 1707054 73853693 := bstep (se 3 (by rfl) ⟨13847567, by rfl⟩ : syracuseStep 73853693 = 27695135) B27695135
theorem B24628049 : Blo 1707054 24628049 := bstep (se 2 (by rfl) ⟨9235518, by rfl⟩ : syracuseStep 24628049 = 18471037) B18471037
theorem B5761961 : Blo 1707054 5761961 := bstep (se 2 (by rfl) ⟨2160735, by rfl⟩ : syracuseStep 5761961 = 4321471) B4321471
theorem B3001417 : Blo 1707054 3001417 := bstep (se 2 (by rfl) ⟨1125531, by rfl⟩ : syracuseStep 3001417 = 2251063) B2251063
theorem B37424521 : Blo 1707054 37424521 := bstep (se 2 (by rfl) ⟨14034195, by rfl⟩ : syracuseStep 37424521 = 28068391) B28068391
theorem B3648959 : Blo 1707054 3648959 := bstep (se 1 (by rfl) ⟨2736719, by rfl⟩ : syracuseStep 3648959 = 5473439) B5473439
theorem B10948031 : Blo 1707054 10948031 := bstep (se 1 (by rfl) ⟨8211023, by rfl⟩ : syracuseStep 10948031 = 16422047) B16422047
theorem B22498919 : Blo 1707054 22498919 := bstep (se 1 (by rfl) ⟨16874189, by rfl⟩ : syracuseStep 22498919 = 33748379) B33748379
theorem B177393347 : Blo 1707054 177393347 := bstep (se 1 (by rfl) ⟨133045010, by rfl⟩ : syracuseStep 177393347 = 266090021) B266090021
theorem B5762825 : Blo 1707054 5762825 := bstep (se 2 (by rfl) ⟨2161059, by rfl⟩ : syracuseStep 5762825 = 4322119) B4322119
theorem B10391327 : Blo 1707054 10391327 := bstep (se 1 (by rfl) ⟨7793495, by rfl⟩ : syracuseStep 10391327 = 15586991) B15586991
theorem B5762879 : Blo 1707054 5762879 := bstep (se 1 (by rfl) ⟨4322159, by rfl⟩ : syracuseStep 5762879 = 8644319) B8644319
theorem B1707867 : Blo 1707054 1707867 := bstep (se 1 (by rfl) ⟨1280900, by rfl⟩ : syracuseStep 1707867 = 2561801) B2561801
theorem B16412705 : Blo 1707054 16412705 := bstep (se 2 (by rfl) ⟨6154764, by rfl⟩ : syracuseStep 16412705 = 12309529) B12309529
theorem B10383515 : Blo 1707054 10383515 := bstep (se 1 (by rfl) ⟨7787636, by rfl⟩ : syracuseStep 10383515 = 15575273) B15575273
theorem B1708199 : Blo 1707054 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B3649711 : Blo 1707054 3649711 := bstep (se 1 (by rfl) ⟨2737283, by rfl⟩ : syracuseStep 3649711 = 5474567) B5474567
theorem B1708479 : Blo 1707054 1708479 := bstep (se 1 (by rfl) ⟨1281359, by rfl⟩ : syracuseStep 1708479 = 2562719) B2562719
theorem B12309155 : Blo 1707054 12309155 := bstep (se 1 (by rfl) ⟨9231866, by rfl⟩ : syracuseStep 12309155 = 18463733) B18463733
theorem B2560823 : Blo 1707054 2560823 := bstep (se 1 (by rfl) ⟨1920617, by rfl⟩ : syracuseStep 2560823 = 3841235) B3841235
theorem B14586743 : Blo 1707054 14586743 := bstep (se 1 (by rfl) ⟨10940057, by rfl⟩ : syracuseStep 14586743 = 21880115) B21880115
theorem B2560895 : Blo 1707054 2560895 := bstep (se 1 (by rfl) ⟨1920671, by rfl⟩ : syracuseStep 2560895 = 3841343) B3841343
theorem B2560967 : Blo 1707054 2560967 := bstep (se 1 (by rfl) ⟨1920725, by rfl⟩ : syracuseStep 2560967 = 3841451) B3841451
theorem B5764121 : Blo 1707054 5764121 := bstep (se 2 (by rfl) ⟨2161545, by rfl⟩ : syracuseStep 5764121 = 4323091) B4323091
theorem B2561351 : Blo 1707054 2561351 := bstep (se 1 (by rfl) ⟨1921013, by rfl⟩ : syracuseStep 2561351 = 3842027) B3842027
theorem B2881001 : Blo 1707054 2881001 := bstep (se 2 (by rfl) ⟨1080375, by rfl⟩ : syracuseStep 2881001 = 2160751) B2160751
theorem B5764715 : Blo 1707054 5764715 := bstep (se 1 (by rfl) ⟨4323536, by rfl⟩ : syracuseStep 5764715 = 8647073) B8647073
theorem B2561711 : Blo 1707054 2561711 := bstep (se 1 (by rfl) ⟨1921283, by rfl⟩ : syracuseStep 2561711 = 3842567) B3842567
theorem B11851487 : Blo 1707054 11851487 := bstep (se 1 (by rfl) ⟨8888615, by rfl⟩ : syracuseStep 11851487 = 17777231) B17777231
theorem B8886185 : Blo 1707054 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B2562119 : Blo 1707054 2562119 := bstep (se 1 (by rfl) ⟨1921589, by rfl⟩ : syracuseStep 2562119 = 3843179) B3843179
theorem B2562155 : Blo 1707054 2562155 := bstep (se 1 (by rfl) ⟨1921616, by rfl⟩ : syracuseStep 2562155 = 3843233) B3843233
theorem B2922779 : Blo 1707054 2922779 := bstep (se 1 (by rfl) ⟨2192084, by rfl⟩ : syracuseStep 2922779 = 4384169) B4384169
theorem B3078479 : Blo 1707054 3078479 := bstep (se 1 (by rfl) ⟨2308859, by rfl⟩ : syracuseStep 3078479 = 4617719) B4617719
theorem B5765471 : Blo 1707054 5765471 := bstep (se 1 (by rfl) ⟨4324103, by rfl⟩ : syracuseStep 5765471 = 8648207) B8648207
theorem B3897695 : Blo 1707054 3897695 := bstep (se 1 (by rfl) ⟨2923271, by rfl⟩ : syracuseStep 3897695 = 5846543) B5846543
theorem B2881919 : Blo 1707054 2881919 := bstep (se 1 (by rfl) ⟨2161439, by rfl⟩ : syracuseStep 2881919 = 4322879) B4322879
theorem B10385927 : Blo 1707054 10385927 := bstep (se 1 (by rfl) ⟨7789445, by rfl⟩ : syracuseStep 10385927 = 15578891) B15578891
theorem B2562671 : Blo 1707054 2562671 := bstep (se 1 (by rfl) ⟨1922003, by rfl⟩ : syracuseStep 2562671 = 3844007) B3844007
theorem B9722855 : Blo 1707054 9722855 := bstep (se 1 (by rfl) ⟨7292141, by rfl⟩ : syracuseStep 9722855 = 14584283) B14584283
theorem B3242987 : Blo 1707054 3242987 := bstep (se 1 (by rfl) ⟨2432240, by rfl⟩ : syracuseStep 3242987 = 4864481) B4864481
theorem B29178953 : Blo 1707054 29178953 := bstep (se 2 (by rfl) ⟨10942107, by rfl⟩ : syracuseStep 29178953 = 21884215) B21884215
theorem B2162047 : Blo 1707054 2162047 := bstep (se 1 (by rfl) ⟨1621535, by rfl⟩ : syracuseStep 2162047 = 3243071) B3243071
theorem B5766713 : Blo 1707054 5766713 := bstep (se 2 (by rfl) ⟨2162517, by rfl⟩ : syracuseStep 5766713 = 4325035) B4325035
theorem B2883323 : Blo 1707054 2883323 := bstep (se 1 (by rfl) ⟨2162492, by rfl⟩ : syracuseStep 2883323 = 4324985) B4324985
theorem B3841991 : Blo 1707054 3841991 := bstep (se 1 (by rfl) ⟨2881493, by rfl⟩ : syracuseStep 3841991 = 5762987) B5762987
theorem B17522639 : Blo 1707054 17522639 := bstep (se 1 (by rfl) ⟨13141979, by rfl⟩ : syracuseStep 17522639 = 26283959) B26283959
theorem B10944467 : Blo 1707054 10944467 := bstep (se 1 (by rfl) ⟨8208350, by rfl⟩ : syracuseStep 10944467 = 16416701) B16416701
theorem B6488039 : Blo 1707054 6488039 := bstep (se 1 (by rfl) ⟨4866029, by rfl⟩ : syracuseStep 6488039 = 9732059) B9732059
theorem B6922343 : Blo 1707054 6922343 := bstep (se 1 (by rfl) ⟨5191757, by rfl⟩ : syracuseStep 6922343 = 10383515) B10383515
theorem B4866281 : Blo 1707054 4866281 := bstep (se 2 (by rfl) ⟨1824855, by rfl⟩ : syracuseStep 4866281 = 3649711) B3649711
theorem B33276215 : Blo 1707054 33276215 := bstep (se 1 (by rfl) ⟨24957161, by rfl⟩ : syracuseStep 33276215 = 49914323) B49914323
theorem B16007557 : Blo 1707054 16007557 := bstep (se 4 (by rfl) ⟨1500708, by rfl⟩ : syracuseStep 16007557 = 3001417) B3001417
theorem B9724495 : Blo 1707054 9724495 := bstep (se 1 (by rfl) ⟨7293371, by rfl⟩ : syracuseStep 9724495 = 14586743) B14586743
theorem B3842747 : Blo 1707054 3842747 := bstep (se 1 (by rfl) ⟨2882060, by rfl⟩ : syracuseStep 3842747 = 5764121) B5764121
theorem B3843143 : Blo 1707054 3843143 := bstep (se 1 (by rfl) ⟨2882357, by rfl⟩ : syracuseStep 3843143 = 5764715) B5764715
theorem B5924123 : Blo 1707054 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B33293693 : Blo 1707054 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B3843647 : Blo 1707054 3843647 := bstep (se 1 (by rfl) ⟨2882735, by rfl⟩ : syracuseStep 3843647 = 5765471) B5765471
theorem B2598463 : Blo 1707054 2598463 := bstep (se 1 (by rfl) ⟨1948847, by rfl⟩ : syracuseStep 2598463 = 3897695) B3897695
theorem B6923951 : Blo 1707054 6923951 := bstep (se 1 (by rfl) ⟨5192963, by rfl⟩ : syracuseStep 6923951 = 10385927) B10385927
theorem B18466541 : Blo 1707054 18466541 := bstep (se 3 (by rfl) ⟨3462476, by rfl⟩ : syracuseStep 18466541 = 6924953) B6924953
theorem B49235795 : Blo 1707054 49235795 := bstep (se 1 (by rfl) ⟨36926846, by rfl⟩ : syracuseStep 49235795 = 73853693) B73853693
theorem B16418699 : Blo 1707054 16418699 := bstep (se 1 (by rfl) ⟨12314024, by rfl⟩ : syracuseStep 16418699 = 24628049) B24628049
theorem B6481903 : Blo 1707054 6481903 := bstep (se 1 (by rfl) ⟨4861427, by rfl⟩ : syracuseStep 6481903 = 9722855) B9722855
theorem B3844475 : Blo 1707054 3844475 := bstep (se 1 (by rfl) ⟨2883356, by rfl⟩ : syracuseStep 3844475 = 5766713) B5766713
theorem B118262231 : Blo 1707054 118262231 := bstep (se 1 (by rfl) ⟨88696673, by rfl⟩ : syracuseStep 118262231 = 177393347) B177393347
theorem B14593031 : Blo 1707054 14593031 := bstep (se 1 (by rfl) ⟨10944773, by rfl⟩ : syracuseStep 14593031 = 21889547) B21889547
theorem B1707215 : Blo 1707054 1707215 := bstep (se 1 (by rfl) ⟨1280411, by rfl⟩ : syracuseStep 1707215 = 2560823) B2560823
theorem B1707263 : Blo 1707054 1707263 := bstep (se 1 (by rfl) ⟨1280447, by rfl⟩ : syracuseStep 1707263 = 2560895) B2560895
theorem B1707311 : Blo 1707054 1707311 := bstep (se 1 (by rfl) ⟨1280483, by rfl⟩ : syracuseStep 1707311 = 2560967) B2560967
theorem B1707567 : Blo 1707054 1707567 := bstep (se 1 (by rfl) ⟨1280675, by rfl⟩ : syracuseStep 1707567 = 2561351) B2561351
theorem B1920667 : Blo 1707054 1920667 := bstep (se 1 (by rfl) ⟨1440500, by rfl⟩ : syracuseStep 1920667 = 2881001) B2881001
theorem B1707807 : Blo 1707054 1707807 := bstep (se 1 (by rfl) ⟨1280855, by rfl⟩ : syracuseStep 1707807 = 2561711) B2561711
theorem B7900991 : Blo 1707054 7900991 := bstep (se 1 (by rfl) ⟨5925743, by rfl⟩ : syracuseStep 7900991 = 11851487) B11851487
theorem B4321259 : Blo 1707054 4321259 := bstep (se 1 (by rfl) ⟨3240944, by rfl⟩ : syracuseStep 4321259 = 6481889) B6481889
theorem B1708079 : Blo 1707054 1708079 := bstep (se 1 (by rfl) ⟨1281059, by rfl⟩ : syracuseStep 1708079 = 2562119) B2562119
theorem B1708103 : Blo 1707054 1708103 := bstep (se 1 (by rfl) ⟨1281077, by rfl⟩ : syracuseStep 1708103 = 2562155) B2562155
theorem B2052319 : Blo 1707054 2052319 := bstep (se 1 (by rfl) ⟨1539239, by rfl⟩ : syracuseStep 2052319 = 3078479) B3078479
theorem B1921279 : Blo 1707054 1921279 := bstep (se 1 (by rfl) ⟨1440959, by rfl⟩ : syracuseStep 1921279 = 2881919) B2881919
theorem B8646911 : Blo 1707054 8646911 := bstep (se 1 (by rfl) ⟨6485183, by rfl⟩ : syracuseStep 8646911 = 12970367) B12970367
theorem B1708447 : Blo 1707054 1708447 := bstep (se 1 (by rfl) ⟨1281335, by rfl⟩ : syracuseStep 1708447 = 2562671) B2562671
theorem B5763527 : Blo 1707054 5763527 := bstep (se 1 (by rfl) ⟨4322645, by rfl⟩ : syracuseStep 5763527 = 8645291) B8645291
theorem B19452635 : Blo 1707054 19452635 := bstep (se 1 (by rfl) ⟨14589476, by rfl⟩ : syracuseStep 19452635 = 29178953) B29178953
theorem B1922215 : Blo 1707054 1922215 := bstep (se 1 (by rfl) ⟨1441661, by rfl⟩ : syracuseStep 1922215 = 2883323) B2883323
theorem B6927551 : Blo 1707054 6927551 := bstep (se 1 (by rfl) ⟨5195663, by rfl⟩ : syracuseStep 6927551 = 10391327) B10391327
theorem B2561327 : Blo 1707054 2561327 := bstep (se 1 (by rfl) ⟨1920995, by rfl⟩ : syracuseStep 2561327 = 3841991) B3841991
theorem B7296311 : Blo 1707054 7296311 := bstep (se 1 (by rfl) ⟨5472233, by rfl⟩ : syracuseStep 7296311 = 10944467) B10944467
theorem B10941803 : Blo 1707054 10941803 := bstep (se 1 (by rfl) ⟨8206352, by rfl⟩ : syracuseStep 10941803 = 16412705) B16412705
theorem B8206103 : Blo 1707054 8206103 := bstep (se 1 (by rfl) ⟨6154577, by rfl⟩ : syracuseStep 8206103 = 12309155) B12309155
theorem B2562767 : Blo 1707054 2562767 := bstep (se 1 (by rfl) ⟨1922075, by rfl⟩ : syracuseStep 2562767 = 3844151) B3844151
theorem B2562791 : Blo 1707054 2562791 := bstep (se 1 (by rfl) ⟨1922093, by rfl⟩ : syracuseStep 2562791 = 3844187) B3844187
theorem B2562815 : Blo 1707054 2562815 := bstep (se 1 (by rfl) ⟨1922111, by rfl⟩ : syracuseStep 2562815 = 3844223) B3844223
theorem B1948519 : Blo 1707054 1948519 := bstep (se 1 (by rfl) ⟨1461389, by rfl⟩ : syracuseStep 1948519 = 2922779) B2922779
theorem B3841019 : Blo 1707054 3841019 := bstep (se 1 (by rfl) ⟨2880764, by rfl⟩ : syracuseStep 3841019 = 5761529) B5761529
theorem B9723037 : Blo 1707054 9723037 := bstep (se 3 (by rfl) ⟨1823069, by rfl⟩ : syracuseStep 9723037 = 3646139) B3646139
theorem B2882729 : Blo 1707054 2882729 := bstep (se 2 (by rfl) ⟨1081023, by rfl⟩ : syracuseStep 2882729 = 2162047) B2162047
theorem B3841307 : Blo 1707054 3841307 := bstep (se 1 (by rfl) ⟨2880980, by rfl⟩ : syracuseStep 3841307 = 5761961) B5761961
theorem B2161991 : Blo 1707054 2161991 := bstep (se 1 (by rfl) ⟨1621493, by rfl⟩ : syracuseStep 2161991 = 3242987) B3242987
theorem B199597445 : Blo 1707054 199597445 := bstep (se 4 (by rfl) ⟨18712260, by rfl⟩ : syracuseStep 199597445 = 37424521) B37424521
theorem B2432639 : Blo 1707054 2432639 := bstep (se 1 (by rfl) ⟨1824479, by rfl⟩ : syracuseStep 2432639 = 3648959) B3648959
theorem B7298687 : Blo 1707054 7298687 := bstep (se 1 (by rfl) ⟨5474015, by rfl⟩ : syracuseStep 7298687 = 10948031) B10948031
theorem B14999279 : Blo 1707054 14999279 := bstep (se 1 (by rfl) ⟨11249459, by rfl⟩ : syracuseStep 14999279 = 22498919) B22498919
theorem B3841883 : Blo 1707054 3841883 := bstep (se 1 (by rfl) ⟨2881412, by rfl⟩ : syracuseStep 3841883 = 5762825) B5762825
theorem B3841919 : Blo 1707054 3841919 := bstep (se 1 (by rfl) ⟨2881439, by rfl⟩ : syracuseStep 3841919 = 5762879) B5762879
theorem B11681759 : Blo 1707054 11681759 := bstep (se 1 (by rfl) ⟨8761319, by rfl⟩ : syracuseStep 11681759 = 17522639) B17522639
theorem B4325359 : Blo 1707054 4325359 := bstep (se 1 (by rfl) ⟨3244019, by rfl⟩ : syracuseStep 4325359 = 6488039) B6488039
theorem B3244187 : Blo 1707054 3244187 := bstep (se 1 (by rfl) ⟨2433140, by rfl⟩ : syracuseStep 3244187 = 4866281) B4866281
theorem B2736425 : Blo 1707054 2736425 := bstep (se 2 (by rfl) ⟨1026159, by rfl⟩ : syracuseStep 2736425 = 2052319) B2052319
theorem B3842351 : Blo 1707054 3842351 := bstep (se 1 (by rfl) ⟨2881763, by rfl⟩ : syracuseStep 3842351 = 5763527) B5763527
theorem B12968423 : Blo 1707054 12968423 := bstep (se 1 (by rfl) ⟨9726317, by rfl⟩ : syracuseStep 12968423 = 19452635) B19452635
theorem B88736573 : Blo 1707054 88736573 := bstep (se 3 (by rfl) ⟨16638107, by rfl⟩ : syracuseStep 88736573 = 33276215) B33276215
theorem B3949415 : Blo 1707054 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B10945799 : Blo 1707054 10945799 := bstep (se 1 (by rfl) ⟨8209349, by rfl⟩ : syracuseStep 10945799 = 16418699) B16418699
theorem B78841487 : Blo 1707054 78841487 := bstep (se 1 (by rfl) ⟨59131115, by rfl⟩ : syracuseStep 78841487 = 118262231) B118262231
theorem B133064963 : Blo 1707054 133064963 := bstep (se 1 (by rfl) ⟨99798722, by rfl⟩ : syracuseStep 133064963 = 199597445) B199597445
theorem B159992309 : Blo 1707054 159992309 := bstep (se 5 (by rfl) ⟨7499639, by rfl⟩ : syracuseStep 159992309 = 14999279) B14999279
theorem B4614895 : Blo 1707054 4614895 := bstep (se 1 (by rfl) ⟨3461171, by rfl⟩ : syracuseStep 4614895 = 6922343) B6922343
theorem B21343409 : Blo 1707054 21343409 := bstep (se 2 (by rfl) ⟨8003778, by rfl⟩ : syracuseStep 21343409 = 16007557) B16007557
theorem B1707551 : Blo 1707054 1707551 := bstep (se 1 (by rfl) ⟨1280663, by rfl⟩ : syracuseStep 1707551 = 2561327) B2561327
theorem B7294535 : Blo 1707054 7294535 := bstep (se 1 (by rfl) ⟨5470901, by rfl⟩ : syracuseStep 7294535 = 10941803) B10941803
theorem B22195795 : Blo 1707054 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B4615967 : Blo 1707054 4615967 := bstep (se 1 (by rfl) ⟨3461975, by rfl⟩ : syracuseStep 4615967 = 6923951) B6923951
theorem B12964049 : Blo 1707054 12964049 := bstep (se 2 (by rfl) ⟨4861518, by rfl⟩ : syracuseStep 12964049 = 9723037) B9723037
theorem B1708511 : Blo 1707054 1708511 := bstep (se 1 (by rfl) ⟨1281383, by rfl⟩ : syracuseStep 1708511 = 2562767) B2562767
theorem B1708527 : Blo 1707054 1708527 := bstep (se 1 (by rfl) ⟨1281395, by rfl⟩ : syracuseStep 1708527 = 2562791) B2562791
theorem B1708543 : Blo 1707054 1708543 := bstep (se 1 (by rfl) ⟨1281407, by rfl⟩ : syracuseStep 1708543 = 2562815) B2562815
theorem B10392101 : Blo 1707054 10392101 := bstep (se 4 (by rfl) ⟨974259, by rfl⟩ : syracuseStep 10392101 = 1948519) B1948519
theorem B2560679 : Blo 1707054 2560679 := bstep (se 1 (by rfl) ⟨1920509, by rfl⟩ : syracuseStep 2560679 = 3841019) B3841019
theorem B9728687 : Blo 1707054 9728687 := bstep (se 1 (by rfl) ⟨7296515, by rfl⟩ : syracuseStep 9728687 = 14593031) B14593031
theorem B1921819 : Blo 1707054 1921819 := bstep (se 1 (by rfl) ⟨1441364, by rfl⟩ : syracuseStep 1921819 = 2882729) B2882729
theorem B2560871 : Blo 1707054 2560871 := bstep (se 1 (by rfl) ⟨1920653, by rfl⟩ : syracuseStep 2560871 = 3841307) B3841307
theorem B2560889 : Blo 1707054 2560889 := bstep (se 2 (by rfl) ⟨960333, by rfl⟩ : syracuseStep 2560889 = 1920667) B1920667
theorem B2561255 : Blo 1707054 2561255 := bstep (se 1 (by rfl) ⟨1920941, by rfl⟩ : syracuseStep 2561255 = 3841883) B3841883
theorem B2561279 : Blo 1707054 2561279 := bstep (se 1 (by rfl) ⟨1920959, by rfl⟩ : syracuseStep 2561279 = 3841919) B3841919
theorem B7787839 : Blo 1707054 7787839 := bstep (se 1 (by rfl) ⟨5840879, by rfl⟩ : syracuseStep 7787839 = 11681759) B11681759
theorem B2880839 : Blo 1707054 2880839 := bstep (se 1 (by rfl) ⟨2160629, by rfl⟩ : syracuseStep 2880839 = 4321259) B4321259
theorem B5764607 : Blo 1707054 5764607 := bstep (se 1 (by rfl) ⟨4323455, by rfl⟩ : syracuseStep 5764607 = 8646911) B8646911
theorem B2561705 : Blo 1707054 2561705 := bstep (se 2 (by rfl) ⟨960639, by rfl⟩ : syracuseStep 2561705 = 1921279) B1921279
theorem B2561831 : Blo 1707054 2561831 := bstep (se 1 (by rfl) ⟨1921373, by rfl⟩ : syracuseStep 2561831 = 3842747) B3842747
theorem B2562095 : Blo 1707054 2562095 := bstep (se 1 (by rfl) ⟨1921571, by rfl⟩ : syracuseStep 2562095 = 3843143) B3843143
theorem B12965993 : Blo 1707054 12965993 := bstep (se 2 (by rfl) ⟨4862247, by rfl⟩ : syracuseStep 12965993 = 9724495) B9724495
theorem B4618367 : Blo 1707054 4618367 := bstep (se 1 (by rfl) ⟨3463775, by rfl⟩ : syracuseStep 4618367 = 6927551) B6927551
theorem B5765309 : Blo 1707054 5765309 := bstep (se 3 (by rfl) ⟨1080995, by rfl⟩ : syracuseStep 5765309 = 2161991) B2161991
theorem B4864207 : Blo 1707054 4864207 := bstep (se 1 (by rfl) ⟨3648155, by rfl⟩ : syracuseStep 4864207 = 7296311) B7296311
theorem B2562431 : Blo 1707054 2562431 := bstep (se 1 (by rfl) ⟨1921823, by rfl⟩ : syracuseStep 2562431 = 3843647) B3843647
theorem B12311027 : Blo 1707054 12311027 := bstep (se 1 (by rfl) ⟨9233270, by rfl⟩ : syracuseStep 12311027 = 18466541) B18466541
theorem B5470735 : Blo 1707054 5470735 := bstep (se 1 (by rfl) ⟨4103051, by rfl⟩ : syracuseStep 5470735 = 8206103) B8206103
theorem B32823863 : Blo 1707054 32823863 := bstep (se 1 (by rfl) ⟨24617897, by rfl⟩ : syracuseStep 32823863 = 49235795) B49235795
theorem B2562953 : Blo 1707054 2562953 := bstep (se 2 (by rfl) ⟨961107, by rfl⟩ : syracuseStep 2562953 = 1922215) B1922215
theorem B2562983 : Blo 1707054 2562983 := bstep (se 1 (by rfl) ⟨1922237, by rfl⟩ : syracuseStep 2562983 = 3844475) B3844475
theorem B6487037 : Blo 1707054 6487037 := bstep (se 3 (by rfl) ⟨1216319, by rfl⟩ : syracuseStep 6487037 = 2432639) B2432639
theorem B3464617 : Blo 1707054 3464617 := bstep (se 2 (by rfl) ⟨1299231, by rfl⟩ : syracuseStep 3464617 = 2598463) B2598463
theorem B4865791 : Blo 1707054 4865791 := bstep (se 1 (by rfl) ⟨3649343, by rfl⟩ : syracuseStep 4865791 = 7298687) B7298687
theorem B5267327 : Blo 1707054 5267327 := bstep (se 1 (by rfl) ⟨3950495, by rfl⟩ : syracuseStep 5267327 = 7900991) B7900991
theorem B8642537 : Blo 1707054 8642537 := bstep (se 2 (by rfl) ⟨3240951, by rfl⟩ : syracuseStep 8642537 = 6481903) B6481903
theorem B5767145 : Blo 1707054 5767145 := bstep (se 2 (by rfl) ⟨2162679, by rfl⟩ : syracuseStep 5767145 = 4325359) B4325359
theorem B2162791 : Blo 1707054 2162791 := bstep (se 1 (by rfl) ⟨1622093, by rfl⟩ : syracuseStep 2162791 = 3244187) B3244187
theorem B8642699 : Blo 1707054 8642699 := bstep (se 1 (by rfl) ⟨6482024, by rfl⟩ : syracuseStep 8642699 = 12964049) B12964049
theorem B6153193 : Blo 1707054 6153193 := bstep (se 2 (by rfl) ⟨2307447, by rfl⟩ : syracuseStep 6153193 = 4614895) B4614895
theorem B3843071 : Blo 1707054 3843071 := bstep (se 1 (by rfl) ⟨2882303, by rfl⟩ : syracuseStep 3843071 = 5764607) B5764607
theorem B52560991 : Blo 1707054 52560991 := bstep (se 1 (by rfl) ⟨39420743, by rfl⟩ : syracuseStep 52560991 = 78841487) B78841487
theorem B8643995 : Blo 1707054 8643995 := bstep (se 1 (by rfl) ⟨6482996, by rfl⟩ : syracuseStep 8643995 = 12965993) B12965993
theorem B3843539 : Blo 1707054 3843539 := bstep (se 1 (by rfl) ⟨2882654, by rfl⟩ : syracuseStep 3843539 = 5765309) B5765309
theorem B106661539 : Blo 1707054 106661539 := bstep (se 1 (by rfl) ⟨79996154, by rfl⟩ : syracuseStep 106661539 = 159992309) B159992309
theorem B21882575 : Blo 1707054 21882575 := bstep (se 1 (by rfl) ⟨16411931, by rfl⟩ : syracuseStep 21882575 = 32823863) B32823863
theorem B5761691 : Blo 1707054 5761691 := bstep (se 1 (by rfl) ⟨4321268, by rfl⟩ : syracuseStep 5761691 = 8642537) B8642537
theorem B3844763 : Blo 1707054 3844763 := bstep (se 1 (by rfl) ⟨2883572, by rfl⟩ : syracuseStep 3844763 = 5767145) B5767145
theorem B8645615 : Blo 1707054 8645615 := bstep (se 1 (by rfl) ⟨6484211, by rfl⟩ : syracuseStep 8645615 = 12968423) B12968423
theorem B1707119 : Blo 1707054 1707119 := bstep (se 1 (by rfl) ⟨1280339, by rfl⟩ : syracuseStep 1707119 = 2560679) B2560679
theorem B59157715 : Blo 1707054 59157715 := bstep (se 1 (by rfl) ⟨44368286, by rfl⟩ : syracuseStep 59157715 = 88736573) B88736573
theorem B1707247 : Blo 1707054 1707247 := bstep (se 1 (by rfl) ⟨1280435, by rfl⟩ : syracuseStep 1707247 = 2560871) B2560871
theorem B2632943 : Blo 1707054 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B1707259 : Blo 1707054 1707259 := bstep (se 1 (by rfl) ⟨1280444, by rfl⟩ : syracuseStep 1707259 = 2560889) B2560889
theorem B7294313 : Blo 1707054 7294313 := bstep (se 2 (by rfl) ⟨2735367, by rfl⟩ : syracuseStep 7294313 = 5470735) B5470735
theorem B1707503 : Blo 1707054 1707503 := bstep (se 1 (by rfl) ⟨1280627, by rfl⟩ : syracuseStep 1707503 = 2561255) B2561255
theorem B1707519 : Blo 1707054 1707519 := bstep (se 1 (by rfl) ⟨1280639, by rfl⟩ : syracuseStep 1707519 = 2561279) B2561279
theorem B1920559 : Blo 1707054 1920559 := bstep (se 1 (by rfl) ⟨1440419, by rfl⟩ : syracuseStep 1920559 = 2880839) B2880839
theorem B1707803 : Blo 1707054 1707803 := bstep (se 1 (by rfl) ⟨1280852, by rfl⟩ : syracuseStep 1707803 = 2561705) B2561705
theorem B1707887 : Blo 1707054 1707887 := bstep (se 1 (by rfl) ⟨1280915, by rfl⟩ : syracuseStep 1707887 = 2561831) B2561831
theorem B1708063 : Blo 1707054 1708063 := bstep (se 1 (by rfl) ⟨1281047, by rfl⟩ : syracuseStep 1708063 = 2562095) B2562095
theorem B1708287 : Blo 1707054 1708287 := bstep (se 1 (by rfl) ⟨1281215, by rfl⟩ : syracuseStep 1708287 = 2562431) B2562431
theorem B10383785 : Blo 1707054 10383785 := bstep (se 2 (by rfl) ⟨3893919, by rfl⟩ : syracuseStep 10383785 = 7787839) B7787839
theorem B1708635 : Blo 1707054 1708635 := bstep (se 1 (by rfl) ⟨1281476, by rfl⟩ : syracuseStep 1708635 = 2562953) B2562953
theorem B1708655 : Blo 1707054 1708655 := bstep (se 1 (by rfl) ⟨1281491, by rfl⟩ : syracuseStep 1708655 = 2562983) B2562983
theorem B29594393 : Blo 1707054 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B14046205 : Blo 1707054 14046205 := bstep (se 3 (by rfl) ⟨2633663, by rfl⟩ : syracuseStep 14046205 = 5267327) B5267327
theorem B4863023 : Blo 1707054 4863023 := bstep (se 1 (by rfl) ⟨3647267, by rfl⟩ : syracuseStep 4863023 = 7294535) B7294535
theorem B3077311 : Blo 1707054 3077311 := bstep (se 1 (by rfl) ⟨2307983, by rfl⟩ : syracuseStep 3077311 = 4615967) B4615967
theorem B1824283 : Blo 1707054 1824283 := bstep (se 1 (by rfl) ⟨1368212, by rfl⟩ : syracuseStep 1824283 = 2736425) B2736425
theorem B2561567 : Blo 1707054 2561567 := bstep (se 1 (by rfl) ⟨1921175, by rfl⟩ : syracuseStep 2561567 = 3842351) B3842351
theorem B6485609 : Blo 1707054 6485609 := bstep (se 2 (by rfl) ⟨2432103, by rfl⟩ : syracuseStep 6485609 = 4864207) B4864207
theorem B6928067 : Blo 1707054 6928067 := bstep (se 1 (by rfl) ⟨5196050, by rfl⟩ : syracuseStep 6928067 = 10392101) B10392101
theorem B6485791 : Blo 1707054 6485791 := bstep (se 1 (by rfl) ⟨4864343, by rfl⟩ : syracuseStep 6485791 = 9728687) B9728687
theorem B7297199 : Blo 1707054 7297199 := bstep (se 1 (by rfl) ⟨5472899, by rfl⟩ : syracuseStep 7297199 = 10945799) B10945799
theorem B2562425 : Blo 1707054 2562425 := bstep (se 2 (by rfl) ⟨960909, by rfl⟩ : syracuseStep 2562425 = 1921819) B1921819
theorem B3078911 : Blo 1707054 3078911 := bstep (se 1 (by rfl) ⟨2309183, by rfl⟩ : syracuseStep 3078911 = 4618367) B4618367
theorem B88709975 : Blo 1707054 88709975 := bstep (se 1 (by rfl) ⟨66532481, by rfl⟩ : syracuseStep 88709975 = 133064963) B133064963
theorem B8207351 : Blo 1707054 8207351 := bstep (se 1 (by rfl) ⟨6155513, by rfl⟩ : syracuseStep 8207351 = 12311027) B12311027
theorem B4619489 : Blo 1707054 4619489 := bstep (se 2 (by rfl) ⟨1732308, by rfl⟩ : syracuseStep 4619489 = 3464617) B3464617
theorem B4324691 : Blo 1707054 4324691 := bstep (se 1 (by rfl) ⟨3243518, by rfl⟩ : syracuseStep 4324691 = 6487037) B6487037
theorem B14228939 : Blo 1707054 14228939 := bstep (se 1 (by rfl) ⟨10671704, by rfl⟩ : syracuseStep 14228939 = 21343409) B21343409
theorem B6487721 : Blo 1707054 6487721 := bstep (se 2 (by rfl) ⟨2432895, by rfl⟩ : syracuseStep 6487721 = 4865791) B4865791
theorem B2883721 : Blo 1707054 2883721 := bstep (se 2 (by rfl) ⟨1081395, by rfl⟩ : syracuseStep 2883721 = 2162791) B2162791
theorem B6922523 : Blo 1707054 6922523 := bstep (se 1 (by rfl) ⟨5191892, by rfl⟩ : syracuseStep 6922523 = 10383785) B10383785
theorem B568861541 : Blo 1707054 568861541 := bstep (se 4 (by rfl) ⟨53330769, by rfl⟩ : syracuseStep 568861541 = 106661539) B106661539
theorem B18728273 : Blo 1707054 18728273 := bstep (se 2 (by rfl) ⟨7023102, by rfl⟩ : syracuseStep 18728273 = 14046205) B14046205
theorem B59139983 : Blo 1707054 59139983 := bstep (se 1 (by rfl) ⟨44354987, by rfl⟩ : syracuseStep 59139983 = 88709975) B88709975
theorem B1755295 : Blo 1707054 1755295 := bstep (se 1 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 1755295 = 2632943) B2632943
theorem B5761799 : Blo 1707054 5761799 := bstep (se 1 (by rfl) ⟨4321349, by rfl⟩ : syracuseStep 5761799 = 8642699) B8642699
theorem B280325285 : Blo 1707054 280325285 := bstep (se 4 (by rfl) ⟨26280495, by rfl⟩ : syracuseStep 280325285 = 52560991) B52560991
theorem B19729595 : Blo 1707054 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B5762663 : Blo 1707054 5762663 := bstep (se 1 (by rfl) ⟨4321997, by rfl⟩ : syracuseStep 5762663 = 8643995) B8643995
theorem B1707711 : Blo 1707054 1707711 := bstep (se 1 (by rfl) ⟨1280783, by rfl⟩ : syracuseStep 1707711 = 2561567) B2561567
theorem B8204257 : Blo 1707054 8204257 := bstep (se 2 (by rfl) ⟨3076596, by rfl⟩ : syracuseStep 8204257 = 6153193) B6153193
theorem B1708283 : Blo 1707054 1708283 := bstep (se 1 (by rfl) ⟨1281212, by rfl⟩ : syracuseStep 1708283 = 2562425) B2562425
theorem B78876953 : Blo 1707054 78876953 := bstep (se 2 (by rfl) ⟨29578857, by rfl⟩ : syracuseStep 78876953 = 59157715) B59157715
theorem B2052607 : Blo 1707054 2052607 := bstep (se 1 (by rfl) ⟨1539455, by rfl⟩ : syracuseStep 2052607 = 3078911) B3078911
theorem B5763743 : Blo 1707054 5763743 := bstep (se 1 (by rfl) ⟨4322807, by rfl⟩ : syracuseStep 5763743 = 8645615) B8645615
theorem B2560745 : Blo 1707054 2560745 := bstep (se 2 (by rfl) ⟨960279, by rfl⟩ : syracuseStep 2560745 = 1920559) B1920559
theorem B4862875 : Blo 1707054 4862875 := bstep (se 1 (by rfl) ⟨3647156, by rfl⟩ : syracuseStep 4862875 = 7294313) B7294313
theorem B8647721 : Blo 1707054 8647721 := bstep (se 2 (by rfl) ⟨3242895, by rfl⟩ : syracuseStep 8647721 = 6485791) B6485791
theorem B12318637 : Blo 1707054 12318637 := bstep (se 3 (by rfl) ⟨2309744, by rfl⟩ : syracuseStep 12318637 = 4619489) B4619489
theorem B2562047 : Blo 1707054 2562047 := bstep (se 1 (by rfl) ⟨1921535, by rfl⟩ : syracuseStep 2562047 = 3843071) B3843071
theorem B3242015 : Blo 1707054 3242015 := bstep (se 1 (by rfl) ⟨2431511, by rfl⟩ : syracuseStep 3242015 = 4863023) B4863023
theorem B2562359 : Blo 1707054 2562359 := bstep (se 1 (by rfl) ⟨1921769, by rfl⟩ : syracuseStep 2562359 = 3843539) B3843539
theorem B4323739 : Blo 1707054 4323739 := bstep (se 1 (by rfl) ⟨3242804, by rfl⟩ : syracuseStep 4323739 = 6485609) B6485609
theorem B4618711 : Blo 1707054 4618711 := bstep (se 1 (by rfl) ⟨3464033, by rfl⟩ : syracuseStep 4618711 = 6928067) B6928067
theorem B14588383 : Blo 1707054 14588383 := bstep (se 1 (by rfl) ⟨10941287, by rfl⟩ : syracuseStep 14588383 = 21882575) B21882575
theorem B4864799 : Blo 1707054 4864799 := bstep (se 1 (by rfl) ⟨3648599, by rfl⟩ : syracuseStep 4864799 = 7297199) B7297199
theorem B4103081 : Blo 1707054 4103081 := bstep (se 2 (by rfl) ⟨1538655, by rfl⟩ : syracuseStep 4103081 = 3077311) B3077311
theorem B3841127 : Blo 1707054 3841127 := bstep (se 1 (by rfl) ⟨2880845, by rfl⟩ : syracuseStep 3841127 = 5761691) B5761691
theorem B2563175 : Blo 1707054 2563175 := bstep (se 1 (by rfl) ⟨1922381, by rfl⟩ : syracuseStep 2563175 = 3844763) B3844763
theorem B5471567 : Blo 1707054 5471567 := bstep (se 1 (by rfl) ⟨4103675, by rfl⟩ : syracuseStep 5471567 = 8207351) B8207351
theorem B2432377 : Blo 1707054 2432377 := bstep (se 2 (by rfl) ⟨912141, by rfl⟩ : syracuseStep 2432377 = 1824283) B1824283
theorem B2883127 : Blo 1707054 2883127 := bstep (se 1 (by rfl) ⟨2162345, by rfl⟩ : syracuseStep 2883127 = 4324691) B4324691
theorem B9485959 : Blo 1707054 9485959 := bstep (se 1 (by rfl) ⟨7114469, by rfl⟩ : syracuseStep 9485959 = 14228939) B14228939
theorem B4325147 : Blo 1707054 4325147 := bstep (se 1 (by rfl) ⟨3243860, by rfl⟩ : syracuseStep 4325147 = 6487721) B6487721
theorem B52584635 : Blo 1707054 52584635 := bstep (se 1 (by rfl) ⟨39438476, by rfl⟩ : syracuseStep 52584635 = 78876953) B78876953
theorem B3842495 : Blo 1707054 3842495 := bstep (se 1 (by rfl) ⟨2881871, by rfl⟩ : syracuseStep 3842495 = 5763743) B5763743
theorem B379241027 : Blo 1707054 379241027 := bstep (se 1 (by rfl) ⟨284430770, by rfl⟩ : syracuseStep 379241027 = 568861541) B568861541
theorem B37446293 : Blo 1707054 37446293 := bstep (se 6 (by rfl) ⟨877647, by rfl⟩ : syracuseStep 37446293 = 1755295) B1755295
theorem B2736809 : Blo 1707054 2736809 := bstep (se 2 (by rfl) ⟨1026303, by rfl⟩ : syracuseStep 2736809 = 2052607) B2052607
theorem B12485515 : Blo 1707054 12485515 := bstep (se 1 (by rfl) ⟨9364136, by rfl⟩ : syracuseStep 12485515 = 18728273) B18728273
theorem B3844169 : Blo 1707054 3844169 := bstep (se 2 (by rfl) ⟨1441563, by rfl⟩ : syracuseStep 3844169 = 2883127) B2883127
theorem B3647711 : Blo 1707054 3647711 := bstep (se 1 (by rfl) ⟨2735783, by rfl⟩ : syracuseStep 3647711 = 5471567) B5471567
theorem B157706621 : Blo 1707054 157706621 := bstep (se 3 (by rfl) ⟨29569991, by rfl⟩ : syracuseStep 157706621 = 59139983) B59139983
theorem B10939009 : Blo 1707054 10939009 := bstep (se 2 (by rfl) ⟨4102128, by rfl⟩ : syracuseStep 10939009 = 8204257) B8204257
theorem B3844961 : Blo 1707054 3844961 := bstep (se 2 (by rfl) ⟨1441860, by rfl⟩ : syracuseStep 3844961 = 2883721) B2883721
theorem B4615015 : Blo 1707054 4615015 := bstep (se 1 (by rfl) ⟨3461261, by rfl⟩ : syracuseStep 4615015 = 6922523) B6922523
theorem B1707163 : Blo 1707054 1707163 := bstep (se 1 (by rfl) ⟨1280372, by rfl⟩ : syracuseStep 1707163 = 2560745) B2560745
theorem B19451177 : Blo 1707054 19451177 := bstep (se 2 (by rfl) ⟨7294191, by rfl⟩ : syracuseStep 19451177 = 14588383) B14588383
theorem B6483833 : Blo 1707054 6483833 := bstep (se 2 (by rfl) ⟨2431437, by rfl⟩ : syracuseStep 6483833 = 4862875) B4862875
theorem B1708031 : Blo 1707054 1708031 := bstep (se 1 (by rfl) ⟨1281023, by rfl⟩ : syracuseStep 1708031 = 2562047) B2562047
theorem B1708239 : Blo 1707054 1708239 := bstep (se 1 (by rfl) ⟨1281179, by rfl⟩ : syracuseStep 1708239 = 2562359) B2562359
theorem B2560751 : Blo 1707054 2560751 := bstep (se 1 (by rfl) ⟨1920563, by rfl⟩ : syracuseStep 2560751 = 3841127) B3841127
theorem B1708783 : Blo 1707054 1708783 := bstep (se 1 (by rfl) ⟨1281587, by rfl⟩ : syracuseStep 1708783 = 2563175) B2563175
theorem B12972797 : Blo 1707054 12972797 := bstep (se 3 (by rfl) ⟨2432399, by rfl⟩ : syracuseStep 12972797 = 4864799) B4864799
theorem B13153063 : Blo 1707054 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B5764985 : Blo 1707054 5764985 := bstep (se 2 (by rfl) ⟨2161869, by rfl⟩ : syracuseStep 5764985 = 4323739) B4323739
theorem B6158281 : Blo 1707054 6158281 := bstep (se 2 (by rfl) ⟨2309355, by rfl⟩ : syracuseStep 6158281 = 4618711) B4618711
theorem B5765147 : Blo 1707054 5765147 := bstep (se 1 (by rfl) ⟨4323860, by rfl⟩ : syracuseStep 5765147 = 8647721) B8647721
theorem B2161343 : Blo 1707054 2161343 := bstep (se 1 (by rfl) ⟨1621007, by rfl⟩ : syracuseStep 2161343 = 3242015) B3242015
theorem B3243169 : Blo 1707054 3243169 := bstep (se 2 (by rfl) ⟨1216188, by rfl⟩ : syracuseStep 3243169 = 2432377) B2432377
theorem B3841199 : Blo 1707054 3841199 := bstep (se 1 (by rfl) ⟨2880899, by rfl⟩ : syracuseStep 3841199 = 5761799) B5761799
theorem B2735387 : Blo 1707054 2735387 := bstep (se 1 (by rfl) ⟨2051540, by rfl⟩ : syracuseStep 2735387 = 4103081) B4103081
theorem B186883523 : Blo 1707054 186883523 := bstep (se 1 (by rfl) ⟨140162642, by rfl⟩ : syracuseStep 186883523 = 280325285) B280325285
theorem B12647945 : Blo 1707054 12647945 := bstep (se 2 (by rfl) ⟨4742979, by rfl⟩ : syracuseStep 12647945 = 9485959) B9485959
theorem B3841775 : Blo 1707054 3841775 := bstep (se 1 (by rfl) ⟨2881331, by rfl⟩ : syracuseStep 3841775 = 5762663) B5762663
theorem B2883431 : Blo 1707054 2883431 := bstep (se 1 (by rfl) ⟨2162573, by rfl⟩ : syracuseStep 2883431 = 4325147) B4325147
theorem B16424849 : Blo 1707054 16424849 := bstep (se 2 (by rfl) ⟨6159318, by rfl⟩ : syracuseStep 16424849 = 12318637) B12318637
theorem B6153353 : Blo 1707054 6153353 := bstep (se 2 (by rfl) ⟨2307507, by rfl⟩ : syracuseStep 6153353 = 4615015) B4615015
theorem B16647353 : Blo 1707054 16647353 := bstep (se 2 (by rfl) ⟨6242757, by rfl⟩ : syracuseStep 16647353 = 12485515) B12485515
theorem B3843323 : Blo 1707054 3843323 := bstep (se 1 (by rfl) ⟨2882492, by rfl⟩ : syracuseStep 3843323 = 5764985) B5764985
theorem B3843431 : Blo 1707054 3843431 := bstep (se 1 (by rfl) ⟨2882573, by rfl⟩ : syracuseStep 3843431 = 5765147) B5765147
theorem B33727853 : Blo 1707054 33727853 := bstep (se 3 (by rfl) ⟨6323972, by rfl⟩ : syracuseStep 33727853 = 12647945) B12647945
theorem B105137747 : Blo 1707054 105137747 := bstep (se 1 (by rfl) ⟨78853310, by rfl⟩ : syracuseStep 105137747 = 157706621) B157706621
theorem B8211041 : Blo 1707054 8211041 := bstep (se 2 (by rfl) ⟨3079140, by rfl⟩ : syracuseStep 8211041 = 6158281) B6158281
theorem B35056423 : Blo 1707054 35056423 := bstep (se 1 (by rfl) ⟨26292317, by rfl⟩ : syracuseStep 35056423 = 52584635) B52584635
theorem B24964195 : Blo 1707054 24964195 := bstep (se 1 (by rfl) ⟨18723146, by rfl⟩ : syracuseStep 24964195 = 37446293) B37446293
theorem B1707167 : Blo 1707054 1707167 := bstep (se 1 (by rfl) ⟨1280375, by rfl⟩ : syracuseStep 1707167 = 2560751) B2560751
theorem B9727229 : Blo 1707054 9727229 := bstep (se 3 (by rfl) ⟨1823855, by rfl⟩ : syracuseStep 9727229 = 3647711) B3647711
theorem B14585345 : Blo 1707054 14585345 := bstep (se 2 (by rfl) ⟨5469504, by rfl⟩ : syracuseStep 14585345 = 10939009) B10939009
theorem B5763581 : Blo 1707054 5763581 := bstep (se 3 (by rfl) ⟨1080671, by rfl⟩ : syracuseStep 5763581 = 2161343) B2161343
theorem B2560799 : Blo 1707054 2560799 := bstep (se 1 (by rfl) ⟨1920599, by rfl⟩ : syracuseStep 2560799 = 3841199) B3841199
theorem B1823591 : Blo 1707054 1823591 := bstep (se 1 (by rfl) ⟨1367693, by rfl⟩ : syracuseStep 1823591 = 2735387) B2735387
theorem B124589015 : Blo 1707054 124589015 := bstep (se 1 (by rfl) ⟨93441761, by rfl⟩ : syracuseStep 124589015 = 186883523) B186883523
theorem B2561183 : Blo 1707054 2561183 := bstep (se 1 (by rfl) ⟨1920887, by rfl⟩ : syracuseStep 2561183 = 3841775) B3841775
theorem B1922287 : Blo 1707054 1922287 := bstep (se 1 (by rfl) ⟨1441715, by rfl⟩ : syracuseStep 1922287 = 2883431) B2883431
theorem B4322555 : Blo 1707054 4322555 := bstep (se 1 (by rfl) ⟨3241916, by rfl⟩ : syracuseStep 4322555 = 6483833) B6483833
theorem B10949899 : Blo 1707054 10949899 := bstep (se 1 (by rfl) ⟨8212424, by rfl⟩ : syracuseStep 10949899 = 16424849) B16424849
theorem B2561663 : Blo 1707054 2561663 := bstep (se 1 (by rfl) ⟨1921247, by rfl⟩ : syracuseStep 2561663 = 3842495) B3842495
theorem B252827351 : Blo 1707054 252827351 := bstep (se 1 (by rfl) ⟨189620513, by rfl⟩ : syracuseStep 252827351 = 379241027) B379241027
theorem B1824539 : Blo 1707054 1824539 := bstep (se 1 (by rfl) ⟨1368404, by rfl⟩ : syracuseStep 1824539 = 2736809) B2736809
theorem B8648531 : Blo 1707054 8648531 := bstep (se 1 (by rfl) ⟨6486398, by rfl⟩ : syracuseStep 8648531 = 12972797) B12972797
theorem B17537417 : Blo 1707054 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B2562779 : Blo 1707054 2562779 := bstep (se 1 (by rfl) ⟨1922084, by rfl⟩ : syracuseStep 2562779 = 3844169) B3844169
theorem B4324225 : Blo 1707054 4324225 := bstep (se 2 (by rfl) ⟨1621584, by rfl⟩ : syracuseStep 4324225 = 3243169) B3243169
theorem B2563307 : Blo 1707054 2563307 := bstep (se 1 (by rfl) ⟨1922480, by rfl⟩ : syracuseStep 2563307 = 3844961) B3844961
theorem B12967451 : Blo 1707054 12967451 := bstep (se 1 (by rfl) ⟨9725588, by rfl⟩ : syracuseStep 12967451 = 19451177) B19451177
theorem B3842387 : Blo 1707054 3842387 := bstep (se 1 (by rfl) ⟨2881790, by rfl⟩ : syracuseStep 3842387 = 5763581) B5763581
theorem B83059343 : Blo 1707054 83059343 := bstep (se 1 (by rfl) ⟨62294507, by rfl⟩ : syracuseStep 83059343 = 124589015) B124589015
theorem B70091831 : Blo 1707054 70091831 := bstep (se 1 (by rfl) ⟨52568873, by rfl⟩ : syracuseStep 70091831 = 105137747) B105137747
theorem B168551567 : Blo 1707054 168551567 := bstep (se 1 (by rfl) ⟨126413675, by rfl⟩ : syracuseStep 168551567 = 252827351) B252827351
theorem B33285593 : Blo 1707054 33285593 := bstep (se 2 (by rfl) ⟨12482097, by rfl⟩ : syracuseStep 33285593 = 24964195) B24964195
theorem B11691611 : Blo 1707054 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B14599865 : Blo 1707054 14599865 := bstep (se 2 (by rfl) ⟨5474949, by rfl⟩ : syracuseStep 14599865 = 10949899) B10949899
theorem B5474027 : Blo 1707054 5474027 := bstep (se 1 (by rfl) ⟨4105520, by rfl⟩ : syracuseStep 5474027 = 8211041) B8211041
theorem B8644967 : Blo 1707054 8644967 := bstep (se 1 (by rfl) ⟨6483725, by rfl⟩ : syracuseStep 8644967 = 12967451) B12967451
theorem B1707199 : Blo 1707054 1707199 := bstep (se 1 (by rfl) ⟨1280399, by rfl⟩ : syracuseStep 1707199 = 2560799) B2560799
theorem B1707455 : Blo 1707054 1707455 := bstep (se 1 (by rfl) ⟨1280591, by rfl⟩ : syracuseStep 1707455 = 2561183) B2561183
theorem B1707775 : Blo 1707054 1707775 := bstep (se 1 (by rfl) ⟨1280831, by rfl⟩ : syracuseStep 1707775 = 2561663) B2561663
theorem B1708519 : Blo 1707054 1708519 := bstep (se 1 (by rfl) ⟨1281389, by rfl⟩ : syracuseStep 1708519 = 2562779) B2562779
theorem B1708871 : Blo 1707054 1708871 := bstep (se 1 (by rfl) ⟨1281653, by rfl⟩ : syracuseStep 1708871 = 2563307) B2563307
theorem B6484819 : Blo 1707054 6484819 := bstep (se 1 (by rfl) ⟨4863614, by rfl⟩ : syracuseStep 6484819 = 9727229) B9727229
theorem B4862909 : Blo 1707054 4862909 := bstep (se 3 (by rfl) ⟨911795, by rfl⟩ : syracuseStep 4862909 = 1823591) B1823591
theorem B4102235 : Blo 1707054 4102235 := bstep (se 1 (by rfl) ⟨3076676, by rfl⟩ : syracuseStep 4102235 = 6153353) B6153353
theorem B11098235 : Blo 1707054 11098235 := bstep (se 1 (by rfl) ⟨8323676, by rfl⟩ : syracuseStep 11098235 = 16647353) B16647353
theorem B2881703 : Blo 1707054 2881703 := bstep (se 1 (by rfl) ⟨2161277, by rfl⟩ : syracuseStep 2881703 = 4322555) B4322555
theorem B2562215 : Blo 1707054 2562215 := bstep (se 1 (by rfl) ⟨1921661, by rfl⟩ : syracuseStep 2562215 = 3843323) B3843323
theorem B2562287 : Blo 1707054 2562287 := bstep (se 1 (by rfl) ⟨1921715, by rfl⟩ : syracuseStep 2562287 = 3843431) B3843431
theorem B22485235 : Blo 1707054 22485235 := bstep (se 1 (by rfl) ⟨16863926, by rfl⟩ : syracuseStep 22485235 = 33727853) B33727853
theorem B46741897 : Blo 1707054 46741897 := bstep (se 2 (by rfl) ⟨17528211, by rfl⟩ : syracuseStep 46741897 = 35056423) B35056423
theorem B5765633 : Blo 1707054 5765633 := bstep (se 2 (by rfl) ⟨2162112, by rfl⟩ : syracuseStep 5765633 = 4324225) B4324225
theorem B5765687 : Blo 1707054 5765687 := bstep (se 1 (by rfl) ⟨4324265, by rfl⟩ : syracuseStep 5765687 = 8648531) B8648531
theorem B2563049 : Blo 1707054 2563049 := bstep (se 2 (by rfl) ⟨961143, by rfl⟩ : syracuseStep 2563049 = 1922287) B1922287
theorem B4865437 : Blo 1707054 4865437 := bstep (se 3 (by rfl) ⟨912269, by rfl⟩ : syracuseStep 4865437 = 1824539) B1824539
theorem B9723563 : Blo 1707054 9723563 := bstep (se 1 (by rfl) ⟨7292672, by rfl⟩ : syracuseStep 9723563 = 14585345) B14585345
theorem B46727887 : Blo 1707054 46727887 := bstep (se 1 (by rfl) ⟨35045915, by rfl⟩ : syracuseStep 46727887 = 70091831) B70091831
theorem B9733243 : Blo 1707054 9733243 := bstep (se 1 (by rfl) ⟨7299932, by rfl⟩ : syracuseStep 9733243 = 14599865) B14599865
theorem B7398823 : Blo 1707054 7398823 := bstep (se 1 (by rfl) ⟨5549117, by rfl⟩ : syracuseStep 7398823 = 11098235) B11098235
theorem B3843755 : Blo 1707054 3843755 := bstep (se 1 (by rfl) ⟨2882816, by rfl⟩ : syracuseStep 3843755 = 5765633) B5765633
theorem B3843791 : Blo 1707054 3843791 := bstep (se 1 (by rfl) ⟨2882843, by rfl⟩ : syracuseStep 3843791 = 5765687) B5765687
theorem B6482375 : Blo 1707054 6482375 := bstep (se 1 (by rfl) ⟨4861781, by rfl⟩ : syracuseStep 6482375 = 9723563) B9723563
theorem B55372895 : Blo 1707054 55372895 := bstep (se 1 (by rfl) ⟨41529671, by rfl⟩ : syracuseStep 55372895 = 83059343) B83059343
theorem B7794407 : Blo 1707054 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B8646425 : Blo 1707054 8646425 := bstep (se 2 (by rfl) ⟨3242409, by rfl⟩ : syracuseStep 8646425 = 6484819) B6484819
theorem B1921135 : Blo 1707054 1921135 := bstep (se 1 (by rfl) ⟨1440851, by rfl⟩ : syracuseStep 1921135 = 2881703) B2881703
theorem B1708143 : Blo 1707054 1708143 := bstep (se 1 (by rfl) ⟨1281107, by rfl⟩ : syracuseStep 1708143 = 2562215) B2562215
theorem B1708191 : Blo 1707054 1708191 := bstep (se 1 (by rfl) ⟨1281143, by rfl⟩ : syracuseStep 1708191 = 2562287) B2562287
theorem B5763311 : Blo 1707054 5763311 := bstep (se 1 (by rfl) ⟨4322483, by rfl⟩ : syracuseStep 5763311 = 8644967) B8644967
theorem B1708699 : Blo 1707054 1708699 := bstep (se 1 (by rfl) ⟨1281524, by rfl⟩ : syracuseStep 1708699 = 2563049) B2563049
theorem B2561591 : Blo 1707054 2561591 := bstep (se 1 (by rfl) ⟨1921193, by rfl⟩ : syracuseStep 2561591 = 3842387) B3842387
theorem B29980313 : Blo 1707054 29980313 := bstep (se 2 (by rfl) ⟨11242617, by rfl⟩ : syracuseStep 29980313 = 22485235) B22485235
theorem B62322529 : Blo 1707054 62322529 := bstep (se 2 (by rfl) ⟨23370948, by rfl⟩ : syracuseStep 62322529 = 46741897) B46741897
theorem B3241939 : Blo 1707054 3241939 := bstep (se 1 (by rfl) ⟨2431454, by rfl⟩ : syracuseStep 3241939 = 4862909) B4862909
theorem B112367711 : Blo 1707054 112367711 := bstep (se 1 (by rfl) ⟨84275783, by rfl⟩ : syracuseStep 112367711 = 168551567) B168551567
theorem B22190395 : Blo 1707054 22190395 := bstep (se 1 (by rfl) ⟨16642796, by rfl⟩ : syracuseStep 22190395 = 33285593) B33285593
theorem B2734823 : Blo 1707054 2734823 := bstep (se 1 (by rfl) ⟨2051117, by rfl⟩ : syracuseStep 2734823 = 4102235) B4102235
theorem B6487249 : Blo 1707054 6487249 := bstep (se 2 (by rfl) ⟨2432718, by rfl⟩ : syracuseStep 6487249 = 4865437) B4865437
theorem B14597405 : Blo 1707054 14597405 := bstep (se 3 (by rfl) ⟨2737013, by rfl⟩ : syracuseStep 14597405 = 5474027) B5474027
theorem B3842207 : Blo 1707054 3842207 := bstep (se 1 (by rfl) ⟨2881655, by rfl⟩ : syracuseStep 3842207 = 5763311) B5763311
theorem B12977657 : Blo 1707054 12977657 := bstep (se 2 (by rfl) ⟨4866621, by rfl⟩ : syracuseStep 12977657 = 9733243) B9733243
theorem B9865097 : Blo 1707054 9865097 := bstep (se 2 (by rfl) ⟨3699411, by rfl⟩ : syracuseStep 9865097 = 7398823) B7398823
theorem B7292861 : Blo 1707054 7292861 := bstep (se 3 (by rfl) ⟨1367411, by rfl⟩ : syracuseStep 7292861 = 2734823) B2734823
theorem B36915263 : Blo 1707054 36915263 := bstep (se 1 (by rfl) ⟨27686447, by rfl⟩ : syracuseStep 36915263 = 55372895) B55372895
theorem B5196271 : Blo 1707054 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B62303849 : Blo 1707054 62303849 := bstep (se 2 (by rfl) ⟨23363943, by rfl⟩ : syracuseStep 62303849 = 46727887) B46727887
theorem B1707727 : Blo 1707054 1707727 := bstep (se 1 (by rfl) ⟨1280795, by rfl⟩ : syracuseStep 1707727 = 2561591) B2561591
theorem B74911807 : Blo 1707054 74911807 := bstep (se 1 (by rfl) ⟨56183855, by rfl⟩ : syracuseStep 74911807 = 112367711) B112367711
theorem B4321583 : Blo 1707054 4321583 := bstep (se 1 (by rfl) ⟨3241187, by rfl⟩ : syracuseStep 4321583 = 6482375) B6482375
theorem B83096705 : Blo 1707054 83096705 := bstep (se 2 (by rfl) ⟨31161264, by rfl⟩ : syracuseStep 83096705 = 62322529) B62322529
theorem B5764283 : Blo 1707054 5764283 := bstep (se 1 (by rfl) ⟨4323212, by rfl⟩ : syracuseStep 5764283 = 8646425) B8646425
theorem B4322585 : Blo 1707054 4322585 := bstep (se 2 (by rfl) ⟨1620969, by rfl⟩ : syracuseStep 4322585 = 3241939) B3241939
theorem B2561513 : Blo 1707054 2561513 := bstep (se 2 (by rfl) ⟨960567, by rfl⟩ : syracuseStep 2561513 = 1921135) B1921135
theorem B29587193 : Blo 1707054 29587193 := bstep (se 2 (by rfl) ⟨11095197, by rfl⟩ : syracuseStep 29587193 = 22190395) B22190395
theorem B19986875 : Blo 1707054 19986875 := bstep (se 1 (by rfl) ⟨14990156, by rfl⟩ : syracuseStep 19986875 = 29980313) B29980313
theorem B2562503 : Blo 1707054 2562503 := bstep (se 1 (by rfl) ⟨1921877, by rfl⟩ : syracuseStep 2562503 = 3843755) B3843755
theorem B2562527 : Blo 1707054 2562527 := bstep (se 1 (by rfl) ⟨1921895, by rfl⟩ : syracuseStep 2562527 = 3843791) B3843791
theorem B8649665 : Blo 1707054 8649665 := bstep (se 2 (by rfl) ⟨3243624, by rfl⟩ : syracuseStep 8649665 = 6487249) B6487249
theorem B9731603 : Blo 1707054 9731603 := bstep (se 1 (by rfl) ⟨7298702, by rfl⟩ : syracuseStep 9731603 = 14597405) B14597405
theorem B3842855 : Blo 1707054 3842855 := bstep (se 1 (by rfl) ⟨2882141, by rfl⟩ : syracuseStep 3842855 = 5764283) B5764283
theorem B8651771 : Blo 1707054 8651771 := bstep (se 1 (by rfl) ⟨6488828, by rfl⟩ : syracuseStep 8651771 = 12977657) B12977657
theorem B24610175 : Blo 1707054 24610175 := bstep (se 1 (by rfl) ⟨18457631, by rfl⟩ : syracuseStep 24610175 = 36915263) B36915263
theorem B41535899 : Blo 1707054 41535899 := bstep (se 1 (by rfl) ⟨31151924, by rfl⟩ : syracuseStep 41535899 = 62303849) B62303849
theorem B55397803 : Blo 1707054 55397803 := bstep (se 1 (by rfl) ⟨41548352, by rfl⟩ : syracuseStep 55397803 = 83096705) B83096705
theorem B1707675 : Blo 1707054 1707675 := bstep (se 1 (by rfl) ⟨1280756, by rfl⟩ : syracuseStep 1707675 = 2561513) B2561513
theorem B4861907 : Blo 1707054 4861907 := bstep (se 1 (by rfl) ⟨3646430, by rfl⟩ : syracuseStep 4861907 = 7292861) B7292861
theorem B13324583 : Blo 1707054 13324583 := bstep (se 1 (by rfl) ⟨9993437, by rfl⟩ : syracuseStep 13324583 = 19986875) B19986875
theorem B1708335 : Blo 1707054 1708335 := bstep (se 1 (by rfl) ⟨1281251, by rfl⟩ : syracuseStep 1708335 = 2562503) B2562503
theorem B1708351 : Blo 1707054 1708351 := bstep (se 1 (by rfl) ⟨1281263, by rfl⟩ : syracuseStep 1708351 = 2562527) B2562527
theorem B99882409 : Blo 1707054 99882409 := bstep (se 2 (by rfl) ⟨37455903, by rfl⟩ : syracuseStep 99882409 = 74911807) B74911807
theorem B2561471 : Blo 1707054 2561471 := bstep (se 1 (by rfl) ⟨1921103, by rfl⟩ : syracuseStep 2561471 = 3842207) B3842207
theorem B2881055 : Blo 1707054 2881055 := bstep (se 1 (by rfl) ⟨2160791, by rfl⟩ : syracuseStep 2881055 = 4321583) B4321583
theorem B6928361 : Blo 1707054 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B2881723 : Blo 1707054 2881723 := bstep (se 1 (by rfl) ⟨2161292, by rfl⟩ : syracuseStep 2881723 = 4322585) B4322585
theorem B19724795 : Blo 1707054 19724795 := bstep (se 1 (by rfl) ⟨14793596, by rfl⟩ : syracuseStep 19724795 = 29587193) B29587193
theorem B6576731 : Blo 1707054 6576731 := bstep (se 1 (by rfl) ⟨4932548, by rfl⟩ : syracuseStep 6576731 = 9865097) B9865097
theorem B5766443 : Blo 1707054 5766443 := bstep (se 1 (by rfl) ⟨4324832, by rfl⟩ : syracuseStep 5766443 = 8649665) B8649665
theorem B6487735 : Blo 1707054 6487735 := bstep (se 1 (by rfl) ⟨4865801, by rfl⟩ : syracuseStep 6487735 = 9731603) B9731603
theorem B3842297 : Blo 1707054 3842297 := bstep (se 2 (by rfl) ⟨1440861, by rfl⟩ : syracuseStep 3842297 = 2881723) B2881723
theorem B5767847 : Blo 1707054 5767847 := bstep (se 1 (by rfl) ⟨4325885, by rfl⟩ : syracuseStep 5767847 = 8651771) B8651771
theorem B27690599 : Blo 1707054 27690599 := bstep (se 1 (by rfl) ⟨20767949, by rfl⟩ : syracuseStep 27690599 = 41535899) B41535899
theorem B13149863 : Blo 1707054 13149863 := bstep (se 1 (by rfl) ⟨9862397, by rfl⟩ : syracuseStep 13149863 = 19724795) B19724795
theorem B4384487 : Blo 1707054 4384487 := bstep (se 1 (by rfl) ⟨3288365, by rfl⟩ : syracuseStep 4384487 = 6576731) B6576731
theorem B3844295 : Blo 1707054 3844295 := bstep (se 1 (by rfl) ⟨2883221, by rfl⟩ : syracuseStep 3844295 = 5766443) B5766443
theorem B8883055 : Blo 1707054 8883055 := bstep (se 1 (by rfl) ⟨6662291, by rfl⟩ : syracuseStep 8883055 = 13324583) B13324583
theorem B1707647 : Blo 1707054 1707647 := bstep (se 1 (by rfl) ⟨1280735, by rfl⟩ : syracuseStep 1707647 = 2561471) B2561471
theorem B1920703 : Blo 1707054 1920703 := bstep (se 1 (by rfl) ⟨1440527, by rfl⟩ : syracuseStep 1920703 = 2881055) B2881055
theorem B73863737 : Blo 1707054 73863737 := bstep (se 2 (by rfl) ⟨27698901, by rfl⟩ : syracuseStep 73863737 = 55397803) B55397803
theorem B3241271 : Blo 1707054 3241271 := bstep (se 1 (by rfl) ⟨2430953, by rfl⟩ : syracuseStep 3241271 = 4861907) B4861907
theorem B2561903 : Blo 1707054 2561903 := bstep (se 1 (by rfl) ⟨1921427, by rfl⟩ : syracuseStep 2561903 = 3842855) B3842855
theorem B16406783 : Blo 1707054 16406783 := bstep (se 1 (by rfl) ⟨12305087, by rfl⟩ : syracuseStep 16406783 = 24610175) B24610175
theorem B4618907 : Blo 1707054 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B133176545 : Blo 1707054 133176545 := bstep (se 2 (by rfl) ⟨49941204, by rfl⟩ : syracuseStep 133176545 = 99882409) B99882409
theorem B8650313 : Blo 1707054 8650313 := bstep (se 2 (by rfl) ⟨3243867, by rfl⟩ : syracuseStep 8650313 = 6487735) B6487735
theorem B49242491 : Blo 1707054 49242491 := bstep (se 1 (by rfl) ⟨36931868, by rfl⟩ : syracuseStep 49242491 = 73863737) B73863737
theorem B8766575 : Blo 1707054 8766575 := bstep (se 1 (by rfl) ⟨6574931, by rfl⟩ : syracuseStep 8766575 = 13149863) B13149863
theorem B10937855 : Blo 1707054 10937855 := bstep (se 1 (by rfl) ⟨8203391, by rfl⟩ : syracuseStep 10937855 = 16406783) B16406783
theorem B11691965 : Blo 1707054 11691965 := bstep (se 3 (by rfl) ⟨2192243, by rfl⟩ : syracuseStep 11691965 = 4384487) B4384487
theorem B3845231 : Blo 1707054 3845231 := bstep (se 1 (by rfl) ⟨2883923, by rfl⟩ : syracuseStep 3845231 = 5767847) B5767847
theorem B18460399 : Blo 1707054 18460399 := bstep (se 1 (by rfl) ⟨13845299, by rfl⟩ : syracuseStep 18460399 = 27690599) B27690599
theorem B1707935 : Blo 1707054 1707935 := bstep (se 1 (by rfl) ⟨1280951, by rfl⟩ : syracuseStep 1707935 = 2561903) B2561903
theorem B2560937 : Blo 1707054 2560937 := bstep (se 2 (by rfl) ⟨960351, by rfl⟩ : syracuseStep 2560937 = 1920703) B1920703
theorem B2561531 : Blo 1707054 2561531 := bstep (se 1 (by rfl) ⟨1921148, by rfl⟩ : syracuseStep 2561531 = 3842297) B3842297
theorem B2160847 : Blo 1707054 2160847 := bstep (se 1 (by rfl) ⟨1620635, by rfl⟩ : syracuseStep 2160847 = 3241271) B3241271
theorem B11844073 : Blo 1707054 11844073 := bstep (se 2 (by rfl) ⟨4441527, by rfl⟩ : syracuseStep 11844073 = 8883055) B8883055
theorem B2562863 : Blo 1707054 2562863 := bstep (se 1 (by rfl) ⟨1922147, by rfl⟩ : syracuseStep 2562863 = 3844295) B3844295
theorem B3079271 : Blo 1707054 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B88784363 : Blo 1707054 88784363 := bstep (se 1 (by rfl) ⟨66588272, by rfl⟩ : syracuseStep 88784363 = 133176545) B133176545
theorem B5766875 : Blo 1707054 5766875 := bstep (se 1 (by rfl) ⟨4325156, by rfl⟩ : syracuseStep 5766875 = 8650313) B8650313
theorem B7291903 : Blo 1707054 7291903 := bstep (se 1 (by rfl) ⟨5468927, by rfl⟩ : syracuseStep 7291903 = 10937855) B10937855
theorem B236758301 : Blo 1707054 236758301 := bstep (se 3 (by rfl) ⟨44392181, by rfl⟩ : syracuseStep 236758301 = 88784363) B88784363
theorem B3844583 : Blo 1707054 3844583 := bstep (se 1 (by rfl) ⟨2883437, by rfl⟩ : syracuseStep 3844583 = 5766875) B5766875
theorem B32828327 : Blo 1707054 32828327 := bstep (se 1 (by rfl) ⟨24621245, by rfl⟩ : syracuseStep 32828327 = 49242491) B49242491
theorem B1707291 : Blo 1707054 1707291 := bstep (se 1 (by rfl) ⟨1280468, by rfl⟩ : syracuseStep 1707291 = 2560937) B2560937
theorem B5844383 : Blo 1707054 5844383 := bstep (se 1 (by rfl) ⟨4383287, by rfl⟩ : syracuseStep 5844383 = 8766575) B8766575
theorem B1707687 : Blo 1707054 1707687 := bstep (se 1 (by rfl) ⟨1280765, by rfl⟩ : syracuseStep 1707687 = 2561531) B2561531
theorem B7794643 : Blo 1707054 7794643 := bstep (se 1 (by rfl) ⟨5845982, by rfl⟩ : syracuseStep 7794643 = 11691965) B11691965
theorem B1708575 : Blo 1707054 1708575 := bstep (se 1 (by rfl) ⟨1281431, by rfl⟩ : syracuseStep 1708575 = 2562863) B2562863
theorem B2052847 : Blo 1707054 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B24613865 : Blo 1707054 24613865 := bstep (se 2 (by rfl) ⟨9230199, by rfl⟩ : syracuseStep 24613865 = 18460399) B18460399
theorem B2881129 : Blo 1707054 2881129 := bstep (se 2 (by rfl) ⟨1080423, by rfl⟩ : syracuseStep 2881129 = 2160847) B2160847
theorem B15792097 : Blo 1707054 15792097 := bstep (se 2 (by rfl) ⟨5922036, by rfl⟩ : syracuseStep 15792097 = 11844073) B11844073
theorem B2563487 : Blo 1707054 2563487 := bstep (se 1 (by rfl) ⟨1922615, by rfl⟩ : syracuseStep 2563487 = 3845231) B3845231
theorem B16409243 : Blo 1707054 16409243 := bstep (se 1 (by rfl) ⟨12306932, by rfl⟩ : syracuseStep 16409243 = 24613865) B24613865
theorem B21056129 : Blo 1707054 21056129 := bstep (se 2 (by rfl) ⟨7896048, by rfl⟩ : syracuseStep 21056129 = 15792097) B15792097
theorem B157838867 : Blo 1707054 157838867 := bstep (se 1 (by rfl) ⟨118379150, by rfl⟩ : syracuseStep 157838867 = 236758301) B236758301
theorem B10948517 : Blo 1707054 10948517 := bstep (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) B2052847
theorem B21885551 : Blo 1707054 21885551 := bstep (se 1 (by rfl) ⟨16414163, by rfl⟩ : syracuseStep 21885551 = 32828327) B32828327
theorem B3896255 : Blo 1707054 3896255 := bstep (se 1 (by rfl) ⟨2922191, by rfl⟩ : syracuseStep 3896255 = 5844383) B5844383
theorem B1708991 : Blo 1707054 1708991 := bstep (se 1 (by rfl) ⟨1281743, by rfl⟩ : syracuseStep 1708991 = 2563487) B2563487
theorem B10392857 : Blo 1707054 10392857 := bstep (se 2 (by rfl) ⟨3897321, by rfl⟩ : syracuseStep 10392857 = 7794643) B7794643
theorem B9722537 : Blo 1707054 9722537 := bstep (se 2 (by rfl) ⟨3645951, by rfl⟩ : syracuseStep 9722537 = 7291903) B7291903
theorem B2563055 : Blo 1707054 2563055 := bstep (se 1 (by rfl) ⟨1922291, by rfl⟩ : syracuseStep 2563055 = 3844583) B3844583
theorem B3841505 : Blo 1707054 3841505 := bstep (se 2 (by rfl) ⟨1440564, by rfl⟩ : syracuseStep 3841505 = 2881129) B2881129
theorem B14590367 : Blo 1707054 14590367 := bstep (se 1 (by rfl) ⟨10942775, by rfl⟩ : syracuseStep 14590367 = 21885551) B21885551
theorem B2597503 : Blo 1707054 2597503 := bstep (se 1 (by rfl) ⟨1948127, by rfl⟩ : syracuseStep 2597503 = 3896255) B3896255
theorem B6481691 : Blo 1707054 6481691 := bstep (se 1 (by rfl) ⟨4861268, by rfl⟩ : syracuseStep 6481691 = 9722537) B9722537
theorem B10939495 : Blo 1707054 10939495 := bstep (se 1 (by rfl) ⟨8204621, by rfl⟩ : syracuseStep 10939495 = 16409243) B16409243
theorem B14037419 : Blo 1707054 14037419 := bstep (se 1 (by rfl) ⟨10528064, by rfl⟩ : syracuseStep 14037419 = 21056129) B21056129
theorem B1708703 : Blo 1707054 1708703 := bstep (se 1 (by rfl) ⟨1281527, by rfl⟩ : syracuseStep 1708703 = 2563055) B2563055
theorem B2561003 : Blo 1707054 2561003 := bstep (se 1 (by rfl) ⟨1920752, by rfl⟩ : syracuseStep 2561003 = 3841505) B3841505
theorem B6928571 : Blo 1707054 6928571 := bstep (se 1 (by rfl) ⟨5196428, by rfl⟩ : syracuseStep 6928571 = 10392857) B10392857
theorem B105225911 : Blo 1707054 105225911 := bstep (se 1 (by rfl) ⟨78919433, by rfl⟩ : syracuseStep 105225911 = 157838867) B157838867
theorem B7299011 : Blo 1707054 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B70150607 : Blo 1707054 70150607 := bstep (se 1 (by rfl) ⟨52612955, by rfl⟩ : syracuseStep 70150607 = 105225911) B105225911
theorem B9726911 : Blo 1707054 9726911 := bstep (se 1 (by rfl) ⟨7295183, by rfl⟩ : syracuseStep 9726911 = 14590367) B14590367
theorem B1707335 : Blo 1707054 1707335 := bstep (se 1 (by rfl) ⟨1280501, by rfl⟩ : syracuseStep 1707335 = 2561003) B2561003
theorem B37433117 : Blo 1707054 37433117 := bstep (se 3 (by rfl) ⟨7018709, by rfl⟩ : syracuseStep 37433117 = 14037419) B14037419
theorem B4321127 : Blo 1707054 4321127 := bstep (se 1 (by rfl) ⟨3240845, by rfl⟩ : syracuseStep 4321127 = 6481691) B6481691
theorem B14585993 : Blo 1707054 14585993 := bstep (se 2 (by rfl) ⟨5469747, by rfl⟩ : syracuseStep 14585993 = 10939495) B10939495
theorem B3463337 : Blo 1707054 3463337 := bstep (se 2 (by rfl) ⟨1298751, by rfl⟩ : syracuseStep 3463337 = 2597503) B2597503
theorem B4619047 : Blo 1707054 4619047 := bstep (se 1 (by rfl) ⟨3464285, by rfl⟩ : syracuseStep 4619047 = 6928571) B6928571
theorem B4866007 : Blo 1707054 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B9723995 : Blo 1707054 9723995 := bstep (se 1 (by rfl) ⟨7292996, by rfl⟩ : syracuseStep 9723995 = 14585993) B14585993
theorem B99821645 : Blo 1707054 99821645 := bstep (se 3 (by rfl) ⟨18716558, by rfl⟩ : syracuseStep 99821645 = 37433117) B37433117
theorem B9235565 : Blo 1707054 9235565 := bstep (se 3 (by rfl) ⟨1731668, by rfl⟩ : syracuseStep 9235565 = 3463337) B3463337
theorem B6484607 : Blo 1707054 6484607 := bstep (se 1 (by rfl) ⟨4863455, by rfl⟩ : syracuseStep 6484607 = 9726911) B9726911
theorem B2880751 : Blo 1707054 2880751 := bstep (se 1 (by rfl) ⟨2160563, by rfl⟩ : syracuseStep 2880751 = 4321127) B4321127
theorem B6158729 : Blo 1707054 6158729 := bstep (se 2 (by rfl) ⟨2309523, by rfl⟩ : syracuseStep 6158729 = 4619047) B4619047
theorem B46767071 : Blo 1707054 46767071 := bstep (se 1 (by rfl) ⟨35075303, by rfl⟩ : syracuseStep 46767071 = 70150607) B70150607
theorem B6488009 : Blo 1707054 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B4105819 : Blo 1707054 4105819 := bstep (se 1 (by rfl) ⟨3079364, by rfl⟩ : syracuseStep 4105819 = 6158729) B6158729
theorem B6482663 : Blo 1707054 6482663 := bstep (se 1 (by rfl) ⟨4861997, by rfl⟩ : syracuseStep 6482663 = 9723995) B9723995
theorem B66547763 : Blo 1707054 66547763 := bstep (se 1 (by rfl) ⟨49910822, by rfl⟩ : syracuseStep 66547763 = 99821645) B99821645
theorem B6157043 : Blo 1707054 6157043 := bstep (se 1 (by rfl) ⟨4617782, by rfl⟩ : syracuseStep 6157043 = 9235565) B9235565
theorem B4323071 : Blo 1707054 4323071 := bstep (se 1 (by rfl) ⟨3242303, by rfl⟩ : syracuseStep 4323071 = 6484607) B6484607
theorem B3841001 : Blo 1707054 3841001 := bstep (se 2 (by rfl) ⟨1440375, by rfl⟩ : syracuseStep 3841001 = 2880751) B2880751
theorem B31178047 : Blo 1707054 31178047 := bstep (se 1 (by rfl) ⟨23383535, by rfl⟩ : syracuseStep 31178047 = 46767071) B46767071
theorem B4325339 : Blo 1707054 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B21897701 : Blo 1707054 21897701 := bstep (se 4 (by rfl) ⟨2052909, by rfl⟩ : syracuseStep 21897701 = 4105819) B4105819
theorem B4104695 : Blo 1707054 4104695 := bstep (se 1 (by rfl) ⟨3078521, by rfl⟩ : syracuseStep 4104695 = 6157043) B6157043
theorem B41570729 : Blo 1707054 41570729 := bstep (se 2 (by rfl) ⟨15589023, by rfl⟩ : syracuseStep 41570729 = 31178047) B31178047
theorem B4321775 : Blo 1707054 4321775 := bstep (se 1 (by rfl) ⟨3241331, by rfl⟩ : syracuseStep 4321775 = 6482663) B6482663
theorem B2560667 : Blo 1707054 2560667 := bstep (se 1 (by rfl) ⟨1920500, by rfl⟩ : syracuseStep 2560667 = 3841001) B3841001
theorem B44365175 : Blo 1707054 44365175 := bstep (se 1 (by rfl) ⟨33273881, by rfl⟩ : syracuseStep 44365175 = 66547763) B66547763
theorem B2882047 : Blo 1707054 2882047 := bstep (se 1 (by rfl) ⟨2161535, by rfl⟩ : syracuseStep 2882047 = 4323071) B4323071
theorem B2883559 : Blo 1707054 2883559 := bstep (se 1 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 2883559 = 4325339) B4325339
theorem B27713819 : Blo 1707054 27713819 := bstep (se 1 (by rfl) ⟨20785364, by rfl⟩ : syracuseStep 27713819 = 41570729) B41570729
theorem B14598467 : Blo 1707054 14598467 := bstep (se 1 (by rfl) ⟨10948850, by rfl⟩ : syracuseStep 14598467 = 21897701) B21897701
theorem B3842729 : Blo 1707054 3842729 := bstep (se 2 (by rfl) ⟨1441023, by rfl⟩ : syracuseStep 3842729 = 2882047) B2882047
theorem B10945853 : Blo 1707054 10945853 := bstep (se 3 (by rfl) ⟨2052347, by rfl⟩ : syracuseStep 10945853 = 4104695) B4104695
theorem B3844745 : Blo 1707054 3844745 := bstep (se 2 (by rfl) ⟨1441779, by rfl⟩ : syracuseStep 3844745 = 2883559) B2883559
theorem B1707111 : Blo 1707054 1707111 := bstep (se 1 (by rfl) ⟨1280333, by rfl⟩ : syracuseStep 1707111 = 2560667) B2560667
theorem B29576783 : Blo 1707054 29576783 := bstep (se 1 (by rfl) ⟨22182587, by rfl⟩ : syracuseStep 29576783 = 44365175) B44365175
theorem B2881183 : Blo 1707054 2881183 := bstep (se 1 (by rfl) ⟨2160887, by rfl⟩ : syracuseStep 2881183 = 4321775) B4321775
theorem B9732311 : Blo 1707054 9732311 := bstep (se 1 (by rfl) ⟨7299233, by rfl⟩ : syracuseStep 9732311 = 14598467) B14598467
theorem B18475879 : Blo 1707054 18475879 := bstep (se 1 (by rfl) ⟨13856909, by rfl⟩ : syracuseStep 18475879 = 27713819) B27713819
theorem B2561819 : Blo 1707054 2561819 := bstep (se 1 (by rfl) ⟨1921364, by rfl⟩ : syracuseStep 2561819 = 3842729) B3842729
theorem B7297235 : Blo 1707054 7297235 := bstep (se 1 (by rfl) ⟨5472926, by rfl⟩ : syracuseStep 7297235 = 10945853) B10945853
theorem B78871421 : Blo 1707054 78871421 := bstep (se 3 (by rfl) ⟨14788391, by rfl⟩ : syracuseStep 78871421 = 29576783) B29576783
theorem B2563163 : Blo 1707054 2563163 := bstep (se 1 (by rfl) ⟨1922372, by rfl⟩ : syracuseStep 2563163 = 3844745) B3844745
theorem B3841577 : Blo 1707054 3841577 := bstep (se 2 (by rfl) ⟨1440591, by rfl⟩ : syracuseStep 3841577 = 2881183) B2881183
theorem B6488207 : Blo 1707054 6488207 := bstep (se 1 (by rfl) ⟨4866155, by rfl⟩ : syracuseStep 6488207 = 9732311) B9732311
theorem B24634505 : Blo 1707054 24634505 := bstep (se 2 (by rfl) ⟨9237939, by rfl⟩ : syracuseStep 24634505 = 18475879) B18475879
theorem B1707879 : Blo 1707054 1707879 := bstep (se 1 (by rfl) ⟨1280909, by rfl⟩ : syracuseStep 1707879 = 2561819) B2561819
theorem B52580947 : Blo 1707054 52580947 := bstep (se 1 (by rfl) ⟨39435710, by rfl⟩ : syracuseStep 52580947 = 78871421) B78871421
theorem B1708775 : Blo 1707054 1708775 := bstep (se 1 (by rfl) ⟨1281581, by rfl⟩ : syracuseStep 1708775 = 2563163) B2563163
theorem B2561051 : Blo 1707054 2561051 := bstep (se 1 (by rfl) ⟨1920788, by rfl⟩ : syracuseStep 2561051 = 3841577) B3841577
theorem B4864823 : Blo 1707054 4864823 := bstep (se 1 (by rfl) ⟨3648617, by rfl⟩ : syracuseStep 4864823 = 7297235) B7297235
theorem B4325471 : Blo 1707054 4325471 := bstep (se 1 (by rfl) ⟨3244103, by rfl⟩ : syracuseStep 4325471 = 6488207) B6488207
theorem B70107929 : Blo 1707054 70107929 := bstep (se 2 (by rfl) ⟨26290473, by rfl⟩ : syracuseStep 70107929 = 52580947) B52580947
theorem B1707367 : Blo 1707054 1707367 := bstep (se 1 (by rfl) ⟨1280525, by rfl⟩ : syracuseStep 1707367 = 2561051) B2561051
theorem B16423003 : Blo 1707054 16423003 := bstep (se 1 (by rfl) ⟨12317252, by rfl⟩ : syracuseStep 16423003 = 24634505) B24634505
theorem B3243215 : Blo 1707054 3243215 := bstep (se 1 (by rfl) ⟨2432411, by rfl⟩ : syracuseStep 3243215 = 4864823) B4864823
theorem B2883647 : Blo 1707054 2883647 := bstep (se 1 (by rfl) ⟨2162735, by rfl⟩ : syracuseStep 2883647 = 4325471) B4325471
theorem B21897337 : Blo 1707054 21897337 := bstep (se 2 (by rfl) ⟨8211501, by rfl⟩ : syracuseStep 21897337 = 16423003) B16423003
theorem B46738619 : Blo 1707054 46738619 := bstep (se 1 (by rfl) ⟨35053964, by rfl⟩ : syracuseStep 46738619 = 70107929) B70107929
theorem B2162143 : Blo 1707054 2162143 := bstep (se 1 (by rfl) ⟨1621607, by rfl⟩ : syracuseStep 2162143 = 3243215) B3243215
theorem B29196449 : Blo 1707054 29196449 := bstep (se 2 (by rfl) ⟨10948668, by rfl⟩ : syracuseStep 29196449 = 21897337) B21897337
theorem B31159079 : Blo 1707054 31159079 := bstep (se 1 (by rfl) ⟨23369309, by rfl⟩ : syracuseStep 31159079 = 46738619) B46738619
theorem B1922431 : Blo 1707054 1922431 := bstep (se 1 (by rfl) ⟨1441823, by rfl⟩ : syracuseStep 1922431 = 2883647) B2883647
theorem B2882857 : Blo 1707054 2882857 := bstep (se 2 (by rfl) ⟨1081071, by rfl⟩ : syracuseStep 2882857 = 2162143) B2162143
theorem B19464299 : Blo 1707054 19464299 := bstep (se 1 (by rfl) ⟨14598224, by rfl⟩ : syracuseStep 19464299 = 29196449) B29196449
theorem B3843809 : Blo 1707054 3843809 := bstep (se 2 (by rfl) ⟨1441428, by rfl⟩ : syracuseStep 3843809 = 2882857) B2882857
theorem B20772719 : Blo 1707054 20772719 := bstep (se 1 (by rfl) ⟨15579539, by rfl⟩ : syracuseStep 20772719 = 31159079) B31159079
theorem B2563241 : Blo 1707054 2563241 := bstep (se 2 (by rfl) ⟨961215, by rfl⟩ : syracuseStep 2563241 = 1922431) B1922431
theorem B12976199 : Blo 1707054 12976199 := bstep (se 1 (by rfl) ⟨9732149, by rfl⟩ : syracuseStep 12976199 = 19464299) B19464299
theorem B13848479 : Blo 1707054 13848479 := bstep (se 1 (by rfl) ⟨10386359, by rfl⟩ : syracuseStep 13848479 = 20772719) B20772719
theorem B1708827 : Blo 1707054 1708827 := bstep (se 1 (by rfl) ⟨1281620, by rfl⟩ : syracuseStep 1708827 = 2563241) B2563241
theorem B2562539 : Blo 1707054 2562539 := bstep (se 1 (by rfl) ⟨1921904, by rfl⟩ : syracuseStep 2562539 = 3843809) B3843809
theorem B8650799 : Blo 1707054 8650799 := bstep (se 1 (by rfl) ⟨6488099, by rfl⟩ : syracuseStep 8650799 = 12976199) B12976199
theorem B1708359 : Blo 1707054 1708359 := bstep (se 1 (by rfl) ⟨1281269, by rfl⟩ : syracuseStep 1708359 = 2562539) B2562539
theorem B9232319 : Blo 1707054 9232319 := bstep (se 1 (by rfl) ⟨6924239, by rfl⟩ : syracuseStep 9232319 = 13848479) B13848479
theorem B5767199 : Blo 1707054 5767199 := bstep (se 1 (by rfl) ⟨4325399, by rfl⟩ : syracuseStep 5767199 = 8650799) B8650799
theorem B6154879 : Blo 1707054 6154879 := bstep (se 1 (by rfl) ⟨4616159, by rfl⟩ : syracuseStep 6154879 = 9232319) B9232319
theorem B3844799 : Blo 1707054 3844799 := bstep (se 1 (by rfl) ⟨2883599, by rfl⟩ : syracuseStep 3844799 = 5767199) B5767199
theorem B8206505 : Blo 1707054 8206505 := bstep (se 2 (by rfl) ⟨3077439, by rfl⟩ : syracuseStep 8206505 = 6154879) B6154879
theorem B5471003 : Blo 1707054 5471003 := bstep (se 1 (by rfl) ⟨4103252, by rfl⟩ : syracuseStep 5471003 = 8206505) B8206505
theorem B2563199 : Blo 1707054 2563199 := bstep (se 1 (by rfl) ⟨1922399, by rfl⟩ : syracuseStep 2563199 = 3844799) B3844799
theorem B1708799 : Blo 1707054 1708799 := bstep (se 1 (by rfl) ⟨1281599, by rfl⟩ : syracuseStep 1708799 = 2563199) B2563199
theorem B14589341 : Blo 1707054 14589341 := bstep (se 3 (by rfl) ⟨2735501, by rfl⟩ : syracuseStep 14589341 = 5471003) B5471003
theorem B9726227 : Blo 1707054 9726227 := bstep (se 1 (by rfl) ⟨7294670, by rfl⟩ : syracuseStep 9726227 = 14589341) B14589341
theorem B6484151 : Blo 1707054 6484151 := bstep (se 1 (by rfl) ⟨4863113, by rfl⟩ : syracuseStep 6484151 = 9726227) B9726227
theorem B4322767 : Blo 1707054 4322767 := bstep (se 1 (by rfl) ⟨3242075, by rfl⟩ : syracuseStep 4322767 = 6484151) B6484151
theorem B5763689 : Blo 1707054 5763689 := bstep (se 2 (by rfl) ⟨2161383, by rfl⟩ : syracuseStep 5763689 = 4322767) B4322767
theorem B3842459 : Blo 1707054 3842459 := bstep (se 1 (by rfl) ⟨2881844, by rfl⟩ : syracuseStep 3842459 = 5763689) B5763689
theorem B2561639 : Blo 1707054 2561639 := bstep (se 1 (by rfl) ⟨1921229, by rfl⟩ : syracuseStep 2561639 = 3842459) B3842459
theorem B1707759 : Blo 1707054 1707759 := bstep (se 1 (by rfl) ⟨1280819, by rfl⟩ : syracuseStep 1707759 = 2561639) B2561639

theorem C0 (j : ℕ) (h1 : 426763 ≤ j) (h2 : j ≤ 427262) : Blo 1707054 (4 * j + 3) := by
  interval_cases j
  · exact B1707055
  · exact B1707059
  · exact B1707063
  · exact B1707067
  · exact B1707071
  · exact B1707075
  · exact B1707079
  · exact B1707083
  · exact B1707087
  · exact B1707091
  · exact B1707095
  · exact B1707099
  · exact B1707103
  · exact B1707107
  · exact B1707111
  · exact B1707115
  · exact B1707119
  · exact B1707123
  · exact B1707127
  · exact B1707131
  · exact B1707135
  · exact B1707139
  · exact B1707143
  · exact B1707147
  · exact B1707151
  · exact B1707155
  · exact B1707159
  · exact B1707163
  · exact B1707167
  · exact B1707171
  · exact B1707175
  · exact B1707179
  · exact B1707183
  · exact B1707187
  · exact B1707191
  · exact B1707195
  · exact B1707199
  · exact B1707203
  · exact B1707207
  · exact B1707211
  · exact B1707215
  · exact B1707219
  · exact B1707223
  · exact B1707227
  · exact B1707231
  · exact B1707235
  · exact B1707239
  · exact B1707243
  · exact B1707247
  · exact B1707251
  · exact B1707255
  · exact B1707259
  · exact B1707263
  · exact B1707267
  · exact B1707271
  · exact B1707275
  · exact B1707279
  · exact B1707283
  · exact B1707287
  · exact B1707291
  · exact B1707295
  · exact B1707299
  · exact B1707303
  · exact B1707307
  · exact B1707311
  · exact B1707315
  · exact B1707319
  · exact B1707323
  · exact B1707327
  · exact B1707331
  · exact B1707335
  · exact B1707339
  · exact B1707343
  · exact B1707347
  · exact B1707351
  · exact B1707355
  · exact B1707359
  · exact B1707363
  · exact B1707367
  · exact B1707371
  · exact B1707375
  · exact B1707379
  · exact B1707383
  · exact B1707387
  · exact B1707391
  · exact B1707395
  · exact B1707399
  · exact B1707403
  · exact B1707407
  · exact B1707411
  · exact B1707415
  · exact B1707419
  · exact B1707423
  · exact B1707427
  · exact B1707431
  · exact B1707435
  · exact B1707439
  · exact B1707443
  · exact B1707447
  · exact B1707451
  · exact B1707455
  · exact B1707459
  · exact B1707463
  · exact B1707467
  · exact B1707471
  · exact B1707475
  · exact B1707479
  · exact B1707483
  · exact B1707487
  · exact B1707491
  · exact B1707495
  · exact B1707499
  · exact B1707503
  · exact B1707507
  · exact B1707511
  · exact B1707515
  · exact B1707519
  · exact B1707523
  · exact B1707527
  · exact B1707531
  · exact B1707535
  · exact B1707539
  · exact B1707543
  · exact B1707547
  · exact B1707551
  · exact B1707555
  · exact B1707559
  · exact B1707563
  · exact B1707567
  · exact B1707571
  · exact B1707575
  · exact B1707579
  · exact B1707583
  · exact B1707587
  · exact B1707591
  · exact B1707595
  · exact B1707599
  · exact B1707603
  · exact B1707607
  · exact B1707611
  · exact B1707615
  · exact B1707619
  · exact B1707623
  · exact B1707627
  · exact B1707631
  · exact B1707635
  · exact B1707639
  · exact B1707643
  · exact B1707647
  · exact B1707651
  · exact B1707655
  · exact B1707659
  · exact B1707663
  · exact B1707667
  · exact B1707671
  · exact B1707675
  · exact B1707679
  · exact B1707683
  · exact B1707687
  · exact B1707691
  · exact B1707695
  · exact B1707699
  · exact B1707703
  · exact B1707707
  · exact B1707711
  · exact B1707715
  · exact B1707719
  · exact B1707723
  · exact B1707727
  · exact B1707731
  · exact B1707735
  · exact B1707739
  · exact B1707743
  · exact B1707747
  · exact B1707751
  · exact B1707755
  · exact B1707759
  · exact B1707763
  · exact B1707767
  · exact B1707771
  · exact B1707775
  · exact B1707779
  · exact B1707783
  · exact B1707787
  · exact B1707791
  · exact B1707795
  · exact B1707799
  · exact B1707803
  · exact B1707807
  · exact B1707811
  · exact B1707815
  · exact B1707819
  · exact B1707823
  · exact B1707827
  · exact B1707831
  · exact B1707835
  · exact B1707839
  · exact B1707843
  · exact B1707847
  · exact B1707851
  · exact B1707855
  · exact B1707859
  · exact B1707863
  · exact B1707867
  · exact B1707871
  · exact B1707875
  · exact B1707879
  · exact B1707883
  · exact B1707887
  · exact B1707891
  · exact B1707895
  · exact B1707899
  · exact B1707903
  · exact B1707907
  · exact B1707911
  · exact B1707915
  · exact B1707919
  · exact B1707923
  · exact B1707927
  · exact B1707931
  · exact B1707935
  · exact B1707939
  · exact B1707943
  · exact B1707947
  · exact B1707951
  · exact B1707955
  · exact B1707959
  · exact B1707963
  · exact B1707967
  · exact B1707971
  · exact B1707975
  · exact B1707979
  · exact B1707983
  · exact B1707987
  · exact B1707991
  · exact B1707995
  · exact B1707999
  · exact B1708003
  · exact B1708007
  · exact B1708011
  · exact B1708015
  · exact B1708019
  · exact B1708023
  · exact B1708027
  · exact B1708031
  · exact B1708035
  · exact B1708039
  · exact B1708043
  · exact B1708047
  · exact B1708051
  · exact B1708055
  · exact B1708059
  · exact B1708063
  · exact B1708067
  · exact B1708071
  · exact B1708075
  · exact B1708079
  · exact B1708083
  · exact B1708087
  · exact B1708091
  · exact B1708095
  · exact B1708099
  · exact B1708103
  · exact B1708107
  · exact B1708111
  · exact B1708115
  · exact B1708119
  · exact B1708123
  · exact B1708127
  · exact B1708131
  · exact B1708135
  · exact B1708139
  · exact B1708143
  · exact B1708147
  · exact B1708151
  · exact B1708155
  · exact B1708159
  · exact B1708163
  · exact B1708167
  · exact B1708171
  · exact B1708175
  · exact B1708179
  · exact B1708183
  · exact B1708187
  · exact B1708191
  · exact B1708195
  · exact B1708199
  · exact B1708203
  · exact B1708207
  · exact B1708211
  · exact B1708215
  · exact B1708219
  · exact B1708223
  · exact B1708227
  · exact B1708231
  · exact B1708235
  · exact B1708239
  · exact B1708243
  · exact B1708247
  · exact B1708251
  · exact B1708255
  · exact B1708259
  · exact B1708263
  · exact B1708267
  · exact B1708271
  · exact B1708275
  · exact B1708279
  · exact B1708283
  · exact B1708287
  · exact B1708291
  · exact B1708295
  · exact B1708299
  · exact B1708303
  · exact B1708307
  · exact B1708311
  · exact B1708315
  · exact B1708319
  · exact B1708323
  · exact B1708327
  · exact B1708331
  · exact B1708335
  · exact B1708339
  · exact B1708343
  · exact B1708347
  · exact B1708351
  · exact B1708355
  · exact B1708359
  · exact B1708363
  · exact B1708367
  · exact B1708371
  · exact B1708375
  · exact B1708379
  · exact B1708383
  · exact B1708387
  · exact B1708391
  · exact B1708395
  · exact B1708399
  · exact B1708403
  · exact B1708407
  · exact B1708411
  · exact B1708415
  · exact B1708419
  · exact B1708423
  · exact B1708427
  · exact B1708431
  · exact B1708435
  · exact B1708439
  · exact B1708443
  · exact B1708447
  · exact B1708451
  · exact B1708455
  · exact B1708459
  · exact B1708463
  · exact B1708467
  · exact B1708471
  · exact B1708475
  · exact B1708479
  · exact B1708483
  · exact B1708487
  · exact B1708491
  · exact B1708495
  · exact B1708499
  · exact B1708503
  · exact B1708507
  · exact B1708511
  · exact B1708515
  · exact B1708519
  · exact B1708523
  · exact B1708527
  · exact B1708531
  · exact B1708535
  · exact B1708539
  · exact B1708543
  · exact B1708547
  · exact B1708551
  · exact B1708555
  · exact B1708559
  · exact B1708563
  · exact B1708567
  · exact B1708571
  · exact B1708575
  · exact B1708579
  · exact B1708583
  · exact B1708587
  · exact B1708591
  · exact B1708595
  · exact B1708599
  · exact B1708603
  · exact B1708607
  · exact B1708611
  · exact B1708615
  · exact B1708619
  · exact B1708623
  · exact B1708627
  · exact B1708631
  · exact B1708635
  · exact B1708639
  · exact B1708643
  · exact B1708647
  · exact B1708651
  · exact B1708655
  · exact B1708659
  · exact B1708663
  · exact B1708667
  · exact B1708671
  · exact B1708675
  · exact B1708679
  · exact B1708683
  · exact B1708687
  · exact B1708691
  · exact B1708695
  · exact B1708699
  · exact B1708703
  · exact B1708707
  · exact B1708711
  · exact B1708715
  · exact B1708719
  · exact B1708723
  · exact B1708727
  · exact B1708731
  · exact B1708735
  · exact B1708739
  · exact B1708743
  · exact B1708747
  · exact B1708751
  · exact B1708755
  · exact B1708759
  · exact B1708763
  · exact B1708767
  · exact B1708771
  · exact B1708775
  · exact B1708779
  · exact B1708783
  · exact B1708787
  · exact B1708791
  · exact B1708795
  · exact B1708799
  · exact B1708803
  · exact B1708807
  · exact B1708811
  · exact B1708815
  · exact B1708819
  · exact B1708823
  · exact B1708827
  · exact B1708831
  · exact B1708835
  · exact B1708839
  · exact B1708843
  · exact B1708847
  · exact B1708851
  · exact B1708855
  · exact B1708859
  · exact B1708863
  · exact B1708867
  · exact B1708871
  · exact B1708875
  · exact B1708879
  · exact B1708883
  · exact B1708887
  · exact B1708891
  · exact B1708895
  · exact B1708899
  · exact B1708903
  · exact B1708907
  · exact B1708911
  · exact B1708915
  · exact B1708919
  · exact B1708923
  · exact B1708927
  · exact B1708931
  · exact B1708935
  · exact B1708939
  · exact B1708943
  · exact B1708947
  · exact B1708951
  · exact B1708955
  · exact B1708959
  · exact B1708963
  · exact B1708967
  · exact B1708971
  · exact B1708975
  · exact B1708979
  · exact B1708983
  · exact B1708987
  · exact B1708991
  · exact B1708995
  · exact B1708999
  · exact B1709003
  · exact B1709007
  · exact B1709011
  · exact B1709015
  · exact B1709019
  · exact B1709023
  · exact B1709027
  · exact B1709031
  · exact B1709035
  · exact B1709039
  · exact B1709043
  · exact B1709047
  · exact B1709051

theorem solution (m : ℕ) (hlo : 1707054 ≤ m) (hhi : m ≤ 1709054) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 426763 ≤ j := by omega
    have hj2 : j ≤ 427262 := by omega
    have hb : Blo 1707054 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
