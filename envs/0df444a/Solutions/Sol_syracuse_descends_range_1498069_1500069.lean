-- Prove2me | solution 1 for syracuse_descends_range_1498069_1500069
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:47:35.738882+00:00
-- url     : https://prove2.me/submissions/bf7366b4-db04-446d-aaf0-2029f1dba93e

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


theorem B5062661 : Blo 1498069 5062661 := bbase (se 4 (by rfl) ⟨474624, by rfl⟩ : syracuseStep 5062661 = 949249) (by norm_num)
theorem B3375125 : Blo 1498069 3375125 := bbase (se 6 (by rfl) ⟨79104, by rfl⟩ : syracuseStep 3375125 = 158209) (by norm_num)
theorem B3203101 : Blo 1498069 3203101 := bbase (se 3 (by rfl) ⟨600581, by rfl⟩ : syracuseStep 3203101 = 1201163) (by norm_num)
theorem B2400301 : Blo 1498069 2400301 := bbase (se 3 (by rfl) ⟨450056, by rfl⟩ : syracuseStep 2400301 = 900113) (by norm_num)
theorem B3039277 : Blo 1498069 3039277 := bbase (se 3 (by rfl) ⟨569864, by rfl⟩ : syracuseStep 3039277 = 1139729) (by norm_num)
theorem B17080469 : Blo 1498069 17080469 := bbase (se 6 (by rfl) ⟨400323, by rfl⟩ : syracuseStep 17080469 = 800647) (by norm_num)
theorem B3203221 : Blo 1498069 3203221 := bbase (se 6 (by rfl) ⟨75075, by rfl⟩ : syracuseStep 3203221 = 150151) (by norm_num)
theorem B7585973 : Blo 1498069 7585973 := bbase (se 5 (by rfl) ⟨355592, by rfl⟩ : syracuseStep 7585973 = 711185) (by norm_num)
theorem B3793189 : Blo 1498069 3793189 := bbase (se 4 (by rfl) ⟨355611, by rfl⟩ : syracuseStep 3793189 = 711223) (by norm_num)
theorem B2883917 : Blo 1498069 2883917 := bbase (se 3 (by rfl) ⟨540734, by rfl⟩ : syracuseStep 2883917 = 1081469) (by norm_num)
theorem B3793301 : Blo 1498069 3793301 := bbase (se 6 (by rfl) ⟨88905, by rfl⟩ : syracuseStep 3793301 = 177811) (by norm_num)
theorem B3203477 : Blo 1498069 3203477 := bbase (se 6 (by rfl) ⟨75081, by rfl⟩ : syracuseStep 3203477 = 150163) (by norm_num)
theorem B4268501 : Blo 1498069 4268501 := bbase (se 7 (by rfl) ⟨50021, by rfl⟩ : syracuseStep 4268501 = 100043) (by norm_num)
theorem B24322517 : Blo 1498069 24322517 := bbase (se 7 (by rfl) ⟨285029, by rfl⟩ : syracuseStep 24322517 = 570059) (by norm_num)
theorem B6406613 : Blo 1498069 6406613 := bbase (se 7 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 6406613 = 150155) (by norm_num)
theorem B2277877 : Blo 1498069 2277877 := bbase (se 5 (by rfl) ⟨106775, by rfl⟩ : syracuseStep 2277877 = 213551) (by norm_num)
theorem B25960981 : Blo 1498069 25960981 := bbase (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) (by norm_num)
theorem B3793493 : Blo 1498069 3793493 := bbase (se 8 (by rfl) ⟨22227, by rfl⟩ : syracuseStep 3793493 = 44455) (by norm_num)
theorem B21897877 : Blo 1498069 21897877 := bbase (se 6 (by rfl) ⟨513231, by rfl⟩ : syracuseStep 21897877 = 1026463) (by norm_num)
theorem B5399237 : Blo 1498069 5399237 := bbase (se 4 (by rfl) ⟨506178, by rfl⟩ : syracuseStep 5399237 = 1012357) (by norm_num)
theorem B2884349 : Blo 1498069 2884349 := bbase (se 3 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 2884349 = 1081631) (by norm_num)
theorem B4268933 : Blo 1498069 4268933 := bbase (se 4 (by rfl) ⟨400212, by rfl⟩ : syracuseStep 4268933 = 800425) (by norm_num)
theorem B2737037 : Blo 1498069 2737037 := bbase (se 3 (by rfl) ⟨513194, by rfl⟩ : syracuseStep 2737037 = 1026389) (by norm_num)
theorem B17302421 : Blo 1498069 17302421 := bbase (se 6 (by rfl) ⟨405525, by rfl⟩ : syracuseStep 17302421 = 811051) (by norm_num)
theorem B3793837 : Blo 1498069 3793837 := bbase (se 3 (by rfl) ⟨711344, by rfl⟩ : syracuseStep 3793837 = 1422689) (by norm_num)
theorem B2401301 : Blo 1498069 2401301 := bbase (se 6 (by rfl) ⟨56280, by rfl⟩ : syracuseStep 2401301 = 112561) (by norm_num)
theorem B3793949 : Blo 1498069 3793949 := bbase (se 3 (by rfl) ⟨711365, by rfl⟩ : syracuseStep 3793949 = 1422731) (by norm_num)
theorem B3417125 : Blo 1498069 3417125 := bbase (se 4 (by rfl) ⟨320355, by rfl⟩ : syracuseStep 3417125 = 640711) (by norm_num)
theorem B2311237 : Blo 1498069 2311237 := bbase (se 4 (by rfl) ⟨216678, by rfl⟩ : syracuseStep 2311237 = 433357) (by norm_num)
theorem B7693397 : Blo 1498069 7693397 := bbase (se 8 (by rfl) ⟨45078, by rfl⟩ : syracuseStep 7693397 = 90157) (by norm_num)
theorem B5399669 : Blo 1498069 5399669 := bbase (se 5 (by rfl) ⟨253109, by rfl⟩ : syracuseStep 5399669 = 506219) (by norm_num)
theorem B2401429 : Blo 1498069 2401429 := bbase (se 6 (by rfl) ⟨56283, by rfl⟩ : syracuseStep 2401429 = 112567) (by norm_num)
theorem B2401493 : Blo 1498069 2401493 := bbase (se 7 (by rfl) ⟨28142, by rfl⟩ : syracuseStep 2401493 = 56285) (by norm_num)
theorem B3794141 : Blo 1498069 3794141 := bbase (se 3 (by rfl) ⟨711401, by rfl⟩ : syracuseStep 3794141 = 1422803) (by norm_num)
theorem B4801781 : Blo 1498069 4801781 := bbase (se 5 (by rfl) ⟨225083, by rfl⟩ : syracuseStep 4801781 = 450167) (by norm_num)
theorem B2884901 : Blo 1498069 2884901 := bbase (se 4 (by rfl) ⟨270459, by rfl⟩ : syracuseStep 2884901 = 540919) (by norm_num)
theorem B7587269 : Blo 1498069 7587269 := bbase (se 4 (by rfl) ⟨711306, by rfl⟩ : syracuseStep 7587269 = 1422613) (by norm_num)
theorem B12977653 : Blo 1498069 12977653 := bbase (se 5 (by rfl) ⟨608327, by rfl⟩ : syracuseStep 12977653 = 1216655) (by norm_num)
theorem B11388437 : Blo 1498069 11388437 := bbase (se 6 (by rfl) ⟨266916, by rfl⟩ : syracuseStep 11388437 = 533833) (by norm_num)
theorem B2885149 : Blo 1498069 2885149 := bbase (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) (by norm_num)
theorem B3794485 : Blo 1498069 3794485 := bbase (se 5 (by rfl) ⟨177866, by rfl⟩ : syracuseStep 3794485 = 355733) (by norm_num)
theorem B6399557 : Blo 1498069 6399557 := bbase (se 4 (by rfl) ⟨599958, by rfl⟩ : syracuseStep 6399557 = 1199917) (by norm_num)
theorem B7300709 : Blo 1498069 7300709 := bbase (se 4 (by rfl) ⟨684441, by rfl⟩ : syracuseStep 7300709 = 1368883) (by norm_num)
theorem B4269685 : Blo 1498069 4269685 := bbase (se 5 (by rfl) ⟨200141, by rfl⟩ : syracuseStep 4269685 = 400283) (by norm_num)
theorem B3794597 : Blo 1498069 3794597 := bbase (se 4 (by rfl) ⟨355743, by rfl⟩ : syracuseStep 3794597 = 711487) (by norm_num)
theorem B5056181 : Blo 1498069 5056181 := bbase (se 5 (by rfl) ⟨237008, by rfl⟩ : syracuseStep 5056181 = 474017) (by norm_num)
theorem B3794789 : Blo 1498069 3794789 := bbase (se 4 (by rfl) ⟨355761, by rfl⟩ : syracuseStep 3794789 = 711523) (by norm_num)
theorem B10258325 : Blo 1498069 10258325 := bbase (se 6 (by rfl) ⟨240429, by rfl⟩ : syracuseStep 10258325 = 480859) (by norm_num)
theorem B11380661 : Blo 1498069 11380661 := bbase (se 5 (by rfl) ⟨533468, by rfl⟩ : syracuseStep 11380661 = 1066937) (by norm_num)
theorem B9734069 : Blo 1498069 9734069 := bbase (se 5 (by rfl) ⟨456284, by rfl⟩ : syracuseStep 9734069 = 912569) (by norm_num)
theorem B5695541 : Blo 1498069 5695541 := bbase (se 5 (by rfl) ⟨266978, by rfl⟩ : syracuseStep 5695541 = 533957) (by norm_num)
theorem B2844733 : Blo 1498069 2844733 := bbase (se 3 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 2844733 = 1066775) (by norm_num)
theorem B25618517 : Blo 1498069 25618517 := bbase (se 8 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 25618517 = 300217) (by norm_num)
theorem B5056613 : Blo 1498069 5056613 := bbase (se 4 (by rfl) ⟨474057, by rfl⟩ : syracuseStep 5056613 = 948115) (by norm_num)
theorem B3795133 : Blo 1498069 3795133 := bbase (se 3 (by rfl) ⟨711587, by rfl⟩ : syracuseStep 3795133 = 1423175) (by norm_num)
theorem B2844877 : Blo 1498069 2844877 := bbase (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) (by norm_num)
theorem B3467501 : Blo 1498069 3467501 := bbase (se 3 (by rfl) ⟨650156, by rfl⟩ : syracuseStep 3467501 = 1300313) (by norm_num)
theorem B3795245 : Blo 1498069 3795245 := bbase (se 3 (by rfl) ⟨711608, by rfl⟩ : syracuseStep 3795245 = 1423217) (by norm_num)
theorem B2468141 : Blo 1498069 2468141 := bbase (se 3 (by rfl) ⟨462776, by rfl⟩ : syracuseStep 2468141 = 925553) (by norm_num)
theorem B4802885 : Blo 1498069 4802885 := bbase (se 4 (by rfl) ⟨450270, by rfl⟩ : syracuseStep 4802885 = 900541) (by norm_num)
theorem B2845037 : Blo 1498069 2845037 := bbase (se 3 (by rfl) ⟨533444, by rfl⟩ : syracuseStep 2845037 = 1066889) (by norm_num)
theorem B10799509 : Blo 1498069 10799509 := bbase (se 6 (by rfl) ⟨253113, by rfl⟩ : syracuseStep 10799509 = 506227) (by norm_num)
theorem B3467669 : Blo 1498069 3467669 := bbase (se 6 (by rfl) ⟨81273, by rfl⟩ : syracuseStep 3467669 = 162547) (by norm_num)
theorem B4106693 : Blo 1498069 4106693 := bbase (se 4 (by rfl) ⟨385002, by rfl⟩ : syracuseStep 4106693 = 770005) (by norm_num)
theorem B2247125 : Blo 1498069 2247125 := bbase (se 7 (by rfl) ⟨26333, by rfl⟩ : syracuseStep 2247125 = 52667) (by norm_num)
theorem B2247149 : Blo 1498069 2247149 := bbase (se 3 (by rfl) ⟨421340, by rfl⟩ : syracuseStep 2247149 = 842681) (by norm_num)
theorem B3795437 : Blo 1498069 3795437 := bbase (se 3 (by rfl) ⟨711644, by rfl⟩ : syracuseStep 3795437 = 1423289) (by norm_num)
theorem B4385269 : Blo 1498069 4385269 := bbase (se 5 (by rfl) ⟨205559, by rfl⟩ : syracuseStep 4385269 = 411119) (by norm_num)
theorem B2845181 : Blo 1498069 2845181 := bbase (se 3 (by rfl) ⟨533471, by rfl⟩ : syracuseStep 2845181 = 1066943) (by norm_num)
theorem B2402813 : Blo 1498069 2402813 := bbase (se 3 (by rfl) ⟨450527, by rfl⟩ : syracuseStep 2402813 = 901055) (by norm_num)
theorem B2247173 : Blo 1498069 2247173 := bbase (se 4 (by rfl) ⟨210672, by rfl⟩ : syracuseStep 2247173 = 421345) (by norm_num)
theorem B1600013 : Blo 1498069 1600013 := bbase (se 3 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 1600013 = 600005) (by norm_num)
theorem B5057045 : Blo 1498069 5057045 := bbase (se 6 (by rfl) ⟨118524, by rfl⟩ : syracuseStep 5057045 = 237049) (by norm_num)
theorem B2247197 : Blo 1498069 2247197 := bbase (se 3 (by rfl) ⟨421349, by rfl⟩ : syracuseStep 2247197 = 842699) (by norm_num)
theorem B2247221 : Blo 1498069 2247221 := bbase (se 5 (by rfl) ⟨105338, by rfl⟩ : syracuseStep 2247221 = 210677) (by norm_num)
theorem B6400565 : Blo 1498069 6400565 := bbase (se 5 (by rfl) ⟨300026, by rfl⟩ : syracuseStep 6400565 = 600053) (by norm_num)
theorem B2247245 : Blo 1498069 2247245 := bbase (se 3 (by rfl) ⟨421358, by rfl⟩ : syracuseStep 2247245 = 842717) (by norm_num)
theorem B2247269 : Blo 1498069 2247269 := bbase (se 4 (by rfl) ⟨210681, by rfl⟩ : syracuseStep 2247269 = 421363) (by norm_num)
theorem B2247293 : Blo 1498069 2247293 := bbase (se 3 (by rfl) ⟨421367, by rfl⟩ : syracuseStep 2247293 = 842735) (by norm_num)
theorem B2247317 : Blo 1498069 2247317 := bbase (se 6 (by rfl) ⟨52671, by rfl⟩ : syracuseStep 2247317 = 105343) (by norm_num)
theorem B2247341 : Blo 1498069 2247341 := bbase (se 3 (by rfl) ⟨421376, by rfl⟩ : syracuseStep 2247341 = 842753) (by norm_num)
theorem B2247365 : Blo 1498069 2247365 := bbase (se 4 (by rfl) ⟨210690, by rfl⟩ : syracuseStep 2247365 = 421381) (by norm_num)
theorem B7588565 : Blo 1498069 7588565 := bbase (se 7 (by rfl) ⟨88928, by rfl⟩ : syracuseStep 7588565 = 177857) (by norm_num)
theorem B2247389 : Blo 1498069 2247389 := bbase (se 3 (by rfl) ⟨421385, by rfl⟩ : syracuseStep 2247389 = 842771) (by norm_num)
theorem B5688053 : Blo 1498069 5688053 := bbase (se 5 (by rfl) ⟨266627, by rfl⟩ : syracuseStep 5688053 = 533255) (by norm_num)
theorem B2247413 : Blo 1498069 2247413 := bbase (se 5 (by rfl) ⟨105347, by rfl⟩ : syracuseStep 2247413 = 210695) (by norm_num)
theorem B2247437 : Blo 1498069 2247437 := bbase (se 3 (by rfl) ⟨421394, by rfl⟩ : syracuseStep 2247437 = 842789) (by norm_num)
theorem B2845469 : Blo 1498069 2845469 := bbase (se 3 (by rfl) ⟨533525, by rfl⟩ : syracuseStep 2845469 = 1067051) (by norm_num)
theorem B2247461 : Blo 1498069 2247461 := bbase (se 4 (by rfl) ⟨210699, by rfl⟩ : syracuseStep 2247461 = 421399) (by norm_num)
theorem B2247485 : Blo 1498069 2247485 := bbase (se 3 (by rfl) ⟨421403, by rfl⟩ : syracuseStep 2247485 = 842807) (by norm_num)
theorem B3795781 : Blo 1498069 3795781 := bbase (se 4 (by rfl) ⟨355854, by rfl⟩ : syracuseStep 3795781 = 711709) (by norm_num)
theorem B2247509 : Blo 1498069 2247509 := bbase (se 9 (by rfl) ⟨6584, by rfl⟩ : syracuseStep 2247509 = 13169) (by norm_num)
theorem B2247533 : Blo 1498069 2247533 := bbase (se 3 (by rfl) ⟨421412, by rfl⟩ : syracuseStep 2247533 = 842825) (by norm_num)
theorem B2247557 : Blo 1498069 2247557 := bbase (se 4 (by rfl) ⟨210708, by rfl⟩ : syracuseStep 2247557 = 421417) (by norm_num)
theorem B2247581 : Blo 1498069 2247581 := bbase (se 3 (by rfl) ⟨421421, by rfl⟩ : syracuseStep 2247581 = 842843) (by norm_num)
theorem B2247605 : Blo 1498069 2247605 := bbase (se 5 (by rfl) ⟨105356, by rfl⟩ : syracuseStep 2247605 = 210713) (by norm_num)
theorem B2845621 : Blo 1498069 2845621 := bbase (se 5 (by rfl) ⟨133388, by rfl⟩ : syracuseStep 2845621 = 266777) (by norm_num)
theorem B3795893 : Blo 1498069 3795893 := bbase (se 5 (by rfl) ⟨177932, by rfl⟩ : syracuseStep 3795893 = 355865) (by norm_num)
theorem B14412725 : Blo 1498069 14412725 := bbase (se 5 (by rfl) ⟨675596, by rfl⟩ : syracuseStep 14412725 = 1351193) (by norm_num)
theorem B5057477 : Blo 1498069 5057477 := bbase (se 4 (by rfl) ⟨474138, by rfl⟩ : syracuseStep 5057477 = 948277) (by norm_num)
theorem B1600457 : Blo 1498069 1600457 := bbase (se 2 (by rfl) ⟨600171, by rfl⟩ : syracuseStep 1600457 = 1200343) (by norm_num)
theorem B2247629 : Blo 1498069 2247629 := bbase (se 3 (by rfl) ⟨421430, by rfl⟩ : syracuseStep 2247629 = 842861) (by norm_num)
theorem B2247653 : Blo 1498069 2247653 := bbase (se 4 (by rfl) ⟨210717, by rfl⟩ : syracuseStep 2247653 = 421435) (by norm_num)
theorem B2247677 : Blo 1498069 2247677 := bbase (se 3 (by rfl) ⟨421439, by rfl⟩ : syracuseStep 2247677 = 842879) (by norm_num)
theorem B1600517 : Blo 1498069 1600517 := bbase (se 4 (by rfl) ⟨150048, by rfl⟩ : syracuseStep 1600517 = 300097) (by norm_num)
theorem B2247701 : Blo 1498069 2247701 := bbase (se 6 (by rfl) ⟨52680, by rfl⟩ : syracuseStep 2247701 = 105361) (by norm_num)
theorem B2247725 : Blo 1498069 2247725 := bbase (se 3 (by rfl) ⟨421448, by rfl⟩ : syracuseStep 2247725 = 842897) (by norm_num)
theorem B2247749 : Blo 1498069 2247749 := bbase (se 4 (by rfl) ⟨210726, by rfl⟩ : syracuseStep 2247749 = 421453) (by norm_num)
theorem B3599453 : Blo 1498069 3599453 := bbase (se 3 (by rfl) ⟨674897, by rfl⟩ : syracuseStep 3599453 = 1349795) (by norm_num)
theorem B2247773 : Blo 1498069 2247773 := bbase (se 3 (by rfl) ⟨421457, by rfl⟩ : syracuseStep 2247773 = 842915) (by norm_num)
theorem B2247797 : Blo 1498069 2247797 := bbase (se 5 (by rfl) ⟨105365, by rfl⟩ : syracuseStep 2247797 = 210731) (by norm_num)
theorem B3796085 : Blo 1498069 3796085 := bbase (se 5 (by rfl) ⟨177941, by rfl⟩ : syracuseStep 3796085 = 355883) (by norm_num)
theorem B1600645 : Blo 1498069 1600645 := bbase (se 4 (by rfl) ⟨150060, by rfl⟩ : syracuseStep 1600645 = 300121) (by norm_num)
theorem B2247821 : Blo 1498069 2247821 := bbase (se 3 (by rfl) ⟨421466, by rfl⟩ : syracuseStep 2247821 = 842933) (by norm_num)
theorem B2133157 : Blo 1498069 2133157 := bbase (se 4 (by rfl) ⟨199983, by rfl⟩ : syracuseStep 2133157 = 399967) (by norm_num)
theorem B2247845 : Blo 1498069 2247845 := bbase (se 4 (by rfl) ⟨210735, by rfl⟩ : syracuseStep 2247845 = 421471) (by norm_num)
theorem B2247869 : Blo 1498069 2247869 := bbase (se 3 (by rfl) ⟨421475, by rfl⟩ : syracuseStep 2247869 = 842951) (by norm_num)
theorem B3419333 : Blo 1498069 3419333 := bbase (se 4 (by rfl) ⟨320562, by rfl⟩ : syracuseStep 3419333 = 641125) (by norm_num)
theorem B2247893 : Blo 1498069 2247893 := bbase (se 7 (by rfl) ⟨26342, by rfl⟩ : syracuseStep 2247893 = 52685) (by norm_num)
theorem B36457685 : Blo 1498069 36457685 := bbase (se 7 (by rfl) ⟨427238, by rfl⟩ : syracuseStep 36457685 = 854477) (by norm_num)
theorem B2845925 : Blo 1498069 2845925 := bbase (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) (by norm_num)
theorem B3599597 : Blo 1498069 3599597 := bbase (se 3 (by rfl) ⟨674924, by rfl⟩ : syracuseStep 3599597 = 1349849) (by norm_num)
theorem B2247917 : Blo 1498069 2247917 := bbase (se 3 (by rfl) ⟨421484, by rfl⟩ : syracuseStep 2247917 = 842969) (by norm_num)
theorem B2247941 : Blo 1498069 2247941 := bbase (se 4 (by rfl) ⟨210744, by rfl⟩ : syracuseStep 2247941 = 421489) (by norm_num)
theorem B2247965 : Blo 1498069 2247965 := bbase (se 3 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 2247965 = 842987) (by norm_num)
theorem B7204133 : Blo 1498069 7204133 := bbase (se 4 (by rfl) ⟨675387, by rfl⟩ : syracuseStep 7204133 = 1350775) (by norm_num)
theorem B2247989 : Blo 1498069 2247989 := bbase (se 5 (by rfl) ⟨105374, by rfl⟩ : syracuseStep 2247989 = 210749) (by norm_num)
theorem B6491461 : Blo 1498069 6491461 := bbase (se 4 (by rfl) ⟨608574, by rfl⟩ : syracuseStep 6491461 = 1217149) (by norm_num)
theorem B2248013 : Blo 1498069 2248013 := bbase (se 3 (by rfl) ⟨421502, by rfl⟩ : syracuseStep 2248013 = 843005) (by norm_num)
theorem B2248037 : Blo 1498069 2248037 := bbase (se 4 (by rfl) ⟨210753, by rfl⟩ : syracuseStep 2248037 = 421507) (by norm_num)
theorem B5057909 : Blo 1498069 5057909 := bbase (se 5 (by rfl) ⟨237089, by rfl⟩ : syracuseStep 5057909 = 474179) (by norm_num)
theorem B2133373 : Blo 1498069 2133373 := bbase (se 3 (by rfl) ⟨400007, by rfl⟩ : syracuseStep 2133373 = 800015) (by norm_num)
theorem B2248061 : Blo 1498069 2248061 := bbase (se 3 (by rfl) ⟨421511, by rfl⟩ : syracuseStep 2248061 = 843023) (by norm_num)
theorem B2248085 : Blo 1498069 2248085 := bbase (se 6 (by rfl) ⟨52689, by rfl⟩ : syracuseStep 2248085 = 105379) (by norm_num)
theorem B2248109 : Blo 1498069 2248109 := bbase (se 3 (by rfl) ⟨421520, by rfl⟩ : syracuseStep 2248109 = 843041) (by norm_num)
theorem B2248133 : Blo 1498069 2248133 := bbase (se 4 (by rfl) ⟨210762, by rfl⟩ : syracuseStep 2248133 = 421525) (by norm_num)
theorem B3796429 : Blo 1498069 3796429 := bbase (se 3 (by rfl) ⟨711830, by rfl⟩ : syracuseStep 3796429 = 1423661) (by norm_num)
theorem B2248157 : Blo 1498069 2248157 := bbase (se 3 (by rfl) ⟨421529, by rfl⟩ : syracuseStep 2248157 = 843059) (by norm_num)
theorem B1687549 : Blo 1498069 1687549 := bbase (se 3 (by rfl) ⟨316415, by rfl⟩ : syracuseStep 1687549 = 632831) (by norm_num)
theorem B2248181 : Blo 1498069 2248181 := bbase (se 5 (by rfl) ⟨105383, by rfl⟩ : syracuseStep 2248181 = 210767) (by norm_num)
theorem B3419653 : Blo 1498069 3419653 := bbase (se 4 (by rfl) ⟨320592, by rfl⟩ : syracuseStep 3419653 = 641185) (by norm_num)
theorem B2248205 : Blo 1498069 2248205 := bbase (se 3 (by rfl) ⟨421538, by rfl⟩ : syracuseStep 2248205 = 843077) (by norm_num)
theorem B2248229 : Blo 1498069 2248229 := bbase (se 4 (by rfl) ⟨210771, by rfl⟩ : syracuseStep 2248229 = 421543) (by norm_num)
theorem B2248253 : Blo 1498069 2248253 := bbase (se 3 (by rfl) ⟨421547, by rfl⟩ : syracuseStep 2248253 = 843095) (by norm_num)
theorem B3796541 : Blo 1498069 3796541 := bbase (se 3 (by rfl) ⟨711851, by rfl⟩ : syracuseStep 3796541 = 1423703) (by norm_num)
theorem B1601089 : Blo 1498069 1601089 := bbase (se 2 (by rfl) ⟨600408, by rfl⟩ : syracuseStep 1601089 = 1200817) (by norm_num)
theorem B2248277 : Blo 1498069 2248277 := bbase (se 8 (by rfl) ⟨13173, by rfl⟩ : syracuseStep 2248277 = 26347) (by norm_num)
theorem B2248301 : Blo 1498069 2248301 := bbase (se 3 (by rfl) ⟨421556, by rfl⟩ : syracuseStep 2248301 = 843113) (by norm_num)
theorem B2027125 : Blo 1498069 2027125 := bbase (se 5 (by rfl) ⟨95021, by rfl⟩ : syracuseStep 2027125 = 190043) (by norm_num)
theorem B2248325 : Blo 1498069 2248325 := bbase (se 4 (by rfl) ⟨210780, by rfl⟩ : syracuseStep 2248325 = 421561) (by norm_num)
theorem B2248349 : Blo 1498069 2248349 := bbase (se 3 (by rfl) ⟨421565, by rfl⟩ : syracuseStep 2248349 = 843131) (by norm_num)
theorem B3370661 : Blo 1498069 3370661 := bbase (se 4 (by rfl) ⟨315999, by rfl⟩ : syracuseStep 3370661 = 631999) (by norm_num)
theorem B2248373 : Blo 1498069 2248373 := bbase (se 5 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 2248373 = 210785) (by norm_num)
theorem B1601209 : Blo 1498069 1601209 := bbase (se 2 (by rfl) ⟨600453, by rfl⟩ : syracuseStep 1601209 = 1200907) (by norm_num)
theorem B2248397 : Blo 1498069 2248397 := bbase (se 3 (by rfl) ⟨421574, by rfl⟩ : syracuseStep 2248397 = 843149) (by norm_num)
theorem B1896149 : Blo 1498069 1896149 := bbase (se 7 (by rfl) ⟨22220, by rfl⟩ : syracuseStep 1896149 = 44441) (by norm_num)
theorem B2248421 : Blo 1498069 2248421 := bbase (se 4 (by rfl) ⟨210789, by rfl⟩ : syracuseStep 2248421 = 421579) (by norm_num)
theorem B3370733 : Blo 1498069 3370733 := bbase (se 3 (by rfl) ⟨632012, by rfl⟩ : syracuseStep 3370733 = 1264025) (by norm_num)
theorem B2133749 : Blo 1498069 2133749 := bbase (se 5 (by rfl) ⟨100019, by rfl⟩ : syracuseStep 2133749 = 200039) (by norm_num)
theorem B2248445 : Blo 1498069 2248445 := bbase (se 3 (by rfl) ⟨421583, by rfl⟩ : syracuseStep 2248445 = 843167) (by norm_num)
theorem B3796733 : Blo 1498069 3796733 := bbase (se 3 (by rfl) ⟨711887, by rfl⟩ : syracuseStep 3796733 = 1423775) (by norm_num)
theorem B1896205 : Blo 1498069 1896205 := bbase (se 3 (by rfl) ⟨355538, by rfl⟩ : syracuseStep 1896205 = 711077) (by norm_num)
theorem B2248469 : Blo 1498069 2248469 := bbase (se 6 (by rfl) ⟨52698, by rfl⟩ : syracuseStep 2248469 = 105397) (by norm_num)
theorem B5058341 : Blo 1498069 5058341 := bbase (se 4 (by rfl) ⟨474219, by rfl⟩ : syracuseStep 5058341 = 948439) (by norm_num)
theorem B2248493 : Blo 1498069 2248493 := bbase (se 3 (by rfl) ⟨421592, by rfl⟩ : syracuseStep 2248493 = 843185) (by norm_num)
theorem B3370805 : Blo 1498069 3370805 := bbase (se 5 (by rfl) ⟨158006, by rfl⟩ : syracuseStep 3370805 = 316013) (by norm_num)
theorem B2248517 : Blo 1498069 2248517 := bbase (se 4 (by rfl) ⟨210798, by rfl⟩ : syracuseStep 2248517 = 421597) (by norm_num)
theorem B2248541 : Blo 1498069 2248541 := bbase (se 3 (by rfl) ⟨421601, by rfl⟩ : syracuseStep 2248541 = 843203) (by norm_num)
theorem B1896301 : Blo 1498069 1896301 := bbase (se 3 (by rfl) ⟨355556, by rfl⟩ : syracuseStep 1896301 = 711113) (by norm_num)
theorem B2248565 : Blo 1498069 2248565 := bbase (se 5 (by rfl) ⟨105401, by rfl⟩ : syracuseStep 2248565 = 210803) (by norm_num)
theorem B3370877 : Blo 1498069 3370877 := bbase (se 3 (by rfl) ⟨632039, by rfl⟩ : syracuseStep 3370877 = 1264079) (by norm_num)
theorem B2248589 : Blo 1498069 2248589 := bbase (se 3 (by rfl) ⟨421610, by rfl⟩ : syracuseStep 2248589 = 843221) (by norm_num)
theorem B5689237 : Blo 1498069 5689237 := bbase (se 6 (by rfl) ⟨133341, by rfl⟩ : syracuseStep 5689237 = 266683) (by norm_num)
theorem B2248613 : Blo 1498069 2248613 := bbase (se 4 (by rfl) ⟨210807, by rfl⟩ : syracuseStep 2248613 = 421615) (by norm_num)
theorem B1601461 : Blo 1498069 1601461 := bbase (se 5 (by rfl) ⟨75068, by rfl⟩ : syracuseStep 1601461 = 150137) (by norm_num)
theorem B1601465 : Blo 1498069 1601465 := bbase (se 2 (by rfl) ⟨600549, by rfl⟩ : syracuseStep 1601465 = 1201099) (by norm_num)
theorem B2248637 : Blo 1498069 2248637 := bbase (se 3 (by rfl) ⟨421619, by rfl⟩ : syracuseStep 2248637 = 843239) (by norm_num)
theorem B3370949 : Blo 1498069 3370949 := bbase (se 4 (by rfl) ⟨316026, by rfl⟩ : syracuseStep 3370949 = 632053) (by norm_num)
theorem B2248661 : Blo 1498069 2248661 := bbase (se 7 (by rfl) ⟨26351, by rfl⟩ : syracuseStep 2248661 = 52703) (by norm_num)
theorem B2846677 : Blo 1498069 2846677 := bbase (se 7 (by rfl) ⟨33359, by rfl⟩ : syracuseStep 2846677 = 66719) (by norm_num)
theorem B7589861 : Blo 1498069 7589861 := bbase (se 4 (by rfl) ⟨711549, by rfl⟩ : syracuseStep 7589861 = 1423099) (by norm_num)
theorem B2248685 : Blo 1498069 2248685 := bbase (se 3 (by rfl) ⟨421628, by rfl⟩ : syracuseStep 2248685 = 843257) (by norm_num)
theorem B2248709 : Blo 1498069 2248709 := bbase (se 4 (by rfl) ⟨210816, by rfl⟩ : syracuseStep 2248709 = 421633) (by norm_num)
theorem B3371021 : Blo 1498069 3371021 := bbase (se 3 (by rfl) ⟨632066, by rfl⟩ : syracuseStep 3371021 = 1264133) (by norm_num)
theorem B1896473 : Blo 1498069 1896473 := bbase (se 2 (by rfl) ⟨711177, by rfl⟩ : syracuseStep 1896473 = 1422355) (by norm_num)
theorem B2248733 : Blo 1498069 2248733 := bbase (se 3 (by rfl) ⟨421637, by rfl⟩ : syracuseStep 2248733 = 843275) (by norm_num)
theorem B2248757 : Blo 1498069 2248757 := bbase (se 5 (by rfl) ⟨105410, by rfl⟩ : syracuseStep 2248757 = 210821) (by norm_num)
theorem B2248781 : Blo 1498069 2248781 := bbase (se 3 (by rfl) ⟨421646, by rfl⟩ : syracuseStep 2248781 = 843293) (by norm_num)
theorem B1896529 : Blo 1498069 1896529 := bbase (se 2 (by rfl) ⟨711198, by rfl⟩ : syracuseStep 1896529 = 1422397) (by norm_num)
theorem B3371093 : Blo 1498069 3371093 := bbase (se 8 (by rfl) ⟨19752, by rfl⟩ : syracuseStep 3371093 = 39505) (by norm_num)
theorem B2248805 : Blo 1498069 2248805 := bbase (se 4 (by rfl) ⟨210825, by rfl⟩ : syracuseStep 2248805 = 421651) (by norm_num)
theorem B2846821 : Blo 1498069 2846821 := bbase (se 4 (by rfl) ⟨266889, by rfl⟩ : syracuseStep 2846821 = 533779) (by norm_num)
theorem B2248829 : Blo 1498069 2248829 := bbase (se 3 (by rfl) ⟨421655, by rfl⟩ : syracuseStep 2248829 = 843311) (by norm_num)
theorem B2248853 : Blo 1498069 2248853 := bbase (se 6 (by rfl) ⟨52707, by rfl⟩ : syracuseStep 2248853 = 105415) (by norm_num)
theorem B3371165 : Blo 1498069 3371165 := bbase (se 3 (by rfl) ⟨632093, by rfl⟩ : syracuseStep 3371165 = 1264187) (by norm_num)
theorem B2248877 : Blo 1498069 2248877 := bbase (se 3 (by rfl) ⟨421664, by rfl⟩ : syracuseStep 2248877 = 843329) (by norm_num)
theorem B1896625 : Blo 1498069 1896625 := bbase (se 2 (by rfl) ⟨711234, by rfl⟩ : syracuseStep 1896625 = 1422469) (by norm_num)
theorem B5689541 : Blo 1498069 5689541 := bbase (se 4 (by rfl) ⟨533394, by rfl⟩ : syracuseStep 5689541 = 1066789) (by norm_num)
theorem B2248901 : Blo 1498069 2248901 := bbase (se 4 (by rfl) ⟨210834, by rfl⟩ : syracuseStep 2248901 = 421669) (by norm_num)
theorem B4804805 : Blo 1498069 4804805 := bbase (se 4 (by rfl) ⟨450450, by rfl⟩ : syracuseStep 4804805 = 900901) (by norm_num)
theorem B1519817 : Blo 1498069 1519817 := bbase (se 2 (by rfl) ⟨569931, by rfl⟩ : syracuseStep 1519817 = 1139863) (by norm_num)
theorem B5058773 : Blo 1498069 5058773 := bbase (se 7 (by rfl) ⟨59282, by rfl⟩ : syracuseStep 5058773 = 118565) (by norm_num)
theorem B2248925 : Blo 1498069 2248925 := bbase (se 3 (by rfl) ⟨421673, by rfl⟩ : syracuseStep 2248925 = 843347) (by norm_num)
theorem B3371237 : Blo 1498069 3371237 := bbase (se 4 (by rfl) ⟨316053, by rfl⟩ : syracuseStep 3371237 = 632107) (by norm_num)
theorem B2248949 : Blo 1498069 2248949 := bbase (se 5 (by rfl) ⟨105419, by rfl⟩ : syracuseStep 2248949 = 210839) (by norm_num)
theorem B2846981 : Blo 1498069 2846981 := bbase (se 4 (by rfl) ⟨266904, by rfl⟩ : syracuseStep 2846981 = 533809) (by norm_num)
theorem B2248973 : Blo 1498069 2248973 := bbase (se 3 (by rfl) ⟨421682, by rfl⟩ : syracuseStep 2248973 = 843365) (by norm_num)
theorem B6402341 : Blo 1498069 6402341 := bbase (se 4 (by rfl) ⟨600219, by rfl⟩ : syracuseStep 6402341 = 1200439) (by norm_num)
theorem B2248997 : Blo 1498069 2248997 := bbase (se 4 (by rfl) ⟨210843, by rfl⟩ : syracuseStep 2248997 = 421687) (by norm_num)
theorem B3371309 : Blo 1498069 3371309 := bbase (se 3 (by rfl) ⟨632120, by rfl⟩ : syracuseStep 3371309 = 1264241) (by norm_num)
theorem B2249021 : Blo 1498069 2249021 := bbase (se 3 (by rfl) ⟨421691, by rfl⟩ : syracuseStep 2249021 = 843383) (by norm_num)
theorem B5476693 : Blo 1498069 5476693 := bbase (se 10 (by rfl) ⟨8022, by rfl⟩ : syracuseStep 5476693 = 16045) (by norm_num)
theorem B2249045 : Blo 1498069 2249045 := bbase (se 10 (by rfl) ⟨3294, by rfl⟩ : syracuseStep 2249045 = 6589) (by norm_num)
theorem B1896797 : Blo 1498069 1896797 := bbase (se 3 (by rfl) ⟨355649, by rfl⟩ : syracuseStep 1896797 = 711299) (by norm_num)
theorem B2249069 : Blo 1498069 2249069 := bbase (se 3 (by rfl) ⟨421700, by rfl⟩ : syracuseStep 2249069 = 843401) (by norm_num)
theorem B3371381 : Blo 1498069 3371381 := bbase (se 5 (by rfl) ⟨158033, by rfl⟩ : syracuseStep 3371381 = 316067) (by norm_num)
theorem B2249093 : Blo 1498069 2249093 := bbase (se 4 (by rfl) ⟨210852, by rfl⟩ : syracuseStep 2249093 = 421705) (by norm_num)
theorem B1896853 : Blo 1498069 1896853 := bbase (se 6 (by rfl) ⟨44457, by rfl⟩ : syracuseStep 1896853 = 88915) (by norm_num)
theorem B2847125 : Blo 1498069 2847125 := bbase (se 6 (by rfl) ⟨66729, by rfl⟩ : syracuseStep 2847125 = 133459) (by norm_num)
theorem B2249117 : Blo 1498069 2249117 := bbase (se 3 (by rfl) ⟨421709, by rfl⟩ : syracuseStep 2249117 = 843419) (by norm_num)
theorem B2249141 : Blo 1498069 2249141 := bbase (se 5 (by rfl) ⟨105428, by rfl⟩ : syracuseStep 2249141 = 210857) (by norm_num)
theorem B3371453 : Blo 1498069 3371453 := bbase (se 3 (by rfl) ⟨632147, by rfl⟩ : syracuseStep 3371453 = 1264295) (by norm_num)
theorem B2249165 : Blo 1498069 2249165 := bbase (se 3 (by rfl) ⟨421718, by rfl⟩ : syracuseStep 2249165 = 843437) (by norm_num)
theorem B3650005 : Blo 1498069 3650005 := bbase (se 7 (by rfl) ⟨42773, by rfl⟩ : syracuseStep 3650005 = 85547) (by norm_num)
theorem B2249189 : Blo 1498069 2249189 := bbase (se 4 (by rfl) ⟨210861, by rfl⟩ : syracuseStep 2249189 = 421723) (by norm_num)
theorem B1896949 : Blo 1498069 1896949 := bbase (se 5 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 1896949 = 177839) (by norm_num)
theorem B2249213 : Blo 1498069 2249213 := bbase (se 3 (by rfl) ⟨421727, by rfl⟩ : syracuseStep 2249213 = 843455) (by norm_num)
theorem B3371525 : Blo 1498069 3371525 := bbase (se 4 (by rfl) ⟨316080, by rfl⟩ : syracuseStep 3371525 = 632161) (by norm_num)
theorem B2249237 : Blo 1498069 2249237 := bbase (se 6 (by rfl) ⟨52716, by rfl⟩ : syracuseStep 2249237 = 105433) (by norm_num)
theorem B2249261 : Blo 1498069 2249261 := bbase (se 3 (by rfl) ⟨421736, by rfl⟩ : syracuseStep 2249261 = 843473) (by norm_num)
theorem B2249285 : Blo 1498069 2249285 := bbase (se 4 (by rfl) ⟨210870, by rfl⟩ : syracuseStep 2249285 = 421741) (by norm_num)
theorem B3371597 : Blo 1498069 3371597 := bbase (se 3 (by rfl) ⟨632174, by rfl⟩ : syracuseStep 3371597 = 1264349) (by norm_num)
theorem B2249309 : Blo 1498069 2249309 := bbase (se 3 (by rfl) ⟨421745, by rfl⟩ : syracuseStep 2249309 = 843491) (by norm_num)
theorem B1733233 : Blo 1498069 1733233 := bbase (se 2 (by rfl) ⟨649962, by rfl⟩ : syracuseStep 1733233 = 1299925) (by norm_num)
theorem B2249333 : Blo 1498069 2249333 := bbase (se 5 (by rfl) ⟨105437, by rfl⟩ : syracuseStep 2249333 = 210875) (by norm_num)
theorem B5059205 : Blo 1498069 5059205 := bbase (se 4 (by rfl) ⟨474300, by rfl⟩ : syracuseStep 5059205 = 948601) (by norm_num)
theorem B2249357 : Blo 1498069 2249357 := bbase (se 3 (by rfl) ⟨421754, by rfl⟩ : syracuseStep 2249357 = 843509) (by norm_num)
theorem B3371669 : Blo 1498069 3371669 := bbase (se 6 (by rfl) ⟨79023, by rfl⟩ : syracuseStep 3371669 = 158047) (by norm_num)
theorem B1897121 : Blo 1498069 1897121 := bbase (se 2 (by rfl) ⟨711420, by rfl⟩ : syracuseStep 1897121 = 1422841) (by norm_num)
theorem B2249381 : Blo 1498069 2249381 := bbase (se 4 (by rfl) ⟨210879, by rfl⟩ : syracuseStep 2249381 = 421759) (by norm_num)
theorem B7205557 : Blo 1498069 7205557 := bbase (se 5 (by rfl) ⟨337760, by rfl⟩ : syracuseStep 7205557 = 675521) (by norm_num)
theorem B2847413 : Blo 1498069 2847413 := bbase (se 5 (by rfl) ⟨133472, by rfl⟩ : syracuseStep 2847413 = 266945) (by norm_num)
theorem B2249405 : Blo 1498069 2249405 := bbase (se 3 (by rfl) ⟨421763, by rfl⟩ : syracuseStep 2249405 = 843527) (by norm_num)
theorem B2249429 : Blo 1498069 2249429 := bbase (se 7 (by rfl) ⟨26360, by rfl⟩ : syracuseStep 2249429 = 52721) (by norm_num)
theorem B1897177 : Blo 1498069 1897177 := bbase (se 2 (by rfl) ⟨711441, by rfl⟩ : syracuseStep 1897177 = 1422883) (by norm_num)
theorem B3371741 : Blo 1498069 3371741 := bbase (se 3 (by rfl) ⟨632201, by rfl⟩ : syracuseStep 3371741 = 1264403) (by norm_num)
theorem B3420893 : Blo 1498069 3420893 := bbase (se 3 (by rfl) ⟨641417, by rfl⟩ : syracuseStep 3420893 = 1282835) (by norm_num)
theorem B2249453 : Blo 1498069 2249453 := bbase (se 3 (by rfl) ⟨421772, by rfl⟩ : syracuseStep 2249453 = 843545) (by norm_num)
theorem B1520365 : Blo 1498069 1520365 := bbase (se 3 (by rfl) ⟨285068, by rfl⟩ : syracuseStep 1520365 = 570137) (by norm_num)
theorem B2249477 : Blo 1498069 2249477 := bbase (se 4 (by rfl) ⟨210888, by rfl⟩ : syracuseStep 2249477 = 421777) (by norm_num)
theorem B2249501 : Blo 1498069 2249501 := bbase (se 3 (by rfl) ⟨421781, by rfl⟩ : syracuseStep 2249501 = 843563) (by norm_num)
theorem B3371813 : Blo 1498069 3371813 := bbase (se 4 (by rfl) ⟨316107, by rfl⟩ : syracuseStep 3371813 = 632215) (by norm_num)
theorem B2249525 : Blo 1498069 2249525 := bbase (se 5 (by rfl) ⟨105446, by rfl⟩ : syracuseStep 2249525 = 210893) (by norm_num)
theorem B1897273 : Blo 1498069 1897273 := bbase (se 2 (by rfl) ⟨711477, by rfl⟩ : syracuseStep 1897273 = 1422955) (by norm_num)
theorem B2528077 : Blo 1498069 2528077 := bbase (se 3 (by rfl) ⟨474014, by rfl⟩ : syracuseStep 2528077 = 948029) (by norm_num)
theorem B2249549 : Blo 1498069 2249549 := bbase (se 3 (by rfl) ⟨421790, by rfl⟩ : syracuseStep 2249549 = 843581) (by norm_num)
theorem B2847565 : Blo 1498069 2847565 := bbase (se 3 (by rfl) ⟨533918, by rfl⟩ : syracuseStep 2847565 = 1067837) (by norm_num)
theorem B2249573 : Blo 1498069 2249573 := bbase (se 4 (by rfl) ⟨210897, by rfl⟩ : syracuseStep 2249573 = 421795) (by norm_num)
theorem B3371885 : Blo 1498069 3371885 := bbase (se 3 (by rfl) ⟨632228, by rfl⟩ : syracuseStep 3371885 = 1264457) (by norm_num)
theorem B3208061 : Blo 1498069 3208061 := bbase (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) (by norm_num)
theorem B2249597 : Blo 1498069 2249597 := bbase (se 3 (by rfl) ⟨421799, by rfl⟩ : syracuseStep 2249597 = 843599) (by norm_num)
theorem B2249621 : Blo 1498069 2249621 := bbase (se 6 (by rfl) ⟨52725, by rfl⟩ : syracuseStep 2249621 = 105451) (by norm_num)
theorem B2528165 : Blo 1498069 2528165 := bbase (se 4 (by rfl) ⟨237015, by rfl⟩ : syracuseStep 2528165 = 474031) (by norm_num)
theorem B2249645 : Blo 1498069 2249645 := bbase (se 3 (by rfl) ⟨421808, by rfl⟩ : syracuseStep 2249645 = 843617) (by norm_num)
theorem B3371957 : Blo 1498069 3371957 := bbase (se 5 (by rfl) ⟨158060, by rfl⟩ : syracuseStep 3371957 = 316121) (by norm_num)
theorem B11539381 : Blo 1498069 11539381 := bbase (se 5 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 11539381 = 1081817) (by norm_num)
theorem B2249669 : Blo 1498069 2249669 := bbase (se 4 (by rfl) ⟨210906, by rfl⟩ : syracuseStep 2249669 = 421813) (by norm_num)
theorem B3650509 : Blo 1498069 3650509 := bbase (se 3 (by rfl) ⟨684470, by rfl⟩ : syracuseStep 3650509 = 1368941) (by norm_num)
theorem B2249693 : Blo 1498069 2249693 := bbase (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) (by norm_num)
theorem B1897445 : Blo 1498069 1897445 := bbase (se 4 (by rfl) ⟨177885, by rfl⟩ : syracuseStep 1897445 = 355771) (by norm_num)
theorem B2249717 : Blo 1498069 2249717 := bbase (se 5 (by rfl) ⟨105455, by rfl⟩ : syracuseStep 2249717 = 210911) (by norm_num)
theorem B3372029 : Blo 1498069 3372029 := bbase (se 3 (by rfl) ⟨632255, by rfl⟩ : syracuseStep 3372029 = 1264511) (by norm_num)
theorem B2249741 : Blo 1498069 2249741 := bbase (se 3 (by rfl) ⟨421826, by rfl⟩ : syracuseStep 2249741 = 843653) (by norm_num)
theorem B1897501 : Blo 1498069 1897501 := bbase (se 3 (by rfl) ⟨355781, by rfl⟩ : syracuseStep 1897501 = 711563) (by norm_num)
theorem B2528293 : Blo 1498069 2528293 := bbase (se 4 (by rfl) ⟨237027, by rfl⟩ : syracuseStep 2528293 = 474055) (by norm_num)
theorem B2249765 : Blo 1498069 2249765 := bbase (se 4 (by rfl) ⟨210915, by rfl⟩ : syracuseStep 2249765 = 421831) (by norm_num)
theorem B5059637 : Blo 1498069 5059637 := bbase (se 5 (by rfl) ⟨237170, by rfl⟩ : syracuseStep 5059637 = 474341) (by norm_num)
theorem B2249789 : Blo 1498069 2249789 := bbase (se 3 (by rfl) ⟨421835, by rfl⟩ : syracuseStep 2249789 = 843671) (by norm_num)
theorem B3372101 : Blo 1498069 3372101 := bbase (se 4 (by rfl) ⟨316134, by rfl⟩ : syracuseStep 3372101 = 632269) (by norm_num)
theorem B3200077 : Blo 1498069 3200077 := bbase (se 3 (by rfl) ⟨600014, by rfl⟩ : syracuseStep 3200077 = 1200029) (by norm_num)
theorem B2249813 : Blo 1498069 2249813 := bbase (se 8 (by rfl) ⟨13182, by rfl⟩ : syracuseStep 2249813 = 26365) (by norm_num)
theorem B2249837 : Blo 1498069 2249837 := bbase (se 3 (by rfl) ⟨421844, by rfl⟩ : syracuseStep 2249837 = 843689) (by norm_num)
theorem B2528381 : Blo 1498069 2528381 := bbase (se 3 (by rfl) ⟨474071, by rfl⟩ : syracuseStep 2528381 = 948143) (by norm_num)
theorem B1897597 : Blo 1498069 1897597 := bbase (se 3 (by rfl) ⟨355799, by rfl⟩ : syracuseStep 1897597 = 711599) (by norm_num)
theorem B2135173 : Blo 1498069 2135173 := bbase (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) (by norm_num)
theorem B2249861 : Blo 1498069 2249861 := bbase (se 4 (by rfl) ⟨210924, by rfl⟩ : syracuseStep 2249861 = 421849) (by norm_num)
theorem B3372173 : Blo 1498069 3372173 := bbase (se 3 (by rfl) ⟨632282, by rfl⟩ : syracuseStep 3372173 = 1264565) (by norm_num)
theorem B2249885 : Blo 1498069 2249885 := bbase (se 3 (by rfl) ⟨421853, by rfl⟩ : syracuseStep 2249885 = 843707) (by norm_num)
theorem B1922225 : Blo 1498069 1922225 := bbase (se 2 (by rfl) ⟨720834, by rfl⟩ : syracuseStep 1922225 = 1441669) (by norm_num)
theorem B2249909 : Blo 1498069 2249909 := bbase (se 5 (by rfl) ⟨105464, by rfl⟩ : syracuseStep 2249909 = 210929) (by norm_num)
theorem B3601597 : Blo 1498069 3601597 := bbase (se 3 (by rfl) ⟨675299, by rfl⟩ : syracuseStep 3601597 = 1350599) (by norm_num)
theorem B2249933 : Blo 1498069 2249933 := bbase (se 3 (by rfl) ⟨421862, by rfl⟩ : syracuseStep 2249933 = 843725) (by norm_num)
theorem B3372245 : Blo 1498069 3372245 := bbase (se 7 (by rfl) ⟨39518, by rfl⟩ : syracuseStep 3372245 = 79037) (by norm_num)
theorem B2249957 : Blo 1498069 2249957 := bbase (se 4 (by rfl) ⟨210933, by rfl⟩ : syracuseStep 2249957 = 421867) (by norm_num)
theorem B7591157 : Blo 1498069 7591157 := bbase (se 5 (by rfl) ⟨355835, by rfl⟩ : syracuseStep 7591157 = 711671) (by norm_num)
theorem B2528509 : Blo 1498069 2528509 := bbase (se 3 (by rfl) ⟨474095, by rfl⟩ : syracuseStep 2528509 = 948191) (by norm_num)
theorem B2700541 : Blo 1498069 2700541 := bbase (se 3 (by rfl) ⟨506351, by rfl⟩ : syracuseStep 2700541 = 1012703) (by norm_num)
theorem B2249981 : Blo 1498069 2249981 := bbase (se 3 (by rfl) ⟨421871, by rfl⟩ : syracuseStep 2249981 = 843743) (by norm_num)
theorem B2250005 : Blo 1498069 2250005 := bbase (se 6 (by rfl) ⟨52734, by rfl⟩ : syracuseStep 2250005 = 105469) (by norm_num)
theorem B3372317 : Blo 1498069 3372317 := bbase (se 3 (by rfl) ⟨632309, by rfl⟩ : syracuseStep 3372317 = 1264619) (by norm_num)
theorem B1897769 : Blo 1498069 1897769 := bbase (se 2 (by rfl) ⟨711663, by rfl⟩ : syracuseStep 1897769 = 1423327) (by norm_num)
theorem B2250029 : Blo 1498069 2250029 := bbase (se 3 (by rfl) ⟨421880, by rfl⟩ : syracuseStep 2250029 = 843761) (by norm_num)
theorem B5199173 : Blo 1498069 5199173 := bbase (se 4 (by rfl) ⟨487422, by rfl⟩ : syracuseStep 5199173 = 974845) (by norm_num)
theorem B2250053 : Blo 1498069 2250053 := bbase (se 4 (by rfl) ⟨210942, by rfl⟩ : syracuseStep 2250053 = 421885) (by norm_num)
theorem B2528597 : Blo 1498069 2528597 := bbase (se 14 (by rfl) ⟨231, by rfl⟩ : syracuseStep 2528597 = 463) (by norm_num)
theorem B2250077 : Blo 1498069 2250077 := bbase (se 3 (by rfl) ⟨421889, by rfl⟩ : syracuseStep 2250077 = 843779) (by norm_num)
theorem B1897825 : Blo 1498069 1897825 := bbase (se 2 (by rfl) ⟨711684, by rfl⟩ : syracuseStep 1897825 = 1423369) (by norm_num)
theorem B3372389 : Blo 1498069 3372389 := bbase (se 4 (by rfl) ⟨316161, by rfl⟩ : syracuseStep 3372389 = 632323) (by norm_num)
theorem B4560229 : Blo 1498069 4560229 := bbase (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) (by norm_num)
theorem B1709429 : Blo 1498069 1709429 := bbase (se 5 (by rfl) ⟨80129, by rfl⟩ : syracuseStep 1709429 = 160259) (by norm_num)
theorem B8541557 : Blo 1498069 8541557 := bbase (se 5 (by rfl) ⟨400385, by rfl⟩ : syracuseStep 8541557 = 800771) (by norm_num)
theorem B2250101 : Blo 1498069 2250101 := bbase (se 5 (by rfl) ⟨105473, by rfl⟩ : syracuseStep 2250101 = 210947) (by norm_num)
theorem B3372461 : Blo 1498069 3372461 := bbase (se 3 (by rfl) ⟨632336, by rfl⟩ : syracuseStep 3372461 = 1264673) (by norm_num)
theorem B1897921 : Blo 1498069 1897921 := bbase (se 2 (by rfl) ⟨711720, by rfl⟩ : syracuseStep 1897921 = 1423441) (by norm_num)
theorem B2528725 : Blo 1498069 2528725 := bbase (se 7 (by rfl) ⟨29633, by rfl⟩ : syracuseStep 2528725 = 59267) (by norm_num)
theorem B5060069 : Blo 1498069 5060069 := bbase (se 4 (by rfl) ⟨474381, by rfl⟩ : syracuseStep 5060069 = 948763) (by norm_num)
theorem B6075893 : Blo 1498069 6075893 := bbase (se 5 (by rfl) ⟨284807, by rfl⟩ : syracuseStep 6075893 = 569615) (by norm_num)
theorem B3372533 : Blo 1498069 3372533 := bbase (se 5 (by rfl) ⟨158087, by rfl⟩ : syracuseStep 3372533 = 316175) (by norm_num)
theorem B2528813 : Blo 1498069 2528813 := bbase (se 3 (by rfl) ⟨474152, by rfl⟩ : syracuseStep 2528813 = 948305) (by norm_num)
theorem B3200573 : Blo 1498069 3200573 := bbase (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) (by norm_num)
theorem B3372605 : Blo 1498069 3372605 := bbase (se 3 (by rfl) ⟨632363, by rfl⟩ : syracuseStep 3372605 = 1264727) (by norm_num)
theorem B1799761 : Blo 1498069 1799761 := bbase (se 2 (by rfl) ⟨674910, by rfl⟩ : syracuseStep 1799761 = 1349821) (by norm_num)
theorem B1898093 : Blo 1498069 1898093 := bbase (se 3 (by rfl) ⟨355892, by rfl⟩ : syracuseStep 1898093 = 711785) (by norm_num)
theorem B3372677 : Blo 1498069 3372677 := bbase (se 4 (by rfl) ⟨316188, by rfl⟩ : syracuseStep 3372677 = 632377) (by norm_num)
theorem B1898149 : Blo 1498069 1898149 := bbase (se 4 (by rfl) ⟨177951, by rfl⟩ : syracuseStep 1898149 = 355903) (by norm_num)
theorem B2528941 : Blo 1498069 2528941 := bbase (se 3 (by rfl) ⟨474176, by rfl⟩ : syracuseStep 2528941 = 948353) (by norm_num)
theorem B3372749 : Blo 1498069 3372749 := bbase (se 3 (by rfl) ⟨632390, by rfl⟩ : syracuseStep 3372749 = 1264781) (by norm_num)
theorem B2135765 : Blo 1498069 2135765 := bbase (se 7 (by rfl) ⟨25028, by rfl⟩ : syracuseStep 2135765 = 50057) (by norm_num)
theorem B2529029 : Blo 1498069 2529029 := bbase (se 4 (by rfl) ⟨237096, by rfl⟩ : syracuseStep 2529029 = 474193) (by norm_num)
theorem B1898245 : Blo 1498069 1898245 := bbase (se 4 (by rfl) ⟨177960, by rfl⟩ : syracuseStep 1898245 = 355921) (by norm_num)
theorem B3372821 : Blo 1498069 3372821 := bbase (se 6 (by rfl) ⟨79050, by rfl⟩ : syracuseStep 3372821 = 158101) (by norm_num)
theorem B3372893 : Blo 1498069 3372893 := bbase (se 3 (by rfl) ⟨632417, by rfl⟩ : syracuseStep 3372893 = 1264835) (by norm_num)
theorem B1685353 : Blo 1498069 1685353 := bbase (se 2 (by rfl) ⟨632007, by rfl⟩ : syracuseStep 1685353 = 1264015) (by norm_num)
theorem B2529157 : Blo 1498069 2529157 := bbase (se 4 (by rfl) ⟨237108, by rfl⟩ : syracuseStep 2529157 = 474217) (by norm_num)
theorem B1685389 : Blo 1498069 1685389 := bbase (se 3 (by rfl) ⟨316010, by rfl⟩ : syracuseStep 1685389 = 632021) (by norm_num)
theorem B5060501 : Blo 1498069 5060501 := bbase (se 6 (by rfl) ⟨118605, by rfl⟩ : syracuseStep 5060501 = 237211) (by norm_num)
theorem B3372965 : Blo 1498069 3372965 := bbase (se 4 (by rfl) ⟨316215, by rfl⟩ : syracuseStep 3372965 = 632431) (by norm_num)
theorem B1685425 : Blo 1498069 1685425 := bbase (se 2 (by rfl) ⟨632034, by rfl⟩ : syracuseStep 1685425 = 1264069) (by norm_num)
theorem B1898417 : Blo 1498069 1898417 := bbase (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) (by norm_num)
theorem B1685461 : Blo 1498069 1685461 := bbase (se 7 (by rfl) ⟨19751, by rfl⟩ : syracuseStep 1685461 = 39503) (by norm_num)
theorem B1800149 : Blo 1498069 1800149 := bbase (se 7 (by rfl) ⟨21095, by rfl⟩ : syracuseStep 1800149 = 42191) (by norm_num)
theorem B2529245 : Blo 1498069 2529245 := bbase (se 3 (by rfl) ⟨474233, by rfl⟩ : syracuseStep 2529245 = 948467) (by norm_num)
theorem B1898473 : Blo 1498069 1898473 := bbase (se 2 (by rfl) ⟨711927, by rfl⟩ : syracuseStep 1898473 = 1423855) (by norm_num)
theorem B3373037 : Blo 1498069 3373037 := bbase (se 3 (by rfl) ⟨632444, by rfl⟩ : syracuseStep 3373037 = 1264889) (by norm_num)
theorem B1685497 : Blo 1498069 1685497 := bbase (se 2 (by rfl) ⟨632061, by rfl⟩ : syracuseStep 1685497 = 1264123) (by norm_num)
theorem B1685533 : Blo 1498069 1685533 := bbase (se 3 (by rfl) ⟨316037, by rfl⟩ : syracuseStep 1685533 = 632075) (by norm_num)
theorem B3373109 : Blo 1498069 3373109 := bbase (se 5 (by rfl) ⟨158114, by rfl⟩ : syracuseStep 3373109 = 316229) (by norm_num)
theorem B1685569 : Blo 1498069 1685569 := bbase (se 2 (by rfl) ⟨632088, by rfl⟩ : syracuseStep 1685569 = 1264177) (by norm_num)
theorem B1923149 : Blo 1498069 1923149 := bbase (se 3 (by rfl) ⟨360590, by rfl⟩ : syracuseStep 1923149 = 721181) (by norm_num)
theorem B3848269 : Blo 1498069 3848269 := bbase (se 3 (by rfl) ⟨721550, by rfl⟩ : syracuseStep 3848269 = 1443101) (by norm_num)
theorem B2529373 : Blo 1498069 2529373 := bbase (se 3 (by rfl) ⟨474257, by rfl⟩ : syracuseStep 2529373 = 948515) (by norm_num)
theorem B1685605 : Blo 1498069 1685605 := bbase (se 4 (by rfl) ⟨158025, by rfl⟩ : syracuseStep 1685605 = 316051) (by norm_num)
theorem B3373181 : Blo 1498069 3373181 := bbase (se 3 (by rfl) ⟨632471, by rfl⟩ : syracuseStep 3373181 = 1264943) (by norm_num)
theorem B1685641 : Blo 1498069 1685641 := bbase (se 2 (by rfl) ⟨632115, by rfl⟩ : syracuseStep 1685641 = 1264231) (by norm_num)
theorem B1685677 : Blo 1498069 1685677 := bbase (se 3 (by rfl) ⟨316064, by rfl⟩ : syracuseStep 1685677 = 632129) (by norm_num)
theorem B2529461 : Blo 1498069 2529461 := bbase (se 5 (by rfl) ⟨118568, by rfl⟩ : syracuseStep 2529461 = 237137) (by norm_num)
theorem B3373253 : Blo 1498069 3373253 := bbase (se 4 (by rfl) ⟨316242, by rfl⟩ : syracuseStep 3373253 = 632485) (by norm_num)
theorem B1685713 : Blo 1498069 1685713 := bbase (se 2 (by rfl) ⟨632142, by rfl⟩ : syracuseStep 1685713 = 1264285) (by norm_num)
theorem B46807253 : Blo 1498069 46807253 := bbase (se 7 (by rfl) ⟨548522, by rfl⟩ : syracuseStep 46807253 = 1097045) (by norm_num)
theorem B1710301 : Blo 1498069 1710301 := bbase (se 3 (by rfl) ⟨320681, by rfl⟩ : syracuseStep 1710301 = 641363) (by norm_num)
theorem B3037421 : Blo 1498069 3037421 := bbase (se 3 (by rfl) ⟨569516, by rfl⟩ : syracuseStep 3037421 = 1139033) (by norm_num)
theorem B1685749 : Blo 1498069 1685749 := bbase (se 5 (by rfl) ⟨79019, by rfl⟩ : syracuseStep 1685749 = 158039) (by norm_num)
theorem B4266245 : Blo 1498069 4266245 := bbase (se 4 (by rfl) ⟨399960, by rfl⟩ : syracuseStep 4266245 = 799921) (by norm_num)
theorem B5691653 : Blo 1498069 5691653 := bbase (se 4 (by rfl) ⟨533592, by rfl⟩ : syracuseStep 5691653 = 1067185) (by norm_num)
theorem B3373325 : Blo 1498069 3373325 := bbase (se 3 (by rfl) ⟨632498, by rfl⟩ : syracuseStep 3373325 = 1264997) (by norm_num)
theorem B1685785 : Blo 1498069 1685785 := bbase (se 2 (by rfl) ⟨632169, by rfl⟩ : syracuseStep 1685785 = 1264339) (by norm_num)
theorem B3037493 : Blo 1498069 3037493 := bbase (se 5 (by rfl) ⟨142382, by rfl⟩ : syracuseStep 3037493 = 284765) (by norm_num)
theorem B2529589 : Blo 1498069 2529589 := bbase (se 5 (by rfl) ⟨118574, by rfl⟩ : syracuseStep 2529589 = 237149) (by norm_num)
theorem B13678901 : Blo 1498069 13678901 := bbase (se 5 (by rfl) ⟨641198, by rfl⟩ : syracuseStep 13678901 = 1282397) (by norm_num)
theorem B1800505 : Blo 1498069 1800505 := bbase (se 2 (by rfl) ⟨675189, by rfl⟩ : syracuseStep 1800505 = 1350379) (by norm_num)
theorem B1685821 : Blo 1498069 1685821 := bbase (se 3 (by rfl) ⟨316091, by rfl⟩ : syracuseStep 1685821 = 632183) (by norm_num)
theorem B5060933 : Blo 1498069 5060933 := bbase (se 4 (by rfl) ⟨474462, by rfl⟩ : syracuseStep 5060933 = 948925) (by norm_num)
theorem B3373397 : Blo 1498069 3373397 := bbase (se 10 (by rfl) ⟨4941, by rfl⟩ : syracuseStep 3373397 = 9883) (by norm_num)
theorem B1685857 : Blo 1498069 1685857 := bbase (se 2 (by rfl) ⟨632196, by rfl⟩ : syracuseStep 1685857 = 1264393) (by norm_num)
theorem B1685893 : Blo 1498069 1685893 := bbase (se 4 (by rfl) ⟨158052, by rfl⟩ : syracuseStep 1685893 = 316105) (by norm_num)
theorem B2529677 : Blo 1498069 2529677 := bbase (se 3 (by rfl) ⟨474314, by rfl⟩ : syracuseStep 2529677 = 948629) (by norm_num)
theorem B3373469 : Blo 1498069 3373469 := bbase (se 3 (by rfl) ⟨632525, by rfl⟩ : syracuseStep 3373469 = 1265051) (by norm_num)
theorem B1685929 : Blo 1498069 1685929 := bbase (se 2 (by rfl) ⟨632223, by rfl⟩ : syracuseStep 1685929 = 1264447) (by norm_num)
theorem B3201461 : Blo 1498069 3201461 := bbase (se 5 (by rfl) ⟨150068, by rfl⟩ : syracuseStep 3201461 = 300137) (by norm_num)
theorem B1685965 : Blo 1498069 1685965 := bbase (se 3 (by rfl) ⟨316118, by rfl⟩ : syracuseStep 1685965 = 632237) (by norm_num)
theorem B3373541 : Blo 1498069 3373541 := bbase (se 4 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 3373541 = 632539) (by norm_num)
theorem B1686001 : Blo 1498069 1686001 := bbase (se 2 (by rfl) ⟨632250, by rfl⟩ : syracuseStep 1686001 = 1264501) (by norm_num)
theorem B7592453 : Blo 1498069 7592453 := bbase (se 4 (by rfl) ⟨711792, by rfl⟩ : syracuseStep 7592453 = 1423585) (by norm_num)
theorem B2529805 : Blo 1498069 2529805 := bbase (se 3 (by rfl) ⟨474338, by rfl⟩ : syracuseStep 2529805 = 948677) (by norm_num)
theorem B1686037 : Blo 1498069 1686037 := bbase (se 6 (by rfl) ⟨39516, by rfl⟩ : syracuseStep 1686037 = 79033) (by norm_num)
theorem B2341405 : Blo 1498069 2341405 := bbase (se 3 (by rfl) ⟨439013, by rfl⟩ : syracuseStep 2341405 = 878027) (by norm_num)
theorem B5691941 : Blo 1498069 5691941 := bbase (se 4 (by rfl) ⟨533619, by rfl⟩ : syracuseStep 5691941 = 1067239) (by norm_num)
theorem B3602981 : Blo 1498069 3602981 := bbase (se 4 (by rfl) ⟨337779, by rfl⟩ : syracuseStep 3602981 = 675559) (by norm_num)
theorem B3201581 : Blo 1498069 3201581 := bbase (se 3 (by rfl) ⟨600296, by rfl⟩ : syracuseStep 3201581 = 1200593) (by norm_num)
theorem B3373613 : Blo 1498069 3373613 := bbase (se 3 (by rfl) ⟨632552, by rfl⟩ : syracuseStep 3373613 = 1265105) (by norm_num)
theorem B3602989 : Blo 1498069 3602989 := bbase (se 3 (by rfl) ⟨675560, by rfl⟩ : syracuseStep 3602989 = 1351121) (by norm_num)
theorem B3381805 : Blo 1498069 3381805 := bbase (se 3 (by rfl) ⟨634088, by rfl⟩ : syracuseStep 3381805 = 1268177) (by norm_num)
theorem B1686073 : Blo 1498069 1686073 := bbase (se 2 (by rfl) ⟨632277, by rfl⟩ : syracuseStep 1686073 = 1264555) (by norm_num)
theorem B1686109 : Blo 1498069 1686109 := bbase (se 3 (by rfl) ⟨316145, by rfl⟩ : syracuseStep 1686109 = 632291) (by norm_num)
theorem B2529893 : Blo 1498069 2529893 := bbase (se 4 (by rfl) ⟨237177, by rfl⟩ : syracuseStep 2529893 = 474355) (by norm_num)
theorem B2701925 : Blo 1498069 2701925 := bbase (se 4 (by rfl) ⟨253305, by rfl⟩ : syracuseStep 2701925 = 506611) (by norm_num)
theorem B5765749 : Blo 1498069 5765749 := bbase (se 5 (by rfl) ⟨270269, by rfl⟩ : syracuseStep 5765749 = 540539) (by norm_num)
theorem B3373685 : Blo 1498069 3373685 := bbase (se 5 (by rfl) ⟨158141, by rfl⟩ : syracuseStep 3373685 = 316283) (by norm_num)
theorem B1686145 : Blo 1498069 1686145 := bbase (se 2 (by rfl) ⟨632304, by rfl⟩ : syracuseStep 1686145 = 1264609) (by norm_num)
theorem B1800841 : Blo 1498069 1800841 := bbase (se 2 (by rfl) ⟨675315, by rfl⟩ : syracuseStep 1800841 = 1350631) (by norm_num)
theorem B1686181 : Blo 1498069 1686181 := bbase (se 4 (by rfl) ⟨158079, by rfl⟩ : syracuseStep 1686181 = 316159) (by norm_num)
theorem B2562749 : Blo 1498069 2562749 := bbase (se 3 (by rfl) ⟨480515, by rfl⟩ : syracuseStep 2562749 = 961031) (by norm_num)
theorem B3373757 : Blo 1498069 3373757 := bbase (se 3 (by rfl) ⟨632579, by rfl⟩ : syracuseStep 3373757 = 1265159) (by norm_num)
theorem B1686217 : Blo 1498069 1686217 := bbase (se 2 (by rfl) ⟨632331, by rfl⟩ : syracuseStep 1686217 = 1264663) (by norm_num)
theorem B3078869 : Blo 1498069 3078869 := bbase (se 7 (by rfl) ⟨36080, by rfl⟩ : syracuseStep 3078869 = 72161) (by norm_num)
theorem B2530021 : Blo 1498069 2530021 := bbase (se 4 (by rfl) ⟨237189, by rfl⟩ : syracuseStep 2530021 = 474379) (by norm_num)
theorem B1686253 : Blo 1498069 1686253 := bbase (se 3 (by rfl) ⟨316172, by rfl⟩ : syracuseStep 1686253 = 632345) (by norm_num)
theorem B5061365 : Blo 1498069 5061365 := bbase (se 5 (by rfl) ⟨237251, by rfl⟩ : syracuseStep 5061365 = 474503) (by norm_num)
theorem B3373829 : Blo 1498069 3373829 := bbase (se 4 (by rfl) ⟨316296, by rfl⟩ : syracuseStep 3373829 = 632593) (by norm_num)
theorem B1686289 : Blo 1498069 1686289 := bbase (se 2 (by rfl) ⟨632358, by rfl⟩ : syracuseStep 1686289 = 1264717) (by norm_num)
theorem B1686325 : Blo 1498069 1686325 := bbase (se 5 (by rfl) ⟨79046, by rfl⟩ : syracuseStep 1686325 = 158093) (by norm_num)
theorem B2530109 : Blo 1498069 2530109 := bbase (se 3 (by rfl) ⟨474395, by rfl⟩ : syracuseStep 2530109 = 948791) (by norm_num)
theorem B3373901 : Blo 1498069 3373901 := bbase (se 3 (by rfl) ⟨632606, by rfl⟩ : syracuseStep 3373901 = 1265213) (by norm_num)
theorem B1686361 : Blo 1498069 1686361 := bbase (se 2 (by rfl) ⟨632385, by rfl⟩ : syracuseStep 1686361 = 1264771) (by norm_num)
theorem B3038077 : Blo 1498069 3038077 := bbase (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) (by norm_num)
theorem B1686397 : Blo 1498069 1686397 := bbase (se 3 (by rfl) ⟨316199, by rfl⟩ : syracuseStep 1686397 = 632399) (by norm_num)
theorem B3373973 : Blo 1498069 3373973 := bbase (se 6 (by rfl) ⟨79077, by rfl⟩ : syracuseStep 3373973 = 158155) (by norm_num)
theorem B1686433 : Blo 1498069 1686433 := bbase (se 2 (by rfl) ⟨632412, by rfl⟩ : syracuseStep 1686433 = 1264825) (by norm_num)
theorem B7584677 : Blo 1498069 7584677 := bbase (se 4 (by rfl) ⟨711063, by rfl⟩ : syracuseStep 7584677 = 1422127) (by norm_num)
theorem B2530237 : Blo 1498069 2530237 := bbase (se 3 (by rfl) ⟨474419, by rfl⟩ : syracuseStep 2530237 = 948839) (by norm_num)
theorem B1686469 : Blo 1498069 1686469 := bbase (se 4 (by rfl) ⟨158106, by rfl⟩ : syracuseStep 1686469 = 316213) (by norm_num)
theorem B3374045 : Blo 1498069 3374045 := bbase (se 3 (by rfl) ⟨632633, by rfl⟩ : syracuseStep 3374045 = 1265267) (by norm_num)
theorem B1686505 : Blo 1498069 1686505 := bbase (se 2 (by rfl) ⟨632439, by rfl⟩ : syracuseStep 1686505 = 1264879) (by norm_num)
theorem B1686541 : Blo 1498069 1686541 := bbase (se 3 (by rfl) ⟨316226, by rfl⟩ : syracuseStep 1686541 = 632453) (by norm_num)
theorem B2530325 : Blo 1498069 2530325 := bbase (se 6 (by rfl) ⟨59304, by rfl⟩ : syracuseStep 2530325 = 118609) (by norm_num)
theorem B3374117 : Blo 1498069 3374117 := bbase (se 4 (by rfl) ⟨316323, by rfl⟩ : syracuseStep 3374117 = 632647) (by norm_num)
theorem B1686577 : Blo 1498069 1686577 := bbase (se 2 (by rfl) ⟨632466, by rfl⟩ : syracuseStep 1686577 = 1264933) (by norm_num)
theorem B1686613 : Blo 1498069 1686613 := bbase (se 8 (by rfl) ⟨9882, by rfl⟩ : syracuseStep 1686613 = 19765) (by norm_num)
theorem B3374189 : Blo 1498069 3374189 := bbase (se 3 (by rfl) ⟨632660, by rfl⟩ : syracuseStep 3374189 = 1265321) (by norm_num)
theorem B1686649 : Blo 1498069 1686649 := bbase (se 2 (by rfl) ⟨632493, by rfl⟩ : syracuseStep 1686649 = 1264987) (by norm_num)
theorem B3792005 : Blo 1498069 3792005 := bbase (se 4 (by rfl) ⟨355500, by rfl⟩ : syracuseStep 3792005 = 711001) (by norm_num)
theorem B2530453 : Blo 1498069 2530453 := bbase (se 6 (by rfl) ⟨59307, by rfl⟩ : syracuseStep 2530453 = 118615) (by norm_num)
theorem B1686685 : Blo 1498069 1686685 := bbase (se 3 (by rfl) ⟨316253, by rfl⟩ : syracuseStep 1686685 = 632507) (by norm_num)
theorem B3202213 : Blo 1498069 3202213 := bbase (se 4 (by rfl) ⟨300207, by rfl⟩ : syracuseStep 3202213 = 600415) (by norm_num)
theorem B5061797 : Blo 1498069 5061797 := bbase (se 4 (by rfl) ⟨474543, by rfl⟩ : syracuseStep 5061797 = 949087) (by norm_num)
theorem B3374261 : Blo 1498069 3374261 := bbase (se 5 (by rfl) ⟨158168, by rfl⟩ : syracuseStep 3374261 = 316337) (by norm_num)
theorem B1686721 : Blo 1498069 1686721 := bbase (se 2 (by rfl) ⟨632520, by rfl⟩ : syracuseStep 1686721 = 1265041) (by norm_num)
theorem B1686757 : Blo 1498069 1686757 := bbase (se 4 (by rfl) ⟨158133, by rfl⟩ : syracuseStep 1686757 = 316267) (by norm_num)
theorem B2530541 : Blo 1498069 2530541 := bbase (se 3 (by rfl) ⟨474476, by rfl⟩ : syracuseStep 2530541 = 948953) (by norm_num)
theorem B3374333 : Blo 1498069 3374333 := bbase (se 3 (by rfl) ⟨632687, by rfl⟩ : syracuseStep 3374333 = 1265375) (by norm_num)
theorem B1686793 : Blo 1498069 1686793 := bbase (se 2 (by rfl) ⟨632547, by rfl⟩ : syracuseStep 1686793 = 1265095) (by norm_num)
theorem B7306517 : Blo 1498069 7306517 := bbase (se 6 (by rfl) ⟨171246, by rfl⟩ : syracuseStep 7306517 = 342493) (by norm_num)
theorem B1686829 : Blo 1498069 1686829 := bbase (se 3 (by rfl) ⟨316280, by rfl⟩ : syracuseStep 1686829 = 632561) (by norm_num)
theorem B3792197 : Blo 1498069 3792197 := bbase (se 4 (by rfl) ⟨355518, by rfl⟩ : syracuseStep 3792197 = 711037) (by norm_num)
theorem B3374405 : Blo 1498069 3374405 := bbase (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) (by norm_num)
theorem B1686865 : Blo 1498069 1686865 := bbase (se 2 (by rfl) ⟨632574, by rfl⟩ : syracuseStep 1686865 = 1265149) (by norm_num)
theorem B2530669 : Blo 1498069 2530669 := bbase (se 3 (by rfl) ⟨474500, by rfl⟩ : syracuseStep 2530669 = 949001) (by norm_num)
theorem B1686901 : Blo 1498069 1686901 := bbase (se 5 (by rfl) ⟨79073, by rfl⟩ : syracuseStep 1686901 = 158147) (by norm_num)
theorem B3374477 : Blo 1498069 3374477 := bbase (se 3 (by rfl) ⟨632714, by rfl⟩ : syracuseStep 3374477 = 1265429) (by norm_num)
theorem B1686937 : Blo 1498069 1686937 := bbase (se 2 (by rfl) ⟨632601, by rfl⟩ : syracuseStep 1686937 = 1265203) (by norm_num)
theorem B1686973 : Blo 1498069 1686973 := bbase (se 3 (by rfl) ⟨316307, by rfl⟩ : syracuseStep 1686973 = 632615) (by norm_num)
theorem B2530757 : Blo 1498069 2530757 := bbase (se 4 (by rfl) ⟨237258, by rfl⟩ : syracuseStep 2530757 = 474517) (by norm_num)
theorem B1539533 : Blo 1498069 1539533 := bbase (se 3 (by rfl) ⟨288662, by rfl⟩ : syracuseStep 1539533 = 577325) (by norm_num)
theorem B3374549 : Blo 1498069 3374549 := bbase (se 7 (by rfl) ⟨39545, by rfl⟩ : syracuseStep 3374549 = 79091) (by norm_num)
theorem B1687009 : Blo 1498069 1687009 := bbase (se 2 (by rfl) ⟨632628, by rfl⟩ : syracuseStep 1687009 = 1265257) (by norm_num)
theorem B6839797 : Blo 1498069 6839797 := bbase (se 5 (by rfl) ⟨320615, by rfl⟩ : syracuseStep 6839797 = 641231) (by norm_num)
theorem B1801721 : Blo 1498069 1801721 := bbase (se 2 (by rfl) ⟨675645, by rfl⟩ : syracuseStep 1801721 = 1351291) (by norm_num)
theorem B3038717 : Blo 1498069 3038717 := bbase (se 3 (by rfl) ⟨569759, by rfl⟩ : syracuseStep 3038717 = 1139519) (by norm_num)
theorem B1687045 : Blo 1498069 1687045 := bbase (se 4 (by rfl) ⟨158160, by rfl⟩ : syracuseStep 1687045 = 316321) (by norm_num)
theorem B3603989 : Blo 1498069 3603989 := bbase (se 6 (by rfl) ⟨84468, by rfl⟩ : syracuseStep 3603989 = 168937) (by norm_num)
theorem B3374621 : Blo 1498069 3374621 := bbase (se 3 (by rfl) ⟨632741, by rfl⟩ : syracuseStep 3374621 = 1265483) (by norm_num)
theorem B1687081 : Blo 1498069 1687081 := bbase (se 2 (by rfl) ⟨632655, by rfl⟩ : syracuseStep 1687081 = 1265311) (by norm_num)
theorem B2399789 : Blo 1498069 2399789 := bbase (se 3 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 2399789 = 899921) (by norm_num)
theorem B9600565 : Blo 1498069 9600565 := bbase (se 5 (by rfl) ⟨450026, by rfl⟩ : syracuseStep 9600565 = 900053) (by norm_num)
theorem B2530885 : Blo 1498069 2530885 := bbase (se 4 (by rfl) ⟨237270, by rfl⟩ : syracuseStep 2530885 = 474541) (by norm_num)
theorem B1687117 : Blo 1498069 1687117 := bbase (se 3 (by rfl) ⟨316334, by rfl⟩ : syracuseStep 1687117 = 632669) (by norm_num)
theorem B5062229 : Blo 1498069 5062229 := bbase (se 8 (by rfl) ⟨29661, by rfl⟩ : syracuseStep 5062229 = 59323) (by norm_num)
theorem B3374693 : Blo 1498069 3374693 := bbase (se 4 (by rfl) ⟨316377, by rfl⟩ : syracuseStep 3374693 = 632755) (by norm_num)
theorem B1687153 : Blo 1498069 1687153 := bbase (se 2 (by rfl) ⟨632682, by rfl⟩ : syracuseStep 1687153 = 1265365) (by norm_num)
theorem B4054661 : Blo 1498069 4054661 := bbase (se 4 (by rfl) ⟨380124, by rfl⟩ : syracuseStep 4054661 = 760249) (by norm_num)
theorem B1687189 : Blo 1498069 1687189 := bbase (se 6 (by rfl) ⟨39543, by rfl⟩ : syracuseStep 1687189 = 79087) (by norm_num)
theorem B3792541 : Blo 1498069 3792541 := bbase (se 3 (by rfl) ⟨711101, by rfl⟩ : syracuseStep 3792541 = 1422203) (by norm_num)
theorem B2530973 : Blo 1498069 2530973 := bbase (se 3 (by rfl) ⟨474557, by rfl⟩ : syracuseStep 2530973 = 949115) (by norm_num)
theorem B3374765 : Blo 1498069 3374765 := bbase (se 3 (by rfl) ⟨632768, by rfl⟩ : syracuseStep 3374765 = 1265537) (by norm_num)
theorem B4800181 : Blo 1498069 4800181 := bbase (se 5 (by rfl) ⟨225008, by rfl⟩ : syracuseStep 4800181 = 450017) (by norm_num)
theorem B1687225 : Blo 1498069 1687225 := bbase (se 2 (by rfl) ⟨632709, by rfl⟩ : syracuseStep 1687225 = 1265419) (by norm_num)
theorem B5693125 : Blo 1498069 5693125 := bbase (se 4 (by rfl) ⟨533730, by rfl⟩ : syracuseStep 5693125 = 1067461) (by norm_num)
theorem B1687261 : Blo 1498069 1687261 := bbase (se 3 (by rfl) ⟨316361, by rfl⟩ : syracuseStep 1687261 = 632723) (by norm_num)
theorem B3374837 : Blo 1498069 3374837 := bbase (se 5 (by rfl) ⟨158195, by rfl⟩ : syracuseStep 3374837 = 316391) (by norm_num)
theorem B1687297 : Blo 1498069 1687297 := bbase (se 2 (by rfl) ⟨632736, by rfl⟩ : syracuseStep 1687297 = 1265473) (by norm_num)
theorem B3792653 : Blo 1498069 3792653 := bbase (se 3 (by rfl) ⟨711122, by rfl⟩ : syracuseStep 3792653 = 1422245) (by norm_num)
theorem B7593749 : Blo 1498069 7593749 := bbase (se 6 (by rfl) ⟨177978, by rfl⟩ : syracuseStep 7593749 = 355957) (by norm_num)
theorem B2531101 : Blo 1498069 2531101 := bbase (se 3 (by rfl) ⟨474581, by rfl⟩ : syracuseStep 2531101 = 949163) (by norm_num)
theorem B1687333 : Blo 1498069 1687333 := bbase (se 4 (by rfl) ⟨158187, by rfl⟩ : syracuseStep 1687333 = 316375) (by norm_num)
theorem B1802029 : Blo 1498069 1802029 := bbase (se 3 (by rfl) ⟨337880, by rfl⟩ : syracuseStep 1802029 = 675761) (by norm_num)
theorem B4267829 : Blo 1498069 4267829 := bbase (se 5 (by rfl) ⟨200054, by rfl⟩ : syracuseStep 4267829 = 400109) (by norm_num)
theorem B3374909 : Blo 1498069 3374909 := bbase (se 3 (by rfl) ⟨632795, by rfl⟩ : syracuseStep 3374909 = 1265591) (by norm_num)
theorem B1687369 : Blo 1498069 1687369 := bbase (se 2 (by rfl) ⟨632763, by rfl⟩ : syracuseStep 1687369 = 1265527) (by norm_num)
theorem B1687405 : Blo 1498069 1687405 := bbase (se 3 (by rfl) ⟨316388, by rfl⟩ : syracuseStep 1687405 = 632777) (by norm_num)
theorem B2531189 : Blo 1498069 2531189 := bbase (se 5 (by rfl) ⟨118649, by rfl⟩ : syracuseStep 2531189 = 237299) (by norm_num)
theorem B6840197 : Blo 1498069 6840197 := bbase (se 4 (by rfl) ⟨641268, by rfl⟩ : syracuseStep 6840197 = 1282537) (by norm_num)
theorem B3374981 : Blo 1498069 3374981 := bbase (se 4 (by rfl) ⟨316404, by rfl⟩ : syracuseStep 3374981 = 632809) (by norm_num)
theorem B1687441 : Blo 1498069 1687441 := bbase (se 2 (by rfl) ⟨632790, by rfl⟩ : syracuseStep 1687441 = 1265581) (by norm_num)
theorem B19464085 : Blo 1498069 19464085 := bbase (se 6 (by rfl) ⟨456189, by rfl⟩ : syracuseStep 19464085 = 912379) (by norm_num)
theorem B1687477 : Blo 1498069 1687477 := bbase (se 5 (by rfl) ⟨79100, by rfl⟩ : syracuseStep 1687477 = 158201) (by norm_num)
theorem B3792845 : Blo 1498069 3792845 := bbase (se 3 (by rfl) ⟨711158, by rfl⟩ : syracuseStep 3792845 = 1422317) (by norm_num)
theorem B3375053 : Blo 1498069 3375053 := bbase (se 3 (by rfl) ⟨632822, by rfl⟩ : syracuseStep 3375053 = 1265645) (by norm_num)
theorem B1687513 : Blo 1498069 1687513 := bbase (se 2 (by rfl) ⟨632817, by rfl⟩ : syracuseStep 1687513 = 1265635) (by norm_num)
theorem B5693429 : Blo 1498069 5693429 := bbase (se 5 (by rfl) ⟨266879, by rfl⟩ : syracuseStep 5693429 = 533759) (by norm_num)
theorem B2531317 : Blo 1498069 2531317 := bbase (se 5 (by rfl) ⟨118655, by rfl⟩ : syracuseStep 2531317 = 237311) (by norm_num)
theorem B1499139 : Blo 1498069 1499139 := bstep (se 1 (by rfl) ⟨1124354, by rfl⟩ : syracuseStep 1499139 = 2248709) B2248709
theorem B3375107 : Blo 1498069 3375107 := bstep (se 1 (by rfl) ⟨2531330, by rfl⟩ : syracuseStep 3375107 = 5062661) B5062661
theorem B4268045 : Blo 1498069 4268045 := bstep (se 3 (by rfl) ⟨800258, by rfl⟩ : syracuseStep 4268045 = 1600517) B1600517
theorem B1499155 : Blo 1498069 1499155 := bstep (se 1 (by rfl) ⟨1124366, by rfl⟩ : syracuseStep 1499155 = 2248733) B2248733
theorem B1499171 : Blo 1498069 1499171 := bstep (se 1 (by rfl) ⟨1124378, by rfl⟩ : syracuseStep 1499171 = 2248757) B2248757
theorem B1499187 : Blo 1498069 1499187 := bstep (se 1 (by rfl) ⟨1124390, by rfl⟩ : syracuseStep 1499187 = 2248781) B2248781
theorem B1499203 : Blo 1498069 1499203 := bstep (se 1 (by rfl) ⟨1124402, by rfl⟩ : syracuseStep 1499203 = 2248805) B2248805
theorem B3792977 : Blo 1498069 3792977 := bstep (se 2 (by rfl) ⟨1422366, by rfl⟩ : syracuseStep 3792977 = 2844733) B2844733
theorem B1499219 : Blo 1498069 1499219 := bstep (se 1 (by rfl) ⟨1124414, by rfl⟩ : syracuseStep 1499219 = 2248829) B2248829
theorem B1499235 : Blo 1498069 1499235 := bstep (se 1 (by rfl) ⟨1124426, by rfl⟩ : syracuseStep 1499235 = 2248853) B2248853
theorem B11386979 : Blo 1498069 11386979 := bstep (se 1 (by rfl) ⟨8540234, by rfl⟩ : syracuseStep 11386979 = 17080469) B17080469
theorem B1499251 : Blo 1498069 1499251 := bstep (se 1 (by rfl) ⟨1124438, by rfl⟩ : syracuseStep 1499251 = 2248877) B2248877
theorem B3793027 : Blo 1498069 3793027 := bstep (se 1 (by rfl) ⟨2844770, by rfl⟩ : syracuseStep 3793027 = 5689541) B5689541
theorem B1499267 : Blo 1498069 1499267 := bstep (se 1 (by rfl) ⟨1124450, by rfl⟩ : syracuseStep 1499267 = 2248901) B2248901
theorem B1499283 : Blo 1498069 1499283 := bstep (se 1 (by rfl) ⟨1124462, by rfl⟩ : syracuseStep 1499283 = 2248925) B2248925
theorem B1499299 : Blo 1498069 1499299 := bstep (se 1 (by rfl) ⟨1124474, by rfl⟩ : syracuseStep 1499299 = 2248949) B2248949
theorem B1499315 : Blo 1498069 1499315 := bstep (se 1 (by rfl) ⟨1124486, by rfl⟩ : syracuseStep 1499315 = 2248973) B2248973
theorem B4268227 : Blo 1498069 4268227 := bstep (se 1 (by rfl) ⟨3201170, by rfl⟩ : syracuseStep 4268227 = 6402341) B6402341
theorem B1499331 : Blo 1498069 1499331 := bstep (se 1 (by rfl) ⟨1124498, by rfl⟩ : syracuseStep 1499331 = 2248997) B2248997
theorem B5128397 : Blo 1498069 5128397 := bstep (se 3 (by rfl) ⟨961574, by rfl⟩ : syracuseStep 5128397 = 1923149) B1923149
theorem B1499347 : Blo 1498069 1499347 := bstep (se 1 (by rfl) ⟨1124510, by rfl⟩ : syracuseStep 1499347 = 2249021) B2249021
theorem B1499363 : Blo 1498069 1499363 := bstep (se 1 (by rfl) ⟨1124522, by rfl⟩ : syracuseStep 1499363 = 2249045) B2249045
theorem B1499379 : Blo 1498069 1499379 := bstep (se 1 (by rfl) ⟨1124534, by rfl⟩ : syracuseStep 1499379 = 2249069) B2249069
theorem B1499395 : Blo 1498069 1499395 := bstep (se 1 (by rfl) ⟨1124546, by rfl⟩ : syracuseStep 1499395 = 2249093) B2249093
theorem B3793169 : Blo 1498069 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B1499411 : Blo 1498069 1499411 := bstep (se 1 (by rfl) ⟨1124558, by rfl⟩ : syracuseStep 1499411 = 2249117) B2249117
theorem B1499427 : Blo 1498069 1499427 := bstep (se 1 (by rfl) ⟨1124570, by rfl⟩ : syracuseStep 1499427 = 2249141) B2249141
theorem B1499443 : Blo 1498069 1499443 := bstep (se 1 (by rfl) ⟨1124582, by rfl⟩ : syracuseStep 1499443 = 2249165) B2249165
theorem B1499459 : Blo 1498069 1499459 := bstep (se 1 (by rfl) ⟨1124594, by rfl⟩ : syracuseStep 1499459 = 2249189) B2249189
theorem B1499475 : Blo 1498069 1499475 := bstep (se 1 (by rfl) ⟨1124606, by rfl⟩ : syracuseStep 1499475 = 2249213) B2249213
theorem B1499491 : Blo 1498069 1499491 := bstep (se 1 (by rfl) ⟨1124618, by rfl⟩ : syracuseStep 1499491 = 2249237) B2249237
theorem B1499507 : Blo 1498069 1499507 := bstep (se 1 (by rfl) ⟨1124630, by rfl⟩ : syracuseStep 1499507 = 2249261) B2249261
theorem B1499523 : Blo 1498069 1499523 := bstep (se 1 (by rfl) ⟨1124642, by rfl⟩ : syracuseStep 1499523 = 2249285) B2249285
theorem B1499539 : Blo 1498069 1499539 := bstep (se 1 (by rfl) ⟨1124654, by rfl⟩ : syracuseStep 1499539 = 2249309) B2249309
theorem B2400673 : Blo 1498069 2400673 := bstep (se 2 (by rfl) ⟨900252, by rfl⟩ : syracuseStep 2400673 = 1800505) B1800505
theorem B1499555 : Blo 1498069 1499555 := bstep (se 1 (by rfl) ⟨1124666, by rfl⟩ : syracuseStep 1499555 = 2249333) B2249333
theorem B1499571 : Blo 1498069 1499571 := bstep (se 1 (by rfl) ⟨1124678, by rfl⟩ : syracuseStep 1499571 = 2249357) B2249357
theorem B1499587 : Blo 1498069 1499587 := bstep (se 1 (by rfl) ⟨1124690, by rfl⟩ : syracuseStep 1499587 = 2249381) B2249381
theorem B1499603 : Blo 1498069 1499603 := bstep (se 1 (by rfl) ⟨1124702, by rfl⟩ : syracuseStep 1499603 = 2249405) B2249405
theorem B1499619 : Blo 1498069 1499619 := bstep (se 1 (by rfl) ⟨1124714, by rfl⟩ : syracuseStep 1499619 = 2249429) B2249429
theorem B1499635 : Blo 1498069 1499635 := bstep (se 1 (by rfl) ⟨1124726, by rfl⟩ : syracuseStep 1499635 = 2249453) B2249453
theorem B1499651 : Blo 1498069 1499651 := bstep (se 1 (by rfl) ⟨1124738, by rfl⟩ : syracuseStep 1499651 = 2249477) B2249477
theorem B12812813 : Blo 1498069 12812813 := bstep (se 3 (by rfl) ⟨2402402, by rfl⟩ : syracuseStep 12812813 = 4804805) B4804805
theorem B1499667 : Blo 1498069 1499667 := bstep (se 1 (by rfl) ⟨1124750, by rfl⟩ : syracuseStep 1499667 = 2249501) B2249501
theorem B1499683 : Blo 1498069 1499683 := bstep (se 1 (by rfl) ⟨1124762, by rfl⟩ : syracuseStep 1499683 = 2249525) B2249525
theorem B1499699 : Blo 1498069 1499699 := bstep (se 1 (by rfl) ⟨1124774, by rfl⟩ : syracuseStep 1499699 = 2249549) B2249549
theorem B1499715 : Blo 1498069 1499715 := bstep (se 1 (by rfl) ⟨1124786, by rfl⟩ : syracuseStep 1499715 = 2249573) B2249573
theorem B2138707 : Blo 1498069 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B1499731 : Blo 1498069 1499731 := bstep (se 1 (by rfl) ⟨1124798, by rfl⟩ : syracuseStep 1499731 = 2249597) B2249597
theorem B1499747 : Blo 1498069 1499747 := bstep (se 1 (by rfl) ⟨1124810, by rfl⟩ : syracuseStep 1499747 = 2249621) B2249621
theorem B1499763 : Blo 1498069 1499763 := bstep (se 1 (by rfl) ⟨1124822, by rfl⟩ : syracuseStep 1499763 = 2249645) B2249645
theorem B1499779 : Blo 1498069 1499779 := bstep (se 1 (by rfl) ⟨1124834, by rfl⟩ : syracuseStep 1499779 = 2249669) B2249669
theorem B12804749 : Blo 1498069 12804749 := bstep (se 3 (by rfl) ⟨2400890, by rfl⟩ : syracuseStep 12804749 = 4801781) B4801781
theorem B1499795 : Blo 1498069 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B1499811 : Blo 1498069 1499811 := bstep (se 1 (by rfl) ⟨1124858, by rfl⟩ : syracuseStep 1499811 = 2249717) B2249717
theorem B1499827 : Blo 1498069 1499827 := bstep (se 1 (by rfl) ⟨1124870, by rfl⟩ : syracuseStep 1499827 = 2249741) B2249741
theorem B1499843 : Blo 1498069 1499843 := bstep (se 1 (by rfl) ⟨1124882, by rfl⟩ : syracuseStep 1499843 = 2249765) B2249765
theorem B1499859 : Blo 1498069 1499859 := bstep (se 1 (by rfl) ⟨1124894, by rfl⟩ : syracuseStep 1499859 = 2249789) B2249789
theorem B5128931 : Blo 1498069 5128931 := bstep (se 1 (by rfl) ⟨3846698, by rfl⟩ : syracuseStep 5128931 = 7693397) B7693397
theorem B1499875 : Blo 1498069 1499875 := bstep (se 1 (by rfl) ⟨1124906, by rfl⟩ : syracuseStep 1499875 = 2249813) B2249813
theorem B1499891 : Blo 1498069 1499891 := bstep (se 1 (by rfl) ⟨1124918, by rfl⟩ : syracuseStep 1499891 = 2249837) B2249837
theorem B1499907 : Blo 1498069 1499907 := bstep (se 1 (by rfl) ⟨1124930, by rfl⟩ : syracuseStep 1499907 = 2249861) B2249861
theorem B7693069 : Blo 1498069 7693069 := bstep (se 3 (by rfl) ⟨1442450, by rfl⟩ : syracuseStep 7693069 = 2884901) B2884901
theorem B1499923 : Blo 1498069 1499923 := bstep (se 1 (by rfl) ⟨1124942, by rfl⟩ : syracuseStep 1499923 = 2249885) B2249885
theorem B1499939 : Blo 1498069 1499939 := bstep (se 1 (by rfl) ⟨1124954, by rfl⟩ : syracuseStep 1499939 = 2249909) B2249909
theorem B1499955 : Blo 1498069 1499955 := bstep (se 1 (by rfl) ⟨1124966, by rfl⟩ : syracuseStep 1499955 = 2249933) B2249933
theorem B2310977 : Blo 1498069 2310977 := bstep (se 2 (by rfl) ⟨866616, by rfl⟩ : syracuseStep 2310977 = 1733233) B1733233
theorem B1499971 : Blo 1498069 1499971 := bstep (se 1 (by rfl) ⟨1124978, by rfl⟩ : syracuseStep 1499971 = 2249957) B2249957
theorem B1499987 : Blo 1498069 1499987 := bstep (se 1 (by rfl) ⟨1124990, by rfl⟩ : syracuseStep 1499987 = 2249981) B2249981
theorem B2401121 : Blo 1498069 2401121 := bstep (se 2 (by rfl) ⟨900420, by rfl⟩ : syracuseStep 2401121 = 1800841) B1800841
theorem B1500003 : Blo 1498069 1500003 := bstep (se 1 (by rfl) ⟨1125002, by rfl⟩ : syracuseStep 1500003 = 2250005) B2250005
theorem B29197169 : Blo 1498069 29197169 := bstep (se 2 (by rfl) ⟨10948938, by rfl⟩ : syracuseStep 29197169 = 21897877) B21897877
theorem B1500019 : Blo 1498069 1500019 := bstep (se 1 (by rfl) ⟨1125014, by rfl⟩ : syracuseStep 1500019 = 2250029) B2250029
theorem B3466115 : Blo 1498069 3466115 := bstep (se 1 (by rfl) ⟨2599586, by rfl⟩ : syracuseStep 3466115 = 5199173) B5199173
theorem B1500035 : Blo 1498069 1500035 := bstep (se 1 (by rfl) ⟨1125026, by rfl⟩ : syracuseStep 1500035 = 2250053) B2250053
theorem B1500051 : Blo 1498069 1500051 := bstep (se 1 (by rfl) ⟨1125038, by rfl⟩ : syracuseStep 1500051 = 2250077) B2250077
theorem B5694371 : Blo 1498069 5694371 := bstep (se 1 (by rfl) ⟨4270778, by rfl⟩ : syracuseStep 5694371 = 8541557) B8541557
theorem B1500067 : Blo 1498069 1500067 := bstep (se 1 (by rfl) ⟨1125050, by rfl⟩ : syracuseStep 1500067 = 2250101) B2250101
theorem B4867139 : Blo 1498069 4867139 := bstep (se 1 (by rfl) ⟨3650354, by rfl⟩ : syracuseStep 4867139 = 7300709) B7300709
theorem B4105421 : Blo 1498069 4105421 := bstep (se 3 (by rfl) ⟨769766, by rfl⟩ : syracuseStep 4105421 = 1539533) B1539533
theorem B3794161 : Blo 1498069 3794161 := bstep (se 2 (by rfl) ⟨1422810, by rfl⟩ : syracuseStep 3794161 = 2845621) B2845621
theorem B15385841 : Blo 1498069 15385841 := bstep (se 2 (by rfl) ⟨5769690, by rfl⟩ : syracuseStep 15385841 = 11539381) B11539381
theorem B4867345 : Blo 1498069 4867345 := bstep (se 2 (by rfl) ⟨1825254, by rfl⟩ : syracuseStep 4867345 = 3650509) B3650509
theorem B7587107 : Blo 1498069 7587107 := bstep (se 1 (by rfl) ⟨5690330, by rfl⟩ : syracuseStep 7587107 = 11380661) B11380661
theorem B6489379 : Blo 1498069 6489379 := bstep (se 1 (by rfl) ⟨4867034, by rfl⟩ : syracuseStep 6489379 = 9734069) B9734069
theorem B8103245 : Blo 1498069 8103245 := bstep (se 3 (by rfl) ⟨1519358, by rfl⟩ : syracuseStep 8103245 = 3038717) B3038717
theorem B3081649 : Blo 1498069 3081649 := bstep (se 2 (by rfl) ⟨1155618, by rfl⟩ : syracuseStep 3081649 = 2311237) B2311237
theorem B31204835 : Blo 1498069 31204835 := bstep (se 1 (by rfl) ⟨23403626, by rfl⟩ : syracuseStep 31204835 = 46807253) B46807253
theorem B2024947 : Blo 1498069 2024947 := bstep (se 1 (by rfl) ⟨1518710, by rfl⟩ : syracuseStep 2024947 = 3037421) B3037421
theorem B2311667 : Blo 1498069 2311667 := bstep (se 1 (by rfl) ⟨1733750, by rfl⟩ : syracuseStep 2311667 = 3467501) B3467501
theorem B2844163 : Blo 1498069 2844163 := bstep (se 1 (by rfl) ⟨2133122, by rfl⟩ : syracuseStep 2844163 = 4266245) B4266245
theorem B3794435 : Blo 1498069 3794435 := bstep (se 1 (by rfl) ⟨2845826, by rfl⟩ : syracuseStep 3794435 = 5691653) B5691653
theorem B2024995 : Blo 1498069 2024995 := bstep (se 1 (by rfl) ⟨1518746, by rfl⟩ : syracuseStep 2024995 = 3037493) B3037493
theorem B9119267 : Blo 1498069 9119267 := bstep (se 1 (by rfl) ⟨6839450, by rfl⟩ : syracuseStep 9119267 = 13678901) B13678901
theorem B2844209 : Blo 1498069 2844209 := bstep (se 2 (by rfl) ⟨1066578, by rfl⟩ : syracuseStep 2844209 = 2133157) B2133157
theorem B4269617 : Blo 1498069 4269617 := bstep (se 2 (by rfl) ⟨1601106, by rfl⟩ : syracuseStep 4269617 = 3202213) B3202213
theorem B4802129 : Blo 1498069 4802129 := bstep (se 2 (by rfl) ⟨1800798, by rfl⟩ : syracuseStep 4802129 = 3601597) B3601597
theorem B3794627 : Blo 1498069 3794627 := bstep (se 1 (by rfl) ⟨2845970, by rfl⟩ : syracuseStep 3794627 = 5691941) B5691941
theorem B2401987 : Blo 1498069 2401987 := bstep (se 1 (by rfl) ⟨1801490, by rfl⟩ : syracuseStep 2401987 = 3602981) B3602981
theorem B6080305 : Blo 1498069 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B2844497 : Blo 1498069 2844497 := bstep (se 2 (by rfl) ⟨1066686, by rfl⟩ : syracuseStep 2844497 = 2133373) B2133373
theorem B5056397 : Blo 1498069 5056397 := bstep (se 3 (by rfl) ⟨948074, by rfl⟩ : syracuseStep 5056397 = 1896149) B1896149
theorem B8210317 : Blo 1498069 8210317 := bstep (se 3 (by rfl) ⟨1539434, by rfl⟩ : syracuseStep 8210317 = 3078869) B3078869
theorem B5695373 : Blo 1498069 5695373 := bstep (se 3 (by rfl) ⟨1067882, by rfl⟩ : syracuseStep 5695373 = 2135765) B2135765
theorem B5056451 : Blo 1498069 5056451 := bstep (se 1 (by rfl) ⟨3792338, by rfl⟩ : syracuseStep 5056451 = 7584677) B7584677
theorem B17303537 : Blo 1498069 17303537 := bstep (se 2 (by rfl) ⟨6488826, by rfl⟩ : syracuseStep 17303537 = 12977653) B12977653
theorem B9119729 : Blo 1498069 9119729 := bstep (se 2 (by rfl) ⟨3419898, by rfl⟩ : syracuseStep 9119729 = 6839797) B6839797
theorem B7587917 : Blo 1498069 7587917 := bstep (se 3 (by rfl) ⟨1422734, by rfl⟩ : syracuseStep 7587917 = 2845469) B2845469
theorem B2279555 : Blo 1498069 2279555 := bstep (se 1 (by rfl) ⟨1709666, by rfl⟩ : syracuseStep 2279555 = 3419333) B3419333
theorem B4802755 : Blo 1498069 4802755 := bstep (se 1 (by rfl) ⟨3602066, by rfl⟩ : syracuseStep 4802755 = 7204133) B7204133
theorem B5056721 : Blo 1498069 5056721 := bstep (se 2 (by rfl) ⟨1896270, by rfl⟩ : syracuseStep 5056721 = 3792541) B3792541
theorem B6400241 : Blo 1498069 6400241 := bstep (se 2 (by rfl) ⟨2400090, by rfl⟩ : syracuseStep 6400241 = 4800181) B4800181
theorem B2402659 : Blo 1498069 2402659 := bstep (se 1 (by rfl) ⟨1801994, by rfl⟩ : syracuseStep 2402659 = 3603989) B3603989
theorem B1599859 : Blo 1498069 1599859 := bstep (se 1 (by rfl) ⟨1199894, by rfl⟩ : syracuseStep 1599859 = 2399789) B2399789
theorem B46139789 : Blo 1498069 46139789 := bstep (se 3 (by rfl) ⟨8651210, by rfl⟩ : syracuseStep 46139789 = 17302421) B17302421
theorem B2402705 : Blo 1498069 2402705 := bstep (se 2 (by rfl) ⟨901014, by rfl⟩ : syracuseStep 2402705 = 1802029) B1802029
theorem B2247107 : Blo 1498069 2247107 := bstep (se 1 (by rfl) ⟨1685330, by rfl⟩ : syracuseStep 2247107 = 3370661) B3370661
theorem B19466693 : Blo 1498069 19466693 := bstep (se 4 (by rfl) ⟨1825002, by rfl⟩ : syracuseStep 19466693 = 3650005) B3650005
theorem B2247137 : Blo 1498069 2247137 := bstep (se 2 (by rfl) ⟨842676, by rfl⟩ : syracuseStep 2247137 = 1685353) B1685353
theorem B4270573 : Blo 1498069 4270573 := bstep (se 3 (by rfl) ⟨800732, by rfl⟩ : syracuseStep 4270573 = 1601465) B1601465
theorem B2247155 : Blo 1498069 2247155 := bstep (se 1 (by rfl) ⟨1685366, by rfl⟩ : syracuseStep 2247155 = 3370733) B3370733
theorem B2247185 : Blo 1498069 2247185 := bstep (se 2 (by rfl) ⟨842694, by rfl⟩ : syracuseStep 2247185 = 1685389) B1685389
theorem B2247203 : Blo 1498069 2247203 := bstep (se 1 (by rfl) ⟨1685402, by rfl⟩ : syracuseStep 2247203 = 3370805) B3370805
theorem B2845219 : Blo 1498069 2845219 := bstep (se 1 (by rfl) ⟨2133914, by rfl⟩ : syracuseStep 2845219 = 4267829) B4267829
theorem B2247233 : Blo 1498069 2247233 := bstep (se 2 (by rfl) ⟨842712, by rfl⟩ : syracuseStep 2247233 = 1685425) B1685425
theorem B2247251 : Blo 1498069 2247251 := bstep (se 1 (by rfl) ⟨1685438, by rfl⟩ : syracuseStep 2247251 = 3370877) B3370877
theorem B2247281 : Blo 1498069 2247281 := bstep (se 2 (by rfl) ⟨842730, by rfl⟩ : syracuseStep 2247281 = 1685461) B1685461
theorem B3795569 : Blo 1498069 3795569 := bstep (se 2 (by rfl) ⟨1423338, by rfl⟩ : syracuseStep 3795569 = 2846677) B2846677
theorem B2247299 : Blo 1498069 2247299 := bstep (se 1 (by rfl) ⟨1685474, by rfl⟩ : syracuseStep 2247299 = 3370949) B3370949
theorem B2247329 : Blo 1498069 2247329 := bstep (se 2 (by rfl) ⟨842748, by rfl⟩ : syracuseStep 2247329 = 1685497) B1685497
theorem B3795619 : Blo 1498069 3795619 := bstep (se 1 (by rfl) ⟨2846714, by rfl⟩ : syracuseStep 3795619 = 5693429) B5693429
theorem B2247347 : Blo 1498069 2247347 := bstep (se 1 (by rfl) ⟨1685510, by rfl⟩ : syracuseStep 2247347 = 3371021) B3371021
theorem B2247377 : Blo 1498069 2247377 := bstep (se 2 (by rfl) ⟨842766, by rfl⟩ : syracuseStep 2247377 = 1685533) B1685533
theorem B4270801 : Blo 1498069 4270801 := bstep (se 2 (by rfl) ⟨1601550, by rfl⟩ : syracuseStep 4270801 = 3203101) B3203101
theorem B2247395 : Blo 1498069 2247395 := bstep (se 1 (by rfl) ⟨1685546, by rfl⟩ : syracuseStep 2247395 = 3371093) B3371093
theorem B5057261 : Blo 1498069 5057261 := bstep (se 3 (by rfl) ⟨948236, by rfl⟩ : syracuseStep 5057261 = 1896473) B1896473
theorem B2247425 : Blo 1498069 2247425 := bstep (se 2 (by rfl) ⟨842784, by rfl⟩ : syracuseStep 2247425 = 1685569) B1685569
theorem B9112333 : Blo 1498069 9112333 := bstep (se 3 (by rfl) ⟨1708562, by rfl⟩ : syracuseStep 9112333 = 3417125) B3417125
theorem B5131025 : Blo 1498069 5131025 := bstep (se 2 (by rfl) ⟨1924134, by rfl⟩ : syracuseStep 5131025 = 3848269) B3848269
theorem B2247443 : Blo 1498069 2247443 := bstep (se 1 (by rfl) ⟨1685582, by rfl⟩ : syracuseStep 2247443 = 3371165) B3371165
theorem B5057315 : Blo 1498069 5057315 := bstep (se 1 (by rfl) ⟨3792986, by rfl⟩ : syracuseStep 5057315 = 7585973) B7585973
theorem B2247473 : Blo 1498069 2247473 := bstep (se 2 (by rfl) ⟨842802, by rfl⟩ : syracuseStep 2247473 = 1685605) B1685605
theorem B3795761 : Blo 1498069 3795761 := bstep (se 2 (by rfl) ⟨1423410, by rfl⟩ : syracuseStep 3795761 = 2846821) B2846821
theorem B2247491 : Blo 1498069 2247491 := bstep (se 1 (by rfl) ⟨1685618, by rfl⟩ : syracuseStep 2247491 = 3371237) B3371237
theorem B12487493 : Blo 1498069 12487493 := bstep (se 4 (by rfl) ⟨1170702, by rfl⟩ : syracuseStep 12487493 = 2341405) B2341405
theorem B2247521 : Blo 1498069 2247521 := bstep (se 2 (by rfl) ⟨842820, by rfl⟩ : syracuseStep 2247521 = 1685641) B1685641
theorem B4270961 : Blo 1498069 4270961 := bstep (se 2 (by rfl) ⟨1601610, by rfl⟩ : syracuseStep 4270961 = 3203221) B3203221
theorem B2247539 : Blo 1498069 2247539 := bstep (se 1 (by rfl) ⟨1685654, by rfl⟩ : syracuseStep 2247539 = 3371309) B3371309
theorem B2247569 : Blo 1498069 2247569 := bstep (se 2 (by rfl) ⟨842838, by rfl⟩ : syracuseStep 2247569 = 1685677) B1685677
theorem B2247587 : Blo 1498069 2247587 := bstep (se 1 (by rfl) ⟨1685690, by rfl⟩ : syracuseStep 2247587 = 3371381) B3371381
theorem B2247617 : Blo 1498069 2247617 := bstep (se 2 (by rfl) ⟨842856, by rfl⟩ : syracuseStep 2247617 = 1685713) B1685713
theorem B2280401 : Blo 1498069 2280401 := bstep (se 2 (by rfl) ⟨855150, by rfl⟩ : syracuseStep 2280401 = 1710301) B1710301
theorem B2247635 : Blo 1498069 2247635 := bstep (se 1 (by rfl) ⟨1685726, by rfl⟩ : syracuseStep 2247635 = 3371453) B3371453
theorem B2845667 : Blo 1498069 2845667 := bstep (se 1 (by rfl) ⟨2134250, by rfl⟩ : syracuseStep 2845667 = 4268501) B4268501
theorem B16215011 : Blo 1498069 16215011 := bstep (se 1 (by rfl) ⟨12161258, by rfl⟩ : syracuseStep 16215011 = 24322517) B24322517
theorem B4271075 : Blo 1498069 4271075 := bstep (se 1 (by rfl) ⟨3203306, by rfl⟩ : syracuseStep 4271075 = 6406613) B6406613
theorem B2247665 : Blo 1498069 2247665 := bstep (se 2 (by rfl) ⟨842874, by rfl⟩ : syracuseStep 2247665 = 1685749) B1685749
theorem B2247683 : Blo 1498069 2247683 := bstep (se 1 (by rfl) ⟨1685762, by rfl⟩ : syracuseStep 2247683 = 3371525) B3371525
theorem B8539141 : Blo 1498069 8539141 := bstep (se 4 (by rfl) ⟨800544, by rfl⟩ : syracuseStep 8539141 = 1601089) B1601089
theorem B2247713 : Blo 1498069 2247713 := bstep (se 2 (by rfl) ⟨842892, by rfl⟩ : syracuseStep 2247713 = 1685785) B1685785
theorem B5057585 : Blo 1498069 5057585 := bstep (se 2 (by rfl) ⟨1896594, by rfl⟩ : syracuseStep 5057585 = 3793189) B3793189
theorem B2247731 : Blo 1498069 2247731 := bstep (se 1 (by rfl) ⟨1685798, by rfl⟩ : syracuseStep 2247731 = 3371597) B3371597
theorem B2247761 : Blo 1498069 2247761 := bstep (se 2 (by rfl) ⟨842910, by rfl⟩ : syracuseStep 2247761 = 1685821) B1685821
theorem B2247779 : Blo 1498069 2247779 := bstep (se 1 (by rfl) ⟨1685834, by rfl⟩ : syracuseStep 2247779 = 3371669) B3371669
theorem B7302257 : Blo 1498069 7302257 := bstep (se 2 (by rfl) ⟨2738346, by rfl⟩ : syracuseStep 7302257 = 5476693) B5476693
theorem B2247809 : Blo 1498069 2247809 := bstep (se 2 (by rfl) ⟨842928, by rfl⟩ : syracuseStep 2247809 = 1685857) B1685857
theorem B3599491 : Blo 1498069 3599491 := bstep (se 1 (by rfl) ⟨2699618, by rfl⟩ : syracuseStep 3599491 = 5399237) B5399237
theorem B2247827 : Blo 1498069 2247827 := bstep (se 1 (by rfl) ⟨1685870, by rfl⟩ : syracuseStep 2247827 = 3371741) B3371741
theorem B2247857 : Blo 1498069 2247857 := bstep (se 2 (by rfl) ⟨842946, by rfl⟩ : syracuseStep 2247857 = 1685893) B1685893
theorem B2247875 : Blo 1498069 2247875 := bstep (se 1 (by rfl) ⟨1685906, by rfl⟩ : syracuseStep 2247875 = 3371813) B3371813
theorem B2247905 : Blo 1498069 2247905 := bstep (se 2 (by rfl) ⟨842964, by rfl⟩ : syracuseStep 2247905 = 1685929) B1685929
theorem B2247923 : Blo 1498069 2247923 := bstep (se 1 (by rfl) ⟨1685942, by rfl⟩ : syracuseStep 2247923 = 3371885) B3371885
theorem B2845955 : Blo 1498069 2845955 := bstep (se 1 (by rfl) ⟨2134466, by rfl⟩ : syracuseStep 2845955 = 4268933) B4268933
theorem B2247953 : Blo 1498069 2247953 := bstep (se 2 (by rfl) ⟨842982, by rfl⟩ : syracuseStep 2247953 = 1685965) B1685965
theorem B2247971 : Blo 1498069 2247971 := bstep (se 1 (by rfl) ⟨1685978, by rfl⟩ : syracuseStep 2247971 = 3371957) B3371957
theorem B2248001 : Blo 1498069 2248001 := bstep (se 2 (by rfl) ⟨843000, by rfl⟩ : syracuseStep 2248001 = 1686001) B1686001
theorem B2248019 : Blo 1498069 2248019 := bstep (se 1 (by rfl) ⟨1686014, by rfl⟩ : syracuseStep 2248019 = 3372029) B3372029
theorem B1600867 : Blo 1498069 1600867 := bstep (se 1 (by rfl) ⟨1200650, by rfl⟩ : syracuseStep 1600867 = 2401301) B2401301
theorem B2248049 : Blo 1498069 2248049 := bstep (se 2 (by rfl) ⟨843018, by rfl⟩ : syracuseStep 2248049 = 1686037) B1686037
theorem B34614641 : Blo 1498069 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B2248067 : Blo 1498069 2248067 := bstep (se 1 (by rfl) ⟨1686050, by rfl⟩ : syracuseStep 2248067 = 3372101) B3372101
theorem B4803985 : Blo 1498069 4803985 := bstep (se 2 (by rfl) ⟨1801494, by rfl⟩ : syracuseStep 4803985 = 3602989) B3602989
theorem B4509073 : Blo 1498069 4509073 := bstep (se 2 (by rfl) ⟨1690902, by rfl⟩ : syracuseStep 4509073 = 3381805) B3381805
theorem B2248097 : Blo 1498069 2248097 := bstep (se 2 (by rfl) ⟨843036, by rfl⟩ : syracuseStep 2248097 = 1686073) B1686073
theorem B2248115 : Blo 1498069 2248115 := bstep (se 1 (by rfl) ⟨1686086, by rfl⟩ : syracuseStep 2248115 = 3372173) B3372173
theorem B2248145 : Blo 1498069 2248145 := bstep (se 2 (by rfl) ⟨843054, by rfl⟩ : syracuseStep 2248145 = 1686109) B1686109
theorem B2248163 : Blo 1498069 2248163 := bstep (se 1 (by rfl) ⟨1686122, by rfl⟩ : syracuseStep 2248163 = 3372245) B3372245
theorem B2248193 : Blo 1498069 2248193 := bstep (se 2 (by rfl) ⟨843072, by rfl⟩ : syracuseStep 2248193 = 1686145) B1686145
theorem B2248211 : Blo 1498069 2248211 := bstep (se 1 (by rfl) ⟨1686158, by rfl⟩ : syracuseStep 2248211 = 3372317) B3372317
theorem B2248241 : Blo 1498069 2248241 := bstep (se 2 (by rfl) ⟨843090, by rfl⟩ : syracuseStep 2248241 = 1686181) B1686181
theorem B2248259 : Blo 1498069 2248259 := bstep (se 1 (by rfl) ⟨1686194, by rfl⟩ : syracuseStep 2248259 = 3372389) B3372389
theorem B5058125 : Blo 1498069 5058125 := bstep (se 3 (by rfl) ⟨948398, by rfl⟩ : syracuseStep 5058125 = 1896797) B1896797
theorem B2248289 : Blo 1498069 2248289 := bstep (se 2 (by rfl) ⟨843108, by rfl⟩ : syracuseStep 2248289 = 1686217) B1686217
theorem B2248307 : Blo 1498069 2248307 := bstep (se 1 (by rfl) ⟨1686230, by rfl⟩ : syracuseStep 2248307 = 3372461) B3372461
theorem B5058179 : Blo 1498069 5058179 := bstep (se 1 (by rfl) ⟨3793634, by rfl⟩ : syracuseStep 5058179 = 7587269) B7587269
theorem B2248337 : Blo 1498069 2248337 := bstep (se 2 (by rfl) ⟨843126, by rfl⟩ : syracuseStep 2248337 = 1686253) B1686253
theorem B2027153 : Blo 1498069 2027153 := bstep (se 2 (by rfl) ⟨760182, by rfl⟩ : syracuseStep 2027153 = 1520365) B1520365
theorem B4050595 : Blo 1498069 4050595 := bstep (se 1 (by rfl) ⟨3037946, by rfl⟩ : syracuseStep 4050595 = 6075893) B6075893
theorem B2248355 : Blo 1498069 2248355 := bstep (se 1 (by rfl) ⟨1686266, by rfl⟩ : syracuseStep 2248355 = 3372533) B3372533
theorem B2248385 : Blo 1498069 2248385 := bstep (se 2 (by rfl) ⟨843144, by rfl⟩ : syracuseStep 2248385 = 1686289) B1686289
theorem B2133715 : Blo 1498069 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B2248403 : Blo 1498069 2248403 := bstep (se 1 (by rfl) ⟨1686302, by rfl⟩ : syracuseStep 2248403 = 3372605) B3372605
theorem B2248433 : Blo 1498069 2248433 := bstep (se 2 (by rfl) ⟨843162, by rfl⟩ : syracuseStep 2248433 = 1686325) B1686325
theorem B2248451 : Blo 1498069 2248451 := bstep (se 1 (by rfl) ⟨1686338, by rfl⟩ : syracuseStep 2248451 = 3372677) B3372677
theorem B3370769 : Blo 1498069 3370769 := bstep (se 2 (by rfl) ⟨1264038, by rfl⟩ : syracuseStep 3370769 = 2528077) B2528077
theorem B3796753 : Blo 1498069 3796753 := bstep (se 2 (by rfl) ⟨1423782, by rfl⟩ : syracuseStep 3796753 = 2847565) B2847565
theorem B2248481 : Blo 1498069 2248481 := bstep (se 2 (by rfl) ⟨843180, by rfl⟩ : syracuseStep 2248481 = 1686361) B1686361
theorem B3370787 : Blo 1498069 3370787 := bstep (se 1 (by rfl) ⟨2528090, by rfl⟩ : syracuseStep 3370787 = 5056181) B5056181
theorem B2248499 : Blo 1498069 2248499 := bstep (se 1 (by rfl) ⟨1686374, by rfl⟩ : syracuseStep 2248499 = 3372749) B3372749
theorem B4050769 : Blo 1498069 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B2248529 : Blo 1498069 2248529 := bstep (se 2 (by rfl) ⟨843198, by rfl⟩ : syracuseStep 2248529 = 1686397) B1686397
theorem B2248547 : Blo 1498069 2248547 := bstep (se 1 (by rfl) ⟨1686410, by rfl⟩ : syracuseStep 2248547 = 3372821) B3372821
theorem B2248577 : Blo 1498069 2248577 := bstep (se 2 (by rfl) ⟨843216, by rfl⟩ : syracuseStep 2248577 = 1686433) B1686433
theorem B5058449 : Blo 1498069 5058449 := bstep (se 2 (by rfl) ⟨1896918, by rfl⟩ : syracuseStep 5058449 = 3793837) B3793837
theorem B2248595 : Blo 1498069 2248595 := bstep (se 1 (by rfl) ⟨1686446, by rfl⟩ : syracuseStep 2248595 = 3372893) B3372893
theorem B2248625 : Blo 1498069 2248625 := bstep (se 2 (by rfl) ⟨843234, by rfl⟩ : syracuseStep 2248625 = 1686469) B1686469
theorem B2248643 : Blo 1498069 2248643 := bstep (se 1 (by rfl) ⟨1686482, by rfl⟩ : syracuseStep 2248643 = 3372965) B3372965
theorem B2248673 : Blo 1498069 2248673 := bstep (se 2 (by rfl) ⟨843252, by rfl⟩ : syracuseStep 2248673 = 1686505) B1686505
theorem B4804589 : Blo 1498069 4804589 := bstep (se 3 (by rfl) ⟨900860, by rfl⟩ : syracuseStep 4804589 = 1801721) B1801721
theorem B2248691 : Blo 1498069 2248691 := bstep (se 1 (by rfl) ⟨1686518, by rfl⟩ : syracuseStep 2248691 = 3373037) B3373037
theorem B2248721 : Blo 1498069 2248721 := bstep (se 2 (by rfl) ⟨843270, by rfl⟩ : syracuseStep 2248721 = 1686541) B1686541
theorem B2248739 : Blo 1498069 2248739 := bstep (se 1 (by rfl) ⟨1686554, by rfl⟩ : syracuseStep 2248739 = 3373109) B3373109
theorem B3797027 : Blo 1498069 3797027 := bstep (se 1 (by rfl) ⟨2847770, by rfl⟩ : syracuseStep 3797027 = 5695541) B5695541
theorem B3371057 : Blo 1498069 3371057 := bstep (se 2 (by rfl) ⟨1264146, by rfl⟩ : syracuseStep 3371057 = 2528293) B2528293
theorem B2248769 : Blo 1498069 2248769 := bstep (se 2 (by rfl) ⟨843288, by rfl⟩ : syracuseStep 2248769 = 1686577) B1686577
theorem B3371075 : Blo 1498069 3371075 := bstep (se 1 (by rfl) ⟨2528306, by rfl⟩ : syracuseStep 3371075 = 5056613) B5056613
theorem B2248787 : Blo 1498069 2248787 := bstep (se 1 (by rfl) ⟨1686590, by rfl⟩ : syracuseStep 2248787 = 3373181) B3373181
theorem B2248817 : Blo 1498069 2248817 := bstep (se 2 (by rfl) ⟨843306, by rfl⟩ : syracuseStep 2248817 = 1686613) B1686613
theorem B2248835 : Blo 1498069 2248835 := bstep (se 1 (by rfl) ⟨1686626, by rfl⟩ : syracuseStep 2248835 = 3373253) B3373253
theorem B2248865 : Blo 1498069 2248865 := bstep (se 2 (by rfl) ⟨843324, by rfl⟩ : syracuseStep 2248865 = 1686649) B1686649
theorem B2134193 : Blo 1498069 2134193 := bstep (se 2 (by rfl) ⟨800322, by rfl⟩ : syracuseStep 2134193 = 1600645) B1600645
theorem B2248883 : Blo 1498069 2248883 := bstep (se 1 (by rfl) ⟨1686662, by rfl⟩ : syracuseStep 2248883 = 3373325) B3373325
theorem B2846897 : Blo 1498069 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B2248913 : Blo 1498069 2248913 := bstep (se 2 (by rfl) ⟨843342, by rfl⟩ : syracuseStep 2248913 = 1686685) B1686685
theorem B2248931 : Blo 1498069 2248931 := bstep (se 1 (by rfl) ⟨1686698, by rfl⟩ : syracuseStep 2248931 = 3373397) B3373397
theorem B1896691 : Blo 1498069 1896691 := bstep (se 1 (by rfl) ⟨1422518, by rfl⟩ : syracuseStep 1896691 = 2845037) B2845037
theorem B2248961 : Blo 1498069 2248961 := bstep (se 2 (by rfl) ⟨843360, by rfl⟩ : syracuseStep 2248961 = 1686721) B1686721
theorem B2248979 : Blo 1498069 2248979 := bstep (se 1 (by rfl) ⟨1686734, by rfl⟩ : syracuseStep 2248979 = 3373469) B3373469
theorem B2134307 : Blo 1498069 2134307 := bstep (se 1 (by rfl) ⟨1600730, by rfl⟩ : syracuseStep 2134307 = 3201461) B3201461
theorem B2249009 : Blo 1498069 2249009 := bstep (se 2 (by rfl) ⟨843378, by rfl⟩ : syracuseStep 2249009 = 1686757) B1686757
theorem B2249027 : Blo 1498069 2249027 := bstep (se 1 (by rfl) ⟨1686770, by rfl⟩ : syracuseStep 2249027 = 3373541) B3373541
theorem B3371345 : Blo 1498069 3371345 := bstep (se 2 (by rfl) ⟨1264254, by rfl⟩ : syracuseStep 3371345 = 2528509) B2528509
theorem B3600721 : Blo 1498069 3600721 := bstep (se 2 (by rfl) ⟨1350270, by rfl⟩ : syracuseStep 3600721 = 2700541) B2700541
theorem B1896787 : Blo 1498069 1896787 := bstep (se 1 (by rfl) ⟨1422590, by rfl⟩ : syracuseStep 1896787 = 2845181) B2845181
theorem B1601875 : Blo 1498069 1601875 := bstep (se 1 (by rfl) ⟨1201406, by rfl⟩ : syracuseStep 1601875 = 2402813) B2402813
theorem B2249057 : Blo 1498069 2249057 := bstep (se 2 (by rfl) ⟨843396, by rfl⟩ : syracuseStep 2249057 = 1686793) B1686793
theorem B3371363 : Blo 1498069 3371363 := bstep (se 1 (by rfl) ⟨2528522, by rfl⟩ : syracuseStep 3371363 = 5057045) B5057045
theorem B2134387 : Blo 1498069 2134387 := bstep (se 1 (by rfl) ⟨1600790, by rfl⟩ : syracuseStep 2134387 = 3201581) B3201581
theorem B2249075 : Blo 1498069 2249075 := bstep (se 1 (by rfl) ⟨1686806, by rfl⟩ : syracuseStep 2249075 = 3373613) B3373613
theorem B2249105 : Blo 1498069 2249105 := bstep (se 2 (by rfl) ⟨843414, by rfl⟩ : syracuseStep 2249105 = 1686829) B1686829
theorem B2249123 : Blo 1498069 2249123 := bstep (se 1 (by rfl) ⟨1686842, by rfl⟩ : syracuseStep 2249123 = 3373685) B3373685
theorem B5058989 : Blo 1498069 5058989 := bstep (se 3 (by rfl) ⟨948560, by rfl⟩ : syracuseStep 5058989 = 1897121) B1897121
theorem B8655281 : Blo 1498069 8655281 := bstep (se 2 (by rfl) ⟨3245730, by rfl⟩ : syracuseStep 8655281 = 6491461) B6491461
theorem B2249153 : Blo 1498069 2249153 := bstep (se 2 (by rfl) ⟨843432, by rfl⟩ : syracuseStep 2249153 = 1686865) B1686865
theorem B1708499 : Blo 1498069 1708499 := bstep (se 1 (by rfl) ⟨1281374, by rfl⟩ : syracuseStep 1708499 = 2562749) B2562749
theorem B2249171 : Blo 1498069 2249171 := bstep (se 1 (by rfl) ⟨1686878, by rfl⟩ : syracuseStep 2249171 = 3373757) B3373757
theorem B5059043 : Blo 1498069 5059043 := bstep (se 1 (by rfl) ⟨3794282, by rfl⟩ : syracuseStep 5059043 = 7588565) B7588565
theorem B2249201 : Blo 1498069 2249201 := bstep (se 2 (by rfl) ⟨843450, by rfl⟩ : syracuseStep 2249201 = 1686901) B1686901
theorem B2249219 : Blo 1498069 2249219 := bstep (se 1 (by rfl) ⟨1686914, by rfl⟩ : syracuseStep 2249219 = 3373829) B3373829
theorem B2249249 : Blo 1498069 2249249 := bstep (se 2 (by rfl) ⟨843468, by rfl⟩ : syracuseStep 2249249 = 1686937) B1686937
theorem B2249267 : Blo 1498069 2249267 := bstep (se 1 (by rfl) ⟨1686950, by rfl⟩ : syracuseStep 2249267 = 3373901) B3373901
theorem B9122381 : Blo 1498069 9122381 := bstep (se 3 (by rfl) ⟨1710446, by rfl⟩ : syracuseStep 9122381 = 3420893) B3420893
theorem B2249297 : Blo 1498069 2249297 := bstep (se 2 (by rfl) ⟨843486, by rfl⟩ : syracuseStep 2249297 = 1686973) B1686973
theorem B2249315 : Blo 1498069 2249315 := bstep (se 1 (by rfl) ⟨1686986, by rfl⟩ : syracuseStep 2249315 = 3373973) B3373973
theorem B3371633 : Blo 1498069 3371633 := bstep (se 2 (by rfl) ⟨1264362, by rfl⟩ : syracuseStep 3371633 = 2528725) B2528725
theorem B2249345 : Blo 1498069 2249345 := bstep (se 2 (by rfl) ⟨843504, by rfl⟩ : syracuseStep 2249345 = 1687009) B1687009
theorem B3371651 : Blo 1498069 3371651 := bstep (se 1 (by rfl) ⟨2528738, by rfl⟩ : syracuseStep 3371651 = 5057477) B5057477
theorem B5689997 : Blo 1498069 5689997 := bstep (se 3 (by rfl) ⟨1066874, by rfl⟩ : syracuseStep 5689997 = 2133749) B2133749
theorem B2249363 : Blo 1498069 2249363 := bstep (se 1 (by rfl) ⟨1687022, by rfl⟩ : syracuseStep 2249363 = 3374045) B3374045
theorem B4559537 : Blo 1498069 4559537 := bstep (se 2 (by rfl) ⟨1709826, by rfl⟩ : syracuseStep 4559537 = 3419653) B3419653
theorem B2249393 : Blo 1498069 2249393 := bstep (se 2 (by rfl) ⟨843522, by rfl⟩ : syracuseStep 2249393 = 1687045) B1687045
theorem B2249411 : Blo 1498069 2249411 := bstep (se 1 (by rfl) ⟨1687058, by rfl⟩ : syracuseStep 2249411 = 3374117) B3374117
theorem B3846865 : Blo 1498069 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B2249441 : Blo 1498069 2249441 := bstep (se 2 (by rfl) ⟨843540, by rfl⟩ : syracuseStep 2249441 = 1687081) B1687081
theorem B12800753 : Blo 1498069 12800753 := bstep (se 2 (by rfl) ⟨4800282, by rfl⟩ : syracuseStep 12800753 = 9600565) B9600565
theorem B5059313 : Blo 1498069 5059313 := bstep (se 2 (by rfl) ⟨1897242, by rfl⟩ : syracuseStep 5059313 = 3794485) B3794485
theorem B2249459 : Blo 1498069 2249459 := bstep (se 1 (by rfl) ⟨1687094, by rfl⟩ : syracuseStep 2249459 = 3374189) B3374189
theorem B2528003 : Blo 1498069 2528003 := bstep (se 1 (by rfl) ⟨1896002, by rfl⟩ : syracuseStep 2528003 = 3792005) B3792005
theorem B2249489 : Blo 1498069 2249489 := bstep (se 2 (by rfl) ⟨843558, by rfl⟩ : syracuseStep 2249489 = 1687117) B1687117
theorem B2249507 : Blo 1498069 2249507 := bstep (se 1 (by rfl) ⟨1687130, by rfl⟩ : syracuseStep 2249507 = 3374261) B3374261
theorem B2249537 : Blo 1498069 2249537 := bstep (se 2 (by rfl) ⟨843576, by rfl⟩ : syracuseStep 2249537 = 1687153) B1687153
theorem B1897283 : Blo 1498069 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B2249555 : Blo 1498069 2249555 := bstep (se 1 (by rfl) ⟨1687166, by rfl⟩ : syracuseStep 2249555 = 3374333) B3374333
theorem B4871011 : Blo 1498069 4871011 := bstep (se 1 (by rfl) ⟨3653258, by rfl⟩ : syracuseStep 4871011 = 7306517) B7306517
theorem B2249585 : Blo 1498069 2249585 := bstep (se 2 (by rfl) ⟨843594, by rfl⟩ : syracuseStep 2249585 = 1687189) B1687189
theorem B2528131 : Blo 1498069 2528131 := bstep (se 1 (by rfl) ⟨1896098, by rfl⟩ : syracuseStep 2528131 = 3792197) B3792197
theorem B2249603 : Blo 1498069 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B3371921 : Blo 1498069 3371921 := bstep (se 2 (by rfl) ⟨1264470, by rfl⟩ : syracuseStep 3371921 = 2528941) B2528941
theorem B2134945 : Blo 1498069 2134945 := bstep (se 2 (by rfl) ⟨800604, by rfl⟩ : syracuseStep 2134945 = 1601209) B1601209
theorem B3371939 : Blo 1498069 3371939 := bstep (se 1 (by rfl) ⟨2528954, by rfl⟩ : syracuseStep 3371939 = 5057909) B5057909
theorem B2249633 : Blo 1498069 2249633 := bstep (se 2 (by rfl) ⟨843612, by rfl⟩ : syracuseStep 2249633 = 1687225) B1687225
theorem B7590833 : Blo 1498069 7590833 := bstep (se 2 (by rfl) ⟨2846562, by rfl⟩ : syracuseStep 7590833 = 5693125) B5693125
theorem B2249651 : Blo 1498069 2249651 := bstep (se 1 (by rfl) ⟨1687238, by rfl⟩ : syracuseStep 2249651 = 3374477) B3374477
theorem B8541125 : Blo 1498069 8541125 := bstep (se 4 (by rfl) ⟨800730, by rfl⟩ : syracuseStep 8541125 = 1601461) B1601461
theorem B2249681 : Blo 1498069 2249681 := bstep (se 2 (by rfl) ⟨843630, by rfl⟩ : syracuseStep 2249681 = 1687261) B1687261
theorem B2249699 : Blo 1498069 2249699 := bstep (se 1 (by rfl) ⟨1687274, by rfl⟩ : syracuseStep 2249699 = 3374549) B3374549
theorem B2249729 : Blo 1498069 2249729 := bstep (se 2 (by rfl) ⟨843648, by rfl⟩ : syracuseStep 2249729 = 1687297) B1687297
theorem B2528273 : Blo 1498069 2528273 := bstep (se 2 (by rfl) ⟨948102, by rfl⟩ : syracuseStep 2528273 = 1896205) B1896205
theorem B2249747 : Blo 1498069 2249747 := bstep (se 1 (by rfl) ⟨1687310, by rfl⟩ : syracuseStep 2249747 = 3374621) B3374621
theorem B2249777 : Blo 1498069 2249777 := bstep (se 2 (by rfl) ⟨843666, by rfl⟩ : syracuseStep 2249777 = 1687333) B1687333
theorem B2249795 : Blo 1498069 2249795 := bstep (se 1 (by rfl) ⟨1687346, by rfl⟩ : syracuseStep 2249795 = 3374693) B3374693
theorem B2249825 : Blo 1498069 2249825 := bstep (se 2 (by rfl) ⟨843684, by rfl⟩ : syracuseStep 2249825 = 1687369) B1687369
theorem B2249843 : Blo 1498069 2249843 := bstep (se 1 (by rfl) ⟨1687382, by rfl⟩ : syracuseStep 2249843 = 3374765) B3374765
theorem B2528401 : Blo 1498069 2528401 := bstep (se 2 (by rfl) ⟨948150, by rfl⟩ : syracuseStep 2528401 = 1896301) B1896301
theorem B2249873 : Blo 1498069 2249873 := bstep (se 2 (by rfl) ⟨843702, by rfl⟩ : syracuseStep 2249873 = 1687405) B1687405
theorem B2249891 : Blo 1498069 2249891 := bstep (se 1 (by rfl) ⟨1687418, by rfl⟩ : syracuseStep 2249891 = 3374837) B3374837
theorem B3372209 : Blo 1498069 3372209 := bstep (se 2 (by rfl) ⟨1264578, by rfl⟩ : syracuseStep 3372209 = 2529157) B2529157
theorem B2528435 : Blo 1498069 2528435 := bstep (se 1 (by rfl) ⟨1896326, by rfl⟩ : syracuseStep 2528435 = 3792653) B3792653
theorem B2249921 : Blo 1498069 2249921 := bstep (se 2 (by rfl) ⟨843720, by rfl⟩ : syracuseStep 2249921 = 1687441) B1687441
theorem B3372227 : Blo 1498069 3372227 := bstep (se 1 (by rfl) ⟨2529170, by rfl⟩ : syracuseStep 3372227 = 5058341) B5058341
theorem B2249939 : Blo 1498069 2249939 := bstep (se 1 (by rfl) ⟨1687454, by rfl⟩ : syracuseStep 2249939 = 3374909) B3374909
theorem B2249969 : Blo 1498069 2249969 := bstep (se 2 (by rfl) ⟨843738, by rfl⟩ : syracuseStep 2249969 = 1687477) B1687477
theorem B4560131 : Blo 1498069 4560131 := bstep (se 1 (by rfl) ⟨3420098, by rfl⟩ : syracuseStep 4560131 = 6840197) B6840197
theorem B2249987 : Blo 1498069 2249987 := bstep (se 1 (by rfl) ⟨1687490, by rfl⟩ : syracuseStep 2249987 = 3374981) B3374981
theorem B5059853 : Blo 1498069 5059853 := bstep (se 3 (by rfl) ⟨948722, by rfl⟩ : syracuseStep 5059853 = 1897445) B1897445
theorem B2250017 : Blo 1498069 2250017 := bstep (se 2 (by rfl) ⟨843756, by rfl⟩ : syracuseStep 2250017 = 1687513) B1687513
theorem B2528563 : Blo 1498069 2528563 := bstep (se 1 (by rfl) ⟨1896422, by rfl⟩ : syracuseStep 2528563 = 3792845) B3792845
theorem B2250035 : Blo 1498069 2250035 := bstep (se 1 (by rfl) ⟨1687526, by rfl⟩ : syracuseStep 2250035 = 3375053) B3375053
theorem B5059907 : Blo 1498069 5059907 := bstep (se 1 (by rfl) ⟨3794930, by rfl⟩ : syracuseStep 5059907 = 7589861) B7589861
theorem B2250065 : Blo 1498069 2250065 := bstep (se 2 (by rfl) ⟨843774, by rfl⟩ : syracuseStep 2250065 = 1687549) B1687549
theorem B2250083 : Blo 1498069 2250083 := bstep (se 1 (by rfl) ⟨1687562, by rfl⟩ : syracuseStep 2250083 = 3375125) B3375125
theorem B3200401 : Blo 1498069 3200401 := bstep (se 2 (by rfl) ⟨1200150, by rfl⟩ : syracuseStep 3200401 = 2400301) B2400301
theorem B4052369 : Blo 1498069 4052369 := bstep (se 2 (by rfl) ⟨1519638, by rfl⟩ : syracuseStep 4052369 = 3039277) B3039277
theorem B2528705 : Blo 1498069 2528705 := bstep (se 2 (by rfl) ⟨948264, by rfl⟩ : syracuseStep 2528705 = 1896529) B1896529
theorem B3372497 : Blo 1498069 3372497 := bstep (se 2 (by rfl) ⟨1264686, by rfl⟩ : syracuseStep 3372497 = 2529373) B2529373
theorem B3372515 : Blo 1498069 3372515 := bstep (se 1 (by rfl) ⟨2529386, by rfl⟩ : syracuseStep 3372515 = 5058773) B5058773
theorem B1897987 : Blo 1498069 1897987 := bstep (se 1 (by rfl) ⟨1423490, by rfl⟩ : syracuseStep 1897987 = 2846981) B2846981
theorem B1922611 : Blo 1498069 1922611 := bstep (se 1 (by rfl) ⟨1441958, by rfl⟩ : syracuseStep 1922611 = 2883917) B2883917
theorem B2528833 : Blo 1498069 2528833 := bstep (se 2 (by rfl) ⟨948312, by rfl⟩ : syracuseStep 2528833 = 1896625) B1896625
theorem B5060177 : Blo 1498069 5060177 := bstep (se 2 (by rfl) ⟨1897566, by rfl⟩ : syracuseStep 5060177 = 3795133) B3795133
theorem B2528867 : Blo 1498069 2528867 := bstep (se 1 (by rfl) ⟨1896650, by rfl⟩ : syracuseStep 2528867 = 3793301) B3793301
theorem B1898083 : Blo 1498069 1898083 := bstep (se 1 (by rfl) ⟨1423562, by rfl⟩ : syracuseStep 1898083 = 2847125) B2847125
theorem B2135651 : Blo 1498069 2135651 := bstep (se 1 (by rfl) ⟨1601738, by rfl⟩ : syracuseStep 2135651 = 3203477) B3203477
theorem B14399117 : Blo 1498069 14399117 := bstep (se 3 (by rfl) ⟨2699834, by rfl⟩ : syracuseStep 14399117 = 5399669) B5399669
theorem B2528995 : Blo 1498069 2528995 := bstep (se 1 (by rfl) ⟨1896746, by rfl⟩ : syracuseStep 2528995 = 3793493) B3793493
theorem B3372785 : Blo 1498069 3372785 := bstep (se 2 (by rfl) ⟨1264794, by rfl⟩ : syracuseStep 3372785 = 2529589) B2529589
theorem B3372803 : Blo 1498069 3372803 := bstep (se 1 (by rfl) ⟨2529602, by rfl⟩ : syracuseStep 3372803 = 5059205) B5059205
theorem B5125933 : Blo 1498069 5125933 := bstep (se 3 (by rfl) ⟨961112, by rfl⟩ : syracuseStep 5125933 = 1922225) B1922225
theorem B4052845 : Blo 1498069 4052845 := bstep (se 3 (by rfl) ⟨759908, by rfl⟩ : syracuseStep 4052845 = 1519817) B1519817
theorem B14399345 : Blo 1498069 14399345 := bstep (se 2 (by rfl) ⟨5399754, by rfl⟩ : syracuseStep 14399345 = 10799509) B10799509
theorem B2529137 : Blo 1498069 2529137 := bstep (se 2 (by rfl) ⟨948426, by rfl⟩ : syracuseStep 2529137 = 1896853) B1896853
theorem B6403981 : Blo 1498069 6403981 := bstep (se 3 (by rfl) ⟨1200746, by rfl⟩ : syracuseStep 6403981 = 2401493) B2401493
theorem B1824691 : Blo 1498069 1824691 := bstep (se 1 (by rfl) ⟨1368518, by rfl⟩ : syracuseStep 1824691 = 2737037) B2737037
theorem B1685443 : Blo 1498069 1685443 := bstep (se 1 (by rfl) ⟨1264082, by rfl⟩ : syracuseStep 1685443 = 2528165) B2528165
theorem B30750661 : Blo 1498069 30750661 := bstep (se 4 (by rfl) ⟨2882874, by rfl⟩ : syracuseStep 30750661 = 5765749) B5765749
theorem B10811333 : Blo 1498069 10811333 := bstep (se 4 (by rfl) ⟨1013562, by rfl⟩ : syracuseStep 10811333 = 2027125) B2027125
theorem B9598925 : Blo 1498069 9598925 := bstep (se 3 (by rfl) ⟨1799798, by rfl⟩ : syracuseStep 9598925 = 3599597) B3599597
theorem B3037169 : Blo 1498069 3037169 := bstep (se 2 (by rfl) ⟨1138938, by rfl⟩ : syracuseStep 3037169 = 2277877) B2277877
theorem B5847025 : Blo 1498069 5847025 := bstep (se 2 (by rfl) ⟨2192634, by rfl⟩ : syracuseStep 5847025 = 4385269) B4385269
theorem B2529265 : Blo 1498069 2529265 := bstep (se 2 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 2529265 = 1896949) B1896949
theorem B3373073 : Blo 1498069 3373073 := bstep (se 2 (by rfl) ⟨1264902, by rfl⟩ : syracuseStep 3373073 = 2529805) B2529805
theorem B2529299 : Blo 1498069 2529299 := bstep (se 1 (by rfl) ⟨1896974, by rfl⟩ : syracuseStep 2529299 = 3793949) B3793949
theorem B3373091 : Blo 1498069 3373091 := bstep (se 1 (by rfl) ⟨2529818, by rfl⟩ : syracuseStep 3373091 = 5059637) B5059637
theorem B1685587 : Blo 1498069 1685587 := bstep (se 1 (by rfl) ⟨1264190, by rfl⟩ : syracuseStep 1685587 = 2528381) B2528381
theorem B5060717 : Blo 1498069 5060717 := bstep (se 3 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 5060717 = 1897769) B1897769
theorem B2529427 : Blo 1498069 2529427 := bstep (se 1 (by rfl) ⟨1897070, by rfl⟩ : syracuseStep 2529427 = 3794141) B3794141
theorem B5060771 : Blo 1498069 5060771 := bstep (se 1 (by rfl) ⟨3795578, by rfl⟩ : syracuseStep 5060771 = 7591157) B7591157
theorem B1685731 : Blo 1498069 1685731 := bstep (se 1 (by rfl) ⟨1264298, by rfl⟩ : syracuseStep 1685731 = 2528597) B2528597
theorem B9607409 : Blo 1498069 9607409 := bstep (se 2 (by rfl) ⟨3602778, by rfl⟩ : syracuseStep 9607409 = 7205557) B7205557
theorem B2529569 : Blo 1498069 2529569 := bstep (se 2 (by rfl) ⟨948588, by rfl⟩ : syracuseStep 2529569 = 1897177) B1897177
theorem B3373361 : Blo 1498069 3373361 := bstep (se 2 (by rfl) ⟨1265010, by rfl⟩ : syracuseStep 3373361 = 2530021) B2530021
theorem B3373379 : Blo 1498069 3373379 := bstep (se 1 (by rfl) ⟨2530034, by rfl⟩ : syracuseStep 3373379 = 5060069) B5060069
theorem B7592291 : Blo 1498069 7592291 := bstep (se 1 (by rfl) ⟨5694218, by rfl⟩ : syracuseStep 7592291 = 11388437) B11388437
theorem B1685875 : Blo 1498069 1685875 := bstep (se 1 (by rfl) ⟨1264406, by rfl⟩ : syracuseStep 1685875 = 2528813) B2528813
theorem B4266371 : Blo 1498069 4266371 := bstep (se 1 (by rfl) ⟨3199778, by rfl⟩ : syracuseStep 4266371 = 6399557) B6399557
theorem B9247117 : Blo 1498069 9247117 := bstep (se 3 (by rfl) ⟨1733834, by rfl⟩ : syracuseStep 9247117 = 3467669) B3467669
theorem B2529697 : Blo 1498069 2529697 := bstep (se 2 (by rfl) ⟨948636, by rfl⟩ : syracuseStep 2529697 = 1897273) B1897273
theorem B5061041 : Blo 1498069 5061041 := bstep (se 2 (by rfl) ⟨1897890, by rfl⟩ : syracuseStep 5061041 = 3795781) B3795781
theorem B2529731 : Blo 1498069 2529731 := bstep (se 1 (by rfl) ⟨1897298, by rfl⟩ : syracuseStep 2529731 = 3794597) B3794597
theorem B1686019 : Blo 1498069 1686019 := bstep (se 1 (by rfl) ⟨1264514, by rfl⟩ : syracuseStep 1686019 = 2529029) B2529029
theorem B10951181 : Blo 1498069 10951181 := bstep (se 3 (by rfl) ⟨2053346, by rfl⟩ : syracuseStep 10951181 = 4106693) B4106693
theorem B18233909 : Blo 1498069 18233909 := bstep (se 5 (by rfl) ⟨854714, by rfl⟩ : syracuseStep 18233909 = 1709429) B1709429
theorem B2529859 : Blo 1498069 2529859 := bstep (se 1 (by rfl) ⟨1897394, by rfl⟩ : syracuseStep 2529859 = 3794789) B3794789
theorem B3373649 : Blo 1498069 3373649 := bstep (se 2 (by rfl) ⟨1265118, by rfl⟩ : syracuseStep 3373649 = 2530237) B2530237
theorem B6838883 : Blo 1498069 6838883 := bstep (se 1 (by rfl) ⟨5129162, by rfl⟩ : syracuseStep 6838883 = 10258325) B10258325
theorem B3373667 : Blo 1498069 3373667 := bstep (se 1 (by rfl) ⟨2530250, by rfl⟩ : syracuseStep 3373667 = 5060501) B5060501
theorem B1686163 : Blo 1498069 1686163 := bstep (se 1 (by rfl) ⟨1264622, by rfl⟩ : syracuseStep 1686163 = 2529245) B2529245
theorem B4266701 : Blo 1498069 4266701 := bstep (se 3 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 4266701 = 1600013) B1600013
theorem B2530001 : Blo 1498069 2530001 := bstep (se 2 (by rfl) ⟨948750, by rfl⟩ : syracuseStep 2530001 = 1897501) B1897501
theorem B17079011 : Blo 1498069 17079011 := bstep (se 1 (by rfl) ⟨12809258, by rfl⟩ : syracuseStep 17079011 = 25618517) B25618517
theorem B4266769 : Blo 1498069 4266769 := bstep (se 2 (by rfl) ⟨1600038, by rfl⟩ : syracuseStep 4266769 = 3200077) B3200077
theorem B1686307 : Blo 1498069 1686307 := bstep (se 1 (by rfl) ⟨1264730, by rfl⟩ : syracuseStep 1686307 = 2529461) B2529461
theorem B2530129 : Blo 1498069 2530129 := bstep (se 2 (by rfl) ⟨948798, by rfl⟩ : syracuseStep 2530129 = 1897597) B1897597
theorem B3201905 : Blo 1498069 3201905 := bstep (se 2 (by rfl) ⟨1200714, by rfl⟩ : syracuseStep 3201905 = 2401429) B2401429
theorem B3373937 : Blo 1498069 3373937 := bstep (se 2 (by rfl) ⟨1265226, by rfl⟩ : syracuseStep 3373937 = 2530453) B2530453
theorem B2530163 : Blo 1498069 2530163 := bstep (se 1 (by rfl) ⟨1897622, by rfl⟩ : syracuseStep 2530163 = 3795245) B3795245
theorem B1645427 : Blo 1498069 1645427 := bstep (se 1 (by rfl) ⟨1234070, by rfl⟩ : syracuseStep 1645427 = 2468141) B2468141
theorem B3201923 : Blo 1498069 3201923 := bstep (se 1 (by rfl) ⟨2401442, by rfl⟩ : syracuseStep 3201923 = 4802885) B4802885
theorem B3373955 : Blo 1498069 3373955 := bstep (se 1 (by rfl) ⟨2530466, by rfl⟩ : syracuseStep 3373955 = 5060933) B5060933
theorem B1686451 : Blo 1498069 1686451 := bstep (se 1 (by rfl) ⟨1264838, by rfl⟩ : syracuseStep 1686451 = 2529677) B2529677
theorem B5061581 : Blo 1498069 5061581 := bstep (se 3 (by rfl) ⟨949046, by rfl⟩ : syracuseStep 5061581 = 1898093) B1898093
theorem B1498083 : Blo 1498069 1498083 := bstep (se 1 (by rfl) ⟨1123562, by rfl⟩ : syracuseStep 1498083 = 2247125) B2247125
theorem B1498099 : Blo 1498069 1498099 := bstep (se 1 (by rfl) ⟨1123574, by rfl⟩ : syracuseStep 1498099 = 2247149) B2247149
theorem B2530291 : Blo 1498069 2530291 := bstep (se 1 (by rfl) ⟨1897718, by rfl⟩ : syracuseStep 2530291 = 3795437) B3795437
theorem B1498115 : Blo 1498069 1498115 := bstep (se 1 (by rfl) ⟨1123586, by rfl⟩ : syracuseStep 1498115 = 2247173) B2247173
theorem B5061635 : Blo 1498069 5061635 := bstep (se 1 (by rfl) ⟨3796226, by rfl⟩ : syracuseStep 5061635 = 7592453) B7592453
theorem B1498131 : Blo 1498069 1498131 := bstep (se 1 (by rfl) ⟨1123598, by rfl⟩ : syracuseStep 1498131 = 2247197) B2247197
theorem B1498147 : Blo 1498069 1498147 := bstep (se 1 (by rfl) ⟨1123610, by rfl⟩ : syracuseStep 1498147 = 2247221) B2247221
theorem B4267043 : Blo 1498069 4267043 := bstep (se 1 (by rfl) ⟨3200282, by rfl⟩ : syracuseStep 4267043 = 6400565) B6400565
theorem B1498163 : Blo 1498069 1498163 := bstep (se 1 (by rfl) ⟨1123622, by rfl⟩ : syracuseStep 1498163 = 2247245) B2247245
theorem B1498179 : Blo 1498069 1498179 := bstep (se 1 (by rfl) ⟨1123634, by rfl⟩ : syracuseStep 1498179 = 2247269) B2247269
theorem B1686595 : Blo 1498069 1686595 := bstep (se 1 (by rfl) ⟨1264946, by rfl⟩ : syracuseStep 1686595 = 2529893) B2529893
theorem B1801283 : Blo 1498069 1801283 := bstep (se 1 (by rfl) ⟨1350962, by rfl⟩ : syracuseStep 1801283 = 2701925) B2701925
theorem B1498195 : Blo 1498069 1498195 := bstep (se 1 (by rfl) ⟨1123646, by rfl⟩ : syracuseStep 1498195 = 2247293) B2247293
theorem B1498211 : Blo 1498069 1498211 := bstep (se 1 (by rfl) ⟨1123658, by rfl⟩ : syracuseStep 1498211 = 2247317) B2247317
theorem B1498227 : Blo 1498069 1498227 := bstep (se 1 (by rfl) ⟨1123670, by rfl⟩ : syracuseStep 1498227 = 2247341) B2247341
theorem B2530433 : Blo 1498069 2530433 := bstep (se 2 (by rfl) ⟨948912, by rfl⟩ : syracuseStep 2530433 = 1897825) B1897825
theorem B1498243 : Blo 1498069 1498243 := bstep (se 1 (by rfl) ⟨1123682, by rfl⟩ : syracuseStep 1498243 = 2247365) B2247365
theorem B7593101 : Blo 1498069 7593101 := bstep (se 3 (by rfl) ⟨1423706, by rfl⟩ : syracuseStep 7593101 = 2847413) B2847413
theorem B3374225 : Blo 1498069 3374225 := bstep (se 2 (by rfl) ⟨1265334, by rfl⟩ : syracuseStep 3374225 = 2530669) B2530669
theorem B1498259 : Blo 1498069 1498259 := bstep (se 1 (by rfl) ⟨1123694, by rfl⟩ : syracuseStep 1498259 = 2247389) B2247389
theorem B3792035 : Blo 1498069 3792035 := bstep (se 1 (by rfl) ⟨2844026, by rfl⟩ : syracuseStep 3792035 = 5688053) B5688053
theorem B1498275 : Blo 1498069 1498275 := bstep (se 1 (by rfl) ⟨1123706, by rfl⟩ : syracuseStep 1498275 = 2247413) B2247413
theorem B3374243 : Blo 1498069 3374243 := bstep (se 1 (by rfl) ⟨2530682, by rfl⟩ : syracuseStep 3374243 = 5061365) B5061365
theorem B1498291 : Blo 1498069 1498291 := bstep (se 1 (by rfl) ⟨1123718, by rfl⟩ : syracuseStep 1498291 = 2247437) B2247437
theorem B1498307 : Blo 1498069 1498307 := bstep (se 1 (by rfl) ⟨1123730, by rfl⟩ : syracuseStep 1498307 = 2247461) B2247461
theorem B1498323 : Blo 1498069 1498323 := bstep (se 1 (by rfl) ⟨1123742, by rfl⟩ : syracuseStep 1498323 = 2247485) B2247485
theorem B1686739 : Blo 1498069 1686739 := bstep (se 1 (by rfl) ⟨1265054, by rfl⟩ : syracuseStep 1686739 = 2530109) B2530109
theorem B1498339 : Blo 1498069 1498339 := bstep (se 1 (by rfl) ⟨1123754, by rfl⟩ : syracuseStep 1498339 = 2247509) B2247509
theorem B1498355 : Blo 1498069 1498355 := bstep (se 1 (by rfl) ⟨1123766, by rfl⟩ : syracuseStep 1498355 = 2247533) B2247533
theorem B2530561 : Blo 1498069 2530561 := bstep (se 2 (by rfl) ⟨948960, by rfl⟩ : syracuseStep 2530561 = 1897921) B1897921
theorem B1498371 : Blo 1498069 1498371 := bstep (se 1 (by rfl) ⟨1123778, by rfl⟩ : syracuseStep 1498371 = 2247557) B2247557
theorem B5061905 : Blo 1498069 5061905 := bstep (se 2 (by rfl) ⟨1898214, by rfl⟩ : syracuseStep 5061905 = 3796429) B3796429
theorem B1498387 : Blo 1498069 1498387 := bstep (se 1 (by rfl) ⟨1123790, by rfl⟩ : syracuseStep 1498387 = 2247581) B2247581
theorem B1498403 : Blo 1498069 1498403 := bstep (se 1 (by rfl) ⟨1123802, by rfl⟩ : syracuseStep 1498403 = 2247605) B2247605
theorem B2530595 : Blo 1498069 2530595 := bstep (se 1 (by rfl) ⟨1897946, by rfl⟩ : syracuseStep 2530595 = 3795893) B3795893
theorem B9608483 : Blo 1498069 9608483 := bstep (se 1 (by rfl) ⟨7206362, by rfl⟩ : syracuseStep 9608483 = 14412725) B14412725
theorem B1498419 : Blo 1498069 1498419 := bstep (se 1 (by rfl) ⟨1123814, by rfl⟩ : syracuseStep 1498419 = 2247629) B2247629
theorem B1498435 : Blo 1498069 1498435 := bstep (se 1 (by rfl) ⟨1123826, by rfl⟩ : syracuseStep 1498435 = 2247653) B2247653
theorem B7691597 : Blo 1498069 7691597 := bstep (se 3 (by rfl) ⟨1442174, by rfl⟩ : syracuseStep 7691597 = 2884349) B2884349
theorem B1498451 : Blo 1498069 1498451 := bstep (se 1 (by rfl) ⟨1123838, by rfl⟩ : syracuseStep 1498451 = 2247677) B2247677
theorem B1498467 : Blo 1498069 1498467 := bstep (se 1 (by rfl) ⟨1123850, by rfl⟩ : syracuseStep 1498467 = 2247701) B2247701
theorem B1686883 : Blo 1498069 1686883 := bstep (se 1 (by rfl) ⟨1265162, by rfl⟩ : syracuseStep 1686883 = 2530325) B2530325
theorem B1498483 : Blo 1498069 1498483 := bstep (se 1 (by rfl) ⟨1123862, by rfl⟩ : syracuseStep 1498483 = 2247725) B2247725
theorem B1498499 : Blo 1498069 1498499 := bstep (se 1 (by rfl) ⟨1123874, by rfl⟩ : syracuseStep 1498499 = 2247749) B2247749
theorem B2399635 : Blo 1498069 2399635 := bstep (se 1 (by rfl) ⟨1799726, by rfl⟩ : syracuseStep 2399635 = 3599453) B3599453
theorem B1498515 : Blo 1498069 1498515 := bstep (se 1 (by rfl) ⟨1123886, by rfl⟩ : syracuseStep 1498515 = 2247773) B2247773
theorem B1498531 : Blo 1498069 1498531 := bstep (se 1 (by rfl) ⟨1123898, by rfl⟩ : syracuseStep 1498531 = 2247797) B2247797
theorem B2530723 : Blo 1498069 2530723 := bstep (se 1 (by rfl) ⟨1898042, by rfl⟩ : syracuseStep 2530723 = 3796085) B3796085
theorem B3374513 : Blo 1498069 3374513 := bstep (se 2 (by rfl) ⟨1265442, by rfl⟩ : syracuseStep 3374513 = 2530885) B2530885
theorem B1498547 : Blo 1498069 1498547 := bstep (se 1 (by rfl) ⟨1123910, by rfl⟩ : syracuseStep 1498547 = 2247821) B2247821
theorem B2399681 : Blo 1498069 2399681 := bstep (se 2 (by rfl) ⟨899880, by rfl⟩ : syracuseStep 2399681 = 1799761) B1799761
theorem B1498563 : Blo 1498069 1498563 := bstep (se 1 (by rfl) ⟨1123922, by rfl⟩ : syracuseStep 1498563 = 2247845) B2247845
theorem B3374531 : Blo 1498069 3374531 := bstep (se 1 (by rfl) ⟨2530898, by rfl⟩ : syracuseStep 3374531 = 5061797) B5061797
theorem B1498579 : Blo 1498069 1498579 := bstep (se 1 (by rfl) ⟨1123934, by rfl⟩ : syracuseStep 1498579 = 2247869) B2247869
theorem B1498595 : Blo 1498069 1498595 := bstep (se 1 (by rfl) ⟨1123946, by rfl⟩ : syracuseStep 1498595 = 2247893) B2247893
theorem B24305123 : Blo 1498069 24305123 := bstep (se 1 (by rfl) ⟨18228842, by rfl⟩ : syracuseStep 24305123 = 36457685) B36457685
theorem B5692913 : Blo 1498069 5692913 := bstep (se 2 (by rfl) ⟨2134842, by rfl⟩ : syracuseStep 5692913 = 4269685) B4269685
theorem B1498611 : Blo 1498069 1498611 := bstep (se 1 (by rfl) ⟨1123958, by rfl⟩ : syracuseStep 1498611 = 2247917) B2247917
theorem B1687027 : Blo 1498069 1687027 := bstep (se 1 (by rfl) ⟨1265270, by rfl⟩ : syracuseStep 1687027 = 2530541) B2530541
theorem B1498627 : Blo 1498069 1498627 := bstep (se 1 (by rfl) ⟨1123970, by rfl⟩ : syracuseStep 1498627 = 2247941) B2247941
theorem B1498643 : Blo 1498069 1498643 := bstep (se 1 (by rfl) ⟨1123982, by rfl⟩ : syracuseStep 1498643 = 2247965) B2247965
theorem B1498659 : Blo 1498069 1498659 := bstep (se 1 (by rfl) ⟨1123994, by rfl⟩ : syracuseStep 1498659 = 2247989) B2247989
theorem B2530865 : Blo 1498069 2530865 := bstep (se 2 (by rfl) ⟨949074, by rfl⟩ : syracuseStep 2530865 = 1898149) B1898149
theorem B1498675 : Blo 1498069 1498675 := bstep (se 1 (by rfl) ⟨1124006, by rfl⟩ : syracuseStep 1498675 = 2248013) B2248013
theorem B1498691 : Blo 1498069 1498691 := bstep (se 1 (by rfl) ⟨1124018, by rfl⟩ : syracuseStep 1498691 = 2248037) B2248037
theorem B1498707 : Blo 1498069 1498707 := bstep (se 1 (by rfl) ⟨1124030, by rfl⟩ : syracuseStep 1498707 = 2248061) B2248061
theorem B1498723 : Blo 1498069 1498723 := bstep (se 1 (by rfl) ⟨1124042, by rfl⟩ : syracuseStep 1498723 = 2248085) B2248085
theorem B1498739 : Blo 1498069 1498739 := bstep (se 1 (by rfl) ⟨1124054, by rfl⟩ : syracuseStep 1498739 = 2248109) B2248109
theorem B1498755 : Blo 1498069 1498755 := bstep (se 1 (by rfl) ⟨1124066, by rfl⟩ : syracuseStep 1498755 = 2248133) B2248133
theorem B1687171 : Blo 1498069 1687171 := bstep (se 1 (by rfl) ⟨1265378, by rfl⟩ : syracuseStep 1687171 = 2530757) B2530757
theorem B1498771 : Blo 1498069 1498771 := bstep (se 1 (by rfl) ⟨1124078, by rfl⟩ : syracuseStep 1498771 = 2248157) B2248157
theorem B1498787 : Blo 1498069 1498787 := bstep (se 1 (by rfl) ⟨1124090, by rfl⟩ : syracuseStep 1498787 = 2248181) B2248181
theorem B2530993 : Blo 1498069 2530993 := bstep (se 2 (by rfl) ⟨949122, by rfl⟩ : syracuseStep 2530993 = 1898245) B1898245
theorem B1498803 : Blo 1498069 1498803 := bstep (se 1 (by rfl) ⟨1124102, by rfl⟩ : syracuseStep 1498803 = 2248205) B2248205
theorem B1498819 : Blo 1498069 1498819 := bstep (se 1 (by rfl) ⟨1124114, by rfl⟩ : syracuseStep 1498819 = 2248229) B2248229
theorem B3374801 : Blo 1498069 3374801 := bstep (se 2 (by rfl) ⟨1265550, by rfl⟩ : syracuseStep 3374801 = 2531101) B2531101
theorem B1498835 : Blo 1498069 1498835 := bstep (se 1 (by rfl) ⟨1124126, by rfl⟩ : syracuseStep 1498835 = 2248253) B2248253
theorem B2531027 : Blo 1498069 2531027 := bstep (se 1 (by rfl) ⟨1898270, by rfl⟩ : syracuseStep 2531027 = 3796541) B3796541
theorem B1498851 : Blo 1498069 1498851 := bstep (se 1 (by rfl) ⟨1124138, by rfl⟩ : syracuseStep 1498851 = 2248277) B2248277
theorem B3374819 : Blo 1498069 3374819 := bstep (se 1 (by rfl) ⟨2531114, by rfl⟩ : syracuseStep 3374819 = 5062229) B5062229
theorem B1498867 : Blo 1498069 1498867 := bstep (se 1 (by rfl) ⟨1124150, by rfl⟩ : syracuseStep 1498867 = 2248301) B2248301
theorem B1498883 : Blo 1498069 1498883 := bstep (se 1 (by rfl) ⟨1124162, by rfl⟩ : syracuseStep 1498883 = 2248325) B2248325
theorem B2703107 : Blo 1498069 2703107 := bstep (se 1 (by rfl) ⟨2027330, by rfl⟩ : syracuseStep 2703107 = 4054661) B4054661
theorem B1498899 : Blo 1498069 1498899 := bstep (se 1 (by rfl) ⟨1124174, by rfl⟩ : syracuseStep 1498899 = 2248349) B2248349
theorem B1687315 : Blo 1498069 1687315 := bstep (se 1 (by rfl) ⟨1265486, by rfl⟩ : syracuseStep 1687315 = 2530973) B2530973
theorem B1498915 : Blo 1498069 1498915 := bstep (se 1 (by rfl) ⟨1124186, by rfl⟩ : syracuseStep 1498915 = 2248373) B2248373
theorem B5062445 : Blo 1498069 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B1498931 : Blo 1498069 1498931 := bstep (se 1 (by rfl) ⟨1124198, by rfl⟩ : syracuseStep 1498931 = 2248397) B2248397
theorem B1498947 : Blo 1498069 1498947 := bstep (se 1 (by rfl) ⟨1124210, by rfl⟩ : syracuseStep 1498947 = 2248421) B2248421
theorem B1498963 : Blo 1498069 1498963 := bstep (se 1 (by rfl) ⟨1124222, by rfl⟩ : syracuseStep 1498963 = 2248445) B2248445
theorem B2531155 : Blo 1498069 2531155 := bstep (se 1 (by rfl) ⟨1898366, by rfl⟩ : syracuseStep 2531155 = 3796733) B3796733
theorem B1498979 : Blo 1498069 1498979 := bstep (se 1 (by rfl) ⟨1124234, by rfl⟩ : syracuseStep 1498979 = 2248469) B2248469
theorem B5062499 : Blo 1498069 5062499 := bstep (se 1 (by rfl) ⟨3796874, by rfl⟩ : syracuseStep 5062499 = 7593749) B7593749
theorem B4267885 : Blo 1498069 4267885 := bstep (se 3 (by rfl) ⟨800228, by rfl⟩ : syracuseStep 4267885 = 1600457) B1600457
theorem B7585649 : Blo 1498069 7585649 := bstep (se 2 (by rfl) ⟨2844618, by rfl⟩ : syracuseStep 7585649 = 5689237) B5689237
theorem B25952113 : Blo 1498069 25952113 := bstep (se 2 (by rfl) ⟨9732042, by rfl⟩ : syracuseStep 25952113 = 19464085) B19464085
theorem B1498995 : Blo 1498069 1498995 := bstep (se 1 (by rfl) ⟨1124246, by rfl⟩ : syracuseStep 1498995 = 2248493) B2248493
theorem B1499011 : Blo 1498069 1499011 := bstep (se 1 (by rfl) ⟨1124258, by rfl⟩ : syracuseStep 1499011 = 2248517) B2248517
theorem B4800397 : Blo 1498069 4800397 := bstep (se 3 (by rfl) ⟨900074, by rfl⟩ : syracuseStep 4800397 = 1800149) B1800149
theorem B1499027 : Blo 1498069 1499027 := bstep (se 1 (by rfl) ⟨1124270, by rfl⟩ : syracuseStep 1499027 = 2248541) B2248541
theorem B1499043 : Blo 1498069 1499043 := bstep (se 1 (by rfl) ⟨1124282, by rfl⟩ : syracuseStep 1499043 = 2248565) B2248565
theorem B1687459 : Blo 1498069 1687459 := bstep (se 1 (by rfl) ⟨1265594, by rfl⟩ : syracuseStep 1687459 = 2531189) B2531189
theorem B1499059 : Blo 1498069 1499059 := bstep (se 1 (by rfl) ⟨1124294, by rfl⟩ : syracuseStep 1499059 = 2248589) B2248589
theorem B1499075 : Blo 1498069 1499075 := bstep (se 1 (by rfl) ⟨1124306, by rfl⟩ : syracuseStep 1499075 = 2248613) B2248613
theorem B1499091 : Blo 1498069 1499091 := bstep (se 1 (by rfl) ⟨1124318, by rfl⟩ : syracuseStep 1499091 = 2248637) B2248637
theorem B1499107 : Blo 1498069 1499107 := bstep (se 1 (by rfl) ⟨1124330, by rfl⟩ : syracuseStep 1499107 = 2248661) B2248661
theorem B2531297 : Blo 1498069 2531297 := bstep (se 2 (by rfl) ⟨949236, by rfl⟩ : syracuseStep 2531297 = 1898473) B1898473
theorem B3375089 : Blo 1498069 3375089 := bstep (se 2 (by rfl) ⟨1265658, by rfl⟩ : syracuseStep 3375089 = 2531317) B2531317
theorem B1499123 : Blo 1498069 1499123 := bstep (se 1 (by rfl) ⟨1124342, by rfl⟩ : syracuseStep 1499123 = 2248685) B2248685
theorem B1499147 : Blo 1498069 1499147 := bstep (se 1 (by rfl) ⟨1124360, by rfl⟩ : syracuseStep 1499147 = 2248721) B2248721
theorem B1499159 : Blo 1498069 1499159 := bstep (se 1 (by rfl) ⟨1124369, by rfl⟩ : syracuseStep 1499159 = 2248739) B2248739
theorem B2531351 : Blo 1498069 2531351 := bstep (se 1 (by rfl) ⟨1898513, by rfl⟩ : syracuseStep 2531351 = 3797027) B3797027
theorem B1499179 : Blo 1498069 1499179 := bstep (se 1 (by rfl) ⟨1124384, by rfl⟩ : syracuseStep 1499179 = 2248769) B2248769
theorem B1499191 : Blo 1498069 1499191 := bstep (se 1 (by rfl) ⟨1124393, by rfl⟩ : syracuseStep 1499191 = 2248787) B2248787
theorem B1499211 : Blo 1498069 1499211 := bstep (se 1 (by rfl) ⟨1124408, by rfl⟩ : syracuseStep 1499211 = 2248817) B2248817
theorem B1499223 : Blo 1498069 1499223 := bstep (se 1 (by rfl) ⟨1124417, by rfl⟩ : syracuseStep 1499223 = 2248835) B2248835
theorem B1499243 : Blo 1498069 1499243 := bstep (se 1 (by rfl) ⟨1124432, by rfl⟩ : syracuseStep 1499243 = 2248865) B2248865
theorem B1499255 : Blo 1498069 1499255 := bstep (se 1 (by rfl) ⟨1124441, by rfl⟩ : syracuseStep 1499255 = 2248883) B2248883
theorem B1499275 : Blo 1498069 1499275 := bstep (se 1 (by rfl) ⟨1124456, by rfl⟩ : syracuseStep 1499275 = 2248913) B2248913
theorem B1499287 : Blo 1498069 1499287 := bstep (se 1 (by rfl) ⟨1124465, by rfl⟩ : syracuseStep 1499287 = 2248931) B2248931
theorem B1499307 : Blo 1498069 1499307 := bstep (se 1 (by rfl) ⟨1124480, by rfl⟩ : syracuseStep 1499307 = 2248961) B2248961
theorem B1499319 : Blo 1498069 1499319 := bstep (se 1 (by rfl) ⟨1124489, by rfl⟩ : syracuseStep 1499319 = 2248979) B2248979
theorem B1499339 : Blo 1498069 1499339 := bstep (se 1 (by rfl) ⟨1124504, by rfl⟩ : syracuseStep 1499339 = 2249009) B2249009
theorem B1499351 : Blo 1498069 1499351 := bstep (se 1 (by rfl) ⟨1124513, by rfl⟩ : syracuseStep 1499351 = 2249027) B2249027
theorem B1499371 : Blo 1498069 1499371 := bstep (se 1 (by rfl) ⟨1124528, by rfl⟩ : syracuseStep 1499371 = 2249057) B2249057
theorem B1499383 : Blo 1498069 1499383 := bstep (se 1 (by rfl) ⟨1124537, by rfl⟩ : syracuseStep 1499383 = 2249075) B2249075
theorem B1499403 : Blo 1498069 1499403 := bstep (se 1 (by rfl) ⟨1124552, by rfl⟩ : syracuseStep 1499403 = 2249105) B2249105
theorem B1499415 : Blo 1498069 1499415 := bstep (se 1 (by rfl) ⟨1124561, by rfl⟩ : syracuseStep 1499415 = 2249123) B2249123
theorem B1499435 : Blo 1498069 1499435 := bstep (se 1 (by rfl) ⟨1124576, by rfl⟩ : syracuseStep 1499435 = 2249153) B2249153
theorem B1499447 : Blo 1498069 1499447 := bstep (se 1 (by rfl) ⟨1124585, by rfl⟩ : syracuseStep 1499447 = 2249171) B2249171
theorem B1499467 : Blo 1498069 1499467 := bstep (se 1 (by rfl) ⟨1124600, by rfl⟩ : syracuseStep 1499467 = 2249201) B2249201
theorem B1499479 : Blo 1498069 1499479 := bstep (se 1 (by rfl) ⟨1124609, by rfl⟩ : syracuseStep 1499479 = 2249219) B2249219
theorem B1499499 : Blo 1498069 1499499 := bstep (se 1 (by rfl) ⟨1124624, by rfl⟩ : syracuseStep 1499499 = 2249249) B2249249
theorem B1499511 : Blo 1498069 1499511 := bstep (se 1 (by rfl) ⟨1124633, by rfl⟩ : syracuseStep 1499511 = 2249267) B2249267
theorem B1499531 : Blo 1498069 1499531 := bstep (se 1 (by rfl) ⟨1124648, by rfl⟩ : syracuseStep 1499531 = 2249297) B2249297
theorem B1499543 : Blo 1498069 1499543 := bstep (se 1 (by rfl) ⟨1124657, by rfl⟩ : syracuseStep 1499543 = 2249315) B2249315
theorem B1499563 : Blo 1498069 1499563 := bstep (se 1 (by rfl) ⟨1124672, by rfl⟩ : syracuseStep 1499563 = 2249345) B2249345
theorem B3793331 : Blo 1498069 3793331 := bstep (se 1 (by rfl) ⟨2844998, by rfl⟩ : syracuseStep 3793331 = 5689997) B5689997
theorem B8536499 : Blo 1498069 8536499 := bstep (se 1 (by rfl) ⟨6402374, by rfl⟩ : syracuseStep 8536499 = 12804749) B12804749
theorem B1499575 : Blo 1498069 1499575 := bstep (se 1 (by rfl) ⟨1124681, by rfl⟩ : syracuseStep 1499575 = 2249363) B2249363
theorem B4800961 : Blo 1498069 4800961 := bstep (se 2 (by rfl) ⟨1800360, by rfl⟩ : syracuseStep 4800961 = 3600721) B3600721
theorem B3039691 : Blo 1498069 3039691 := bstep (se 1 (by rfl) ⟨2279768, by rfl⟩ : syracuseStep 3039691 = 4559537) B4559537
theorem B1499595 : Blo 1498069 1499595 := bstep (se 1 (by rfl) ⟨1124696, by rfl⟩ : syracuseStep 1499595 = 2249393) B2249393
theorem B1499607 : Blo 1498069 1499607 := bstep (se 1 (by rfl) ⟨1124705, by rfl⟩ : syracuseStep 1499607 = 2249411) B2249411
theorem B3203545 : Blo 1498069 3203545 := bstep (se 2 (by rfl) ⟨1201329, by rfl⟩ : syracuseStep 3203545 = 2402659) B2402659
theorem B1499627 : Blo 1498069 1499627 := bstep (se 1 (by rfl) ⟨1124720, by rfl⟩ : syracuseStep 1499627 = 2249441) B2249441
theorem B1499639 : Blo 1498069 1499639 := bstep (se 1 (by rfl) ⟨1124729, by rfl⟩ : syracuseStep 1499639 = 2249459) B2249459
theorem B1499659 : Blo 1498069 1499659 := bstep (se 1 (by rfl) ⟨1124744, by rfl⟩ : syracuseStep 1499659 = 2249489) B2249489
theorem B12329489 : Blo 1498069 12329489 := bstep (se 2 (by rfl) ⟨4623558, by rfl⟩ : syracuseStep 12329489 = 9247117) B9247117
theorem B1499671 : Blo 1498069 1499671 := bstep (se 1 (by rfl) ⟨1124753, by rfl⟩ : syracuseStep 1499671 = 2249507) B2249507
theorem B1499691 : Blo 1498069 1499691 := bstep (se 1 (by rfl) ⟨1124768, by rfl⟩ : syracuseStep 1499691 = 2249537) B2249537
theorem B1499703 : Blo 1498069 1499703 := bstep (se 1 (by rfl) ⟨1124777, by rfl⟩ : syracuseStep 1499703 = 2249555) B2249555
theorem B19464779 : Blo 1498069 19464779 := bstep (se 1 (by rfl) ⟨14598584, by rfl⟩ : syracuseStep 19464779 = 29197169) B29197169
theorem B1499723 : Blo 1498069 1499723 := bstep (se 1 (by rfl) ⟨1124792, by rfl⟩ : syracuseStep 1499723 = 2249585) B2249585
theorem B2310743 : Blo 1498069 2310743 := bstep (se 1 (by rfl) ⟨1733057, by rfl⟩ : syracuseStep 2310743 = 3466115) B3466115
theorem B1499735 : Blo 1498069 1499735 := bstep (se 1 (by rfl) ⟨1124801, by rfl⟩ : syracuseStep 1499735 = 2249603) B2249603
theorem B1499755 : Blo 1498069 1499755 := bstep (se 1 (by rfl) ⟨1124816, by rfl⟩ : syracuseStep 1499755 = 2249633) B2249633
theorem B1499767 : Blo 1498069 1499767 := bstep (se 1 (by rfl) ⟨1124825, by rfl⟩ : syracuseStep 1499767 = 2249651) B2249651
theorem B5694083 : Blo 1498069 5694083 := bstep (se 1 (by rfl) ⟨4270562, by rfl⟩ : syracuseStep 5694083 = 8541125) B8541125
theorem B1499787 : Blo 1498069 1499787 := bstep (se 1 (by rfl) ⟨1124840, by rfl⟩ : syracuseStep 1499787 = 2249681) B2249681
theorem B5694097 : Blo 1498069 5694097 := bstep (se 2 (by rfl) ⟨2135286, by rfl⟩ : syracuseStep 5694097 = 4270573) B4270573
theorem B1499799 : Blo 1498069 1499799 := bstep (se 1 (by rfl) ⟨1124849, by rfl⟩ : syracuseStep 1499799 = 2249699) B2249699
theorem B1499819 : Blo 1498069 1499819 := bstep (se 1 (by rfl) ⟨1124864, by rfl⟩ : syracuseStep 1499819 = 2249729) B2249729
theorem B1499831 : Blo 1498069 1499831 := bstep (se 1 (by rfl) ⟨1124873, by rfl⟩ : syracuseStep 1499831 = 2249747) B2249747
theorem B1499851 : Blo 1498069 1499851 := bstep (se 1 (by rfl) ⟨1124888, by rfl⟩ : syracuseStep 1499851 = 2249777) B2249777
theorem B1499863 : Blo 1498069 1499863 := bstep (se 1 (by rfl) ⟨1124897, by rfl⟩ : syracuseStep 1499863 = 2249795) B2249795
theorem B3793625 : Blo 1498069 3793625 := bstep (se 2 (by rfl) ⟨1422609, by rfl⟩ : syracuseStep 3793625 = 2845219) B2845219
theorem B1499883 : Blo 1498069 1499883 := bstep (se 1 (by rfl) ⟨1124912, by rfl⟩ : syracuseStep 1499883 = 2249825) B2249825
theorem B1499895 : Blo 1498069 1499895 := bstep (se 1 (by rfl) ⟨1124921, by rfl⟩ : syracuseStep 1499895 = 2249843) B2249843
theorem B1499915 : Blo 1498069 1499915 := bstep (se 1 (by rfl) ⟨1124936, by rfl⟩ : syracuseStep 1499915 = 2249873) B2249873
theorem B1499927 : Blo 1498069 1499927 := bstep (se 1 (by rfl) ⟨1124945, by rfl⟩ : syracuseStep 1499927 = 2249891) B2249891
theorem B2851609 : Blo 1498069 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B1499947 : Blo 1498069 1499947 := bstep (se 1 (by rfl) ⟨1124960, by rfl⟩ : syracuseStep 1499947 = 2249921) B2249921
theorem B2736947 : Blo 1498069 2736947 := bstep (se 1 (by rfl) ⟨2052710, by rfl⟩ : syracuseStep 2736947 = 4105421) B4105421
theorem B1499959 : Blo 1498069 1499959 := bstep (se 1 (by rfl) ⟨1124969, by rfl⟩ : syracuseStep 1499959 = 2249939) B2249939
theorem B10257227 : Blo 1498069 10257227 := bstep (se 1 (by rfl) ⟨7692920, by rfl⟩ : syracuseStep 10257227 = 15385841) B15385841
theorem B1499979 : Blo 1498069 1499979 := bstep (se 1 (by rfl) ⟨1124984, by rfl⟩ : syracuseStep 1499979 = 2249969) B2249969
theorem B3040087 : Blo 1498069 3040087 := bstep (se 1 (by rfl) ⟨2280065, by rfl⟩ : syracuseStep 3040087 = 4560131) B4560131
theorem B1499991 : Blo 1498069 1499991 := bstep (se 1 (by rfl) ⟨1124993, by rfl⟩ : syracuseStep 1499991 = 2249987) B2249987
theorem B1500011 : Blo 1498069 1500011 := bstep (se 1 (by rfl) ⟨1125008, by rfl⟩ : syracuseStep 1500011 = 2250017) B2250017
theorem B1500023 : Blo 1498069 1500023 := bstep (se 1 (by rfl) ⟨1125017, by rfl⟩ : syracuseStep 1500023 = 2250035) B2250035
theorem B1500043 : Blo 1498069 1500043 := bstep (se 1 (by rfl) ⟨1125032, by rfl⟩ : syracuseStep 1500043 = 2250065) B2250065
theorem B1500055 : Blo 1498069 1500055 := bstep (se 1 (by rfl) ⟨1125041, by rfl⟩ : syracuseStep 1500055 = 2250083) B2250083
theorem B5129153 : Blo 1498069 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B5694401 : Blo 1498069 5694401 := bstep (se 2 (by rfl) ⟨2135400, by rfl⟩ : syracuseStep 5694401 = 4270801) B4270801
theorem B1541111 : Blo 1498069 1541111 := bstep (se 1 (by rfl) ⟨1155833, by rfl⟩ : syracuseStep 1541111 = 2311667) B2311667
theorem B12149777 : Blo 1498069 12149777 := bstep (se 2 (by rfl) ⟨4556166, by rfl⟩ : syracuseStep 12149777 = 9112333) B9112333
theorem B10257425 : Blo 1498069 10257425 := bstep (se 2 (by rfl) ⟨3846534, by rfl⟩ : syracuseStep 10257425 = 7693069) B7693069
theorem B6079511 : Blo 1498069 6079511 := bstep (se 1 (by rfl) ⟨4559633, by rfl⟩ : syracuseStep 6079511 = 9119267) B9119267
theorem B10806317 : Blo 1498069 10806317 := bstep (se 3 (by rfl) ⟨2026184, by rfl⟩ : syracuseStep 10806317 = 4052369) B4052369
theorem B4555997 : Blo 1498069 4555997 := bstep (se 3 (by rfl) ⟨854249, by rfl⟩ : syracuseStep 4555997 = 1708499) B1708499
theorem B6399283 : Blo 1498069 6399283 := bstep (se 1 (by rfl) ⟨4799462, by rfl⟩ : syracuseStep 6399283 = 9598925) B9598925
theorem B2024779 : Blo 1498069 2024779 := bstep (se 1 (by rfl) ⟨1518584, by rfl⟩ : syracuseStep 2024779 = 3037169) B3037169
theorem B11535691 : Blo 1498069 11535691 := bstep (se 1 (by rfl) ⟨8651768, by rfl⟩ : syracuseStep 11535691 = 17303537) B17303537
theorem B6079819 : Blo 1498069 6079819 := bstep (se 1 (by rfl) ⟨4559864, by rfl⟩ : syracuseStep 6079819 = 9119729) B9119729
theorem B2844247 : Blo 1498069 2844247 := bstep (se 1 (by rfl) ⟨2133185, by rfl⟩ : syracuseStep 2844247 = 4266371) B4266371
theorem B5695069 : Blo 1498069 5695069 := bstep (se 3 (by rfl) ⟨1067825, by rfl⟩ : syracuseStep 5695069 = 2135651) B2135651
theorem B12977795 : Blo 1498069 12977795 := bstep (se 1 (by rfl) ⟨9733346, by rfl⟩ : syracuseStep 12977795 = 19466693) B19466693
theorem B7300787 : Blo 1498069 7300787 := bstep (se 1 (by rfl) ⟨5475590, by rfl⟩ : syracuseStep 7300787 = 10951181) B10951181
theorem B6489793 : Blo 1498069 6489793 := bstep (se 2 (by rfl) ⟨2433672, by rfl⟩ : syracuseStep 6489793 = 4867345) B4867345
theorem B8652505 : Blo 1498069 8652505 := bstep (se 2 (by rfl) ⟨3244689, by rfl⟩ : syracuseStep 8652505 = 6489379) B6489379
theorem B2844467 : Blo 1498069 2844467 := bstep (se 1 (by rfl) ⟨2133350, by rfl⟩ : syracuseStep 2844467 = 4266701) B4266701
theorem B8537957 : Blo 1498069 8537957 := bstep (se 4 (by rfl) ⟨800433, by rfl⟩ : syracuseStep 8537957 = 1600867) B1600867
theorem B8324995 : Blo 1498069 8324995 := bstep (se 1 (by rfl) ⟨6243746, by rfl⟩ : syracuseStep 8324995 = 12487493) B12487493
theorem B2844695 : Blo 1498069 2844695 := bstep (se 1 (by rfl) ⟨2133521, by rfl⟩ : syracuseStep 2844695 = 4267043) B4267043
theorem B4868171 : Blo 1498069 4868171 := bstep (se 1 (by rfl) ⟨3651128, by rfl⟩ : syracuseStep 4868171 = 7302257) B7302257
theorem B6162605 : Blo 1498069 6162605 := bstep (se 3 (by rfl) ⟨1155488, by rfl⟩ : syracuseStep 6162605 = 2310977) B2310977
theorem B5400793 : Blo 1498069 5400793 := bstep (se 2 (by rfl) ⟨2025297, by rfl⟩ : syracuseStep 5400793 = 4050595) B4050595
theorem B2844953 : Blo 1498069 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B1599787 : Blo 1498069 1599787 := bstep (se 1 (by rfl) ⟨1199840, by rfl⟩ : syracuseStep 1599787 = 2399681) B2399681
theorem B3795275 : Blo 1498069 3795275 := bstep (se 1 (by rfl) ⟨2846456, by rfl⟩ : syracuseStep 3795275 = 5692913) B5692913
theorem B6834577 : Blo 1498069 6834577 := bstep (se 2 (by rfl) ⟨2562966, by rfl⟩ : syracuseStep 6834577 = 5125933) B5125933
theorem B5401025 : Blo 1498069 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B2247179 : Blo 1498069 2247179 := bstep (se 1 (by rfl) ⟨1685384, by rfl⟩ : syracuseStep 2247179 = 3370769) B3370769
theorem B10947089 : Blo 1498069 10947089 := bstep (se 2 (by rfl) ⟨4105158, by rfl⟩ : syracuseStep 10947089 = 8210317) B8210317
theorem B6400529 : Blo 1498069 6400529 := bstep (se 2 (by rfl) ⟨2400198, by rfl⟩ : syracuseStep 6400529 = 4800397) B4800397
theorem B8538641 : Blo 1498069 8538641 := bstep (se 2 (by rfl) ⟨3201990, by rfl⟩ : syracuseStep 8538641 = 6403981) B6403981
theorem B2247191 : Blo 1498069 2247191 := bstep (se 1 (by rfl) ⟨1685393, by rfl⟩ : syracuseStep 2247191 = 3370787) B3370787
theorem B5057099 : Blo 1498069 5057099 := bstep (se 1 (by rfl) ⟨3792824, by rfl⟩ : syracuseStep 5057099 = 7585649) B7585649
theorem B2247257 : Blo 1498069 2247257 := bstep (se 2 (by rfl) ⟨842721, by rfl⟩ : syracuseStep 2247257 = 1685443) B1685443
theorem B2845363 : Blo 1498069 2845363 := bstep (se 1 (by rfl) ⟨2134022, by rfl⟩ : syracuseStep 2845363 = 4268045) B4268045
theorem B2247371 : Blo 1498069 2247371 := bstep (se 1 (by rfl) ⟨1685528, by rfl⟩ : syracuseStep 2247371 = 3371057) B3371057
theorem B2247383 : Blo 1498069 2247383 := bstep (se 1 (by rfl) ⟨1685537, by rfl⟩ : syracuseStep 2247383 = 3371075) B3371075
theorem B2247449 : Blo 1498069 2247449 := bstep (se 2 (by rfl) ⟨842793, by rfl⟩ : syracuseStep 2247449 = 1685587) B1685587
theorem B3418931 : Blo 1498069 3418931 := bstep (se 1 (by rfl) ⟨2564198, by rfl⟩ : syracuseStep 3418931 = 5128397) B5128397
theorem B5057369 : Blo 1498069 5057369 := bstep (se 2 (by rfl) ⟨1896513, by rfl⟩ : syracuseStep 5057369 = 3793027) B3793027
theorem B12979037 : Blo 1498069 12979037 := bstep (se 3 (by rfl) ⟨2433569, by rfl⟩ : syracuseStep 12979037 = 4867139) B4867139
theorem B2247563 : Blo 1498069 2247563 := bstep (se 1 (by rfl) ⟨1685672, by rfl⟩ : syracuseStep 2247563 = 3371345) B3371345
theorem B2247575 : Blo 1498069 2247575 := bstep (se 1 (by rfl) ⟨1685681, by rfl⟩ : syracuseStep 2247575 = 3371363) B3371363
theorem B5770187 : Blo 1498069 5770187 := bstep (se 1 (by rfl) ⟨4327640, by rfl⟩ : syracuseStep 5770187 = 8655281) B8655281
theorem B2247641 : Blo 1498069 2247641 := bstep (se 2 (by rfl) ⟨842865, by rfl⟩ : syracuseStep 2247641 = 1685731) B1685731
theorem B6081587 : Blo 1498069 6081587 := bstep (se 1 (by rfl) ⟨4561190, by rfl⟩ : syracuseStep 6081587 = 9122381) B9122381
theorem B2247755 : Blo 1498069 2247755 := bstep (se 1 (by rfl) ⟨1685816, by rfl⟩ : syracuseStep 2247755 = 3371633) B3371633
theorem B2247767 : Blo 1498069 2247767 := bstep (se 1 (by rfl) ⟨1685825, by rfl⟩ : syracuseStep 2247767 = 3371651) B3371651
theorem B2133145 : Blo 1498069 2133145 := bstep (se 2 (by rfl) ⟨799929, by rfl⟩ : syracuseStep 2133145 = 1599859) B1599859
theorem B2247833 : Blo 1498069 2247833 := bstep (se 2 (by rfl) ⟨842937, by rfl⟩ : syracuseStep 2247833 = 1685875) B1685875
theorem B2845849 : Blo 1498069 2845849 := bstep (se 2 (by rfl) ⟨1067193, by rfl⟩ : syracuseStep 2845849 = 2134387) B2134387
theorem B2247947 : Blo 1498069 2247947 := bstep (se 1 (by rfl) ⟨1685960, by rfl⟩ : syracuseStep 2247947 = 3371921) B3371921
theorem B2247959 : Blo 1498069 2247959 := bstep (se 1 (by rfl) ⟨1685969, by rfl⟩ : syracuseStep 2247959 = 3371939) B3371939
theorem B3796247 : Blo 1498069 3796247 := bstep (se 1 (by rfl) ⟨2847185, by rfl⟩ : syracuseStep 3796247 = 5694371) B5694371
theorem B2248025 : Blo 1498069 2248025 := bstep (se 2 (by rfl) ⟨843009, by rfl⟩ : syracuseStep 2248025 = 1686019) B1686019
theorem B7589213 : Blo 1498069 7589213 := bstep (se 3 (by rfl) ⟨1422977, by rfl⟩ : syracuseStep 7589213 = 2845955) B2845955
theorem B19213685 : Blo 1498069 19213685 := bstep (se 5 (by rfl) ⟨900641, by rfl⟩ : syracuseStep 19213685 = 1801283) B1801283
theorem B2248139 : Blo 1498069 2248139 := bstep (se 1 (by rfl) ⟨1686104, by rfl⟩ : syracuseStep 2248139 = 3372209) B3372209
theorem B2248151 : Blo 1498069 2248151 := bstep (se 1 (by rfl) ⟨1686113, by rfl⟩ : syracuseStep 2248151 = 3372227) B3372227
theorem B5058071 : Blo 1498069 5058071 := bstep (se 1 (by rfl) ⟨3793553, by rfl⟩ : syracuseStep 5058071 = 7587107) B7587107
theorem B2248217 : Blo 1498069 2248217 := bstep (se 2 (by rfl) ⟨843081, by rfl⟩ : syracuseStep 2248217 = 1686163) B1686163
theorem B2248331 : Blo 1498069 2248331 := bstep (se 1 (by rfl) ⟨1686248, by rfl⟩ : syracuseStep 2248331 = 3372497) B3372497
theorem B2248343 : Blo 1498069 2248343 := bstep (se 1 (by rfl) ⟨1686257, by rfl⟩ : syracuseStep 2248343 = 3372515) B3372515
theorem B20803223 : Blo 1498069 20803223 := bstep (se 1 (by rfl) ⟨15602417, by rfl⟩ : syracuseStep 20803223 = 31204835) B31204835
theorem B5689025 : Blo 1498069 5689025 := bstep (se 2 (by rfl) ⟨2133384, by rfl⟩ : syracuseStep 5689025 = 4266769) B4266769
theorem B1896139 : Blo 1498069 1896139 := bstep (se 1 (by rfl) ⟨1422104, by rfl⟩ : syracuseStep 1896139 = 2844209) B2844209
theorem B2846411 : Blo 1498069 2846411 := bstep (se 1 (by rfl) ⟨2134808, by rfl⟩ : syracuseStep 2846411 = 4269617) B4269617
theorem B2248409 : Blo 1498069 2248409 := bstep (se 2 (by rfl) ⟨843153, by rfl⟩ : syracuseStep 2248409 = 1686307) B1686307
theorem B2248523 : Blo 1498069 2248523 := bstep (se 1 (by rfl) ⟨1686392, by rfl⟩ : syracuseStep 2248523 = 3372785) B3372785
theorem B2248535 : Blo 1498069 2248535 := bstep (se 1 (by rfl) ⟨1686401, by rfl⟩ : syracuseStep 2248535 = 3372803) B3372803
theorem B3370841 : Blo 1498069 3370841 := bstep (se 2 (by rfl) ⟨1264065, by rfl⟩ : syracuseStep 3370841 = 2528131) B2528131
theorem B2846593 : Blo 1498069 2846593 := bstep (se 2 (by rfl) ⟨1067472, by rfl⟩ : syracuseStep 2846593 = 2134945) B2134945
theorem B2248601 : Blo 1498069 2248601 := bstep (se 2 (by rfl) ⟨843225, by rfl⟩ : syracuseStep 2248601 = 1686451) B1686451
theorem B3370931 : Blo 1498069 3370931 := bstep (se 1 (by rfl) ⟨2528198, by rfl⟩ : syracuseStep 3370931 = 5056397) B5056397
theorem B3796915 : Blo 1498069 3796915 := bstep (se 1 (by rfl) ⟨2847686, by rfl⟩ : syracuseStep 3796915 = 5695373) B5695373
theorem B3370967 : Blo 1498069 3370967 := bstep (se 1 (by rfl) ⟨2528225, by rfl⟩ : syracuseStep 3370967 = 5056451) B5056451
theorem B2248715 : Blo 1498069 2248715 := bstep (se 1 (by rfl) ⟨1686536, by rfl⟩ : syracuseStep 2248715 = 3373073) B3373073
theorem B2248727 : Blo 1498069 2248727 := bstep (se 1 (by rfl) ⟨1686545, by rfl⟩ : syracuseStep 2248727 = 3373091) B3373091
theorem B5058611 : Blo 1498069 5058611 := bstep (se 1 (by rfl) ⟨3793958, by rfl⟩ : syracuseStep 5058611 = 7587917) B7587917
theorem B1519703 : Blo 1498069 1519703 := bstep (se 1 (by rfl) ⟨1139777, by rfl⟩ : syracuseStep 1519703 = 2279555) B2279555
theorem B2248793 : Blo 1498069 2248793 := bstep (se 2 (by rfl) ⟨843297, by rfl⟩ : syracuseStep 2248793 = 1686595) B1686595
theorem B3371147 : Blo 1498069 3371147 := bstep (se 1 (by rfl) ⟨2528360, by rfl⟩ : syracuseStep 3371147 = 5056721) B5056721
theorem B3371201 : Blo 1498069 3371201 := bstep (se 2 (by rfl) ⟨1264200, by rfl⟩ : syracuseStep 3371201 = 2528401) B2528401
theorem B2248907 : Blo 1498069 2248907 := bstep (se 1 (by rfl) ⟨1686680, by rfl⟩ : syracuseStep 2248907 = 3373361) B3373361
theorem B2248919 : Blo 1498069 2248919 := bstep (se 1 (by rfl) ⟨1686689, by rfl⟩ : syracuseStep 2248919 = 3373379) B3373379
theorem B1601803 : Blo 1498069 1601803 := bstep (se 1 (by rfl) ⟨1201352, by rfl⟩ : syracuseStep 1601803 = 2402705) B2402705
theorem B2248985 : Blo 1498069 2248985 := bstep (se 2 (by rfl) ⟨843369, by rfl⟩ : syracuseStep 2248985 = 1686739) B1686739
theorem B5058881 : Blo 1498069 5058881 := bstep (se 2 (by rfl) ⟨1897080, by rfl⟩ : syracuseStep 5058881 = 3794161) B3794161
theorem B2249099 : Blo 1498069 2249099 := bstep (se 1 (by rfl) ⟨1686824, by rfl⟩ : syracuseStep 2249099 = 3373649) B3373649
theorem B4559255 : Blo 1498069 4559255 := bstep (se 1 (by rfl) ⟨3419441, by rfl⟩ : syracuseStep 4559255 = 6838883) B6838883
theorem B2249111 : Blo 1498069 2249111 := bstep (se 1 (by rfl) ⟨1686833, by rfl⟩ : syracuseStep 2249111 = 3373667) B3373667
theorem B3371417 : Blo 1498069 3371417 := bstep (se 2 (by rfl) ⟨1264281, by rfl⟩ : syracuseStep 3371417 = 2528563) B2528563
theorem B2249177 : Blo 1498069 2249177 := bstep (se 2 (by rfl) ⟨843441, by rfl⟩ : syracuseStep 2249177 = 1686883) B1686883
theorem B3371507 : Blo 1498069 3371507 := bstep (se 1 (by rfl) ⟨2528630, by rfl⟩ : syracuseStep 3371507 = 5057261) B5057261
theorem B3420683 : Blo 1498069 3420683 := bstep (se 1 (by rfl) ⟨2565512, by rfl⟩ : syracuseStep 3420683 = 5131025) B5131025
theorem B3371543 : Blo 1498069 3371543 := bstep (se 1 (by rfl) ⟨2528657, by rfl⟩ : syracuseStep 3371543 = 5057315) B5057315
theorem B3199513 : Blo 1498069 3199513 := bstep (se 2 (by rfl) ⟨1199817, by rfl⟩ : syracuseStep 3199513 = 2399635) B2399635
theorem B4108865 : Blo 1498069 4108865 := bstep (se 2 (by rfl) ⟨1540824, by rfl⟩ : syracuseStep 4108865 = 3081649) B3081649
theorem B2134603 : Blo 1498069 2134603 := bstep (se 1 (by rfl) ⟨1600952, by rfl⟩ : syracuseStep 2134603 = 3201905) B3201905
theorem B2249291 : Blo 1498069 2249291 := bstep (se 1 (by rfl) ⟨1686968, by rfl⟩ : syracuseStep 2249291 = 3373937) B3373937
theorem B2847307 : Blo 1498069 2847307 := bstep (se 1 (by rfl) ⟨2135480, by rfl⟩ : syracuseStep 2847307 = 4270961) B4270961
theorem B2134615 : Blo 1498069 2134615 := bstep (se 1 (by rfl) ⟨1600961, by rfl⟩ : syracuseStep 2134615 = 3201923) B3201923
theorem B2249303 : Blo 1498069 2249303 := bstep (se 1 (by rfl) ⟨1686977, by rfl⟩ : syracuseStep 2249303 = 3373955) B3373955
theorem B13677149 : Blo 1498069 13677149 := bstep (se 3 (by rfl) ⟨2564465, by rfl⟩ : syracuseStep 13677149 = 5128931) B5128931
theorem B1520267 : Blo 1498069 1520267 := bstep (se 1 (by rfl) ⟨1140200, by rfl⟩ : syracuseStep 1520267 = 2280401) B2280401
theorem B1897111 : Blo 1498069 1897111 := bstep (se 1 (by rfl) ⟨1422833, by rfl⟩ : syracuseStep 1897111 = 2845667) B2845667
theorem B10810007 : Blo 1498069 10810007 := bstep (se 1 (by rfl) ⟨8107505, by rfl⟩ : syracuseStep 10810007 = 16215011) B16215011
theorem B2699929 : Blo 1498069 2699929 := bstep (se 2 (by rfl) ⟨1012473, by rfl⟩ : syracuseStep 2699929 = 2024947) B2024947
theorem B2249369 : Blo 1498069 2249369 := bstep (se 2 (by rfl) ⟨843513, by rfl⟩ : syracuseStep 2249369 = 1687027) B1687027
theorem B2847383 : Blo 1498069 2847383 := bstep (se 1 (by rfl) ⟨2135537, by rfl⟩ : syracuseStep 2847383 = 4271075) B4271075
theorem B3371723 : Blo 1498069 3371723 := bstep (se 1 (by rfl) ⟨2528792, by rfl⟩ : syracuseStep 3371723 = 5057585) B5057585
theorem B2699993 : Blo 1498069 2699993 := bstep (se 2 (by rfl) ⟨1012497, by rfl⟩ : syracuseStep 2699993 = 2024995) B2024995
theorem B3371777 : Blo 1498069 3371777 := bstep (se 2 (by rfl) ⟨1264416, by rfl⟩ : syracuseStep 3371777 = 2528833) B2528833
theorem B17068805 : Blo 1498069 17068805 := bstep (se 4 (by rfl) ⟨1600200, by rfl⟩ : syracuseStep 17068805 = 3200401) B3200401
theorem B24048389 : Blo 1498069 24048389 := bstep (se 4 (by rfl) ⟨2254536, by rfl⟩ : syracuseStep 24048389 = 4509073) B4509073
theorem B2249483 : Blo 1498069 2249483 := bstep (se 1 (by rfl) ⟨1687112, by rfl⟩ : syracuseStep 2249483 = 3374225) B3374225
theorem B2528023 : Blo 1498069 2528023 := bstep (se 1 (by rfl) ⟨1896017, by rfl⟩ : syracuseStep 2528023 = 3792035) B3792035
theorem B2249495 : Blo 1498069 2249495 := bstep (se 1 (by rfl) ⟨1687121, by rfl⟩ : syracuseStep 2249495 = 3374243) B3374243
theorem B2249561 : Blo 1498069 2249561 := bstep (se 2 (by rfl) ⟨843585, by rfl⟩ : syracuseStep 2249561 = 1687171) B1687171
theorem B5059421 : Blo 1498069 5059421 := bstep (se 3 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 5059421 = 1897283) B1897283
theorem B6402989 : Blo 1498069 6402989 := bstep (se 3 (by rfl) ⟨1200560, by rfl⟩ : syracuseStep 6402989 = 2401121) B2401121
theorem B2249675 : Blo 1498069 2249675 := bstep (se 1 (by rfl) ⟨1687256, by rfl⟩ : syracuseStep 2249675 = 3374513) B3374513
theorem B2249687 : Blo 1498069 2249687 := bstep (se 1 (by rfl) ⟨1687265, by rfl⟩ : syracuseStep 2249687 = 3374531) B3374531
theorem B3371993 : Blo 1498069 3371993 := bstep (se 2 (by rfl) ⟨1264497, by rfl⟩ : syracuseStep 3371993 = 2528995) B2528995
theorem B4387805 : Blo 1498069 4387805 := bstep (se 3 (by rfl) ⟨822713, by rfl⟩ : syracuseStep 4387805 = 1645427) B1645427
theorem B2249753 : Blo 1498069 2249753 := bstep (se 2 (by rfl) ⟨843657, by rfl⟩ : syracuseStep 2249753 = 1687315) B1687315
theorem B3372083 : Blo 1498069 3372083 := bstep (se 1 (by rfl) ⟨2529062, by rfl⟩ : syracuseStep 3372083 = 5058125) B5058125
theorem B8107073 : Blo 1498069 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B3372119 : Blo 1498069 3372119 := bstep (se 1 (by rfl) ⟨2529089, by rfl⟩ : syracuseStep 3372119 = 5058179) B5058179
theorem B2249867 : Blo 1498069 2249867 := bstep (se 1 (by rfl) ⟨1687400, by rfl⟩ : syracuseStep 2249867 = 3374801) B3374801
theorem B5690513 : Blo 1498069 5690513 := bstep (se 2 (by rfl) ⟨2133942, by rfl⟩ : syracuseStep 5690513 = 4267885) B4267885
theorem B5403793 : Blo 1498069 5403793 := bstep (se 2 (by rfl) ⟨2026422, by rfl⟩ : syracuseStep 5403793 = 4052845) B4052845
theorem B2249879 : Blo 1498069 2249879 := bstep (se 1 (by rfl) ⟨1687409, by rfl⟩ : syracuseStep 2249879 = 3374819) B3374819
theorem B2249945 : Blo 1498069 2249945 := bstep (se 2 (by rfl) ⟨843729, by rfl⟩ : syracuseStep 2249945 = 1687459) B1687459
theorem B3372299 : Blo 1498069 3372299 := bstep (se 1 (by rfl) ⟨2529224, by rfl⟩ : syracuseStep 3372299 = 5058449) B5058449
theorem B7796033 : Blo 1498069 7796033 := bstep (se 2 (by rfl) ⟨2923512, by rfl⟩ : syracuseStep 7796033 = 5847025) B5847025
theorem B3372353 : Blo 1498069 3372353 := bstep (se 2 (by rfl) ⟨1264632, by rfl⟩ : syracuseStep 3372353 = 2529265) B2529265
theorem B2250059 : Blo 1498069 2250059 := bstep (se 1 (by rfl) ⟨1687544, by rfl⟩ : syracuseStep 2250059 = 3375089) B3375089
theorem B2250071 : Blo 1498069 2250071 := bstep (se 1 (by rfl) ⟨1687553, by rfl⟩ : syracuseStep 2250071 = 3375107) B3375107
theorem B2528651 : Blo 1498069 2528651 := bstep (se 1 (by rfl) ⟨1896488, by rfl⟩ : syracuseStep 2528651 = 3792977) B3792977
theorem B7591319 : Blo 1498069 7591319 := bstep (se 1 (by rfl) ⟨5693489, by rfl⟩ : syracuseStep 7591319 = 11386979) B11386979
theorem B1897931 : Blo 1498069 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B2528779 : Blo 1498069 2528779 := bstep (se 1 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 2528779 = 3793169) B3793169
theorem B3372569 : Blo 1498069 3372569 := bstep (se 2 (by rfl) ⟨1264713, by rfl⟩ : syracuseStep 3372569 = 2529427) B2529427
theorem B5690969 : Blo 1498069 5690969 := bstep (se 2 (by rfl) ⟨2134113, by rfl⟩ : syracuseStep 5690969 = 4268227) B4268227
theorem B6403673 : Blo 1498069 6403673 := bstep (se 2 (by rfl) ⟨2401377, by rfl⟩ : syracuseStep 6403673 = 4802755) B4802755
theorem B3372659 : Blo 1498069 3372659 := bstep (se 1 (by rfl) ⟨2529494, by rfl⟩ : syracuseStep 3372659 = 5058989) B5058989
theorem B3372695 : Blo 1498069 3372695 := bstep (se 1 (by rfl) ⟨2529521, by rfl⟩ : syracuseStep 3372695 = 5059043) B5059043
theorem B2528921 : Blo 1498069 2528921 := bstep (se 2 (by rfl) ⟨948345, by rfl⟩ : syracuseStep 2528921 = 1896691) B1896691
theorem B8541875 : Blo 1498069 8541875 := bstep (se 1 (by rfl) ⟨6406406, by rfl⟩ : syracuseStep 8541875 = 12812813) B12812813
theorem B2529049 : Blo 1498069 2529049 := bstep (se 2 (by rfl) ⟨948393, by rfl⟩ : syracuseStep 2529049 = 1896787) B1896787
theorem B5691181 : Blo 1498069 5691181 := bstep (se 3 (by rfl) ⟨1067096, by rfl⟩ : syracuseStep 5691181 = 2134193) B2134193
theorem B8533835 : Blo 1498069 8533835 := bstep (se 1 (by rfl) ⟨6400376, by rfl⟩ : syracuseStep 8533835 = 12800753) B12800753
theorem B3372875 : Blo 1498069 3372875 := bstep (se 1 (by rfl) ⟨2529656, by rfl⟩ : syracuseStep 3372875 = 5059313) B5059313
theorem B1685335 : Blo 1498069 1685335 := bstep (se 1 (by rfl) ⟨1264001, by rfl⟩ : syracuseStep 1685335 = 2528003) B2528003
theorem B3200897 : Blo 1498069 3200897 := bstep (se 2 (by rfl) ⟨1200336, by rfl⟩ : syracuseStep 3200897 = 2400673) B2400673
theorem B3372929 : Blo 1498069 3372929 := bstep (se 2 (by rfl) ⟨1264848, by rfl⟩ : syracuseStep 3372929 = 2529697) B2529697
theorem B5060555 : Blo 1498069 5060555 := bstep (se 1 (by rfl) ⟨3795416, by rfl⟩ : syracuseStep 5060555 = 7590833) B7590833
theorem B1685515 : Blo 1498069 1685515 := bstep (se 1 (by rfl) ⟨1264136, by rfl⟩ : syracuseStep 1685515 = 2528273) B2528273
theorem B3373145 : Blo 1498069 3373145 := bstep (se 2 (by rfl) ⟨1264929, by rfl⟩ : syracuseStep 3373145 = 2529859) B2529859
theorem B5691485 : Blo 1498069 5691485 := bstep (se 3 (by rfl) ⟨1067153, by rfl⟩ : syracuseStep 5691485 = 2134307) B2134307
theorem B1685623 : Blo 1498069 1685623 := bstep (se 1 (by rfl) ⟨1264217, by rfl⟩ : syracuseStep 1685623 = 2528435) B2528435
theorem B3373235 : Blo 1498069 3373235 := bstep (se 1 (by rfl) ⟨2529926, by rfl⟩ : syracuseStep 3373235 = 5059853) B5059853
theorem B21608653 : Blo 1498069 21608653 := bstep (se 3 (by rfl) ⟨4051622, by rfl⟩ : syracuseStep 21608653 = 8103245) B8103245
theorem B3373271 : Blo 1498069 3373271 := bstep (se 1 (by rfl) ⟨2529953, by rfl⟩ : syracuseStep 3373271 = 5059907) B5059907
theorem B5060825 : Blo 1498069 5060825 := bstep (se 2 (by rfl) ⟨1897809, by rfl⟩ : syracuseStep 5060825 = 3795619) B3795619
theorem B1685803 : Blo 1498069 1685803 := bstep (se 1 (by rfl) ⟨1264352, by rfl⟩ : syracuseStep 1685803 = 2528705) B2528705
theorem B2529623 : Blo 1498069 2529623 := bstep (se 1 (by rfl) ⟨1897217, by rfl⟩ : syracuseStep 2529623 = 3794435) B3794435
theorem B3201419 : Blo 1498069 3201419 := bstep (se 1 (by rfl) ⟨2401064, by rfl⟩ : syracuseStep 3201419 = 4802129) B4802129
theorem B3373451 : Blo 1498069 3373451 := bstep (se 1 (by rfl) ⟨2530088, by rfl⟩ : syracuseStep 3373451 = 5060177) B5060177
theorem B1685911 : Blo 1498069 1685911 := bstep (se 1 (by rfl) ⟨1264433, by rfl⟩ : syracuseStep 1685911 = 2528867) B2528867
theorem B9599411 : Blo 1498069 9599411 := bstep (se 1 (by rfl) ⟨7199558, by rfl⟩ : syracuseStep 9599411 = 14399117) B14399117
theorem B3373505 : Blo 1498069 3373505 := bstep (se 2 (by rfl) ⟨1265064, by rfl⟩ : syracuseStep 3373505 = 2530129) B2530129
theorem B2529751 : Blo 1498069 2529751 := bstep (se 1 (by rfl) ⟨1897313, by rfl⟩ : syracuseStep 2529751 = 3794627) B3794627
theorem B6494681 : Blo 1498069 6494681 := bstep (se 2 (by rfl) ⟨2435505, by rfl⟩ : syracuseStep 6494681 = 4871011) B4871011
theorem B9599563 : Blo 1498069 9599563 := bstep (se 1 (by rfl) ⟨7199672, by rfl⟩ : syracuseStep 9599563 = 14399345) B14399345
theorem B1686091 : Blo 1498069 1686091 := bstep (se 1 (by rfl) ⟨1264568, by rfl⟩ : syracuseStep 1686091 = 2529137) B2529137
theorem B7207555 : Blo 1498069 7207555 := bstep (se 1 (by rfl) ⟨5405666, by rfl⟩ : syracuseStep 7207555 = 10811333) B10811333
theorem B3373721 : Blo 1498069 3373721 := bstep (se 2 (by rfl) ⟨1265145, by rfl⟩ : syracuseStep 3373721 = 2530291) B2530291
theorem B11385521 : Blo 1498069 11385521 := bstep (se 2 (by rfl) ⟨4269570, by rfl⟩ : syracuseStep 11385521 = 8539141) B8539141
theorem B1686199 : Blo 1498069 1686199 := bstep (se 1 (by rfl) ⟨1264649, by rfl⟩ : syracuseStep 1686199 = 2529299) B2529299
theorem B3373811 : Blo 1498069 3373811 := bstep (se 1 (by rfl) ⟨2530358, by rfl⟩ : syracuseStep 3373811 = 5060717) B5060717
theorem B3373847 : Blo 1498069 3373847 := bstep (se 1 (by rfl) ⟨2530385, by rfl⟩ : syracuseStep 3373847 = 5060771) B5060771
theorem B4266827 : Blo 1498069 4266827 := bstep (se 1 (by rfl) ⟨3200120, by rfl⟩ : syracuseStep 4266827 = 6400241) B6400241
theorem B6404939 : Blo 1498069 6404939 := bstep (se 1 (by rfl) ⟨4803704, by rfl⟩ : syracuseStep 6404939 = 9607409) B9607409
theorem B4799321 : Blo 1498069 4799321 := bstep (se 2 (by rfl) ⟨1799745, by rfl⟩ : syracuseStep 4799321 = 3599491) B3599491
theorem B1686379 : Blo 1498069 1686379 := bstep (se 1 (by rfl) ⟨1264784, by rfl⟩ : syracuseStep 1686379 = 2529569) B2529569
theorem B5061527 : Blo 1498069 5061527 := bstep (se 1 (by rfl) ⟨3796145, by rfl⟩ : syracuseStep 5061527 = 7592291) B7592291
theorem B30759859 : Blo 1498069 30759859 := bstep (se 1 (by rfl) ⟨23069894, by rfl⟩ : syracuseStep 30759859 = 46139789) B46139789
theorem B3374027 : Blo 1498069 3374027 := bstep (se 1 (by rfl) ⟨2530520, by rfl⟩ : syracuseStep 3374027 = 5061041) B5061041
theorem B1498071 : Blo 1498069 1498071 := bstep (se 1 (by rfl) ⟨1123553, by rfl⟩ : syracuseStep 1498071 = 2247107) B2247107
theorem B1686487 : Blo 1498069 1686487 := bstep (se 1 (by rfl) ⟨1264865, by rfl⟩ : syracuseStep 1686487 = 2529731) B2529731
theorem B1498091 : Blo 1498069 1498091 := bstep (se 1 (by rfl) ⟨1123568, by rfl⟩ : syracuseStep 1498091 = 2247137) B2247137
theorem B1498103 : Blo 1498069 1498103 := bstep (se 1 (by rfl) ⟨1123577, by rfl⟩ : syracuseStep 1498103 = 2247155) B2247155
theorem B3374081 : Blo 1498069 3374081 := bstep (se 2 (by rfl) ⟨1265280, by rfl⟩ : syracuseStep 3374081 = 2530561) B2530561
theorem B1498123 : Blo 1498069 1498123 := bstep (se 1 (by rfl) ⟨1123592, by rfl⟩ : syracuseStep 1498123 = 2247185) B2247185
theorem B1498135 : Blo 1498069 1498135 := bstep (se 1 (by rfl) ⟨1123601, by rfl⟩ : syracuseStep 1498135 = 2247203) B2247203
theorem B12155939 : Blo 1498069 12155939 := bstep (se 1 (by rfl) ⟨9116954, by rfl⟩ : syracuseStep 12155939 = 18233909) B18233909
theorem B1498155 : Blo 1498069 1498155 := bstep (se 1 (by rfl) ⟨1123616, by rfl⟩ : syracuseStep 1498155 = 2247233) B2247233
theorem B5405741 : Blo 1498069 5405741 := bstep (se 3 (by rfl) ⟨1013576, by rfl⟩ : syracuseStep 5405741 = 2027153) B2027153
theorem B1498167 : Blo 1498069 1498167 := bstep (se 1 (by rfl) ⟨1123625, by rfl⟩ : syracuseStep 1498167 = 2247251) B2247251
theorem B1498187 : Blo 1498069 1498187 := bstep (se 1 (by rfl) ⟨1123640, by rfl⟩ : syracuseStep 1498187 = 2247281) B2247281
theorem B2530379 : Blo 1498069 2530379 := bstep (se 1 (by rfl) ⟨1897784, by rfl⟩ : syracuseStep 2530379 = 3795569) B3795569
theorem B1498199 : Blo 1498069 1498199 := bstep (se 1 (by rfl) ⟨1123649, by rfl⟩ : syracuseStep 1498199 = 2247299) B2247299
theorem B8543333 : Blo 1498069 8543333 := bstep (se 4 (by rfl) ⟨800937, by rfl⟩ : syracuseStep 8543333 = 1601875) B1601875
theorem B1498219 : Blo 1498069 1498219 := bstep (se 1 (by rfl) ⟨1123664, by rfl⟩ : syracuseStep 1498219 = 2247329) B2247329
theorem B1498231 : Blo 1498069 1498231 := bstep (se 1 (by rfl) ⟨1123673, by rfl⟩ : syracuseStep 1498231 = 2247347) B2247347
theorem B1498251 : Blo 1498069 1498251 := bstep (se 1 (by rfl) ⟨1123688, by rfl⟩ : syracuseStep 1498251 = 2247377) B2247377
theorem B1686667 : Blo 1498069 1686667 := bstep (se 1 (by rfl) ⟨1265000, by rfl⟩ : syracuseStep 1686667 = 2530001) B2530001
theorem B1498263 : Blo 1498069 1498263 := bstep (se 1 (by rfl) ⟨1123697, by rfl⟩ : syracuseStep 1498263 = 2247395) B2247395
theorem B11386007 : Blo 1498069 11386007 := bstep (se 1 (by rfl) ⟨8539505, by rfl⟩ : syracuseStep 11386007 = 17079011) B17079011
theorem B1498283 : Blo 1498069 1498283 := bstep (se 1 (by rfl) ⟨1123712, by rfl⟩ : syracuseStep 1498283 = 2247425) B2247425
theorem B1498295 : Blo 1498069 1498295 := bstep (se 1 (by rfl) ⟨1123721, by rfl⟩ : syracuseStep 1498295 = 2247443) B2247443
theorem B6405313 : Blo 1498069 6405313 := bstep (se 2 (by rfl) ⟨2401992, by rfl⟩ : syracuseStep 6405313 = 4803985) B4803985
theorem B1498315 : Blo 1498069 1498315 := bstep (se 1 (by rfl) ⟨1123736, by rfl⟩ : syracuseStep 1498315 = 2247473) B2247473
theorem B2530507 : Blo 1498069 2530507 := bstep (se 1 (by rfl) ⟨1897880, by rfl⟩ : syracuseStep 2530507 = 3795761) B3795761
theorem B1498327 : Blo 1498069 1498327 := bstep (se 1 (by rfl) ⟨1123745, by rfl⟩ : syracuseStep 1498327 = 2247491) B2247491
theorem B3374297 : Blo 1498069 3374297 := bstep (se 2 (by rfl) ⟨1265361, by rfl⟩ : syracuseStep 3374297 = 2530723) B2530723
theorem B1498347 : Blo 1498069 1498347 := bstep (se 1 (by rfl) ⟨1123760, by rfl⟩ : syracuseStep 1498347 = 2247521) B2247521
theorem B1498359 : Blo 1498069 1498359 := bstep (se 1 (by rfl) ⟨1123769, by rfl⟩ : syracuseStep 1498359 = 2247539) B2247539
theorem B1686775 : Blo 1498069 1686775 := bstep (se 1 (by rfl) ⟨1265081, by rfl⟩ : syracuseStep 1686775 = 2530163) B2530163
theorem B1498379 : Blo 1498069 1498379 := bstep (se 1 (by rfl) ⟨1123784, by rfl⟩ : syracuseStep 1498379 = 2247569) B2247569
theorem B1498391 : Blo 1498069 1498391 := bstep (se 1 (by rfl) ⟨1123793, by rfl⟩ : syracuseStep 1498391 = 2247587) B2247587
theorem B1498411 : Blo 1498069 1498411 := bstep (se 1 (by rfl) ⟨1123808, by rfl⟩ : syracuseStep 1498411 = 2247617) B2247617
theorem B3374387 : Blo 1498069 3374387 := bstep (se 1 (by rfl) ⟨2530790, by rfl⟩ : syracuseStep 3374387 = 5061581) B5061581
theorem B1498423 : Blo 1498069 1498423 := bstep (se 1 (by rfl) ⟨1123817, by rfl⟩ : syracuseStep 1498423 = 2247635) B2247635
theorem B1498443 : Blo 1498069 1498443 := bstep (se 1 (by rfl) ⟨1123832, by rfl⟩ : syracuseStep 1498443 = 2247665) B2247665
theorem B1498455 : Blo 1498069 1498455 := bstep (se 1 (by rfl) ⟨1123841, by rfl⟩ : syracuseStep 1498455 = 2247683) B2247683
theorem B3792217 : Blo 1498069 3792217 := bstep (se 2 (by rfl) ⟨1422081, by rfl⟩ : syracuseStep 3792217 = 2844163) B2844163
theorem B2530649 : Blo 1498069 2530649 := bstep (se 2 (by rfl) ⟨948993, by rfl⟩ : syracuseStep 2530649 = 1897987) B1897987
theorem B3374423 : Blo 1498069 3374423 := bstep (se 1 (by rfl) ⟨2530817, by rfl⟩ : syracuseStep 3374423 = 5061635) B5061635
theorem B1498475 : Blo 1498069 1498475 := bstep (se 1 (by rfl) ⟨1123856, by rfl⟩ : syracuseStep 1498475 = 2247713) B2247713
theorem B1498487 : Blo 1498069 1498487 := bstep (se 1 (by rfl) ⟨1123865, by rfl⟩ : syracuseStep 1498487 = 2247731) B2247731
theorem B1498507 : Blo 1498069 1498507 := bstep (se 1 (by rfl) ⟨1123880, by rfl⟩ : syracuseStep 1498507 = 2247761) B2247761
theorem B1498519 : Blo 1498069 1498519 := bstep (se 1 (by rfl) ⟨1123889, by rfl⟩ : syracuseStep 1498519 = 2247779) B2247779
theorem B2563481 : Blo 1498069 2563481 := bstep (se 2 (by rfl) ⟨961305, by rfl⟩ : syracuseStep 2563481 = 1922611) B1922611
theorem B1498539 : Blo 1498069 1498539 := bstep (se 1 (by rfl) ⟨1123904, by rfl⟩ : syracuseStep 1498539 = 2247809) B2247809
theorem B1686955 : Blo 1498069 1686955 := bstep (se 1 (by rfl) ⟨1265216, by rfl⟩ : syracuseStep 1686955 = 2530433) B2530433
theorem B5062067 : Blo 1498069 5062067 := bstep (se 1 (by rfl) ⟨3796550, by rfl⟩ : syracuseStep 5062067 = 7593101) B7593101
theorem B1498551 : Blo 1498069 1498551 := bstep (se 1 (by rfl) ⟨1123913, by rfl⟩ : syracuseStep 1498551 = 2247827) B2247827
theorem B1498571 : Blo 1498069 1498571 := bstep (se 1 (by rfl) ⟨1123928, by rfl⟩ : syracuseStep 1498571 = 2247857) B2247857
theorem B1498583 : Blo 1498069 1498583 := bstep (se 1 (by rfl) ⟨1123937, by rfl⟩ : syracuseStep 1498583 = 2247875) B2247875
theorem B2530777 : Blo 1498069 2530777 := bstep (se 2 (by rfl) ⟨949041, by rfl⟩ : syracuseStep 2530777 = 1898083) B1898083
theorem B1498603 : Blo 1498069 1498603 := bstep (se 1 (by rfl) ⟨1123952, by rfl⟩ : syracuseStep 1498603 = 2247905) B2247905
theorem B1498615 : Blo 1498069 1498615 := bstep (se 1 (by rfl) ⟨1123961, by rfl⟩ : syracuseStep 1498615 = 2247923) B2247923
theorem B1498635 : Blo 1498069 1498635 := bstep (se 1 (by rfl) ⟨1123976, by rfl⟩ : syracuseStep 1498635 = 2247953) B2247953
theorem B3374603 : Blo 1498069 3374603 := bstep (se 1 (by rfl) ⟨2530952, by rfl⟩ : syracuseStep 3374603 = 5061905) B5061905
theorem B1498647 : Blo 1498069 1498647 := bstep (se 1 (by rfl) ⟨1123985, by rfl⟩ : syracuseStep 1498647 = 2247971) B2247971
theorem B1687063 : Blo 1498069 1687063 := bstep (se 1 (by rfl) ⟨1265297, by rfl⟩ : syracuseStep 1687063 = 2530595) B2530595
theorem B6405655 : Blo 1498069 6405655 := bstep (se 1 (by rfl) ⟨4804241, by rfl⟩ : syracuseStep 6405655 = 9608483) B9608483
theorem B1498667 : Blo 1498069 1498667 := bstep (se 1 (by rfl) ⟨1124000, by rfl⟩ : syracuseStep 1498667 = 2248001) B2248001
theorem B7585325 : Blo 1498069 7585325 := bstep (se 3 (by rfl) ⟨1422248, by rfl⟩ : syracuseStep 7585325 = 2844497) B2844497
theorem B5127731 : Blo 1498069 5127731 := bstep (se 1 (by rfl) ⟨3845798, by rfl⟩ : syracuseStep 5127731 = 7691597) B7691597
theorem B1498679 : Blo 1498069 1498679 := bstep (se 1 (by rfl) ⟨1124009, by rfl⟩ : syracuseStep 1498679 = 2248019) B2248019
theorem B3374657 : Blo 1498069 3374657 := bstep (se 2 (by rfl) ⟨1265496, by rfl⟩ : syracuseStep 3374657 = 2530993) B2530993
theorem B1498699 : Blo 1498069 1498699 := bstep (se 1 (by rfl) ⟨1124024, by rfl⟩ : syracuseStep 1498699 = 2248049) B2248049
theorem B23076427 : Blo 1498069 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B1498711 : Blo 1498069 1498711 := bstep (se 1 (by rfl) ⟨1124033, by rfl⟩ : syracuseStep 1498711 = 2248067) B2248067
theorem B3202649 : Blo 1498069 3202649 := bstep (se 2 (by rfl) ⟨1200993, by rfl⟩ : syracuseStep 3202649 = 2401987) B2401987
theorem B1498731 : Blo 1498069 1498731 := bstep (se 1 (by rfl) ⟨1124048, by rfl⟩ : syracuseStep 1498731 = 2248097) B2248097
theorem B1498743 : Blo 1498069 1498743 := bstep (se 1 (by rfl) ⟨1124057, by rfl⟩ : syracuseStep 1498743 = 2248115) B2248115
theorem B1498763 : Blo 1498069 1498763 := bstep (se 1 (by rfl) ⟨1124072, by rfl⟩ : syracuseStep 1498763 = 2248145) B2248145
theorem B16203415 : Blo 1498069 16203415 := bstep (se 1 (by rfl) ⟨12152561, by rfl⟩ : syracuseStep 16203415 = 24305123) B24305123
theorem B1498775 : Blo 1498069 1498775 := bstep (se 1 (by rfl) ⟨1124081, by rfl⟩ : syracuseStep 1498775 = 2248163) B2248163
theorem B1498795 : Blo 1498069 1498795 := bstep (se 1 (by rfl) ⟨1124096, by rfl⟩ : syracuseStep 1498795 = 2248193) B2248193
theorem B1498807 : Blo 1498069 1498807 := bstep (se 1 (by rfl) ⟨1124105, by rfl⟩ : syracuseStep 1498807 = 2248211) B2248211
theorem B5062337 : Blo 1498069 5062337 := bstep (se 2 (by rfl) ⟨1898376, by rfl⟩ : syracuseStep 5062337 = 3796753) B3796753
theorem B164003525 : Blo 1498069 164003525 := bstep (se 4 (by rfl) ⟨15375330, by rfl⟩ : syracuseStep 164003525 = 30750661) B30750661
theorem B1498827 : Blo 1498069 1498827 := bstep (se 1 (by rfl) ⟨1124120, by rfl⟩ : syracuseStep 1498827 = 2248241) B2248241
theorem B1687243 : Blo 1498069 1687243 := bstep (se 1 (by rfl) ⟨1265432, by rfl⟩ : syracuseStep 1687243 = 2530865) B2530865
theorem B1498839 : Blo 1498069 1498839 := bstep (se 1 (by rfl) ⟨1124129, by rfl⟩ : syracuseStep 1498839 = 2248259) B2248259
theorem B1498859 : Blo 1498069 1498859 := bstep (se 1 (by rfl) ⟨1124144, by rfl⟩ : syracuseStep 1498859 = 2248289) B2248289
theorem B1498871 : Blo 1498069 1498871 := bstep (se 1 (by rfl) ⟨1124153, by rfl⟩ : syracuseStep 1498871 = 2248307) B2248307
theorem B1498891 : Blo 1498069 1498891 := bstep (se 1 (by rfl) ⟨1124168, by rfl⟩ : syracuseStep 1498891 = 2248337) B2248337
theorem B1498903 : Blo 1498069 1498903 := bstep (se 1 (by rfl) ⟨1124177, by rfl⟩ : syracuseStep 1498903 = 2248355) B2248355
theorem B3374873 : Blo 1498069 3374873 := bstep (se 2 (by rfl) ⟨1265577, by rfl⟩ : syracuseStep 3374873 = 2531155) B2531155
theorem B1498923 : Blo 1498069 1498923 := bstep (se 1 (by rfl) ⟨1124192, by rfl⟩ : syracuseStep 1498923 = 2248385) B2248385
theorem B1498935 : Blo 1498069 1498935 := bstep (se 1 (by rfl) ⟨1124201, by rfl⟩ : syracuseStep 1498935 = 2248403) B2248403
theorem B1687351 : Blo 1498069 1687351 := bstep (se 1 (by rfl) ⟨1265513, by rfl⟩ : syracuseStep 1687351 = 2531027) B2531027
theorem B34602817 : Blo 1498069 34602817 := bstep (se 2 (by rfl) ⟨12976056, by rfl⟩ : syracuseStep 34602817 = 25952113) B25952113
theorem B1498955 : Blo 1498069 1498955 := bstep (se 1 (by rfl) ⟨1124216, by rfl⟩ : syracuseStep 1498955 = 2248433) B2248433
theorem B1498967 : Blo 1498069 1498967 := bstep (se 1 (by rfl) ⟨1124225, by rfl⟩ : syracuseStep 1498967 = 2248451) B2248451
theorem B1802071 : Blo 1498069 1802071 := bstep (se 1 (by rfl) ⟨1351553, by rfl⟩ : syracuseStep 1802071 = 2703107) B2703107
theorem B1498987 : Blo 1498069 1498987 := bstep (se 1 (by rfl) ⟨1124240, by rfl⟩ : syracuseStep 1498987 = 2248481) B2248481
theorem B3374963 : Blo 1498069 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B1498999 : Blo 1498069 1498999 := bstep (se 1 (by rfl) ⟨1124249, by rfl⟩ : syracuseStep 1498999 = 2248499) B2248499
theorem B1499019 : Blo 1498069 1499019 := bstep (se 1 (by rfl) ⟨1124264, by rfl⟩ : syracuseStep 1499019 = 2248529) B2248529
theorem B1499031 : Blo 1498069 1499031 := bstep (se 1 (by rfl) ⟨1124273, by rfl⟩ : syracuseStep 1499031 = 2248547) B2248547
theorem B3374999 : Blo 1498069 3374999 := bstep (se 1 (by rfl) ⟨2531249, by rfl⟩ : syracuseStep 3374999 = 5062499) B5062499
theorem B2432921 : Blo 1498069 2432921 := bstep (se 2 (by rfl) ⟨912345, by rfl⟩ : syracuseStep 2432921 = 1824691) B1824691
theorem B1499051 : Blo 1498069 1499051 := bstep (se 1 (by rfl) ⟨1124288, by rfl⟩ : syracuseStep 1499051 = 2248577) B2248577
theorem B1499063 : Blo 1498069 1499063 := bstep (se 1 (by rfl) ⟨1124297, by rfl⟩ : syracuseStep 1499063 = 2248595) B2248595
theorem B1499083 : Blo 1498069 1499083 := bstep (se 1 (by rfl) ⟨1124312, by rfl⟩ : syracuseStep 1499083 = 2248625) B2248625
theorem B1499095 : Blo 1498069 1499095 := bstep (se 1 (by rfl) ⟨1124321, by rfl⟩ : syracuseStep 1499095 = 2248643) B2248643
theorem B1499115 : Blo 1498069 1499115 := bstep (se 1 (by rfl) ⟨1124336, by rfl⟩ : syracuseStep 1499115 = 2248673) B2248673
theorem B1687531 : Blo 1498069 1687531 := bstep (se 1 (by rfl) ⟨1265648, by rfl⟩ : syracuseStep 1687531 = 2531297) B2531297
theorem B3203059 : Blo 1498069 3203059 := bstep (se 1 (by rfl) ⟨2402294, by rfl⟩ : syracuseStep 3203059 = 4804589) B4804589
theorem B1499127 : Blo 1498069 1499127 := bstep (se 1 (by rfl) ⟨1124345, by rfl⟩ : syracuseStep 1499127 = 2248691) B2248691
theorem B1499143 : Blo 1498069 1499143 := bstep (se 1 (by rfl) ⟨1124357, by rfl⟩ : syracuseStep 1499143 = 2248715) B2248715
theorem B1499151 : Blo 1498069 1499151 := bstep (se 1 (by rfl) ⟨1124363, by rfl⟩ : syracuseStep 1499151 = 2248727) B2248727
theorem B1687567 : Blo 1498069 1687567 := bstep (se 1 (by rfl) ⟨1265675, by rfl⟩ : syracuseStep 1687567 = 2531351) B2531351
theorem B1499195 : Blo 1498069 1499195 := bstep (se 1 (by rfl) ⟨1124396, by rfl⟩ : syracuseStep 1499195 = 2248793) B2248793
theorem B1499271 : Blo 1498069 1499271 := bstep (se 1 (by rfl) ⟨1124453, by rfl⟩ : syracuseStep 1499271 = 2248907) B2248907
theorem B1499279 : Blo 1498069 1499279 := bstep (se 1 (by rfl) ⟨1124459, by rfl⟩ : syracuseStep 1499279 = 2248919) B2248919
theorem B1499323 : Blo 1498069 1499323 := bstep (se 1 (by rfl) ⟨1124492, by rfl⟩ : syracuseStep 1499323 = 2248985) B2248985
theorem B1499399 : Blo 1498069 1499399 := bstep (se 1 (by rfl) ⟨1124549, by rfl⟩ : syracuseStep 1499399 = 2249099) B2249099
theorem B3039503 : Blo 1498069 3039503 := bstep (se 1 (by rfl) ⟨2279627, by rfl⟩ : syracuseStep 3039503 = 4559255) B4559255
theorem B1499407 : Blo 1498069 1499407 := bstep (se 1 (by rfl) ⟨1124555, by rfl⟩ : syracuseStep 1499407 = 2249111) B2249111
theorem B28811537 : Blo 1498069 28811537 := bstep (se 2 (by rfl) ⟨10804326, by rfl⟩ : syracuseStep 28811537 = 21608653) B21608653
theorem B7201057 : Blo 1498069 7201057 := bstep (se 2 (by rfl) ⟨2700396, by rfl⟩ : syracuseStep 7201057 = 5400793) B5400793
theorem B1499451 : Blo 1498069 1499451 := bstep (se 1 (by rfl) ⟨1124588, by rfl⟩ : syracuseStep 1499451 = 2249177) B2249177
theorem B12976519 : Blo 1498069 12976519 := bstep (se 1 (by rfl) ⟨9732389, by rfl⟩ : syracuseStep 12976519 = 19464779) B19464779
theorem B1499527 : Blo 1498069 1499527 := bstep (se 1 (by rfl) ⟨1124645, by rfl⟩ : syracuseStep 1499527 = 2249291) B2249291
theorem B1540495 : Blo 1498069 1540495 := bstep (se 1 (by rfl) ⟨1155371, by rfl⟩ : syracuseStep 1540495 = 2310743) B2310743
theorem B1499535 : Blo 1498069 1499535 := bstep (se 1 (by rfl) ⟨1124651, by rfl⟩ : syracuseStep 1499535 = 2249303) B2249303
theorem B9118099 : Blo 1498069 9118099 := bstep (se 1 (by rfl) ⟨6838574, by rfl⟩ : syracuseStep 9118099 = 13677149) B13677149
theorem B1499579 : Blo 1498069 1499579 := bstep (se 1 (by rfl) ⟨1124684, by rfl⟩ : syracuseStep 1499579 = 2249369) B2249369
theorem B11379203 : Blo 1498069 11379203 := bstep (se 1 (by rfl) ⟨8534402, by rfl⟩ : syracuseStep 11379203 = 17068805) B17068805
theorem B16032259 : Blo 1498069 16032259 := bstep (se 1 (by rfl) ⟨12024194, by rfl⟩ : syracuseStep 16032259 = 24048389) B24048389
theorem B1499655 : Blo 1498069 1499655 := bstep (se 1 (by rfl) ⟨1124741, by rfl⟩ : syracuseStep 1499655 = 2249483) B2249483
theorem B1499663 : Blo 1498069 1499663 := bstep (se 1 (by rfl) ⟨1124747, by rfl⟩ : syracuseStep 1499663 = 2249495) B2249495
theorem B1499707 : Blo 1498069 1499707 := bstep (se 1 (by rfl) ⟨1124780, by rfl⟩ : syracuseStep 1499707 = 2249561) B2249561
theorem B1499783 : Blo 1498069 1499783 := bstep (se 1 (by rfl) ⟨1124837, by rfl⟩ : syracuseStep 1499783 = 2249675) B2249675
theorem B1499791 : Blo 1498069 1499791 := bstep (se 1 (by rfl) ⟨1124843, by rfl⟩ : syracuseStep 1499791 = 2249687) B2249687
theorem B1499835 : Blo 1498069 1499835 := bstep (se 1 (by rfl) ⟨1124876, by rfl⟩ : syracuseStep 1499835 = 2249753) B2249753
theorem B1499911 : Blo 1498069 1499911 := bstep (se 1 (by rfl) ⟨1124933, by rfl⟩ : syracuseStep 1499911 = 2249867) B2249867
theorem B3793675 : Blo 1498069 3793675 := bstep (se 1 (by rfl) ⟨2845256, by rfl⟩ : syracuseStep 3793675 = 5690513) B5690513
theorem B1499919 : Blo 1498069 1499919 := bstep (se 1 (by rfl) ⟨1124939, by rfl⟩ : syracuseStep 1499919 = 2249879) B2249879
theorem B1499963 : Blo 1498069 1499963 := bstep (se 1 (by rfl) ⟨1124972, by rfl⟩ : syracuseStep 1499963 = 2249945) B2249945
theorem B9610073 : Blo 1498069 9610073 := bstep (se 2 (by rfl) ⟨3603777, by rfl⟩ : syracuseStep 9610073 = 7207555) B7207555
theorem B1500039 : Blo 1498069 1500039 := bstep (se 1 (by rfl) ⟨1125029, by rfl⟩ : syracuseStep 1500039 = 2250059) B2250059
theorem B1500047 : Blo 1498069 1500047 := bstep (se 1 (by rfl) ⟨1125035, by rfl⟩ : syracuseStep 1500047 = 2250071) B2250071
theorem B3793817 : Blo 1498069 3793817 := bstep (se 2 (by rfl) ⟨1422681, by rfl⟩ : syracuseStep 3793817 = 2845363) B2845363
theorem B34612229 : Blo 1498069 34612229 := bstep (se 4 (by rfl) ⟨3244896, by rfl⟩ : syracuseStep 34612229 = 6489793) B6489793
theorem B3802145 : Blo 1498069 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B3793979 : Blo 1498069 3793979 := bstep (se 1 (by rfl) ⟨2845484, by rfl⟩ : syracuseStep 3793979 = 5690969) B5690969
theorem B4269115 : Blo 1498069 4269115 := bstep (se 1 (by rfl) ⟨3201836, by rfl⟩ : syracuseStep 4269115 = 6403673) B6403673
theorem B8651863 : Blo 1498069 8651863 := bstep (se 1 (by rfl) ⟨6488897, by rfl⟩ : syracuseStep 8651863 = 12977795) B12977795
theorem B5694583 : Blo 1498069 5694583 := bstep (se 1 (by rfl) ⟨4270937, by rfl⟩ : syracuseStep 5694583 = 8541875) B8541875
theorem B3245447 : Blo 1498069 3245447 := bstep (se 1 (by rfl) ⟨2434085, by rfl⟩ : syracuseStep 3245447 = 4868171) B4868171
theorem B3794323 : Blo 1498069 3794323 := bstep (se 1 (by rfl) ⟨2845742, by rfl⟩ : syracuseStep 3794323 = 5691485) B5691485
theorem B3794465 : Blo 1498069 3794465 := bstep (se 2 (by rfl) ⟨1422924, by rfl⟩ : syracuseStep 3794465 = 2845849) B2845849
theorem B6399607 : Blo 1498069 6399607 := bstep (se 1 (by rfl) ⟨4799705, by rfl⟩ : syracuseStep 6399607 = 9599411) B9599411
theorem B5056289 : Blo 1498069 5056289 := bstep (se 2 (by rfl) ⟨1896108, by rfl⟩ : syracuseStep 5056289 = 3792217) B3792217
theorem B9611045 : Blo 1498069 9611045 := bstep (se 4 (by rfl) ⟨901035, by rfl⟩ : syracuseStep 9611045 = 1802071) B1802071
theorem B2279287 : Blo 1498069 2279287 := bstep (se 1 (by rfl) ⟨1709465, by rfl⟩ : syracuseStep 2279287 = 3418931) B3418931
theorem B2844551 : Blo 1498069 2844551 := bstep (se 1 (by rfl) ⟨2133413, by rfl⟩ : syracuseStep 2844551 = 4266827) B4266827
theorem B4269959 : Blo 1498069 4269959 := bstep (se 1 (by rfl) ⟨3202469, by rfl⟩ : syracuseStep 4269959 = 6404939) B6404939
theorem B8652691 : Blo 1498069 8652691 := bstep (se 1 (by rfl) ⟨6489518, by rfl⟩ : syracuseStep 8652691 = 12979037) B12979037
theorem B8103959 : Blo 1498069 8103959 := bstep (se 1 (by rfl) ⟨6077969, by rfl⟩ : syracuseStep 8103959 = 12155939) B12155939
theorem B5695555 : Blo 1498069 5695555 := bstep (se 1 (by rfl) ⟨4271666, by rfl⟩ : syracuseStep 5695555 = 8543333) B8543333
theorem B21604553 : Blo 1498069 21604553 := bstep (se 2 (by rfl) ⟨8101707, by rfl⟩ : syracuseStep 21604553 = 16203415) B16203415
theorem B11536673 : Blo 1498069 11536673 := bstep (se 2 (by rfl) ⟨4326252, by rfl⟩ : syracuseStep 11536673 = 8652505) B8652505
theorem B46803253 : Blo 1498069 46803253 := bstep (se 5 (by rfl) ⟨2193902, by rfl⟩ : syracuseStep 46803253 = 4387805) B4387805
theorem B5056883 : Blo 1498069 5056883 := bstep (se 1 (by rfl) ⟨3792662, by rfl⟩ : syracuseStep 5056883 = 7585325) B7585325
theorem B3418487 : Blo 1498069 3418487 := bstep (se 1 (by rfl) ⟨2563865, by rfl⟩ : syracuseStep 3418487 = 5127731) B5127731
theorem B7588241 : Blo 1498069 7588241 := bstep (se 2 (by rfl) ⟨2845590, by rfl⟩ : syracuseStep 7588241 = 5691181) B5691181
theorem B2247113 : Blo 1498069 2247113 := bstep (se 2 (by rfl) ⟨842667, by rfl⟩ : syracuseStep 2247113 = 1685335) B1685335
theorem B17074637 : Blo 1498069 17074637 := bstep (se 3 (by rfl) ⟨3201494, by rfl⟩ : syracuseStep 17074637 = 6402989) B6402989
theorem B3795457 : Blo 1498069 3795457 := bstep (se 2 (by rfl) ⟨1423296, by rfl⟩ : syracuseStep 3795457 = 2846593) B2846593
theorem B2247227 : Blo 1498069 2247227 := bstep (se 1 (by rfl) ⟨1685420, by rfl⟩ : syracuseStep 2247227 = 3370841) B3370841
theorem B2247287 : Blo 1498069 2247287 := bstep (se 1 (by rfl) ⟨1685465, by rfl⟩ : syracuseStep 2247287 = 3370931) B3370931
theorem B2247311 : Blo 1498069 2247311 := bstep (se 1 (by rfl) ⟨1685483, by rfl⟩ : syracuseStep 2247311 = 3370967) B3370967
theorem B4270745 : Blo 1498069 4270745 := bstep (se 2 (by rfl) ⟨1601529, by rfl⟩ : syracuseStep 4270745 = 3203059) B3203059
theorem B2247353 : Blo 1498069 2247353 := bstep (se 2 (by rfl) ⟨842757, by rfl⟩ : syracuseStep 2247353 = 1685515) B1685515
theorem B2247431 : Blo 1498069 2247431 := bstep (se 1 (by rfl) ⟨1685573, by rfl⟩ : syracuseStep 2247431 = 3371147) B3371147
theorem B2247467 : Blo 1498069 2247467 := bstep (se 1 (by rfl) ⟨1685600, by rfl⟩ : syracuseStep 2247467 = 3371201) B3371201
theorem B2247497 : Blo 1498069 2247497 := bstep (se 2 (by rfl) ⟨842811, by rfl⟩ : syracuseStep 2247497 = 1685623) B1685623
theorem B2247611 : Blo 1498069 2247611 := bstep (se 1 (by rfl) ⟨1685708, by rfl⟩ : syracuseStep 2247611 = 3371417) B3371417
theorem B2247671 : Blo 1498069 2247671 := bstep (se 1 (by rfl) ⟨1685753, by rfl⟩ : syracuseStep 2247671 = 3371507) B3371507
theorem B2280455 : Blo 1498069 2280455 := bstep (se 1 (by rfl) ⟨1710341, by rfl⟩ : syracuseStep 2280455 = 3420683) B3420683
theorem B8219659 : Blo 1498069 8219659 := bstep (se 1 (by rfl) ⟨6164744, by rfl⟩ : syracuseStep 8219659 = 12329489) B12329489
theorem B2247695 : Blo 1498069 2247695 := bstep (se 1 (by rfl) ⟨1685771, by rfl⟩ : syracuseStep 2247695 = 3371543) B3371543
theorem B2133049 : Blo 1498069 2133049 := bstep (se 2 (by rfl) ⟨799893, by rfl⟩ : syracuseStep 2133049 = 1599787) B1599787
theorem B2247737 : Blo 1498069 2247737 := bstep (se 2 (by rfl) ⟨842901, by rfl⟩ : syracuseStep 2247737 = 1685803) B1685803
theorem B3796055 : Blo 1498069 3796055 := bstep (se 1 (by rfl) ⟨2847041, by rfl⟩ : syracuseStep 3796055 = 5694083) B5694083
theorem B2247815 : Blo 1498069 2247815 := bstep (se 1 (by rfl) ⟨1685861, by rfl⟩ : syracuseStep 2247815 = 3371723) B3371723
theorem B2247851 : Blo 1498069 2247851 := bstep (se 1 (by rfl) ⟨1685888, by rfl⟩ : syracuseStep 2247851 = 3371777) B3371777
theorem B9112769 : Blo 1498069 9112769 := bstep (se 2 (by rfl) ⟨3417288, by rfl⟩ : syracuseStep 9112769 = 6834577) B6834577
theorem B2247881 : Blo 1498069 2247881 := bstep (se 2 (by rfl) ⟨842955, by rfl⟩ : syracuseStep 2247881 = 1685911) B1685911
theorem B6401281 : Blo 1498069 6401281 := bstep (se 2 (by rfl) ⟨2400480, by rfl⟩ : syracuseStep 6401281 = 4800961) B4800961
theorem B4271393 : Blo 1498069 4271393 := bstep (se 2 (by rfl) ⟨1601772, by rfl⟩ : syracuseStep 4271393 = 3203545) B3203545
theorem B3419435 : Blo 1498069 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B3796267 : Blo 1498069 3796267 := bstep (se 1 (by rfl) ⟨2847200, by rfl⟩ : syracuseStep 3796267 = 5694401) B5694401
theorem B2247995 : Blo 1498069 2247995 := bstep (se 1 (by rfl) ⟨1685996, by rfl⟩ : syracuseStep 2247995 = 3371993) B3371993
theorem B7204211 : Blo 1498069 7204211 := bstep (se 1 (by rfl) ⟨5403158, by rfl⟩ : syracuseStep 7204211 = 10806317) B10806317
theorem B2248055 : Blo 1498069 2248055 := bstep (se 1 (by rfl) ⟨1686041, by rfl⟩ : syracuseStep 2248055 = 3372083) B3372083
theorem B2248079 : Blo 1498069 2248079 := bstep (se 1 (by rfl) ⟨1686059, by rfl⟩ : syracuseStep 2248079 = 3372119) B3372119
theorem B12799417 : Blo 1498069 12799417 := bstep (se 2 (by rfl) ⟨4799781, by rfl⟩ : syracuseStep 12799417 = 9599563) B9599563
theorem B2248121 : Blo 1498069 2248121 := bstep (se 2 (by rfl) ⟨843045, by rfl⟩ : syracuseStep 2248121 = 1686091) B1686091
theorem B3796409 : Blo 1498069 3796409 := bstep (se 2 (by rfl) ⟨1423653, by rfl⟩ : syracuseStep 3796409 = 2847307) B2847307
theorem B2846153 : Blo 1498069 2846153 := bstep (se 2 (by rfl) ⟨1067307, by rfl⟩ : syracuseStep 2846153 = 2134615) B2134615
theorem B2248199 : Blo 1498069 2248199 := bstep (se 1 (by rfl) ⟨1686149, by rfl⟩ : syracuseStep 2248199 = 3372299) B3372299
theorem B3599905 : Blo 1498069 3599905 := bstep (se 2 (by rfl) ⟨1349964, by rfl⟩ : syracuseStep 3599905 = 2699929) B2699929
theorem B2248235 : Blo 1498069 2248235 := bstep (se 1 (by rfl) ⟨1686176, by rfl⟩ : syracuseStep 2248235 = 3372353) B3372353
theorem B5197355 : Blo 1498069 5197355 := bstep (se 1 (by rfl) ⟨3898016, by rfl⟩ : syracuseStep 5197355 = 7796033) B7796033
theorem B2248265 : Blo 1498069 2248265 := bstep (se 2 (by rfl) ⟨843099, by rfl⟩ : syracuseStep 2248265 = 1686199) B1686199
theorem B2248379 : Blo 1498069 2248379 := bstep (se 1 (by rfl) ⟨1686284, by rfl⟩ : syracuseStep 2248379 = 3372569) B3372569
theorem B3370697 : Blo 1498069 3370697 := bstep (se 2 (by rfl) ⟨1264011, by rfl⟩ : syracuseStep 3370697 = 2528023) B2528023
theorem B2248439 : Blo 1498069 2248439 := bstep (se 1 (by rfl) ⟨1686329, by rfl⟩ : syracuseStep 2248439 = 3372659) B3372659
theorem B2248463 : Blo 1498069 2248463 := bstep (se 1 (by rfl) ⟨1686347, by rfl⟩ : syracuseStep 2248463 = 3372695) B3372695
theorem B2248505 : Blo 1498069 2248505 := bstep (se 2 (by rfl) ⟨843189, by rfl⟩ : syracuseStep 2248505 = 1686379) B1686379
theorem B1896311 : Blo 1498069 1896311 := bstep (se 1 (by rfl) ⟨1422233, by rfl⟩ : syracuseStep 1896311 = 2844467) B2844467
theorem B5689223 : Blo 1498069 5689223 := bstep (se 1 (by rfl) ⟨4266917, by rfl⟩ : syracuseStep 5689223 = 8533835) B8533835
theorem B2248583 : Blo 1498069 2248583 := bstep (se 1 (by rfl) ⟨1686437, by rfl⟩ : syracuseStep 2248583 = 3372875) B3372875
theorem B41013145 : Blo 1498069 41013145 := bstep (se 2 (by rfl) ⟨15379929, by rfl⟩ : syracuseStep 41013145 = 30759859) B30759859
theorem B2248619 : Blo 1498069 2248619 := bstep (se 1 (by rfl) ⟨1686464, by rfl⟩ : syracuseStep 2248619 = 3372929) B3372929
theorem B2248649 : Blo 1498069 2248649 := bstep (se 2 (by rfl) ⟨843243, by rfl⟩ : syracuseStep 2248649 = 1686487) B1686487
theorem B1896463 : Blo 1498069 1896463 := bstep (se 1 (by rfl) ⟨1422347, by rfl⟩ : syracuseStep 1896463 = 2844695) B2844695
theorem B29192237 : Blo 1498069 29192237 := bstep (se 3 (by rfl) ⟨5473544, by rfl⟩ : syracuseStep 29192237 = 10947089) B10947089
theorem B2248763 : Blo 1498069 2248763 := bstep (se 1 (by rfl) ⟨1686572, by rfl⟩ : syracuseStep 2248763 = 3373145) B3373145
theorem B4108403 : Blo 1498069 4108403 := bstep (se 1 (by rfl) ⟨3081302, by rfl⟩ : syracuseStep 4108403 = 6162605) B6162605
theorem B2248823 : Blo 1498069 2248823 := bstep (se 1 (by rfl) ⟨1686617, by rfl⟩ : syracuseStep 2248823 = 3373235) B3373235
theorem B2248847 : Blo 1498069 2248847 := bstep (se 1 (by rfl) ⟨1686635, by rfl⟩ : syracuseStep 2248847 = 3373271) B3373271
theorem B10956973 : Blo 1498069 10956973 := bstep (se 3 (by rfl) ⟨2054432, by rfl⟩ : syracuseStep 10956973 = 4108865) B4108865
theorem B2248889 : Blo 1498069 2248889 := bstep (se 2 (by rfl) ⟨843333, by rfl⟩ : syracuseStep 2248889 = 1686667) B1686667
theorem B1896635 : Blo 1498069 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B7205057 : Blo 1498069 7205057 := bstep (se 2 (by rfl) ⟨2701896, by rfl⟩ : syracuseStep 7205057 = 5403793) B5403793
theorem B8540417 : Blo 1498069 8540417 := bstep (se 2 (by rfl) ⟨3202656, by rfl⟩ : syracuseStep 8540417 = 6405313) B6405313
theorem B2134279 : Blo 1498069 2134279 := bstep (se 1 (by rfl) ⟨1600709, by rfl⟩ : syracuseStep 2134279 = 3201419) B3201419
theorem B2248967 : Blo 1498069 2248967 := bstep (se 1 (by rfl) ⟨1686725, by rfl⟩ : syracuseStep 2248967 = 3373451) B3373451
theorem B3600683 : Blo 1498069 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B2249003 : Blo 1498069 2249003 := bstep (se 1 (by rfl) ⟨1686752, by rfl⟩ : syracuseStep 2249003 = 3373505) B3373505
theorem B4329787 : Blo 1498069 4329787 := bstep (se 1 (by rfl) ⟨3247340, by rfl⟩ : syracuseStep 4329787 = 6494681) B6494681
theorem B2249033 : Blo 1498069 2249033 := bstep (se 2 (by rfl) ⟨843387, by rfl⟩ : syracuseStep 2249033 = 1686775) B1686775
theorem B3371399 : Blo 1498069 3371399 := bstep (se 1 (by rfl) ⟨2528549, by rfl⟩ : syracuseStep 3371399 = 5057099) B5057099
theorem B8532377 : Blo 1498069 8532377 := bstep (se 2 (by rfl) ⟨3199641, by rfl⟩ : syracuseStep 8532377 = 6399283) B6399283
theorem B2699705 : Blo 1498069 2699705 := bstep (se 2 (by rfl) ⟨1012389, by rfl⟩ : syracuseStep 2699705 = 2024779) B2024779
theorem B15380921 : Blo 1498069 15380921 := bstep (se 2 (by rfl) ⟨5767845, by rfl⟩ : syracuseStep 15380921 = 11535691) B11535691
theorem B2249147 : Blo 1498069 2249147 := bstep (se 1 (by rfl) ⟨1686860, by rfl⟩ : syracuseStep 2249147 = 3373721) B3373721
theorem B8106425 : Blo 1498069 8106425 := bstep (se 2 (by rfl) ⟨3039909, by rfl⟩ : syracuseStep 8106425 = 6079819) B6079819
theorem B7590347 : Blo 1498069 7590347 := bstep (se 1 (by rfl) ⟨5692760, by rfl⟩ : syracuseStep 7590347 = 11385521) B11385521
theorem B19468765 : Blo 1498069 19468765 := bstep (se 3 (by rfl) ⟨3650393, by rfl⟩ : syracuseStep 19468765 = 7300787) B7300787
theorem B2249207 : Blo 1498069 2249207 := bstep (se 1 (by rfl) ⟨1686905, by rfl⟩ : syracuseStep 2249207 = 3373811) B3373811
theorem B2249231 : Blo 1498069 2249231 := bstep (se 1 (by rfl) ⟨1686923, by rfl⟩ : syracuseStep 2249231 = 3373847) B3373847
theorem B2249273 : Blo 1498069 2249273 := bstep (se 2 (by rfl) ⟨843477, by rfl⟩ : syracuseStep 2249273 = 1686955) B1686955
theorem B3199547 : Blo 1498069 3199547 := bstep (se 1 (by rfl) ⟨2399660, by rfl⟩ : syracuseStep 3199547 = 4799321) B4799321
theorem B3371579 : Blo 1498069 3371579 := bstep (se 1 (by rfl) ⟨2528684, by rfl⟩ : syracuseStep 3371579 = 5057369) B5057369
theorem B3846791 : Blo 1498069 3846791 := bstep (se 1 (by rfl) ⟨2885093, by rfl⟩ : syracuseStep 3846791 = 5770187) B5770187
theorem B2249351 : Blo 1498069 2249351 := bstep (se 1 (by rfl) ⟨1687013, by rfl⟩ : syracuseStep 2249351 = 3374027) B3374027
theorem B2249387 : Blo 1498069 2249387 := bstep (se 1 (by rfl) ⟨1687040, by rfl⟩ : syracuseStep 2249387 = 3374081) B3374081
theorem B3371705 : Blo 1498069 3371705 := bstep (se 2 (by rfl) ⟨1264389, by rfl⟩ : syracuseStep 3371705 = 2528779) B2528779
theorem B2249417 : Blo 1498069 2249417 := bstep (se 2 (by rfl) ⟨843531, by rfl⟩ : syracuseStep 2249417 = 1687063) B1687063
theorem B8540873 : Blo 1498069 8540873 := bstep (se 2 (by rfl) ⟨3202827, by rfl⟩ : syracuseStep 8540873 = 6405655) B6405655
theorem B7590671 : Blo 1498069 7590671 := bstep (se 1 (by rfl) ⟨5693003, by rfl⟩ : syracuseStep 7590671 = 11386007) B11386007
theorem B2249531 : Blo 1498069 2249531 := bstep (se 1 (by rfl) ⟨1687148, by rfl⟩ : syracuseStep 2249531 = 3374297) B3374297
theorem B2249591 : Blo 1498069 2249591 := bstep (se 1 (by rfl) ⟨1687193, by rfl⟩ : syracuseStep 2249591 = 3374387) B3374387
theorem B2249615 : Blo 1498069 2249615 := bstep (se 1 (by rfl) ⟨1687211, by rfl⟩ : syracuseStep 2249615 = 3374423) B3374423
theorem B5059475 : Blo 1498069 5059475 := bstep (se 1 (by rfl) ⟨3794606, by rfl⟩ : syracuseStep 5059475 = 7589213) B7589213
theorem B12809123 : Blo 1498069 12809123 := bstep (se 1 (by rfl) ⟨9606842, by rfl⟩ : syracuseStep 12809123 = 19213685) B19213685
theorem B2528185 : Blo 1498069 2528185 := bstep (se 2 (by rfl) ⟨948069, by rfl⟩ : syracuseStep 2528185 = 1896139) B1896139
theorem B2249657 : Blo 1498069 2249657 := bstep (se 2 (by rfl) ⟨843621, by rfl⟩ : syracuseStep 2249657 = 1687243) B1687243
theorem B1708987 : Blo 1498069 1708987 := bstep (se 1 (by rfl) ⟨1281740, by rfl⟩ : syracuseStep 1708987 = 2563481) B2563481
theorem B2249735 : Blo 1498069 2249735 := bstep (se 1 (by rfl) ⟨1687301, by rfl⟩ : syracuseStep 2249735 = 3374603) B3374603
theorem B3372047 : Blo 1498069 3372047 := bstep (se 1 (by rfl) ⟨2529035, by rfl⟩ : syracuseStep 3372047 = 5058071) B5058071
theorem B3372065 : Blo 1498069 3372065 := bstep (se 2 (by rfl) ⟨1264524, by rfl⟩ : syracuseStep 3372065 = 2529049) B2529049
theorem B2249771 : Blo 1498069 2249771 := bstep (se 1 (by rfl) ⟨1687328, by rfl⟩ : syracuseStep 2249771 = 3374657) B3374657
theorem B2135099 : Blo 1498069 2135099 := bstep (se 1 (by rfl) ⟨1601324, by rfl⟩ : syracuseStep 2135099 = 3202649) B3202649
theorem B2249801 : Blo 1498069 2249801 := bstep (se 2 (by rfl) ⟨843675, by rfl⟩ : syracuseStep 2249801 = 1687351) B1687351
theorem B109335683 : Blo 1498069 109335683 := bstep (se 1 (by rfl) ⟨82001762, by rfl⟩ : syracuseStep 109335683 = 164003525) B164003525
theorem B1897607 : Blo 1498069 1897607 := bstep (se 1 (by rfl) ⟨1423205, by rfl⟩ : syracuseStep 1897607 = 2846411) B2846411
theorem B2249915 : Blo 1498069 2249915 := bstep (se 1 (by rfl) ⟨1687436, by rfl⟩ : syracuseStep 2249915 = 3374873) B3374873
theorem B2249975 : Blo 1498069 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B2249999 : Blo 1498069 2249999 := bstep (se 1 (by rfl) ⟨1687499, by rfl⟩ : syracuseStep 2249999 = 3374999) B3374999
theorem B2250041 : Blo 1498069 2250041 := bstep (se 2 (by rfl) ⟨843765, by rfl⟩ : syracuseStep 2250041 = 1687531) B1687531
theorem B4109629 : Blo 1498069 4109629 := bstep (se 3 (by rfl) ⟨770555, by rfl⟩ : syracuseStep 4109629 = 1541111) B1541111
theorem B3372407 : Blo 1498069 3372407 := bstep (se 1 (by rfl) ⟨2529305, by rfl⟩ : syracuseStep 3372407 = 5058611) B5058611
theorem B3372587 : Blo 1498069 3372587 := bstep (se 1 (by rfl) ⟨2529440, by rfl⟩ : syracuseStep 3372587 = 5058881) B5058881
theorem B2528887 : Blo 1498069 2528887 := bstep (se 1 (by rfl) ⟨1896665, by rfl⟩ : syracuseStep 2528887 = 3793331) B3793331
theorem B5690999 : Blo 1498069 5690999 := bstep (se 1 (by rfl) ⟨4268249, by rfl⟩ : syracuseStep 5690999 = 8536499) B8536499
theorem B2135737 : Blo 1498069 2135737 := bstep (se 2 (by rfl) ⟨800901, by rfl⟩ : syracuseStep 2135737 = 1601803) B1601803
theorem B11384549 : Blo 1498069 11384549 := bstep (se 4 (by rfl) ⟨1067301, by rfl⟩ : syracuseStep 11384549 = 2134603) B2134603
theorem B7206671 : Blo 1498069 7206671 := bstep (se 1 (by rfl) ⟨5405003, by rfl⟩ : syracuseStep 7206671 = 10810007) B10810007
theorem B1898255 : Blo 1498069 1898255 := bstep (se 1 (by rfl) ⟨1423691, by rfl⟩ : syracuseStep 1898255 = 2847383) B2847383
theorem B2529083 : Blo 1498069 2529083 := bstep (se 1 (by rfl) ⟨1896812, by rfl⟩ : syracuseStep 2529083 = 3793625) B3793625
theorem B1824631 : Blo 1498069 1824631 := bstep (se 1 (by rfl) ⟨1368473, by rfl⟩ : syracuseStep 1824631 = 2736947) B2736947
theorem B6838151 : Blo 1498069 6838151 := bstep (se 1 (by rfl) ⟨5128613, by rfl⟩ : syracuseStep 6838151 = 10257227) B10257227
theorem B3372947 : Blo 1498069 3372947 := bstep (se 1 (by rfl) ⟨2529710, by rfl⟩ : syracuseStep 3372947 = 5059421) B5059421
theorem B4052921 : Blo 1498069 4052921 := bstep (se 2 (by rfl) ⟨1519845, by rfl⟩ : syracuseStep 4052921 = 3039691) B3039691
theorem B3373001 : Blo 1498069 3373001 := bstep (se 2 (by rfl) ⟨1264875, by rfl⟩ : syracuseStep 3373001 = 2529751) B2529751
theorem B8099851 : Blo 1498069 8099851 := bstep (se 1 (by rfl) ⟨6074888, by rfl⟩ : syracuseStep 8099851 = 12149777) B12149777
theorem B6838283 : Blo 1498069 6838283 := bstep (se 1 (by rfl) ⟨5128712, by rfl⟩ : syracuseStep 6838283 = 10257425) B10257425
theorem B4053007 : Blo 1498069 4053007 := bstep (se 1 (by rfl) ⟨3039755, by rfl⟩ : syracuseStep 4053007 = 6079511) B6079511
theorem B4266017 : Blo 1498069 4266017 := bstep (se 2 (by rfl) ⟨1599756, by rfl⟩ : syracuseStep 4266017 = 3199513) B3199513
theorem B5404715 : Blo 1498069 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B11376773 : Blo 1498069 11376773 := bstep (se 4 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 11376773 = 2133145) B2133145
theorem B3037331 : Blo 1498069 3037331 := bstep (se 1 (by rfl) ⟨2277998, by rfl⟩ : syracuseStep 3037331 = 4555997) B4555997
theorem B7592129 : Blo 1498069 7592129 := bstep (se 2 (by rfl) ⟨2847048, by rfl⟩ : syracuseStep 7592129 = 5694097) B5694097
theorem B2529481 : Blo 1498069 2529481 := bstep (se 2 (by rfl) ⟨948555, by rfl⟩ : syracuseStep 2529481 = 1897111) B1897111
theorem B16210165 : Blo 1498069 16210165 := bstep (se 5 (by rfl) ⟨759851, by rfl⟩ : syracuseStep 16210165 = 1519703) B1519703
theorem B1685767 : Blo 1498069 1685767 := bstep (se 1 (by rfl) ⟨1264325, by rfl⟩ : syracuseStep 1685767 = 2528651) B2528651
theorem B5060879 : Blo 1498069 5060879 := bstep (se 1 (by rfl) ⟨3795659, by rfl⟩ : syracuseStep 5060879 = 7591319) B7591319
theorem B1685947 : Blo 1498069 1685947 := bstep (se 1 (by rfl) ⟨1264460, by rfl⟩ : syracuseStep 1685947 = 2528921) B2528921
theorem B4053449 : Blo 1498069 4053449 := bstep (se 2 (by rfl) ⟨1520043, by rfl⟩ : syracuseStep 4053449 = 3040087) B3040087
theorem B5061149 : Blo 1498069 5061149 := bstep (se 3 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 5061149 = 1897931) B1897931
theorem B5691971 : Blo 1498069 5691971 := bstep (se 1 (by rfl) ⟨4268978, by rfl⟩ : syracuseStep 5691971 = 8537957) B8537957
theorem B3373703 : Blo 1498069 3373703 := bstep (se 1 (by rfl) ⟨2530277, by rfl⟩ : syracuseStep 3373703 = 5060555) B5060555
theorem B3373883 : Blo 1498069 3373883 := bstep (se 1 (by rfl) ⟨2530412, by rfl⟩ : syracuseStep 3373883 = 5060825) B5060825
theorem B2530183 : Blo 1498069 2530183 := bstep (se 1 (by rfl) ⟨1897637, by rfl⟩ : syracuseStep 2530183 = 3795275) B3795275
theorem B1686415 : Blo 1498069 1686415 := bstep (se 1 (by rfl) ⟨1264811, by rfl⟩ : syracuseStep 1686415 = 2529623) B2529623
theorem B3374009 : Blo 1498069 3374009 := bstep (se 2 (by rfl) ⟨1265253, by rfl⟩ : syracuseStep 3374009 = 2530507) B2530507
theorem B1498119 : Blo 1498069 1498119 := bstep (se 1 (by rfl) ⟨1123589, by rfl⟩ : syracuseStep 1498119 = 2247179) B2247179
theorem B4267019 : Blo 1498069 4267019 := bstep (se 1 (by rfl) ⟨3200264, by rfl⟩ : syracuseStep 4267019 = 6400529) B6400529
theorem B5692427 : Blo 1498069 5692427 := bstep (se 1 (by rfl) ⟨4269320, by rfl⟩ : syracuseStep 5692427 = 8538641) B8538641
theorem B1498127 : Blo 1498069 1498127 := bstep (se 1 (by rfl) ⟨1123595, by rfl⟩ : syracuseStep 1498127 = 2247191) B2247191
theorem B4054045 : Blo 1498069 4054045 := bstep (se 3 (by rfl) ⟨760133, by rfl⟩ : syracuseStep 4054045 = 1520267) B1520267
theorem B1498171 : Blo 1498069 1498171 := bstep (se 1 (by rfl) ⟨1123628, by rfl⟩ : syracuseStep 1498171 = 2247257) B2247257
theorem B1498247 : Blo 1498069 1498247 := bstep (se 1 (by rfl) ⟨1123685, by rfl⟩ : syracuseStep 1498247 = 2247371) B2247371
theorem B1498255 : Blo 1498069 1498255 := bstep (se 1 (by rfl) ⟨1123691, by rfl⟩ : syracuseStep 1498255 = 2247383) B2247383
theorem B1498299 : Blo 1498069 1498299 := bstep (se 1 (by rfl) ⟨1123724, by rfl⟩ : syracuseStep 1498299 = 2247449) B2247449
theorem B7199981 : Blo 1498069 7199981 := bstep (se 3 (by rfl) ⟨1349996, by rfl⟩ : syracuseStep 7199981 = 2699993) B2699993
theorem B1498375 : Blo 1498069 1498375 := bstep (se 1 (by rfl) ⟨1123781, by rfl⟩ : syracuseStep 1498375 = 2247563) B2247563
theorem B1498383 : Blo 1498069 1498383 := bstep (se 1 (by rfl) ⟨1123787, by rfl⟩ : syracuseStep 1498383 = 2247575) B2247575
theorem B3374351 : Blo 1498069 3374351 := bstep (se 1 (by rfl) ⟨2530763, by rfl⟩ : syracuseStep 3374351 = 5061527) B5061527
theorem B3374369 : Blo 1498069 3374369 := bstep (se 2 (by rfl) ⟨1265388, by rfl⟩ : syracuseStep 3374369 = 2530777) B2530777
theorem B1498427 : Blo 1498069 1498427 := bstep (se 1 (by rfl) ⟨1123820, by rfl⟩ : syracuseStep 1498427 = 2247641) B2247641
theorem B3603827 : Blo 1498069 3603827 := bstep (se 1 (by rfl) ⟨2702870, by rfl⟩ : syracuseStep 3603827 = 5405741) B5405741
theorem B4054391 : Blo 1498069 4054391 := bstep (se 1 (by rfl) ⟨3040793, by rfl⟩ : syracuseStep 4054391 = 6081587) B6081587
theorem B1498503 : Blo 1498069 1498503 := bstep (se 1 (by rfl) ⟨1123877, by rfl⟩ : syracuseStep 1498503 = 2247755) B2247755
theorem B1686919 : Blo 1498069 1686919 := bstep (se 1 (by rfl) ⟨1265189, by rfl⟩ : syracuseStep 1686919 = 2530379) B2530379
theorem B1498511 : Blo 1498069 1498511 := bstep (se 1 (by rfl) ⟨1123883, by rfl⟩ : syracuseStep 1498511 = 2247767) B2247767
theorem B30768569 : Blo 1498069 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B1498555 : Blo 1498069 1498555 := bstep (se 1 (by rfl) ⟨1123916, by rfl⟩ : syracuseStep 1498555 = 2247833) B2247833
theorem B3792329 : Blo 1498069 3792329 := bstep (se 2 (by rfl) ⟨1422123, by rfl⟩ : syracuseStep 3792329 = 2844247) B2844247
theorem B7593425 : Blo 1498069 7593425 := bstep (se 2 (by rfl) ⟨2847534, by rfl⟩ : syracuseStep 7593425 = 5695069) B5695069
theorem B1498631 : Blo 1498069 1498631 := bstep (se 1 (by rfl) ⟨1123973, by rfl⟩ : syracuseStep 1498631 = 2247947) B2247947
theorem B1498639 : Blo 1498069 1498639 := bstep (se 1 (by rfl) ⟨1123979, by rfl⟩ : syracuseStep 1498639 = 2247959) B2247959
theorem B2530831 : Blo 1498069 2530831 := bstep (se 1 (by rfl) ⟨1898123, by rfl⟩ : syracuseStep 2530831 = 3796247) B3796247
theorem B1498683 : Blo 1498069 1498683 := bstep (se 1 (by rfl) ⟨1124012, by rfl⟩ : syracuseStep 1498683 = 2248025) B2248025
theorem B1687099 : Blo 1498069 1687099 := bstep (se 1 (by rfl) ⟨1265324, by rfl⟩ : syracuseStep 1687099 = 2530649) B2530649
theorem B3374711 : Blo 1498069 3374711 := bstep (se 1 (by rfl) ⟨2531033, by rfl⟩ : syracuseStep 3374711 = 5062067) B5062067
theorem B1498759 : Blo 1498069 1498759 := bstep (se 1 (by rfl) ⟨1124069, by rfl⟩ : syracuseStep 1498759 = 2248139) B2248139
theorem B1498767 : Blo 1498069 1498767 := bstep (se 1 (by rfl) ⟨1124075, by rfl⟩ : syracuseStep 1498767 = 2248151) B2248151
theorem B8535725 : Blo 1498069 8535725 := bstep (se 3 (by rfl) ⟨1600448, by rfl⟩ : syracuseStep 8535725 = 3200897) B3200897
theorem B1498811 : Blo 1498069 1498811 := bstep (se 1 (by rfl) ⟨1124108, by rfl⟩ : syracuseStep 1498811 = 2248217) B2248217
theorem B6487789 : Blo 1498069 6487789 := bstep (se 3 (by rfl) ⟨1216460, by rfl⟩ : syracuseStep 6487789 = 2432921) B2432921
theorem B46137089 : Blo 1498069 46137089 := bstep (se 2 (by rfl) ⟨17301408, by rfl⟩ : syracuseStep 46137089 = 34602817) B34602817
theorem B1498887 : Blo 1498069 1498887 := bstep (se 1 (by rfl) ⟨1124165, by rfl⟩ : syracuseStep 1498887 = 2248331) B2248331
theorem B1498895 : Blo 1498069 1498895 := bstep (se 1 (by rfl) ⟨1124171, by rfl⟩ : syracuseStep 1498895 = 2248343) B2248343
theorem B13868815 : Blo 1498069 13868815 := bstep (se 1 (by rfl) ⟨10401611, by rfl⟩ : syracuseStep 13868815 = 20803223) B20803223
theorem B3792683 : Blo 1498069 3792683 := bstep (se 1 (by rfl) ⟨2844512, by rfl⟩ : syracuseStep 3792683 = 5689025) B5689025
theorem B3374891 : Blo 1498069 3374891 := bstep (se 1 (by rfl) ⟨2531168, by rfl⟩ : syracuseStep 3374891 = 5062337) B5062337
theorem B1498939 : Blo 1498069 1498939 := bstep (se 1 (by rfl) ⟨1124204, by rfl⟩ : syracuseStep 1498939 = 2248409) B2248409
theorem B11099993 : Blo 1498069 11099993 := bstep (se 2 (by rfl) ⟨4162497, by rfl⟩ : syracuseStep 11099993 = 8324995) B8324995
theorem B1499015 : Blo 1498069 1499015 := bstep (se 1 (by rfl) ⟨1124261, by rfl⟩ : syracuseStep 1499015 = 2248523) B2248523
theorem B1499023 : Blo 1498069 1499023 := bstep (se 1 (by rfl) ⟨1124267, by rfl⟩ : syracuseStep 1499023 = 2248535) B2248535
theorem B5062553 : Blo 1498069 5062553 := bstep (se 2 (by rfl) ⟨1898457, by rfl⟩ : syracuseStep 5062553 = 3796915) B3796915
theorem B1499067 : Blo 1498069 1499067 := bstep (se 1 (by rfl) ⟨1124300, by rfl⟩ : syracuseStep 1499067 = 2248601) B2248601
theorem B92299277 : Blo 1498069 92299277 := bstep (se 3 (by rfl) ⟨17306114, by rfl⟩ : syracuseStep 92299277 = 34612229) B34612229
theorem B11378717 : Blo 1498069 11378717 := bstep (se 3 (by rfl) ⟨2133509, by rfl⟩ : syracuseStep 11378717 = 4267019) B4267019
theorem B1499175 : Blo 1498069 1499175 := bstep (se 1 (by rfl) ⟨1124381, by rfl⟩ : syracuseStep 1499175 = 2248763) B2248763
theorem B1499215 : Blo 1498069 1499215 := bstep (se 1 (by rfl) ⟨1124411, by rfl⟩ : syracuseStep 1499215 = 2248823) B2248823
theorem B7594073 : Blo 1498069 7594073 := bstep (se 2 (by rfl) ⟨2847777, by rfl⟩ : syracuseStep 7594073 = 5695555) B5695555
theorem B1499231 : Blo 1498069 1499231 := bstep (se 1 (by rfl) ⟨1124423, by rfl⟩ : syracuseStep 1499231 = 2248847) B2248847
theorem B1499259 : Blo 1498069 1499259 := bstep (se 1 (by rfl) ⟨1124444, by rfl⟩ : syracuseStep 1499259 = 2248889) B2248889
theorem B5693597 : Blo 1498069 5693597 := bstep (se 3 (by rfl) ⟨1067549, by rfl⟩ : syracuseStep 5693597 = 2135099) B2135099
theorem B5693611 : Blo 1498069 5693611 := bstep (se 1 (by rfl) ⟨4270208, by rfl⟩ : syracuseStep 5693611 = 8540417) B8540417
theorem B1499311 : Blo 1498069 1499311 := bstep (se 1 (by rfl) ⟨1124483, by rfl⟩ : syracuseStep 1499311 = 2248967) B2248967
theorem B2400455 : Blo 1498069 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B1499335 : Blo 1498069 1499335 := bstep (se 1 (by rfl) ⟨1124501, by rfl⟩ : syracuseStep 1499335 = 2249003) B2249003
theorem B1499355 : Blo 1498069 1499355 := bstep (se 1 (by rfl) ⟨1124516, by rfl⟩ : syracuseStep 1499355 = 2249033) B2249033
theorem B1499431 : Blo 1498069 1499431 := bstep (se 1 (by rfl) ⟨1124573, by rfl⟩ : syracuseStep 1499431 = 2249147) B2249147
theorem B1499471 : Blo 1498069 1499471 := bstep (se 1 (by rfl) ⟨1124603, by rfl⟩ : syracuseStep 1499471 = 2249207) B2249207
theorem B7586135 : Blo 1498069 7586135 := bstep (se 1 (by rfl) ⟨5689601, by rfl⟩ : syracuseStep 7586135 = 11379203) B11379203
theorem B1499487 : Blo 1498069 1499487 := bstep (se 1 (by rfl) ⟨1124615, by rfl⟩ : syracuseStep 1499487 = 2249231) B2249231
theorem B1499515 : Blo 1498069 1499515 := bstep (se 1 (by rfl) ⟨1124636, by rfl⟩ : syracuseStep 1499515 = 2249273) B2249273
theorem B9601409 : Blo 1498069 9601409 := bstep (se 2 (by rfl) ⟨3600528, by rfl⟩ : syracuseStep 9601409 = 7201057) B7201057
theorem B1499567 : Blo 1498069 1499567 := bstep (se 1 (by rfl) ⟨1124675, by rfl⟩ : syracuseStep 1499567 = 2249351) B2249351
theorem B1499591 : Blo 1498069 1499591 := bstep (se 1 (by rfl) ⟨1124693, by rfl⟩ : syracuseStep 1499591 = 2249387) B2249387
theorem B1499611 : Blo 1498069 1499611 := bstep (se 1 (by rfl) ⟨1124708, by rfl⟩ : syracuseStep 1499611 = 2249417) B2249417
theorem B5693915 : Blo 1498069 5693915 := bstep (se 1 (by rfl) ⟨4270436, by rfl⟩ : syracuseStep 5693915 = 8540873) B8540873
theorem B17302025 : Blo 1498069 17302025 := bstep (se 2 (by rfl) ⟨6488259, by rfl⟩ : syracuseStep 17302025 = 12976519) B12976519
theorem B12157465 : Blo 1498069 12157465 := bstep (se 2 (by rfl) ⟨4559049, by rfl⟩ : syracuseStep 12157465 = 9118099) B9118099
theorem B1499687 : Blo 1498069 1499687 := bstep (se 1 (by rfl) ⟨1124765, by rfl⟩ : syracuseStep 1499687 = 2249531) B2249531
theorem B6406715 : Blo 1498069 6406715 := bstep (se 1 (by rfl) ⟨4805036, by rfl⟩ : syracuseStep 6406715 = 9610073) B9610073
theorem B1499727 : Blo 1498069 1499727 := bstep (se 1 (by rfl) ⟨1124795, by rfl⟩ : syracuseStep 1499727 = 2249591) B2249591
theorem B1499743 : Blo 1498069 1499743 := bstep (se 1 (by rfl) ⟨1124807, by rfl⟩ : syracuseStep 1499743 = 2249615) B2249615
theorem B1499771 : Blo 1498069 1499771 := bstep (se 1 (by rfl) ⟨1124828, by rfl⟩ : syracuseStep 1499771 = 2249657) B2249657
theorem B1499823 : Blo 1498069 1499823 := bstep (se 1 (by rfl) ⟨1124867, by rfl⟩ : syracuseStep 1499823 = 2249735) B2249735
theorem B1499847 : Blo 1498069 1499847 := bstep (se 1 (by rfl) ⟨1124885, by rfl⟩ : syracuseStep 1499847 = 2249771) B2249771
theorem B1499867 : Blo 1498069 1499867 := bstep (se 1 (by rfl) ⟨1124900, by rfl⟩ : syracuseStep 1499867 = 2249801) B2249801
theorem B9118493 : Blo 1498069 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B1499943 : Blo 1498069 1499943 := bstep (se 1 (by rfl) ⟨1124957, by rfl⟩ : syracuseStep 1499943 = 2249915) B2249915
theorem B1499983 : Blo 1498069 1499983 := bstep (se 1 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 1499983 = 2249975) B2249975
theorem B1499999 : Blo 1498069 1499999 := bstep (se 1 (by rfl) ⟨1124999, by rfl⟩ : syracuseStep 1499999 = 2249999) B2249999
theorem B1500027 : Blo 1498069 1500027 := bstep (se 1 (by rfl) ⟨1125020, by rfl⟩ : syracuseStep 1500027 = 2250041) B2250041
theorem B3793999 : Blo 1498069 3793999 := bstep (se 1 (by rfl) ⟨2845499, by rfl⟩ : syracuseStep 3793999 = 5690999) B5690999
theorem B6407363 : Blo 1498069 6407363 := bstep (se 1 (by rfl) ⟨4805522, by rfl⟩ : syracuseStep 6407363 = 9611045) B9611045
theorem B2278649 : Blo 1498069 2278649 := bstep (se 2 (by rfl) ⟨854493, by rfl⟩ : syracuseStep 2278649 = 1708987) B1708987
theorem B2844011 : Blo 1498069 2844011 := bstep (se 1 (by rfl) ⟨2133008, by rfl⟩ : syracuseStep 2844011 = 4266017) B4266017
theorem B2844065 : Blo 1498069 2844065 := bstep (se 2 (by rfl) ⟨1066524, by rfl⟩ : syracuseStep 2844065 = 2133049) B2133049
theorem B2024887 : Blo 1498069 2024887 := bstep (se 1 (by rfl) ⟨1518665, by rfl⟩ : syracuseStep 2024887 = 3037331) B3037331
theorem B11535817 : Blo 1498069 11535817 := bstep (se 2 (by rfl) ⟨4325931, by rfl⟩ : syracuseStep 11535817 = 8651863) B8651863
theorem B14403035 : Blo 1498069 14403035 := bstep (se 1 (by rfl) ⟨10802276, by rfl⟩ : syracuseStep 14403035 = 21604553) B21604553
theorem B2278991 : Blo 1498069 2278991 := bstep (se 1 (by rfl) ⟨1709243, by rfl⟩ : syracuseStep 2278991 = 3418487) B3418487
theorem B10258109 : Blo 1498069 10258109 := bstep (se 3 (by rfl) ⟨1923395, by rfl⟩ : syracuseStep 10258109 = 3846791) B3846791
theorem B3794647 : Blo 1498069 3794647 := bstep (se 1 (by rfl) ⟨2845985, by rfl⟩ : syracuseStep 3794647 = 5691971) B5691971
theorem B17065889 : Blo 1498069 17065889 := bstep (se 2 (by rfl) ⟨6399708, by rfl⟩ : syracuseStep 17065889 = 12799417) B12799417
theorem B3794951 : Blo 1498069 3794951 := bstep (se 1 (by rfl) ⟨2846213, by rfl⟩ : syracuseStep 3794951 = 5692427) B5692427
theorem B29599981 : Blo 1498069 29599981 := bstep (se 3 (by rfl) ⟨5549996, by rfl⟩ : syracuseStep 29599981 = 11099993) B11099993
theorem B4802807 : Blo 1498069 4802807 := bstep (se 1 (by rfl) ⟨3602105, by rfl⟩ : syracuseStep 4802807 = 7204211) B7204211
theorem B2402551 : Blo 1498069 2402551 := bstep (se 1 (by rfl) ⟨1801913, by rfl⟩ : syracuseStep 2402551 = 3603827) B3603827
theorem B5056829 : Blo 1498069 5056829 := bstep (se 3 (by rfl) ⟨948155, by rfl⟩ : syracuseStep 5056829 = 1896311) B1896311
theorem B18491753 : Blo 1498069 18491753 := bstep (se 2 (by rfl) ⟨6934407, by rfl⟩ : syracuseStep 18491753 = 13868815) B13868815
theorem B2247131 : Blo 1498069 2247131 := bstep (se 1 (by rfl) ⟨1685348, by rfl⟩ : syracuseStep 2247131 = 3370697) B3370697
theorem B10807789 : Blo 1498069 10807789 := bstep (se 3 (by rfl) ⟨2026460, by rfl⟩ : syracuseStep 10807789 = 4052921) B4052921
theorem B11536921 : Blo 1498069 11536921 := bstep (se 2 (by rfl) ⟨4326345, by rfl⟩ : syracuseStep 11536921 = 8652691) B8652691
theorem B54684193 : Blo 1498069 54684193 := bstep (se 2 (by rfl) ⟨20506572, by rfl⟩ : syracuseStep 54684193 = 41013145) B41013145
theorem B10799801 : Blo 1498069 10799801 := bstep (se 2 (by rfl) ⟨4049925, by rfl⟩ : syracuseStep 10799801 = 8099851) B8099851
theorem B2738935 : Blo 1498069 2738935 := bstep (se 1 (by rfl) ⟨2054201, by rfl⟩ : syracuseStep 2738935 = 4108403) B4108403
theorem B4803371 : Blo 1498069 4803371 := bstep (se 1 (by rfl) ⟨3602528, by rfl⟩ : syracuseStep 4803371 = 7205057) B7205057
theorem B14609297 : Blo 1498069 14609297 := bstep (se 2 (by rfl) ⟨5478486, by rfl⟩ : syracuseStep 14609297 = 10956973) B10956973
theorem B2247599 : Blo 1498069 2247599 := bstep (se 1 (by rfl) ⟨1685699, by rfl⟩ : syracuseStep 2247599 = 3371399) B3371399
theorem B5688251 : Blo 1498069 5688251 := bstep (se 1 (by rfl) ⟨4266188, by rfl⟩ : syracuseStep 5688251 = 8532377) B8532377
theorem B21613553 : Blo 1498069 21613553 := bstep (se 2 (by rfl) ⟨8105082, by rfl⟩ : syracuseStep 21613553 = 16210165) B16210165
theorem B2247689 : Blo 1498069 2247689 := bstep (se 2 (by rfl) ⟨842883, by rfl⟩ : syracuseStep 2247689 = 1685767) B1685767
theorem B2845705 : Blo 1498069 2845705 := bstep (se 2 (by rfl) ⟨1067139, by rfl⟩ : syracuseStep 2845705 = 2134279) B2134279
theorem B2247719 : Blo 1498069 2247719 := bstep (se 1 (by rfl) ⟨1685789, by rfl⟩ : syracuseStep 2247719 = 3371579) B3371579
theorem B2247803 : Blo 1498069 2247803 := bstep (se 1 (by rfl) ⟨1685852, by rfl⟩ : syracuseStep 2247803 = 3371705) B3371705
theorem B5057693 : Blo 1498069 5057693 := bstep (se 3 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 5057693 = 1896635) B1896635
theorem B2247929 : Blo 1498069 2247929 := bstep (se 2 (by rfl) ⟨842973, by rfl⟩ : syracuseStep 2247929 = 1685947) B1685947
theorem B8539415 : Blo 1498069 8539415 := bstep (se 1 (by rfl) ⟨6404561, by rfl⟩ : syracuseStep 8539415 = 12809123) B12809123
theorem B2248031 : Blo 1498069 2248031 := bstep (se 1 (by rfl) ⟨1686023, by rfl⟩ : syracuseStep 2248031 = 3372047) B3372047
theorem B2248043 : Blo 1498069 2248043 := bstep (se 1 (by rfl) ⟨1686032, by rfl⟩ : syracuseStep 2248043 = 3372065) B3372065
theorem B8105341 : Blo 1498069 8105341 := bstep (se 3 (by rfl) ⟨1519751, by rfl⟩ : syracuseStep 8105341 = 3039503) B3039503
theorem B30764461 : Blo 1498069 30764461 := bstep (se 3 (by rfl) ⟨5768336, by rfl⟩ : syracuseStep 30764461 = 11536673) B11536673
theorem B11390381 : Blo 1498069 11390381 := bstep (se 3 (by rfl) ⟨2135696, by rfl⟩ : syracuseStep 11390381 = 4271393) B4271393
theorem B2248271 : Blo 1498069 2248271 := bstep (se 1 (by rfl) ⟨1686203, by rfl⟩ : syracuseStep 2248271 = 3372407) B3372407
theorem B5058233 : Blo 1498069 5058233 := bstep (se 2 (by rfl) ⟨1896837, by rfl⟩ : syracuseStep 5058233 = 3793675) B3793675
theorem B8654525 : Blo 1498069 8654525 := bstep (se 3 (by rfl) ⟨1622723, by rfl⟩ : syracuseStep 8654525 = 3245447) B3245447
theorem B2248391 : Blo 1498069 2248391 := bstep (se 1 (by rfl) ⟨1686293, by rfl⟩ : syracuseStep 2248391 = 3372587) B3372587
theorem B7589699 : Blo 1498069 7589699 := bstep (se 1 (by rfl) ⟨5692274, by rfl⟩ : syracuseStep 7589699 = 11384549) B11384549
theorem B4804447 : Blo 1498069 4804447 := bstep (se 1 (by rfl) ⟨3603335, by rfl⟩ : syracuseStep 4804447 = 7206671) B7206671
theorem B2248553 : Blo 1498069 2248553 := bstep (se 2 (by rfl) ⟨843207, by rfl⟩ : syracuseStep 2248553 = 1686415) B1686415
theorem B3370859 : Blo 1498069 3370859 := bstep (se 1 (by rfl) ⟨2528144, by rfl⟩ : syracuseStep 3370859 = 5056289) B5056289
theorem B10809197 : Blo 1498069 10809197 := bstep (se 3 (by rfl) ⟨2026724, by rfl⟩ : syracuseStep 10809197 = 4053449) B4053449
theorem B3370913 : Blo 1498069 3370913 := bstep (se 2 (by rfl) ⟨1264092, by rfl⟩ : syracuseStep 3370913 = 2528185) B2528185
theorem B1896367 : Blo 1498069 1896367 := bstep (se 1 (by rfl) ⟨1422275, by rfl⟩ : syracuseStep 1896367 = 2844551) B2844551
theorem B2846639 : Blo 1498069 2846639 := bstep (se 1 (by rfl) ⟨2134979, by rfl⟩ : syracuseStep 2846639 = 4269959) B4269959
theorem B2248631 : Blo 1498069 2248631 := bstep (se 1 (by rfl) ⟨1686473, by rfl⟩ : syracuseStep 2248631 = 3372947) B3372947
theorem B2248667 : Blo 1498069 2248667 := bstep (se 1 (by rfl) ⟨1686500, by rfl⟩ : syracuseStep 2248667 = 3373001) B3373001
theorem B4558855 : Blo 1498069 4558855 := bstep (se 1 (by rfl) ⟨3419141, by rfl⟩ : syracuseStep 4558855 = 6838283) B6838283
theorem B5402639 : Blo 1498069 5402639 := bstep (se 1 (by rfl) ⟨4051979, by rfl⟩ : syracuseStep 5402639 = 8103959) B8103959
theorem B8532125 : Blo 1498069 8532125 := bstep (se 3 (by rfl) ⟨1599773, by rfl⟩ : syracuseStep 8532125 = 3199547) B3199547
theorem B3371255 : Blo 1498069 3371255 := bstep (se 1 (by rfl) ⟨2528441, by rfl⟩ : syracuseStep 3371255 = 5056883) B5056883
theorem B5058827 : Blo 1498069 5058827 := bstep (se 1 (by rfl) ⟨3794120, by rfl⟩ : syracuseStep 5058827 = 7588241) B7588241
theorem B11383091 : Blo 1498069 11383091 := bstep (se 1 (by rfl) ⟨8537318, by rfl⟩ : syracuseStep 11383091 = 17074637) B17074637
theorem B2249135 : Blo 1498069 2249135 := bstep (se 1 (by rfl) ⟨1686851, by rfl⟩ : syracuseStep 2249135 = 3373703) B3373703
theorem B2847163 : Blo 1498069 2847163 := bstep (se 1 (by rfl) ⟨2135372, by rfl⟩ : syracuseStep 2847163 = 4270745) B4270745
theorem B2249225 : Blo 1498069 2249225 := bstep (se 2 (by rfl) ⟨843459, by rfl⟩ : syracuseStep 2249225 = 1686919) B1686919
theorem B5059097 : Blo 1498069 5059097 := bstep (se 2 (by rfl) ⟨1897161, by rfl⟩ : syracuseStep 5059097 = 3794323) B3794323
theorem B2249255 : Blo 1498069 2249255 := bstep (se 1 (by rfl) ⟨1686941, by rfl⟩ : syracuseStep 2249255 = 3373883) B3373883
theorem B2249339 : Blo 1498069 2249339 := bstep (se 1 (by rfl) ⟨1687004, by rfl⟩ : syracuseStep 2249339 = 3374009) B3374009
theorem B1520303 : Blo 1498069 1520303 := bstep (se 1 (by rfl) ⟨1140227, by rfl⟩ : syracuseStep 1520303 = 2280455) B2280455
theorem B2249465 : Blo 1498069 2249465 := bstep (se 2 (by rfl) ⟨843549, by rfl⟩ : syracuseStep 2249465 = 1687099) B1687099
theorem B6075179 : Blo 1498069 6075179 := bstep (se 1 (by rfl) ⟨4556384, by rfl⟩ : syracuseStep 6075179 = 9112769) B9112769
theorem B8532809 : Blo 1498069 8532809 := bstep (se 2 (by rfl) ⟨3199803, by rfl⟩ : syracuseStep 8532809 = 6399607) B6399607
theorem B3371849 : Blo 1498069 3371849 := bstep (se 2 (by rfl) ⟨1264443, by rfl⟩ : syracuseStep 3371849 = 2528887) B2528887
theorem B2249567 : Blo 1498069 2249567 := bstep (se 1 (by rfl) ⟨1687175, by rfl⟩ : syracuseStep 2249567 = 3374351) B3374351
theorem B2249579 : Blo 1498069 2249579 := bstep (se 1 (by rfl) ⟨1687184, by rfl⟩ : syracuseStep 2249579 = 3374369) B3374369
theorem B2847649 : Blo 1498069 2847649 := bstep (se 2 (by rfl) ⟨1067868, by rfl⟩ : syracuseStep 2847649 = 2135737) B2135737
theorem B2528219 : Blo 1498069 2528219 := bstep (se 1 (by rfl) ⟨1896164, by rfl⟩ : syracuseStep 2528219 = 3792329) B3792329
theorem B1897435 : Blo 1498069 1897435 := bstep (se 1 (by rfl) ⟨1423076, by rfl⟩ : syracuseStep 1897435 = 2846153) B2846153
theorem B2249807 : Blo 1498069 2249807 := bstep (se 1 (by rfl) ⟨1687355, by rfl⟩ : syracuseStep 2249807 = 3374711) B3374711
theorem B5690483 : Blo 1498069 5690483 := bstep (se 1 (by rfl) ⟨4267862, by rfl⟩ : syracuseStep 5690483 = 8535725) B8535725
theorem B38925461 : Blo 1498069 38925461 := bstep (se 6 (by rfl) ⟨912315, by rfl⟩ : syracuseStep 38925461 = 1824631) B1824631
theorem B30758059 : Blo 1498069 30758059 := bstep (se 1 (by rfl) ⟨23068544, by rfl⟩ : syracuseStep 30758059 = 46137089) B46137089
theorem B2528455 : Blo 1498069 2528455 := bstep (se 1 (by rfl) ⟨1896341, by rfl⟩ : syracuseStep 2528455 = 3792683) B3792683
theorem B2249927 : Blo 1498069 2249927 := bstep (se 1 (by rfl) ⟨1687445, by rfl⟩ : syracuseStep 2249927 = 3374891) B3374891
theorem B85505381 : Blo 1498069 85505381 := bstep (se 4 (by rfl) ⟨8016129, by rfl⟩ : syracuseStep 85505381 = 16032259) B16032259
theorem B2528617 : Blo 1498069 2528617 := bstep (se 2 (by rfl) ⟨948231, by rfl⟩ : syracuseStep 2528617 = 1896463) B1896463
theorem B5404009 : Blo 1498069 5404009 := bstep (se 2 (by rfl) ⟨2026503, by rfl⟩ : syracuseStep 5404009 = 4053007) B4053007
theorem B2250089 : Blo 1498069 2250089 := bstep (se 2 (by rfl) ⟨843783, by rfl⟩ : syracuseStep 2250089 = 1687567) B1687567
theorem B19461491 : Blo 1498069 19461491 := bstep (se 1 (by rfl) ⟨14596118, by rfl⟩ : syracuseStep 19461491 = 29192237) B29192237
theorem B10139053 : Blo 1498069 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B19207691 : Blo 1498069 19207691 := bstep (se 1 (by rfl) ⟨14405768, by rfl⟩ : syracuseStep 19207691 = 28811537) B28811537
theorem B3372641 : Blo 1498069 3372641 := bstep (se 2 (by rfl) ⟨1264740, by rfl⟩ : syracuseStep 3372641 = 2529481) B2529481
theorem B1799803 : Blo 1498069 1799803 := bstep (se 1 (by rfl) ⟨1349852, by rfl⟩ : syracuseStep 1799803 = 2699705) B2699705
theorem B10253947 : Blo 1498069 10253947 := bstep (se 1 (by rfl) ⟨7690460, by rfl⟩ : syracuseStep 10253947 = 15380921) B15380921
theorem B5404283 : Blo 1498069 5404283 := bstep (se 1 (by rfl) ⟨4053212, by rfl⟩ : syracuseStep 5404283 = 8106425) B8106425
theorem B5060231 : Blo 1498069 5060231 := bstep (se 1 (by rfl) ⟨3795173, by rfl⟩ : syracuseStep 5060231 = 7590347) B7590347
theorem B5060285 : Blo 1498069 5060285 := bstep (se 3 (by rfl) ⟨948803, by rfl⟩ : syracuseStep 5060285 = 1897607) B1897607
theorem B62404337 : Blo 1498069 62404337 := bstep (se 2 (by rfl) ⟨23401626, by rfl⟩ : syracuseStep 62404337 = 46803253) B46803253
theorem B5773049 : Blo 1498069 5773049 := bstep (se 2 (by rfl) ⟨2164893, by rfl⟩ : syracuseStep 5773049 = 4329787) B4329787
theorem B5060447 : Blo 1498069 5060447 := bstep (se 1 (by rfl) ⟨3795335, by rfl⟩ : syracuseStep 5060447 = 7590671) B7590671
theorem B2053993 : Blo 1498069 2053993 := bstep (se 2 (by rfl) ⟨770247, by rfl⟩ : syracuseStep 2053993 = 1540495) B1540495
theorem B3372983 : Blo 1498069 3372983 := bstep (se 1 (by rfl) ⟨2529737, by rfl⟩ : syracuseStep 3372983 = 5059475) B5059475
theorem B2529211 : Blo 1498069 2529211 := bstep (se 1 (by rfl) ⟨1896908, by rfl⟩ : syracuseStep 2529211 = 3793817) B3793817
theorem B25958353 : Blo 1498069 25958353 := bstep (se 2 (by rfl) ⟨9734382, by rfl⟩ : syracuseStep 25958353 = 19468765) B19468765
theorem B5060609 : Blo 1498069 5060609 := bstep (se 2 (by rfl) ⟨1897728, by rfl⟩ : syracuseStep 5060609 = 3795457) B3795457
theorem B2529319 : Blo 1498069 2529319 := bstep (se 1 (by rfl) ⟨1896989, by rfl⟩ : syracuseStep 2529319 = 3793979) B3793979
theorem B72890455 : Blo 1498069 72890455 := bstep (se 1 (by rfl) ⟨54667841, by rfl⟩ : syracuseStep 72890455 = 109335683) B109335683
theorem B2529643 : Blo 1498069 2529643 := bstep (se 1 (by rfl) ⟨1897232, by rfl⟩ : syracuseStep 2529643 = 3794465) B3794465
theorem B3373577 : Blo 1498069 3373577 := bstep (se 2 (by rfl) ⟨1265091, by rfl⟩ : syracuseStep 3373577 = 2530183) B2530183
theorem B1686055 : Blo 1498069 1686055 := bstep (se 1 (by rfl) ⟨1264541, by rfl⟩ : syracuseStep 1686055 = 2529083) B2529083
theorem B10959545 : Blo 1498069 10959545 := bstep (se 2 (by rfl) ⟨4109829, by rfl⟩ : syracuseStep 10959545 = 8219659) B8219659
theorem B3603143 : Blo 1498069 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B5405393 : Blo 1498069 5405393 := bstep (se 2 (by rfl) ⟨2027022, by rfl⟩ : syracuseStep 5405393 = 4054045) B4054045
theorem B72940277 : Blo 1498069 72940277 := bstep (se 5 (by rfl) ⟨3419075, by rfl⟩ : syracuseStep 72940277 = 6838151) B6838151
theorem B5692153 : Blo 1498069 5692153 := bstep (se 2 (by rfl) ⟨2134557, by rfl⟩ : syracuseStep 5692153 = 4269115) B4269115
theorem B7584515 : Blo 1498069 7584515 := bstep (se 1 (by rfl) ⟨5688386, by rfl⟩ : syracuseStep 7584515 = 11376773) B11376773
theorem B5061419 : Blo 1498069 5061419 := bstep (se 1 (by rfl) ⟨3796064, by rfl⟩ : syracuseStep 5061419 = 7592129) B7592129
theorem B7592777 : Blo 1498069 7592777 := bstep (se 2 (by rfl) ⟨2847291, by rfl⟩ : syracuseStep 7592777 = 5694583) B5694583
theorem B3373919 : Blo 1498069 3373919 := bstep (se 1 (by rfl) ⟨2530439, by rfl⟩ : syracuseStep 3373919 = 5060879) B5060879
theorem B1498075 : Blo 1498069 1498075 := bstep (se 1 (by rfl) ⟨1123556, by rfl⟩ : syracuseStep 1498075 = 2247113) B2247113
theorem B8535041 : Blo 1498069 8535041 := bstep (se 2 (by rfl) ⟨3200640, by rfl⟩ : syracuseStep 8535041 = 6401281) B6401281
theorem B3374099 : Blo 1498069 3374099 := bstep (se 1 (by rfl) ⟨2530574, by rfl⟩ : syracuseStep 3374099 = 5061149) B5061149
theorem B1498151 : Blo 1498069 1498151 := bstep (se 1 (by rfl) ⟨1123613, by rfl⟩ : syracuseStep 1498151 = 2247227) B2247227
theorem B5061689 : Blo 1498069 5061689 := bstep (se 2 (by rfl) ⟨1898133, by rfl⟩ : syracuseStep 5061689 = 3796267) B3796267
theorem B1498191 : Blo 1498069 1498191 := bstep (se 1 (by rfl) ⟨1123643, by rfl⟩ : syracuseStep 1498191 = 2247287) B2247287
theorem B5479505 : Blo 1498069 5479505 := bstep (se 2 (by rfl) ⟨2054814, by rfl⟩ : syracuseStep 5479505 = 4109629) B4109629
theorem B1498207 : Blo 1498069 1498207 := bstep (se 1 (by rfl) ⟨1123655, by rfl⟩ : syracuseStep 1498207 = 2247311) B2247311
theorem B1498235 : Blo 1498069 1498235 := bstep (se 1 (by rfl) ⟨1123676, by rfl⟩ : syracuseStep 1498235 = 2247353) B2247353
theorem B1498287 : Blo 1498069 1498287 := bstep (se 1 (by rfl) ⟨1123715, by rfl⟩ : syracuseStep 1498287 = 2247431) B2247431
theorem B1498311 : Blo 1498069 1498311 := bstep (se 1 (by rfl) ⟨1123733, by rfl⟩ : syracuseStep 1498311 = 2247467) B2247467
theorem B1498331 : Blo 1498069 1498331 := bstep (se 1 (by rfl) ⟨1123748, by rfl⟩ : syracuseStep 1498331 = 2247497) B2247497
theorem B1498407 : Blo 1498069 1498407 := bstep (se 1 (by rfl) ⟨1123805, by rfl⟩ : syracuseStep 1498407 = 2247611) B2247611
theorem B1498447 : Blo 1498069 1498447 := bstep (se 1 (by rfl) ⟨1123835, by rfl⟩ : syracuseStep 1498447 = 2247671) B2247671
theorem B1498463 : Blo 1498069 1498463 := bstep (se 1 (by rfl) ⟨1123847, by rfl⟩ : syracuseStep 1498463 = 2247695) B2247695
theorem B3374441 : Blo 1498069 3374441 := bstep (se 2 (by rfl) ⟨1265415, by rfl⟩ : syracuseStep 3374441 = 2530831) B2530831
theorem B1498491 : Blo 1498069 1498491 := bstep (se 1 (by rfl) ⟨1123868, by rfl⟩ : syracuseStep 1498491 = 2247737) B2247737
theorem B5062013 : Blo 1498069 5062013 := bstep (se 3 (by rfl) ⟨949127, by rfl⟩ : syracuseStep 5062013 = 1898255) B1898255
theorem B4799873 : Blo 1498069 4799873 := bstep (se 2 (by rfl) ⟨1799952, by rfl⟩ : syracuseStep 4799873 = 3599905) B3599905
theorem B2530703 : Blo 1498069 2530703 := bstep (se 1 (by rfl) ⟨1898027, by rfl⟩ : syracuseStep 2530703 = 3796055) B3796055
theorem B1498543 : Blo 1498069 1498543 := bstep (se 1 (by rfl) ⟨1123907, by rfl⟩ : syracuseStep 1498543 = 2247815) B2247815
theorem B1498567 : Blo 1498069 1498567 := bstep (se 1 (by rfl) ⟨1123925, by rfl⟩ : syracuseStep 1498567 = 2247851) B2247851
theorem B1498587 : Blo 1498069 1498587 := bstep (se 1 (by rfl) ⟨1123940, by rfl⟩ : syracuseStep 1498587 = 2247881) B2247881
theorem B4799987 : Blo 1498069 4799987 := bstep (se 1 (by rfl) ⟨3599990, by rfl⟩ : syracuseStep 4799987 = 7199981) B7199981
theorem B1498663 : Blo 1498069 1498663 := bstep (se 1 (by rfl) ⟨1123997, by rfl⟩ : syracuseStep 1498663 = 2247995) B2247995
theorem B1498703 : Blo 1498069 1498703 := bstep (se 1 (by rfl) ⟨1124027, by rfl⟩ : syracuseStep 1498703 = 2248055) B2248055
theorem B2702927 : Blo 1498069 2702927 := bstep (se 1 (by rfl) ⟨2027195, by rfl⟩ : syracuseStep 2702927 = 4054391) B4054391
theorem B1498719 : Blo 1498069 1498719 := bstep (se 1 (by rfl) ⟨1124039, by rfl⟩ : syracuseStep 1498719 = 2248079) B2248079
theorem B1498747 : Blo 1498069 1498747 := bstep (se 1 (by rfl) ⟨1124060, by rfl⟩ : syracuseStep 1498747 = 2248121) B2248121
theorem B20512379 : Blo 1498069 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B2530939 : Blo 1498069 2530939 := bstep (se 1 (by rfl) ⟨1898204, by rfl⟩ : syracuseStep 2530939 = 3796409) B3796409
theorem B5062283 : Blo 1498069 5062283 := bstep (se 1 (by rfl) ⟨3796712, by rfl⟩ : syracuseStep 5062283 = 7593425) B7593425
theorem B8650385 : Blo 1498069 8650385 := bstep (se 2 (by rfl) ⟨3243894, by rfl⟩ : syracuseStep 8650385 = 6487789) B6487789
theorem B1498799 : Blo 1498069 1498799 := bstep (se 1 (by rfl) ⟨1124099, by rfl⟩ : syracuseStep 1498799 = 2248199) B2248199
theorem B3464903 : Blo 1498069 3464903 := bstep (se 1 (by rfl) ⟨2598677, by rfl⟩ : syracuseStep 3464903 = 5197355) B5197355
theorem B1498823 : Blo 1498069 1498823 := bstep (se 1 (by rfl) ⟨1124117, by rfl⟩ : syracuseStep 1498823 = 2248235) B2248235
theorem B1498843 : Blo 1498069 1498843 := bstep (se 1 (by rfl) ⟨1124132, by rfl⟩ : syracuseStep 1498843 = 2248265) B2248265
theorem B1498919 : Blo 1498069 1498919 := bstep (se 1 (by rfl) ⟨1124189, by rfl⟩ : syracuseStep 1498919 = 2248379) B2248379
theorem B3039049 : Blo 1498069 3039049 := bstep (se 2 (by rfl) ⟨1139643, by rfl⟩ : syracuseStep 3039049 = 2279287) B2279287
theorem B1498959 : Blo 1498069 1498959 := bstep (se 1 (by rfl) ⟨1124219, by rfl⟩ : syracuseStep 1498959 = 2248439) B2248439
theorem B1498975 : Blo 1498069 1498975 := bstep (se 1 (by rfl) ⟨1124231, by rfl⟩ : syracuseStep 1498975 = 2248463) B2248463
theorem B1499003 : Blo 1498069 1499003 := bstep (se 1 (by rfl) ⟨1124252, by rfl⟩ : syracuseStep 1499003 = 2248505) B2248505
theorem B3792815 : Blo 1498069 3792815 := bstep (se 1 (by rfl) ⟨2844611, by rfl⟩ : syracuseStep 3792815 = 5689223) B5689223
theorem B1499055 : Blo 1498069 1499055 := bstep (se 1 (by rfl) ⟨1124291, by rfl⟩ : syracuseStep 1499055 = 2248583) B2248583
theorem B3375035 : Blo 1498069 3375035 := bstep (se 1 (by rfl) ⟨2531276, by rfl⟩ : syracuseStep 3375035 = 5062553) B5062553
theorem B1499079 : Blo 1498069 1499079 := bstep (se 1 (by rfl) ⟨1124309, by rfl⟩ : syracuseStep 1499079 = 2248619) B2248619
theorem B1499099 : Blo 1498069 1499099 := bstep (se 1 (by rfl) ⟨1124324, by rfl⟩ : syracuseStep 1499099 = 2248649) B2248649
theorem B6078473 : Blo 1498069 6078473 := bstep (se 2 (by rfl) ⟨2279427, by rfl⟩ : syracuseStep 6078473 = 4558855) B4558855
theorem B7585811 : Blo 1498069 7585811 := bstep (se 1 (by rfl) ⟨5689358, by rfl⟩ : syracuseStep 7585811 = 11378717) B11378717
theorem B5062715 : Blo 1498069 5062715 := bstep (se 1 (by rfl) ⟨3797036, by rfl⟩ : syracuseStep 5062715 = 7594073) B7594073
theorem B1499423 : Blo 1498069 1499423 := bstep (se 1 (by rfl) ⟨1124567, by rfl⟩ : syracuseStep 1499423 = 2249135) B2249135
theorem B3203401 : Blo 1498069 3203401 := bstep (se 2 (by rfl) ⟨1201275, by rfl⟩ : syracuseStep 3203401 = 2402551) B2402551
theorem B11534683 : Blo 1498069 11534683 := bstep (se 1 (by rfl) ⟨8651012, by rfl⟩ : syracuseStep 11534683 = 17302025) B17302025
theorem B1499483 : Blo 1498069 1499483 := bstep (se 1 (by rfl) ⟨1124612, by rfl⟩ : syracuseStep 1499483 = 2249225) B2249225
theorem B1499503 : Blo 1498069 1499503 := bstep (se 1 (by rfl) ⟨1124627, by rfl⟩ : syracuseStep 1499503 = 2249255) B2249255
theorem B1499559 : Blo 1498069 1499559 := bstep (se 1 (by rfl) ⟨1124669, by rfl⟩ : syracuseStep 1499559 = 2249339) B2249339
theorem B1499643 : Blo 1498069 1499643 := bstep (se 1 (by rfl) ⟨1124732, by rfl⟩ : syracuseStep 1499643 = 2249465) B2249465
theorem B6078995 : Blo 1498069 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B1499711 : Blo 1498069 1499711 := bstep (se 1 (by rfl) ⟨1124783, by rfl⟩ : syracuseStep 1499711 = 2249567) B2249567
theorem B1499719 : Blo 1498069 1499719 := bstep (se 1 (by rfl) ⟨1124789, by rfl⟩ : syracuseStep 1499719 = 2249579) B2249579
theorem B14410385 : Blo 1498069 14410385 := bstep (se 2 (by rfl) ⟨5403894, by rfl⟩ : syracuseStep 14410385 = 10807789) B10807789
theorem B1499871 : Blo 1498069 1499871 := bstep (se 1 (by rfl) ⟨1124903, by rfl⟩ : syracuseStep 1499871 = 2249807) B2249807
theorem B3793655 : Blo 1498069 3793655 := bstep (se 1 (by rfl) ⟨2845241, by rfl⟩ : syracuseStep 3793655 = 5690483) B5690483
theorem B1499951 : Blo 1498069 1499951 := bstep (se 1 (by rfl) ⟨1124963, by rfl⟩ : syracuseStep 1499951 = 2249927) B2249927
theorem B1500059 : Blo 1498069 1500059 := bstep (se 1 (by rfl) ⟨1125044, by rfl⟩ : syracuseStep 1500059 = 2250089) B2250089
theorem B12805127 : Blo 1498069 12805127 := bstep (se 1 (by rfl) ⟨9603845, by rfl⟩ : syracuseStep 12805127 = 19207691) B19207691
theorem B3794273 : Blo 1498069 3794273 := bstep (se 2 (by rfl) ⟨1422852, by rfl⟩ : syracuseStep 3794273 = 2845705) B2845705
theorem B41010745 : Blo 1498069 41010745 := bstep (se 2 (by rfl) ⟨15379029, by rfl⟩ : syracuseStep 41010745 = 30758059) B30758059
theorem B10807121 : Blo 1498069 10807121 := bstep (se 2 (by rfl) ⟨4052670, by rfl⟩ : syracuseStep 10807121 = 8105341) B8105341
theorem B5056343 : Blo 1498069 5056343 := bstep (se 1 (by rfl) ⟨3792257, by rfl⟩ : syracuseStep 5056343 = 7584515) B7584515
theorem B41019281 : Blo 1498069 41019281 := bstep (se 2 (by rfl) ⟨15382230, by rfl⟩ : syracuseStep 41019281 = 30764461) B30764461
theorem B13518737 : Blo 1498069 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B13674919 : Blo 1498069 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B5769683 : Blo 1498069 5769683 := bstep (se 1 (by rfl) ⟨4327262, by rfl⟩ : syracuseStep 5769683 = 8654525) B8654525
theorem B2738657 : Blo 1498069 2738657 := bstep (se 2 (by rfl) ⟨1026996, by rfl⟩ : syracuseStep 2738657 = 2053993) B2053993
theorem B2247239 : Blo 1498069 2247239 := bstep (se 1 (by rfl) ⟨1685429, by rfl⟩ : syracuseStep 2247239 = 3370859) B3370859
theorem B2247275 : Blo 1498069 2247275 := bstep (se 1 (by rfl) ⟨1685456, by rfl⟩ : syracuseStep 2247275 = 3370913) B3370913
theorem B246131405 : Blo 1498069 246131405 := bstep (se 3 (by rfl) ⟨46149638, by rfl⟩ : syracuseStep 246131405 = 92299277) B92299277
theorem B5688083 : Blo 1498069 5688083 := bstep (se 1 (by rfl) ⟨4266062, by rfl⟩ : syracuseStep 5688083 = 8532125) B8532125
theorem B3795731 : Blo 1498069 3795731 := bstep (se 1 (by rfl) ⟨2846798, by rfl⟩ : syracuseStep 3795731 = 5693597) B5693597
theorem B2247503 : Blo 1498069 2247503 := bstep (se 1 (by rfl) ⟨1685627, by rfl⟩ : syracuseStep 2247503 = 3371255) B3371255
theorem B7588727 : Blo 1498069 7588727 := bstep (se 1 (by rfl) ⟨5691545, by rfl⟩ : syracuseStep 7588727 = 11383091) B11383091
theorem B5057423 : Blo 1498069 5057423 := bstep (se 1 (by rfl) ⟨3793067, by rfl⟩ : syracuseStep 5057423 = 7586135) B7586135
theorem B6400939 : Blo 1498069 6400939 := bstep (se 1 (by rfl) ⟨4800704, by rfl⟩ : syracuseStep 6400939 = 9601409) B9601409
theorem B3795943 : Blo 1498069 3795943 := bstep (se 1 (by rfl) ⟨2846957, by rfl⟩ : syracuseStep 3795943 = 5693915) B5693915
theorem B4271143 : Blo 1498069 4271143 := bstep (se 1 (by rfl) ⟨3203357, by rfl⟩ : syracuseStep 4271143 = 6406715) B6406715
theorem B6401213 : Blo 1498069 6401213 := bstep (se 3 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 6401213 = 2400455) B2400455
theorem B4050119 : Blo 1498069 4050119 := bstep (se 1 (by rfl) ⟨3037589, by rfl⟩ : syracuseStep 4050119 = 6075179) B6075179
theorem B5688539 : Blo 1498069 5688539 := bstep (se 1 (by rfl) ⟨4266404, by rfl⟩ : syracuseStep 5688539 = 8532809) B8532809
theorem B2247899 : Blo 1498069 2247899 := bstep (se 1 (by rfl) ⟨1685924, by rfl⟩ : syracuseStep 2247899 = 3371849) B3371849
theorem B3796217 : Blo 1498069 3796217 := bstep (se 2 (by rfl) ⟨1423581, by rfl⟩ : syracuseStep 3796217 = 2847163) B2847163
theorem B72912257 : Blo 1498069 72912257 := bstep (se 2 (by rfl) ⟨27342096, by rfl⟩ : syracuseStep 72912257 = 54684193) B54684193
theorem B2248073 : Blo 1498069 2248073 := bstep (se 2 (by rfl) ⟨843027, by rfl⟩ : syracuseStep 2248073 = 1686055) B1686055
theorem B57003587 : Blo 1498069 57003587 := bstep (se 1 (by rfl) ⟨42752690, by rfl⟩ : syracuseStep 57003587 = 85505381) B85505381
theorem B1896043 : Blo 1498069 1896043 := bstep (se 1 (by rfl) ⟨1422032, by rfl⟩ : syracuseStep 1896043 = 2844065) B2844065
theorem B7589537 : Blo 1498069 7589537 := bstep (se 2 (by rfl) ⟨2846076, by rfl⟩ : syracuseStep 7589537 = 5692153) B5692153
theorem B1519327 : Blo 1498069 1519327 := bstep (se 1 (by rfl) ⟨1139495, by rfl⟩ : syracuseStep 1519327 = 2278991) B2278991
theorem B2248427 : Blo 1498069 2248427 := bstep (se 1 (by rfl) ⟨1686320, by rfl⟩ : syracuseStep 2248427 = 3372641) B3372641
theorem B41602891 : Blo 1498069 41602891 := bstep (se 1 (by rfl) ⟨31202168, by rfl⟩ : syracuseStep 41602891 = 62404337) B62404337
theorem B3796865 : Blo 1498069 3796865 := bstep (se 2 (by rfl) ⟨1423824, by rfl⟩ : syracuseStep 3796865 = 2847649) B2847649
theorem B38408093 : Blo 1498069 38408093 := bstep (se 3 (by rfl) ⟨7201517, by rfl⟩ : syracuseStep 38408093 = 14403035) B14403035
theorem B2248655 : Blo 1498069 2248655 := bstep (se 1 (by rfl) ⟨1686491, by rfl⟩ : syracuseStep 2248655 = 3372983) B3372983
theorem B5058665 : Blo 1498069 5058665 := bstep (se 2 (by rfl) ⟨1896999, by rfl⟩ : syracuseStep 5058665 = 3793999) B3793999
theorem B3371219 : Blo 1498069 3371219 := bstep (se 1 (by rfl) ⟨2528414, by rfl⟩ : syracuseStep 3371219 = 5056829) B5056829
theorem B3371273 : Blo 1498069 3371273 := bstep (se 2 (by rfl) ⟨1264227, by rfl⟩ : syracuseStep 3371273 = 2528455) B2528455
theorem B2249051 : Blo 1498069 2249051 := bstep (se 1 (by rfl) ⟨1686788, by rfl⟩ : syracuseStep 2249051 = 3373577) B3373577
theorem B16208261 : Blo 1498069 16208261 := bstep (se 4 (by rfl) ⟨1519524, by rfl⟩ : syracuseStep 16208261 = 3039049) B3039049
theorem B3371489 : Blo 1498069 3371489 := bstep (se 2 (by rfl) ⟨1264308, by rfl⟩ : syracuseStep 3371489 = 2528617) B2528617
theorem B7205345 : Blo 1498069 7205345 := bstep (se 2 (by rfl) ⟨2702004, by rfl⟩ : syracuseStep 7205345 = 5404009) B5404009
theorem B14414381 : Blo 1498069 14414381 := bstep (se 3 (by rfl) ⟨2702696, by rfl⟩ : syracuseStep 14414381 = 5405393) B5405393
theorem B2249279 : Blo 1498069 2249279 := bstep (se 1 (by rfl) ⟨1686959, by rfl⟩ : syracuseStep 2249279 = 3373919) B3373919
theorem B2699849 : Blo 1498069 2699849 := bstep (se 2 (by rfl) ⟨1012443, by rfl⟩ : syracuseStep 2699849 = 2024887) B2024887
theorem B15381089 : Blo 1498069 15381089 := bstep (se 2 (by rfl) ⟨5767908, by rfl⟩ : syracuseStep 15381089 = 11535817) B11535817
theorem B194507405 : Blo 1498069 194507405 := bstep (se 3 (by rfl) ⟨36470138, by rfl⟩ : syracuseStep 194507405 = 72940277) B72940277
theorem B5690027 : Blo 1498069 5690027 := bstep (se 1 (by rfl) ⟨4267520, by rfl⟩ : syracuseStep 5690027 = 8535041) B8535041
theorem B2249399 : Blo 1498069 2249399 := bstep (se 1 (by rfl) ⟨1687049, by rfl⟩ : syracuseStep 2249399 = 3374099) B3374099
theorem B3371795 : Blo 1498069 3371795 := bstep (se 1 (by rfl) ⟨2528846, by rfl⟩ : syracuseStep 3371795 = 5057693) B5057693
theorem B2249627 : Blo 1498069 2249627 := bstep (se 1 (by rfl) ⟨1687220, by rfl⟩ : syracuseStep 2249627 = 3374441) B3374441
theorem B3199915 : Blo 1498069 3199915 := bstep (se 1 (by rfl) ⟨2399936, by rfl⟩ : syracuseStep 3199915 = 4799873) B4799873
theorem B5059529 : Blo 1498069 5059529 := bstep (se 2 (by rfl) ⟨1897323, by rfl⟩ : syracuseStep 5059529 = 3794647) B3794647
theorem B3199991 : Blo 1498069 3199991 := bstep (se 1 (by rfl) ⟨2399993, by rfl⟩ : syracuseStep 3199991 = 4799987) B4799987
theorem B3372155 : Blo 1498069 3372155 := bstep (se 1 (by rfl) ⟨2529116, by rfl⟩ : syracuseStep 3372155 = 5058233) B5058233
theorem B5059799 : Blo 1498069 5059799 := bstep (se 1 (by rfl) ⟨3794849, by rfl⟩ : syracuseStep 5059799 = 7589699) B7589699
theorem B2528489 : Blo 1498069 2528489 := bstep (se 2 (by rfl) ⟨948183, by rfl⟩ : syracuseStep 2528489 = 1896367) B1896367
theorem B7206131 : Blo 1498069 7206131 := bstep (se 1 (by rfl) ⟨5404598, by rfl⟩ : syracuseStep 7206131 = 10809197) B10809197
theorem B3372281 : Blo 1498069 3372281 := bstep (se 2 (by rfl) ⟨1264605, by rfl⟩ : syracuseStep 3372281 = 2529211) B2529211
theorem B2528543 : Blo 1498069 2528543 := bstep (se 1 (by rfl) ⟨1896407, by rfl⟩ : syracuseStep 2528543 = 3792815) B3792815
theorem B1897759 : Blo 1498069 1897759 := bstep (se 1 (by rfl) ⟨1423319, by rfl⟩ : syracuseStep 1897759 = 2846639) B2846639
theorem B2250023 : Blo 1498069 2250023 := bstep (se 1 (by rfl) ⟨1687517, by rfl⟩ : syracuseStep 2250023 = 3375035) B3375035
theorem B3601759 : Blo 1498069 3601759 := bstep (se 1 (by rfl) ⟨2701319, by rfl⟩ : syracuseStep 3601759 = 5402639) B5402639
theorem B3372425 : Blo 1498069 3372425 := bstep (se 2 (by rfl) ⟨1264659, by rfl⟩ : syracuseStep 3372425 = 2529319) B2529319
theorem B97187273 : Blo 1498069 97187273 := bstep (se 2 (by rfl) ⟨36445227, by rfl⟩ : syracuseStep 97187273 = 72890455) B72890455
theorem B3372551 : Blo 1498069 3372551 := bstep (se 1 (by rfl) ⟨2529413, by rfl⟩ : syracuseStep 3372551 = 5058827) B5058827
theorem B7591481 : Blo 1498069 7591481 := bstep (se 2 (by rfl) ⟨2846805, by rfl⟩ : syracuseStep 7591481 = 5693611) B5693611
theorem B3372731 : Blo 1498069 3372731 := bstep (se 1 (by rfl) ⟨2529548, by rfl⟩ : syracuseStep 3372731 = 5059097) B5059097
theorem B3372857 : Blo 1498069 3372857 := bstep (se 2 (by rfl) ⟨1264821, by rfl⟩ : syracuseStep 3372857 = 2529643) B2529643
theorem B17086301 : Blo 1498069 17086301 := bstep (se 3 (by rfl) ⟨3203681, by rfl⟩ : syracuseStep 17086301 = 6407363) B6407363
theorem B9598949 : Blo 1498069 9598949 := bstep (se 4 (by rfl) ⟨899901, by rfl⟩ : syracuseStep 9598949 = 1799803) B1799803
theorem B1685479 : Blo 1498069 1685479 := bstep (se 1 (by rfl) ⟨1264109, by rfl⟩ : syracuseStep 1685479 = 2528219) B2528219
theorem B6076397 : Blo 1498069 6076397 := bstep (se 3 (by rfl) ⟨1139324, by rfl⟩ : syracuseStep 6076397 = 2278649) B2278649
theorem B15382561 : Blo 1498069 15382561 := bstep (se 2 (by rfl) ⟨5768460, by rfl⟩ : syracuseStep 15382561 = 11536921) B11536921
theorem B16209953 : Blo 1498069 16209953 := bstep (se 2 (by rfl) ⟨6078732, by rfl⟩ : syracuseStep 16209953 = 12157465) B12157465
theorem B25950307 : Blo 1498069 25950307 := bstep (se 1 (by rfl) ⟨19462730, by rfl⟩ : syracuseStep 25950307 = 38925461) B38925461
theorem B12974327 : Blo 1498069 12974327 := bstep (se 1 (by rfl) ⟨9730745, by rfl⟩ : syracuseStep 12974327 = 19461491) B19461491
theorem B7584029 : Blo 1498069 7584029 := bstep (se 3 (by rfl) ⟨1422005, by rfl⟩ : syracuseStep 7584029 = 2844011) B2844011
theorem B3651913 : Blo 1498069 3651913 := bstep (se 2 (by rfl) ⟨1369467, by rfl⟩ : syracuseStep 3651913 = 2738935) B2738935
theorem B3602855 : Blo 1498069 3602855 := bstep (se 1 (by rfl) ⟨2702141, by rfl⟩ : syracuseStep 3602855 = 5404283) B5404283
theorem B3373487 : Blo 1498069 3373487 := bstep (se 1 (by rfl) ⟨2530115, by rfl⟩ : syracuseStep 3373487 = 5060231) B5060231
theorem B6838739 : Blo 1498069 6838739 := bstep (se 1 (by rfl) ⟨5129054, by rfl⟩ : syracuseStep 6838739 = 10258109) B10258109
theorem B3373523 : Blo 1498069 3373523 := bstep (se 1 (by rfl) ⟨2530142, by rfl⟩ : syracuseStep 3373523 = 5060285) B5060285
theorem B3848699 : Blo 1498069 3848699 := bstep (se 1 (by rfl) ⟨2886524, by rfl⟩ : syracuseStep 3848699 = 5773049) B5773049
theorem B3373631 : Blo 1498069 3373631 := bstep (se 1 (by rfl) ⟨2530223, by rfl⟩ : syracuseStep 3373631 = 5060447) B5060447
theorem B157866565 : Blo 1498069 157866565 := bstep (se 4 (by rfl) ⟨14799990, by rfl⟩ : syracuseStep 157866565 = 29599981) B29599981
theorem B11377259 : Blo 1498069 11377259 := bstep (se 1 (by rfl) ⟨8532944, by rfl⟩ : syracuseStep 11377259 = 17065889) B17065889
theorem B2529913 : Blo 1498069 2529913 := bstep (se 2 (by rfl) ⟨948717, by rfl⟩ : syracuseStep 2529913 = 1897435) B1897435
theorem B3373739 : Blo 1498069 3373739 := bstep (se 1 (by rfl) ⟨2530304, by rfl⟩ : syracuseStep 3373739 = 5060609) B5060609
theorem B2529967 : Blo 1498069 2529967 := bstep (se 1 (by rfl) ⟨1897475, by rfl⟩ : syracuseStep 2529967 = 3794951) B3794951
theorem B3201871 : Blo 1498069 3201871 := bstep (se 1 (by rfl) ⟨2401403, by rfl⟩ : syracuseStep 3201871 = 4802807) B4802807
theorem B7207805 : Blo 1498069 7207805 := bstep (se 3 (by rfl) ⟨1351463, by rfl⟩ : syracuseStep 7207805 = 2702927) B2702927
theorem B12327835 : Blo 1498069 12327835 := bstep (se 1 (by rfl) ⟨9245876, by rfl⟩ : syracuseStep 12327835 = 18491753) B18491753
theorem B1498087 : Blo 1498069 1498087 := bstep (se 1 (by rfl) ⟨1123565, by rfl⟩ : syracuseStep 1498087 = 2247131) B2247131
theorem B7199867 : Blo 1498069 7199867 := bstep (se 1 (by rfl) ⟨5399900, by rfl⟩ : syracuseStep 7199867 = 10799801) B10799801
theorem B4054141 : Blo 1498069 4054141 := bstep (se 3 (by rfl) ⟨760151, by rfl⟩ : syracuseStep 4054141 = 1520303) B1520303
theorem B7306363 : Blo 1498069 7306363 := bstep (se 1 (by rfl) ⟨5479772, by rfl⟩ : syracuseStep 7306363 = 10959545) B10959545
theorem B9239741 : Blo 1498069 9239741 := bstep (se 3 (by rfl) ⟨1732451, by rfl⟩ : syracuseStep 9239741 = 3464903) B3464903
theorem B9608381 : Blo 1498069 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B3202247 : Blo 1498069 3202247 := bstep (se 1 (by rfl) ⟨2401685, by rfl⟩ : syracuseStep 3202247 = 4803371) B4803371
theorem B3374279 : Blo 1498069 3374279 := bstep (se 1 (by rfl) ⟨2530709, by rfl⟩ : syracuseStep 3374279 = 5061419) B5061419
theorem B5061851 : Blo 1498069 5061851 := bstep (se 1 (by rfl) ⟨3796388, by rfl⟩ : syracuseStep 5061851 = 7592777) B7592777
theorem B9739531 : Blo 1498069 9739531 := bstep (se 1 (by rfl) ⟨7304648, by rfl⟩ : syracuseStep 9739531 = 14609297) B14609297
theorem B1498399 : Blo 1498069 1498399 := bstep (se 1 (by rfl) ⟨1123799, by rfl⟩ : syracuseStep 1498399 = 2247599) B2247599
theorem B3792167 : Blo 1498069 3792167 := bstep (se 1 (by rfl) ⟨2844125, by rfl⟩ : syracuseStep 3792167 = 5688251) B5688251
theorem B14409035 : Blo 1498069 14409035 := bstep (se 1 (by rfl) ⟨10806776, by rfl⟩ : syracuseStep 14409035 = 21613553) B21613553
theorem B1498459 : Blo 1498069 1498459 := bstep (se 1 (by rfl) ⟨1123844, by rfl⟩ : syracuseStep 1498459 = 2247689) B2247689
theorem B1498479 : Blo 1498069 1498479 := bstep (se 1 (by rfl) ⟨1123859, by rfl⟩ : syracuseStep 1498479 = 2247719) B2247719
theorem B3374459 : Blo 1498069 3374459 := bstep (se 1 (by rfl) ⟨2530844, by rfl⟩ : syracuseStep 3374459 = 5061689) B5061689
theorem B3653003 : Blo 1498069 3653003 := bstep (se 1 (by rfl) ⟨2739752, by rfl⟩ : syracuseStep 3653003 = 5479505) B5479505
theorem B1498535 : Blo 1498069 1498535 := bstep (se 1 (by rfl) ⟨1123901, by rfl⟩ : syracuseStep 1498535 = 2247803) B2247803
theorem B13671929 : Blo 1498069 13671929 := bstep (se 2 (by rfl) ⟨5126973, by rfl⟩ : syracuseStep 13671929 = 10253947) B10253947
theorem B1498619 : Blo 1498069 1498619 := bstep (se 1 (by rfl) ⟨1123964, by rfl⟩ : syracuseStep 1498619 = 2247929) B2247929
theorem B3374585 : Blo 1498069 3374585 := bstep (se 2 (by rfl) ⟨1265469, by rfl⟩ : syracuseStep 3374585 = 2530939) B2530939
theorem B5692943 : Blo 1498069 5692943 := bstep (se 1 (by rfl) ⟨4269707, by rfl⟩ : syracuseStep 5692943 = 8539415) B8539415
theorem B1498687 : Blo 1498069 1498687 := bstep (se 1 (by rfl) ⟨1124015, by rfl⟩ : syracuseStep 1498687 = 2248031) B2248031
theorem B1498695 : Blo 1498069 1498695 := bstep (se 1 (by rfl) ⟨1124021, by rfl⟩ : syracuseStep 1498695 = 2248043) B2248043
theorem B3374675 : Blo 1498069 3374675 := bstep (se 1 (by rfl) ⟨2531006, by rfl⟩ : syracuseStep 3374675 = 5062013) B5062013
theorem B1687135 : Blo 1498069 1687135 := bstep (se 1 (by rfl) ⟨1265351, by rfl⟩ : syracuseStep 1687135 = 2530703) B2530703
theorem B7593587 : Blo 1498069 7593587 := bstep (se 1 (by rfl) ⟨5695190, by rfl⟩ : syracuseStep 7593587 = 11390381) B11390381
theorem B1498847 : Blo 1498069 1498847 := bstep (se 1 (by rfl) ⟨1124135, by rfl⟩ : syracuseStep 1498847 = 2248271) B2248271
theorem B3374855 : Blo 1498069 3374855 := bstep (se 1 (by rfl) ⟨2531141, by rfl⟩ : syracuseStep 3374855 = 5062283) B5062283
theorem B5766923 : Blo 1498069 5766923 := bstep (se 1 (by rfl) ⟨4325192, by rfl⟩ : syracuseStep 5766923 = 8650385) B8650385
theorem B6405929 : Blo 1498069 6405929 := bstep (se 2 (by rfl) ⟨2402223, by rfl⟩ : syracuseStep 6405929 = 4804447) B4804447
theorem B1498927 : Blo 1498069 1498927 := bstep (se 1 (by rfl) ⟨1124195, by rfl⟩ : syracuseStep 1498927 = 2248391) B2248391
theorem B1499035 : Blo 1498069 1499035 := bstep (se 1 (by rfl) ⟨1124276, by rfl⟩ : syracuseStep 1499035 = 2248553) B2248553
theorem B34611137 : Blo 1498069 34611137 := bstep (se 2 (by rfl) ⟨12979176, by rfl⟩ : syracuseStep 34611137 = 25958353) B25958353
theorem B1499087 : Blo 1498069 1499087 := bstep (se 1 (by rfl) ⟨1124315, by rfl⟩ : syracuseStep 1499087 = 2248631) B2248631
theorem B1499111 : Blo 1498069 1499111 := bstep (se 1 (by rfl) ⟨1124333, by rfl⟩ : syracuseStep 1499111 = 2248667) B2248667
theorem B3375143 : Blo 1498069 3375143 := bstep (se 1 (by rfl) ⟨2531357, by rfl⟩ : syracuseStep 3375143 = 5062715) B5062715
theorem B1499367 : Blo 1498069 1499367 := bstep (se 1 (by rfl) ⟨1124525, by rfl⟩ : syracuseStep 1499367 = 2249051) B2249051
theorem B10805507 : Blo 1498069 10805507 := bstep (se 1 (by rfl) ⟨8104130, by rfl⟩ : syracuseStep 10805507 = 16208261) B16208261
theorem B9609587 : Blo 1498069 9609587 := bstep (se 1 (by rfl) ⟨7207190, by rfl⟩ : syracuseStep 9609587 = 14414381) B14414381
theorem B1499519 : Blo 1498069 1499519 := bstep (se 1 (by rfl) ⟨1124639, by rfl⟩ : syracuseStep 1499519 = 2249279) B2249279
theorem B129671603 : Blo 1498069 129671603 := bstep (se 1 (by rfl) ⟨97253702, by rfl⟩ : syracuseStep 129671603 = 194507405) B194507405
theorem B3793351 : Blo 1498069 3793351 := bstep (se 1 (by rfl) ⟨2845013, by rfl⟩ : syracuseStep 3793351 = 5690027) B5690027
theorem B1499599 : Blo 1498069 1499599 := bstep (se 1 (by rfl) ⟨1124699, by rfl⟩ : syracuseStep 1499599 = 2249399) B2249399
theorem B1499751 : Blo 1498069 1499751 := bstep (se 1 (by rfl) ⟨1124813, by rfl⟩ : syracuseStep 1499751 = 2249627) B2249627
theorem B8536751 : Blo 1498069 8536751 := bstep (se 1 (by rfl) ⟨6402563, by rfl⟩ : syracuseStep 8536751 = 12805127) B12805127
theorem B1500015 : Blo 1498069 1500015 := bstep (se 1 (by rfl) ⟨1125011, by rfl⟩ : syracuseStep 1500015 = 2250023) B2250023
theorem B64791515 : Blo 1498069 64791515 := bstep (se 1 (by rfl) ⟨48593636, by rfl⟩ : syracuseStep 64791515 = 97187273) B97187273
theorem B9741341 : Blo 1498069 9741341 := bstep (se 3 (by rfl) ⟨1826501, by rfl⟩ : syracuseStep 9741341 = 3653003) B3653003
theorem B4269161 : Blo 1498069 4269161 := bstep (se 2 (by rfl) ⟨1600935, by rfl⟩ : syracuseStep 4269161 = 3201871) B3201871
theorem B8103077 : Blo 1498069 8103077 := bstep (se 4 (by rfl) ⟨759663, by rfl⟩ : syracuseStep 8103077 = 1519327) B1519327
theorem B27346187 : Blo 1498069 27346187 := bstep (se 1 (by rfl) ⟨20509640, by rfl⟩ : syracuseStep 27346187 = 41019281) B41019281
theorem B9012491 : Blo 1498069 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B6399299 : Blo 1498069 6399299 := bstep (se 1 (by rfl) ⟨4799474, by rfl⟩ : syracuseStep 6399299 = 9598949) B9598949
theorem B10806635 : Blo 1498069 10806635 := bstep (se 1 (by rfl) ⟨8104976, by rfl⟩ : syracuseStep 10806635 = 16209953) B16209953
theorem B5694857 : Blo 1498069 5694857 := bstep (se 2 (by rfl) ⟨2135571, by rfl⟩ : syracuseStep 5694857 = 4271143) B4271143
theorem B9741817 : Blo 1498069 9741817 := bstep (se 2 (by rfl) ⟨3653181, by rfl⟩ : syracuseStep 9741817 = 7306363) B7306363
theorem B5056019 : Blo 1498069 5056019 := bstep (se 1 (by rfl) ⟨3792014, by rfl⟩ : syracuseStep 5056019 = 7584029) B7584029
theorem B2401903 : Blo 1498069 2401903 := bstep (se 1 (by rfl) ⟨1801427, by rfl⟩ : syracuseStep 2401903 = 3602855) B3602855
theorem B2565799 : Blo 1498069 2565799 := bstep (se 1 (by rfl) ⟨1924349, by rfl⟩ : syracuseStep 2565799 = 3848699) B3848699
theorem B12986041 : Blo 1498069 12986041 := bstep (se 2 (by rfl) ⟨4869765, by rfl⟩ : syracuseStep 12986041 = 9739531) B9739531
theorem B4802345 : Blo 1498069 4802345 := bstep (se 2 (by rfl) ⟨1800879, by rfl⟩ : syracuseStep 4802345 = 3601759) B3601759
theorem B164087603 : Blo 1498069 164087603 := bstep (se 1 (by rfl) ⟨123065702, by rfl⟩ : syracuseStep 164087603 = 246131405) B246131405
theorem B15378461 : Blo 1498069 15378461 := bstep (se 3 (by rfl) ⟨2883461, by rfl⟩ : syracuseStep 15378461 = 5766923) B5766923
theorem B19220813 : Blo 1498069 19220813 := bstep (se 3 (by rfl) ⟨3603902, by rfl⟩ : syracuseStep 19220813 = 7207805) B7207805
theorem B3795295 : Blo 1498069 3795295 := bstep (se 1 (by rfl) ⟨2846471, by rfl⟩ : syracuseStep 3795295 = 5692943) B5692943
theorem B55470521 : Blo 1498069 55470521 := bstep (se 2 (by rfl) ⟨20801445, by rfl⟩ : syracuseStep 55470521 = 41602891) B41602891
theorem B4270619 : Blo 1498069 4270619 := bstep (se 1 (by rfl) ⟨3202964, by rfl⟩ : syracuseStep 4270619 = 6405929) B6405929
theorem B2247305 : Blo 1498069 2247305 := bstep (se 2 (by rfl) ⟨842739, by rfl⟩ : syracuseStep 2247305 = 1685479) B1685479
theorem B5057207 : Blo 1498069 5057207 := bstep (se 1 (by rfl) ⟨3792905, by rfl⟩ : syracuseStep 5057207 = 7585811) B7585811
theorem B2247479 : Blo 1498069 2247479 := bstep (se 1 (by rfl) ⟨1685609, by rfl⟩ : syracuseStep 2247479 = 3371219) B3371219
theorem B2247515 : Blo 1498069 2247515 := bstep (se 1 (by rfl) ⟨1685636, by rfl⟩ : syracuseStep 2247515 = 3371273) B3371273
theorem B2247659 : Blo 1498069 2247659 := bstep (se 1 (by rfl) ⟨1685744, by rfl⟩ : syracuseStep 2247659 = 3371489) B3371489
theorem B4803563 : Blo 1498069 4803563 := bstep (se 1 (by rfl) ⟨3602672, by rfl⟩ : syracuseStep 4803563 = 7205345) B7205345
theorem B4869217 : Blo 1498069 4869217 := bstep (se 2 (by rfl) ⟨1825956, by rfl⟩ : syracuseStep 4869217 = 3651913) B3651913
theorem B4271201 : Blo 1498069 4271201 := bstep (se 2 (by rfl) ⟨1601700, by rfl⟩ : syracuseStep 4271201 = 3203401) B3203401
theorem B15379577 : Blo 1498069 15379577 := bstep (se 2 (by rfl) ⟨5767341, by rfl⟩ : syracuseStep 15379577 = 11534683) B11534683
theorem B2247863 : Blo 1498069 2247863 := bstep (se 1 (by rfl) ⟨1685897, by rfl⟩ : syracuseStep 2247863 = 3371795) B3371795
theorem B10800317 : Blo 1498069 10800317 := bstep (se 3 (by rfl) ⟨2025059, by rfl⟩ : syracuseStep 10800317 = 4050119) B4050119
theorem B21622085 : Blo 1498069 21622085 := bstep (se 4 (by rfl) ⟨2027070, by rfl⟩ : syracuseStep 21622085 = 4054141) B4054141
theorem B2248103 : Blo 1498069 2248103 := bstep (se 1 (by rfl) ⟨1686077, by rfl⟩ : syracuseStep 2248103 = 3372155) B3372155
theorem B210488753 : Blo 1498069 210488753 := bstep (se 2 (by rfl) ⟨78933282, by rfl⟩ : syracuseStep 210488753 = 157866565) B157866565
theorem B2248187 : Blo 1498069 2248187 := bstep (se 1 (by rfl) ⟨1686140, by rfl⟩ : syracuseStep 2248187 = 3372281) B3372281
theorem B2248283 : Blo 1498069 2248283 := bstep (se 1 (by rfl) ⟨1686212, by rfl⟩ : syracuseStep 2248283 = 3372425) B3372425
theorem B2248367 : Blo 1498069 2248367 := bstep (se 1 (by rfl) ⟨1686275, by rfl⟩ : syracuseStep 2248367 = 3372551) B3372551
theorem B2248487 : Blo 1498069 2248487 := bstep (se 1 (by rfl) ⟨1686365, by rfl⟩ : syracuseStep 2248487 = 3372731) B3372731
theorem B16437113 : Blo 1498069 16437113 := bstep (se 2 (by rfl) ⟨6163917, by rfl⟩ : syracuseStep 16437113 = 12327835) B12327835
theorem B2248571 : Blo 1498069 2248571 := bstep (se 1 (by rfl) ⟨1686428, by rfl⟩ : syracuseStep 2248571 = 3372857) B3372857
theorem B3370895 : Blo 1498069 3370895 := bstep (se 1 (by rfl) ⟨2528171, by rfl⟩ : syracuseStep 3370895 = 5056343) B5056343
theorem B11390867 : Blo 1498069 11390867 := bstep (se 1 (by rfl) ⟨8543150, by rfl⟩ : syracuseStep 11390867 = 17086301) B17086301
theorem B7303085 : Blo 1498069 7303085 := bstep (se 3 (by rfl) ⟨1369328, by rfl⟩ : syracuseStep 7303085 = 2738657) B2738657
theorem B2248991 : Blo 1498069 2248991 := bstep (se 1 (by rfl) ⟨1686743, by rfl⟩ : syracuseStep 2248991 = 3373487) B3373487
theorem B3846455 : Blo 1498069 3846455 := bstep (se 1 (by rfl) ⟨2884841, by rfl⟩ : syracuseStep 3846455 = 5769683) B5769683
theorem B4559159 : Blo 1498069 4559159 := bstep (se 1 (by rfl) ⟨3419369, by rfl⟩ : syracuseStep 4559159 = 6838739) B6838739
theorem B2249015 : Blo 1498069 2249015 := bstep (se 1 (by rfl) ⟨1686761, by rfl⟩ : syracuseStep 2249015 = 3373523) B3373523
theorem B2249087 : Blo 1498069 2249087 := bstep (se 1 (by rfl) ⟨1686815, by rfl⟩ : syracuseStep 2249087 = 3373631) B3373631
theorem B2249159 : Blo 1498069 2249159 := bstep (se 1 (by rfl) ⟨1686869, by rfl⟩ : syracuseStep 2249159 = 3373739) B3373739
theorem B5059151 : Blo 1498069 5059151 := bstep (se 1 (by rfl) ⟨3794363, by rfl⟩ : syracuseStep 5059151 = 7588727) B7588727
theorem B3371615 : Blo 1498069 3371615 := bstep (se 1 (by rfl) ⟨2528711, by rfl⟩ : syracuseStep 3371615 = 5057423) B5057423
theorem B2249513 : Blo 1498069 2249513 := bstep (se 2 (by rfl) ⟨843567, by rfl⟩ : syracuseStep 2249513 = 1687135) B1687135
theorem B2134831 : Blo 1498069 2134831 := bstep (se 1 (by rfl) ⟨1601123, by rfl⟩ : syracuseStep 2134831 = 3202247) B3202247
theorem B2249519 : Blo 1498069 2249519 := bstep (se 1 (by rfl) ⟨1687139, by rfl⟩ : syracuseStep 2249519 = 3374279) B3374279
theorem B2528057 : Blo 1498069 2528057 := bstep (se 2 (by rfl) ⟨948021, by rfl⟩ : syracuseStep 2528057 = 1896043) B1896043
theorem B2528111 : Blo 1498069 2528111 := bstep (se 1 (by rfl) ⟨1896083, by rfl⟩ : syracuseStep 2528111 = 3792167) B3792167
theorem B9606023 : Blo 1498069 9606023 := bstep (se 1 (by rfl) ⟨7204517, by rfl⟩ : syracuseStep 9606023 = 14409035) B14409035
theorem B2249639 : Blo 1498069 2249639 := bstep (se 1 (by rfl) ⟨1687229, by rfl⟩ : syracuseStep 2249639 = 3374459) B3374459
theorem B48608171 : Blo 1498069 48608171 := bstep (se 1 (by rfl) ⟨36456128, by rfl⟩ : syracuseStep 48608171 = 72912257) B72912257
theorem B9114619 : Blo 1498069 9114619 := bstep (se 1 (by rfl) ⟨6835964, by rfl⟩ : syracuseStep 9114619 = 13671929) B13671929
theorem B2249723 : Blo 1498069 2249723 := bstep (se 1 (by rfl) ⟨1687292, by rfl⟩ : syracuseStep 2249723 = 3374585) B3374585
theorem B2249783 : Blo 1498069 2249783 := bstep (se 1 (by rfl) ⟨1687337, by rfl⟩ : syracuseStep 2249783 = 3374675) B3374675
theorem B5059691 : Blo 1498069 5059691 := bstep (se 1 (by rfl) ⟨3794768, by rfl⟩ : syracuseStep 5059691 = 7589537) B7589537
theorem B2249903 : Blo 1498069 2249903 := bstep (se 1 (by rfl) ⟨1687427, by rfl⟩ : syracuseStep 2249903 = 3374855) B3374855
theorem B25605395 : Blo 1498069 25605395 := bstep (se 1 (by rfl) ⟨19204046, by rfl⟩ : syracuseStep 25605395 = 38408093) B38408093
theorem B23074091 : Blo 1498069 23074091 := bstep (se 1 (by rfl) ⟨17305568, by rfl⟩ : syracuseStep 23074091 = 34611137) B34611137
theorem B8533309 : Blo 1498069 8533309 := bstep (se 3 (by rfl) ⟨1599995, by rfl⟩ : syracuseStep 8533309 = 3199991) B3199991
theorem B4052315 : Blo 1498069 4052315 := bstep (se 1 (by rfl) ⟨3039236, by rfl⟩ : syracuseStep 4052315 = 6078473) B6078473
theorem B20510081 : Blo 1498069 20510081 := bstep (se 2 (by rfl) ⟨7691280, by rfl⟩ : syracuseStep 20510081 = 15382561) B15382561
theorem B3372443 : Blo 1498069 3372443 := bstep (se 1 (by rfl) ⟨2529332, by rfl⟩ : syracuseStep 3372443 = 5058665) B5058665
theorem B34600409 : Blo 1498069 34600409 := bstep (se 2 (by rfl) ⟨12975153, by rfl⟩ : syracuseStep 34600409 = 25950307) B25950307
theorem B4052663 : Blo 1498069 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B10254059 : Blo 1498069 10254059 := bstep (se 1 (by rfl) ⟨7690544, by rfl⟩ : syracuseStep 10254059 = 15381089) B15381089
theorem B9606923 : Blo 1498069 9606923 := bstep (se 1 (by rfl) ⟨7205192, by rfl⟩ : syracuseStep 9606923 = 14410385) B14410385
theorem B2529103 : Blo 1498069 2529103 := bstep (se 1 (by rfl) ⟨1896827, by rfl⟩ : syracuseStep 2529103 = 3793655) B3793655
theorem B18233225 : Blo 1498069 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B3373019 : Blo 1498069 3373019 := bstep (se 1 (by rfl) ⟨2529764, by rfl⟩ : syracuseStep 3373019 = 5059529) B5059529
theorem B19216349 : Blo 1498069 19216349 := bstep (se 3 (by rfl) ⟨3603065, by rfl⟩ : syracuseStep 19216349 = 7206131) B7206131
theorem B3373199 : Blo 1498069 3373199 := bstep (se 1 (by rfl) ⟨2529899, by rfl⟩ : syracuseStep 3373199 = 5059799) B5059799
theorem B1685659 : Blo 1498069 1685659 := bstep (se 1 (by rfl) ⟨1264244, by rfl⟩ : syracuseStep 1685659 = 2528489) B2528489
theorem B3373217 : Blo 1498069 3373217 := bstep (se 2 (by rfl) ⟨1264956, by rfl⟩ : syracuseStep 3373217 = 2529913) B2529913
theorem B1685695 : Blo 1498069 1685695 := bstep (se 1 (by rfl) ⟨1264271, by rfl⟩ : syracuseStep 1685695 = 2528543) B2528543
theorem B3373289 : Blo 1498069 3373289 := bstep (se 2 (by rfl) ⟨1264983, by rfl⟩ : syracuseStep 3373289 = 2529967) B2529967
theorem B2529515 : Blo 1498069 2529515 := bstep (se 1 (by rfl) ⟨1897136, by rfl⟩ : syracuseStep 2529515 = 3794273) B3794273
theorem B5060987 : Blo 1498069 5060987 := bstep (se 1 (by rfl) ⟨3795740, by rfl⟩ : syracuseStep 5060987 = 7591481) B7591481
theorem B4266553 : Blo 1498069 4266553 := bstep (se 2 (by rfl) ⟨1599957, by rfl⟩ : syracuseStep 4266553 = 3199915) B3199915
theorem B8534585 : Blo 1498069 8534585 := bstep (se 2 (by rfl) ⟨3200469, by rfl⟩ : syracuseStep 8534585 = 6400939) B6400939
theorem B5061257 : Blo 1498069 5061257 := bstep (se 2 (by rfl) ⟨1897971, by rfl⟩ : syracuseStep 5061257 = 3795943) B3795943
theorem B8649551 : Blo 1498069 8649551 := bstep (se 1 (by rfl) ⟨6487163, by rfl⟩ : syracuseStep 8649551 = 12974327) B12974327
theorem B7199597 : Blo 1498069 7199597 := bstep (se 3 (by rfl) ⟨1349924, by rfl⟩ : syracuseStep 7199597 = 2699849) B2699849
theorem B2530345 : Blo 1498069 2530345 := bstep (se 2 (by rfl) ⟨948879, by rfl⟩ : syracuseStep 2530345 = 1897759) B1897759
theorem B1498159 : Blo 1498069 1498159 := bstep (se 1 (by rfl) ⟨1123619, by rfl⟩ : syracuseStep 1498159 = 2247239) B2247239
theorem B1498183 : Blo 1498069 1498183 := bstep (se 1 (by rfl) ⟨1123637, by rfl⟩ : syracuseStep 1498183 = 2247275) B2247275
theorem B7584839 : Blo 1498069 7584839 := bstep (se 1 (by rfl) ⟨5688629, by rfl⟩ : syracuseStep 7584839 = 11377259) B11377259
theorem B3792055 : Blo 1498069 3792055 := bstep (se 1 (by rfl) ⟨2844041, by rfl⟩ : syracuseStep 3792055 = 5688083) B5688083
theorem B2530487 : Blo 1498069 2530487 := bstep (se 1 (by rfl) ⟨1897865, by rfl⟩ : syracuseStep 2530487 = 3795731) B3795731
theorem B1498335 : Blo 1498069 1498335 := bstep (se 1 (by rfl) ⟨1123751, by rfl⟩ : syracuseStep 1498335 = 2247503) B2247503
theorem B54680993 : Blo 1498069 54680993 := bstep (se 2 (by rfl) ⟨20505372, by rfl⟩ : syracuseStep 54680993 = 41010745) B41010745
theorem B4799911 : Blo 1498069 4799911 := bstep (se 1 (by rfl) ⟨3599933, by rfl⟩ : syracuseStep 4799911 = 7199867) B7199867
theorem B4267475 : Blo 1498069 4267475 := bstep (se 1 (by rfl) ⟨3200606, by rfl⟩ : syracuseStep 4267475 = 6401213) B6401213
theorem B6159827 : Blo 1498069 6159827 := bstep (se 1 (by rfl) ⟨4619870, by rfl⟩ : syracuseStep 6159827 = 9239741) B9239741
theorem B6405587 : Blo 1498069 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B3792359 : Blo 1498069 3792359 := bstep (se 1 (by rfl) ⟨2844269, by rfl⟩ : syracuseStep 3792359 = 5688539) B5688539
theorem B1498599 : Blo 1498069 1498599 := bstep (se 1 (by rfl) ⟨1123949, by rfl⟩ : syracuseStep 1498599 = 2247899) B2247899
theorem B3374567 : Blo 1498069 3374567 := bstep (se 1 (by rfl) ⟨2530925, by rfl⟩ : syracuseStep 3374567 = 5061851) B5061851
theorem B2530811 : Blo 1498069 2530811 := bstep (se 1 (by rfl) ⟨1898108, by rfl⟩ : syracuseStep 2530811 = 3796217) B3796217
theorem B28818989 : Blo 1498069 28818989 := bstep (se 3 (by rfl) ⟨5403560, by rfl⟩ : syracuseStep 28818989 = 10807121) B10807121
theorem B1498715 : Blo 1498069 1498715 := bstep (se 1 (by rfl) ⟨1124036, by rfl⟩ : syracuseStep 1498715 = 2248073) B2248073
theorem B38002391 : Blo 1498069 38002391 := bstep (se 1 (by rfl) ⟨28501793, by rfl⟩ : syracuseStep 38002391 = 57003587) B57003587
theorem B5062391 : Blo 1498069 5062391 := bstep (se 1 (by rfl) ⟨3796793, by rfl⟩ : syracuseStep 5062391 = 7593587) B7593587
theorem B1498951 : Blo 1498069 1498951 := bstep (se 1 (by rfl) ⟨1124213, by rfl⟩ : syracuseStep 1498951 = 2248427) B2248427
theorem B2531243 : Blo 1498069 2531243 := bstep (se 1 (by rfl) ⟨1898432, by rfl⟩ : syracuseStep 2531243 = 3796865) B3796865
theorem B16203725 : Blo 1498069 16203725 := bstep (se 3 (by rfl) ⟨3038198, by rfl⟩ : syracuseStep 16203725 = 6076397) B6076397
theorem B1499103 : Blo 1498069 1499103 := bstep (se 1 (by rfl) ⟨1124327, by rfl⟩ : syracuseStep 1499103 = 2248655) B2248655
theorem B25976909 : Blo 1498069 25976909 := bstep (se 3 (by rfl) ⟨4870670, by rfl⟩ : syracuseStep 25976909 = 9741341) B9741341
theorem B1499327 : Blo 1498069 1499327 := bstep (se 1 (by rfl) ⟨1124495, by rfl⟩ : syracuseStep 1499327 = 2248991) B2248991
theorem B2564303 : Blo 1498069 2564303 := bstep (se 1 (by rfl) ⟨1923227, by rfl⟩ : syracuseStep 2564303 = 3846455) B3846455
theorem B3039439 : Blo 1498069 3039439 := bstep (se 1 (by rfl) ⟨2279579, by rfl⟩ : syracuseStep 3039439 = 4559159) B4559159
theorem B1499343 : Blo 1498069 1499343 := bstep (se 1 (by rfl) ⟨1124507, by rfl⟩ : syracuseStep 1499343 = 2249015) B2249015
theorem B6406391 : Blo 1498069 6406391 := bstep (se 1 (by rfl) ⟨4804793, by rfl⟩ : syracuseStep 6406391 = 9609587) B9609587
theorem B1499391 : Blo 1498069 1499391 := bstep (se 1 (by rfl) ⟨1124543, by rfl⟩ : syracuseStep 1499391 = 2249087) B2249087
theorem B1499439 : Blo 1498069 1499439 := bstep (se 1 (by rfl) ⟨1124579, by rfl⟩ : syracuseStep 1499439 = 2249159) B2249159
theorem B25969157 : Blo 1498069 25969157 := bstep (se 4 (by rfl) ⟨2434608, by rfl⟩ : syracuseStep 25969157 = 4869217) B4869217
theorem B1499675 : Blo 1498069 1499675 := bstep (se 1 (by rfl) ⟨1124756, by rfl⟩ : syracuseStep 1499675 = 2249513) B2249513
theorem B1499679 : Blo 1498069 1499679 := bstep (se 1 (by rfl) ⟨1124759, by rfl⟩ : syracuseStep 1499679 = 2249519) B2249519
theorem B1499759 : Blo 1498069 1499759 := bstep (se 1 (by rfl) ⟨1124819, by rfl⟩ : syracuseStep 1499759 = 2249639) B2249639
theorem B1499815 : Blo 1498069 1499815 := bstep (se 1 (by rfl) ⟨1124861, by rfl⟩ : syracuseStep 1499815 = 2249723) B2249723
theorem B1499855 : Blo 1498069 1499855 := bstep (se 1 (by rfl) ⟨1124891, by rfl⟩ : syracuseStep 1499855 = 2249783) B2249783
theorem B1499935 : Blo 1498069 1499935 := bstep (se 1 (by rfl) ⟨1124951, by rfl⟩ : syracuseStep 1499935 = 2249903) B2249903
theorem B10806173 : Blo 1498069 10806173 := bstep (se 3 (by rfl) ⟨2026157, by rfl⟩ : syracuseStep 10806173 = 4052315) B4052315
theorem B13673387 : Blo 1498069 13673387 := bstep (se 1 (by rfl) ⟨10255040, by rfl⟩ : syracuseStep 13673387 = 20510081) B20510081
theorem B16426205 : Blo 1498069 16426205 := bstep (se 3 (by rfl) ⟨3079913, by rfl⟩ : syracuseStep 16426205 = 6159827) B6159827
theorem B12813875 : Blo 1498069 12813875 := bstep (se 1 (by rfl) ⟨9610406, by rfl⟩ : syracuseStep 12813875 = 19220813) B19220813
theorem B5056073 : Blo 1498069 5056073 := bstep (se 2 (by rfl) ⟨1896027, by rfl⟩ : syracuseStep 5056073 = 3792055) B3792055
theorem B77899573 : Blo 1498069 77899573 := bstep (se 5 (by rfl) ⟨3651542, by rfl⟩ : syracuseStep 77899573 = 7303085) B7303085
theorem B6399881 : Blo 1498069 6399881 := bstep (se 2 (by rfl) ⟨2399955, by rfl⟩ : syracuseStep 6399881 = 4799911) B4799911
theorem B5056559 : Blo 1498069 5056559 := bstep (se 1 (by rfl) ⟨3792419, by rfl⟩ : syracuseStep 5056559 = 7584839) B7584839
theorem B2844983 : Blo 1498069 2844983 := bstep (se 1 (by rfl) ⟨2133737, by rfl⟩ : syracuseStep 2844983 = 4267475) B4267475
theorem B4270391 : Blo 1498069 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B19212659 : Blo 1498069 19212659 := bstep (se 1 (by rfl) ⟨14409494, by rfl⟩ : syracuseStep 19212659 = 28818989) B28818989
theorem B2247263 : Blo 1498069 2247263 := bstep (se 1 (by rfl) ⟨1685447, by rfl⟩ : syracuseStep 2247263 = 3370895) B3370895
theorem B7203671 : Blo 1498069 7203671 := bstep (se 1 (by rfl) ⟨5402753, by rfl⟩ : syracuseStep 7203671 = 10805507) B10805507
theorem B2247545 : Blo 1498069 2247545 := bstep (se 2 (by rfl) ⟨842829, by rfl⟩ : syracuseStep 2247545 = 1685659) B1685659
theorem B2247593 : Blo 1498069 2247593 := bstep (se 2 (by rfl) ⟨842847, by rfl⟩ : syracuseStep 2247593 = 1685695) B1685695
theorem B2247743 : Blo 1498069 2247743 := bstep (se 1 (by rfl) ⟨1685807, by rfl⟩ : syracuseStep 2247743 = 3371615) B3371615
theorem B5057801 : Blo 1498069 5057801 := bstep (se 2 (by rfl) ⟨1896675, by rfl⟩ : syracuseStep 5057801 = 3793351) B3793351
theorem B2846107 : Blo 1498069 2846107 := bstep (se 1 (by rfl) ⟨2134580, by rfl⟩ : syracuseStep 2846107 = 4269161) B4269161
theorem B5688737 : Blo 1498069 5688737 := bstep (se 2 (by rfl) ⟨2133276, by rfl⟩ : syracuseStep 5688737 = 4266553) B4266553
theorem B5402051 : Blo 1498069 5402051 := bstep (se 1 (by rfl) ⟨4051538, by rfl⟩ : syracuseStep 5402051 = 8103077) B8103077
theorem B18230791 : Blo 1498069 18230791 := bstep (se 1 (by rfl) ⟨13673093, by rfl⟩ : syracuseStep 18230791 = 27346187) B27346187
theorem B6008327 : Blo 1498069 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B13684261 : Blo 1498069 13684261 := bstep (se 4 (by rfl) ⟨1282899, by rfl⟩ : syracuseStep 13684261 = 2565799) B2565799
theorem B7204423 : Blo 1498069 7204423 := bstep (se 1 (by rfl) ⟨5403317, by rfl⟩ : syracuseStep 7204423 = 10806635) B10806635
theorem B3796571 : Blo 1498069 3796571 := bstep (se 1 (by rfl) ⟨2847428, by rfl⟩ : syracuseStep 3796571 = 5694857) B5694857
theorem B2248295 : Blo 1498069 2248295 := bstep (se 1 (by rfl) ⟨1686221, by rfl⟩ : syracuseStep 2248295 = 3372443) B3372443
theorem B3370679 : Blo 1498069 3370679 := bstep (se 1 (by rfl) ⟨2528009, by rfl⟩ : syracuseStep 3370679 = 5056019) B5056019
theorem B2846441 : Blo 1498069 2846441 := bstep (se 2 (by rfl) ⟨1067415, by rfl⟩ : syracuseStep 2846441 = 2134831) B2134831
theorem B561303341 : Blo 1498069 561303341 := bstep (se 3 (by rfl) ⟨105244376, by rfl⟩ : syracuseStep 561303341 = 210488753) B210488753
theorem B6836039 : Blo 1498069 6836039 := bstep (se 1 (by rfl) ⟨5127029, by rfl⟩ : syracuseStep 6836039 = 10254059) B10254059
theorem B109391735 : Blo 1498069 109391735 := bstep (se 1 (by rfl) ⟨82043801, by rfl⟩ : syracuseStep 109391735 = 164087603) B164087603
theorem B2248679 : Blo 1498069 2248679 := bstep (se 1 (by rfl) ⟨1686509, by rfl⟩ : syracuseStep 2248679 = 3373019) B3373019
theorem B12152825 : Blo 1498069 12152825 := bstep (se 2 (by rfl) ⟨4557309, by rfl⟩ : syracuseStep 12152825 = 9114619) B9114619
theorem B10252307 : Blo 1498069 10252307 := bstep (se 1 (by rfl) ⟨7689230, by rfl⟩ : syracuseStep 10252307 = 15378461) B15378461
theorem B2248799 : Blo 1498069 2248799 := bstep (se 1 (by rfl) ⟨1686599, by rfl⟩ : syracuseStep 2248799 = 3373199) B3373199
theorem B2248811 : Blo 1498069 2248811 := bstep (se 1 (by rfl) ⟨1686608, by rfl⟩ : syracuseStep 2248811 = 3373217) B3373217
theorem B2248859 : Blo 1498069 2248859 := bstep (se 1 (by rfl) ⟨1686644, by rfl⟩ : syracuseStep 2248859 = 3373289) B3373289
theorem B2847079 : Blo 1498069 2847079 := bstep (se 1 (by rfl) ⟨2135309, by rfl⟩ : syracuseStep 2847079 = 4270619) B4270619
theorem B5689723 : Blo 1498069 5689723 := bstep (se 1 (by rfl) ⟨4267292, by rfl⟩ : syracuseStep 5689723 = 8534585) B8534585
theorem B3371471 : Blo 1498069 3371471 := bstep (se 1 (by rfl) ⟨2528603, by rfl⟩ : syracuseStep 3371471 = 5057207) B5057207
theorem B12989089 : Blo 1498069 12989089 := bstep (se 2 (by rfl) ⟨4870908, by rfl⟩ : syracuseStep 12989089 = 9741817) B9741817
theorem B2847467 : Blo 1498069 2847467 := bstep (se 1 (by rfl) ⟨2135600, by rfl⟩ : syracuseStep 2847467 = 4271201) B4271201
theorem B10253051 : Blo 1498069 10253051 := bstep (se 1 (by rfl) ⟨7689788, by rfl⟩ : syracuseStep 10253051 = 15379577) B15379577
theorem B23065469 : Blo 1498069 23065469 := bstep (se 3 (by rfl) ⟨4324775, by rfl⟩ : syracuseStep 23065469 = 8649551) B8649551
theorem B14414723 : Blo 1498069 14414723 := bstep (se 1 (by rfl) ⟨10811042, by rfl⟩ : syracuseStep 14414723 = 21622085) B21622085
theorem B17314721 : Blo 1498069 17314721 := bstep (se 2 (by rfl) ⟨6493020, by rfl⟩ : syracuseStep 17314721 = 12986041) B12986041
theorem B2528239 : Blo 1498069 2528239 := bstep (se 1 (by rfl) ⟨1896179, by rfl⟩ : syracuseStep 2528239 = 3792359) B3792359
theorem B2249711 : Blo 1498069 2249711 := bstep (se 1 (by rfl) ⟨1687283, by rfl⟩ : syracuseStep 2249711 = 3374567) B3374567
theorem B3372137 : Blo 1498069 3372137 := bstep (se 2 (by rfl) ⟨1264551, by rfl⟩ : syracuseStep 3372137 = 2529103) B2529103
theorem B25334927 : Blo 1498069 25334927 := bstep (se 1 (by rfl) ⟨19001195, by rfl⟩ : syracuseStep 25334927 = 38002391) B38002391
theorem B10958075 : Blo 1498069 10958075 := bstep (se 1 (by rfl) ⟨8218556, by rfl⟩ : syracuseStep 10958075 = 16437113) B16437113
theorem B12809501 : Blo 1498069 12809501 := bstep (se 3 (by rfl) ⟨2401781, by rfl⟩ : syracuseStep 12809501 = 4803563) B4803563
theorem B10802483 : Blo 1498069 10802483 := bstep (se 1 (by rfl) ⟨8101862, by rfl⟩ : syracuseStep 10802483 = 16203725) B16203725
theorem B2250095 : Blo 1498069 2250095 := bstep (se 1 (by rfl) ⟨1687571, by rfl⟩ : syracuseStep 2250095 = 3375143) B3375143
theorem B86447735 : Blo 1498069 86447735 := bstep (se 1 (by rfl) ⟨64835801, by rfl⟩ : syracuseStep 86447735 = 129671603) B129671603
theorem B3372767 : Blo 1498069 3372767 := bstep (se 1 (by rfl) ⟨2529575, by rfl⟩ : syracuseStep 3372767 = 5059151) B5059151
theorem B5691167 : Blo 1498069 5691167 := bstep (se 1 (by rfl) ⟨4268375, by rfl⟩ : syracuseStep 5691167 = 8536751) B8536751
theorem B5060393 : Blo 1498069 5060393 := bstep (se 2 (by rfl) ⟨1897647, by rfl⟩ : syracuseStep 5060393 = 3795295) B3795295
theorem B28800845 : Blo 1498069 28800845 := bstep (se 3 (by rfl) ⟨5400158, by rfl⟩ : syracuseStep 28800845 = 10800317) B10800317
theorem B1685371 : Blo 1498069 1685371 := bstep (se 1 (by rfl) ⟨1264028, by rfl⟩ : syracuseStep 1685371 = 2528057) B2528057
theorem B1685407 : Blo 1498069 1685407 := bstep (se 1 (by rfl) ⟨1264055, by rfl⟩ : syracuseStep 1685407 = 2528111) B2528111
theorem B12810149 : Blo 1498069 12810149 := bstep (se 4 (by rfl) ⟨1200951, by rfl⟩ : syracuseStep 12810149 = 2401903) B2401903
theorem B6404015 : Blo 1498069 6404015 := bstep (se 1 (by rfl) ⟨4803011, by rfl⟩ : syracuseStep 6404015 = 9606023) B9606023
theorem B32405447 : Blo 1498069 32405447 := bstep (se 1 (by rfl) ⟨24304085, by rfl⟩ : syracuseStep 32405447 = 48608171) B48608171
theorem B43194343 : Blo 1498069 43194343 := bstep (se 1 (by rfl) ⟨32395757, by rfl⟩ : syracuseStep 43194343 = 64791515) B64791515
theorem B3373127 : Blo 1498069 3373127 := bstep (se 1 (by rfl) ⟨2529845, by rfl⟩ : syracuseStep 3373127 = 5059691) B5059691
theorem B17070263 : Blo 1498069 17070263 := bstep (se 1 (by rfl) ⟨12802697, by rfl⟩ : syracuseStep 17070263 = 25605395) B25605395
theorem B15382727 : Blo 1498069 15382727 := bstep (se 1 (by rfl) ⟨11537045, by rfl⟩ : syracuseStep 15382727 = 23074091) B23074091
theorem B4266199 : Blo 1498069 4266199 := bstep (se 1 (by rfl) ⟨3199649, by rfl⟩ : syracuseStep 4266199 = 6399299) B6399299
theorem B23066939 : Blo 1498069 23066939 := bstep (se 1 (by rfl) ⟨17300204, by rfl⟩ : syracuseStep 23066939 = 34600409) B34600409
theorem B2701775 : Blo 1498069 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B147921389 : Blo 1498069 147921389 := bstep (se 3 (by rfl) ⟨27735260, by rfl⟩ : syracuseStep 147921389 = 55470521) B55470521
theorem B6404615 : Blo 1498069 6404615 := bstep (se 1 (by rfl) ⟨4803461, by rfl⟩ : syracuseStep 6404615 = 9606923) B9606923
theorem B3201563 : Blo 1498069 3201563 := bstep (se 1 (by rfl) ⟨2401172, by rfl⟩ : syracuseStep 3201563 = 4802345) B4802345
theorem B12155483 : Blo 1498069 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B12810899 : Blo 1498069 12810899 := bstep (se 1 (by rfl) ⟨9608174, by rfl⟩ : syracuseStep 12810899 = 19216349) B19216349
theorem B3373793 : Blo 1498069 3373793 := bstep (se 2 (by rfl) ⟨1265172, by rfl⟩ : syracuseStep 3373793 = 2530345) B2530345
theorem B1686343 : Blo 1498069 1686343 := bstep (se 1 (by rfl) ⟨1264757, by rfl⟩ : syracuseStep 1686343 = 2529515) B2529515
theorem B3373991 : Blo 1498069 3373991 := bstep (se 1 (by rfl) ⟨2530493, by rfl⟩ : syracuseStep 3373991 = 5060987) B5060987
theorem B11377745 : Blo 1498069 11377745 := bstep (se 2 (by rfl) ⟨4266654, by rfl⟩ : syracuseStep 11377745 = 8533309) B8533309
theorem B1498203 : Blo 1498069 1498203 := bstep (se 1 (by rfl) ⟨1123652, by rfl⟩ : syracuseStep 1498203 = 2247305) B2247305
theorem B3374171 : Blo 1498069 3374171 := bstep (se 1 (by rfl) ⟨2530628, by rfl⟩ : syracuseStep 3374171 = 5061257) B5061257
theorem B1498319 : Blo 1498069 1498319 := bstep (se 1 (by rfl) ⟨1123739, by rfl⟩ : syracuseStep 1498319 = 2247479) B2247479
theorem B1498343 : Blo 1498069 1498343 := bstep (se 1 (by rfl) ⟨1123757, by rfl⟩ : syracuseStep 1498343 = 2247515) B2247515
theorem B4799731 : Blo 1498069 4799731 := bstep (se 1 (by rfl) ⟨3599798, by rfl⟩ : syracuseStep 4799731 = 7199597) B7199597
theorem B1498439 : Blo 1498069 1498439 := bstep (se 1 (by rfl) ⟨1123829, by rfl⟩ : syracuseStep 1498439 = 2247659) B2247659
theorem B1498575 : Blo 1498069 1498575 := bstep (se 1 (by rfl) ⟨1123931, by rfl⟩ : syracuseStep 1498575 = 2247863) B2247863
theorem B1686991 : Blo 1498069 1686991 := bstep (se 1 (by rfl) ⟨1265243, by rfl⟩ : syracuseStep 1686991 = 2530487) B2530487
theorem B36453995 : Blo 1498069 36453995 := bstep (se 1 (by rfl) ⟨27340496, by rfl⟩ : syracuseStep 36453995 = 54680993) B54680993
theorem B1498735 : Blo 1498069 1498735 := bstep (se 1 (by rfl) ⟨1124051, by rfl⟩ : syracuseStep 1498735 = 2248103) B2248103
theorem B1498791 : Blo 1498069 1498791 := bstep (se 1 (by rfl) ⟨1124093, by rfl⟩ : syracuseStep 1498791 = 2248187) B2248187
theorem B1687207 : Blo 1498069 1687207 := bstep (se 1 (by rfl) ⟨1265405, by rfl⟩ : syracuseStep 1687207 = 2530811) B2530811
theorem B1498855 : Blo 1498069 1498855 := bstep (se 1 (by rfl) ⟨1124141, by rfl⟩ : syracuseStep 1498855 = 2248283) B2248283
theorem B1498911 : Blo 1498069 1498911 := bstep (se 1 (by rfl) ⟨1124183, by rfl⟩ : syracuseStep 1498911 = 2248367) B2248367
theorem B3374927 : Blo 1498069 3374927 := bstep (se 1 (by rfl) ⟨2531195, by rfl⟩ : syracuseStep 3374927 = 5062391) B5062391
theorem B1498991 : Blo 1498069 1498991 := bstep (se 1 (by rfl) ⟨1124243, by rfl⟩ : syracuseStep 1498991 = 2248487) B2248487
theorem B1499047 : Blo 1498069 1499047 := bstep (se 1 (by rfl) ⟨1124285, by rfl⟩ : syracuseStep 1499047 = 2248571) B2248571
theorem B7593911 : Blo 1498069 7593911 := bstep (se 1 (by rfl) ⟨5695433, by rfl⟩ : syracuseStep 7593911 = 11390867) B11390867
theorem B1687495 : Blo 1498069 1687495 := bstep (se 1 (by rfl) ⟨1265621, by rfl⟩ : syracuseStep 1687495 = 2531243) B2531243
theorem B1499199 : Blo 1498069 1499199 := bstep (se 1 (by rfl) ⟨1124399, by rfl⟩ : syracuseStep 1499199 = 2248799) B2248799
theorem B1499207 : Blo 1498069 1499207 := bstep (se 1 (by rfl) ⟨1124405, by rfl⟩ : syracuseStep 1499207 = 2248811) B2248811
theorem B1499239 : Blo 1498069 1499239 := bstep (se 1 (by rfl) ⟨1124429, by rfl⟩ : syracuseStep 1499239 = 2248859) B2248859
theorem B69271757 : Blo 1498069 69271757 := bstep (se 3 (by rfl) ⟨12988454, by rfl⟩ : syracuseStep 69271757 = 25976909) B25976909
theorem B7586297 : Blo 1498069 7586297 := bstep (se 2 (by rfl) ⟨2844861, by rfl⟩ : syracuseStep 7586297 = 5689723) B5689723
theorem B15376979 : Blo 1498069 15376979 := bstep (se 1 (by rfl) ⟨11532734, by rfl⟩ : syracuseStep 15376979 = 23065469) B23065469
theorem B9609815 : Blo 1498069 9609815 := bstep (se 1 (by rfl) ⟨7207361, by rfl⟩ : syracuseStep 9609815 = 14414723) B14414723
theorem B11543147 : Blo 1498069 11543147 := bstep (se 1 (by rfl) ⟨8657360, by rfl⟩ : syracuseStep 11543147 = 17314721) B17314721
theorem B1499807 : Blo 1498069 1499807 := bstep (se 1 (by rfl) ⟨1124855, by rfl⟩ : syracuseStep 1499807 = 2249711) B2249711
theorem B7586621 : Blo 1498069 7586621 := bstep (se 3 (by rfl) ⟨1422491, by rfl⟩ : syracuseStep 7586621 = 2844983) B2844983
theorem B7201655 : Blo 1498069 7201655 := bstep (se 1 (by rfl) ⟨5401241, by rfl⟩ : syracuseStep 7201655 = 10802483) B10802483
theorem B17318785 : Blo 1498069 17318785 := bstep (se 2 (by rfl) ⟨6494544, by rfl⟩ : syracuseStep 17318785 = 12989089) B12989089
theorem B1500063 : Blo 1498069 1500063 := bstep (se 1 (by rfl) ⟨1125047, by rfl⟩ : syracuseStep 1500063 = 2250095) B2250095
theorem B57631823 : Blo 1498069 57631823 := bstep (se 1 (by rfl) ⟨43223867, by rfl⟩ : syracuseStep 57631823 = 86447735) B86447735
theorem B3794111 : Blo 1498069 3794111 := bstep (se 1 (by rfl) ⟨2845583, by rfl⟩ : syracuseStep 3794111 = 5691167) B5691167
theorem B4269343 : Blo 1498069 4269343 := bstep (se 1 (by rfl) ⟨3202007, by rfl⟩ : syracuseStep 4269343 = 6404015) B6404015
theorem B21603631 : Blo 1498069 21603631 := bstep (se 1 (by rfl) ⟨16202723, by rfl⟩ : syracuseStep 21603631 = 32405447) B32405447
theorem B8537501 : Blo 1498069 8537501 := bstep (se 3 (by rfl) ⟨1600781, by rfl⟩ : syracuseStep 8537501 = 3201563) B3201563
theorem B11380175 : Blo 1498069 11380175 := bstep (se 1 (by rfl) ⟨8535131, by rfl⟩ : syracuseStep 11380175 = 17070263) B17070263
theorem B15377959 : Blo 1498069 15377959 := bstep (se 1 (by rfl) ⟨11533469, by rfl⟩ : syracuseStep 15377959 = 23066939) B23066939
theorem B6399641 : Blo 1498069 6399641 := bstep (se 2 (by rfl) ⟨2399865, by rfl⟩ : syracuseStep 6399641 = 4799731) B4799731
theorem B4269743 : Blo 1498069 4269743 := bstep (se 1 (by rfl) ⟨3202307, by rfl⟩ : syracuseStep 4269743 = 6404615) B6404615
theorem B8103655 : Blo 1498069 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B3794809 : Blo 1498069 3794809 := bstep (se 2 (by rfl) ⟨1423053, by rfl⟩ : syracuseStep 3794809 = 2846107) B2846107
theorem B4802447 : Blo 1498069 4802447 := bstep (se 1 (by rfl) ⟨3601835, by rfl⟩ : syracuseStep 4802447 = 7203671) B7203671
theorem B24307721 : Blo 1498069 24307721 := bstep (se 2 (by rfl) ⟨9115395, by rfl⟩ : syracuseStep 24307721 = 18230791) B18230791
theorem B18245681 : Blo 1498069 18245681 := bstep (se 2 (by rfl) ⟨6842130, by rfl⟩ : syracuseStep 18245681 = 13684261) B13684261
theorem B2247119 : Blo 1498069 2247119 := bstep (se 1 (by rfl) ⟨1685339, by rfl⟩ : syracuseStep 2247119 = 3370679) B3370679
theorem B2247161 : Blo 1498069 2247161 := bstep (se 2 (by rfl) ⟨842685, by rfl⟩ : syracuseStep 2247161 = 1685371) B1685371
theorem B2247209 : Blo 1498069 2247209 := bstep (se 2 (by rfl) ⟨842703, by rfl⟩ : syracuseStep 2247209 = 1685407) B1685407
theorem B4557359 : Blo 1498069 4557359 := bstep (se 1 (by rfl) ⟨3418019, by rfl⟩ : syracuseStep 4557359 = 6836039) B6836039
theorem B72927823 : Blo 1498069 72927823 := bstep (se 1 (by rfl) ⟨54695867, by rfl⟩ : syracuseStep 72927823 = 109391735) B109391735
theorem B57592457 : Blo 1498069 57592457 := bstep (se 2 (by rfl) ⟨21597171, by rfl⟩ : syracuseStep 57592457 = 43194343) B43194343
theorem B6834871 : Blo 1498069 6834871 := bstep (se 1 (by rfl) ⟨5126153, by rfl⟩ : syracuseStep 6834871 = 10252307) B10252307
theorem B4270927 : Blo 1498069 4270927 := bstep (se 1 (by rfl) ⟨3203195, by rfl⟩ : syracuseStep 4270927 = 6406391) B6406391
theorem B5688265 : Blo 1498069 5688265 := bstep (se 2 (by rfl) ⟨2133099, by rfl⟩ : syracuseStep 5688265 = 4266199) B4266199
theorem B2247647 : Blo 1498069 2247647 := bstep (se 1 (by rfl) ⟨1685735, by rfl⟩ : syracuseStep 2247647 = 3371471) B3371471
theorem B17312771 : Blo 1498069 17312771 := bstep (se 1 (by rfl) ⟨12984578, by rfl⟩ : syracuseStep 17312771 = 25969157) B25969157
theorem B3796105 : Blo 1498069 3796105 := bstep (se 2 (by rfl) ⟨1423539, by rfl⟩ : syracuseStep 3796105 = 2847079) B2847079
theorem B6835367 : Blo 1498069 6835367 := bstep (se 1 (by rfl) ⟨5126525, by rfl⟩ : syracuseStep 6835367 = 10253051) B10253051
theorem B7204115 : Blo 1498069 7204115 := bstep (se 1 (by rfl) ⟨5403086, by rfl⟩ : syracuseStep 7204115 = 10806173) B10806173
theorem B2248091 : Blo 1498069 2248091 := bstep (se 1 (by rfl) ⟨1686068, by rfl⟩ : syracuseStep 2248091 = 3372137) B3372137
theorem B8539667 : Blo 1498069 8539667 := bstep (se 1 (by rfl) ⟨6404750, by rfl⟩ : syracuseStep 8539667 = 12809501) B12809501
theorem B3370715 : Blo 1498069 3370715 := bstep (se 1 (by rfl) ⟨2528036, by rfl⟩ : syracuseStep 3370715 = 5056073) B5056073
theorem B2248457 : Blo 1498069 2248457 := bstep (se 2 (by rfl) ⟨843171, by rfl⟩ : syracuseStep 2248457 = 1686343) B1686343
theorem B2248511 : Blo 1498069 2248511 := bstep (se 1 (by rfl) ⟨1686383, by rfl⟩ : syracuseStep 2248511 = 3372767) B3372767
theorem B8540099 : Blo 1498069 8540099 := bstep (se 1 (by rfl) ⟨6405074, by rfl⟩ : syracuseStep 8540099 = 12810149) B12810149
theorem B3370985 : Blo 1498069 3370985 := bstep (se 2 (by rfl) ⟨1264119, by rfl⟩ : syracuseStep 3370985 = 2528239) B2528239
theorem B3371039 : Blo 1498069 3371039 := bstep (se 1 (by rfl) ⟨2528279, by rfl⟩ : syracuseStep 3371039 = 5056559) B5056559
theorem B2248751 : Blo 1498069 2248751 := bstep (se 1 (by rfl) ⟨1686563, by rfl⟩ : syracuseStep 2248751 = 3373127) B3373127
theorem B2846927 : Blo 1498069 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B12808439 : Blo 1498069 12808439 := bstep (se 1 (by rfl) ⟨9606329, by rfl⟩ : syracuseStep 12808439 = 19212659) B19212659
theorem B8540599 : Blo 1498069 8540599 := bstep (se 1 (by rfl) ⟨6405449, by rfl⟩ : syracuseStep 8540599 = 12810899) B12810899
theorem B2249195 : Blo 1498069 2249195 := bstep (se 1 (by rfl) ⟨1686896, by rfl⟩ : syracuseStep 2249195 = 3373793) B3373793
theorem B2249321 : Blo 1498069 2249321 := bstep (se 2 (by rfl) ⟨843495, by rfl⟩ : syracuseStep 2249321 = 1686991) B1686991
theorem B7590509 : Blo 1498069 7590509 := bstep (se 3 (by rfl) ⟨1423220, by rfl⟩ : syracuseStep 7590509 = 2846441) B2846441
theorem B2249327 : Blo 1498069 2249327 := bstep (se 1 (by rfl) ⟨1686995, by rfl⟩ : syracuseStep 2249327 = 3373991) B3373991
theorem B2249447 : Blo 1498069 2249447 := bstep (se 1 (by rfl) ⟨1687085, by rfl⟩ : syracuseStep 2249447 = 3374171) B3374171
theorem B9605897 : Blo 1498069 9605897 := bstep (se 2 (by rfl) ⟨3602211, by rfl⟩ : syracuseStep 9605897 = 7204423) B7204423
theorem B3371867 : Blo 1498069 3371867 := bstep (se 1 (by rfl) ⟨2528900, by rfl⟩ : syracuseStep 3371867 = 5057801) B5057801
theorem B2249609 : Blo 1498069 2249609 := bstep (se 2 (by rfl) ⟨843603, by rfl⟩ : syracuseStep 2249609 = 1687207) B1687207
theorem B3601367 : Blo 1498069 3601367 := bstep (se 1 (by rfl) ⟨2701025, by rfl⟩ : syracuseStep 3601367 = 5402051) B5402051
theorem B24302663 : Blo 1498069 24302663 := bstep (se 1 (by rfl) ⟨18226997, by rfl⟩ : syracuseStep 24302663 = 36453995) B36453995
theorem B2249951 : Blo 1498069 2249951 := bstep (se 1 (by rfl) ⟨1687463, by rfl⟩ : syracuseStep 2249951 = 3374927) B3374927
theorem B2249993 : Blo 1498069 2249993 := bstep (se 2 (by rfl) ⟨843747, by rfl⟩ : syracuseStep 2249993 = 1687495) B1687495
theorem B4052585 : Blo 1498069 4052585 := bstep (se 2 (by rfl) ⟨1519719, by rfl⟩ : syracuseStep 4052585 = 3039439) B3039439
theorem B1898311 : Blo 1498069 1898311 := bstep (se 1 (by rfl) ⟨1423733, by rfl⟩ : syracuseStep 1898311 = 2847467) B2847467
theorem B6838141 : Blo 1498069 6838141 := bstep (se 3 (by rfl) ⟨1282151, by rfl⟩ : syracuseStep 6838141 = 2564303) B2564303
theorem B9115591 : Blo 1498069 9115591 := bstep (se 1 (by rfl) ⟨6836693, by rfl⟩ : syracuseStep 9115591 = 13673387) B13673387
theorem B16889951 : Blo 1498069 16889951 := bstep (se 1 (by rfl) ⟨12667463, by rfl⟩ : syracuseStep 16889951 = 25334927) B25334927
theorem B10950803 : Blo 1498069 10950803 := bstep (se 1 (by rfl) ⟨8213102, by rfl⟩ : syracuseStep 10950803 = 16426205) B16426205
theorem B7305383 : Blo 1498069 7305383 := bstep (se 1 (by rfl) ⟨5479037, by rfl⟩ : syracuseStep 7305383 = 10958075) B10958075
theorem B8542583 : Blo 1498069 8542583 := bstep (se 1 (by rfl) ⟨6406937, by rfl⟩ : syracuseStep 8542583 = 12813875) B12813875
theorem B3373595 : Blo 1498069 3373595 := bstep (se 1 (by rfl) ⟨2530196, by rfl⟩ : syracuseStep 3373595 = 5060393) B5060393
theorem B19200563 : Blo 1498069 19200563 := bstep (se 1 (by rfl) ⟨14400422, by rfl⟩ : syracuseStep 19200563 = 28800845) B28800845
theorem B4266587 : Blo 1498069 4266587 := bstep (se 1 (by rfl) ⟨3199940, by rfl⟩ : syracuseStep 4266587 = 6399881) B6399881
theorem B10255151 : Blo 1498069 10255151 := bstep (se 1 (by rfl) ⟨7691363, by rfl⟩ : syracuseStep 10255151 = 15382727) B15382727
theorem B415464389 : Blo 1498069 415464389 := bstep (se 4 (by rfl) ⟨38949786, by rfl⟩ : syracuseStep 415464389 = 77899573) B77899573
theorem B1801183 : Blo 1498069 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B98614259 : Blo 1498069 98614259 := bstep (se 1 (by rfl) ⟨73960694, by rfl⟩ : syracuseStep 98614259 = 147921389) B147921389
theorem B1498175 : Blo 1498069 1498175 := bstep (se 1 (by rfl) ⟨1123631, by rfl⟩ : syracuseStep 1498175 = 2247263) B2247263
theorem B1498363 : Blo 1498069 1498363 := bstep (se 1 (by rfl) ⟨1123772, by rfl⟩ : syracuseStep 1498363 = 2247545) B2247545
theorem B1498395 : Blo 1498069 1498395 := bstep (se 1 (by rfl) ⟨1123796, by rfl⟩ : syracuseStep 1498395 = 2247593) B2247593
theorem B1498495 : Blo 1498069 1498495 := bstep (se 1 (by rfl) ⟨1123871, by rfl⟩ : syracuseStep 1498495 = 2247743) B2247743
theorem B7585163 : Blo 1498069 7585163 := bstep (se 1 (by rfl) ⟨5688872, by rfl⟩ : syracuseStep 7585163 = 11377745) B11377745
theorem B3792491 : Blo 1498069 3792491 := bstep (se 1 (by rfl) ⟨2844368, by rfl⟩ : syracuseStep 3792491 = 5688737) B5688737
theorem B4005551 : Blo 1498069 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B2531047 : Blo 1498069 2531047 := bstep (se 1 (by rfl) ⟨1898285, by rfl⟩ : syracuseStep 2531047 = 3796571) B3796571
theorem B1498863 : Blo 1498069 1498863 := bstep (se 1 (by rfl) ⟨1124147, by rfl⟩ : syracuseStep 1498863 = 2248295) B2248295
theorem B374202227 : Blo 1498069 374202227 := bstep (se 1 (by rfl) ⟨280651670, by rfl⟩ : syracuseStep 374202227 = 561303341) B561303341
theorem B5062607 : Blo 1498069 5062607 := bstep (se 1 (by rfl) ⟨3796955, by rfl⟩ : syracuseStep 5062607 = 7593911) B7593911
theorem B1499119 : Blo 1498069 1499119 := bstep (se 1 (by rfl) ⟨1124339, by rfl⟩ : syracuseStep 1499119 = 2248679) B2248679
theorem B8101883 : Blo 1498069 8101883 := bstep (se 1 (by rfl) ⟨6076412, by rfl⟩ : syracuseStep 8101883 = 12152825) B12152825
theorem B1499167 : Blo 1498069 1499167 := bstep (se 1 (by rfl) ⟨1124375, by rfl⟩ : syracuseStep 1499167 = 2248751) B2248751
theorem B1499463 : Blo 1498069 1499463 := bstep (se 1 (by rfl) ⟨1124597, by rfl⟩ : syracuseStep 1499463 = 2249195) B2249195
theorem B6406543 : Blo 1498069 6406543 := bstep (se 1 (by rfl) ⟨4804907, by rfl⟩ : syracuseStep 6406543 = 9609815) B9609815
theorem B1499547 : Blo 1498069 1499547 := bstep (se 1 (by rfl) ⟨1124660, by rfl⟩ : syracuseStep 1499547 = 2249321) B2249321
theorem B1499551 : Blo 1498069 1499551 := bstep (se 1 (by rfl) ⟨1124663, by rfl⟩ : syracuseStep 1499551 = 2249327) B2249327
theorem B1499631 : Blo 1498069 1499631 := bstep (se 1 (by rfl) ⟨1124723, by rfl⟩ : syracuseStep 1499631 = 2249447) B2249447
theorem B11387465 : Blo 1498069 11387465 := bstep (se 2 (by rfl) ⟨4270299, by rfl⟩ : syracuseStep 11387465 = 8540599) B8540599
theorem B4801103 : Blo 1498069 4801103 := bstep (se 1 (by rfl) ⟨3600827, by rfl⟩ : syracuseStep 4801103 = 7201655) B7201655
theorem B1499739 : Blo 1498069 1499739 := bstep (se 1 (by rfl) ⟨1124804, by rfl⟩ : syracuseStep 1499739 = 2249609) B2249609
theorem B2400911 : Blo 1498069 2400911 := bstep (se 1 (by rfl) ⟨1800683, by rfl⟩ : syracuseStep 2400911 = 3601367) B3601367
theorem B38421215 : Blo 1498069 38421215 := bstep (se 1 (by rfl) ⟨28815911, by rfl⟩ : syracuseStep 38421215 = 57631823) B57631823
theorem B1499967 : Blo 1498069 1499967 := bstep (se 1 (by rfl) ⟨1124975, by rfl⟩ : syracuseStep 1499967 = 2249951) B2249951
theorem B1499995 : Blo 1498069 1499995 := bstep (se 1 (by rfl) ⟨1124996, by rfl⟩ : syracuseStep 1499995 = 2249993) B2249993
theorem B7586783 : Blo 1498069 7586783 := bstep (se 1 (by rfl) ⟨5690087, by rfl⟩ : syracuseStep 7586783 = 11380175) B11380175
theorem B5694569 : Blo 1498069 5694569 := bstep (se 2 (by rfl) ⟨2135463, by rfl⟩ : syracuseStep 5694569 = 4270927) B4270927
theorem B2401577 : Blo 1498069 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B16205147 : Blo 1498069 16205147 := bstep (se 1 (by rfl) ⟨12153860, by rfl⟩ : syracuseStep 16205147 = 24307721) B24307721
theorem B7300535 : Blo 1498069 7300535 := bstep (se 1 (by rfl) ⟨5475401, by rfl⟩ : syracuseStep 7300535 = 10950803) B10950803
theorem B5695055 : Blo 1498069 5695055 := bstep (se 1 (by rfl) ⟨4271291, by rfl⟩ : syracuseStep 5695055 = 8542583) B8542583
theorem B2844391 : Blo 1498069 2844391 := bstep (se 1 (by rfl) ⟨2133293, by rfl⟩ : syracuseStep 2844391 = 4266587) B4266587
theorem B28804841 : Blo 1498069 28804841 := bstep (se 2 (by rfl) ⟨10801815, by rfl⟩ : syracuseStep 28804841 = 21603631) B21603631
theorem B65742839 : Blo 1498069 65742839 := bstep (se 1 (by rfl) ⟨49307129, by rfl⟩ : syracuseStep 65742839 = 98614259) B98614259
theorem B4556911 : Blo 1498069 4556911 := bstep (se 1 (by rfl) ⟨3417683, by rfl⟩ : syracuseStep 4556911 = 6835367) B6835367
theorem B4802743 : Blo 1498069 4802743 := bstep (se 1 (by rfl) ⟨3602057, by rfl⟩ : syracuseStep 4802743 = 7204115) B7204115
theorem B5056775 : Blo 1498069 5056775 := bstep (se 1 (by rfl) ⟨3792581, by rfl⟩ : syracuseStep 5056775 = 7585163) B7585163
theorem B12806525 : Blo 1498069 12806525 := bstep (se 3 (by rfl) ⟨2401223, by rfl⟩ : syracuseStep 12806525 = 4802447) B4802447
theorem B2247143 : Blo 1498069 2247143 := bstep (se 1 (by rfl) ⟨1685357, by rfl⟩ : syracuseStep 2247143 = 3370715) B3370715
theorem B2247323 : Blo 1498069 2247323 := bstep (se 1 (by rfl) ⟨1685492, by rfl⟩ : syracuseStep 2247323 = 3370985) B3370985
theorem B5401255 : Blo 1498069 5401255 := bstep (se 1 (by rfl) ⟨4050941, by rfl⟩ : syracuseStep 5401255 = 8101883) B8101883
theorem B2247359 : Blo 1498069 2247359 := bstep (se 1 (by rfl) ⟨1685519, by rfl⟩ : syracuseStep 2247359 = 3371039) B3371039
theorem B46181171 : Blo 1498069 46181171 := bstep (se 1 (by rfl) ⟨34635878, by rfl⟩ : syracuseStep 46181171 = 69271757) B69271757
theorem B8538959 : Blo 1498069 8538959 := bstep (se 1 (by rfl) ⟨6404219, by rfl⟩ : syracuseStep 8538959 = 12808439) B12808439
theorem B5057531 : Blo 1498069 5057531 := bstep (se 1 (by rfl) ⟨3793148, by rfl⟩ : syracuseStep 5057531 = 7586297) B7586297
theorem B10251319 : Blo 1498069 10251319 := bstep (se 1 (by rfl) ⟨7688489, by rfl⟩ : syracuseStep 10251319 = 15376979) B15376979
theorem B7695431 : Blo 1498069 7695431 := bstep (se 1 (by rfl) ⟨5771573, by rfl⟩ : syracuseStep 7695431 = 11543147) B11543147
theorem B5057747 : Blo 1498069 5057747 := bstep (se 1 (by rfl) ⟨3793310, by rfl⟩ : syracuseStep 5057747 = 7586621) B7586621
theorem B2247911 : Blo 1498069 2247911 := bstep (se 1 (by rfl) ⟨1685933, by rfl⟩ : syracuseStep 2247911 = 3371867) B3371867
theorem B9113161 : Blo 1498069 9113161 := bstep (se 2 (by rfl) ⟨3417435, by rfl⟩ : syracuseStep 9113161 = 6834871) B6834871
theorem B2846495 : Blo 1498069 2846495 := bstep (se 1 (by rfl) ⟨2134871, by rfl⟩ : syracuseStep 2846495 = 4269743) B4269743
theorem B11259967 : Blo 1498069 11259967 := bstep (se 1 (by rfl) ⟨8444975, by rfl⟩ : syracuseStep 11259967 = 16889951) B16889951
theorem B4870255 : Blo 1498069 4870255 := bstep (se 1 (by rfl) ⟨3652691, by rfl⟩ : syracuseStep 4870255 = 7305383) B7305383
theorem B2249063 : Blo 1498069 2249063 := bstep (se 1 (by rfl) ⟨1686797, by rfl⟩ : syracuseStep 2249063 = 3373595) B3373595
theorem B12800375 : Blo 1498069 12800375 := bstep (se 1 (by rfl) ⟨9600281, by rfl⟩ : syracuseStep 12800375 = 19200563) B19200563
theorem B6836767 : Blo 1498069 6836767 := bstep (se 1 (by rfl) ⟨5127575, by rfl⟩ : syracuseStep 6836767 = 10255151) B10255151
theorem B276976259 : Blo 1498069 276976259 := bstep (se 1 (by rfl) ⟨207732194, by rfl⟩ : syracuseStep 276976259 = 415464389) B415464389
theorem B997872605 : Blo 1498069 997872605 := bstep (se 3 (by rfl) ⟨187101113, by rfl⟩ : syracuseStep 997872605 = 374202227) B374202227
theorem B2528327 : Blo 1498069 2528327 := bstep (se 1 (by rfl) ⟨1896245, by rfl⟩ : syracuseStep 2528327 = 3792491) B3792491
theorem B5059745 : Blo 1498069 5059745 := bstep (se 2 (by rfl) ⟨1897404, by rfl⟩ : syracuseStep 5059745 = 3794809) B3794809
theorem B12154121 : Blo 1498069 12154121 := bstep (se 2 (by rfl) ⟨4557795, by rfl⟩ : syracuseStep 12154121 = 9115591) B9115591
theorem B5060339 : Blo 1498069 5060339 := bstep (se 1 (by rfl) ⟨3795254, by rfl⟩ : syracuseStep 5060339 = 7590509) B7590509
theorem B6403931 : Blo 1498069 6403931 := bstep (se 1 (by rfl) ⟨4802948, by rfl⟩ : syracuseStep 6403931 = 9605897) B9605897
theorem B7591805 : Blo 1498069 7591805 := bstep (se 3 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 7591805 = 2846927) B2846927
theorem B16201775 : Blo 1498069 16201775 := bstep (se 1 (by rfl) ⟨12151331, by rfl⟩ : syracuseStep 16201775 = 24302663) B24302663
theorem B97237097 : Blo 1498069 97237097 := bstep (se 2 (by rfl) ⟨36463911, by rfl⟩ : syracuseStep 97237097 = 72927823) B72927823
theorem B2529407 : Blo 1498069 2529407 := bstep (se 1 (by rfl) ⟨1897055, by rfl⟩ : syracuseStep 2529407 = 3794111) B3794111
theorem B5691667 : Blo 1498069 5691667 := bstep (se 1 (by rfl) ⟨4268750, by rfl⟩ : syracuseStep 5691667 = 8537501) B8537501
theorem B2701723 : Blo 1498069 2701723 := bstep (se 1 (by rfl) ⟨2026292, by rfl⟩ : syracuseStep 2701723 = 4052585) B4052585
theorem B4266427 : Blo 1498069 4266427 := bstep (se 1 (by rfl) ⟨3199820, by rfl⟩ : syracuseStep 4266427 = 6399641) B6399641
theorem B23091713 : Blo 1498069 23091713 := bstep (se 2 (by rfl) ⟨8659392, by rfl⟩ : syracuseStep 23091713 = 17318785) B17318785
theorem B43219493 : Blo 1498069 43219493 := bstep (se 4 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 43219493 = 8103655) B8103655
theorem B7584353 : Blo 1498069 7584353 := bstep (se 2 (by rfl) ⟨2844132, by rfl⟩ : syracuseStep 7584353 = 5688265) B5688265
theorem B12163787 : Blo 1498069 12163787 := bstep (se 1 (by rfl) ⟨9122840, by rfl⟩ : syracuseStep 12163787 = 18245681) B18245681
theorem B5061473 : Blo 1498069 5061473 := bstep (se 2 (by rfl) ⟨1898052, by rfl⟩ : syracuseStep 5061473 = 3796105) B3796105
theorem B1498079 : Blo 1498069 1498079 := bstep (se 1 (by rfl) ⟨1123559, by rfl⟩ : syracuseStep 1498079 = 2247119) B2247119
theorem B1498107 : Blo 1498069 1498107 := bstep (se 1 (by rfl) ⟨1123580, by rfl⟩ : syracuseStep 1498107 = 2247161) B2247161
theorem B1498139 : Blo 1498069 1498139 := bstep (se 1 (by rfl) ⟨1123604, by rfl⟩ : syracuseStep 1498139 = 2247209) B2247209
theorem B3038239 : Blo 1498069 3038239 := bstep (se 1 (by rfl) ⟨2278679, by rfl⟩ : syracuseStep 3038239 = 4557359) B4557359
theorem B5692457 : Blo 1498069 5692457 := bstep (se 2 (by rfl) ⟨2134671, by rfl⟩ : syracuseStep 5692457 = 4269343) B4269343
theorem B38394971 : Blo 1498069 38394971 := bstep (se 1 (by rfl) ⟨28796228, by rfl⟩ : syracuseStep 38394971 = 57592457) B57592457
theorem B10681469 : Blo 1498069 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B1498431 : Blo 1498069 1498431 := bstep (se 1 (by rfl) ⟨1123823, by rfl⟩ : syracuseStep 1498431 = 2247647) B2247647
theorem B11541847 : Blo 1498069 11541847 := bstep (se 1 (by rfl) ⟨8656385, by rfl⟩ : syracuseStep 11541847 = 17312771) B17312771
theorem B20503945 : Blo 1498069 20503945 := bstep (se 2 (by rfl) ⟨7688979, by rfl⟩ : syracuseStep 20503945 = 15377959) B15377959
theorem B1498727 : Blo 1498069 1498727 := bstep (se 1 (by rfl) ⟨1124045, by rfl⟩ : syracuseStep 1498727 = 2248091) B2248091
theorem B3374729 : Blo 1498069 3374729 := bstep (se 2 (by rfl) ⟨1265523, by rfl⟩ : syracuseStep 3374729 = 2531047) B2531047
theorem B5693111 : Blo 1498069 5693111 := bstep (se 1 (by rfl) ⟨4269833, by rfl⟩ : syracuseStep 5693111 = 8539667) B8539667
theorem B2531081 : Blo 1498069 2531081 := bstep (se 2 (by rfl) ⟨949155, by rfl⟩ : syracuseStep 2531081 = 1898311) B1898311
theorem B9117521 : Blo 1498069 9117521 := bstep (se 2 (by rfl) ⟨3419070, by rfl⟩ : syracuseStep 9117521 = 6838141) B6838141
theorem B1498971 : Blo 1498069 1498971 := bstep (se 1 (by rfl) ⟨1124228, by rfl⟩ : syracuseStep 1498971 = 2248457) B2248457
theorem B1499007 : Blo 1498069 1499007 := bstep (se 1 (by rfl) ⟨1124255, by rfl⟩ : syracuseStep 1499007 = 2248511) B2248511
theorem B5693399 : Blo 1498069 5693399 := bstep (se 1 (by rfl) ⟨4270049, by rfl⟩ : syracuseStep 5693399 = 8540099) B8540099
theorem B3375071 : Blo 1498069 3375071 := bstep (se 1 (by rfl) ⟨2531303, by rfl⟩ : syracuseStep 3375071 = 5062607) B5062607
theorem B36462757 : Blo 1498069 36462757 := bstep (se 4 (by rfl) ⟨3418383, by rfl⟩ : syracuseStep 36462757 = 6836767) B6836767
theorem B1499375 : Blo 1498069 1499375 := bstep (se 1 (by rfl) ⟨1124531, by rfl⟩ : syracuseStep 1499375 = 2249063) B2249063
theorem B665248403 : Blo 1498069 665248403 := bstep (se 1 (by rfl) ⟨498936302, by rfl⟩ : syracuseStep 665248403 = 997872605) B997872605
theorem B8102747 : Blo 1498069 8102747 := bstep (se 1 (by rfl) ⟨6077060, by rfl⟩ : syracuseStep 8102747 = 12154121) B12154121
theorem B7201673 : Blo 1498069 7201673 := bstep (se 2 (by rfl) ⟨2700627, by rfl⟩ : syracuseStep 7201673 = 5401255) B5401255
theorem B19203227 : Blo 1498069 19203227 := bstep (se 1 (by rfl) ⟨14402420, by rfl⟩ : syracuseStep 19203227 = 28804841) B28804841
theorem B4269287 : Blo 1498069 4269287 := bstep (se 1 (by rfl) ⟨3201965, by rfl⟩ : syracuseStep 4269287 = 6403931) B6403931
theorem B43828559 : Blo 1498069 43828559 := bstep (se 1 (by rfl) ⟨32871419, by rfl⟩ : syracuseStep 43828559 = 65742839) B65742839
theorem B64824731 : Blo 1498069 64824731 := bstep (se 1 (by rfl) ⟨48618548, by rfl⟩ : syracuseStep 64824731 = 97237097) B97237097
theorem B8537683 : Blo 1498069 8537683 := bstep (se 1 (by rfl) ⟨6403262, by rfl⟩ : syracuseStep 8537683 = 12806525) B12806525
theorem B15394475 : Blo 1498069 15394475 := bstep (se 1 (by rfl) ⟨11545856, by rfl⟩ : syracuseStep 15394475 = 23091713) B23091713
theorem B28812995 : Blo 1498069 28812995 := bstep (se 1 (by rfl) ⟨21609746, by rfl⟩ : syracuseStep 28812995 = 43219493) B43219493
theorem B5056235 : Blo 1498069 5056235 := bstep (se 1 (by rfl) ⟨3792176, by rfl⟩ : syracuseStep 5056235 = 7584353) B7584353
theorem B30787447 : Blo 1498069 30787447 := bstep (se 1 (by rfl) ⟨23090585, by rfl⟩ : syracuseStep 30787447 = 46181171) B46181171
theorem B3794971 : Blo 1498069 3794971 := bstep (se 1 (by rfl) ⟨2846228, by rfl⟩ : syracuseStep 3794971 = 5692457) B5692457
theorem B5130287 : Blo 1498069 5130287 := bstep (se 1 (by rfl) ⟨3847715, by rfl⟩ : syracuseStep 5130287 = 7695431) B7695431
theorem B7120979 : Blo 1498069 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B12150881 : Blo 1498069 12150881 := bstep (se 2 (by rfl) ⟨4556580, by rfl⟩ : syracuseStep 12150881 = 9113161) B9113161
theorem B3795407 : Blo 1498069 3795407 := bstep (se 1 (by rfl) ⟨2846555, by rfl⟩ : syracuseStep 3795407 = 5693111) B5693111
theorem B3795599 : Blo 1498069 3795599 := bstep (se 1 (by rfl) ⟨2846699, by rfl⟩ : syracuseStep 3795599 = 5693399) B5693399
theorem B7588889 : Blo 1498069 7588889 := bstep (se 2 (by rfl) ⟨2845833, by rfl⟩ : syracuseStep 7588889 = 5691667) B5691667
theorem B184650839 : Blo 1498069 184650839 := bstep (se 1 (by rfl) ⟨138488129, by rfl⟩ : syracuseStep 184650839 = 276976259) B276976259
theorem B1600607 : Blo 1498069 1600607 := bstep (se 1 (by rfl) ⟨1200455, by rfl⟩ : syracuseStep 1600607 = 2400911) B2400911
theorem B5688569 : Blo 1498069 5688569 := bstep (se 2 (by rfl) ⟨2133213, by rfl⟩ : syracuseStep 5688569 = 4266427) B4266427
theorem B5057855 : Blo 1498069 5057855 := bstep (se 1 (by rfl) ⟨3793391, by rfl⟩ : syracuseStep 5057855 = 7586783) B7586783
theorem B3796379 : Blo 1498069 3796379 := bstep (se 1 (by rfl) ⟨2847284, by rfl⟩ : syracuseStep 3796379 = 5694569) B5694569
theorem B1601051 : Blo 1498069 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B3796703 : Blo 1498069 3796703 := bstep (se 1 (by rfl) ⟨2847527, by rfl⟩ : syracuseStep 3796703 = 5695055) B5695055
theorem B10801183 : Blo 1498069 10801183 := bstep (se 1 (by rfl) ⟨8100887, by rfl⟩ : syracuseStep 10801183 = 16201775) B16201775
theorem B4050985 : Blo 1498069 4050985 := bstep (se 2 (by rfl) ⟨1519119, by rfl⟩ : syracuseStep 4050985 = 3038239) B3038239
theorem B13668425 : Blo 1498069 13668425 := bstep (se 2 (by rfl) ⟨5125659, by rfl⟩ : syracuseStep 13668425 = 10251319) B10251319
theorem B3371183 : Blo 1498069 3371183 := bstep (se 1 (by rfl) ⟨2528387, by rfl⟩ : syracuseStep 3371183 = 5056775) B5056775
theorem B15389129 : Blo 1498069 15389129 := bstep (se 2 (by rfl) ⟨5770923, by rfl⟩ : syracuseStep 15389129 = 11541847) B11541847
theorem B3371687 : Blo 1498069 3371687 := bstep (se 1 (by rfl) ⟨2528765, by rfl⟩ : syracuseStep 3371687 = 5057531) B5057531
theorem B25596647 : Blo 1498069 25596647 := bstep (se 1 (by rfl) ⟨19197485, by rfl⟩ : syracuseStep 25596647 = 38394971) B38394971
theorem B3371831 : Blo 1498069 3371831 := bstep (se 1 (by rfl) ⟨2528873, by rfl⟩ : syracuseStep 3371831 = 5057747) B5057747
theorem B2249819 : Blo 1498069 2249819 := bstep (se 1 (by rfl) ⟨1687364, by rfl⟩ : syracuseStep 2249819 = 3374729) B3374729
theorem B1897663 : Blo 1498069 1897663 := bstep (se 1 (by rfl) ⟨1423247, by rfl⟩ : syracuseStep 1897663 = 2846495) B2846495
theorem B2250047 : Blo 1498069 2250047 := bstep (se 1 (by rfl) ⟨1687535, by rfl⟩ : syracuseStep 2250047 = 3375071) B3375071
theorem B15013289 : Blo 1498069 15013289 := bstep (se 2 (by rfl) ⟨5629983, by rfl⟩ : syracuseStep 15013289 = 11259967) B11259967
theorem B6075881 : Blo 1498069 6075881 := bstep (se 2 (by rfl) ⟨2278455, by rfl⟩ : syracuseStep 6075881 = 4556911) B4556911
theorem B6493673 : Blo 1498069 6493673 := bstep (se 2 (by rfl) ⟨2435127, by rfl⟩ : syracuseStep 6493673 = 4870255) B4870255
theorem B6403657 : Blo 1498069 6403657 := bstep (se 2 (by rfl) ⟨2401371, by rfl⟩ : syracuseStep 6403657 = 4802743) B4802743
theorem B8533583 : Blo 1498069 8533583 := bstep (se 1 (by rfl) ⟨6400187, by rfl⟩ : syracuseStep 8533583 = 12800375) B12800375
theorem B7591643 : Blo 1498069 7591643 := bstep (se 1 (by rfl) ⟨5693732, by rfl⟩ : syracuseStep 7591643 = 11387465) B11387465
theorem B3200735 : Blo 1498069 3200735 := bstep (se 1 (by rfl) ⟨2400551, by rfl⟩ : syracuseStep 3200735 = 4801103) B4801103
theorem B25614143 : Blo 1498069 25614143 := bstep (se 1 (by rfl) ⟨19210607, by rfl⟩ : syracuseStep 25614143 = 38421215) B38421215
theorem B8542057 : Blo 1498069 8542057 := bstep (se 2 (by rfl) ⟨3203271, by rfl⟩ : syracuseStep 8542057 = 6406543) B6406543
theorem B3602297 : Blo 1498069 3602297 := bstep (se 2 (by rfl) ⟨1350861, by rfl⟩ : syracuseStep 3602297 = 2701723) B2701723
theorem B1685551 : Blo 1498069 1685551 := bstep (se 1 (by rfl) ⟨1264163, by rfl⟩ : syracuseStep 1685551 = 2528327) B2528327
theorem B3373163 : Blo 1498069 3373163 := bstep (se 1 (by rfl) ⟨2529872, by rfl⟩ : syracuseStep 3373163 = 5059745) B5059745
theorem B10803431 : Blo 1498069 10803431 := bstep (se 1 (by rfl) ⟨8102573, by rfl⟩ : syracuseStep 10803431 = 16205147) B16205147
theorem B3373559 : Blo 1498069 3373559 := bstep (se 1 (by rfl) ⟨2530169, by rfl⟩ : syracuseStep 3373559 = 5060339) B5060339
theorem B5061203 : Blo 1498069 5061203 := bstep (se 1 (by rfl) ⟨3795902, by rfl⟩ : syracuseStep 5061203 = 7591805) B7591805
theorem B1686271 : Blo 1498069 1686271 := bstep (se 1 (by rfl) ⟨1264703, by rfl⟩ : syracuseStep 1686271 = 2529407) B2529407
theorem B1498095 : Blo 1498069 1498095 := bstep (se 1 (by rfl) ⟨1123571, by rfl⟩ : syracuseStep 1498095 = 2247143) B2247143
theorem B1498215 : Blo 1498069 1498215 := bstep (se 1 (by rfl) ⟨1123661, by rfl⟩ : syracuseStep 1498215 = 2247323) B2247323
theorem B1498239 : Blo 1498069 1498239 := bstep (se 1 (by rfl) ⟨1123679, by rfl⟩ : syracuseStep 1498239 = 2247359) B2247359
theorem B8109191 : Blo 1498069 8109191 := bstep (se 1 (by rfl) ⟨6081893, by rfl⟩ : syracuseStep 8109191 = 12163787) B12163787
theorem B5692639 : Blo 1498069 5692639 := bstep (se 1 (by rfl) ⟨4269479, by rfl⟩ : syracuseStep 5692639 = 8538959) B8538959
theorem B3374315 : Blo 1498069 3374315 := bstep (se 1 (by rfl) ⟨2530736, by rfl⟩ : syracuseStep 3374315 = 5061473) B5061473
theorem B77872373 : Blo 1498069 77872373 := bstep (se 5 (by rfl) ⟨3650267, by rfl⟩ : syracuseStep 77872373 = 7300535) B7300535
theorem B109354373 : Blo 1498069 109354373 := bstep (se 4 (by rfl) ⟨10251972, by rfl⟩ : syracuseStep 109354373 = 20503945) B20503945
theorem B1498607 : Blo 1498069 1498607 := bstep (se 1 (by rfl) ⟨1123955, by rfl⟩ : syracuseStep 1498607 = 2247911) B2247911
theorem B3792521 : Blo 1498069 3792521 := bstep (se 2 (by rfl) ⟨1422195, by rfl⟩ : syracuseStep 3792521 = 2844391) B2844391
theorem B1687387 : Blo 1498069 1687387 := bstep (se 1 (by rfl) ⟨1265540, by rfl⟩ : syracuseStep 1687387 = 2531081) B2531081
theorem B6078347 : Blo 1498069 6078347 := bstep (se 1 (by rfl) ⟨4558760, by rfl⟩ : syracuseStep 6078347 = 9117521) B9117521
theorem B14401577 : Blo 1498069 14401577 := bstep (se 2 (by rfl) ⟨5400591, by rfl⟩ : syracuseStep 14401577 = 10801183) B10801183
theorem B4268285 : Blo 1498069 4268285 := bstep (se 3 (by rfl) ⟨800303, by rfl⟩ : syracuseStep 4268285 = 1600607) B1600607
theorem B443498935 : Blo 1498069 443498935 := bstep (se 1 (by rfl) ⟨332624201, by rfl⟩ : syracuseStep 443498935 = 665248403) B665248403
theorem B17064431 : Blo 1498069 17064431 := bstep (se 1 (by rfl) ⟨12798323, by rfl⟩ : syracuseStep 17064431 = 25596647) B25596647
theorem B4801115 : Blo 1498069 4801115 := bstep (se 1 (by rfl) ⟨3600836, by rfl⟩ : syracuseStep 4801115 = 7201673) B7201673
theorem B1499879 : Blo 1498069 1499879 := bstep (se 1 (by rfl) ⟨1124909, by rfl⟩ : syracuseStep 1499879 = 2249819) B2249819
theorem B1500031 : Blo 1498069 1500031 := bstep (se 1 (by rfl) ⟨1125023, by rfl⟩ : syracuseStep 1500031 = 2250047) B2250047
theorem B40035437 : Blo 1498069 40035437 := bstep (se 3 (by rfl) ⟨7506644, by rfl⟩ : syracuseStep 40035437 = 15013289) B15013289
theorem B2401531 : Blo 1498069 2401531 := bstep (se 1 (by rfl) ⟨1801148, by rfl⟩ : syracuseStep 2401531 = 3602297) B3602297
theorem B4269469 : Blo 1498069 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B7202287 : Blo 1498069 7202287 := bstep (se 1 (by rfl) ⟨5401715, by rfl⟩ : syracuseStep 7202287 = 10803431) B10803431
theorem B8538209 : Blo 1498069 8538209 := bstep (se 2 (by rfl) ⟨3201828, by rfl⟩ : syracuseStep 8538209 = 6403657) B6403657
theorem B51914915 : Blo 1498069 51914915 := bstep (se 1 (by rfl) ⟨38936186, by rfl⟩ : syracuseStep 51914915 = 77872373) B77872373
theorem B72902915 : Blo 1498069 72902915 := bstep (se 1 (by rfl) ⟨54677186, by rfl⟩ : syracuseStep 72902915 = 109354373) B109354373
theorem B11389409 : Blo 1498069 11389409 := bstep (se 2 (by rfl) ⟨4271028, by rfl⟩ : syracuseStep 11389409 = 8542057) B8542057
theorem B9112283 : Blo 1498069 9112283 := bstep (se 1 (by rfl) ⟨6834212, by rfl⟩ : syracuseStep 9112283 = 13668425) B13668425
theorem B5401313 : Blo 1498069 5401313 := bstep (se 2 (by rfl) ⟨2025492, by rfl⟩ : syracuseStep 5401313 = 4050985) B4050985
theorem B2247401 : Blo 1498069 2247401 := bstep (se 2 (by rfl) ⟨842775, by rfl⟩ : syracuseStep 2247401 = 1685551) B1685551
theorem B2247455 : Blo 1498069 2247455 := bstep (se 1 (by rfl) ⟨1685591, by rfl⟩ : syracuseStep 2247455 = 3371183) B3371183
theorem B10259419 : Blo 1498069 10259419 := bstep (se 1 (by rfl) ⟨7694564, by rfl⟩ : syracuseStep 10259419 = 15389129) B15389129
theorem B2247791 : Blo 1498069 2247791 := bstep (se 1 (by rfl) ⟨1685843, by rfl⟩ : syracuseStep 2247791 = 3371687) B3371687
theorem B2247887 : Blo 1498069 2247887 := bstep (se 1 (by rfl) ⟨1685915, by rfl⟩ : syracuseStep 2247887 = 3371831) B3371831
theorem B5401831 : Blo 1498069 5401831 := bstep (se 1 (by rfl) ⟨4051373, by rfl⟩ : syracuseStep 5401831 = 8102747) B8102747
theorem B2846191 : Blo 1498069 2846191 := bstep (se 1 (by rfl) ⟨2134643, by rfl⟩ : syracuseStep 2846191 = 4269287) B4269287
theorem B43216487 : Blo 1498069 43216487 := bstep (se 1 (by rfl) ⟨32412365, by rfl⟩ : syracuseStep 43216487 = 64824731) B64824731
theorem B4050587 : Blo 1498069 4050587 := bstep (se 1 (by rfl) ⟨3037940, by rfl⟩ : syracuseStep 4050587 = 6075881) B6075881
theorem B2248361 : Blo 1498069 2248361 := bstep (se 2 (by rfl) ⟨843135, by rfl⟩ : syracuseStep 2248361 = 1686271) B1686271
theorem B5689055 : Blo 1498069 5689055 := bstep (se 1 (by rfl) ⟨4266791, by rfl⟩ : syracuseStep 5689055 = 8533583) B8533583
theorem B3370823 : Blo 1498069 3370823 := bstep (se 1 (by rfl) ⟨2528117, by rfl⟩ : syracuseStep 3370823 = 5056235) B5056235
theorem B17076095 : Blo 1498069 17076095 := bstep (se 1 (by rfl) ⟨12807071, by rfl⟩ : syracuseStep 17076095 = 25614143) B25614143
theorem B3420191 : Blo 1498069 3420191 := bstep (se 1 (by rfl) ⟨2565143, by rfl⟩ : syracuseStep 3420191 = 5130287) B5130287
theorem B4747319 : Blo 1498069 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B2248775 : Blo 1498069 2248775 := bstep (se 1 (by rfl) ⟨1686581, by rfl⟩ : syracuseStep 2248775 = 3373163) B3373163
theorem B7590185 : Blo 1498069 7590185 := bstep (se 2 (by rfl) ⟨2846319, by rfl⟩ : syracuseStep 7590185 = 5692639) B5692639
theorem B2249039 : Blo 1498069 2249039 := bstep (se 1 (by rfl) ⟨1686779, by rfl⟩ : syracuseStep 2249039 = 3373559) B3373559
theorem B5059259 : Blo 1498069 5059259 := bstep (se 1 (by rfl) ⟨3794444, by rfl⟩ : syracuseStep 5059259 = 7588889) B7588889
theorem B11383577 : Blo 1498069 11383577 := bstep (se 2 (by rfl) ⟨4268841, by rfl⟩ : syracuseStep 11383577 = 8537683) B8537683
theorem B2249543 : Blo 1498069 2249543 := bstep (se 1 (by rfl) ⟨1687157, by rfl⟩ : syracuseStep 2249543 = 3374315) B3374315
theorem B3371903 : Blo 1498069 3371903 := bstep (se 1 (by rfl) ⟨2528927, by rfl⟩ : syracuseStep 3371903 = 5057855) B5057855
theorem B2528347 : Blo 1498069 2528347 := bstep (se 1 (by rfl) ⟨1896260, by rfl⟩ : syracuseStep 2528347 = 3792521) B3792521
theorem B2249849 : Blo 1498069 2249849 := bstep (se 2 (by rfl) ⟨843693, by rfl⟩ : syracuseStep 2249849 = 1687387) B1687387
theorem B4052231 : Blo 1498069 4052231 := bstep (se 1 (by rfl) ⟨3039173, by rfl⟩ : syracuseStep 4052231 = 6078347) B6078347
theorem B5059961 : Blo 1498069 5059961 := bstep (se 2 (by rfl) ⟨1897485, by rfl⟩ : syracuseStep 5059961 = 3794971) B3794971
theorem B48617009 : Blo 1498069 48617009 := bstep (se 2 (by rfl) ⟨18231378, by rfl⟩ : syracuseStep 48617009 = 36462757) B36462757
theorem B21624509 : Blo 1498069 21624509 := bstep (se 3 (by rfl) ⟨4054595, by rfl⟩ : syracuseStep 21624509 = 8109191) B8109191
theorem B12802151 : Blo 1498069 12802151 := bstep (se 1 (by rfl) ⟨9601613, by rfl⟩ : syracuseStep 12802151 = 19203227) B19203227
theorem B29219039 : Blo 1498069 29219039 := bstep (se 1 (by rfl) ⟨21914279, by rfl⟩ : syracuseStep 29219039 = 43828559) B43828559
theorem B10262983 : Blo 1498069 10262983 := bstep (se 1 (by rfl) ⟨7697237, by rfl⟩ : syracuseStep 10262983 = 15394475) B15394475
theorem B19208663 : Blo 1498069 19208663 := bstep (se 1 (by rfl) ⟨14406497, by rfl⟩ : syracuseStep 19208663 = 28812995) B28812995
theorem B5061095 : Blo 1498069 5061095 := bstep (se 1 (by rfl) ⟨3795821, by rfl⟩ : syracuseStep 5061095 = 7591643) B7591643
theorem B17316461 : Blo 1498069 17316461 := bstep (se 3 (by rfl) ⟨3246836, by rfl⟩ : syracuseStep 17316461 = 6493673) B6493673
theorem B8100587 : Blo 1498069 8100587 := bstep (se 1 (by rfl) ⟨6075440, by rfl⟩ : syracuseStep 8100587 = 12150881) B12150881
theorem B2530217 : Blo 1498069 2530217 := bstep (se 2 (by rfl) ⟨948831, by rfl⟩ : syracuseStep 2530217 = 1897663) B1897663
theorem B2530271 : Blo 1498069 2530271 := bstep (se 1 (by rfl) ⟨1897703, by rfl⟩ : syracuseStep 2530271 = 3795407) B3795407
theorem B3374135 : Blo 1498069 3374135 := bstep (se 1 (by rfl) ⟨2530601, by rfl⟩ : syracuseStep 3374135 = 5061203) B5061203
theorem B2530399 : Blo 1498069 2530399 := bstep (se 1 (by rfl) ⟨1897799, by rfl⟩ : syracuseStep 2530399 = 3795599) B3795599
theorem B8535293 : Blo 1498069 8535293 := bstep (se 3 (by rfl) ⟨1600367, by rfl⟩ : syracuseStep 8535293 = 3200735) B3200735
theorem B123100559 : Blo 1498069 123100559 := bstep (se 1 (by rfl) ⟨92325419, by rfl⟩ : syracuseStep 123100559 = 184650839) B184650839
theorem B3792379 : Blo 1498069 3792379 := bstep (se 1 (by rfl) ⟨2844284, by rfl⟩ : syracuseStep 3792379 = 5688569) B5688569
theorem B2530919 : Blo 1498069 2530919 := bstep (se 1 (by rfl) ⟨1898189, by rfl⟩ : syracuseStep 2530919 = 3796379) B3796379
theorem B2531135 : Blo 1498069 2531135 := bstep (se 1 (by rfl) ⟨1898351, by rfl⟩ : syracuseStep 2531135 = 3796703) B3796703
theorem B41049929 : Blo 1498069 41049929 := bstep (se 2 (by rfl) ⟨15393723, by rfl⟩ : syracuseStep 41049929 = 30787447) B30787447
theorem B9601051 : Blo 1498069 9601051 := bstep (se 1 (by rfl) ⟨7200788, by rfl⟩ : syracuseStep 9601051 = 14401577) B14401577
theorem B1499183 : Blo 1498069 1499183 := bstep (se 1 (by rfl) ⟨1124387, by rfl⟩ : syracuseStep 1499183 = 2248775) B2248775
theorem B1499359 : Blo 1498069 1499359 := bstep (se 1 (by rfl) ⟨1124519, by rfl⟩ : syracuseStep 1499359 = 2249039) B2249039
theorem B1499695 : Blo 1498069 1499695 := bstep (se 1 (by rfl) ⟨1124771, by rfl⟩ : syracuseStep 1499695 = 2249543) B2249543
theorem B591331913 : Blo 1498069 591331913 := bstep (se 2 (by rfl) ⟨221749467, by rfl⟩ : syracuseStep 591331913 = 443498935) B443498935
theorem B26690291 : Blo 1498069 26690291 := bstep (se 1 (by rfl) ⟨20017718, by rfl⟩ : syracuseStep 26690291 = 40035437) B40035437
theorem B1499899 : Blo 1498069 1499899 := bstep (se 1 (by rfl) ⟨1124924, by rfl⟩ : syracuseStep 1499899 = 2249849) B2249849
theorem B7202441 : Blo 1498069 7202441 := bstep (se 2 (by rfl) ⟨2700915, by rfl⟩ : syracuseStep 7202441 = 5401831) B5401831
theorem B12805775 : Blo 1498069 12805775 := bstep (se 1 (by rfl) ⟨9604331, by rfl⟩ : syracuseStep 12805775 = 19208663) B19208663
theorem B5400391 : Blo 1498069 5400391 := bstep (se 1 (by rfl) ⟨4050293, by rfl⟩ : syracuseStep 5400391 = 8100587) B8100587
theorem B9603049 : Blo 1498069 9603049 := bstep (se 2 (by rfl) ⟨3601143, by rfl⟩ : syracuseStep 9603049 = 7202287) B7202287
theorem B3794921 : Blo 1498069 3794921 := bstep (se 2 (by rfl) ⟨1423095, by rfl⟩ : syracuseStep 3794921 = 2846191) B2846191
theorem B5056505 : Blo 1498069 5056505 := bstep (se 2 (by rfl) ⟨1896189, by rfl⟩ : syracuseStep 5056505 = 3792379) B3792379
theorem B2247215 : Blo 1498069 2247215 := bstep (se 1 (by rfl) ⟨1685411, by rfl⟩ : syracuseStep 2247215 = 3370823) B3370823
theorem B3164879 : Blo 1498069 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B9120509 : Blo 1498069 9120509 := bstep (se 3 (by rfl) ⟨1710095, by rfl⟩ : syracuseStep 9120509 = 3420191) B3420191
theorem B2845523 : Blo 1498069 2845523 := bstep (se 1 (by rfl) ⟨2134142, by rfl⟩ : syracuseStep 2845523 = 4268285) B4268285
theorem B7589051 : Blo 1498069 7589051 := bstep (se 1 (by rfl) ⟨5691788, by rfl⟩ : syracuseStep 7589051 = 11383577) B11383577
theorem B2247935 : Blo 1498069 2247935 := bstep (se 1 (by rfl) ⟨1685951, by rfl⟩ : syracuseStep 2247935 = 3371903) B3371903
theorem B13683977 : Blo 1498069 13683977 := bstep (se 2 (by rfl) ⟨5131491, by rfl⟩ : syracuseStep 13683977 = 10262983) B10262983
theorem B32411339 : Blo 1498069 32411339 := bstep (se 1 (by rfl) ⟨24308504, by rfl⟩ : syracuseStep 32411339 = 48617009) B48617009
theorem B12808165 : Blo 1498069 12808165 := bstep (se 4 (by rfl) ⟨1200765, by rfl⟩ : syracuseStep 12808165 = 2401531) B2401531
theorem B3371129 : Blo 1498069 3371129 := bstep (se 2 (by rfl) ⟨1264173, by rfl⟩ : syracuseStep 3371129 = 2528347) B2528347
theorem B6074855 : Blo 1498069 6074855 := bstep (se 1 (by rfl) ⟨4556141, by rfl⟩ : syracuseStep 6074855 = 9112283) B9112283
theorem B3600875 : Blo 1498069 3600875 := bstep (se 1 (by rfl) ⟨2700656, by rfl⟩ : syracuseStep 3600875 = 5401313) B5401313
theorem B2249423 : Blo 1498069 2249423 := bstep (se 1 (by rfl) ⟨1687067, by rfl⟩ : syracuseStep 2249423 = 3374135) B3374135
theorem B5690195 : Blo 1498069 5690195 := bstep (se 1 (by rfl) ⟨4267646, by rfl⟩ : syracuseStep 5690195 = 8535293) B8535293
theorem B2700391 : Blo 1498069 2700391 := bstep (se 1 (by rfl) ⟨2025293, by rfl⟩ : syracuseStep 2700391 = 4050587) B4050587
theorem B27366619 : Blo 1498069 27366619 := bstep (se 1 (by rfl) ⟨20524964, by rfl⟩ : syracuseStep 27366619 = 41049929) B41049929
theorem B11384063 : Blo 1498069 11384063 := bstep (se 1 (by rfl) ⟨8538047, by rfl⟩ : syracuseStep 11384063 = 17076095) B17076095
theorem B5060123 : Blo 1498069 5060123 := bstep (se 1 (by rfl) ⟨3795092, by rfl⟩ : syracuseStep 5060123 = 7590185) B7590185
theorem B11376287 : Blo 1498069 11376287 := bstep (se 1 (by rfl) ⟨8532215, by rfl⟩ : syracuseStep 11376287 = 17064431) B17064431
theorem B3200743 : Blo 1498069 3200743 := bstep (se 1 (by rfl) ⟨2400557, by rfl⟩ : syracuseStep 3200743 = 4801115) B4801115
theorem B3372839 : Blo 1498069 3372839 := bstep (se 1 (by rfl) ⟨2529629, by rfl⟩ : syracuseStep 3372839 = 5059259) B5059259
theorem B2701487 : Blo 1498069 2701487 := bstep (se 1 (by rfl) ⟨2026115, by rfl⟩ : syracuseStep 2701487 = 4052231) B4052231
theorem B3373307 : Blo 1498069 3373307 := bstep (se 1 (by rfl) ⟨2529980, by rfl⟩ : syracuseStep 3373307 = 5059961) B5059961
theorem B14416339 : Blo 1498069 14416339 := bstep (se 1 (by rfl) ⟨10812254, by rfl⟩ : syracuseStep 14416339 = 21624509) B21624509
theorem B13679225 : Blo 1498069 13679225 := bstep (se 2 (by rfl) ⟨5129709, by rfl⟩ : syracuseStep 13679225 = 10259419) B10259419
theorem B5692139 : Blo 1498069 5692139 := bstep (se 1 (by rfl) ⟨4269104, by rfl⟩ : syracuseStep 5692139 = 8538209) B8538209
theorem B8534767 : Blo 1498069 8534767 := bstep (se 1 (by rfl) ⟨6401075, by rfl⟩ : syracuseStep 8534767 = 12802151) B12802151
theorem B34609943 : Blo 1498069 34609943 := bstep (se 1 (by rfl) ⟨25957457, by rfl⟩ : syracuseStep 34609943 = 51914915) B51914915
theorem B3373865 : Blo 1498069 3373865 := bstep (se 2 (by rfl) ⟨1265199, by rfl⟩ : syracuseStep 3373865 = 2530399) B2530399
theorem B19479359 : Blo 1498069 19479359 := bstep (se 1 (by rfl) ⟨14609519, by rfl⟩ : syracuseStep 19479359 = 29219039) B29219039
theorem B48601943 : Blo 1498069 48601943 := bstep (se 1 (by rfl) ⟨36451457, by rfl⟩ : syracuseStep 48601943 = 72902915) B72902915
theorem B46177229 : Blo 1498069 46177229 := bstep (se 3 (by rfl) ⟨8658230, by rfl⟩ : syracuseStep 46177229 = 17316461) B17316461
theorem B7592939 : Blo 1498069 7592939 := bstep (se 1 (by rfl) ⟨5694704, by rfl⟩ : syracuseStep 7592939 = 11389409) B11389409
theorem B3374063 : Blo 1498069 3374063 := bstep (se 1 (by rfl) ⟨2530547, by rfl⟩ : syracuseStep 3374063 = 5061095) B5061095
theorem B1498267 : Blo 1498069 1498267 := bstep (se 1 (by rfl) ⟨1123700, by rfl⟩ : syracuseStep 1498267 = 2247401) B2247401
theorem B1498303 : Blo 1498069 1498303 := bstep (se 1 (by rfl) ⟨1123727, by rfl⟩ : syracuseStep 1498303 = 2247455) B2247455
theorem B5692625 : Blo 1498069 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B1686811 : Blo 1498069 1686811 := bstep (se 1 (by rfl) ⟨1265108, by rfl⟩ : syracuseStep 1686811 = 2530217) B2530217
theorem B1686847 : Blo 1498069 1686847 := bstep (se 1 (by rfl) ⟨1265135, by rfl⟩ : syracuseStep 1686847 = 2530271) B2530271
theorem B1498527 : Blo 1498069 1498527 := bstep (se 1 (by rfl) ⟨1123895, by rfl⟩ : syracuseStep 1498527 = 2247791) B2247791
theorem B1498591 : Blo 1498069 1498591 := bstep (se 1 (by rfl) ⟨1123943, by rfl⟩ : syracuseStep 1498591 = 2247887) B2247887
theorem B82067039 : Blo 1498069 82067039 := bstep (se 1 (by rfl) ⟨61550279, by rfl⟩ : syracuseStep 82067039 = 123100559) B123100559
theorem B28810991 : Blo 1498069 28810991 := bstep (se 1 (by rfl) ⟨21608243, by rfl⟩ : syracuseStep 28810991 = 43216487) B43216487
theorem B1687279 : Blo 1498069 1687279 := bstep (se 1 (by rfl) ⟨1265459, by rfl⟩ : syracuseStep 1687279 = 2530919) B2530919
theorem B1498907 : Blo 1498069 1498907 := bstep (se 1 (by rfl) ⟨1124180, by rfl⟩ : syracuseStep 1498907 = 2248361) B2248361
theorem B3792703 : Blo 1498069 3792703 := bstep (se 1 (by rfl) ⟨2844527, by rfl⟩ : syracuseStep 3792703 = 5689055) B5689055
theorem B1687423 : Blo 1498069 1687423 := bstep (se 1 (by rfl) ⟨1265567, by rfl⟩ : syracuseStep 1687423 = 2531135) B2531135
theorem B1499615 : Blo 1498069 1499615 := bstep (se 1 (by rfl) ⟨1124711, by rfl⟩ : syracuseStep 1499615 = 2249423) B2249423
theorem B17793527 : Blo 1498069 17793527 := bstep (se 1 (by rfl) ⟨13345145, by rfl⟩ : syracuseStep 17793527 = 26690291) B26690291
theorem B3793463 : Blo 1498069 3793463 := bstep (se 1 (by rfl) ⟨2845097, by rfl⟩ : syracuseStep 3793463 = 5690195) B5690195
theorem B11379689 : Blo 1498069 11379689 := bstep (se 2 (by rfl) ⟨4267383, by rfl⟩ : syracuseStep 11379689 = 8534767) B8534767
theorem B4801627 : Blo 1498069 4801627 := bstep (se 1 (by rfl) ⟨3601220, by rfl⟩ : syracuseStep 4801627 = 7202441) B7202441
theorem B8537183 : Blo 1498069 8537183 := bstep (se 1 (by rfl) ⟨6402887, by rfl⟩ : syracuseStep 8537183 = 12805775) B12805775
theorem B9602333 : Blo 1498069 9602333 := bstep (se 3 (by rfl) ⟨1800437, by rfl⟩ : syracuseStep 9602333 = 3600875) B3600875
theorem B36488825 : Blo 1498069 36488825 := bstep (se 2 (by rfl) ⟨13683309, by rfl⟩ : syracuseStep 36488825 = 27366619) B27366619
theorem B9119483 : Blo 1498069 9119483 := bstep (se 1 (by rfl) ⟨6839612, by rfl⟩ : syracuseStep 9119483 = 13679225) B13679225
theorem B3794759 : Blo 1498069 3794759 := bstep (se 1 (by rfl) ⟨2846069, by rfl⟩ : syracuseStep 3794759 = 5692139) B5692139
theorem B6080339 : Blo 1498069 6080339 := bstep (se 1 (by rfl) ⟨4560254, by rfl⟩ : syracuseStep 6080339 = 9120509) B9120509
theorem B8439677 : Blo 1498069 8439677 := bstep (se 3 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 8439677 = 3164879) B3164879
theorem B12986239 : Blo 1498069 12986239 := bstep (se 1 (by rfl) ⟨9739679, by rfl⟩ : syracuseStep 12986239 = 19479359) B19479359
theorem B32401295 : Blo 1498069 32401295 := bstep (se 1 (by rfl) ⟨24300971, by rfl⟩ : syracuseStep 32401295 = 48601943) B48601943
theorem B3795083 : Blo 1498069 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B5056937 : Blo 1498069 5056937 := bstep (se 2 (by rfl) ⟨1896351, by rfl⟩ : syracuseStep 5056937 = 3792703) B3792703
theorem B2247419 : Blo 1498069 2247419 := bstep (se 1 (by rfl) ⟨1685564, by rfl⟩ : syracuseStep 2247419 = 3371129) B3371129
theorem B4049903 : Blo 1498069 4049903 := bstep (se 1 (by rfl) ⟨3037427, by rfl⟩ : syracuseStep 4049903 = 6074855) B6074855
theorem B19221785 : Blo 1498069 19221785 := bstep (se 2 (by rfl) ⟨7208169, by rfl⟩ : syracuseStep 19221785 = 14416339) B14416339
theorem B7589375 : Blo 1498069 7589375 := bstep (se 1 (by rfl) ⟨5692031, by rfl⟩ : syracuseStep 7589375 = 11384063) B11384063
theorem B2248559 : Blo 1498069 2248559 := bstep (se 1 (by rfl) ⟨1686419, by rfl⟩ : syracuseStep 2248559 = 3372839) B3372839
theorem B3371003 : Blo 1498069 3371003 := bstep (se 1 (by rfl) ⟨2528252, by rfl⟩ : syracuseStep 3371003 = 5056505) B5056505
theorem B3600521 : Blo 1498069 3600521 := bstep (se 2 (by rfl) ⟨1350195, by rfl⟩ : syracuseStep 3600521 = 2700391) B2700391
theorem B2248871 : Blo 1498069 2248871 := bstep (se 1 (by rfl) ⟨1686653, by rfl⟩ : syracuseStep 2248871 = 3373307) B3373307
theorem B2249081 : Blo 1498069 2249081 := bstep (se 2 (by rfl) ⟨843405, by rfl⟩ : syracuseStep 2249081 = 1686811) B1686811
theorem B2249129 : Blo 1498069 2249129 := bstep (se 2 (by rfl) ⟨843423, by rfl⟩ : syracuseStep 2249129 = 1686847) B1686847
theorem B23073295 : Blo 1498069 23073295 := bstep (se 1 (by rfl) ⟨17304971, by rfl⟩ : syracuseStep 23073295 = 34609943) B34609943
theorem B2249243 : Blo 1498069 2249243 := bstep (se 1 (by rfl) ⟨1686932, by rfl⟩ : syracuseStep 2249243 = 3373865) B3373865
theorem B1897015 : Blo 1498069 1897015 := bstep (se 1 (by rfl) ⟨1422761, by rfl⟩ : syracuseStep 1897015 = 2845523) B2845523
theorem B2249375 : Blo 1498069 2249375 := bstep (se 1 (by rfl) ⟨1687031, by rfl⟩ : syracuseStep 2249375 = 3374063) B3374063
theorem B5059367 : Blo 1498069 5059367 := bstep (se 1 (by rfl) ⟨3794525, by rfl⟩ : syracuseStep 5059367 = 7589051) B7589051
theorem B9122651 : Blo 1498069 9122651 := bstep (se 1 (by rfl) ⟨6841988, by rfl⟩ : syracuseStep 9122651 = 13683977) B13683977
theorem B2249705 : Blo 1498069 2249705 := bstep (se 2 (by rfl) ⟨843639, by rfl⟩ : syracuseStep 2249705 = 1687279) B1687279
theorem B54711359 : Blo 1498069 54711359 := bstep (se 1 (by rfl) ⟨41033519, by rfl⟩ : syracuseStep 54711359 = 82067039) B82067039
theorem B21607559 : Blo 1498069 21607559 := bstep (se 1 (by rfl) ⟨16205669, by rfl⟩ : syracuseStep 21607559 = 32411339) B32411339
theorem B19207327 : Blo 1498069 19207327 := bstep (se 1 (by rfl) ⟨14405495, by rfl⟩ : syracuseStep 19207327 = 28810991) B28810991
theorem B2249897 : Blo 1498069 2249897 := bstep (se 2 (by rfl) ⟨843711, by rfl⟩ : syracuseStep 2249897 = 1687423) B1687423
theorem B123139277 : Blo 1498069 123139277 := bstep (se 3 (by rfl) ⟨23088614, by rfl⟩ : syracuseStep 123139277 = 46177229) B46177229
theorem B17077553 : Blo 1498069 17077553 := bstep (se 2 (by rfl) ⟨6404082, by rfl⟩ : syracuseStep 17077553 = 12808165) B12808165
theorem B12801401 : Blo 1498069 12801401 := bstep (se 2 (by rfl) ⟨4800525, by rfl⟩ : syracuseStep 12801401 = 9601051) B9601051
theorem B394221275 : Blo 1498069 394221275 := bstep (se 1 (by rfl) ⟨295665956, by rfl⟩ : syracuseStep 394221275 = 591331913) B591331913
theorem B3373415 : Blo 1498069 3373415 := bstep (se 1 (by rfl) ⟨2530061, by rfl⟩ : syracuseStep 3373415 = 5060123) B5060123
theorem B7584191 : Blo 1498069 7584191 := bstep (se 1 (by rfl) ⟨5688143, by rfl⟩ : syracuseStep 7584191 = 11376287) B11376287
theorem B2529947 : Blo 1498069 2529947 := bstep (se 1 (by rfl) ⟨1897460, by rfl⟩ : syracuseStep 2529947 = 3794921) B3794921
theorem B1800991 : Blo 1498069 1800991 := bstep (se 1 (by rfl) ⟨1350743, by rfl⟩ : syracuseStep 1800991 = 2701487) B2701487
theorem B1498143 : Blo 1498069 1498143 := bstep (se 1 (by rfl) ⟨1123607, by rfl⟩ : syracuseStep 1498143 = 2247215) B2247215
theorem B5061959 : Blo 1498069 5061959 := bstep (se 1 (by rfl) ⟨3796469, by rfl⟩ : syracuseStep 5061959 = 7592939) B7592939
theorem B1498623 : Blo 1498069 1498623 := bstep (se 1 (by rfl) ⟨1123967, by rfl⟩ : syracuseStep 1498623 = 2247935) B2247935
theorem B4267657 : Blo 1498069 4267657 := bstep (se 2 (by rfl) ⟨1600371, by rfl⟩ : syracuseStep 4267657 = 3200743) B3200743
theorem B7200521 : Blo 1498069 7200521 := bstep (se 2 (by rfl) ⟨2700195, by rfl⟩ : syracuseStep 7200521 = 5400391) B5400391
theorem B12804065 : Blo 1498069 12804065 := bstep (se 2 (by rfl) ⟨4801524, by rfl⟩ : syracuseStep 12804065 = 9603049) B9603049
theorem B2400347 : Blo 1498069 2400347 := bstep (se 1 (by rfl) ⟨1800260, by rfl⟩ : syracuseStep 2400347 = 3600521) B3600521
theorem B1499247 : Blo 1498069 1499247 := bstep (se 1 (by rfl) ⟨1124435, by rfl⟩ : syracuseStep 1499247 = 2248871) B2248871
theorem B1499387 : Blo 1498069 1499387 := bstep (se 1 (by rfl) ⟨1124540, by rfl⟩ : syracuseStep 1499387 = 2249081) B2249081
theorem B1499419 : Blo 1498069 1499419 := bstep (se 1 (by rfl) ⟨1124564, by rfl⟩ : syracuseStep 1499419 = 2249129) B2249129
theorem B1499495 : Blo 1498069 1499495 := bstep (se 1 (by rfl) ⟨1124621, by rfl⟩ : syracuseStep 1499495 = 2249243) B2249243
theorem B1499583 : Blo 1498069 1499583 := bstep (se 1 (by rfl) ⟨1124687, by rfl⟩ : syracuseStep 1499583 = 2249375) B2249375
theorem B7586459 : Blo 1498069 7586459 := bstep (se 1 (by rfl) ⟨5689844, by rfl⟩ : syracuseStep 7586459 = 11379689) B11379689
theorem B1499803 : Blo 1498069 1499803 := bstep (se 1 (by rfl) ⟨1124852, by rfl⟩ : syracuseStep 1499803 = 2249705) B2249705
theorem B1499931 : Blo 1498069 1499931 := bstep (se 1 (by rfl) ⟨1124948, by rfl⟩ : syracuseStep 1499931 = 2249897) B2249897
theorem B82092851 : Blo 1498069 82092851 := bstep (se 1 (by rfl) ⟨61569638, by rfl⟩ : syracuseStep 82092851 = 123139277) B123139277
theorem B2401321 : Blo 1498069 2401321 := bstep (se 2 (by rfl) ⟨900495, by rfl⟩ : syracuseStep 2401321 = 1800991) B1800991
theorem B6079655 : Blo 1498069 6079655 := bstep (se 1 (by rfl) ⟨4559741, by rfl⟩ : syracuseStep 6079655 = 9119483) B9119483
theorem B47449405 : Blo 1498069 47449405 := bstep (se 3 (by rfl) ⟨8896763, by rfl⟩ : syracuseStep 47449405 = 17793527) B17793527
theorem B25609769 : Blo 1498069 25609769 := bstep (se 2 (by rfl) ⟨9603663, by rfl⟩ : syracuseStep 25609769 = 19207327) B19207327
theorem B5056127 : Blo 1498069 5056127 := bstep (se 1 (by rfl) ⟨3792095, by rfl⟩ : syracuseStep 5056127 = 7584191) B7584191
theorem B12814523 : Blo 1498069 12814523 := bstep (se 1 (by rfl) ⟨9610892, by rfl⟩ : syracuseStep 12814523 = 19221785) B19221785
theorem B2247335 : Blo 1498069 2247335 := bstep (se 1 (by rfl) ⟨1685501, by rfl⟩ : syracuseStep 2247335 = 3371003) B3371003
theorem B6081767 : Blo 1498069 6081767 := bstep (se 1 (by rfl) ⟨4561325, by rfl⟩ : syracuseStep 6081767 = 9122651) B9122651
theorem B30764393 : Blo 1498069 30764393 := bstep (se 2 (by rfl) ⟨11536647, by rfl⟩ : syracuseStep 30764393 = 23073295) B23073295
theorem B36474239 : Blo 1498069 36474239 := bstep (se 1 (by rfl) ⟨27355679, by rfl⟩ : syracuseStep 36474239 = 54711359) B54711359
theorem B14405039 : Blo 1498069 14405039 := bstep (se 1 (by rfl) ⟨10803779, by rfl⟩ : syracuseStep 14405039 = 21607559) B21607559
theorem B6401555 : Blo 1498069 6401555 := bstep (se 1 (by rfl) ⟨4801166, by rfl⟩ : syracuseStep 6401555 = 9602333) B9602333
theorem B24325883 : Blo 1498069 24325883 := bstep (se 1 (by rfl) ⟨18244412, by rfl⟩ : syracuseStep 24325883 = 36488825) B36488825
theorem B6402169 : Blo 1498069 6402169 := bstep (se 2 (by rfl) ⟨2400813, by rfl⟩ : syracuseStep 6402169 = 4801627) B4801627
theorem B2248943 : Blo 1498069 2248943 := bstep (se 1 (by rfl) ⟨1686707, by rfl⟩ : syracuseStep 2248943 = 3373415) B3373415
theorem B3371291 : Blo 1498069 3371291 := bstep (se 1 (by rfl) ⟨2528468, by rfl⟩ : syracuseStep 3371291 = 5056937) B5056937
theorem B2699935 : Blo 1498069 2699935 := bstep (se 1 (by rfl) ⟨2024951, by rfl⟩ : syracuseStep 2699935 = 4049903) B4049903
theorem B5690209 : Blo 1498069 5690209 := bstep (se 2 (by rfl) ⟨2133828, by rfl⟩ : syracuseStep 5690209 = 4267657) B4267657
theorem B5059583 : Blo 1498069 5059583 := bstep (se 1 (by rfl) ⟨3794687, by rfl⟩ : syracuseStep 5059583 = 7589375) B7589375
theorem B17314985 : Blo 1498069 17314985 := bstep (se 2 (by rfl) ⟨6493119, by rfl⟩ : syracuseStep 17314985 = 12986239) B12986239
theorem B2528975 : Blo 1498069 2528975 := bstep (se 1 (by rfl) ⟨1896731, by rfl⟩ : syracuseStep 2528975 = 3793463) B3793463
theorem B3372911 : Blo 1498069 3372911 := bstep (se 1 (by rfl) ⟨2529683, by rfl⟩ : syracuseStep 3372911 = 5059367) B5059367
theorem B5691455 : Blo 1498069 5691455 := bstep (se 1 (by rfl) ⟨4268591, by rfl⟩ : syracuseStep 5691455 = 8537183) B8537183
theorem B2529353 : Blo 1498069 2529353 := bstep (se 2 (by rfl) ⟨948507, by rfl⟩ : syracuseStep 2529353 = 1897015) B1897015
theorem B11385035 : Blo 1498069 11385035 := bstep (se 1 (by rfl) ⟨8538776, by rfl⟩ : syracuseStep 11385035 = 17077553) B17077553
theorem B8534267 : Blo 1498069 8534267 := bstep (se 1 (by rfl) ⟨6400700, by rfl⟩ : syracuseStep 8534267 = 12801401) B12801401
theorem B262814183 : Blo 1498069 262814183 := bstep (se 1 (by rfl) ⟨197110637, by rfl⟩ : syracuseStep 262814183 = 394221275) B394221275
theorem B2529839 : Blo 1498069 2529839 := bstep (se 1 (by rfl) ⟨1897379, by rfl⟩ : syracuseStep 2529839 = 3794759) B3794759
theorem B4053559 : Blo 1498069 4053559 := bstep (se 1 (by rfl) ⟨3040169, by rfl⟩ : syracuseStep 4053559 = 6080339) B6080339
theorem B5626451 : Blo 1498069 5626451 := bstep (se 1 (by rfl) ⟨4219838, by rfl⟩ : syracuseStep 5626451 = 8439677) B8439677
theorem B21600863 : Blo 1498069 21600863 := bstep (se 1 (by rfl) ⟨16200647, by rfl⟩ : syracuseStep 21600863 = 32401295) B32401295
theorem B2530055 : Blo 1498069 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B1686631 : Blo 1498069 1686631 := bstep (se 1 (by rfl) ⟨1264973, by rfl⟩ : syracuseStep 1686631 = 2529947) B2529947
theorem B1498279 : Blo 1498069 1498279 := bstep (se 1 (by rfl) ⟨1123709, by rfl⟩ : syracuseStep 1498279 = 2247419) B2247419
theorem B3374639 : Blo 1498069 3374639 := bstep (se 1 (by rfl) ⟨2530979, by rfl⟩ : syracuseStep 3374639 = 5061959) B5061959
theorem B4800347 : Blo 1498069 4800347 := bstep (se 1 (by rfl) ⟨3600260, by rfl⟩ : syracuseStep 4800347 = 7200521) B7200521
theorem B1499039 : Blo 1498069 1499039 := bstep (se 1 (by rfl) ⟨1124279, by rfl⟩ : syracuseStep 1499039 = 2248559) B2248559
theorem B8536043 : Blo 1498069 8536043 := bstep (se 1 (by rfl) ⟨6402032, by rfl⟩ : syracuseStep 8536043 = 12804065) B12804065
theorem B1499295 : Blo 1498069 1499295 := bstep (se 1 (by rfl) ⟨1124471, by rfl⟩ : syracuseStep 1499295 = 2248943) B2248943
theorem B8536225 : Blo 1498069 8536225 := bstep (se 2 (by rfl) ⟨3201084, by rfl⟩ : syracuseStep 8536225 = 6402169) B6402169
theorem B16212413 : Blo 1498069 16212413 := bstep (se 3 (by rfl) ⟨3039827, by rfl⟩ : syracuseStep 16212413 = 6079655) B6079655
theorem B11543323 : Blo 1498069 11543323 := bstep (se 1 (by rfl) ⟨8657492, by rfl⟩ : syracuseStep 11543323 = 17314985) B17314985
theorem B17073179 : Blo 1498069 17073179 := bstep (se 1 (by rfl) ⟨12804884, by rfl⟩ : syracuseStep 17073179 = 25609769) B25609769
theorem B7586945 : Blo 1498069 7586945 := bstep (se 2 (by rfl) ⟨2845104, by rfl⟩ : syracuseStep 7586945 = 5690209) B5690209
theorem B3794303 : Blo 1498069 3794303 := bstep (se 1 (by rfl) ⟨2845727, by rfl⟩ : syracuseStep 3794303 = 5691455) B5691455
theorem B24316159 : Blo 1498069 24316159 := bstep (se 1 (by rfl) ⟨18237119, by rfl⟩ : syracuseStep 24316159 = 36474239) B36474239
theorem B9603359 : Blo 1498069 9603359 := bstep (se 1 (by rfl) ⟨7202519, by rfl⟩ : syracuseStep 9603359 = 14405039) B14405039
theorem B1600231 : Blo 1498069 1600231 := bstep (se 1 (by rfl) ⟨1200173, by rfl⟩ : syracuseStep 1600231 = 2400347) B2400347
theorem B2247527 : Blo 1498069 2247527 := bstep (se 1 (by rfl) ⟨1685645, by rfl⟩ : syracuseStep 2247527 = 3371291) B3371291
theorem B5057639 : Blo 1498069 5057639 := bstep (se 1 (by rfl) ⟨3793229, by rfl⟩ : syracuseStep 5057639 = 7586459) B7586459
theorem B3370751 : Blo 1498069 3370751 := bstep (se 1 (by rfl) ⟨2528063, by rfl⟩ : syracuseStep 3370751 = 5056127) B5056127
theorem B2248607 : Blo 1498069 2248607 := bstep (se 1 (by rfl) ⟨1686455, by rfl⟩ : syracuseStep 2248607 = 3372911) B3372911
theorem B7590023 : Blo 1498069 7590023 := bstep (se 1 (by rfl) ⟨5692517, by rfl⟩ : syracuseStep 7590023 = 11385035) B11385035
theorem B2248841 : Blo 1498069 2248841 := bstep (se 2 (by rfl) ⟨843315, by rfl⟩ : syracuseStep 2248841 = 1686631) B1686631
theorem B5689511 : Blo 1498069 5689511 := bstep (se 1 (by rfl) ⟨4267133, by rfl⟩ : syracuseStep 5689511 = 8534267) B8534267
theorem B20509595 : Blo 1498069 20509595 := bstep (se 1 (by rfl) ⟨15382196, by rfl⟩ : syracuseStep 20509595 = 30764393) B30764393
theorem B2249759 : Blo 1498069 2249759 := bstep (se 1 (by rfl) ⟨1687319, by rfl⟩ : syracuseStep 2249759 = 3374639) B3374639
theorem B16217255 : Blo 1498069 16217255 := bstep (se 1 (by rfl) ⟨12162941, by rfl⟩ : syracuseStep 16217255 = 24325883) B24325883
theorem B3200231 : Blo 1498069 3200231 := bstep (se 1 (by rfl) ⟨2400173, by rfl⟩ : syracuseStep 3200231 = 4800347) B4800347
theorem B5690695 : Blo 1498069 5690695 := bstep (se 1 (by rfl) ⟨4268021, by rfl⟩ : syracuseStep 5690695 = 8536043) B8536043
theorem B54728567 : Blo 1498069 54728567 := bstep (se 1 (by rfl) ⟨41046425, by rfl⟩ : syracuseStep 54728567 = 82092851) B82092851
theorem B3373055 : Blo 1498069 3373055 := bstep (se 1 (by rfl) ⟨2529791, by rfl⟩ : syracuseStep 3373055 = 5059583) B5059583
theorem B5404745 : Blo 1498069 5404745 := bstep (se 2 (by rfl) ⟨2026779, by rfl⟩ : syracuseStep 5404745 = 4053559) B4053559
theorem B14399653 : Blo 1498069 14399653 := bstep (se 4 (by rfl) ⟨1349967, by rfl⟩ : syracuseStep 14399653 = 2699935) B2699935
theorem B1685983 : Blo 1498069 1685983 := bstep (se 1 (by rfl) ⟨1264487, by rfl⟩ : syracuseStep 1685983 = 2528975) B2528975
theorem B1686235 : Blo 1498069 1686235 := bstep (se 1 (by rfl) ⟨1264676, by rfl⟩ : syracuseStep 1686235 = 2529353) B2529353
theorem B3201761 : Blo 1498069 3201761 := bstep (se 2 (by rfl) ⟨1200660, by rfl⟩ : syracuseStep 3201761 = 2401321) B2401321
theorem B8543015 : Blo 1498069 8543015 := bstep (se 1 (by rfl) ⟨6407261, by rfl⟩ : syracuseStep 8543015 = 12814523) B12814523
theorem B175209455 : Blo 1498069 175209455 := bstep (se 1 (by rfl) ⟨131407091, by rfl⟩ : syracuseStep 175209455 = 262814183) B262814183
theorem B1686559 : Blo 1498069 1686559 := bstep (se 1 (by rfl) ⟨1264919, by rfl⟩ : syracuseStep 1686559 = 2529839) B2529839
theorem B3750967 : Blo 1498069 3750967 := bstep (se 1 (by rfl) ⟨2813225, by rfl⟩ : syracuseStep 3750967 = 5626451) B5626451
theorem B14400575 : Blo 1498069 14400575 := bstep (se 1 (by rfl) ⟨10800431, by rfl⟩ : syracuseStep 14400575 = 21600863) B21600863
theorem B63265873 : Blo 1498069 63265873 := bstep (se 2 (by rfl) ⟨23724702, by rfl⟩ : syracuseStep 63265873 = 47449405) B47449405
theorem B1498223 : Blo 1498069 1498223 := bstep (se 1 (by rfl) ⟨1123667, by rfl⟩ : syracuseStep 1498223 = 2247335) B2247335
theorem B1686703 : Blo 1498069 1686703 := bstep (se 1 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 1686703 = 2530055) B2530055
theorem B4054511 : Blo 1498069 4054511 := bstep (se 1 (by rfl) ⟨3040883, by rfl⟩ : syracuseStep 4054511 = 6081767) B6081767
theorem B4267703 : Blo 1498069 4267703 := bstep (se 1 (by rfl) ⟨3200777, by rfl⟩ : syracuseStep 4267703 = 6401555) B6401555
theorem B1499227 : Blo 1498069 1499227 := bstep (se 1 (by rfl) ⟨1124420, by rfl⟩ : syracuseStep 1499227 = 2248841) B2248841
theorem B3793007 : Blo 1498069 3793007 := bstep (se 1 (by rfl) ⟨2844755, by rfl⟩ : syracuseStep 3793007 = 5689511) B5689511
theorem B20005157 : Blo 1498069 20005157 := bstep (se 4 (by rfl) ⟨1875483, by rfl⟩ : syracuseStep 20005157 = 3750967) B3750967
theorem B13673063 : Blo 1498069 13673063 := bstep (se 1 (by rfl) ⟨10254797, by rfl⟩ : syracuseStep 13673063 = 20509595) B20509595
theorem B1499839 : Blo 1498069 1499839 := bstep (se 1 (by rfl) ⟨1124879, by rfl⟩ : syracuseStep 1499839 = 2249759) B2249759
theorem B84354497 : Blo 1498069 84354497 := bstep (se 2 (by rfl) ⟨31632936, by rfl⟩ : syracuseStep 84354497 = 63265873) B63265873
theorem B7587593 : Blo 1498069 7587593 := bstep (se 2 (by rfl) ⟨2845347, by rfl⟩ : syracuseStep 7587593 = 5690695) B5690695
theorem B5695343 : Blo 1498069 5695343 := bstep (se 1 (by rfl) ⟨4271507, by rfl⟩ : syracuseStep 5695343 = 8543015) B8543015
theorem B2845135 : Blo 1498069 2845135 := bstep (se 1 (by rfl) ⟨2133851, by rfl⟩ : syracuseStep 2845135 = 4267703) B4267703
theorem B2247167 : Blo 1498069 2247167 := bstep (se 1 (by rfl) ⟨1685375, by rfl⟩ : syracuseStep 2247167 = 3370751) B3370751
theorem B11381633 : Blo 1498069 11381633 := bstep (se 2 (by rfl) ⟨4268112, by rfl⟩ : syracuseStep 11381633 = 8536225) B8536225
theorem B10808275 : Blo 1498069 10808275 := bstep (se 1 (by rfl) ⟨8106206, by rfl⟩ : syracuseStep 10808275 = 16212413) B16212413
theorem B2247977 : Blo 1498069 2247977 := bstep (se 2 (by rfl) ⟨842991, by rfl⟩ : syracuseStep 2247977 = 1685983) B1685983
theorem B11382119 : Blo 1498069 11382119 := bstep (se 1 (by rfl) ⟨8536589, by rfl⟩ : syracuseStep 11382119 = 17073179) B17073179
theorem B5057963 : Blo 1498069 5057963 := bstep (se 1 (by rfl) ⟨3793472, by rfl⟩ : syracuseStep 5057963 = 7586945) B7586945
theorem B2133487 : Blo 1498069 2133487 := bstep (se 1 (by rfl) ⟨1600115, by rfl⟩ : syracuseStep 2133487 = 3200231) B3200231
theorem B2248313 : Blo 1498069 2248313 := bstep (se 2 (by rfl) ⟨843117, by rfl⟩ : syracuseStep 2248313 = 1686235) B1686235
theorem B2133641 : Blo 1498069 2133641 := bstep (se 2 (by rfl) ⟨800115, by rfl⟩ : syracuseStep 2133641 = 1600231) B1600231
theorem B2248703 : Blo 1498069 2248703 := bstep (se 1 (by rfl) ⟨1686527, by rfl⟩ : syracuseStep 2248703 = 3373055) B3373055
theorem B2248745 : Blo 1498069 2248745 := bstep (se 2 (by rfl) ⟨843279, by rfl⟩ : syracuseStep 2248745 = 1686559) B1686559
theorem B6402239 : Blo 1498069 6402239 := bstep (se 1 (by rfl) ⟨4801679, by rfl⟩ : syracuseStep 6402239 = 9603359) B9603359
theorem B2248937 : Blo 1498069 2248937 := bstep (se 2 (by rfl) ⟨843351, by rfl⟩ : syracuseStep 2248937 = 1686703) B1686703
theorem B2134507 : Blo 1498069 2134507 := bstep (se 1 (by rfl) ⟨1600880, by rfl⟩ : syracuseStep 2134507 = 3201761) B3201761
theorem B116806303 : Blo 1498069 116806303 := bstep (se 1 (by rfl) ⟨87604727, by rfl⟩ : syracuseStep 116806303 = 175209455) B175209455
theorem B3371759 : Blo 1498069 3371759 := bstep (se 1 (by rfl) ⟨2528819, by rfl⟩ : syracuseStep 3371759 = 5057639) B5057639
theorem B5060015 : Blo 1498069 5060015 := bstep (se 1 (by rfl) ⟨3795011, by rfl⟩ : syracuseStep 5060015 = 7590023) B7590023
theorem B19199537 : Blo 1498069 19199537 := bstep (se 2 (by rfl) ⟨7199826, by rfl⟩ : syracuseStep 19199537 = 14399653) B14399653
theorem B32421545 : Blo 1498069 32421545 := bstep (se 2 (by rfl) ⟨12158079, by rfl⟩ : syracuseStep 32421545 = 24316159) B24316159
theorem B10811503 : Blo 1498069 10811503 := bstep (se 1 (by rfl) ⟨8108627, by rfl⟩ : syracuseStep 10811503 = 16217255) B16217255
theorem B2529535 : Blo 1498069 2529535 := bstep (se 1 (by rfl) ⟨1897151, by rfl⟩ : syracuseStep 2529535 = 3794303) B3794303
theorem B15391097 : Blo 1498069 15391097 := bstep (se 2 (by rfl) ⟨5771661, by rfl⟩ : syracuseStep 15391097 = 11543323) B11543323
theorem B36485711 : Blo 1498069 36485711 := bstep (se 1 (by rfl) ⟨27364283, by rfl⟩ : syracuseStep 36485711 = 54728567) B54728567
theorem B3603163 : Blo 1498069 3603163 := bstep (se 1 (by rfl) ⟨2702372, by rfl⟩ : syracuseStep 3603163 = 5404745) B5404745
theorem B1498351 : Blo 1498069 1498351 := bstep (se 1 (by rfl) ⟨1123763, by rfl⟩ : syracuseStep 1498351 = 2247527) B2247527
theorem B9600383 : Blo 1498069 9600383 := bstep (se 1 (by rfl) ⟨7200287, by rfl⟩ : syracuseStep 9600383 = 14400575) B14400575
theorem B2703007 : Blo 1498069 2703007 := bstep (se 1 (by rfl) ⟨2027255, by rfl⟩ : syracuseStep 2703007 = 4054511) B4054511
theorem B1499071 : Blo 1498069 1499071 := bstep (se 1 (by rfl) ⟨1124303, by rfl⟩ : syracuseStep 1499071 = 2248607) B2248607
theorem B1499163 : Blo 1498069 1499163 := bstep (se 1 (by rfl) ⟨1124372, by rfl⟩ : syracuseStep 1499163 = 2248745) B2248745
theorem B4268159 : Blo 1498069 4268159 := bstep (se 1 (by rfl) ⟨3201119, by rfl⟩ : syracuseStep 4268159 = 6402239) B6402239
theorem B1499291 : Blo 1498069 1499291 := bstep (se 1 (by rfl) ⟨1124468, by rfl⟩ : syracuseStep 1499291 = 2248937) B2248937
theorem B13336771 : Blo 1498069 13336771 := bstep (se 1 (by rfl) ⟨10002578, by rfl⟩ : syracuseStep 13336771 = 20005157) B20005157
theorem B3793513 : Blo 1498069 3793513 := bstep (se 2 (by rfl) ⟨1422567, by rfl⟩ : syracuseStep 3793513 = 2845135) B2845135
theorem B25601021 : Blo 1498069 25601021 := bstep (se 3 (by rfl) ⟨4800191, by rfl⟩ : syracuseStep 25601021 = 9600383) B9600383
theorem B14411033 : Blo 1498069 14411033 := bstep (se 2 (by rfl) ⟨5404137, by rfl⟩ : syracuseStep 14411033 = 10808275) B10808275
theorem B24323807 : Blo 1498069 24323807 := bstep (se 1 (by rfl) ⟨18242855, by rfl⟩ : syracuseStep 24323807 = 36485711) B36485711
theorem B7587755 : Blo 1498069 7587755 := bstep (se 1 (by rfl) ⟨5690816, by rfl⟩ : syracuseStep 7587755 = 11381633) B11381633
theorem B2844649 : Blo 1498069 2844649 := bstep (se 2 (by rfl) ⟨1066743, by rfl⟩ : syracuseStep 2844649 = 2133487) B2133487
theorem B7588079 : Blo 1498069 7588079 := bstep (se 1 (by rfl) ⟨5691059, by rfl⟩ : syracuseStep 7588079 = 11382119) B11382119
theorem B2247839 : Blo 1498069 2247839 := bstep (se 1 (by rfl) ⟨1685879, by rfl⟩ : syracuseStep 2247839 = 3371759) B3371759
theorem B2846009 : Blo 1498069 2846009 := bstep (se 2 (by rfl) ⟨1067253, by rfl⟩ : syracuseStep 2846009 = 2134507) B2134507
theorem B4804217 : Blo 1498069 4804217 := bstep (se 2 (by rfl) ⟨1801581, by rfl⟩ : syracuseStep 4804217 = 3603163) B3603163
theorem B12799691 : Blo 1498069 12799691 := bstep (se 1 (by rfl) ⟨9599768, by rfl⟩ : syracuseStep 12799691 = 19199537) B19199537
theorem B21614363 : Blo 1498069 21614363 := bstep (se 1 (by rfl) ⟨16210772, by rfl⟩ : syracuseStep 21614363 = 32421545) B32421545
theorem B5058395 : Blo 1498069 5058395 := bstep (se 1 (by rfl) ⟨3793796, by rfl⟩ : syracuseStep 5058395 = 7587593) B7587593
theorem B3796895 : Blo 1498069 3796895 := bstep (se 1 (by rfl) ⟨2847671, by rfl⟩ : syracuseStep 3796895 = 5695343) B5695343
theorem B10260731 : Blo 1498069 10260731 := bstep (se 1 (by rfl) ⟨7695548, by rfl⟩ : syracuseStep 10260731 = 15391097) B15391097
theorem B5689709 : Blo 1498069 5689709 := bstep (se 3 (by rfl) ⟨1066820, by rfl⟩ : syracuseStep 5689709 = 2133641) B2133641
theorem B3371975 : Blo 1498069 3371975 := bstep (se 1 (by rfl) ⟨2528981, by rfl⟩ : syracuseStep 3371975 = 5057963) B5057963
theorem B2528671 : Blo 1498069 2528671 := bstep (se 1 (by rfl) ⟨1896503, by rfl⟩ : syracuseStep 2528671 = 3793007) B3793007
theorem B14415337 : Blo 1498069 14415337 := bstep (se 2 (by rfl) ⟨5405751, by rfl⟩ : syracuseStep 14415337 = 10811503) B10811503
theorem B3372713 : Blo 1498069 3372713 := bstep (se 2 (by rfl) ⟨1264767, by rfl⟩ : syracuseStep 3372713 = 2529535) B2529535
theorem B9115375 : Blo 1498069 9115375 := bstep (se 1 (by rfl) ⟨6836531, by rfl⟩ : syracuseStep 9115375 = 13673063) B13673063
theorem B622966949 : Blo 1498069 622966949 := bstep (se 4 (by rfl) ⟨58403151, by rfl⟩ : syracuseStep 622966949 = 116806303) B116806303
theorem B3373343 : Blo 1498069 3373343 := bstep (se 1 (by rfl) ⟨2530007, by rfl⟩ : syracuseStep 3373343 = 5060015) B5060015
theorem B56236331 : Blo 1498069 56236331 := bstep (se 1 (by rfl) ⟨42177248, by rfl⟩ : syracuseStep 56236331 = 84354497) B84354497
theorem B1498111 : Blo 1498069 1498111 := bstep (se 1 (by rfl) ⟨1123583, by rfl⟩ : syracuseStep 1498111 = 2247167) B2247167
theorem B1498651 : Blo 1498069 1498651 := bstep (se 1 (by rfl) ⟨1123988, by rfl⟩ : syracuseStep 1498651 = 2247977) B2247977
theorem B3604009 : Blo 1498069 3604009 := bstep (se 2 (by rfl) ⟨1351503, by rfl⟩ : syracuseStep 3604009 = 2703007) B2703007
theorem B1498875 : Blo 1498069 1498875 := bstep (se 1 (by rfl) ⟨1124156, by rfl⟩ : syracuseStep 1498875 = 2248313) B2248313
theorem B1499135 : Blo 1498069 1499135 := bstep (se 1 (by rfl) ⟨1124351, by rfl⟩ : syracuseStep 1499135 = 2248703) B2248703
theorem B6840487 : Blo 1498069 6840487 := bstep (se 1 (by rfl) ⟨5130365, by rfl⟩ : syracuseStep 6840487 = 10260731) B10260731
theorem B3793139 : Blo 1498069 3793139 := bstep (se 1 (by rfl) ⟨2844854, by rfl⟩ : syracuseStep 3793139 = 5689709) B5689709
theorem B415311299 : Blo 1498069 415311299 := bstep (se 1 (by rfl) ⟨311483474, by rfl⟩ : syracuseStep 415311299 = 622966949) B622966949
theorem B19220449 : Blo 1498069 19220449 := bstep (se 2 (by rfl) ⟨7207668, by rfl⟩ : syracuseStep 19220449 = 14415337) B14415337
theorem B2845439 : Blo 1498069 2845439 := bstep (se 1 (by rfl) ⟨2134079, by rfl⟩ : syracuseStep 2845439 = 4268159) B4268159
theorem B2247983 : Blo 1498069 2247983 := bstep (se 1 (by rfl) ⟨1685987, by rfl⟩ : syracuseStep 2247983 = 3371975) B3371975
theorem B17067347 : Blo 1498069 17067347 := bstep (se 1 (by rfl) ⟨12800510, by rfl⟩ : syracuseStep 17067347 = 25601021) B25601021
theorem B5058017 : Blo 1498069 5058017 := bstep (se 2 (by rfl) ⟨1896756, by rfl⟩ : syracuseStep 5058017 = 3793513) B3793513
theorem B2248475 : Blo 1498069 2248475 := bstep (se 1 (by rfl) ⟨1686356, by rfl⟩ : syracuseStep 2248475 = 3372713) B3372713
theorem B16215871 : Blo 1498069 16215871 := bstep (se 1 (by rfl) ⟨12161903, by rfl⟩ : syracuseStep 16215871 = 24323807) B24323807
theorem B5058503 : Blo 1498069 5058503 := bstep (se 1 (by rfl) ⟨3793877, by rfl⟩ : syracuseStep 5058503 = 7587755) B7587755
theorem B5058719 : Blo 1498069 5058719 := bstep (se 1 (by rfl) ⟨3794039, by rfl⟩ : syracuseStep 5058719 = 7588079) B7588079
theorem B2248895 : Blo 1498069 2248895 := bstep (se 1 (by rfl) ⟨1686671, by rfl⟩ : syracuseStep 2248895 = 3373343) B3373343
theorem B37490887 : Blo 1498069 37490887 := bstep (se 1 (by rfl) ⟨28118165, by rfl⟩ : syracuseStep 37490887 = 56236331) B56236331
theorem B3371561 : Blo 1498069 3371561 := bstep (se 2 (by rfl) ⟨1264335, by rfl⟩ : syracuseStep 3371561 = 2528671) B2528671
theorem B4805345 : Blo 1498069 4805345 := bstep (se 2 (by rfl) ⟨1802004, by rfl⟩ : syracuseStep 4805345 = 3604009) B3604009
theorem B1897339 : Blo 1498069 1897339 := bstep (se 1 (by rfl) ⟨1423004, by rfl⟩ : syracuseStep 1897339 = 2846009) B2846009
theorem B12153833 : Blo 1498069 12153833 := bstep (se 2 (by rfl) ⟨4557687, by rfl⟩ : syracuseStep 12153833 = 9115375) B9115375
theorem B8533127 : Blo 1498069 8533127 := bstep (se 1 (by rfl) ⟨6399845, by rfl⟩ : syracuseStep 8533127 = 12799691) B12799691
theorem B3372263 : Blo 1498069 3372263 := bstep (se 1 (by rfl) ⟨2529197, by rfl⟩ : syracuseStep 3372263 = 5058395) B5058395
theorem B17782361 : Blo 1498069 17782361 := bstep (se 2 (by rfl) ⟨6668385, by rfl⟩ : syracuseStep 17782361 = 13336771) B13336771
theorem B9607355 : Blo 1498069 9607355 := bstep (se 1 (by rfl) ⟨7205516, by rfl⟩ : syracuseStep 9607355 = 14411033) B14411033
theorem B1498559 : Blo 1498069 1498559 := bstep (se 1 (by rfl) ⟨1123919, by rfl⟩ : syracuseStep 1498559 = 2247839) B2247839
theorem B3202811 : Blo 1498069 3202811 := bstep (se 1 (by rfl) ⟨2402108, by rfl⟩ : syracuseStep 3202811 = 4804217) B4804217
theorem B14409575 : Blo 1498069 14409575 := bstep (se 1 (by rfl) ⟨10807181, by rfl⟩ : syracuseStep 14409575 = 21614363) B21614363
theorem B2531263 : Blo 1498069 2531263 := bstep (se 1 (by rfl) ⟨1898447, by rfl⟩ : syracuseStep 2531263 = 3796895) B3796895
theorem B3792865 : Blo 1498069 3792865 := bstep (se 2 (by rfl) ⟨1422324, by rfl⟩ : syracuseStep 3792865 = 2844649) B2844649
theorem B1499263 : Blo 1498069 1499263 := bstep (se 1 (by rfl) ⟨1124447, by rfl⟩ : syracuseStep 1499263 = 2248895) B2248895
theorem B49987849 : Blo 1498069 49987849 := bstep (se 2 (by rfl) ⟨18745443, by rfl⟩ : syracuseStep 49987849 = 37490887) B37490887
theorem B3203563 : Blo 1498069 3203563 := bstep (se 1 (by rfl) ⟨2402672, by rfl⟩ : syracuseStep 3203563 = 4805345) B4805345
theorem B8102555 : Blo 1498069 8102555 := bstep (se 1 (by rfl) ⟨6076916, by rfl⟩ : syracuseStep 8102555 = 12153833) B12153833
theorem B276874199 : Blo 1498069 276874199 := bstep (se 1 (by rfl) ⟨207655649, by rfl⟩ : syracuseStep 276874199 = 415311299) B415311299
theorem B11854907 : Blo 1498069 11854907 := bstep (se 1 (by rfl) ⟨8891180, by rfl⟩ : syracuseStep 11854907 = 17782361) B17782361
theorem B21621161 : Blo 1498069 21621161 := bstep (se 2 (by rfl) ⟨8107935, by rfl⟩ : syracuseStep 21621161 = 16215871) B16215871
theorem B5057153 : Blo 1498069 5057153 := bstep (se 2 (by rfl) ⟨1896432, by rfl⟩ : syracuseStep 5057153 = 3792865) B3792865
theorem B25627265 : Blo 1498069 25627265 := bstep (se 2 (by rfl) ⟨9610224, by rfl⟩ : syracuseStep 25627265 = 19220449) B19220449
theorem B9120649 : Blo 1498069 9120649 := bstep (se 2 (by rfl) ⟨3420243, by rfl⟩ : syracuseStep 9120649 = 6840487) B6840487
theorem B2247707 : Blo 1498069 2247707 := bstep (se 1 (by rfl) ⟨1685780, by rfl⟩ : syracuseStep 2247707 = 3371561) B3371561
theorem B5688751 : Blo 1498069 5688751 := bstep (se 1 (by rfl) ⟨4266563, by rfl⟩ : syracuseStep 5688751 = 8533127) B8533127
theorem B2248175 : Blo 1498069 2248175 := bstep (se 1 (by rfl) ⟨1686131, by rfl⟩ : syracuseStep 2248175 = 3372263) B3372263
theorem B1896959 : Blo 1498069 1896959 := bstep (se 1 (by rfl) ⟨1422719, by rfl⟩ : syracuseStep 1896959 = 2845439) B2845439
theorem B3372011 : Blo 1498069 3372011 := bstep (se 1 (by rfl) ⟨2529008, by rfl⟩ : syracuseStep 3372011 = 5058017) B5058017
theorem B2135207 : Blo 1498069 2135207 := bstep (se 1 (by rfl) ⟨1601405, by rfl⟩ : syracuseStep 2135207 = 3202811) B3202811
theorem B9606383 : Blo 1498069 9606383 := bstep (se 1 (by rfl) ⟨7204787, by rfl⟩ : syracuseStep 9606383 = 14409575) B14409575
theorem B3372335 : Blo 1498069 3372335 := bstep (se 1 (by rfl) ⟨2529251, by rfl⟩ : syracuseStep 3372335 = 5058503) B5058503
theorem B3372479 : Blo 1498069 3372479 := bstep (se 1 (by rfl) ⟨2529359, by rfl⟩ : syracuseStep 3372479 = 5058719) B5058719
theorem B2528759 : Blo 1498069 2528759 := bstep (se 1 (by rfl) ⟨1896569, by rfl⟩ : syracuseStep 2528759 = 3793139) B3793139
theorem B2529785 : Blo 1498069 2529785 := bstep (se 2 (by rfl) ⟨948669, by rfl⟩ : syracuseStep 2529785 = 1897339) B1897339
theorem B6404903 : Blo 1498069 6404903 := bstep (se 1 (by rfl) ⟨4803677, by rfl⟩ : syracuseStep 6404903 = 9607355) B9607355
theorem B1498655 : Blo 1498069 1498655 := bstep (se 1 (by rfl) ⟨1123991, by rfl⟩ : syracuseStep 1498655 = 2247983) B2247983
theorem B11378231 : Blo 1498069 11378231 := bstep (se 1 (by rfl) ⟨8533673, by rfl⟩ : syracuseStep 11378231 = 17067347) B17067347
theorem B1498983 : Blo 1498069 1498983 := bstep (se 1 (by rfl) ⟨1124237, by rfl⟩ : syracuseStep 1498983 = 2248475) B2248475
theorem B3375017 : Blo 1498069 3375017 := bstep (se 2 (by rfl) ⟨1265631, by rfl⟩ : syracuseStep 3375017 = 2531263) B2531263
theorem B66650465 : Blo 1498069 66650465 := bstep (se 2 (by rfl) ⟨24993924, by rfl⟩ : syracuseStep 66650465 = 49987849) B49987849
theorem B5693885 : Blo 1498069 5693885 := bstep (se 3 (by rfl) ⟨1067603, by rfl⟩ : syracuseStep 5693885 = 2135207) B2135207
theorem B184582799 : Blo 1498069 184582799 := bstep (se 1 (by rfl) ⟨138437099, by rfl⟩ : syracuseStep 184582799 = 276874199) B276874199
theorem B4269935 : Blo 1498069 4269935 := bstep (se 1 (by rfl) ⟨3202451, by rfl⟩ : syracuseStep 4269935 = 6404903) B6404903
theorem B5401703 : Blo 1498069 5401703 := bstep (se 1 (by rfl) ⟨4051277, by rfl⟩ : syracuseStep 5401703 = 8102555) B8102555
theorem B4271417 : Blo 1498069 4271417 := bstep (se 2 (by rfl) ⟨1601781, by rfl⟩ : syracuseStep 4271417 = 3203563) B3203563
theorem B2248007 : Blo 1498069 2248007 := bstep (se 1 (by rfl) ⟨1686005, by rfl⟩ : syracuseStep 2248007 = 3372011) B3372011
theorem B2248223 : Blo 1498069 2248223 := bstep (se 1 (by rfl) ⟨1686167, by rfl⟩ : syracuseStep 2248223 = 3372335) B3372335
theorem B2248319 : Blo 1498069 2248319 := bstep (se 1 (by rfl) ⟨1686239, by rfl⟩ : syracuseStep 2248319 = 3372479) B3372479
theorem B12160865 : Blo 1498069 12160865 := bstep (se 2 (by rfl) ⟨4560324, by rfl⟩ : syracuseStep 12160865 = 9120649) B9120649
theorem B5058557 : Blo 1498069 5058557 := bstep (se 3 (by rfl) ⟨948479, by rfl⟩ : syracuseStep 5058557 = 1896959) B1896959
theorem B14414107 : Blo 1498069 14414107 := bstep (se 1 (by rfl) ⟨10810580, by rfl⟩ : syracuseStep 14414107 = 21621161) B21621161
theorem B3371435 : Blo 1498069 3371435 := bstep (se 1 (by rfl) ⟨2528576, by rfl⟩ : syracuseStep 3371435 = 5057153) B5057153
theorem B17084843 : Blo 1498069 17084843 := bstep (se 1 (by rfl) ⟨12813632, by rfl⟩ : syracuseStep 17084843 = 25627265) B25627265
theorem B2250011 : Blo 1498069 2250011 := bstep (se 1 (by rfl) ⟨1687508, by rfl⟩ : syracuseStep 2250011 = 3375017) B3375017
theorem B7903271 : Blo 1498069 7903271 := bstep (se 1 (by rfl) ⟨5927453, by rfl⟩ : syracuseStep 7903271 = 11854907) B11854907
theorem B6404255 : Blo 1498069 6404255 := bstep (se 1 (by rfl) ⟨4803191, by rfl⟩ : syracuseStep 6404255 = 9606383) B9606383
theorem B1685839 : Blo 1498069 1685839 := bstep (se 1 (by rfl) ⟨1264379, by rfl⟩ : syracuseStep 1685839 = 2528759) B2528759
theorem B1686523 : Blo 1498069 1686523 := bstep (se 1 (by rfl) ⟨1264892, by rfl⟩ : syracuseStep 1686523 = 2529785) B2529785
theorem B7585001 : Blo 1498069 7585001 := bstep (se 2 (by rfl) ⟨2844375, by rfl⟩ : syracuseStep 7585001 = 5688751) B5688751
theorem B1498471 : Blo 1498069 1498471 := bstep (se 1 (by rfl) ⟨1123853, by rfl⟩ : syracuseStep 1498471 = 2247707) B2247707
theorem B1498783 : Blo 1498069 1498783 := bstep (se 1 (by rfl) ⟨1124087, by rfl⟩ : syracuseStep 1498783 = 2248175) B2248175
theorem B7585487 : Blo 1498069 7585487 := bstep (se 1 (by rfl) ⟨5689115, by rfl⟩ : syracuseStep 7585487 = 11378231) B11378231
theorem B19218809 : Blo 1498069 19218809 := bstep (se 2 (by rfl) ⟨7207053, by rfl⟩ : syracuseStep 19218809 = 14414107) B14414107
theorem B1500007 : Blo 1498069 1500007 := bstep (se 1 (by rfl) ⟨1125005, by rfl⟩ : syracuseStep 1500007 = 2250011) B2250011
theorem B177734573 : Blo 1498069 177734573 := bstep (se 3 (by rfl) ⟨33325232, by rfl⟩ : syracuseStep 177734573 = 66650465) B66650465
theorem B5268847 : Blo 1498069 5268847 := bstep (se 1 (by rfl) ⟨3951635, by rfl⟩ : syracuseStep 5268847 = 7903271) B7903271
theorem B4269503 : Blo 1498069 4269503 := bstep (se 1 (by rfl) ⟨3202127, by rfl⟩ : syracuseStep 4269503 = 6404255) B6404255
theorem B5056667 : Blo 1498069 5056667 := bstep (se 1 (by rfl) ⟨3792500, by rfl⟩ : syracuseStep 5056667 = 7585001) B7585001
theorem B5056991 : Blo 1498069 5056991 := bstep (se 1 (by rfl) ⟨3792743, by rfl⟩ : syracuseStep 5056991 = 7585487) B7585487
theorem B2247623 : Blo 1498069 2247623 := bstep (se 1 (by rfl) ⟨1685717, by rfl⟩ : syracuseStep 2247623 = 3371435) B3371435
theorem B11389895 : Blo 1498069 11389895 := bstep (se 1 (by rfl) ⟨8542421, by rfl⟩ : syracuseStep 11389895 = 17084843) B17084843
theorem B3795923 : Blo 1498069 3795923 := bstep (se 1 (by rfl) ⟨2846942, by rfl⟩ : syracuseStep 3795923 = 5693885) B5693885
theorem B123055199 : Blo 1498069 123055199 := bstep (se 1 (by rfl) ⟨92291399, by rfl⟩ : syracuseStep 123055199 = 184582799) B184582799
theorem B2247785 : Blo 1498069 2247785 := bstep (se 2 (by rfl) ⟨842919, by rfl⟩ : syracuseStep 2247785 = 1685839) B1685839
theorem B2248697 : Blo 1498069 2248697 := bstep (se 2 (by rfl) ⟨843261, by rfl⟩ : syracuseStep 2248697 = 1686523) B1686523
theorem B3601135 : Blo 1498069 3601135 := bstep (se 1 (by rfl) ⟨2700851, by rfl⟩ : syracuseStep 3601135 = 5401703) B5401703
theorem B2847611 : Blo 1498069 2847611 := bstep (se 1 (by rfl) ⟨2135708, by rfl⟩ : syracuseStep 2847611 = 4271417) B4271417
theorem B32428973 : Blo 1498069 32428973 := bstep (se 3 (by rfl) ⟨6080432, by rfl⟩ : syracuseStep 32428973 = 12160865) B12160865
theorem B3372371 : Blo 1498069 3372371 := bstep (se 1 (by rfl) ⟨2529278, by rfl⟩ : syracuseStep 3372371 = 5058557) B5058557
theorem B1498671 : Blo 1498069 1498671 := bstep (se 1 (by rfl) ⟨1124003, by rfl⟩ : syracuseStep 1498671 = 2248007) B2248007
theorem B11386493 : Blo 1498069 11386493 := bstep (se 3 (by rfl) ⟨2134967, by rfl⟩ : syracuseStep 11386493 = 4269935) B4269935
theorem B1498815 : Blo 1498069 1498815 := bstep (se 1 (by rfl) ⟨1124111, by rfl⟩ : syracuseStep 1498815 = 2248223) B2248223
theorem B1498879 : Blo 1498069 1498879 := bstep (se 1 (by rfl) ⟨1124159, by rfl⟩ : syracuseStep 1498879 = 2248319) B2248319
theorem B12812539 : Blo 1498069 12812539 := bstep (se 1 (by rfl) ⟨9609404, by rfl⟩ : syracuseStep 12812539 = 19218809) B19218809
theorem B21619315 : Blo 1498069 21619315 := bstep (se 1 (by rfl) ⟨16214486, by rfl⟩ : syracuseStep 21619315 = 32428973) B32428973
theorem B118489715 : Blo 1498069 118489715 := bstep (se 1 (by rfl) ⟨88867286, by rfl⟩ : syracuseStep 118489715 = 177734573) B177734573
theorem B4801513 : Blo 1498069 4801513 := bstep (se 2 (by rfl) ⟨1800567, by rfl⟩ : syracuseStep 4801513 = 3601135) B3601135
theorem B82036799 : Blo 1498069 82036799 := bstep (se 1 (by rfl) ⟨61527599, by rfl⟩ : syracuseStep 82036799 = 123055199) B123055199
theorem B2248247 : Blo 1498069 2248247 := bstep (se 1 (by rfl) ⟨1686185, by rfl⟩ : syracuseStep 2248247 = 3372371) B3372371
theorem B2846335 : Blo 1498069 2846335 := bstep (se 1 (by rfl) ⟨2134751, by rfl⟩ : syracuseStep 2846335 = 4269503) B4269503
theorem B3371111 : Blo 1498069 3371111 := bstep (se 1 (by rfl) ⟨2528333, by rfl⟩ : syracuseStep 3371111 = 5056667) B5056667
theorem B3371327 : Blo 1498069 3371327 := bstep (se 1 (by rfl) ⟨2528495, by rfl⟩ : syracuseStep 3371327 = 5056991) B5056991
theorem B7025129 : Blo 1498069 7025129 := bstep (se 2 (by rfl) ⟨2634423, by rfl⟩ : syracuseStep 7025129 = 5268847) B5268847
theorem B7590995 : Blo 1498069 7590995 := bstep (se 1 (by rfl) ⟨5693246, by rfl⟩ : syracuseStep 7590995 = 11386493) B11386493
theorem B1499131 : Blo 1498069 1499131 := bstep (se 1 (by rfl) ⟨1124348, by rfl⟩ : syracuseStep 1499131 = 2248697) B2248697
theorem B1898407 : Blo 1498069 1898407 := bstep (se 1 (by rfl) ⟨1423805, by rfl⟩ : syracuseStep 1898407 = 2847611) B2847611
theorem B1498415 : Blo 1498069 1498415 := bstep (se 1 (by rfl) ⟨1123811, by rfl⟩ : syracuseStep 1498415 = 2247623) B2247623
theorem B7593263 : Blo 1498069 7593263 := bstep (se 1 (by rfl) ⟨5694947, by rfl⟩ : syracuseStep 7593263 = 11389895) B11389895
theorem B2530615 : Blo 1498069 2530615 := bstep (se 1 (by rfl) ⟨1897961, by rfl⟩ : syracuseStep 2530615 = 3795923) B3795923
theorem B1498523 : Blo 1498069 1498523 := bstep (se 1 (by rfl) ⟨1123892, by rfl⟩ : syracuseStep 1498523 = 2247785) B2247785
theorem B54691199 : Blo 1498069 54691199 := bstep (se 1 (by rfl) ⟨41018399, by rfl⟩ : syracuseStep 54691199 = 82036799) B82036799
theorem B3795113 : Blo 1498069 3795113 := bstep (se 2 (by rfl) ⟨1423167, by rfl⟩ : syracuseStep 3795113 = 2846335) B2846335
theorem B2247407 : Blo 1498069 2247407 := bstep (se 1 (by rfl) ⟨1685555, by rfl⟩ : syracuseStep 2247407 = 3371111) B3371111
theorem B2247551 : Blo 1498069 2247551 := bstep (se 1 (by rfl) ⟨1685663, by rfl⟩ : syracuseStep 2247551 = 3371327) B3371327
theorem B17083385 : Blo 1498069 17083385 := bstep (se 2 (by rfl) ⟨6406269, by rfl⟩ : syracuseStep 17083385 = 12812539) B12812539
theorem B6402017 : Blo 1498069 6402017 := bstep (se 2 (by rfl) ⟨2400756, by rfl⟩ : syracuseStep 6402017 = 4801513) B4801513
theorem B4683419 : Blo 1498069 4683419 := bstep (se 1 (by rfl) ⟨3512564, by rfl⟩ : syracuseStep 4683419 = 7025129) B7025129
theorem B78993143 : Blo 1498069 78993143 := bstep (se 1 (by rfl) ⟨59244857, by rfl⟩ : syracuseStep 78993143 = 118489715) B118489715
theorem B5060663 : Blo 1498069 5060663 := bstep (se 1 (by rfl) ⟨3795497, by rfl⟩ : syracuseStep 5060663 = 7590995) B7590995
theorem B28825753 : Blo 1498069 28825753 := bstep (se 2 (by rfl) ⟨10809657, by rfl⟩ : syracuseStep 28825753 = 21619315) B21619315
theorem B3374153 : Blo 1498069 3374153 := bstep (se 2 (by rfl) ⟨1265307, by rfl⟩ : syracuseStep 3374153 = 2530615) B2530615
theorem B5062175 : Blo 1498069 5062175 := bstep (se 1 (by rfl) ⟨3796631, by rfl⟩ : syracuseStep 5062175 = 7593263) B7593263
theorem B1498831 : Blo 1498069 1498831 := bstep (se 1 (by rfl) ⟨1124123, by rfl⟩ : syracuseStep 1498831 = 2248247) B2248247
theorem B2531209 : Blo 1498069 2531209 := bstep (se 2 (by rfl) ⟨949203, by rfl⟩ : syracuseStep 2531209 = 1898407) B1898407
theorem B3122279 : Blo 1498069 3122279 := bstep (se 1 (by rfl) ⟨2341709, by rfl⟩ : syracuseStep 3122279 = 4683419) B4683419
theorem B11388923 : Blo 1498069 11388923 := bstep (se 1 (by rfl) ⟨8541692, by rfl⟩ : syracuseStep 11388923 = 17083385) B17083385
theorem B52662095 : Blo 1498069 52662095 := bstep (se 1 (by rfl) ⟨39496571, by rfl⟩ : syracuseStep 52662095 = 78993143) B78993143
theorem B2249435 : Blo 1498069 2249435 := bstep (se 1 (by rfl) ⟨1687076, by rfl⟩ : syracuseStep 2249435 = 3374153) B3374153
theorem B38434337 : Blo 1498069 38434337 := bstep (se 2 (by rfl) ⟨14412876, by rfl⟩ : syracuseStep 38434337 = 28825753) B28825753
theorem B36460799 : Blo 1498069 36460799 := bstep (se 1 (by rfl) ⟨27345599, by rfl⟩ : syracuseStep 36460799 = 54691199) B54691199
theorem B3373775 : Blo 1498069 3373775 := bstep (se 1 (by rfl) ⟨2530331, by rfl⟩ : syracuseStep 3373775 = 5060663) B5060663
theorem B2530075 : Blo 1498069 2530075 := bstep (se 1 (by rfl) ⟨1897556, by rfl⟩ : syracuseStep 2530075 = 3795113) B3795113
theorem B1498271 : Blo 1498069 1498271 := bstep (se 1 (by rfl) ⟨1123703, by rfl⟩ : syracuseStep 1498271 = 2247407) B2247407
theorem B1498367 : Blo 1498069 1498367 := bstep (se 1 (by rfl) ⟨1123775, by rfl⟩ : syracuseStep 1498367 = 2247551) B2247551
theorem B3374783 : Blo 1498069 3374783 := bstep (se 1 (by rfl) ⟨2531087, by rfl⟩ : syracuseStep 3374783 = 5062175) B5062175
theorem B3374945 : Blo 1498069 3374945 := bstep (se 2 (by rfl) ⟨1265604, by rfl⟩ : syracuseStep 3374945 = 2531209) B2531209
theorem B4268011 : Blo 1498069 4268011 := bstep (se 1 (by rfl) ⟨3201008, by rfl⟩ : syracuseStep 4268011 = 6402017) B6402017
theorem B1499623 : Blo 1498069 1499623 := bstep (se 1 (by rfl) ⟨1124717, by rfl⟩ : syracuseStep 1499623 = 2249435) B2249435
theorem B2081519 : Blo 1498069 2081519 := bstep (se 1 (by rfl) ⟨1561139, by rfl⟩ : syracuseStep 2081519 = 3122279) B3122279
theorem B24307199 : Blo 1498069 24307199 := bstep (se 1 (by rfl) ⟨18230399, by rfl⟩ : syracuseStep 24307199 = 36460799) B36460799
theorem B2249183 : Blo 1498069 2249183 := bstep (se 1 (by rfl) ⟨1686887, by rfl⟩ : syracuseStep 2249183 = 3373775) B3373775
theorem B2249855 : Blo 1498069 2249855 := bstep (se 1 (by rfl) ⟨1687391, by rfl⟩ : syracuseStep 2249855 = 3374783) B3374783
theorem B35108063 : Blo 1498069 35108063 := bstep (se 1 (by rfl) ⟨26331047, by rfl⟩ : syracuseStep 35108063 = 52662095) B52662095
theorem B2249963 : Blo 1498069 2249963 := bstep (se 1 (by rfl) ⟨1687472, by rfl⟩ : syracuseStep 2249963 = 3374945) B3374945
theorem B5690681 : Blo 1498069 5690681 := bstep (se 2 (by rfl) ⟨2134005, by rfl⟩ : syracuseStep 5690681 = 4268011) B4268011
theorem B25622891 : Blo 1498069 25622891 := bstep (se 1 (by rfl) ⟨19217168, by rfl⟩ : syracuseStep 25622891 = 38434337) B38434337
theorem B3373433 : Blo 1498069 3373433 := bstep (se 2 (by rfl) ⟨1265037, by rfl⟩ : syracuseStep 3373433 = 2530075) B2530075
theorem B7592615 : Blo 1498069 7592615 := bstep (se 1 (by rfl) ⟨5694461, by rfl⟩ : syracuseStep 7592615 = 11388923) B11388923
theorem B1499455 : Blo 1498069 1499455 := bstep (se 1 (by rfl) ⟨1124591, by rfl⟩ : syracuseStep 1499455 = 2249183) B2249183
theorem B1499903 : Blo 1498069 1499903 := bstep (se 1 (by rfl) ⟨1124927, by rfl⟩ : syracuseStep 1499903 = 2249855) B2249855
theorem B23405375 : Blo 1498069 23405375 := bstep (se 1 (by rfl) ⟨17554031, by rfl⟩ : syracuseStep 23405375 = 35108063) B35108063
theorem B1499975 : Blo 1498069 1499975 := bstep (se 1 (by rfl) ⟨1124981, by rfl⟩ : syracuseStep 1499975 = 2249963) B2249963
theorem B3793787 : Blo 1498069 3793787 := bstep (se 1 (by rfl) ⟨2845340, by rfl⟩ : syracuseStep 3793787 = 5690681) B5690681
theorem B16204799 : Blo 1498069 16204799 := bstep (se 1 (by rfl) ⟨12153599, by rfl⟩ : syracuseStep 16204799 = 24307199) B24307199
theorem B17081927 : Blo 1498069 17081927 := bstep (se 1 (by rfl) ⟨12811445, by rfl⟩ : syracuseStep 17081927 = 25622891) B25622891
theorem B22202869 : Blo 1498069 22202869 := bstep (se 5 (by rfl) ⟨1040759, by rfl⟩ : syracuseStep 22202869 = 2081519) B2081519
theorem B2248955 : Blo 1498069 2248955 := bstep (se 1 (by rfl) ⟨1686716, by rfl⟩ : syracuseStep 2248955 = 3373433) B3373433
theorem B5061743 : Blo 1498069 5061743 := bstep (se 1 (by rfl) ⟨3796307, by rfl⟩ : syracuseStep 5061743 = 7592615) B7592615
theorem B1499303 : Blo 1498069 1499303 := bstep (se 1 (by rfl) ⟨1124477, by rfl⟩ : syracuseStep 1499303 = 2248955) B2248955
theorem B11387951 : Blo 1498069 11387951 := bstep (se 1 (by rfl) ⟨8540963, by rfl⟩ : syracuseStep 11387951 = 17081927) B17081927
theorem B2529191 : Blo 1498069 2529191 := bstep (se 1 (by rfl) ⟨1896893, by rfl⟩ : syracuseStep 2529191 = 3793787) B3793787
theorem B29603825 : Blo 1498069 29603825 := bstep (se 2 (by rfl) ⟨11101434, by rfl⟩ : syracuseStep 29603825 = 22202869) B22202869
theorem B3374495 : Blo 1498069 3374495 := bstep (se 1 (by rfl) ⟨2530871, by rfl⟩ : syracuseStep 3374495 = 5061743) B5061743
theorem B62414333 : Blo 1498069 62414333 := bstep (se 3 (by rfl) ⟨11702687, by rfl⟩ : syracuseStep 62414333 = 23405375) B23405375
theorem B43212797 : Blo 1498069 43212797 := bstep (se 3 (by rfl) ⟨8102399, by rfl⟩ : syracuseStep 43212797 = 16204799) B16204799
theorem B19735883 : Blo 1498069 19735883 := bstep (se 1 (by rfl) ⟨14801912, by rfl⟩ : syracuseStep 19735883 = 29603825) B29603825
theorem B41609555 : Blo 1498069 41609555 := bstep (se 1 (by rfl) ⟨31207166, by rfl⟩ : syracuseStep 41609555 = 62414333) B62414333
theorem B2249663 : Blo 1498069 2249663 := bstep (se 1 (by rfl) ⟨1687247, by rfl⟩ : syracuseStep 2249663 = 3374495) B3374495
theorem B28808531 : Blo 1498069 28808531 := bstep (se 1 (by rfl) ⟨21606398, by rfl⟩ : syracuseStep 28808531 = 43212797) B43212797
theorem B7591967 : Blo 1498069 7591967 := bstep (se 1 (by rfl) ⟨5693975, by rfl⟩ : syracuseStep 7591967 = 11387951) B11387951
theorem B1686127 : Blo 1498069 1686127 := bstep (se 1 (by rfl) ⟨1264595, by rfl⟩ : syracuseStep 1686127 = 2529191) B2529191
theorem B1499775 : Blo 1498069 1499775 := bstep (se 1 (by rfl) ⟨1124831, by rfl⟩ : syracuseStep 1499775 = 2249663) B2249663
theorem B13157255 : Blo 1498069 13157255 := bstep (se 1 (by rfl) ⟨9867941, by rfl⟩ : syracuseStep 13157255 = 19735883) B19735883
theorem B27739703 : Blo 1498069 27739703 := bstep (se 1 (by rfl) ⟨20804777, by rfl⟩ : syracuseStep 27739703 = 41609555) B41609555
theorem B2248169 : Blo 1498069 2248169 := bstep (se 2 (by rfl) ⟨843063, by rfl⟩ : syracuseStep 2248169 = 1686127) B1686127
theorem B19205687 : Blo 1498069 19205687 := bstep (se 1 (by rfl) ⟨14404265, by rfl⟩ : syracuseStep 19205687 = 28808531) B28808531
theorem B5061311 : Blo 1498069 5061311 := bstep (se 1 (by rfl) ⟨3795983, by rfl⟩ : syracuseStep 5061311 = 7591967) B7591967
theorem B8771503 : Blo 1498069 8771503 := bstep (se 1 (by rfl) ⟨6578627, by rfl⟩ : syracuseStep 8771503 = 13157255) B13157255
theorem B73972541 : Blo 1498069 73972541 := bstep (se 3 (by rfl) ⟨13869851, by rfl⟩ : syracuseStep 73972541 = 27739703) B27739703
theorem B3374207 : Blo 1498069 3374207 := bstep (se 1 (by rfl) ⟨2530655, by rfl⟩ : syracuseStep 3374207 = 5061311) B5061311
theorem B1498779 : Blo 1498069 1498779 := bstep (se 1 (by rfl) ⟨1124084, by rfl⟩ : syracuseStep 1498779 = 2248169) B2248169
theorem B12803791 : Blo 1498069 12803791 := bstep (se 1 (by rfl) ⟨9602843, by rfl⟩ : syracuseStep 12803791 = 19205687) B19205687
theorem B2249471 : Blo 1498069 2249471 := bstep (se 1 (by rfl) ⟨1687103, by rfl⟩ : syracuseStep 2249471 = 3374207) B3374207
theorem B197260109 : Blo 1498069 197260109 := bstep (se 3 (by rfl) ⟨36986270, by rfl⟩ : syracuseStep 197260109 = 73972541) B73972541
theorem B11695337 : Blo 1498069 11695337 := bstep (se 2 (by rfl) ⟨4385751, by rfl⟩ : syracuseStep 11695337 = 8771503) B8771503
theorem B17071721 : Blo 1498069 17071721 := bstep (se 2 (by rfl) ⟨6401895, by rfl⟩ : syracuseStep 17071721 = 12803791) B12803791
theorem B1499647 : Blo 1498069 1499647 := bstep (se 1 (by rfl) ⟨1124735, by rfl⟩ : syracuseStep 1499647 = 2249471) B2249471
theorem B131506739 : Blo 1498069 131506739 := bstep (se 1 (by rfl) ⟨98630054, by rfl⟩ : syracuseStep 131506739 = 197260109) B197260109
theorem B11381147 : Blo 1498069 11381147 := bstep (se 1 (by rfl) ⟨8535860, by rfl⟩ : syracuseStep 11381147 = 17071721) B17071721
theorem B7796891 : Blo 1498069 7796891 := bstep (se 1 (by rfl) ⟨5847668, by rfl⟩ : syracuseStep 7796891 = 11695337) B11695337
theorem B87671159 : Blo 1498069 87671159 := bstep (se 1 (by rfl) ⟨65753369, by rfl⟩ : syracuseStep 87671159 = 131506739) B131506739
theorem B7587431 : Blo 1498069 7587431 := bstep (se 1 (by rfl) ⟨5690573, by rfl⟩ : syracuseStep 7587431 = 11381147) B11381147
theorem B5197927 : Blo 1498069 5197927 := bstep (se 1 (by rfl) ⟨3898445, by rfl⟩ : syracuseStep 5197927 = 7796891) B7796891
theorem B6930569 : Blo 1498069 6930569 := bstep (se 2 (by rfl) ⟨2598963, by rfl⟩ : syracuseStep 6930569 = 5197927) B5197927
theorem B5058287 : Blo 1498069 5058287 := bstep (se 1 (by rfl) ⟨3793715, by rfl⟩ : syracuseStep 5058287 = 7587431) B7587431
theorem B58447439 : Blo 1498069 58447439 := bstep (se 1 (by rfl) ⟨43835579, by rfl⟩ : syracuseStep 58447439 = 87671159) B87671159
theorem B18481517 : Blo 1498069 18481517 := bstep (se 3 (by rfl) ⟨3465284, by rfl⟩ : syracuseStep 18481517 = 6930569) B6930569
theorem B38964959 : Blo 1498069 38964959 := bstep (se 1 (by rfl) ⟨29223719, by rfl⟩ : syracuseStep 38964959 = 58447439) B58447439
theorem B3372191 : Blo 1498069 3372191 := bstep (se 1 (by rfl) ⟨2529143, by rfl⟩ : syracuseStep 3372191 = 5058287) B5058287
theorem B12321011 : Blo 1498069 12321011 := bstep (se 1 (by rfl) ⟨9240758, by rfl⟩ : syracuseStep 12321011 = 18481517) B18481517
theorem B2248127 : Blo 1498069 2248127 := bstep (se 1 (by rfl) ⟨1686095, by rfl⟩ : syracuseStep 2248127 = 3372191) B3372191
theorem B25976639 : Blo 1498069 25976639 := bstep (se 1 (by rfl) ⟨19482479, by rfl⟩ : syracuseStep 25976639 = 38964959) B38964959
theorem B8214007 : Blo 1498069 8214007 := bstep (se 1 (by rfl) ⟨6160505, by rfl⟩ : syracuseStep 8214007 = 12321011) B12321011
theorem B69271037 : Blo 1498069 69271037 := bstep (se 3 (by rfl) ⟨12988319, by rfl⟩ : syracuseStep 69271037 = 25976639) B25976639
theorem B1498751 : Blo 1498069 1498751 := bstep (se 1 (by rfl) ⟨1124063, by rfl⟩ : syracuseStep 1498751 = 2248127) B2248127
theorem B46180691 : Blo 1498069 46180691 := bstep (se 1 (by rfl) ⟨34635518, by rfl⟩ : syracuseStep 46180691 = 69271037) B69271037
theorem B10952009 : Blo 1498069 10952009 := bstep (se 2 (by rfl) ⟨4107003, by rfl⟩ : syracuseStep 10952009 = 8214007) B8214007
theorem B30787127 : Blo 1498069 30787127 := bstep (se 1 (by rfl) ⟨23090345, by rfl⟩ : syracuseStep 30787127 = 46180691) B46180691
theorem B7301339 : Blo 1498069 7301339 := bstep (se 1 (by rfl) ⟨5476004, by rfl⟩ : syracuseStep 7301339 = 10952009) B10952009
theorem B4867559 : Blo 1498069 4867559 := bstep (se 1 (by rfl) ⟨3650669, by rfl⟩ : syracuseStep 4867559 = 7301339) B7301339
theorem B20524751 : Blo 1498069 20524751 := bstep (se 1 (by rfl) ⟨15393563, by rfl⟩ : syracuseStep 20524751 = 30787127) B30787127
theorem B3245039 : Blo 1498069 3245039 := bstep (se 1 (by rfl) ⟨2433779, by rfl⟩ : syracuseStep 3245039 = 4867559) B4867559
theorem B13683167 : Blo 1498069 13683167 := bstep (se 1 (by rfl) ⟨10262375, by rfl⟩ : syracuseStep 13683167 = 20524751) B20524751
theorem B2163359 : Blo 1498069 2163359 := bstep (se 1 (by rfl) ⟨1622519, by rfl⟩ : syracuseStep 2163359 = 3245039) B3245039
theorem B9122111 : Blo 1498069 9122111 := bstep (se 1 (by rfl) ⟨6841583, by rfl⟩ : syracuseStep 9122111 = 13683167) B13683167
theorem B5768957 : Blo 1498069 5768957 := bstep (se 3 (by rfl) ⟨1081679, by rfl⟩ : syracuseStep 5768957 = 2163359) B2163359
theorem B6081407 : Blo 1498069 6081407 := bstep (se 1 (by rfl) ⟨4561055, by rfl⟩ : syracuseStep 6081407 = 9122111) B9122111
theorem B3845971 : Blo 1498069 3845971 := bstep (se 1 (by rfl) ⟨2884478, by rfl⟩ : syracuseStep 3845971 = 5768957) B5768957
theorem B4054271 : Blo 1498069 4054271 := bstep (se 1 (by rfl) ⟨3040703, by rfl⟩ : syracuseStep 4054271 = 6081407) B6081407
theorem B10811389 : Blo 1498069 10811389 := bstep (se 3 (by rfl) ⟨2027135, by rfl⟩ : syracuseStep 10811389 = 4054271) B4054271
theorem B5127961 : Blo 1498069 5127961 := bstep (se 2 (by rfl) ⟨1922985, by rfl⟩ : syracuseStep 5127961 = 3845971) B3845971
theorem B6837281 : Blo 1498069 6837281 := bstep (se 2 (by rfl) ⟨2563980, by rfl⟩ : syracuseStep 6837281 = 5127961) B5127961
theorem B14415185 : Blo 1498069 14415185 := bstep (se 2 (by rfl) ⟨5405694, by rfl⟩ : syracuseStep 14415185 = 10811389) B10811389
theorem B9610123 : Blo 1498069 9610123 := bstep (se 1 (by rfl) ⟨7207592, by rfl⟩ : syracuseStep 9610123 = 14415185) B14415185
theorem B4558187 : Blo 1498069 4558187 := bstep (se 1 (by rfl) ⟨3418640, by rfl⟩ : syracuseStep 4558187 = 6837281) B6837281
theorem B12813497 : Blo 1498069 12813497 := bstep (se 2 (by rfl) ⟨4805061, by rfl⟩ : syracuseStep 12813497 = 9610123) B9610123
theorem B3038791 : Blo 1498069 3038791 := bstep (se 1 (by rfl) ⟨2279093, by rfl⟩ : syracuseStep 3038791 = 4558187) B4558187
theorem B4051721 : Blo 1498069 4051721 := bstep (se 2 (by rfl) ⟨1519395, by rfl⟩ : syracuseStep 4051721 = 3038791) B3038791
theorem B8542331 : Blo 1498069 8542331 := bstep (se 1 (by rfl) ⟨6406748, by rfl⟩ : syracuseStep 8542331 = 12813497) B12813497
theorem B5694887 : Blo 1498069 5694887 := bstep (se 1 (by rfl) ⟨4271165, by rfl⟩ : syracuseStep 5694887 = 8542331) B8542331
theorem B2701147 : Blo 1498069 2701147 := bstep (se 1 (by rfl) ⟨2025860, by rfl⟩ : syracuseStep 2701147 = 4051721) B4051721
theorem B3796591 : Blo 1498069 3796591 := bstep (se 1 (by rfl) ⟨2847443, by rfl⟩ : syracuseStep 3796591 = 5694887) B5694887
theorem B3601529 : Blo 1498069 3601529 := bstep (se 2 (by rfl) ⟨1350573, by rfl⟩ : syracuseStep 3601529 = 2701147) B2701147
theorem B2401019 : Blo 1498069 2401019 := bstep (se 1 (by rfl) ⟨1800764, by rfl⟩ : syracuseStep 2401019 = 3601529) B3601529
theorem B5062121 : Blo 1498069 5062121 := bstep (se 2 (by rfl) ⟨1898295, by rfl⟩ : syracuseStep 5062121 = 3796591) B3796591
theorem B1600679 : Blo 1498069 1600679 := bstep (se 1 (by rfl) ⟨1200509, by rfl⟩ : syracuseStep 1600679 = 2401019) B2401019
theorem B3374747 : Blo 1498069 3374747 := bstep (se 1 (by rfl) ⟨2531060, by rfl⟩ : syracuseStep 3374747 = 5062121) B5062121
theorem B4268477 : Blo 1498069 4268477 := bstep (se 3 (by rfl) ⟨800339, by rfl⟩ : syracuseStep 4268477 = 1600679) B1600679
theorem B2249831 : Blo 1498069 2249831 := bstep (se 1 (by rfl) ⟨1687373, by rfl⟩ : syracuseStep 2249831 = 3374747) B3374747
theorem B1499887 : Blo 1498069 1499887 := bstep (se 1 (by rfl) ⟨1124915, by rfl⟩ : syracuseStep 1499887 = 2249831) B2249831
theorem B11382605 : Blo 1498069 11382605 := bstep (se 3 (by rfl) ⟨2134238, by rfl⟩ : syracuseStep 11382605 = 4268477) B4268477
theorem B7588403 : Blo 1498069 7588403 := bstep (se 1 (by rfl) ⟨5691302, by rfl⟩ : syracuseStep 7588403 = 11382605) B11382605
theorem B5058935 : Blo 1498069 5058935 := bstep (se 1 (by rfl) ⟨3794201, by rfl⟩ : syracuseStep 5058935 = 7588403) B7588403
theorem B3372623 : Blo 1498069 3372623 := bstep (se 1 (by rfl) ⟨2529467, by rfl⟩ : syracuseStep 3372623 = 5058935) B5058935
theorem B2248415 : Blo 1498069 2248415 := bstep (se 1 (by rfl) ⟨1686311, by rfl⟩ : syracuseStep 2248415 = 3372623) B3372623
theorem B1498943 : Blo 1498069 1498943 := bstep (se 1 (by rfl) ⟨1124207, by rfl⟩ : syracuseStep 1498943 = 2248415) B2248415

theorem C0 (j : ℕ) (h1 : 374517 ≤ j) (h2 : j ≤ 375016) : Blo 1498069 (4 * j + 3) := by
  interval_cases j
  · exact B1498071
  · exact B1498075
  · exact B1498079
  · exact B1498083
  · exact B1498087
  · exact B1498091
  · exact B1498095
  · exact B1498099
  · exact B1498103
  · exact B1498107
  · exact B1498111
  · exact B1498115
  · exact B1498119
  · exact B1498123
  · exact B1498127
  · exact B1498131
  · exact B1498135
  · exact B1498139
  · exact B1498143
  · exact B1498147
  · exact B1498151
  · exact B1498155
  · exact B1498159
  · exact B1498163
  · exact B1498167
  · exact B1498171
  · exact B1498175
  · exact B1498179
  · exact B1498183
  · exact B1498187
  · exact B1498191
  · exact B1498195
  · exact B1498199
  · exact B1498203
  · exact B1498207
  · exact B1498211
  · exact B1498215
  · exact B1498219
  · exact B1498223
  · exact B1498227
  · exact B1498231
  · exact B1498235
  · exact B1498239
  · exact B1498243
  · exact B1498247
  · exact B1498251
  · exact B1498255
  · exact B1498259
  · exact B1498263
  · exact B1498267
  · exact B1498271
  · exact B1498275
  · exact B1498279
  · exact B1498283
  · exact B1498287
  · exact B1498291
  · exact B1498295
  · exact B1498299
  · exact B1498303
  · exact B1498307
  · exact B1498311
  · exact B1498315
  · exact B1498319
  · exact B1498323
  · exact B1498327
  · exact B1498331
  · exact B1498335
  · exact B1498339
  · exact B1498343
  · exact B1498347
  · exact B1498351
  · exact B1498355
  · exact B1498359
  · exact B1498363
  · exact B1498367
  · exact B1498371
  · exact B1498375
  · exact B1498379
  · exact B1498383
  · exact B1498387
  · exact B1498391
  · exact B1498395
  · exact B1498399
  · exact B1498403
  · exact B1498407
  · exact B1498411
  · exact B1498415
  · exact B1498419
  · exact B1498423
  · exact B1498427
  · exact B1498431
  · exact B1498435
  · exact B1498439
  · exact B1498443
  · exact B1498447
  · exact B1498451
  · exact B1498455
  · exact B1498459
  · exact B1498463
  · exact B1498467
  · exact B1498471
  · exact B1498475
  · exact B1498479
  · exact B1498483
  · exact B1498487
  · exact B1498491
  · exact B1498495
  · exact B1498499
  · exact B1498503
  · exact B1498507
  · exact B1498511
  · exact B1498515
  · exact B1498519
  · exact B1498523
  · exact B1498527
  · exact B1498531
  · exact B1498535
  · exact B1498539
  · exact B1498543
  · exact B1498547
  · exact B1498551
  · exact B1498555
  · exact B1498559
  · exact B1498563
  · exact B1498567
  · exact B1498571
  · exact B1498575
  · exact B1498579
  · exact B1498583
  · exact B1498587
  · exact B1498591
  · exact B1498595
  · exact B1498599
  · exact B1498603
  · exact B1498607
  · exact B1498611
  · exact B1498615
  · exact B1498619
  · exact B1498623
  · exact B1498627
  · exact B1498631
  · exact B1498635
  · exact B1498639
  · exact B1498643
  · exact B1498647
  · exact B1498651
  · exact B1498655
  · exact B1498659
  · exact B1498663
  · exact B1498667
  · exact B1498671
  · exact B1498675
  · exact B1498679
  · exact B1498683
  · exact B1498687
  · exact B1498691
  · exact B1498695
  · exact B1498699
  · exact B1498703
  · exact B1498707
  · exact B1498711
  · exact B1498715
  · exact B1498719
  · exact B1498723
  · exact B1498727
  · exact B1498731
  · exact B1498735
  · exact B1498739
  · exact B1498743
  · exact B1498747
  · exact B1498751
  · exact B1498755
  · exact B1498759
  · exact B1498763
  · exact B1498767
  · exact B1498771
  · exact B1498775
  · exact B1498779
  · exact B1498783
  · exact B1498787
  · exact B1498791
  · exact B1498795
  · exact B1498799
  · exact B1498803
  · exact B1498807
  · exact B1498811
  · exact B1498815
  · exact B1498819
  · exact B1498823
  · exact B1498827
  · exact B1498831
  · exact B1498835
  · exact B1498839
  · exact B1498843
  · exact B1498847
  · exact B1498851
  · exact B1498855
  · exact B1498859
  · exact B1498863
  · exact B1498867
  · exact B1498871
  · exact B1498875
  · exact B1498879
  · exact B1498883
  · exact B1498887
  · exact B1498891
  · exact B1498895
  · exact B1498899
  · exact B1498903
  · exact B1498907
  · exact B1498911
  · exact B1498915
  · exact B1498919
  · exact B1498923
  · exact B1498927
  · exact B1498931
  · exact B1498935
  · exact B1498939
  · exact B1498943
  · exact B1498947
  · exact B1498951
  · exact B1498955
  · exact B1498959
  · exact B1498963
  · exact B1498967
  · exact B1498971
  · exact B1498975
  · exact B1498979
  · exact B1498983
  · exact B1498987
  · exact B1498991
  · exact B1498995
  · exact B1498999
  · exact B1499003
  · exact B1499007
  · exact B1499011
  · exact B1499015
  · exact B1499019
  · exact B1499023
  · exact B1499027
  · exact B1499031
  · exact B1499035
  · exact B1499039
  · exact B1499043
  · exact B1499047
  · exact B1499051
  · exact B1499055
  · exact B1499059
  · exact B1499063
  · exact B1499067
  · exact B1499071
  · exact B1499075
  · exact B1499079
  · exact B1499083
  · exact B1499087
  · exact B1499091
  · exact B1499095
  · exact B1499099
  · exact B1499103
  · exact B1499107
  · exact B1499111
  · exact B1499115
  · exact B1499119
  · exact B1499123
  · exact B1499127
  · exact B1499131
  · exact B1499135
  · exact B1499139
  · exact B1499143
  · exact B1499147
  · exact B1499151
  · exact B1499155
  · exact B1499159
  · exact B1499163
  · exact B1499167
  · exact B1499171
  · exact B1499175
  · exact B1499179
  · exact B1499183
  · exact B1499187
  · exact B1499191
  · exact B1499195
  · exact B1499199
  · exact B1499203
  · exact B1499207
  · exact B1499211
  · exact B1499215
  · exact B1499219
  · exact B1499223
  · exact B1499227
  · exact B1499231
  · exact B1499235
  · exact B1499239
  · exact B1499243
  · exact B1499247
  · exact B1499251
  · exact B1499255
  · exact B1499259
  · exact B1499263
  · exact B1499267
  · exact B1499271
  · exact B1499275
  · exact B1499279
  · exact B1499283
  · exact B1499287
  · exact B1499291
  · exact B1499295
  · exact B1499299
  · exact B1499303
  · exact B1499307
  · exact B1499311
  · exact B1499315
  · exact B1499319
  · exact B1499323
  · exact B1499327
  · exact B1499331
  · exact B1499335
  · exact B1499339
  · exact B1499343
  · exact B1499347
  · exact B1499351
  · exact B1499355
  · exact B1499359
  · exact B1499363
  · exact B1499367
  · exact B1499371
  · exact B1499375
  · exact B1499379
  · exact B1499383
  · exact B1499387
  · exact B1499391
  · exact B1499395
  · exact B1499399
  · exact B1499403
  · exact B1499407
  · exact B1499411
  · exact B1499415
  · exact B1499419
  · exact B1499423
  · exact B1499427
  · exact B1499431
  · exact B1499435
  · exact B1499439
  · exact B1499443
  · exact B1499447
  · exact B1499451
  · exact B1499455
  · exact B1499459
  · exact B1499463
  · exact B1499467
  · exact B1499471
  · exact B1499475
  · exact B1499479
  · exact B1499483
  · exact B1499487
  · exact B1499491
  · exact B1499495
  · exact B1499499
  · exact B1499503
  · exact B1499507
  · exact B1499511
  · exact B1499515
  · exact B1499519
  · exact B1499523
  · exact B1499527
  · exact B1499531
  · exact B1499535
  · exact B1499539
  · exact B1499543
  · exact B1499547
  · exact B1499551
  · exact B1499555
  · exact B1499559
  · exact B1499563
  · exact B1499567
  · exact B1499571
  · exact B1499575
  · exact B1499579
  · exact B1499583
  · exact B1499587
  · exact B1499591
  · exact B1499595
  · exact B1499599
  · exact B1499603
  · exact B1499607
  · exact B1499611
  · exact B1499615
  · exact B1499619
  · exact B1499623
  · exact B1499627
  · exact B1499631
  · exact B1499635
  · exact B1499639
  · exact B1499643
  · exact B1499647
  · exact B1499651
  · exact B1499655
  · exact B1499659
  · exact B1499663
  · exact B1499667
  · exact B1499671
  · exact B1499675
  · exact B1499679
  · exact B1499683
  · exact B1499687
  · exact B1499691
  · exact B1499695
  · exact B1499699
  · exact B1499703
  · exact B1499707
  · exact B1499711
  · exact B1499715
  · exact B1499719
  · exact B1499723
  · exact B1499727
  · exact B1499731
  · exact B1499735
  · exact B1499739
  · exact B1499743
  · exact B1499747
  · exact B1499751
  · exact B1499755
  · exact B1499759
  · exact B1499763
  · exact B1499767
  · exact B1499771
  · exact B1499775
  · exact B1499779
  · exact B1499783
  · exact B1499787
  · exact B1499791
  · exact B1499795
  · exact B1499799
  · exact B1499803
  · exact B1499807
  · exact B1499811
  · exact B1499815
  · exact B1499819
  · exact B1499823
  · exact B1499827
  · exact B1499831
  · exact B1499835
  · exact B1499839
  · exact B1499843
  · exact B1499847
  · exact B1499851
  · exact B1499855
  · exact B1499859
  · exact B1499863
  · exact B1499867
  · exact B1499871
  · exact B1499875
  · exact B1499879
  · exact B1499883
  · exact B1499887
  · exact B1499891
  · exact B1499895
  · exact B1499899
  · exact B1499903
  · exact B1499907
  · exact B1499911
  · exact B1499915
  · exact B1499919
  · exact B1499923
  · exact B1499927
  · exact B1499931
  · exact B1499935
  · exact B1499939
  · exact B1499943
  · exact B1499947
  · exact B1499951
  · exact B1499955
  · exact B1499959
  · exact B1499963
  · exact B1499967
  · exact B1499971
  · exact B1499975
  · exact B1499979
  · exact B1499983
  · exact B1499987
  · exact B1499991
  · exact B1499995
  · exact B1499999
  · exact B1500003
  · exact B1500007
  · exact B1500011
  · exact B1500015
  · exact B1500019
  · exact B1500023
  · exact B1500027
  · exact B1500031
  · exact B1500035
  · exact B1500039
  · exact B1500043
  · exact B1500047
  · exact B1500051
  · exact B1500055
  · exact B1500059
  · exact B1500063
  · exact B1500067

theorem solution (m : ℕ) (hlo : 1498069 ≤ m) (hhi : m ≤ 1500069) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 374517 ≤ j := by omega
    have hj2 : j ≤ 375016 := by omega
    have hb : Blo 1498069 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
