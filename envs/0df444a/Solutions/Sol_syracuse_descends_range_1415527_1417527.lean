-- Prove2me | solution 1 for syracuse_descends_range_1415527_1417527
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:41:18.646141+00:00
-- url     : https://prove2.me/submissions/08cee15d-4fcc-4889-8aa4-00bdc2e4b62c

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


theorem B3186701 : Blo 1415527 3186701 := bbase (se 3 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 3186701 = 1195013) (by norm_num)
theorem B3186773 : Blo 1415527 3186773 := bbase (se 8 (by rfl) ⟨18672, by rfl⟩ : syracuseStep 3186773 = 37345) (by norm_num)
theorem B3186845 : Blo 1415527 3186845 := bbase (se 3 (by rfl) ⟨597533, by rfl⟩ : syracuseStep 3186845 = 1195067) (by norm_num)
theorem B3735773 : Blo 1415527 3735773 := bbase (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) (by norm_num)
theorem B3186917 : Blo 1415527 3186917 := bbase (se 4 (by rfl) ⟨298773, by rfl⟩ : syracuseStep 3186917 = 597547) (by norm_num)
theorem B12927221 : Blo 1415527 12927221 := bbase (se 5 (by rfl) ⟨605963, by rfl⟩ : syracuseStep 12927221 = 1211927) (by norm_num)
theorem B2269453 : Blo 1415527 2269453 := bbase (se 3 (by rfl) ⟨425522, by rfl⟩ : syracuseStep 2269453 = 851045) (by norm_num)
theorem B3186989 : Blo 1415527 3186989 := bbase (se 3 (by rfl) ⟨597560, by rfl⟩ : syracuseStep 3186989 = 1195121) (by norm_num)
theorem B3187061 : Blo 1415527 3187061 := bbase (se 5 (by rfl) ⟨149393, by rfl⟩ : syracuseStep 3187061 = 298787) (by norm_num)
theorem B2687413 : Blo 1415527 2687413 := bbase (se 5 (by rfl) ⟨125972, by rfl⟩ : syracuseStep 2687413 = 251945) (by norm_num)
theorem B3187133 : Blo 1415527 3187133 := bbase (se 3 (by rfl) ⟨597587, by rfl⟩ : syracuseStep 3187133 = 1195175) (by norm_num)
theorem B3187205 : Blo 1415527 3187205 := bbase (se 4 (by rfl) ⟨298800, by rfl⟩ : syracuseStep 3187205 = 597601) (by norm_num)
theorem B3187277 : Blo 1415527 3187277 := bbase (se 3 (by rfl) ⟨597614, by rfl⟩ : syracuseStep 3187277 = 1195229) (by norm_num)
theorem B2687573 : Blo 1415527 2687573 := bbase (se 8 (by rfl) ⟨15747, by rfl⟩ : syracuseStep 2687573 = 31495) (by norm_num)
theorem B3023477 : Blo 1415527 3023477 := bbase (se 5 (by rfl) ⟨141725, by rfl⟩ : syracuseStep 3023477 = 283451) (by norm_num)
theorem B5374613 : Blo 1415527 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B7168661 : Blo 1415527 7168661 := bbase (se 6 (by rfl) ⟨168015, by rfl⟩ : syracuseStep 7168661 = 336031) (by norm_num)
theorem B3187349 : Blo 1415527 3187349 := bbase (se 6 (by rfl) ⟨74703, by rfl⟩ : syracuseStep 3187349 = 149407) (by norm_num)
theorem B2269901 : Blo 1415527 2269901 := bbase (se 3 (by rfl) ⟨425606, by rfl⟩ : syracuseStep 2269901 = 851213) (by norm_num)
theorem B3187421 : Blo 1415527 3187421 := bbase (se 3 (by rfl) ⟨597641, by rfl⟩ : syracuseStep 3187421 = 1195283) (by norm_num)
theorem B2687717 : Blo 1415527 2687717 := bbase (se 4 (by rfl) ⟨251973, by rfl⟩ : syracuseStep 2687717 = 503947) (by norm_num)
theorem B3187493 : Blo 1415527 3187493 := bbase (se 4 (by rfl) ⟨298827, by rfl⟩ : syracuseStep 3187493 = 597655) (by norm_num)
theorem B13640501 : Blo 1415527 13640501 := bbase (se 5 (by rfl) ⟨639398, by rfl⟩ : syracuseStep 13640501 = 1278797) (by norm_num)
theorem B1532737 : Blo 1415527 1532737 := bbase (se 2 (by rfl) ⟨574776, by rfl⟩ : syracuseStep 1532737 = 1149553) (by norm_num)
theorem B1614661 : Blo 1415527 1614661 := bbase (se 4 (by rfl) ⟨151374, by rfl⟩ : syracuseStep 1614661 = 302749) (by norm_num)
theorem B5104453 : Blo 1415527 5104453 := bbase (se 4 (by rfl) ⟨478542, by rfl⟩ : syracuseStep 5104453 = 957085) (by norm_num)
theorem B2491229 : Blo 1415527 2491229 := bbase (se 3 (by rfl) ⟨467105, by rfl⟩ : syracuseStep 2491229 = 934211) (by norm_num)
theorem B3023725 : Blo 1415527 3023725 := bbase (se 3 (by rfl) ⟨566948, by rfl⟩ : syracuseStep 3023725 = 1133897) (by norm_num)
theorem B3187565 : Blo 1415527 3187565 := bbase (se 3 (by rfl) ⟨597668, by rfl⟩ : syracuseStep 3187565 = 1195337) (by norm_num)
theorem B20423573 : Blo 1415527 20423573 := bbase (se 6 (by rfl) ⟨478677, by rfl⟩ : syracuseStep 20423573 = 957355) (by norm_num)
theorem B2270101 : Blo 1415527 2270101 := bbase (se 6 (by rfl) ⟨53205, by rfl⟩ : syracuseStep 2270101 = 106411) (by norm_num)
theorem B6046645 : Blo 1415527 6046645 := bbase (se 5 (by rfl) ⟨283436, by rfl⟩ : syracuseStep 6046645 = 566873) (by norm_num)
theorem B2016181 : Blo 1415527 2016181 := bbase (se 5 (by rfl) ⟨94508, by rfl⟩ : syracuseStep 2016181 = 189017) (by norm_num)
theorem B3187637 : Blo 1415527 3187637 := bbase (se 5 (by rfl) ⟨149420, by rfl⟩ : syracuseStep 3187637 = 298841) (by norm_num)
theorem B1516501 : Blo 1415527 1516501 := bbase (se 7 (by rfl) ⟨17771, by rfl⟩ : syracuseStep 1516501 = 35543) (by norm_num)
theorem B4031461 : Blo 1415527 4031461 := bbase (se 4 (by rfl) ⟨377949, by rfl⟩ : syracuseStep 4031461 = 755899) (by norm_num)
theorem B5104613 : Blo 1415527 5104613 := bbase (se 4 (by rfl) ⟨478557, by rfl⟩ : syracuseStep 5104613 = 957115) (by norm_num)
theorem B3187709 : Blo 1415527 3187709 := bbase (se 3 (by rfl) ⟨597695, by rfl⟩ : syracuseStep 3187709 = 1195391) (by norm_num)
theorem B2688005 : Blo 1415527 2688005 := bbase (se 4 (by rfl) ⟨252000, by rfl⟩ : syracuseStep 2688005 = 504001) (by norm_num)
theorem B3187781 : Blo 1415527 3187781 := bbase (se 4 (by rfl) ⟨298854, by rfl⟩ : syracuseStep 3187781 = 597709) (by norm_num)
theorem B41976917 : Blo 1415527 41976917 := bbase (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) (by norm_num)
theorem B5104741 : Blo 1415527 5104741 := bbase (se 4 (by rfl) ⟨478569, by rfl⟩ : syracuseStep 5104741 = 957139) (by norm_num)
theorem B3187853 : Blo 1415527 3187853 := bbase (se 3 (by rfl) ⟨597722, by rfl⟩ : syracuseStep 3187853 = 1195445) (by norm_num)
theorem B3450005 : Blo 1415527 3450005 := bbase (se 6 (by rfl) ⟨80859, by rfl⟩ : syracuseStep 3450005 = 161719) (by norm_num)
theorem B2270357 : Blo 1415527 2270357 := bbase (se 6 (by rfl) ⟨53211, by rfl⟩ : syracuseStep 2270357 = 106423) (by norm_num)
theorem B2688157 : Blo 1415527 2688157 := bbase (se 3 (by rfl) ⟨504029, by rfl⟩ : syracuseStep 2688157 = 1008059) (by norm_num)
theorem B3187925 : Blo 1415527 3187925 := bbase (se 7 (by rfl) ⟨37358, by rfl⟩ : syracuseStep 3187925 = 74717) (by norm_num)
theorem B2016517 : Blo 1415527 2016517 := bbase (se 4 (by rfl) ⟨189048, by rfl⟩ : syracuseStep 2016517 = 378097) (by norm_num)
theorem B3187997 : Blo 1415527 3187997 := bbase (se 3 (by rfl) ⟨597749, by rfl⟩ : syracuseStep 3187997 = 1195499) (by norm_num)
theorem B3024229 : Blo 1415527 3024229 := bbase (se 4 (by rfl) ⟨283521, by rfl⟩ : syracuseStep 3024229 = 567043) (by norm_num)
theorem B3188069 : Blo 1415527 3188069 := bbase (se 4 (by rfl) ⟨298881, by rfl⟩ : syracuseStep 3188069 = 597763) (by norm_num)
theorem B3188141 : Blo 1415527 3188141 := bbase (se 3 (by rfl) ⟨597776, by rfl⟩ : syracuseStep 3188141 = 1195553) (by norm_num)
theorem B2688461 : Blo 1415527 2688461 := bbase (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) (by norm_num)
theorem B2016733 : Blo 1415527 2016733 := bbase (se 3 (by rfl) ⟨378137, by rfl⟩ : syracuseStep 2016733 = 756275) (by norm_num)
theorem B3188213 : Blo 1415527 3188213 := bbase (se 5 (by rfl) ⟨149447, by rfl⟩ : syracuseStep 3188213 = 298895) (by norm_num)
theorem B2123309 : Blo 1415527 2123309 := bbase (se 3 (by rfl) ⟨398120, by rfl⟩ : syracuseStep 2123309 = 796241) (by norm_num)
theorem B8611381 : Blo 1415527 8611381 := bbase (se 5 (by rfl) ⟨403658, by rfl⟩ : syracuseStep 8611381 = 807317) (by norm_num)
theorem B3188285 : Blo 1415527 3188285 := bbase (se 3 (by rfl) ⟨597803, by rfl⟩ : syracuseStep 3188285 = 1195607) (by norm_num)
theorem B2123333 : Blo 1415527 2123333 := bbase (se 4 (by rfl) ⟨199062, by rfl⟩ : syracuseStep 2123333 = 398125) (by norm_num)
theorem B4777541 : Blo 1415527 4777541 := bbase (se 4 (by rfl) ⟨447894, by rfl⟩ : syracuseStep 4777541 = 895789) (by norm_num)
theorem B8619605 : Blo 1415527 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B1476185 : Blo 1415527 1476185 := bbase (se 2 (by rfl) ⟨553569, by rfl⟩ : syracuseStep 1476185 = 1107139) (by norm_num)
theorem B2123357 : Blo 1415527 2123357 := bbase (se 3 (by rfl) ⟨398129, by rfl⟩ : syracuseStep 2123357 = 796259) (by norm_num)
theorem B2123381 : Blo 1415527 2123381 := bbase (se 5 (by rfl) ⟨99533, by rfl⟩ : syracuseStep 2123381 = 199067) (by norm_num)
theorem B3188357 : Blo 1415527 3188357 := bbase (se 4 (by rfl) ⟨298908, by rfl⟩ : syracuseStep 3188357 = 597817) (by norm_num)
theorem B2123405 : Blo 1415527 2123405 := bbase (se 3 (by rfl) ⟨398138, by rfl⟩ : syracuseStep 2123405 = 796277) (by norm_num)
theorem B2123429 : Blo 1415527 2123429 := bbase (se 4 (by rfl) ⟨199071, by rfl⟩ : syracuseStep 2123429 = 398143) (by norm_num)
theorem B2123453 : Blo 1415527 2123453 := bbase (se 3 (by rfl) ⟨398147, by rfl⟩ : syracuseStep 2123453 = 796295) (by norm_num)
theorem B3188429 : Blo 1415527 3188429 := bbase (se 3 (by rfl) ⟨597830, by rfl⟩ : syracuseStep 3188429 = 1195661) (by norm_num)
theorem B2123477 : Blo 1415527 2123477 := bbase (se 7 (by rfl) ⟨24884, by rfl⟩ : syracuseStep 2123477 = 49769) (by norm_num)
theorem B2123501 : Blo 1415527 2123501 := bbase (se 3 (by rfl) ⟨398156, by rfl⟩ : syracuseStep 2123501 = 796313) (by norm_num)
theorem B2123525 : Blo 1415527 2123525 := bbase (se 4 (by rfl) ⟨199080, by rfl⟩ : syracuseStep 2123525 = 398161) (by norm_num)
theorem B3188501 : Blo 1415527 3188501 := bbase (se 6 (by rfl) ⟨74730, by rfl⟩ : syracuseStep 3188501 = 149461) (by norm_num)
theorem B2123549 : Blo 1415527 2123549 := bbase (se 3 (by rfl) ⟨398165, by rfl⟩ : syracuseStep 2123549 = 796331) (by norm_num)
theorem B2123573 : Blo 1415527 2123573 := bbase (se 5 (by rfl) ⟨99542, by rfl⟩ : syracuseStep 2123573 = 199085) (by norm_num)
theorem B2123597 : Blo 1415527 2123597 := bbase (se 3 (by rfl) ⟨398174, by rfl⟩ : syracuseStep 2123597 = 796349) (by norm_num)
theorem B2017109 : Blo 1415527 2017109 := bbase (se 9 (by rfl) ⟨5909, by rfl⟩ : syracuseStep 2017109 = 11819) (by norm_num)
theorem B3188573 : Blo 1415527 3188573 := bbase (se 3 (by rfl) ⟨597857, by rfl⟩ : syracuseStep 3188573 = 1195715) (by norm_num)
theorem B2123621 : Blo 1415527 2123621 := bbase (se 4 (by rfl) ⟨199089, by rfl⟩ : syracuseStep 2123621 = 398179) (by norm_num)
theorem B2123645 : Blo 1415527 2123645 := bbase (se 3 (by rfl) ⟨398183, by rfl⟩ : syracuseStep 2123645 = 796367) (by norm_num)
theorem B2123669 : Blo 1415527 2123669 := bbase (se 6 (by rfl) ⟨49773, by rfl⟩ : syracuseStep 2123669 = 99547) (by norm_num)
theorem B7169957 : Blo 1415527 7169957 := bbase (se 4 (by rfl) ⟨672183, by rfl⟩ : syracuseStep 7169957 = 1344367) (by norm_num)
theorem B3188645 : Blo 1415527 3188645 := bbase (se 4 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 3188645 = 597871) (by norm_num)
theorem B2123693 : Blo 1415527 2123693 := bbase (se 3 (by rfl) ⟨398192, by rfl⟩ : syracuseStep 2123693 = 796385) (by norm_num)
theorem B8062901 : Blo 1415527 8062901 := bbase (se 5 (by rfl) ⟨377948, by rfl⟩ : syracuseStep 8062901 = 755897) (by norm_num)
theorem B2123717 : Blo 1415527 2123717 := bbase (se 4 (by rfl) ⟨199098, by rfl⟩ : syracuseStep 2123717 = 398197) (by norm_num)
theorem B2123741 : Blo 1415527 2123741 := bbase (se 3 (by rfl) ⟨398201, by rfl⟩ : syracuseStep 2123741 = 796403) (by norm_num)
theorem B3188717 : Blo 1415527 3188717 := bbase (se 3 (by rfl) ⟨597884, by rfl⟩ : syracuseStep 3188717 = 1195769) (by norm_num)
theorem B4777973 : Blo 1415527 4777973 := bbase (se 5 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 4777973 = 447935) (by norm_num)
theorem B2123765 : Blo 1415527 2123765 := bbase (se 5 (by rfl) ⟨99551, by rfl⟩ : syracuseStep 2123765 = 199103) (by norm_num)
theorem B1615861 : Blo 1415527 1615861 := bbase (se 5 (by rfl) ⟨75743, by rfl⟩ : syracuseStep 1615861 = 151487) (by norm_num)
theorem B2123789 : Blo 1415527 2123789 := bbase (se 3 (by rfl) ⟨398210, by rfl⟩ : syracuseStep 2123789 = 796421) (by norm_num)
theorem B2123813 : Blo 1415527 2123813 := bbase (se 4 (by rfl) ⟨199107, by rfl⟩ : syracuseStep 2123813 = 398215) (by norm_num)
theorem B3188789 : Blo 1415527 3188789 := bbase (se 5 (by rfl) ⟨149474, by rfl⟩ : syracuseStep 3188789 = 298949) (by norm_num)
theorem B2123837 : Blo 1415527 2123837 := bbase (se 3 (by rfl) ⟨398219, by rfl⟩ : syracuseStep 2123837 = 796439) (by norm_num)
theorem B2123861 : Blo 1415527 2123861 := bbase (se 8 (by rfl) ⟨12444, by rfl⟩ : syracuseStep 2123861 = 24889) (by norm_num)
theorem B2123885 : Blo 1415527 2123885 := bbase (se 3 (by rfl) ⟨398228, by rfl⟩ : syracuseStep 2123885 = 796457) (by norm_num)
theorem B1435757 : Blo 1415527 1435757 := bbase (se 3 (by rfl) ⟨269204, by rfl⟩ : syracuseStep 1435757 = 538409) (by norm_num)
theorem B3188861 : Blo 1415527 3188861 := bbase (se 3 (by rfl) ⟨597911, by rfl⟩ : syracuseStep 3188861 = 1195823) (by norm_num)
theorem B2123909 : Blo 1415527 2123909 := bbase (se 4 (by rfl) ⟨199116, by rfl⟩ : syracuseStep 2123909 = 398233) (by norm_num)
theorem B2123933 : Blo 1415527 2123933 := bbase (se 3 (by rfl) ⟨398237, by rfl⟩ : syracuseStep 2123933 = 796475) (by norm_num)
theorem B2123957 : Blo 1415527 2123957 := bbase (se 5 (by rfl) ⟨99560, by rfl⟩ : syracuseStep 2123957 = 199121) (by norm_num)
theorem B2689213 : Blo 1415527 2689213 := bbase (se 3 (by rfl) ⟨504227, by rfl⟩ : syracuseStep 2689213 = 1008455) (by norm_num)
theorem B3188933 : Blo 1415527 3188933 := bbase (se 4 (by rfl) ⟨298962, by rfl⟩ : syracuseStep 3188933 = 597925) (by norm_num)
theorem B2123981 : Blo 1415527 2123981 := bbase (se 3 (by rfl) ⟨398246, by rfl⟩ : syracuseStep 2123981 = 796493) (by norm_num)
theorem B18163925 : Blo 1415527 18163925 := bbase (se 7 (by rfl) ⟨212858, by rfl⟩ : syracuseStep 18163925 = 425717) (by norm_num)
theorem B3025117 : Blo 1415527 3025117 := bbase (se 3 (by rfl) ⟨567209, by rfl⟩ : syracuseStep 3025117 = 1134419) (by norm_num)
theorem B2124005 : Blo 1415527 2124005 := bbase (se 4 (by rfl) ⟨199125, by rfl⟩ : syracuseStep 2124005 = 398251) (by norm_num)
theorem B2124029 : Blo 1415527 2124029 := bbase (se 3 (by rfl) ⟨398255, by rfl⟩ : syracuseStep 2124029 = 796511) (by norm_num)
theorem B3189005 : Blo 1415527 3189005 := bbase (se 3 (by rfl) ⟨597938, by rfl⟩ : syracuseStep 3189005 = 1195877) (by norm_num)
theorem B2124053 : Blo 1415527 2124053 := bbase (se 6 (by rfl) ⟨49782, by rfl⟩ : syracuseStep 2124053 = 99565) (by norm_num)
theorem B2124077 : Blo 1415527 2124077 := bbase (se 3 (by rfl) ⟨398264, by rfl⟩ : syracuseStep 2124077 = 796529) (by norm_num)
theorem B2124101 : Blo 1415527 2124101 := bbase (se 4 (by rfl) ⟨199134, by rfl⟩ : syracuseStep 2124101 = 398269) (by norm_num)
theorem B2689357 : Blo 1415527 2689357 := bbase (se 3 (by rfl) ⟨504254, by rfl⟩ : syracuseStep 2689357 = 1008509) (by norm_num)
theorem B3189077 : Blo 1415527 3189077 := bbase (se 10 (by rfl) ⟨4671, by rfl⟩ : syracuseStep 3189077 = 9343) (by norm_num)
theorem B2124125 : Blo 1415527 2124125 := bbase (se 3 (by rfl) ⟨398273, by rfl⟩ : syracuseStep 2124125 = 796547) (by norm_num)
theorem B1436017 : Blo 1415527 1436017 := bbase (se 2 (by rfl) ⟨538506, by rfl⟩ : syracuseStep 1436017 = 1077013) (by norm_num)
theorem B2124149 : Blo 1415527 2124149 := bbase (se 5 (by rfl) ⟨99569, by rfl⟩ : syracuseStep 2124149 = 199139) (by norm_num)
theorem B2124173 : Blo 1415527 2124173 := bbase (se 3 (by rfl) ⟨398282, by rfl⟩ : syracuseStep 2124173 = 796565) (by norm_num)
theorem B3189149 : Blo 1415527 3189149 := bbase (se 3 (by rfl) ⟨597965, by rfl⟩ : syracuseStep 3189149 = 1195931) (by norm_num)
theorem B4778405 : Blo 1415527 4778405 := bbase (se 4 (by rfl) ⟨447975, by rfl⟩ : syracuseStep 4778405 = 895951) (by norm_num)
theorem B2124197 : Blo 1415527 2124197 := bbase (se 4 (by rfl) ⟨199143, by rfl⟩ : syracuseStep 2124197 = 398287) (by norm_num)
theorem B10758581 : Blo 1415527 10758581 := bbase (se 5 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 10758581 = 1008617) (by norm_num)
theorem B2124221 : Blo 1415527 2124221 := bbase (se 3 (by rfl) ⟨398291, by rfl⟩ : syracuseStep 2124221 = 796583) (by norm_num)
theorem B4032965 : Blo 1415527 4032965 := bbase (se 4 (by rfl) ⟨378090, by rfl⟩ : syracuseStep 4032965 = 756181) (by norm_num)
theorem B2124245 : Blo 1415527 2124245 := bbase (se 7 (by rfl) ⟨24893, by rfl⟩ : syracuseStep 2124245 = 49787) (by norm_num)
theorem B3189221 : Blo 1415527 3189221 := bbase (se 4 (by rfl) ⟨298989, by rfl⟩ : syracuseStep 3189221 = 597979) (by norm_num)
theorem B2124269 : Blo 1415527 2124269 := bbase (se 3 (by rfl) ⟨398300, by rfl⟩ : syracuseStep 2124269 = 796601) (by norm_num)
theorem B2689517 : Blo 1415527 2689517 := bbase (se 3 (by rfl) ⟨504284, by rfl⟩ : syracuseStep 2689517 = 1008569) (by norm_num)
theorem B2124293 : Blo 1415527 2124293 := bbase (se 4 (by rfl) ⟨199152, by rfl⟩ : syracuseStep 2124293 = 398305) (by norm_num)
theorem B2869789 : Blo 1415527 2869789 := bbase (se 3 (by rfl) ⟨538085, by rfl⟩ : syracuseStep 2869789 = 1076171) (by norm_num)
theorem B2124317 : Blo 1415527 2124317 := bbase (se 3 (by rfl) ⟨398309, by rfl⟩ : syracuseStep 2124317 = 796619) (by norm_num)
theorem B3189293 : Blo 1415527 3189293 := bbase (se 3 (by rfl) ⟨597992, by rfl⟩ : syracuseStep 3189293 = 1195985) (by norm_num)
theorem B2124341 : Blo 1415527 2124341 := bbase (se 5 (by rfl) ⟨99578, by rfl⟩ : syracuseStep 2124341 = 199157) (by norm_num)
theorem B2124365 : Blo 1415527 2124365 := bbase (se 3 (by rfl) ⟨398318, by rfl⟩ : syracuseStep 2124365 = 796637) (by norm_num)
theorem B2124389 : Blo 1415527 2124389 := bbase (se 4 (by rfl) ⟨199161, by rfl⟩ : syracuseStep 2124389 = 398323) (by norm_num)
theorem B3189365 : Blo 1415527 3189365 := bbase (se 5 (by rfl) ⟨149501, by rfl⟩ : syracuseStep 3189365 = 299003) (by norm_num)
theorem B2124413 : Blo 1415527 2124413 := bbase (se 3 (by rfl) ⟨398327, by rfl⟩ : syracuseStep 2124413 = 796655) (by norm_num)
theorem B2689661 : Blo 1415527 2689661 := bbase (se 3 (by rfl) ⟨504311, by rfl⟩ : syracuseStep 2689661 = 1008623) (by norm_num)
theorem B2124437 : Blo 1415527 2124437 := bbase (se 6 (by rfl) ⟨49791, by rfl⟩ : syracuseStep 2124437 = 99583) (by norm_num)
theorem B2869925 : Blo 1415527 2869925 := bbase (se 4 (by rfl) ⟨269055, by rfl⟩ : syracuseStep 2869925 = 538111) (by norm_num)
theorem B2124461 : Blo 1415527 2124461 := bbase (se 3 (by rfl) ⟨398336, by rfl⟩ : syracuseStep 2124461 = 796673) (by norm_num)
theorem B3189437 : Blo 1415527 3189437 := bbase (se 3 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 3189437 = 1196039) (by norm_num)
theorem B2124485 : Blo 1415527 2124485 := bbase (se 4 (by rfl) ⟨199170, by rfl⟩ : syracuseStep 2124485 = 398341) (by norm_num)
theorem B3025613 : Blo 1415527 3025613 := bbase (se 3 (by rfl) ⟨567302, by rfl⟩ : syracuseStep 3025613 = 1134605) (by norm_num)
theorem B5376725 : Blo 1415527 5376725 := bbase (se 7 (by rfl) ⟨63008, by rfl⟩ : syracuseStep 5376725 = 126017) (by norm_num)
theorem B2124509 : Blo 1415527 2124509 := bbase (se 3 (by rfl) ⟨398345, by rfl⟩ : syracuseStep 2124509 = 796691) (by norm_num)
theorem B3828469 : Blo 1415527 3828469 := bbase (se 5 (by rfl) ⟨179459, by rfl⟩ : syracuseStep 3828469 = 358919) (by norm_num)
theorem B2124533 : Blo 1415527 2124533 := bbase (se 5 (by rfl) ⟨99587, by rfl⟩ : syracuseStep 2124533 = 199175) (by norm_num)
theorem B2124557 : Blo 1415527 2124557 := bbase (se 3 (by rfl) ⟨398354, by rfl⟩ : syracuseStep 2124557 = 796709) (by norm_num)
theorem B2124581 : Blo 1415527 2124581 := bbase (se 4 (by rfl) ⟨199179, by rfl⟩ : syracuseStep 2124581 = 398359) (by norm_num)
theorem B2124605 : Blo 1415527 2124605 := bbase (se 3 (by rfl) ⟨398363, by rfl⟩ : syracuseStep 2124605 = 796727) (by norm_num)
theorem B10750805 : Blo 1415527 10750805 := bbase (se 9 (by rfl) ⟨31496, by rfl⟩ : syracuseStep 10750805 = 62993) (by norm_num)
theorem B4778837 : Blo 1415527 4778837 := bbase (se 9 (by rfl) ⟨14000, by rfl⟩ : syracuseStep 4778837 = 28001) (by norm_num)
theorem B43608917 : Blo 1415527 43608917 := bbase (se 9 (by rfl) ⟨127760, by rfl⟩ : syracuseStep 43608917 = 255521) (by norm_num)
theorem B2124629 : Blo 1415527 2124629 := bbase (se 9 (by rfl) ⟨6224, by rfl⟩ : syracuseStep 2124629 = 12449) (by norm_num)
theorem B2124653 : Blo 1415527 2124653 := bbase (se 3 (by rfl) ⟨398372, by rfl⟩ : syracuseStep 2124653 = 796745) (by norm_num)
theorem B2124677 : Blo 1415527 2124677 := bbase (se 4 (by rfl) ⟨199188, by rfl⟩ : syracuseStep 2124677 = 398377) (by norm_num)
theorem B14740373 : Blo 1415527 14740373 := bbase (se 6 (by rfl) ⟨345477, by rfl⟩ : syracuseStep 14740373 = 690955) (by norm_num)
theorem B2124701 : Blo 1415527 2124701 := bbase (se 3 (by rfl) ⟨398381, by rfl⟩ : syracuseStep 2124701 = 796763) (by norm_num)
theorem B2689949 : Blo 1415527 2689949 := bbase (se 3 (by rfl) ⟨504365, by rfl⟩ : syracuseStep 2689949 = 1008731) (by norm_num)
theorem B3402661 : Blo 1415527 3402661 := bbase (se 4 (by rfl) ⟨318999, by rfl⟩ : syracuseStep 3402661 = 637999) (by norm_num)
theorem B2124725 : Blo 1415527 2124725 := bbase (se 5 (by rfl) ⟨99596, by rfl⟩ : syracuseStep 2124725 = 199193) (by norm_num)
theorem B2124749 : Blo 1415527 2124749 := bbase (se 3 (by rfl) ⟨398390, by rfl⟩ : syracuseStep 2124749 = 796781) (by norm_num)
theorem B2124773 : Blo 1415527 2124773 := bbase (se 4 (by rfl) ⟨199197, by rfl⟩ : syracuseStep 2124773 = 398395) (by norm_num)
theorem B5377013 : Blo 1415527 5377013 := bbase (se 5 (by rfl) ⟨252047, by rfl⟩ : syracuseStep 5377013 = 504095) (by norm_num)
theorem B2124797 : Blo 1415527 2124797 := bbase (se 3 (by rfl) ⟨398399, by rfl⟩ : syracuseStep 2124797 = 796799) (by norm_num)
theorem B2124821 : Blo 1415527 2124821 := bbase (se 6 (by rfl) ⟨49800, by rfl⟩ : syracuseStep 2124821 = 99601) (by norm_num)
theorem B2124845 : Blo 1415527 2124845 := bbase (se 3 (by rfl) ⟨398408, by rfl⟩ : syracuseStep 2124845 = 796817) (by norm_num)
theorem B2690101 : Blo 1415527 2690101 := bbase (se 5 (by rfl) ⟨126098, by rfl⟩ : syracuseStep 2690101 = 252197) (by norm_num)
theorem B2124869 : Blo 1415527 2124869 := bbase (se 4 (by rfl) ⟨199206, by rfl⟩ : syracuseStep 2124869 = 398413) (by norm_num)
theorem B2124893 : Blo 1415527 2124893 := bbase (se 3 (by rfl) ⟨398417, by rfl⟩ : syracuseStep 2124893 = 796835) (by norm_num)
theorem B2124917 : Blo 1415527 2124917 := bbase (se 5 (by rfl) ⟨99605, by rfl⟩ : syracuseStep 2124917 = 199211) (by norm_num)
theorem B2124941 : Blo 1415527 2124941 := bbase (se 3 (by rfl) ⟨398426, by rfl⟩ : syracuseStep 2124941 = 796853) (by norm_num)
theorem B1592473 : Blo 1415527 1592473 := bbase (se 2 (by rfl) ⟨597177, by rfl⟩ : syracuseStep 1592473 = 1194355) (by norm_num)
theorem B5172389 : Blo 1415527 5172389 := bbase (se 4 (by rfl) ⟨484911, by rfl⟩ : syracuseStep 5172389 = 969823) (by norm_num)
theorem B2124965 : Blo 1415527 2124965 := bbase (se 4 (by rfl) ⟨199215, by rfl⟩ : syracuseStep 2124965 = 398431) (by norm_num)
theorem B7171253 : Blo 1415527 7171253 := bbase (se 5 (by rfl) ⟨336152, by rfl⟩ : syracuseStep 7171253 = 672305) (by norm_num)
theorem B1592509 : Blo 1415527 1592509 := bbase (se 3 (by rfl) ⟨298595, by rfl⟩ : syracuseStep 1592509 = 597191) (by norm_num)
theorem B2124989 : Blo 1415527 2124989 := bbase (se 3 (by rfl) ⟨398435, by rfl⟩ : syracuseStep 2124989 = 796871) (by norm_num)
theorem B2125013 : Blo 1415527 2125013 := bbase (se 7 (by rfl) ⟨24902, by rfl⟩ : syracuseStep 2125013 = 49805) (by norm_num)
theorem B24218837 : Blo 1415527 24218837 := bbase (se 7 (by rfl) ⟨283814, by rfl⟩ : syracuseStep 24218837 = 567629) (by norm_num)
theorem B1592545 : Blo 1415527 1592545 := bbase (se 2 (by rfl) ⟨597204, by rfl⟩ : syracuseStep 1592545 = 1194409) (by norm_num)
theorem B2125037 : Blo 1415527 2125037 := bbase (se 3 (by rfl) ⟨398444, by rfl⟩ : syracuseStep 2125037 = 796889) (by norm_num)
theorem B3583237 : Blo 1415527 3583237 := bbase (se 4 (by rfl) ⟨335928, by rfl⟩ : syracuseStep 3583237 = 671857) (by norm_num)
theorem B1592581 : Blo 1415527 1592581 := bbase (se 4 (by rfl) ⟨149304, by rfl⟩ : syracuseStep 1592581 = 298609) (by norm_num)
theorem B4779269 : Blo 1415527 4779269 := bbase (se 4 (by rfl) ⟨448056, by rfl⟩ : syracuseStep 4779269 = 896113) (by norm_num)
theorem B2125061 : Blo 1415527 2125061 := bbase (se 4 (by rfl) ⟨199224, by rfl⟩ : syracuseStep 2125061 = 398449) (by norm_num)
theorem B2125085 : Blo 1415527 2125085 := bbase (se 3 (by rfl) ⟨398453, by rfl⟩ : syracuseStep 2125085 = 796907) (by norm_num)
theorem B1592617 : Blo 1415527 1592617 := bbase (se 2 (by rfl) ⟨597231, by rfl⟩ : syracuseStep 1592617 = 1194463) (by norm_num)
theorem B2125109 : Blo 1415527 2125109 := bbase (se 5 (by rfl) ⟨99614, by rfl⟩ : syracuseStep 2125109 = 199229) (by norm_num)
theorem B1592653 : Blo 1415527 1592653 := bbase (se 3 (by rfl) ⟨298622, by rfl⟩ : syracuseStep 1592653 = 597245) (by norm_num)
theorem B2125133 : Blo 1415527 2125133 := bbase (se 3 (by rfl) ⟨398462, by rfl⟩ : syracuseStep 2125133 = 796925) (by norm_num)
theorem B2125157 : Blo 1415527 2125157 := bbase (se 4 (by rfl) ⟨199233, by rfl⟩ : syracuseStep 2125157 = 398467) (by norm_num)
theorem B2690405 : Blo 1415527 2690405 := bbase (se 4 (by rfl) ⟨252225, by rfl⟩ : syracuseStep 2690405 = 504451) (by norm_num)
theorem B1592689 : Blo 1415527 1592689 := bbase (se 2 (by rfl) ⟨597258, by rfl⟩ : syracuseStep 1592689 = 1194517) (by norm_num)
theorem B3583349 : Blo 1415527 3583349 := bbase (se 5 (by rfl) ⟨167969, by rfl⟩ : syracuseStep 3583349 = 335939) (by norm_num)
theorem B2125181 : Blo 1415527 2125181 := bbase (se 3 (by rfl) ⟨398471, by rfl⟩ : syracuseStep 2125181 = 796943) (by norm_num)
theorem B6991237 : Blo 1415527 6991237 := bbase (se 4 (by rfl) ⟨655428, by rfl⟩ : syracuseStep 6991237 = 1310857) (by norm_num)
theorem B2551189 : Blo 1415527 2551189 := bbase (se 6 (by rfl) ⟨59793, by rfl⟩ : syracuseStep 2551189 = 119587) (by norm_num)
theorem B1592725 : Blo 1415527 1592725 := bbase (se 6 (by rfl) ⟨37329, by rfl⟩ : syracuseStep 1592725 = 74659) (by norm_num)
theorem B2125205 : Blo 1415527 2125205 := bbase (se 6 (by rfl) ⟨49809, by rfl⟩ : syracuseStep 2125205 = 99619) (by norm_num)
theorem B2125229 : Blo 1415527 2125229 := bbase (se 3 (by rfl) ⟨398480, by rfl⟩ : syracuseStep 2125229 = 796961) (by norm_num)
theorem B1592761 : Blo 1415527 1592761 := bbase (se 2 (by rfl) ⟨597285, by rfl⟩ : syracuseStep 1592761 = 1194571) (by norm_num)
theorem B2125253 : Blo 1415527 2125253 := bbase (se 4 (by rfl) ⟨199242, by rfl⟩ : syracuseStep 2125253 = 398485) (by norm_num)
theorem B1592797 : Blo 1415527 1592797 := bbase (se 3 (by rfl) ⟨298649, by rfl⟩ : syracuseStep 1592797 = 597299) (by norm_num)
theorem B2125277 : Blo 1415527 2125277 := bbase (se 3 (by rfl) ⟨398489, by rfl⟩ : syracuseStep 2125277 = 796979) (by norm_num)
theorem B2125301 : Blo 1415527 2125301 := bbase (se 5 (by rfl) ⟨99623, by rfl⟩ : syracuseStep 2125301 = 199247) (by norm_num)
theorem B1592833 : Blo 1415527 1592833 := bbase (se 2 (by rfl) ⟨597312, by rfl⟩ : syracuseStep 1592833 = 1194625) (by norm_num)
theorem B2125325 : Blo 1415527 2125325 := bbase (se 3 (by rfl) ⟨398498, by rfl⟩ : syracuseStep 2125325 = 796997) (by norm_num)
theorem B1592869 : Blo 1415527 1592869 := bbase (se 4 (by rfl) ⟨149331, by rfl⟩ : syracuseStep 1592869 = 298663) (by norm_num)
theorem B2125349 : Blo 1415527 2125349 := bbase (se 4 (by rfl) ⟨199251, by rfl⟩ : syracuseStep 2125349 = 398503) (by norm_num)
theorem B3583541 : Blo 1415527 3583541 := bbase (se 5 (by rfl) ⟨167978, by rfl⟩ : syracuseStep 3583541 = 335957) (by norm_num)
theorem B2125373 : Blo 1415527 2125373 := bbase (se 3 (by rfl) ⟨398507, by rfl⟩ : syracuseStep 2125373 = 797015) (by norm_num)
theorem B3026501 : Blo 1415527 3026501 := bbase (se 4 (by rfl) ⟨283734, by rfl⟩ : syracuseStep 3026501 = 567469) (by norm_num)
theorem B1592905 : Blo 1415527 1592905 := bbase (se 2 (by rfl) ⟨597339, by rfl⟩ : syracuseStep 1592905 = 1194679) (by norm_num)
theorem B2125397 : Blo 1415527 2125397 := bbase (se 8 (by rfl) ⟨12453, by rfl⟩ : syracuseStep 2125397 = 24907) (by norm_num)
theorem B1592941 : Blo 1415527 1592941 := bbase (se 3 (by rfl) ⟨298676, by rfl⟩ : syracuseStep 1592941 = 597353) (by norm_num)
theorem B2125421 : Blo 1415527 2125421 := bbase (se 3 (by rfl) ⟨398516, by rfl⟩ : syracuseStep 2125421 = 797033) (by norm_num)
theorem B2125445 : Blo 1415527 2125445 := bbase (se 4 (by rfl) ⟨199260, by rfl⟩ : syracuseStep 2125445 = 398521) (by norm_num)
theorem B1592977 : Blo 1415527 1592977 := bbase (se 2 (by rfl) ⟨597366, by rfl⟩ : syracuseStep 1592977 = 1194733) (by norm_num)
theorem B2125469 : Blo 1415527 2125469 := bbase (se 3 (by rfl) ⟨398525, by rfl⟩ : syracuseStep 2125469 = 797051) (by norm_num)
theorem B1593013 : Blo 1415527 1593013 := bbase (se 5 (by rfl) ⟨74672, by rfl⟩ : syracuseStep 1593013 = 149345) (by norm_num)
theorem B4779701 : Blo 1415527 4779701 := bbase (se 5 (by rfl) ⟨224048, by rfl⟩ : syracuseStep 4779701 = 448097) (by norm_num)
theorem B2125493 : Blo 1415527 2125493 := bbase (se 5 (by rfl) ⟨99632, by rfl⟩ : syracuseStep 2125493 = 199265) (by norm_num)
theorem B3026621 : Blo 1415527 3026621 := bbase (se 3 (by rfl) ⟨567491, by rfl⟩ : syracuseStep 3026621 = 1134983) (by norm_num)
theorem B2125517 : Blo 1415527 2125517 := bbase (se 3 (by rfl) ⟨398534, by rfl⟩ : syracuseStep 2125517 = 797069) (by norm_num)
theorem B1593049 : Blo 1415527 1593049 := bbase (se 2 (by rfl) ⟨597393, by rfl⟩ : syracuseStep 1593049 = 1194787) (by norm_num)
theorem B2125541 : Blo 1415527 2125541 := bbase (se 4 (by rfl) ⟨199269, by rfl⟩ : syracuseStep 2125541 = 398539) (by norm_num)
theorem B1593085 : Blo 1415527 1593085 := bbase (se 3 (by rfl) ⟨298703, by rfl⟩ : syracuseStep 1593085 = 597407) (by norm_num)
theorem B2125565 : Blo 1415527 2125565 := bbase (se 3 (by rfl) ⟨398543, by rfl⟩ : syracuseStep 2125565 = 797087) (by norm_num)
theorem B6811397 : Blo 1415527 6811397 := bbase (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) (by norm_num)
theorem B2125589 : Blo 1415527 2125589 := bbase (se 6 (by rfl) ⟨49818, by rfl⟩ : syracuseStep 2125589 = 99637) (by norm_num)
theorem B1593121 : Blo 1415527 1593121 := bbase (se 2 (by rfl) ⟨597420, by rfl⟩ : syracuseStep 1593121 = 1194841) (by norm_num)
theorem B2125613 : Blo 1415527 2125613 := bbase (se 3 (by rfl) ⟨398552, by rfl⟩ : syracuseStep 2125613 = 797105) (by norm_num)
theorem B1593157 : Blo 1415527 1593157 := bbase (se 4 (by rfl) ⟨149358, by rfl⟩ : syracuseStep 1593157 = 298717) (by norm_num)
theorem B2125637 : Blo 1415527 2125637 := bbase (se 4 (by rfl) ⟨199278, by rfl⟩ : syracuseStep 2125637 = 398557) (by norm_num)
theorem B3108701 : Blo 1415527 3108701 := bbase (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) (by norm_num)
theorem B2125661 : Blo 1415527 2125661 := bbase (se 3 (by rfl) ⟨398561, by rfl⟩ : syracuseStep 2125661 = 797123) (by norm_num)
theorem B6049637 : Blo 1415527 6049637 := bbase (se 4 (by rfl) ⟨567153, by rfl⟩ : syracuseStep 6049637 = 1134307) (by norm_num)
theorem B1593193 : Blo 1415527 1593193 := bbase (se 2 (by rfl) ⟨597447, by rfl⟩ : syracuseStep 1593193 = 1194895) (by norm_num)
theorem B2125685 : Blo 1415527 2125685 := bbase (se 5 (by rfl) ⟨99641, by rfl⟩ : syracuseStep 2125685 = 199283) (by norm_num)
theorem B3583885 : Blo 1415527 3583885 := bbase (se 3 (by rfl) ⟨671978, by rfl⟩ : syracuseStep 3583885 = 1343957) (by norm_num)
theorem B1593229 : Blo 1415527 1593229 := bbase (se 3 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 1593229 = 597461) (by norm_num)
theorem B2125709 : Blo 1415527 2125709 := bbase (se 3 (by rfl) ⟨398570, by rfl⟩ : syracuseStep 2125709 = 797141) (by norm_num)
theorem B2125733 : Blo 1415527 2125733 := bbase (se 4 (by rfl) ⟨199287, by rfl⟩ : syracuseStep 2125733 = 398575) (by norm_num)
theorem B1593265 : Blo 1415527 1593265 := bbase (se 2 (by rfl) ⟨597474, by rfl⟩ : syracuseStep 1593265 = 1194949) (by norm_num)
theorem B2125757 : Blo 1415527 2125757 := bbase (se 3 (by rfl) ⟨398579, by rfl⟩ : syracuseStep 2125757 = 797159) (by norm_num)
theorem B7655381 : Blo 1415527 7655381 := bbase (se 7 (by rfl) ⟨89711, by rfl⟩ : syracuseStep 7655381 = 179423) (by norm_num)
theorem B1593301 : Blo 1415527 1593301 := bbase (se 7 (by rfl) ⟨18671, by rfl⟩ : syracuseStep 1593301 = 37343) (by norm_num)
theorem B2125781 : Blo 1415527 2125781 := bbase (se 7 (by rfl) ⟨24911, by rfl⟩ : syracuseStep 2125781 = 49823) (by norm_num)
theorem B2125805 : Blo 1415527 2125805 := bbase (se 3 (by rfl) ⟨398588, by rfl⟩ : syracuseStep 2125805 = 797177) (by norm_num)
theorem B12095477 : Blo 1415527 12095477 := bbase (se 5 (by rfl) ⟨566975, by rfl⟩ : syracuseStep 12095477 = 1133951) (by norm_num)
theorem B4034549 : Blo 1415527 4034549 := bbase (se 5 (by rfl) ⟨189119, by rfl⟩ : syracuseStep 4034549 = 378239) (by norm_num)
theorem B1593337 : Blo 1415527 1593337 := bbase (se 2 (by rfl) ⟨597501, by rfl⟩ : syracuseStep 1593337 = 1195003) (by norm_num)
theorem B3583997 : Blo 1415527 3583997 := bbase (se 3 (by rfl) ⟨671999, by rfl⟩ : syracuseStep 3583997 = 1343999) (by norm_num)
theorem B2125829 : Blo 1415527 2125829 := bbase (se 4 (by rfl) ⟨199296, by rfl⟩ : syracuseStep 2125829 = 398593) (by norm_num)
theorem B6803477 : Blo 1415527 6803477 := bbase (se 6 (by rfl) ⟨159456, by rfl⟩ : syracuseStep 6803477 = 318913) (by norm_num)
theorem B1593373 : Blo 1415527 1593373 := bbase (se 3 (by rfl) ⟨298757, by rfl⟩ : syracuseStep 1593373 = 597515) (by norm_num)
theorem B2125853 : Blo 1415527 2125853 := bbase (se 3 (by rfl) ⟨398597, by rfl⟩ : syracuseStep 2125853 = 797195) (by norm_num)
theorem B6811685 : Blo 1415527 6811685 := bbase (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) (by norm_num)
theorem B2125877 : Blo 1415527 2125877 := bbase (se 5 (by rfl) ⟨99650, by rfl⟩ : syracuseStep 2125877 = 199301) (by norm_num)
theorem B1593409 : Blo 1415527 1593409 := bbase (se 2 (by rfl) ⟨597528, by rfl⟩ : syracuseStep 1593409 = 1195057) (by norm_num)
theorem B3403853 : Blo 1415527 3403853 := bbase (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) (by norm_num)
theorem B2125901 : Blo 1415527 2125901 := bbase (se 3 (by rfl) ⟨398606, by rfl⟩ : syracuseStep 2125901 = 797213) (by norm_num)
theorem B8065109 : Blo 1415527 8065109 := bbase (se 8 (by rfl) ⟨47256, by rfl⟩ : syracuseStep 8065109 = 94513) (by norm_num)
theorem B31068245 : Blo 1415527 31068245 := bbase (se 8 (by rfl) ⟨182040, by rfl⟩ : syracuseStep 31068245 = 364081) (by norm_num)
theorem B2551909 : Blo 1415527 2551909 := bbase (se 4 (by rfl) ⟨239241, by rfl⟩ : syracuseStep 2551909 = 478483) (by norm_num)
theorem B4780133 : Blo 1415527 4780133 := bbase (se 4 (by rfl) ⟨448137, by rfl⟩ : syracuseStep 4780133 = 896275) (by norm_num)
theorem B1593445 : Blo 1415527 1593445 := bbase (se 4 (by rfl) ⟨149385, by rfl⟩ : syracuseStep 1593445 = 298771) (by norm_num)
theorem B2125925 : Blo 1415527 2125925 := bbase (se 4 (by rfl) ⟨199305, by rfl⟩ : syracuseStep 2125925 = 398611) (by norm_num)
theorem B2125949 : Blo 1415527 2125949 := bbase (se 3 (by rfl) ⟨398615, by rfl⟩ : syracuseStep 2125949 = 797231) (by norm_num)
theorem B1593481 : Blo 1415527 1593481 := bbase (se 2 (by rfl) ⟨597555, by rfl⟩ : syracuseStep 1593481 = 1195111) (by norm_num)
theorem B5378197 : Blo 1415527 5378197 := bbase (se 6 (by rfl) ⟨126051, by rfl⟩ : syracuseStep 5378197 = 252103) (by norm_num)
theorem B2125973 : Blo 1415527 2125973 := bbase (se 6 (by rfl) ⟨49827, by rfl⟩ : syracuseStep 2125973 = 99655) (by norm_num)
theorem B1593517 : Blo 1415527 1593517 := bbase (se 3 (by rfl) ⟨298784, by rfl⟩ : syracuseStep 1593517 = 597569) (by norm_num)
theorem B2125997 : Blo 1415527 2125997 := bbase (se 3 (by rfl) ⟨398624, by rfl⟩ : syracuseStep 2125997 = 797249) (by norm_num)
theorem B3584189 : Blo 1415527 3584189 := bbase (se 3 (by rfl) ⟨672035, by rfl⟩ : syracuseStep 3584189 = 1344071) (by norm_num)
theorem B2126021 : Blo 1415527 2126021 := bbase (se 4 (by rfl) ⟨199314, by rfl⟩ : syracuseStep 2126021 = 398629) (by norm_num)
theorem B1593553 : Blo 1415527 1593553 := bbase (se 2 (by rfl) ⟨597582, by rfl⟩ : syracuseStep 1593553 = 1195165) (by norm_num)
theorem B2126045 : Blo 1415527 2126045 := bbase (se 3 (by rfl) ⟨398633, by rfl⟩ : syracuseStep 2126045 = 797267) (by norm_num)
theorem B1593589 : Blo 1415527 1593589 := bbase (se 5 (by rfl) ⟨74699, by rfl⟩ : syracuseStep 1593589 = 149399) (by norm_num)
theorem B2126069 : Blo 1415527 2126069 := bbase (se 5 (by rfl) ⟨99659, by rfl⟩ : syracuseStep 2126069 = 199319) (by norm_num)
theorem B3404045 : Blo 1415527 3404045 := bbase (se 3 (by rfl) ⟨638258, by rfl⟩ : syracuseStep 3404045 = 1276517) (by norm_num)
theorem B2126093 : Blo 1415527 2126093 := bbase (se 3 (by rfl) ⟨398642, by rfl⟩ : syracuseStep 2126093 = 797285) (by norm_num)
theorem B1593625 : Blo 1415527 1593625 := bbase (se 2 (by rfl) ⟨597609, by rfl⟩ : syracuseStep 1593625 = 1195219) (by norm_num)
theorem B2724125 : Blo 1415527 2724125 := bbase (se 3 (by rfl) ⟨510773, by rfl⟩ : syracuseStep 2724125 = 1021547) (by norm_num)
theorem B1511713 : Blo 1415527 1511713 := bbase (se 2 (by rfl) ⟨566892, by rfl⟩ : syracuseStep 1511713 = 1133785) (by norm_num)
theorem B2126117 : Blo 1415527 2126117 := bbase (se 4 (by rfl) ⟨199323, by rfl⟩ : syracuseStep 2126117 = 398647) (by norm_num)
theorem B2871605 : Blo 1415527 2871605 := bbase (se 5 (by rfl) ⟨134606, by rfl⟩ : syracuseStep 2871605 = 269213) (by norm_num)
theorem B3027253 : Blo 1415527 3027253 := bbase (se 5 (by rfl) ⟨141902, by rfl⟩ : syracuseStep 3027253 = 283805) (by norm_num)
theorem B1593661 : Blo 1415527 1593661 := bbase (se 3 (by rfl) ⟨298811, by rfl⟩ : syracuseStep 1593661 = 597623) (by norm_num)
theorem B2126141 : Blo 1415527 2126141 := bbase (se 3 (by rfl) ⟨398651, by rfl⟩ : syracuseStep 2126141 = 797303) (by norm_num)
theorem B2552141 : Blo 1415527 2552141 := bbase (se 3 (by rfl) ⟨478526, by rfl⟩ : syracuseStep 2552141 = 957053) (by norm_num)
theorem B2126165 : Blo 1415527 2126165 := bbase (se 10 (by rfl) ⟨3114, by rfl⟩ : syracuseStep 2126165 = 6229) (by norm_num)
theorem B1593697 : Blo 1415527 1593697 := bbase (se 2 (by rfl) ⟨597636, by rfl⟩ : syracuseStep 1593697 = 1195273) (by norm_num)
theorem B2126189 : Blo 1415527 2126189 := bbase (se 3 (by rfl) ⟨398660, by rfl⟩ : syracuseStep 2126189 = 797321) (by norm_num)
theorem B1593733 : Blo 1415527 1593733 := bbase (se 4 (by rfl) ⟨149412, by rfl⟩ : syracuseStep 1593733 = 298825) (by norm_num)
theorem B2126213 : Blo 1415527 2126213 := bbase (se 4 (by rfl) ⟨199332, by rfl⟩ : syracuseStep 2126213 = 398665) (by norm_num)
theorem B2126237 : Blo 1415527 2126237 := bbase (se 3 (by rfl) ⟨398669, by rfl⟩ : syracuseStep 2126237 = 797339) (by norm_num)
theorem B1593769 : Blo 1415527 1593769 := bbase (se 2 (by rfl) ⟨597663, by rfl⟩ : syracuseStep 1593769 = 1195327) (by norm_num)
theorem B2126261 : Blo 1415527 2126261 := bbase (se 5 (by rfl) ⟨99668, by rfl⟩ : syracuseStep 2126261 = 199337) (by norm_num)
theorem B5378501 : Blo 1415527 5378501 := bbase (se 4 (by rfl) ⟨504234, by rfl⟩ : syracuseStep 5378501 = 1008469) (by norm_num)
theorem B7172549 : Blo 1415527 7172549 := bbase (se 4 (by rfl) ⟨672426, by rfl⟩ : syracuseStep 7172549 = 1344853) (by norm_num)
theorem B1593805 : Blo 1415527 1593805 := bbase (se 3 (by rfl) ⟨298838, by rfl⟩ : syracuseStep 1593805 = 597677) (by norm_num)
theorem B2126285 : Blo 1415527 2126285 := bbase (se 3 (by rfl) ⟨398678, by rfl⟩ : syracuseStep 2126285 = 797357) (by norm_num)
theorem B5247461 : Blo 1415527 5247461 := bbase (se 4 (by rfl) ⟨491949, by rfl⟩ : syracuseStep 5247461 = 983899) (by norm_num)
theorem B1593841 : Blo 1415527 1593841 := bbase (se 2 (by rfl) ⟨597690, by rfl⟩ : syracuseStep 1593841 = 1195381) (by norm_num)
theorem B4534805 : Blo 1415527 4534805 := bbase (se 6 (by rfl) ⟨106284, by rfl⟩ : syracuseStep 4534805 = 212569) (by norm_num)
theorem B3584533 : Blo 1415527 3584533 := bbase (se 6 (by rfl) ⟨84012, by rfl⟩ : syracuseStep 3584533 = 168025) (by norm_num)
theorem B4780565 : Blo 1415527 4780565 := bbase (se 6 (by rfl) ⟨112044, by rfl⟩ : syracuseStep 4780565 = 224089) (by norm_num)
theorem B1593877 : Blo 1415527 1593877 := bbase (se 6 (by rfl) ⟨37356, by rfl⟩ : syracuseStep 1593877 = 74713) (by norm_num)
theorem B1593913 : Blo 1415527 1593913 := bbase (se 2 (by rfl) ⟨597717, by rfl⟩ : syracuseStep 1593913 = 1195435) (by norm_num)
theorem B1593949 : Blo 1415527 1593949 := bbase (se 3 (by rfl) ⟨298865, by rfl⟩ : syracuseStep 1593949 = 597731) (by norm_num)
theorem B1593985 : Blo 1415527 1593985 := bbase (se 2 (by rfl) ⟨597744, by rfl⟩ : syracuseStep 1593985 = 1195489) (by norm_num)
theorem B3584645 : Blo 1415527 3584645 := bbase (se 4 (by rfl) ⟨336060, by rfl⟩ : syracuseStep 3584645 = 672121) (by norm_num)
theorem B4035221 : Blo 1415527 4035221 := bbase (se 6 (by rfl) ⟨94575, by rfl⟩ : syracuseStep 4035221 = 189151) (by norm_num)
theorem B1594021 : Blo 1415527 1594021 := bbase (se 4 (by rfl) ⟨149439, by rfl⟩ : syracuseStep 1594021 = 298879) (by norm_num)
theorem B3232453 : Blo 1415527 3232453 := bbase (se 4 (by rfl) ⟨303042, by rfl⟩ : syracuseStep 3232453 = 606085) (by norm_num)
theorem B1594057 : Blo 1415527 1594057 := bbase (se 2 (by rfl) ⟨597771, by rfl⟩ : syracuseStep 1594057 = 1195543) (by norm_num)
theorem B1512157 : Blo 1415527 1512157 := bbase (se 3 (by rfl) ⟨283529, by rfl⟩ : syracuseStep 1512157 = 567059) (by norm_num)
theorem B1700581 : Blo 1415527 1700581 := bbase (se 4 (by rfl) ⟨159429, by rfl⟩ : syracuseStep 1700581 = 318859) (by norm_num)
theorem B1594093 : Blo 1415527 1594093 := bbase (se 3 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 1594093 = 597785) (by norm_num)
theorem B2552573 : Blo 1415527 2552573 := bbase (se 3 (by rfl) ⟨478607, by rfl⟩ : syracuseStep 2552573 = 957215) (by norm_num)
theorem B1594129 : Blo 1415527 1594129 := bbase (se 2 (by rfl) ⟨597798, by rfl⟩ : syracuseStep 1594129 = 1195597) (by norm_num)
theorem B2388757 : Blo 1415527 2388757 := bbase (se 6 (by rfl) ⟨55986, by rfl⟩ : syracuseStep 2388757 = 111973) (by norm_num)
theorem B13611797 : Blo 1415527 13611797 := bbase (se 6 (by rfl) ⟨319026, by rfl⟩ : syracuseStep 13611797 = 638053) (by norm_num)
theorem B1512217 : Blo 1415527 1512217 := bbase (se 2 (by rfl) ⟨567081, by rfl⟩ : syracuseStep 1512217 = 1134163) (by norm_num)
theorem B1594165 : Blo 1415527 1594165 := bbase (se 5 (by rfl) ⟨74726, by rfl⟩ : syracuseStep 1594165 = 149453) (by norm_num)
theorem B3683141 : Blo 1415527 3683141 := bbase (se 4 (by rfl) ⟨345294, by rfl⟩ : syracuseStep 3683141 = 690589) (by norm_num)
theorem B3584837 : Blo 1415527 3584837 := bbase (se 4 (by rfl) ⟨336078, by rfl⟩ : syracuseStep 3584837 = 672157) (by norm_num)
theorem B6050645 : Blo 1415527 6050645 := bbase (se 9 (by rfl) ⟨17726, by rfl⟩ : syracuseStep 6050645 = 35453) (by norm_num)
theorem B1594201 : Blo 1415527 1594201 := bbase (se 2 (by rfl) ⟨597825, by rfl⟩ : syracuseStep 1594201 = 1195651) (by norm_num)
theorem B2388845 : Blo 1415527 2388845 := bbase (se 3 (by rfl) ⟨447908, by rfl⟩ : syracuseStep 2388845 = 895817) (by norm_num)
theorem B1594237 : Blo 1415527 1594237 := bbase (se 3 (by rfl) ⟨298919, by rfl⟩ : syracuseStep 1594237 = 597839) (by norm_num)
theorem B2552717 : Blo 1415527 2552717 := bbase (se 3 (by rfl) ⟨478634, by rfl⟩ : syracuseStep 2552717 = 957269) (by norm_num)
theorem B1594273 : Blo 1415527 1594273 := bbase (se 2 (by rfl) ⟨597852, by rfl⟩ : syracuseStep 1594273 = 1195705) (by norm_num)
theorem B4780997 : Blo 1415527 4780997 := bbase (se 4 (by rfl) ⟨448218, by rfl⟩ : syracuseStep 4780997 = 896437) (by norm_num)
theorem B1594309 : Blo 1415527 1594309 := bbase (se 4 (by rfl) ⟨149466, by rfl⟩ : syracuseStep 1594309 = 298933) (by norm_num)
theorem B40817621 : Blo 1415527 40817621 := bbase (se 7 (by rfl) ⟨478331, by rfl⟩ : syracuseStep 40817621 = 956663) (by norm_num)
theorem B13095893 : Blo 1415527 13095893 := bbase (se 7 (by rfl) ⟨153467, by rfl⟩ : syracuseStep 13095893 = 306935) (by norm_num)
theorem B1594345 : Blo 1415527 1594345 := bbase (se 2 (by rfl) ⟨597879, by rfl⟩ : syracuseStep 1594345 = 1195759) (by norm_num)
theorem B2388973 : Blo 1415527 2388973 := bbase (se 3 (by rfl) ⟨447932, by rfl⟩ : syracuseStep 2388973 = 895865) (by norm_num)
theorem B2872325 : Blo 1415527 2872325 := bbase (se 4 (by rfl) ⟨269280, by rfl⟩ : syracuseStep 2872325 = 538561) (by norm_num)
theorem B1594381 : Blo 1415527 1594381 := bbase (se 3 (by rfl) ⟨298946, by rfl⟩ : syracuseStep 1594381 = 597893) (by norm_num)
theorem B1594417 : Blo 1415527 1594417 := bbase (se 2 (by rfl) ⟨597906, by rfl⟩ : syracuseStep 1594417 = 1195813) (by norm_num)
theorem B2389061 : Blo 1415527 2389061 := bbase (se 4 (by rfl) ⟨223974, by rfl⟩ : syracuseStep 2389061 = 447949) (by norm_num)
theorem B4035653 : Blo 1415527 4035653 := bbase (se 4 (by rfl) ⟨378342, by rfl⟩ : syracuseStep 4035653 = 756685) (by norm_num)
theorem B1512533 : Blo 1415527 1512533 := bbase (se 8 (by rfl) ⟨8862, by rfl⟩ : syracuseStep 1512533 = 17725) (by norm_num)
theorem B1594453 : Blo 1415527 1594453 := bbase (se 8 (by rfl) ⟨9342, by rfl⟩ : syracuseStep 1594453 = 18685) (by norm_num)
theorem B1700965 : Blo 1415527 1700965 := bbase (se 4 (by rfl) ⟨159465, by rfl⟩ : syracuseStep 1700965 = 318931) (by norm_num)
theorem B4846709 : Blo 1415527 4846709 := bbase (se 5 (by rfl) ⟨227189, by rfl⟩ : syracuseStep 4846709 = 454379) (by norm_num)
theorem B1594489 : Blo 1415527 1594489 := bbase (se 2 (by rfl) ⟨597933, by rfl⟩ : syracuseStep 1594489 = 1195867) (by norm_num)
theorem B3634301 : Blo 1415527 3634301 := bbase (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) (by norm_num)
theorem B3585181 : Blo 1415527 3585181 := bbase (se 3 (by rfl) ⟨672221, by rfl⟩ : syracuseStep 3585181 = 1344443) (by norm_num)
theorem B1594525 : Blo 1415527 1594525 := bbase (se 3 (by rfl) ⟨298973, by rfl⟩ : syracuseStep 1594525 = 597947) (by norm_num)
theorem B2553005 : Blo 1415527 2553005 := bbase (se 3 (by rfl) ⟨478688, by rfl⟩ : syracuseStep 2553005 = 957377) (by norm_num)
theorem B1594561 : Blo 1415527 1594561 := bbase (se 2 (by rfl) ⟨597960, by rfl⟩ : syracuseStep 1594561 = 1195921) (by norm_num)
theorem B2389189 : Blo 1415527 2389189 := bbase (se 4 (by rfl) ⟨223986, by rfl⟩ : syracuseStep 2389189 = 447973) (by norm_num)
theorem B2421965 : Blo 1415527 2421965 := bbase (se 3 (by rfl) ⟨454118, by rfl⟩ : syracuseStep 2421965 = 908237) (by norm_num)
theorem B1594597 : Blo 1415527 1594597 := bbase (se 4 (by rfl) ⟨149493, by rfl⟩ : syracuseStep 1594597 = 298987) (by norm_num)
theorem B1594633 : Blo 1415527 1594633 := bbase (se 2 (by rfl) ⟨597987, by rfl⟩ : syracuseStep 1594633 = 1195975) (by norm_num)
theorem B3585293 : Blo 1415527 3585293 := bbase (se 3 (by rfl) ⟨672242, by rfl⟩ : syracuseStep 3585293 = 1344485) (by norm_num)
theorem B2389277 : Blo 1415527 2389277 := bbase (se 3 (by rfl) ⟨447989, by rfl⟩ : syracuseStep 2389277 = 895979) (by norm_num)
theorem B1594669 : Blo 1415527 1594669 := bbase (se 3 (by rfl) ⟨299000, by rfl⟩ : syracuseStep 1594669 = 598001) (by norm_num)
theorem B1594705 : Blo 1415527 1594705 := bbase (se 2 (by rfl) ⟨598014, by rfl⟩ : syracuseStep 1594705 = 1196029) (by norm_num)
theorem B4781429 : Blo 1415527 4781429 := bbase (se 5 (by rfl) ⟨224129, by rfl⟩ : syracuseStep 4781429 = 448259) (by norm_num)
theorem B2553229 : Blo 1415527 2553229 := bbase (se 3 (by rfl) ⟨478730, by rfl⟩ : syracuseStep 2553229 = 957461) (by norm_num)
theorem B9074069 : Blo 1415527 9074069 := bbase (se 6 (by rfl) ⟨212673, by rfl⟩ : syracuseStep 9074069 = 425347) (by norm_num)
theorem B2389405 : Blo 1415527 2389405 := bbase (se 3 (by rfl) ⟨448013, by rfl⟩ : syracuseStep 2389405 = 896027) (by norm_num)
theorem B3585485 : Blo 1415527 3585485 := bbase (se 3 (by rfl) ⟨672278, by rfl⟩ : syracuseStep 3585485 = 1344557) (by norm_num)
theorem B2553293 : Blo 1415527 2553293 := bbase (se 3 (by rfl) ⟨478742, by rfl⟩ : syracuseStep 2553293 = 957485) (by norm_num)
theorem B2389493 : Blo 1415527 2389493 := bbase (se 5 (by rfl) ⟨112007, by rfl⟩ : syracuseStep 2389493 = 224015) (by norm_num)
theorem B1512977 : Blo 1415527 1512977 := bbase (se 2 (by rfl) ⟨567366, by rfl⟩ : syracuseStep 1512977 = 1134733) (by norm_num)
theorem B1791553 : Blo 1415527 1791553 := bbase (se 2 (by rfl) ⟨671832, by rfl⟩ : syracuseStep 1791553 = 1343665) (by norm_num)
theorem B1513037 : Blo 1415527 1513037 := bbase (se 3 (by rfl) ⟨283694, by rfl⟩ : syracuseStep 1513037 = 567389) (by norm_num)
theorem B18142805 : Blo 1415527 18142805 := bbase (se 8 (by rfl) ⟨106305, by rfl⟩ : syracuseStep 18142805 = 212611) (by norm_num)
theorem B6305365 : Blo 1415527 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B2389621 : Blo 1415527 2389621 := bbase (se 5 (by rfl) ⟨112013, by rfl⟩ : syracuseStep 2389621 = 224027) (by norm_num)
theorem B1791649 : Blo 1415527 1791649 := bbase (se 2 (by rfl) ⟨671868, by rfl⟩ : syracuseStep 1791649 = 1343737) (by norm_num)
theorem B2389709 : Blo 1415527 2389709 := bbase (se 3 (by rfl) ⟨448070, by rfl⟩ : syracuseStep 2389709 = 896141) (by norm_num)
theorem B1513165 : Blo 1415527 1513165 := bbase (se 3 (by rfl) ⟨283718, by rfl⟩ : syracuseStep 1513165 = 567437) (by norm_num)
theorem B7173845 : Blo 1415527 7173845 := bbase (se 7 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 7173845 = 168137) (by norm_num)
theorem B1701653 : Blo 1415527 1701653 := bbase (se 6 (by rfl) ⟨39882, by rfl⟩ : syracuseStep 1701653 = 79765) (by norm_num)
theorem B4536101 : Blo 1415527 4536101 := bbase (se 4 (by rfl) ⟨425259, by rfl⟩ : syracuseStep 4536101 = 850519) (by norm_num)
theorem B3585829 : Blo 1415527 3585829 := bbase (se 4 (by rfl) ⟨336171, by rfl⟩ : syracuseStep 3585829 = 672343) (by norm_num)
theorem B4781861 : Blo 1415527 4781861 := bbase (se 4 (by rfl) ⟨448299, by rfl⟩ : syracuseStep 4781861 = 896599) (by norm_num)
theorem B4036405 : Blo 1415527 4036405 := bbase (se 5 (by rfl) ⟨189206, by rfl⟩ : syracuseStep 4036405 = 378413) (by norm_num)
theorem B1791821 : Blo 1415527 1791821 := bbase (se 3 (by rfl) ⟨335966, by rfl⟩ : syracuseStep 1791821 = 671933) (by norm_num)
theorem B2389837 : Blo 1415527 2389837 := bbase (se 3 (by rfl) ⟨448094, by rfl⟩ : syracuseStep 2389837 = 896189) (by norm_num)
theorem B1791877 : Blo 1415527 1791877 := bbase (se 4 (by rfl) ⟨167988, by rfl⟩ : syracuseStep 1791877 = 335977) (by norm_num)
theorem B3585941 : Blo 1415527 3585941 := bbase (se 6 (by rfl) ⟨84045, by rfl⟩ : syracuseStep 3585941 = 168091) (by norm_num)
theorem B2389925 : Blo 1415527 2389925 := bbase (se 4 (by rfl) ⟨224055, by rfl⟩ : syracuseStep 2389925 = 448111) (by norm_num)
theorem B1791973 : Blo 1415527 1791973 := bbase (se 4 (by rfl) ⟨167997, by rfl⟩ : syracuseStep 1791973 = 335995) (by norm_num)
theorem B2152469 : Blo 1415527 2152469 := bbase (se 6 (by rfl) ⟨50448, by rfl⟩ : syracuseStep 2152469 = 100897) (by norm_num)
theorem B2390053 : Blo 1415527 2390053 := bbase (se 4 (by rfl) ⟨224067, by rfl⟩ : syracuseStep 2390053 = 448135) (by norm_num)
theorem B3586133 : Blo 1415527 3586133 := bbase (se 8 (by rfl) ⟨21012, by rfl⟩ : syracuseStep 3586133 = 42025) (by norm_num)
theorem B2390141 : Blo 1415527 2390141 := bbase (se 3 (by rfl) ⟨448151, by rfl⟩ : syracuseStep 2390141 = 896303) (by norm_num)
theorem B1513609 : Blo 1415527 1513609 := bbase (se 2 (by rfl) ⟨567603, by rfl⟩ : syracuseStep 1513609 = 1135207) (by norm_num)
theorem B1792145 : Blo 1415527 1792145 := bbase (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) (by norm_num)
theorem B1792201 : Blo 1415527 1792201 := bbase (se 2 (by rfl) ⟨672075, by rfl⟩ : syracuseStep 1792201 = 1344151) (by norm_num)
theorem B4782293 : Blo 1415527 4782293 := bbase (se 7 (by rfl) ⟨56042, by rfl⟩ : syracuseStep 4782293 = 112085) (by norm_num)
theorem B2390269 : Blo 1415527 2390269 := bbase (se 3 (by rfl) ⟨448175, by rfl⟩ : syracuseStep 2390269 = 896351) (by norm_num)
theorem B1513729 : Blo 1415527 1513729 := bbase (se 2 (by rfl) ⟨567648, by rfl⟩ : syracuseStep 1513729 = 1135297) (by norm_num)
theorem B1792297 : Blo 1415527 1792297 := bbase (se 2 (by rfl) ⟨672111, by rfl⟩ : syracuseStep 1792297 = 1344223) (by norm_num)
theorem B3184973 : Blo 1415527 3184973 := bbase (se 3 (by rfl) ⟨597182, by rfl⟩ : syracuseStep 3184973 = 1194365) (by norm_num)
theorem B2390357 : Blo 1415527 2390357 := bbase (se 10 (by rfl) ⟨3501, by rfl⟩ : syracuseStep 2390357 = 7003) (by norm_num)
theorem B1702253 : Blo 1415527 1702253 := bbase (se 3 (by rfl) ⟨319172, by rfl⟩ : syracuseStep 1702253 = 638345) (by norm_num)
theorem B3185045 : Blo 1415527 3185045 := bbase (se 6 (by rfl) ⟨74649, by rfl⟩ : syracuseStep 3185045 = 149299) (by norm_num)
theorem B3586477 : Blo 1415527 3586477 := bbase (se 3 (by rfl) ⟨672464, by rfl⟩ : syracuseStep 3586477 = 1344929) (by norm_num)
theorem B10205621 : Blo 1415527 10205621 := bbase (se 5 (by rfl) ⟨478388, by rfl⟩ : syracuseStep 10205621 = 956777) (by norm_num)
theorem B1792469 : Blo 1415527 1792469 := bbase (se 7 (by rfl) ⟨21005, by rfl⟩ : syracuseStep 1792469 = 42011) (by norm_num)
theorem B2390485 : Blo 1415527 2390485 := bbase (se 7 (by rfl) ⟨28013, by rfl⟩ : syracuseStep 2390485 = 56027) (by norm_num)
theorem B3185117 : Blo 1415527 3185117 := bbase (se 3 (by rfl) ⟨597209, by rfl⟩ : syracuseStep 3185117 = 1194419) (by norm_num)
theorem B5380613 : Blo 1415527 5380613 := bbase (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) (by norm_num)
theorem B1792525 : Blo 1415527 1792525 := bbase (se 3 (by rfl) ⟨336098, by rfl⟩ : syracuseStep 1792525 = 672197) (by norm_num)
theorem B3586589 : Blo 1415527 3586589 := bbase (se 3 (by rfl) ⟨672485, by rfl⟩ : syracuseStep 3586589 = 1344971) (by norm_num)
theorem B3185189 : Blo 1415527 3185189 := bbase (se 4 (by rfl) ⟨298611, by rfl⟩ : syracuseStep 3185189 = 597223) (by norm_num)
theorem B2390573 : Blo 1415527 2390573 := bbase (se 3 (by rfl) ⟨448232, by rfl⟩ : syracuseStep 2390573 = 896465) (by norm_num)
theorem B6052421 : Blo 1415527 6052421 := bbase (se 4 (by rfl) ⟨567414, by rfl⟩ : syracuseStep 6052421 = 1134829) (by norm_num)
theorem B3185261 : Blo 1415527 3185261 := bbase (se 3 (by rfl) ⟨597236, by rfl⟩ : syracuseStep 3185261 = 1194473) (by norm_num)
theorem B1792621 : Blo 1415527 1792621 := bbase (se 3 (by rfl) ⟨336116, by rfl⟩ : syracuseStep 1792621 = 672233) (by norm_num)
theorem B1915501 : Blo 1415527 1915501 := bbase (se 3 (by rfl) ⟨359156, by rfl⟩ : syracuseStep 1915501 = 718313) (by norm_num)
theorem B4782725 : Blo 1415527 4782725 := bbase (se 4 (by rfl) ⟨448380, by rfl⟩ : syracuseStep 4782725 = 896761) (by norm_num)
theorem B1702561 : Blo 1415527 1702561 := bbase (se 2 (by rfl) ⟨638460, by rfl⟩ : syracuseStep 1702561 = 1276921) (by norm_num)
theorem B2267813 : Blo 1415527 2267813 := bbase (se 4 (by rfl) ⟨212607, by rfl⟩ : syracuseStep 2267813 = 425215) (by norm_num)
theorem B2390701 : Blo 1415527 2390701 := bbase (se 3 (by rfl) ⟨448256, by rfl⟩ : syracuseStep 2390701 = 896513) (by norm_num)
theorem B3185333 : Blo 1415527 3185333 := bbase (se 5 (by rfl) ⟨149312, by rfl⟩ : syracuseStep 3185333 = 298625) (by norm_num)
theorem B5454533 : Blo 1415527 5454533 := bbase (se 4 (by rfl) ⟨511362, by rfl⟩ : syracuseStep 5454533 = 1022725) (by norm_num)
theorem B10205909 : Blo 1415527 10205909 := bbase (se 7 (by rfl) ⟨119600, by rfl⟩ : syracuseStep 10205909 = 239201) (by norm_num)
theorem B3586781 : Blo 1415527 3586781 := bbase (se 3 (by rfl) ⟨672521, by rfl⟩ : syracuseStep 3586781 = 1345043) (by norm_num)
theorem B3185405 : Blo 1415527 3185405 := bbase (se 3 (by rfl) ⟨597263, by rfl⟩ : syracuseStep 3185405 = 1194527) (by norm_num)
theorem B1702657 : Blo 1415527 1702657 := bbase (se 2 (by rfl) ⟨638496, by rfl⟩ : syracuseStep 1702657 = 1276993) (by norm_num)
theorem B2390789 : Blo 1415527 2390789 := bbase (se 4 (by rfl) ⟨224136, by rfl⟩ : syracuseStep 2390789 = 448273) (by norm_num)
theorem B1817353 : Blo 1415527 1817353 := bbase (se 2 (by rfl) ⟨681507, by rfl⟩ : syracuseStep 1817353 = 1363015) (by norm_num)
theorem B1792793 : Blo 1415527 1792793 := bbase (se 2 (by rfl) ⟨672297, by rfl⟩ : syracuseStep 1792793 = 1344595) (by norm_num)
theorem B5380901 : Blo 1415527 5380901 := bbase (se 4 (by rfl) ⟨504459, by rfl⟩ : syracuseStep 5380901 = 1008919) (by norm_num)
theorem B1702705 : Blo 1415527 1702705 := bbase (se 2 (by rfl) ⟨638514, by rfl⟩ : syracuseStep 1702705 = 1277029) (by norm_num)
theorem B3636029 : Blo 1415527 3636029 := bbase (se 3 (by rfl) ⟨681755, by rfl⟩ : syracuseStep 3636029 = 1363511) (by norm_num)
theorem B3185477 : Blo 1415527 3185477 := bbase (se 4 (by rfl) ⟨298638, by rfl⟩ : syracuseStep 3185477 = 597277) (by norm_num)
theorem B1792849 : Blo 1415527 1792849 := bbase (se 2 (by rfl) ⟨672318, by rfl⟩ : syracuseStep 1792849 = 1344637) (by norm_num)
theorem B2390917 : Blo 1415527 2390917 := bbase (se 4 (by rfl) ⟨224148, by rfl⟩ : syracuseStep 2390917 = 448297) (by norm_num)
theorem B3185549 : Blo 1415527 3185549 := bbase (se 3 (by rfl) ⟨597290, by rfl⟩ : syracuseStep 3185549 = 1194581) (by norm_num)
theorem B1792945 : Blo 1415527 1792945 := bbase (se 2 (by rfl) ⟨672354, by rfl⟩ : syracuseStep 1792945 = 1344709) (by norm_num)
theorem B3185621 : Blo 1415527 3185621 := bbase (se 7 (by rfl) ⟨37331, by rfl⟩ : syracuseStep 3185621 = 74663) (by norm_num)
theorem B2391005 : Blo 1415527 2391005 := bbase (se 3 (by rfl) ⟨448313, by rfl⟩ : syracuseStep 2391005 = 896627) (by norm_num)
theorem B7175141 : Blo 1415527 7175141 := bbase (se 4 (by rfl) ⟨672669, by rfl⟩ : syracuseStep 7175141 = 1345339) (by norm_num)
theorem B3185693 : Blo 1415527 3185693 := bbase (se 3 (by rfl) ⟨597317, by rfl⟩ : syracuseStep 3185693 = 1194635) (by norm_num)
theorem B3587125 : Blo 1415527 3587125 := bbase (se 5 (by rfl) ⟨168146, by rfl⟩ : syracuseStep 3587125 = 336293) (by norm_num)
theorem B4783157 : Blo 1415527 4783157 := bbase (se 5 (by rfl) ⟨224210, by rfl⟩ : syracuseStep 4783157 = 448421) (by norm_num)
theorem B1793117 : Blo 1415527 1793117 := bbase (se 3 (by rfl) ⟨336209, by rfl⟩ : syracuseStep 1793117 = 672419) (by norm_num)
theorem B2391133 : Blo 1415527 2391133 := bbase (se 3 (by rfl) ⟨448337, by rfl⟩ : syracuseStep 2391133 = 896675) (by norm_num)
theorem B3185765 : Blo 1415527 3185765 := bbase (se 4 (by rfl) ⟨298665, by rfl⟩ : syracuseStep 3185765 = 597331) (by norm_num)
theorem B1793173 : Blo 1415527 1793173 := bbase (se 6 (by rfl) ⟨42027, by rfl⟩ : syracuseStep 1793173 = 84055) (by norm_num)
theorem B3587237 : Blo 1415527 3587237 := bbase (se 4 (by rfl) ⟨336303, by rfl⟩ : syracuseStep 3587237 = 672607) (by norm_num)
theorem B3185837 : Blo 1415527 3185837 := bbase (se 3 (by rfl) ⟨597344, by rfl⟩ : syracuseStep 3185837 = 1194689) (by norm_num)
theorem B11484341 : Blo 1415527 11484341 := bbase (se 5 (by rfl) ⟨538328, by rfl⟩ : syracuseStep 11484341 = 1076657) (by norm_num)
theorem B2391221 : Blo 1415527 2391221 := bbase (se 5 (by rfl) ⟨112088, by rfl⟩ : syracuseStep 2391221 = 224177) (by norm_num)
theorem B3185909 : Blo 1415527 3185909 := bbase (se 5 (by rfl) ⟨149339, by rfl⟩ : syracuseStep 3185909 = 298679) (by norm_num)
theorem B1793269 : Blo 1415527 1793269 := bbase (se 5 (by rfl) ⟨84059, by rfl⟩ : syracuseStep 1793269 = 168119) (by norm_num)
theorem B10206485 : Blo 1415527 10206485 := bbase (se 6 (by rfl) ⟨239214, by rfl⟩ : syracuseStep 10206485 = 478429) (by norm_num)
theorem B2268461 : Blo 1415527 2268461 := bbase (se 3 (by rfl) ⟨425336, by rfl⟩ : syracuseStep 2268461 = 850673) (by norm_num)
theorem B2391349 : Blo 1415527 2391349 := bbase (se 5 (by rfl) ⟨112094, by rfl⟩ : syracuseStep 2391349 = 224189) (by norm_num)
theorem B3185981 : Blo 1415527 3185981 := bbase (se 3 (by rfl) ⟨597371, by rfl⟩ : syracuseStep 3185981 = 1194743) (by norm_num)
theorem B3587429 : Blo 1415527 3587429 := bbase (se 4 (by rfl) ⟨336321, by rfl⟩ : syracuseStep 3587429 = 672643) (by norm_num)
theorem B7167365 : Blo 1415527 7167365 := bbase (se 4 (by rfl) ⟨671940, by rfl⟩ : syracuseStep 7167365 = 1343881) (by norm_num)
theorem B3186053 : Blo 1415527 3186053 := bbase (se 4 (by rfl) ⟨298692, by rfl⟩ : syracuseStep 3186053 = 597385) (by norm_num)
theorem B2391437 : Blo 1415527 2391437 := bbase (se 3 (by rfl) ⟨448394, by rfl⟩ : syracuseStep 2391437 = 896789) (by norm_num)
theorem B1793441 : Blo 1415527 1793441 := bbase (se 2 (by rfl) ⟨672540, by rfl⟩ : syracuseStep 1793441 = 1345081) (by norm_num)
theorem B3186125 : Blo 1415527 3186125 := bbase (se 3 (by rfl) ⟨597398, by rfl⟩ : syracuseStep 3186125 = 1194797) (by norm_num)
theorem B1793497 : Blo 1415527 1793497 := bbase (se 2 (by rfl) ⟨672561, by rfl⟩ : syracuseStep 1793497 = 1345123) (by norm_num)
theorem B4783589 : Blo 1415527 4783589 := bbase (se 4 (by rfl) ⟨448461, by rfl⟩ : syracuseStep 4783589 = 896923) (by norm_num)
theorem B2391565 : Blo 1415527 2391565 := bbase (se 3 (by rfl) ⟨448418, by rfl⟩ : syracuseStep 2391565 = 896837) (by norm_num)
theorem B3186197 : Blo 1415527 3186197 := bbase (se 6 (by rfl) ⟨74676, by rfl⟩ : syracuseStep 3186197 = 149353) (by norm_num)
theorem B3276341 : Blo 1415527 3276341 := bbase (se 5 (by rfl) ⟨153578, by rfl⟩ : syracuseStep 3276341 = 307157) (by norm_num)
theorem B2424373 : Blo 1415527 2424373 := bbase (se 5 (by rfl) ⟨113642, by rfl⟩ : syracuseStep 2424373 = 227285) (by norm_num)
theorem B1793593 : Blo 1415527 1793593 := bbase (se 2 (by rfl) ⟨672597, by rfl⟩ : syracuseStep 1793593 = 1345195) (by norm_num)
theorem B1818173 : Blo 1415527 1818173 := bbase (se 3 (by rfl) ⟨340907, by rfl⟩ : syracuseStep 1818173 = 681815) (by norm_num)
theorem B3186269 : Blo 1415527 3186269 := bbase (se 3 (by rfl) ⟨597425, by rfl⟩ : syracuseStep 3186269 = 1194851) (by norm_num)
theorem B4537957 : Blo 1415527 4537957 := bbase (se 4 (by rfl) ⟨425433, by rfl⟩ : syracuseStep 4537957 = 850867) (by norm_num)
theorem B2391653 : Blo 1415527 2391653 := bbase (se 4 (by rfl) ⟨224217, by rfl⟩ : syracuseStep 2391653 = 448435) (by norm_num)
theorem B3186341 : Blo 1415527 3186341 := bbase (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) (by norm_num)
theorem B3587773 : Blo 1415527 3587773 := bbase (se 3 (by rfl) ⟨672707, by rfl⟩ : syracuseStep 3587773 = 1345415) (by norm_num)
theorem B1793765 : Blo 1415527 1793765 := bbase (se 4 (by rfl) ⟨168165, by rfl⟩ : syracuseStep 1793765 = 336331) (by norm_num)
theorem B2391781 : Blo 1415527 2391781 := bbase (se 4 (by rfl) ⟨224229, by rfl⟩ : syracuseStep 2391781 = 448459) (by norm_num)
theorem B3186413 : Blo 1415527 3186413 := bbase (se 3 (by rfl) ⟨597452, by rfl⟩ : syracuseStep 3186413 = 1194905) (by norm_num)
theorem B1793821 : Blo 1415527 1793821 := bbase (se 3 (by rfl) ⟨336341, by rfl⟩ : syracuseStep 1793821 = 672683) (by norm_num)
theorem B3587885 : Blo 1415527 3587885 := bbase (se 3 (by rfl) ⟨672728, by rfl⟩ : syracuseStep 3587885 = 1345457) (by norm_num)
theorem B3186485 : Blo 1415527 3186485 := bbase (se 5 (by rfl) ⟨149366, by rfl⟩ : syracuseStep 3186485 = 298733) (by norm_num)
theorem B2154293 : Blo 1415527 2154293 := bbase (se 5 (by rfl) ⟨100982, by rfl⟩ : syracuseStep 2154293 = 201965) (by norm_num)
theorem B2391869 : Blo 1415527 2391869 := bbase (se 3 (by rfl) ⟨448475, by rfl⟩ : syracuseStep 2391869 = 896951) (by norm_num)
theorem B6807397 : Blo 1415527 6807397 := bbase (se 4 (by rfl) ⟨638193, by rfl⟩ : syracuseStep 6807397 = 1276387) (by norm_num)
theorem B3186557 : Blo 1415527 3186557 := bbase (se 3 (by rfl) ⟨597479, by rfl⟩ : syracuseStep 3186557 = 1194959) (by norm_num)
theorem B1793917 : Blo 1415527 1793917 := bbase (se 3 (by rfl) ⟨336359, by rfl⟩ : syracuseStep 1793917 = 672719) (by norm_num)
theorem B4308869 : Blo 1415527 4308869 := bbase (se 4 (by rfl) ⟨403956, by rfl⟩ : syracuseStep 4308869 = 807913) (by norm_num)
theorem B4784021 : Blo 1415527 4784021 := bbase (se 6 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 4784021 = 224251) (by norm_num)
theorem B3448757 : Blo 1415527 3448757 := bbase (se 5 (by rfl) ⟨161660, by rfl⟩ : syracuseStep 3448757 = 323321) (by norm_num)
theorem B2391997 : Blo 1415527 2391997 := bbase (se 3 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 2391997 = 896999) (by norm_num)
theorem B3186629 : Blo 1415527 3186629 := bbase (se 4 (by rfl) ⟨298746, by rfl⟩ : syracuseStep 3186629 = 597493) (by norm_num)
theorem B5382085 : Blo 1415527 5382085 := bbase (se 4 (by rfl) ⟨504570, by rfl⟩ : syracuseStep 5382085 = 1009141) (by norm_num)
theorem B3588077 : Blo 1415527 3588077 := bbase (se 3 (by rfl) ⟨672764, by rfl⟩ : syracuseStep 3588077 = 1345529) (by norm_num)
theorem B1417219 : Blo 1415527 1417219 := bstep (se 1 (by rfl) ⟨1062914, by rfl⟩ : syracuseStep 1417219 = 2125829) B2125829
theorem B7168013 : Blo 1415527 7168013 := bstep (se 3 (by rfl) ⟨1344002, by rfl⟩ : syracuseStep 7168013 = 2688005) B2688005
theorem B1417235 : Blo 1415527 1417235 := bstep (se 1 (by rfl) ⟨1062926, by rfl⟩ : syracuseStep 1417235 = 2125853) B2125853
theorem B1417251 : Blo 1415527 1417251 := bstep (se 1 (by rfl) ⟨1062938, by rfl⟩ : syracuseStep 1417251 = 2125877) B2125877
theorem B3186737 : Blo 1415527 3186737 := bstep (se 2 (by rfl) ⟨1195026, by rfl⟩ : syracuseStep 3186737 = 2390053) B2390053
theorem B2269235 : Blo 1415527 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B1417267 : Blo 1415527 1417267 := bstep (se 1 (by rfl) ⟨1062950, by rfl⟩ : syracuseStep 1417267 = 2125901) B2125901
theorem B3186755 : Blo 1415527 3186755 := bstep (se 1 (by rfl) ⟨2390066, by rfl⟩ : syracuseStep 3186755 = 4780133) B4780133
theorem B1417283 : Blo 1415527 1417283 := bstep (se 1 (by rfl) ⟨1062962, by rfl⟩ : syracuseStep 1417283 = 2125925) B2125925
theorem B1417299 : Blo 1415527 1417299 := bstep (se 1 (by rfl) ⟨1062974, by rfl⟩ : syracuseStep 1417299 = 2125949) B2125949
theorem B1417315 : Blo 1415527 1417315 := bstep (se 1 (by rfl) ⟨1062986, by rfl⟩ : syracuseStep 1417315 = 2125973) B2125973
theorem B1417331 : Blo 1415527 1417331 := bstep (se 1 (by rfl) ⟨1062998, by rfl⟩ : syracuseStep 1417331 = 2125997) B2125997
theorem B1417347 : Blo 1415527 1417347 := bstep (se 1 (by rfl) ⟨1063010, by rfl⟩ : syracuseStep 1417347 = 2126021) B2126021
theorem B2490515 : Blo 1415527 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B1417363 : Blo 1415527 1417363 := bstep (se 1 (by rfl) ⟨1063022, by rfl⟩ : syracuseStep 1417363 = 2126045) B2126045
theorem B8618147 : Blo 1415527 8618147 := bstep (se 1 (by rfl) ⟨6463610, by rfl⟩ : syracuseStep 8618147 = 12927221) B12927221
theorem B1417379 : Blo 1415527 1417379 := bstep (se 1 (by rfl) ⟨1063034, by rfl⟩ : syracuseStep 1417379 = 2126069) B2126069
theorem B1417395 : Blo 1415527 1417395 := bstep (se 1 (by rfl) ⟨1063046, by rfl⟩ : syracuseStep 1417395 = 2126093) B2126093
theorem B1417411 : Blo 1415527 1417411 := bstep (se 1 (by rfl) ⟨1063058, by rfl⟩ : syracuseStep 1417411 = 2126117) B2126117
theorem B1417427 : Blo 1415527 1417427 := bstep (se 1 (by rfl) ⟨1063070, by rfl⟩ : syracuseStep 1417427 = 2126141) B2126141
theorem B1417443 : Blo 1415527 1417443 := bstep (se 1 (by rfl) ⟨1063082, by rfl⟩ : syracuseStep 1417443 = 2126165) B2126165
theorem B1417459 : Blo 1415527 1417459 := bstep (se 1 (by rfl) ⟨1063094, by rfl⟩ : syracuseStep 1417459 = 2126189) B2126189
theorem B1417475 : Blo 1415527 1417475 := bstep (se 1 (by rfl) ⟨1063106, by rfl⟩ : syracuseStep 1417475 = 2126213) B2126213
theorem B1417491 : Blo 1415527 1417491 := bstep (se 1 (by rfl) ⟨1063118, by rfl⟩ : syracuseStep 1417491 = 2126237) B2126237
theorem B1417507 : Blo 1415527 1417507 := bstep (se 1 (by rfl) ⟨1063130, by rfl⟩ : syracuseStep 1417507 = 2126261) B2126261
theorem B1417523 : Blo 1415527 1417523 := bstep (se 1 (by rfl) ⟨1063142, by rfl⟩ : syracuseStep 1417523 = 2126285) B2126285
theorem B9691469 : Blo 1415527 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B3187025 : Blo 1415527 3187025 := bstep (se 2 (by rfl) ⟨1195134, by rfl⟩ : syracuseStep 3187025 = 2390269) B2390269
theorem B3187043 : Blo 1415527 3187043 := bstep (se 1 (by rfl) ⟨2390282, by rfl⟩ : syracuseStep 3187043 = 4780565) B4780565
theorem B2015617 : Blo 1415527 2015617 := bstep (se 2 (by rfl) ⟨755856, by rfl⟩ : syracuseStep 2015617 = 1511713) B1511713
theorem B2015651 : Blo 1415527 2015651 := bstep (se 1 (by rfl) ⟨1511738, by rfl⟩ : syracuseStep 2015651 = 3023477) B3023477
theorem B6808013 : Blo 1415527 6808013 := bstep (se 3 (by rfl) ⟨1276502, by rfl⟩ : syracuseStep 6808013 = 2553005) B2553005
theorem B9093667 : Blo 1415527 9093667 := bstep (se 1 (by rfl) ⟨6820250, by rfl⟩ : syracuseStep 9093667 = 13640501) B13640501
theorem B13615715 : Blo 1415527 13615715 := bstep (se 1 (by rfl) ⟨10211786, by rfl⟩ : syracuseStep 13615715 = 20423573) B20423573
theorem B3187313 : Blo 1415527 3187313 := bstep (se 2 (by rfl) ⟨1195242, by rfl⟩ : syracuseStep 3187313 = 2390485) B2390485
theorem B3187331 : Blo 1415527 3187331 := bstep (se 1 (by rfl) ⟨2390498, by rfl⟩ : syracuseStep 3187331 = 4780997) B4780997
theorem B9077453 : Blo 1415527 9077453 := bstep (se 3 (by rfl) ⟨1702022, by rfl⟩ : syracuseStep 9077453 = 3404045) B3404045
theorem B3826385 : Blo 1415527 3826385 := bstep (se 2 (by rfl) ⟨1434894, by rfl⟩ : syracuseStep 3826385 = 2869789) B2869789
theorem B27984611 : Blo 1415527 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B1614643 : Blo 1415527 1614643 := bstep (se 1 (by rfl) ⟨1210982, by rfl⟩ : syracuseStep 1614643 = 2421965) B2421965
theorem B2270081 : Blo 1415527 2270081 := bstep (se 2 (by rfl) ⟨851280, by rfl⟩ : syracuseStep 2270081 = 1702561) B1702561
theorem B3187601 : Blo 1415527 3187601 := bstep (se 2 (by rfl) ⟨1195350, by rfl⟩ : syracuseStep 3187601 = 2390701) B2390701
theorem B3187619 : Blo 1415527 3187619 := bstep (se 1 (by rfl) ⟨2390714, by rfl⟩ : syracuseStep 3187619 = 4781429) B4781429
theorem B4309937 : Blo 1415527 4309937 := bstep (se 2 (by rfl) ⟨1616226, by rfl⟩ : syracuseStep 4309937 = 3232453) B3232453
theorem B15745973 : Blo 1415527 15745973 := bstep (se 5 (by rfl) ⟨738092, by rfl⟩ : syracuseStep 15745973 = 1476185) B1476185
theorem B4539341 : Blo 1415527 4539341 := bstep (se 3 (by rfl) ⟨851126, by rfl⟩ : syracuseStep 4539341 = 1702253) B1702253
theorem B2016209 : Blo 1415527 2016209 := bstep (se 2 (by rfl) ⟨756078, by rfl⟩ : syracuseStep 2016209 = 1512157) B1512157
theorem B5104625 : Blo 1415527 5104625 := bstep (se 2 (by rfl) ⟨1914234, by rfl⟩ : syracuseStep 5104625 = 3828469) B3828469
theorem B2270209 : Blo 1415527 2270209 := bstep (se 2 (by rfl) ⟨851328, by rfl⟩ : syracuseStep 2270209 = 1702657) B1702657
theorem B2016289 : Blo 1415527 2016289 := bstep (se 2 (by rfl) ⟨756108, by rfl⟩ : syracuseStep 2016289 = 1512217) B1512217
theorem B2270273 : Blo 1415527 2270273 := bstep (se 2 (by rfl) ⟨851352, by rfl⟩ : syracuseStep 2270273 = 1702705) B1702705
theorem B4031633 : Blo 1415527 4031633 := bstep (se 2 (by rfl) ⟨1511862, by rfl⟩ : syracuseStep 4031633 = 3023725) B3023725
theorem B3187889 : Blo 1415527 3187889 := bstep (se 2 (by rfl) ⟨1195458, by rfl⟩ : syracuseStep 3187889 = 2390917) B2390917
theorem B3024067 : Blo 1415527 3024067 := bstep (se 1 (by rfl) ⟨2268050, by rfl⟩ : syracuseStep 3024067 = 4536101) B4536101
theorem B3187907 : Blo 1415527 3187907 := bstep (se 1 (by rfl) ⟨2390930, by rfl⟩ : syracuseStep 3187907 = 4781861) B4781861
theorem B6808781 : Blo 1415527 6808781 := bstep (se 3 (by rfl) ⟨1276646, by rfl⟩ : syracuseStep 6808781 = 2553293) B2553293
theorem B8062193 : Blo 1415527 8062193 := bstep (se 2 (by rfl) ⟨3023322, by rfl⟩ : syracuseStep 8062193 = 6046645) B6046645
theorem B2688241 : Blo 1415527 2688241 := bstep (se 2 (by rfl) ⟨1008090, by rfl⟩ : syracuseStep 2688241 = 2016181) B2016181
theorem B13993229 : Blo 1415527 13993229 := bstep (se 3 (by rfl) ⟨2623730, by rfl⟩ : syracuseStep 13993229 = 5247461) B5247461
theorem B5375267 : Blo 1415527 5375267 := bstep (se 1 (by rfl) ⟨4031450, by rfl⟩ : syracuseStep 5375267 = 8062901) B8062901
theorem B5375281 : Blo 1415527 5375281 := bstep (se 2 (by rfl) ⟨2015730, by rfl⟩ : syracuseStep 5375281 = 4031461) B4031461
theorem B1434979 : Blo 1415527 1434979 := bstep (se 1 (by rfl) ⟨1076234, by rfl⟩ : syracuseStep 1434979 = 2152469) B2152469
theorem B12092813 : Blo 1415527 12092813 := bstep (se 3 (by rfl) ⟨2267402, by rfl⟩ : syracuseStep 12092813 = 4534805) B4534805
theorem B3188177 : Blo 1415527 3188177 := bstep (se 2 (by rfl) ⟨1195566, by rfl⟩ : syracuseStep 3188177 = 2391133) B2391133
theorem B3188195 : Blo 1415527 3188195 := bstep (se 1 (by rfl) ⟨2391146, by rfl⟩ : syracuseStep 3188195 = 4782293) B4782293
theorem B12109283 : Blo 1415527 12109283 := bstep (se 1 (by rfl) ⟨9081962, by rfl⟩ : syracuseStep 12109283 = 18163925) B18163925
theorem B2123297 : Blo 1415527 2123297 := bstep (se 2 (by rfl) ⟨796236, by rfl⟩ : syracuseStep 2123297 = 1592473) B1592473
theorem B2123315 : Blo 1415527 2123315 := bstep (se 1 (by rfl) ⟨1592486, by rfl⟩ : syracuseStep 2123315 = 3184973) B3184973
theorem B2123345 : Blo 1415527 2123345 := bstep (se 2 (by rfl) ⟨796254, by rfl⟩ : syracuseStep 2123345 = 1592509) B1592509
theorem B2123363 : Blo 1415527 2123363 := bstep (se 1 (by rfl) ⟨1592522, by rfl⟩ : syracuseStep 2123363 = 3185045) B3185045
theorem B2123393 : Blo 1415527 2123393 := bstep (se 2 (by rfl) ⟨796272, by rfl⟩ : syracuseStep 2123393 = 1592545) B1592545
theorem B2688643 : Blo 1415527 2688643 := bstep (se 1 (by rfl) ⟨2016482, by rfl⟩ : syracuseStep 2688643 = 4032965) B4032965
theorem B2123411 : Blo 1415527 2123411 := bstep (se 1 (by rfl) ⟨1592558, by rfl⟩ : syracuseStep 2123411 = 3185117) B3185117
theorem B4777649 : Blo 1415527 4777649 := bstep (se 2 (by rfl) ⟨1791618, by rfl⟩ : syracuseStep 4777649 = 3583237) B3583237
theorem B2123441 : Blo 1415527 2123441 := bstep (se 2 (by rfl) ⟨796290, by rfl⟩ : syracuseStep 2123441 = 1592581) B1592581
theorem B2688689 : Blo 1415527 2688689 := bstep (se 2 (by rfl) ⟨1008258, by rfl⟩ : syracuseStep 2688689 = 2016517) B2016517
theorem B2123459 : Blo 1415527 2123459 := bstep (se 1 (by rfl) ⟨1592594, by rfl⟩ : syracuseStep 2123459 = 3185189) B3185189
theorem B8611525 : Blo 1415527 8611525 := bstep (se 4 (by rfl) ⟨807330, by rfl⟩ : syracuseStep 8611525 = 1614661) B1614661
theorem B2123489 : Blo 1415527 2123489 := bstep (se 2 (by rfl) ⟨796308, by rfl⟩ : syracuseStep 2123489 = 1592617) B1592617
theorem B3188465 : Blo 1415527 3188465 := bstep (se 2 (by rfl) ⟨1195674, by rfl⟩ : syracuseStep 3188465 = 2391349) B2391349
theorem B2123507 : Blo 1415527 2123507 := bstep (se 1 (by rfl) ⟨1592630, by rfl⟩ : syracuseStep 2123507 = 3185261) B3185261
theorem B3188483 : Blo 1415527 3188483 := bstep (se 1 (by rfl) ⟨2391362, by rfl⟩ : syracuseStep 3188483 = 4782725) B4782725
theorem B7653133 : Blo 1415527 7653133 := bstep (se 3 (by rfl) ⟨1434962, by rfl⟩ : syracuseStep 7653133 = 2869925) B2869925
theorem B2123537 : Blo 1415527 2123537 := bstep (se 2 (by rfl) ⟨796326, by rfl⟩ : syracuseStep 2123537 = 1592653) B1592653
theorem B2123555 : Blo 1415527 2123555 := bstep (se 1 (by rfl) ⟨1592666, by rfl⟩ : syracuseStep 2123555 = 3185333) B3185333
theorem B4032305 : Blo 1415527 4032305 := bstep (se 2 (by rfl) ⟨1512114, by rfl⟩ : syracuseStep 4032305 = 3024229) B3024229
theorem B2017075 : Blo 1415527 2017075 := bstep (se 1 (by rfl) ⟨1512806, by rfl⟩ : syracuseStep 2017075 = 3025613) B3025613
theorem B2123585 : Blo 1415527 2123585 := bstep (se 2 (by rfl) ⟨796344, by rfl⟩ : syracuseStep 2123585 = 1592689) B1592689
theorem B2123603 : Blo 1415527 2123603 := bstep (se 1 (by rfl) ⟨1592702, by rfl⟩ : syracuseStep 2123603 = 3185405) B3185405
theorem B3401585 : Blo 1415527 3401585 := bstep (se 2 (by rfl) ⟨1275594, by rfl⟩ : syracuseStep 3401585 = 2551189) B2551189
theorem B2123633 : Blo 1415527 2123633 := bstep (se 2 (by rfl) ⟨796362, by rfl⟩ : syracuseStep 2123633 = 1592725) B1592725
theorem B2123651 : Blo 1415527 2123651 := bstep (se 1 (by rfl) ⟨1592738, by rfl⟩ : syracuseStep 2123651 = 3185477) B3185477
theorem B2123681 : Blo 1415527 2123681 := bstep (se 2 (by rfl) ⟨796380, by rfl⟩ : syracuseStep 2123681 = 1592761) B1592761
theorem B2123699 : Blo 1415527 2123699 := bstep (se 1 (by rfl) ⟨1592774, by rfl⟩ : syracuseStep 2123699 = 3185549) B3185549
theorem B2123729 : Blo 1415527 2123729 := bstep (se 2 (by rfl) ⟨796398, by rfl⟩ : syracuseStep 2123729 = 1592797) B1592797
theorem B2688977 : Blo 1415527 2688977 := bstep (se 2 (by rfl) ⟨1008366, by rfl⟩ : syracuseStep 2688977 = 2016733) B2016733
theorem B2123747 : Blo 1415527 2123747 := bstep (se 1 (by rfl) ⟨1592810, by rfl⟩ : syracuseStep 2123747 = 3185621) B3185621
theorem B2123777 : Blo 1415527 2123777 := bstep (se 2 (by rfl) ⟨796416, by rfl⟩ : syracuseStep 2123777 = 1592833) B1592833
theorem B3188753 : Blo 1415527 3188753 := bstep (se 2 (by rfl) ⟨1195782, by rfl⟩ : syracuseStep 3188753 = 2391565) B2391565
theorem B2123795 : Blo 1415527 2123795 := bstep (se 1 (by rfl) ⟨1592846, by rfl⟩ : syracuseStep 2123795 = 3185693) B3185693
theorem B3188771 : Blo 1415527 3188771 := bstep (se 1 (by rfl) ⟨2391578, by rfl⟩ : syracuseStep 3188771 = 4783157) B4783157
theorem B2123825 : Blo 1415527 2123825 := bstep (se 2 (by rfl) ⟨796434, by rfl⟩ : syracuseStep 2123825 = 1592869) B1592869
theorem B2123843 : Blo 1415527 2123843 := bstep (se 1 (by rfl) ⟨1592882, by rfl⟩ : syracuseStep 2123843 = 3185765) B3185765
theorem B2123873 : Blo 1415527 2123873 := bstep (se 2 (by rfl) ⟨796452, by rfl⟩ : syracuseStep 2123873 = 1592905) B1592905
theorem B8407153 : Blo 1415527 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B2123891 : Blo 1415527 2123891 := bstep (se 1 (by rfl) ⟨1592918, by rfl⟩ : syracuseStep 2123891 = 3185837) B3185837
theorem B2123921 : Blo 1415527 2123921 := bstep (se 2 (by rfl) ⟨796470, by rfl⟩ : syracuseStep 2123921 = 1592941) B1592941
theorem B2123939 : Blo 1415527 2123939 := bstep (se 1 (by rfl) ⟨1592954, by rfl⟩ : syracuseStep 2123939 = 3185909) B3185909
theorem B2123969 : Blo 1415527 2123969 := bstep (se 2 (by rfl) ⟨796488, by rfl⟩ : syracuseStep 2123969 = 1592977) B1592977
theorem B4778189 : Blo 1415527 4778189 := bstep (se 3 (by rfl) ⟨895910, by rfl⟩ : syracuseStep 4778189 = 1791821) B1791821
theorem B2123987 : Blo 1415527 2123987 := bstep (se 1 (by rfl) ⟨1592990, by rfl⟩ : syracuseStep 2123987 = 3185981) B3185981
theorem B2124017 : Blo 1415527 2124017 := bstep (se 2 (by rfl) ⟨796506, by rfl⟩ : syracuseStep 2124017 = 1593013) B1593013
theorem B4778243 : Blo 1415527 4778243 := bstep (se 1 (by rfl) ⟨3583682, by rfl⟩ : syracuseStep 4778243 = 7167365) B7167365
theorem B2124035 : Blo 1415527 2124035 := bstep (se 1 (by rfl) ⟨1593026, by rfl⟩ : syracuseStep 2124035 = 3186053) B3186053
theorem B2017553 : Blo 1415527 2017553 := bstep (se 2 (by rfl) ⟨756582, by rfl⟩ : syracuseStep 2017553 = 1513165) B1513165
theorem B2124065 : Blo 1415527 2124065 := bstep (se 2 (by rfl) ⟨796524, by rfl⟩ : syracuseStep 2124065 = 1593049) B1593049
theorem B3189041 : Blo 1415527 3189041 := bstep (se 2 (by rfl) ⟨1195890, by rfl⟩ : syracuseStep 3189041 = 2391781) B2391781
theorem B2124083 : Blo 1415527 2124083 := bstep (se 1 (by rfl) ⟨1593062, by rfl⟩ : syracuseStep 2124083 = 3186125) B3186125
theorem B3189059 : Blo 1415527 3189059 := bstep (se 1 (by rfl) ⟨2391794, by rfl⟩ : syracuseStep 3189059 = 4783589) B4783589
theorem B2124113 : Blo 1415527 2124113 := bstep (se 2 (by rfl) ⟨796542, by rfl⟩ : syracuseStep 2124113 = 1593085) B1593085
theorem B2124131 : Blo 1415527 2124131 := bstep (se 1 (by rfl) ⟨1593098, by rfl⟩ : syracuseStep 2124131 = 3186197) B3186197
theorem B2124161 : Blo 1415527 2124161 := bstep (se 2 (by rfl) ⟨796560, by rfl⟩ : syracuseStep 2124161 = 1593121) B1593121
theorem B2017667 : Blo 1415527 2017667 := bstep (se 1 (by rfl) ⟨1513250, by rfl⟩ : syracuseStep 2017667 = 3026501) B3026501
theorem B2124179 : Blo 1415527 2124179 := bstep (se 1 (by rfl) ⟨1593134, by rfl⟩ : syracuseStep 2124179 = 3186269) B3186269
theorem B2124209 : Blo 1415527 2124209 := bstep (se 2 (by rfl) ⟨796578, by rfl⟩ : syracuseStep 2124209 = 1593157) B1593157
theorem B2124227 : Blo 1415527 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B8088005 : Blo 1415527 8088005 := bstep (se 4 (by rfl) ⟨758250, by rfl⟩ : syracuseStep 8088005 = 1516501) B1516501
theorem B2017747 : Blo 1415527 2017747 := bstep (se 1 (by rfl) ⟨1513310, by rfl⟩ : syracuseStep 2017747 = 3026621) B3026621
theorem B2124257 : Blo 1415527 2124257 := bstep (se 2 (by rfl) ⟨796596, by rfl⟩ : syracuseStep 2124257 = 1593193) B1593193
theorem B2124275 : Blo 1415527 2124275 := bstep (se 1 (by rfl) ⟨1593206, by rfl⟩ : syracuseStep 2124275 = 3186413) B3186413
theorem B4540931 : Blo 1415527 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B4778513 : Blo 1415527 4778513 := bstep (se 2 (by rfl) ⟨1791942, by rfl⟩ : syracuseStep 4778513 = 3583885) B3583885
theorem B2124305 : Blo 1415527 2124305 := bstep (se 2 (by rfl) ⟨796614, by rfl⟩ : syracuseStep 2124305 = 1593229) B1593229
theorem B2124323 : Blo 1415527 2124323 := bstep (se 1 (by rfl) ⟨1593242, by rfl⟩ : syracuseStep 2124323 = 3186485) B3186485
theorem B1436195 : Blo 1415527 1436195 := bstep (se 1 (by rfl) ⟨1077146, by rfl⟩ : syracuseStep 1436195 = 2154293) B2154293
theorem B2124353 : Blo 1415527 2124353 := bstep (se 2 (by rfl) ⟨796632, by rfl⟩ : syracuseStep 2124353 = 1593265) B1593265
theorem B4033091 : Blo 1415527 4033091 := bstep (se 1 (by rfl) ⟨3024818, by rfl⟩ : syracuseStep 4033091 = 6049637) B6049637
theorem B3189329 : Blo 1415527 3189329 := bstep (se 2 (by rfl) ⟨1195998, by rfl⟩ : syracuseStep 3189329 = 2391997) B2391997
theorem B2124371 : Blo 1415527 2124371 := bstep (se 1 (by rfl) ⟨1593278, by rfl⟩ : syracuseStep 2124371 = 3186557) B3186557
theorem B3189347 : Blo 1415527 3189347 := bstep (se 1 (by rfl) ⟨2392010, by rfl⟩ : syracuseStep 3189347 = 4784021) B4784021
theorem B2124401 : Blo 1415527 2124401 := bstep (se 2 (by rfl) ⟨796650, by rfl⟩ : syracuseStep 2124401 = 1593301) B1593301
theorem B2124419 : Blo 1415527 2124419 := bstep (se 1 (by rfl) ⟨1593314, by rfl⟩ : syracuseStep 2124419 = 3186629) B3186629
theorem B2124449 : Blo 1415527 2124449 := bstep (se 2 (by rfl) ⟨796668, by rfl⟩ : syracuseStep 2124449 = 1593337) B1593337
theorem B8063651 : Blo 1415527 8063651 := bstep (se 1 (by rfl) ⟨6047738, by rfl⟩ : syracuseStep 8063651 = 12095477) B12095477
theorem B2689699 : Blo 1415527 2689699 := bstep (se 1 (by rfl) ⟨2017274, by rfl⟩ : syracuseStep 2689699 = 4034549) B4034549
theorem B2124467 : Blo 1415527 2124467 := bstep (se 1 (by rfl) ⟨1593350, by rfl⟩ : syracuseStep 2124467 = 3186701) B3186701
theorem B4541123 : Blo 1415527 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B2124497 : Blo 1415527 2124497 := bstep (se 2 (by rfl) ⟨796686, by rfl⟩ : syracuseStep 2124497 = 1593373) B1593373
theorem B5376739 : Blo 1415527 5376739 := bstep (se 1 (by rfl) ⟨4032554, by rfl⟩ : syracuseStep 5376739 = 8065109) B8065109
theorem B2124515 : Blo 1415527 2124515 := bstep (se 1 (by rfl) ⟨1593386, by rfl⟩ : syracuseStep 2124515 = 3186773) B3186773
theorem B2124545 : Blo 1415527 2124545 := bstep (se 2 (by rfl) ⟨796704, by rfl⟩ : syracuseStep 2124545 = 1593409) B1593409
theorem B2124563 : Blo 1415527 2124563 := bstep (se 1 (by rfl) ⟨1593422, by rfl⟩ : syracuseStep 2124563 = 3186845) B3186845
theorem B3402545 : Blo 1415527 3402545 := bstep (se 2 (by rfl) ⟨1275954, by rfl⟩ : syracuseStep 3402545 = 2551909) B2551909
theorem B2124593 : Blo 1415527 2124593 := bstep (se 2 (by rfl) ⟨796722, by rfl⟩ : syracuseStep 2124593 = 1593445) B1593445
theorem B2124611 : Blo 1415527 2124611 := bstep (se 1 (by rfl) ⟨1593458, by rfl⟩ : syracuseStep 2124611 = 3186917) B3186917
theorem B2124641 : Blo 1415527 2124641 := bstep (se 2 (by rfl) ⟨796740, by rfl⟩ : syracuseStep 2124641 = 1593481) B1593481
theorem B7170929 : Blo 1415527 7170929 := bstep (se 2 (by rfl) ⟨2689098, by rfl⟩ : syracuseStep 7170929 = 5378197) B5378197
theorem B2124659 : Blo 1415527 2124659 := bstep (se 1 (by rfl) ⟨1593494, by rfl⟩ : syracuseStep 2124659 = 3186989) B3186989
theorem B4033421 : Blo 1415527 4033421 := bstep (se 3 (by rfl) ⟨756266, by rfl⟩ : syracuseStep 4033421 = 1512533) B1512533
theorem B82848653 : Blo 1415527 82848653 := bstep (se 3 (by rfl) ⟨15534122, by rfl⟩ : syracuseStep 82848653 = 31068245) B31068245
theorem B2124689 : Blo 1415527 2124689 := bstep (se 2 (by rfl) ⟨796758, by rfl⟩ : syracuseStep 2124689 = 1593517) B1593517
theorem B2124707 : Blo 1415527 2124707 := bstep (se 1 (by rfl) ⟨1593530, by rfl⟩ : syracuseStep 2124707 = 3187061) B3187061
theorem B2124737 : Blo 1415527 2124737 := bstep (se 2 (by rfl) ⟨796776, by rfl⟩ : syracuseStep 2124737 = 1593553) B1593553
theorem B12929989 : Blo 1415527 12929989 := bstep (se 4 (by rfl) ⟨1212186, by rfl⟩ : syracuseStep 12929989 = 2424373) B2424373
theorem B4033489 : Blo 1415527 4033489 := bstep (se 2 (by rfl) ⟨1512558, by rfl⟩ : syracuseStep 4033489 = 3025117) B3025117
theorem B2124755 : Blo 1415527 2124755 := bstep (se 1 (by rfl) ⟨1593566, by rfl⟩ : syracuseStep 2124755 = 3187133) B3187133
theorem B2124785 : Blo 1415527 2124785 := bstep (se 2 (by rfl) ⟨796794, by rfl⟩ : syracuseStep 2124785 = 1593589) B1593589
theorem B2018305 : Blo 1415527 2018305 := bstep (se 2 (by rfl) ⟨756864, by rfl⟩ : syracuseStep 2018305 = 1513729) B1513729
theorem B2124803 : Blo 1415527 2124803 := bstep (se 1 (by rfl) ⟨1593602, by rfl⟩ : syracuseStep 2124803 = 3187205) B3187205
theorem B3025937 : Blo 1415527 3025937 := bstep (se 2 (by rfl) ⟨1134726, by rfl⟩ : syracuseStep 3025937 = 2269453) B2269453
theorem B2124833 : Blo 1415527 2124833 := bstep (se 2 (by rfl) ⟨796812, by rfl⟩ : syracuseStep 2124833 = 1593625) B1593625
theorem B4779053 : Blo 1415527 4779053 := bstep (se 3 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 4779053 = 1792145) B1792145
theorem B2124851 : Blo 1415527 2124851 := bstep (se 1 (by rfl) ⟨1593638, by rfl⟩ : syracuseStep 2124851 = 3187277) B3187277
theorem B2124881 : Blo 1415527 2124881 := bstep (se 2 (by rfl) ⟨796830, by rfl⟩ : syracuseStep 2124881 = 1593661) B1593661
theorem B3583075 : Blo 1415527 3583075 := bstep (se 1 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 3583075 = 5374613) B5374613
theorem B4779107 : Blo 1415527 4779107 := bstep (se 1 (by rfl) ⟨3584330, by rfl⟩ : syracuseStep 4779107 = 7168661) B7168661
theorem B2124899 : Blo 1415527 2124899 := bstep (se 1 (by rfl) ⟨1593674, by rfl⟩ : syracuseStep 2124899 = 3187349) B3187349
theorem B2690147 : Blo 1415527 2690147 := bstep (se 1 (by rfl) ⟨2017610, by rfl⟩ : syracuseStep 2690147 = 4035221) B4035221
theorem B2124929 : Blo 1415527 2124929 := bstep (se 2 (by rfl) ⟨796848, by rfl⟩ : syracuseStep 2124929 = 1593697) B1593697
theorem B2124947 : Blo 1415527 2124947 := bstep (se 1 (by rfl) ⟨1593710, by rfl⟩ : syracuseStep 2124947 = 3187421) B3187421
theorem B2124977 : Blo 1415527 2124977 := bstep (se 2 (by rfl) ⟨796866, by rfl⟩ : syracuseStep 2124977 = 1593733) B1593733
theorem B2124995 : Blo 1415527 2124995 := bstep (se 1 (by rfl) ⟨1593746, by rfl⟩ : syracuseStep 2124995 = 3187493) B3187493
theorem B9071813 : Blo 1415527 9071813 := bstep (se 4 (by rfl) ⟨850482, by rfl⟩ : syracuseStep 9071813 = 1700965) B1700965
theorem B2125025 : Blo 1415527 2125025 := bstep (se 2 (by rfl) ⟨796884, by rfl⟩ : syracuseStep 2125025 = 1593769) B1593769
theorem B4033763 : Blo 1415527 4033763 := bstep (se 1 (by rfl) ⟨3025322, by rfl⟩ : syracuseStep 4033763 = 6050645) B6050645
theorem B3583217 : Blo 1415527 3583217 := bstep (se 2 (by rfl) ⟨1343706, by rfl⟩ : syracuseStep 3583217 = 2687413) B2687413
theorem B1592563 : Blo 1415527 1592563 := bstep (se 1 (by rfl) ⟨1194422, by rfl⟩ : syracuseStep 1592563 = 2388845) B2388845
theorem B2125043 : Blo 1415527 2125043 := bstep (se 1 (by rfl) ⟨1593782, by rfl⟩ : syracuseStep 2125043 = 3187565) B3187565
theorem B2125073 : Blo 1415527 2125073 := bstep (se 2 (by rfl) ⟨796902, by rfl⟩ : syracuseStep 2125073 = 1593805) B1593805
theorem B2125091 : Blo 1415527 2125091 := bstep (se 1 (by rfl) ⟨1593818, by rfl⟩ : syracuseStep 2125091 = 3187637) B3187637
theorem B2125121 : Blo 1415527 2125121 := bstep (se 2 (by rfl) ⟨796920, by rfl⟩ : syracuseStep 2125121 = 1593841) B1593841
theorem B3403075 : Blo 1415527 3403075 := bstep (se 1 (by rfl) ⟨2552306, by rfl⟩ : syracuseStep 3403075 = 5104613) B5104613
theorem B2125139 : Blo 1415527 2125139 := bstep (se 1 (by rfl) ⟨1593854, by rfl⟩ : syracuseStep 2125139 = 3187709) B3187709
theorem B4779377 : Blo 1415527 4779377 := bstep (se 2 (by rfl) ⟨1792266, by rfl⟩ : syracuseStep 4779377 = 3584533) B3584533
theorem B2125169 : Blo 1415527 2125169 := bstep (se 2 (by rfl) ⟨796938, by rfl⟩ : syracuseStep 2125169 = 1593877) B1593877
theorem B1592707 : Blo 1415527 1592707 := bstep (se 1 (by rfl) ⟨1194530, by rfl⟩ : syracuseStep 1592707 = 2389061) B2389061
theorem B2125187 : Blo 1415527 2125187 := bstep (se 1 (by rfl) ⟨1593890, by rfl⟩ : syracuseStep 2125187 = 3187781) B3187781
theorem B2690435 : Blo 1415527 2690435 := bstep (se 1 (by rfl) ⟨2017826, by rfl⟩ : syracuseStep 2690435 = 4035653) B4035653
theorem B8072581 : Blo 1415527 8072581 := bstep (se 4 (by rfl) ⟨756804, by rfl⟩ : syracuseStep 8072581 = 1513609) B1513609
theorem B2125217 : Blo 1415527 2125217 := bstep (se 2 (by rfl) ⟨796956, by rfl⟩ : syracuseStep 2125217 = 1593913) B1593913
theorem B3231139 : Blo 1415527 3231139 := bstep (se 1 (by rfl) ⟨2423354, by rfl⟩ : syracuseStep 3231139 = 4846709) B4846709
theorem B2125235 : Blo 1415527 2125235 := bstep (se 1 (by rfl) ⟨1593926, by rfl⟩ : syracuseStep 2125235 = 3187853) B3187853
theorem B2125265 : Blo 1415527 2125265 := bstep (se 2 (by rfl) ⟨796974, by rfl⟩ : syracuseStep 2125265 = 1593949) B1593949
theorem B2125283 : Blo 1415527 2125283 := bstep (se 1 (by rfl) ⟨1593962, by rfl⟩ : syracuseStep 2125283 = 3187925) B3187925
theorem B2125313 : Blo 1415527 2125313 := bstep (se 2 (by rfl) ⟨796992, by rfl⟩ : syracuseStep 2125313 = 1593985) B1593985
theorem B1592851 : Blo 1415527 1592851 := bstep (se 1 (by rfl) ⟨1194638, by rfl⟩ : syracuseStep 1592851 = 2389277) B2389277
theorem B2125331 : Blo 1415527 2125331 := bstep (se 1 (by rfl) ⟨1593998, by rfl⟩ : syracuseStep 2125331 = 3187997) B3187997
theorem B2125361 : Blo 1415527 2125361 := bstep (se 2 (by rfl) ⟨797010, by rfl⟩ : syracuseStep 2125361 = 1594021) B1594021
theorem B2125379 : Blo 1415527 2125379 := bstep (se 1 (by rfl) ⟨1594034, by rfl⟩ : syracuseStep 2125379 = 3188069) B3188069
theorem B2125409 : Blo 1415527 2125409 := bstep (se 2 (by rfl) ⟨797028, by rfl⟩ : syracuseStep 2125409 = 1594057) B1594057
theorem B6049379 : Blo 1415527 6049379 := bstep (se 1 (by rfl) ⟨4537034, by rfl⟩ : syracuseStep 6049379 = 9074069) B9074069
theorem B2125427 : Blo 1415527 2125427 := bstep (se 1 (by rfl) ⟨1594070, by rfl⟩ : syracuseStep 2125427 = 3188141) B3188141
theorem B2125457 : Blo 1415527 2125457 := bstep (se 2 (by rfl) ⟨797046, by rfl⟩ : syracuseStep 2125457 = 1594093) B1594093
theorem B1592995 : Blo 1415527 1592995 := bstep (se 1 (by rfl) ⟨1194746, by rfl⟩ : syracuseStep 1592995 = 2389493) B2389493
theorem B2125475 : Blo 1415527 2125475 := bstep (se 1 (by rfl) ⟨1594106, by rfl⟩ : syracuseStep 2125475 = 3188213) B3188213
theorem B2125505 : Blo 1415527 2125505 := bstep (se 2 (by rfl) ⟨797064, by rfl⟩ : syracuseStep 2125505 = 1594129) B1594129
theorem B2125523 : Blo 1415527 2125523 := bstep (se 1 (by rfl) ⟨1594142, by rfl⟩ : syracuseStep 2125523 = 3188285) B3188285
theorem B12095203 : Blo 1415527 12095203 := bstep (se 1 (by rfl) ⟨9071402, by rfl⟩ : syracuseStep 12095203 = 18142805) B18142805
theorem B5746403 : Blo 1415527 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B2125553 : Blo 1415527 2125553 := bstep (se 2 (by rfl) ⟨797082, by rfl⟩ : syracuseStep 2125553 = 1594165) B1594165
theorem B2043649 : Blo 1415527 2043649 := bstep (se 2 (by rfl) ⟨766368, by rfl⟩ : syracuseStep 2043649 = 1532737) B1532737
theorem B2125571 : Blo 1415527 2125571 := bstep (se 1 (by rfl) ⟨1594178, by rfl⟩ : syracuseStep 2125571 = 3188357) B3188357
theorem B2125601 : Blo 1415527 2125601 := bstep (se 2 (by rfl) ⟨797100, by rfl⟩ : syracuseStep 2125601 = 1594201) B1594201
theorem B1593139 : Blo 1415527 1593139 := bstep (se 1 (by rfl) ⟨1194854, by rfl⟩ : syracuseStep 1593139 = 2389709) B2389709
theorem B2125619 : Blo 1415527 2125619 := bstep (se 1 (by rfl) ⟨1594214, by rfl⟩ : syracuseStep 2125619 = 3188429) B3188429
theorem B15314741 : Blo 1415527 15314741 := bstep (se 5 (by rfl) ⟨717878, by rfl⟩ : syracuseStep 15314741 = 1435757) B1435757
theorem B2125649 : Blo 1415527 2125649 := bstep (se 2 (by rfl) ⟨797118, by rfl⟩ : syracuseStep 2125649 = 1594237) B1594237
theorem B2125667 : Blo 1415527 2125667 := bstep (se 1 (by rfl) ⟨1594250, by rfl⟩ : syracuseStep 2125667 = 3188501) B3188501
theorem B3026801 : Blo 1415527 3026801 := bstep (se 2 (by rfl) ⟨1135050, by rfl⟩ : syracuseStep 3026801 = 2270101) B2270101
theorem B2125697 : Blo 1415527 2125697 := bstep (se 2 (by rfl) ⟨797136, by rfl⟩ : syracuseStep 2125697 = 1594273) B1594273
theorem B4779917 : Blo 1415527 4779917 := bstep (se 3 (by rfl) ⟨896234, by rfl⟩ : syracuseStep 4779917 = 1792469) B1792469
theorem B2125715 : Blo 1415527 2125715 := bstep (se 1 (by rfl) ⟨1594286, by rfl⟩ : syracuseStep 2125715 = 3188573) B3188573
theorem B2125745 : Blo 1415527 2125745 := bstep (se 2 (by rfl) ⟨797154, by rfl⟩ : syracuseStep 2125745 = 1594309) B1594309
theorem B1593283 : Blo 1415527 1593283 := bstep (se 1 (by rfl) ⟨1194962, by rfl⟩ : syracuseStep 1593283 = 2389925) B2389925
theorem B4779971 : Blo 1415527 4779971 := bstep (se 1 (by rfl) ⟨3584978, by rfl⟩ : syracuseStep 4779971 = 7169957) B7169957
theorem B2125763 : Blo 1415527 2125763 := bstep (se 1 (by rfl) ⟨1594322, by rfl⟩ : syracuseStep 2125763 = 3188645) B3188645
theorem B2125793 : Blo 1415527 2125793 := bstep (se 2 (by rfl) ⟨797172, by rfl⟩ : syracuseStep 2125793 = 1594345) B1594345
theorem B2125811 : Blo 1415527 2125811 := bstep (se 1 (by rfl) ⟨1594358, by rfl⟩ : syracuseStep 2125811 = 3188717) B3188717
theorem B2125841 : Blo 1415527 2125841 := bstep (se 2 (by rfl) ⟨797190, by rfl⟩ : syracuseStep 2125841 = 1594381) B1594381
theorem B2125859 : Blo 1415527 2125859 := bstep (se 1 (by rfl) ⟨1594394, by rfl⟩ : syracuseStep 2125859 = 3188789) B3188789
theorem B4034605 : Blo 1415527 4034605 := bstep (se 3 (by rfl) ⟨756488, by rfl⟩ : syracuseStep 4034605 = 1512977) B1512977
theorem B2125889 : Blo 1415527 2125889 := bstep (se 2 (by rfl) ⟨797208, by rfl⟩ : syracuseStep 2125889 = 1594417) B1594417
theorem B1593427 : Blo 1415527 1593427 := bstep (se 1 (by rfl) ⟨1195070, by rfl⟩ : syracuseStep 1593427 = 2390141) B2390141
theorem B2125907 : Blo 1415527 2125907 := bstep (se 1 (by rfl) ⟨1594430, by rfl⟩ : syracuseStep 2125907 = 3188861) B3188861
theorem B2125937 : Blo 1415527 2125937 := bstep (se 2 (by rfl) ⟨797226, by rfl⟩ : syracuseStep 2125937 = 1594453) B1594453
theorem B2125955 : Blo 1415527 2125955 := bstep (se 1 (by rfl) ⟨1594466, by rfl⟩ : syracuseStep 2125955 = 3188933) B3188933
theorem B2125985 : Blo 1415527 2125985 := bstep (se 2 (by rfl) ⟨797244, by rfl⟩ : syracuseStep 2125985 = 1594489) B1594489
theorem B2126003 : Blo 1415527 2126003 := bstep (se 1 (by rfl) ⟨1594502, by rfl⟩ : syracuseStep 2126003 = 3189005) B3189005
theorem B4034765 : Blo 1415527 4034765 := bstep (se 3 (by rfl) ⟨756518, by rfl⟩ : syracuseStep 4034765 = 1513037) B1513037
theorem B3584209 : Blo 1415527 3584209 := bstep (se 2 (by rfl) ⟨1344078, by rfl⟩ : syracuseStep 3584209 = 2688157) B2688157
theorem B4780241 : Blo 1415527 4780241 := bstep (se 2 (by rfl) ⟨1792590, by rfl⟩ : syracuseStep 4780241 = 3585181) B3585181
theorem B2126033 : Blo 1415527 2126033 := bstep (se 2 (by rfl) ⟨797262, by rfl⟩ : syracuseStep 2126033 = 1594525) B1594525
theorem B1593571 : Blo 1415527 1593571 := bstep (se 1 (by rfl) ⟨1195178, by rfl⟩ : syracuseStep 1593571 = 2390357) B2390357
theorem B2126051 : Blo 1415527 2126051 := bstep (se 1 (by rfl) ⟨1594538, by rfl⟩ : syracuseStep 2126051 = 3189077) B3189077
theorem B2126081 : Blo 1415527 2126081 := bstep (se 2 (by rfl) ⟨797280, by rfl⟩ : syracuseStep 2126081 = 1594561) B1594561
theorem B2126099 : Blo 1415527 2126099 := bstep (se 1 (by rfl) ⟨1594574, by rfl⟩ : syracuseStep 2126099 = 3189149) B3189149
theorem B6803747 : Blo 1415527 6803747 := bstep (se 1 (by rfl) ⟨5102810, by rfl⟩ : syracuseStep 6803747 = 10205621) B10205621
theorem B7172387 : Blo 1415527 7172387 := bstep (se 1 (by rfl) ⟨5379290, by rfl⟩ : syracuseStep 7172387 = 10758581) B10758581
theorem B2126129 : Blo 1415527 2126129 := bstep (se 2 (by rfl) ⟨797298, by rfl⟩ : syracuseStep 2126129 = 1594597) B1594597
theorem B2126147 : Blo 1415527 2126147 := bstep (se 1 (by rfl) ⟨1594610, by rfl⟩ : syracuseStep 2126147 = 3189221) B3189221
theorem B2126177 : Blo 1415527 2126177 := bstep (se 2 (by rfl) ⟨797316, by rfl⟩ : syracuseStep 2126177 = 1594633) B1594633
theorem B1593715 : Blo 1415527 1593715 := bstep (se 1 (by rfl) ⟨1195286, by rfl⟩ : syracuseStep 1593715 = 2390573) B2390573
theorem B2126195 : Blo 1415527 2126195 := bstep (se 1 (by rfl) ⟨1594646, by rfl⟩ : syracuseStep 2126195 = 3189293) B3189293
theorem B4034947 : Blo 1415527 4034947 := bstep (se 1 (by rfl) ⟨3026210, by rfl⟩ : syracuseStep 4034947 = 6052421) B6052421
theorem B2126225 : Blo 1415527 2126225 := bstep (se 2 (by rfl) ⟨797334, by rfl⟩ : syracuseStep 2126225 = 1594669) B1594669
theorem B2126243 : Blo 1415527 2126243 := bstep (se 1 (by rfl) ⟨1594682, by rfl⟩ : syracuseStep 2126243 = 3189365) B3189365
theorem B2126273 : Blo 1415527 2126273 := bstep (se 2 (by rfl) ⟨797352, by rfl⟩ : syracuseStep 2126273 = 1594705) B1594705
theorem B1511875 : Blo 1415527 1511875 := bstep (se 1 (by rfl) ⟨1133906, by rfl⟩ : syracuseStep 1511875 = 2267813) B2267813
theorem B2126291 : Blo 1415527 2126291 := bstep (se 1 (by rfl) ⟨1594718, by rfl⟩ : syracuseStep 2126291 = 3189437) B3189437
theorem B6803939 : Blo 1415527 6803939 := bstep (se 1 (by rfl) ⟨5102954, by rfl⟩ : syracuseStep 6803939 = 10205909) B10205909
theorem B3584483 : Blo 1415527 3584483 := bstep (se 1 (by rfl) ⟨2688362, by rfl⟩ : syracuseStep 3584483 = 5376725) B5376725
theorem B1593859 : Blo 1415527 1593859 := bstep (se 1 (by rfl) ⟨1195394, by rfl⟩ : syracuseStep 1593859 = 2390789) B2390789
theorem B3404305 : Blo 1415527 3404305 := bstep (se 2 (by rfl) ⟨1276614, by rfl⟩ : syracuseStep 3404305 = 2553229) B2553229
theorem B9826915 : Blo 1415527 9826915 := bstep (se 1 (by rfl) ⟨7370186, by rfl⟩ : syracuseStep 9826915 = 14740373) B14740373
theorem B1594003 : Blo 1415527 1594003 := bstep (se 1 (by rfl) ⟨1195502, by rfl⟩ : syracuseStep 1594003 = 2391005) B2391005
theorem B3584675 : Blo 1415527 3584675 := bstep (se 1 (by rfl) ⟨2688506, by rfl⟩ : syracuseStep 3584675 = 5377013) B5377013
theorem B4780781 : Blo 1415527 4780781 := bstep (se 3 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 4780781 = 1792793) B1792793
theorem B11481841 : Blo 1415527 11481841 := bstep (se 2 (by rfl) ⟨4305690, by rfl⟩ : syracuseStep 11481841 = 8611381) B8611381
theorem B2388737 : Blo 1415527 2388737 := bstep (se 2 (by rfl) ⟨895776, by rfl⟩ : syracuseStep 2388737 = 1791553) B1791553
theorem B7656227 : Blo 1415527 7656227 := bstep (se 1 (by rfl) ⟨5742170, by rfl⟩ : syracuseStep 7656227 = 11484341) B11484341
theorem B4780835 : Blo 1415527 4780835 := bstep (se 1 (by rfl) ⟨3585626, by rfl⟩ : syracuseStep 4780835 = 7171253) B7171253
theorem B1594147 : Blo 1415527 1594147 := bstep (se 1 (by rfl) ⟨1195610, by rfl⟩ : syracuseStep 1594147 = 2391221) B2391221
theorem B6050609 : Blo 1415527 6050609 := bstep (se 2 (by rfl) ⟨2268978, by rfl⟩ : syracuseStep 6050609 = 4537957) B4537957
theorem B6804323 : Blo 1415527 6804323 := bstep (se 1 (by rfl) ⟨5103242, by rfl⟩ : syracuseStep 6804323 = 10206485) B10206485
theorem B1512307 : Blo 1415527 1512307 := bstep (se 1 (by rfl) ⟨1134230, by rfl⟩ : syracuseStep 1512307 = 2268461) B2268461
theorem B2388865 : Blo 1415527 2388865 := bstep (se 2 (by rfl) ⟨895824, by rfl⟩ : syracuseStep 2388865 = 1791649) B1791649
theorem B5378957 : Blo 1415527 5378957 := bstep (se 3 (by rfl) ⟨1008554, by rfl⟩ : syracuseStep 5378957 = 2017109) B2017109
theorem B2388899 : Blo 1415527 2388899 := bstep (se 1 (by rfl) ⟨1791674, by rfl⟩ : syracuseStep 2388899 = 3583349) B3583349
theorem B1594291 : Blo 1415527 1594291 := bstep (se 1 (by rfl) ⟨1195718, by rfl⟩ : syracuseStep 1594291 = 2391437) B2391437
theorem B2389027 : Blo 1415527 2389027 := bstep (se 1 (by rfl) ⟨1791770, by rfl⟩ : syracuseStep 2389027 = 3583541) B3583541
theorem B2184227 : Blo 1415527 2184227 := bstep (se 1 (by rfl) ⟨1638170, by rfl⟩ : syracuseStep 2184227 = 3276341) B3276341
theorem B4781105 : Blo 1415527 4781105 := bstep (se 2 (by rfl) ⟨1792914, by rfl⟩ : syracuseStep 4781105 = 3585829) B3585829
theorem B1594435 : Blo 1415527 1594435 := bstep (se 1 (by rfl) ⟨1195826, by rfl⟩ : syracuseStep 1594435 = 2391653) B2391653
theorem B7173197 : Blo 1415527 7173197 := bstep (se 3 (by rfl) ⟨1344974, by rfl⟩ : syracuseStep 7173197 = 2689949) B2689949
theorem B9196685 : Blo 1415527 9196685 := bstep (se 3 (by rfl) ⟨1724378, by rfl⟩ : syracuseStep 9196685 = 3448757) B3448757
theorem B2389169 : Blo 1415527 2389169 := bstep (se 2 (by rfl) ⟨895938, by rfl⟩ : syracuseStep 2389169 = 1791877) B1791877
theorem B1594579 : Blo 1415527 1594579 := bstep (se 1 (by rfl) ⟨1195934, by rfl⟩ : syracuseStep 1594579 = 2391869) B2391869
theorem B2872579 : Blo 1415527 2872579 := bstep (se 1 (by rfl) ⟨2154434, by rfl⟩ : syracuseStep 2872579 = 4308869) B4308869
theorem B2389297 : Blo 1415527 2389297 := bstep (se 2 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 2389297 = 1791973) B1791973
theorem B2389331 : Blo 1415527 2389331 := bstep (se 1 (by rfl) ⟨1791998, by rfl⟩ : syracuseStep 2389331 = 3583997) B3583997
theorem B4535651 : Blo 1415527 4535651 := bstep (se 1 (by rfl) ⟨3401738, by rfl⟩ : syracuseStep 4535651 = 6803477) B6803477
theorem B2389459 : Blo 1415527 2389459 := bstep (se 1 (by rfl) ⟨1792094, by rfl⟩ : syracuseStep 2389459 = 3584189) B3584189
theorem B1914403 : Blo 1415527 1914403 := bstep (se 1 (by rfl) ⟨1435802, by rfl⟩ : syracuseStep 1914403 = 2871605) B2871605
theorem B1701427 : Blo 1415527 1701427 := bstep (se 1 (by rfl) ⟨1276070, by rfl⟩ : syracuseStep 1701427 = 2552141) B2552141
theorem B4781645 : Blo 1415527 4781645 := bstep (se 3 (by rfl) ⟨896558, by rfl⟩ : syracuseStep 4781645 = 1793117) B1793117
theorem B3585617 : Blo 1415527 3585617 := bstep (se 2 (by rfl) ⟨1344606, by rfl⟩ : syracuseStep 3585617 = 2689213) B2689213
theorem B2389601 : Blo 1415527 2389601 := bstep (se 2 (by rfl) ⟨896100, by rfl⟩ : syracuseStep 2389601 = 1792201) B1792201
theorem B3585667 : Blo 1415527 3585667 := bstep (se 1 (by rfl) ⟨2689250, by rfl⟩ : syracuseStep 3585667 = 5378501) B5378501
theorem B4781699 : Blo 1415527 4781699 := bstep (se 1 (by rfl) ⟨3586274, by rfl⟩ : syracuseStep 4781699 = 7172549) B7172549
theorem B2389729 : Blo 1415527 2389729 := bstep (se 2 (by rfl) ⟨896148, by rfl⟩ : syracuseStep 2389729 = 1792297) B1792297
theorem B1791715 : Blo 1415527 1791715 := bstep (se 1 (by rfl) ⟨1343786, by rfl⟩ : syracuseStep 1791715 = 2687573) B2687573
theorem B4036337 : Blo 1415527 4036337 := bstep (se 2 (by rfl) ⟨1513626, by rfl⟩ : syracuseStep 4036337 = 3027253) B3027253
theorem B2389763 : Blo 1415527 2389763 := bstep (se 1 (by rfl) ⟨1792322, by rfl⟩ : syracuseStep 2389763 = 3584645) B3584645
theorem B3585809 : Blo 1415527 3585809 := bstep (se 2 (by rfl) ⟨1344678, by rfl⟩ : syracuseStep 3585809 = 2689357) B2689357
theorem B1914689 : Blo 1415527 1914689 := bstep (se 2 (by rfl) ⟨718008, by rfl⟩ : syracuseStep 1914689 = 1436017) B1436017
theorem B1791811 : Blo 1415527 1791811 := bstep (se 1 (by rfl) ⟨1343858, by rfl⟩ : syracuseStep 1791811 = 2687717) B2687717
theorem B9074531 : Blo 1415527 9074531 := bstep (se 1 (by rfl) ⟨6805898, by rfl⟩ : syracuseStep 9074531 = 13611797) B13611797
theorem B2455427 : Blo 1415527 2455427 := bstep (se 1 (by rfl) ⟨1841570, by rfl⟩ : syracuseStep 2455427 = 3683141) B3683141
theorem B2389891 : Blo 1415527 2389891 := bstep (se 1 (by rfl) ⟨1792418, by rfl⟩ : syracuseStep 2389891 = 3584837) B3584837
theorem B4781969 : Blo 1415527 4781969 := bstep (se 2 (by rfl) ⟨1793238, by rfl⟩ : syracuseStep 4781969 = 3586477) B3586477
theorem B1660819 : Blo 1415527 1660819 := bstep (se 1 (by rfl) ⟨1245614, by rfl⟩ : syracuseStep 1660819 = 2491229) B2491229
theorem B1701811 : Blo 1415527 1701811 := bstep (se 1 (by rfl) ⟨1276358, by rfl⟩ : syracuseStep 1701811 = 2552717) B2552717
theorem B27211747 : Blo 1415527 27211747 := bstep (se 1 (by rfl) ⟨20408810, by rfl⟩ : syracuseStep 27211747 = 40817621) B40817621
theorem B8730595 : Blo 1415527 8730595 := bstep (se 1 (by rfl) ⟨6547946, by rfl⟩ : syracuseStep 8730595 = 13095893) B13095893
theorem B1914883 : Blo 1415527 1914883 := bstep (se 1 (by rfl) ⟨1436162, by rfl⟩ : syracuseStep 1914883 = 2872325) B2872325
theorem B2390033 : Blo 1415527 2390033 := bstep (se 2 (by rfl) ⟨896262, by rfl⟩ : syracuseStep 2390033 = 1792525) B1792525
theorem B7264333 : Blo 1415527 7264333 := bstep (se 3 (by rfl) ⟨1362062, by rfl⟩ : syracuseStep 7264333 = 2724125) B2724125
theorem B2300003 : Blo 1415527 2300003 := bstep (se 1 (by rfl) ⟨1725002, by rfl⟩ : syracuseStep 2300003 = 3450005) B3450005
theorem B1513571 : Blo 1415527 1513571 := bstep (se 1 (by rfl) ⟨1135178, by rfl⟩ : syracuseStep 1513571 = 2270357) B2270357
theorem B2390161 : Blo 1415527 2390161 := bstep (se 2 (by rfl) ⟨896310, by rfl⟩ : syracuseStep 2390161 = 1792621) B1792621
theorem B2554001 : Blo 1415527 2554001 := bstep (se 2 (by rfl) ⟨957750, by rfl⟩ : syracuseStep 2554001 = 1915501) B1915501
theorem B2390195 : Blo 1415527 2390195 := bstep (se 1 (by rfl) ⟨1792646, by rfl⟩ : syracuseStep 2390195 = 3585293) B3585293
theorem B2267441 : Blo 1415527 2267441 := bstep (se 2 (by rfl) ⟨850290, by rfl⟩ : syracuseStep 2267441 = 1700581) B1700581
theorem B1792307 : Blo 1415527 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B2390323 : Blo 1415527 2390323 := bstep (se 1 (by rfl) ⟨1792742, by rfl⟩ : syracuseStep 2390323 = 3585485) B3585485
theorem B2423137 : Blo 1415527 2423137 := bstep (se 2 (by rfl) ⟨908676, by rfl⟩ : syracuseStep 2423137 = 1817353) B1817353
theorem B3185009 : Blo 1415527 3185009 := bstep (se 2 (by rfl) ⟨1194378, by rfl⟩ : syracuseStep 3185009 = 2388757) B2388757
theorem B1415539 : Blo 1415527 1415539 := bstep (se 1 (by rfl) ⟨1061654, by rfl⟩ : syracuseStep 1415539 = 2123309) B2123309
theorem B1415555 : Blo 1415527 1415555 := bstep (se 1 (by rfl) ⟨1061666, by rfl⟩ : syracuseStep 1415555 = 2123333) B2123333
theorem B3185027 : Blo 1415527 3185027 := bstep (se 1 (by rfl) ⟨2388770, by rfl⟩ : syracuseStep 3185027 = 4777541) B4777541
theorem B1415571 : Blo 1415527 1415571 := bstep (se 1 (by rfl) ⟨1061678, by rfl⟩ : syracuseStep 1415571 = 2123357) B2123357
theorem B1415587 : Blo 1415527 1415587 := bstep (se 1 (by rfl) ⟨1061690, by rfl⟩ : syracuseStep 1415587 = 2123381) B2123381
theorem B4782509 : Blo 1415527 4782509 := bstep (se 3 (by rfl) ⟨896720, by rfl⟩ : syracuseStep 4782509 = 1793441) B1793441
theorem B6805937 : Blo 1415527 6805937 := bstep (se 2 (by rfl) ⟨2552226, by rfl⟩ : syracuseStep 6805937 = 5104453) B5104453
theorem B1415603 : Blo 1415527 1415603 := bstep (se 1 (by rfl) ⟨1061702, by rfl⟩ : syracuseStep 1415603 = 2123405) B2123405
theorem B2390465 : Blo 1415527 2390465 := bstep (se 2 (by rfl) ⟨896424, by rfl⟩ : syracuseStep 2390465 = 1792849) B1792849
theorem B1415619 : Blo 1415527 1415619 := bstep (se 1 (by rfl) ⟨1061714, by rfl⟩ : syracuseStep 1415619 = 2123429) B2123429
theorem B1415635 : Blo 1415527 1415635 := bstep (se 1 (by rfl) ⟨1061726, by rfl⟩ : syracuseStep 1415635 = 2123453) B2123453
theorem B1415651 : Blo 1415527 1415651 := bstep (se 1 (by rfl) ⟨1061738, by rfl⟩ : syracuseStep 1415651 = 2123477) B2123477
theorem B4782563 : Blo 1415527 4782563 := bstep (se 1 (by rfl) ⟨3586922, by rfl⟩ : syracuseStep 4782563 = 7173845) B7173845
theorem B1415667 : Blo 1415527 1415667 := bstep (se 1 (by rfl) ⟨1061750, by rfl⟩ : syracuseStep 1415667 = 2123501) B2123501
theorem B1415683 : Blo 1415527 1415683 := bstep (se 1 (by rfl) ⟨1061762, by rfl⟩ : syracuseStep 1415683 = 2123525) B2123525
theorem B1415699 : Blo 1415527 1415699 := bstep (se 1 (by rfl) ⟨1061774, by rfl⟩ : syracuseStep 1415699 = 2123549) B2123549
theorem B1415715 : Blo 1415527 1415715 := bstep (se 1 (by rfl) ⟨1061786, by rfl⟩ : syracuseStep 1415715 = 2123573) B2123573
theorem B4536881 : Blo 1415527 4536881 := bstep (se 2 (by rfl) ⟨1701330, by rfl⟩ : syracuseStep 4536881 = 3402661) B3402661
theorem B1415731 : Blo 1415527 1415731 := bstep (se 1 (by rfl) ⟨1061798, by rfl⟩ : syracuseStep 1415731 = 2123597) B2123597
theorem B2390593 : Blo 1415527 2390593 := bstep (se 2 (by rfl) ⟨896472, by rfl⟩ : syracuseStep 2390593 = 1792945) B1792945
theorem B1415747 : Blo 1415527 1415747 := bstep (se 1 (by rfl) ⟨1061810, by rfl⟩ : syracuseStep 1415747 = 2123621) B2123621
theorem B1415763 : Blo 1415527 1415763 := bstep (se 1 (by rfl) ⟨1061822, by rfl⟩ : syracuseStep 1415763 = 2123645) B2123645
theorem B1415779 : Blo 1415527 1415779 := bstep (se 1 (by rfl) ⟨1061834, by rfl⟩ : syracuseStep 1415779 = 2123669) B2123669
theorem B2390627 : Blo 1415527 2390627 := bstep (se 1 (by rfl) ⟨1792970, by rfl⟩ : syracuseStep 2390627 = 3585941) B3585941
theorem B1415795 : Blo 1415527 1415795 := bstep (se 1 (by rfl) ⟨1061846, by rfl⟩ : syracuseStep 1415795 = 2123693) B2123693
theorem B1415811 : Blo 1415527 1415811 := bstep (se 1 (by rfl) ⟨1061858, by rfl⟩ : syracuseStep 1415811 = 2123717) B2123717
theorem B3185297 : Blo 1415527 3185297 := bstep (se 2 (by rfl) ⟨1194486, by rfl⟩ : syracuseStep 3185297 = 2388973) B2388973
theorem B1415827 : Blo 1415527 1415827 := bstep (se 1 (by rfl) ⟨1061870, by rfl⟩ : syracuseStep 1415827 = 2123741) B2123741
theorem B3185315 : Blo 1415527 3185315 := bstep (se 1 (by rfl) ⟨2388986, by rfl⟩ : syracuseStep 3185315 = 4777973) B4777973
theorem B1415843 : Blo 1415527 1415843 := bstep (se 1 (by rfl) ⟨1061882, by rfl⟩ : syracuseStep 1415843 = 2123765) B2123765
theorem B1415859 : Blo 1415527 1415859 := bstep (se 1 (by rfl) ⟨1061894, by rfl⟩ : syracuseStep 1415859 = 2123789) B2123789
theorem B1415875 : Blo 1415527 1415875 := bstep (se 1 (by rfl) ⟨1061906, by rfl⟩ : syracuseStep 1415875 = 2123813) B2123813
theorem B1415891 : Blo 1415527 1415891 := bstep (se 1 (by rfl) ⟨1061918, by rfl⟩ : syracuseStep 1415891 = 2123837) B2123837
theorem B1415907 : Blo 1415527 1415907 := bstep (se 1 (by rfl) ⟨1061930, by rfl⟩ : syracuseStep 1415907 = 2123861) B2123861
theorem B2390755 : Blo 1415527 2390755 := bstep (se 1 (by rfl) ⟨1793066, by rfl⟩ : syracuseStep 2390755 = 3586133) B3586133
theorem B3586801 : Blo 1415527 3586801 := bstep (se 2 (by rfl) ⟨1345050, by rfl⟩ : syracuseStep 3586801 = 2690101) B2690101
theorem B4782833 : Blo 1415527 4782833 := bstep (se 2 (by rfl) ⟨1793562, by rfl⟩ : syracuseStep 4782833 = 3587125) B3587125
theorem B1415923 : Blo 1415527 1415923 := bstep (se 1 (by rfl) ⟨1061942, by rfl⟩ : syracuseStep 1415923 = 2123885) B2123885
theorem B1415939 : Blo 1415527 1415939 := bstep (se 1 (by rfl) ⟨1061954, by rfl⟩ : syracuseStep 1415939 = 2123909) B2123909
theorem B1415955 : Blo 1415527 1415955 := bstep (se 1 (by rfl) ⟨1061966, by rfl⟩ : syracuseStep 1415955 = 2123933) B2123933
theorem B1415971 : Blo 1415527 1415971 := bstep (se 1 (by rfl) ⟨1061978, by rfl⟩ : syracuseStep 1415971 = 2123957) B2123957
theorem B6806321 : Blo 1415527 6806321 := bstep (se 2 (by rfl) ⟨2552370, by rfl⟩ : syracuseStep 6806321 = 5104741) B5104741
theorem B1415987 : Blo 1415527 1415987 := bstep (se 1 (by rfl) ⟨1061990, by rfl⟩ : syracuseStep 1415987 = 2123981) B2123981
theorem B1416003 : Blo 1415527 1416003 := bstep (se 1 (by rfl) ⟨1062002, by rfl⟩ : syracuseStep 1416003 = 2124005) B2124005
theorem B4848461 : Blo 1415527 4848461 := bstep (se 3 (by rfl) ⟨909086, by rfl⟩ : syracuseStep 4848461 = 1818173) B1818173
theorem B1416019 : Blo 1415527 1416019 := bstep (se 1 (by rfl) ⟨1062014, by rfl⟩ : syracuseStep 1416019 = 2124029) B2124029
theorem B1416035 : Blo 1415527 1416035 := bstep (se 1 (by rfl) ⟨1062026, by rfl⟩ : syracuseStep 1416035 = 2124053) B2124053
theorem B2390897 : Blo 1415527 2390897 := bstep (se 2 (by rfl) ⟨896586, by rfl⟩ : syracuseStep 2390897 = 1793173) B1793173
theorem B1416051 : Blo 1415527 1416051 := bstep (se 1 (by rfl) ⟨1062038, by rfl⟩ : syracuseStep 1416051 = 2124077) B2124077
theorem B1416067 : Blo 1415527 1416067 := bstep (se 1 (by rfl) ⟨1062050, by rfl⟩ : syracuseStep 1416067 = 2124101) B2124101
theorem B1416083 : Blo 1415527 1416083 := bstep (se 1 (by rfl) ⟨1062062, by rfl⟩ : syracuseStep 1416083 = 2124125) B2124125
theorem B1416099 : Blo 1415527 1416099 := bstep (se 1 (by rfl) ⟨1062074, by rfl⟩ : syracuseStep 1416099 = 2124149) B2124149
theorem B3185585 : Blo 1415527 3185585 := bstep (se 2 (by rfl) ⟨1194594, by rfl⟩ : syracuseStep 3185585 = 2389189) B2389189
theorem B1416115 : Blo 1415527 1416115 := bstep (se 1 (by rfl) ⟨1062086, by rfl⟩ : syracuseStep 1416115 = 2124173) B2124173
theorem B3185603 : Blo 1415527 3185603 := bstep (se 1 (by rfl) ⟨2389202, by rfl⟩ : syracuseStep 3185603 = 4778405) B4778405
theorem B1416131 : Blo 1415527 1416131 := bstep (se 1 (by rfl) ⟨1062098, by rfl⟩ : syracuseStep 1416131 = 2124197) B2124197
theorem B1416147 : Blo 1415527 1416147 := bstep (se 1 (by rfl) ⟨1062110, by rfl⟩ : syracuseStep 1416147 = 2124221) B2124221
theorem B1416163 : Blo 1415527 1416163 := bstep (se 1 (by rfl) ⟨1062122, by rfl⟩ : syracuseStep 1416163 = 2124245) B2124245
theorem B2391025 : Blo 1415527 2391025 := bstep (se 2 (by rfl) ⟨896634, by rfl⟩ : syracuseStep 2391025 = 1793269) B1793269
theorem B1416179 : Blo 1415527 1416179 := bstep (se 1 (by rfl) ⟨1062134, by rfl⟩ : syracuseStep 1416179 = 2124269) B2124269
theorem B1793011 : Blo 1415527 1793011 := bstep (se 1 (by rfl) ⟨1344758, by rfl⟩ : syracuseStep 1793011 = 2689517) B2689517
theorem B1416195 : Blo 1415527 1416195 := bstep (se 1 (by rfl) ⟨1062146, by rfl⟩ : syracuseStep 1416195 = 2124293) B2124293
theorem B3587075 : Blo 1415527 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B1416211 : Blo 1415527 1416211 := bstep (se 1 (by rfl) ⟨1062158, by rfl⟩ : syracuseStep 1416211 = 2124317) B2124317
theorem B2391059 : Blo 1415527 2391059 := bstep (se 1 (by rfl) ⟨1793294, by rfl⟩ : syracuseStep 2391059 = 3586589) B3586589
theorem B1416227 : Blo 1415527 1416227 := bstep (se 1 (by rfl) ⟨1062170, by rfl⟩ : syracuseStep 1416227 = 2124341) B2124341
theorem B1416243 : Blo 1415527 1416243 := bstep (se 1 (by rfl) ⟨1062182, by rfl⟩ : syracuseStep 1416243 = 2124365) B2124365
theorem B1416259 : Blo 1415527 1416259 := bstep (se 1 (by rfl) ⟨1062194, by rfl⟩ : syracuseStep 1416259 = 2124389) B2124389
theorem B1416275 : Blo 1415527 1416275 := bstep (se 1 (by rfl) ⟨1062206, by rfl⟩ : syracuseStep 1416275 = 2124413) B2124413
theorem B1793107 : Blo 1415527 1793107 := bstep (se 1 (by rfl) ⟨1344830, by rfl⟩ : syracuseStep 1793107 = 2689661) B2689661
theorem B1416291 : Blo 1415527 1416291 := bstep (se 1 (by rfl) ⟨1062218, by rfl⟩ : syracuseStep 1416291 = 2124437) B2124437
theorem B1416307 : Blo 1415527 1416307 := bstep (se 1 (by rfl) ⟨1062230, by rfl⟩ : syracuseStep 1416307 = 2124461) B2124461
theorem B1416323 : Blo 1415527 1416323 := bstep (se 1 (by rfl) ⟨1062242, by rfl⟩ : syracuseStep 1416323 = 2124485) B2124485
theorem B3636355 : Blo 1415527 3636355 := bstep (se 1 (by rfl) ⟨2727266, by rfl⟩ : syracuseStep 3636355 = 5454533) B5454533
theorem B1416339 : Blo 1415527 1416339 := bstep (se 1 (by rfl) ⟨1062254, by rfl⟩ : syracuseStep 1416339 = 2124509) B2124509
theorem B2391187 : Blo 1415527 2391187 := bstep (se 1 (by rfl) ⟨1793390, by rfl⟩ : syracuseStep 2391187 = 3586781) B3586781
theorem B1416355 : Blo 1415527 1416355 := bstep (se 1 (by rfl) ⟨1062266, by rfl⟩ : syracuseStep 1416355 = 2124533) B2124533
theorem B9321649 : Blo 1415527 9321649 := bstep (se 2 (by rfl) ⟨3495618, by rfl⟩ : syracuseStep 9321649 = 6991237) B6991237
theorem B1416371 : Blo 1415527 1416371 := bstep (se 1 (by rfl) ⟨1062278, by rfl⟩ : syracuseStep 1416371 = 2124557) B2124557
theorem B1416387 : Blo 1415527 1416387 := bstep (se 1 (by rfl) ⟨1062290, by rfl⟩ : syracuseStep 1416387 = 2124581) B2124581
theorem B3587267 : Blo 1415527 3587267 := bstep (se 1 (by rfl) ⟨2690450, by rfl⟩ : syracuseStep 3587267 = 5380901) B5380901
theorem B6053069 : Blo 1415527 6053069 := bstep (se 3 (by rfl) ⟨1134950, by rfl⟩ : syracuseStep 6053069 = 2269901) B2269901
theorem B3185873 : Blo 1415527 3185873 := bstep (se 2 (by rfl) ⟨1194702, by rfl⟩ : syracuseStep 3185873 = 2389405) B2389405
theorem B1416403 : Blo 1415527 1416403 := bstep (se 1 (by rfl) ⟨1062302, by rfl⟩ : syracuseStep 1416403 = 2124605) B2124605
theorem B2424019 : Blo 1415527 2424019 := bstep (se 1 (by rfl) ⟨1818014, by rfl⟩ : syracuseStep 2424019 = 3636029) B3636029
theorem B7167203 : Blo 1415527 7167203 := bstep (se 1 (by rfl) ⟨5375402, by rfl⟩ : syracuseStep 7167203 = 10750805) B10750805
theorem B3185891 : Blo 1415527 3185891 := bstep (se 1 (by rfl) ⟨2389418, by rfl⟩ : syracuseStep 3185891 = 4778837) B4778837
theorem B29072611 : Blo 1415527 29072611 := bstep (se 1 (by rfl) ⟨21804458, by rfl⟩ : syracuseStep 29072611 = 43608917) B43608917
theorem B1416419 : Blo 1415527 1416419 := bstep (se 1 (by rfl) ⟨1062314, by rfl⟩ : syracuseStep 1416419 = 2124629) B2124629
theorem B1416435 : Blo 1415527 1416435 := bstep (se 1 (by rfl) ⟨1062326, by rfl⟩ : syracuseStep 1416435 = 2124653) B2124653
theorem B1416451 : Blo 1415527 1416451 := bstep (se 1 (by rfl) ⟨1062338, by rfl⟩ : syracuseStep 1416451 = 2124677) B2124677
theorem B4783373 : Blo 1415527 4783373 := bstep (se 3 (by rfl) ⟨896882, by rfl⟩ : syracuseStep 4783373 = 1793765) B1793765
theorem B1416467 : Blo 1415527 1416467 := bstep (se 1 (by rfl) ⟨1062350, by rfl⟩ : syracuseStep 1416467 = 2124701) B2124701
theorem B2391329 : Blo 1415527 2391329 := bstep (se 2 (by rfl) ⟨896748, by rfl⟩ : syracuseStep 2391329 = 1793497) B1793497
theorem B1416483 : Blo 1415527 1416483 := bstep (se 1 (by rfl) ⟨1062362, by rfl⟩ : syracuseStep 1416483 = 2124725) B2124725
theorem B1416499 : Blo 1415527 1416499 := bstep (se 1 (by rfl) ⟨1062374, by rfl⟩ : syracuseStep 1416499 = 2124749) B2124749
theorem B1416515 : Blo 1415527 1416515 := bstep (se 1 (by rfl) ⟨1062386, by rfl⟩ : syracuseStep 1416515 = 2124773) B2124773
theorem B4783427 : Blo 1415527 4783427 := bstep (se 1 (by rfl) ⟨3587570, by rfl⟩ : syracuseStep 4783427 = 7175141) B7175141
theorem B6806861 : Blo 1415527 6806861 := bstep (se 3 (by rfl) ⟨1276286, by rfl⟩ : syracuseStep 6806861 = 2552573) B2552573
theorem B1416531 : Blo 1415527 1416531 := bstep (se 1 (by rfl) ⟨1062398, by rfl⟩ : syracuseStep 1416531 = 2124797) B2124797
theorem B1416547 : Blo 1415527 1416547 := bstep (se 1 (by rfl) ⟨1062410, by rfl⟩ : syracuseStep 1416547 = 2124821) B2124821
theorem B1416563 : Blo 1415527 1416563 := bstep (se 1 (by rfl) ⟨1062422, by rfl⟩ : syracuseStep 1416563 = 2124845) B2124845
theorem B1416579 : Blo 1415527 1416579 := bstep (se 1 (by rfl) ⟨1062434, by rfl⟩ : syracuseStep 1416579 = 2124869) B2124869
theorem B4537741 : Blo 1415527 4537741 := bstep (se 3 (by rfl) ⟨850826, by rfl⟩ : syracuseStep 4537741 = 1701653) B1701653
theorem B1416595 : Blo 1415527 1416595 := bstep (se 1 (by rfl) ⟨1062446, by rfl⟩ : syracuseStep 1416595 = 2124893) B2124893
theorem B2391457 : Blo 1415527 2391457 := bstep (se 2 (by rfl) ⟨896796, by rfl⟩ : syracuseStep 2391457 = 1793593) B1793593
theorem B1416611 : Blo 1415527 1416611 := bstep (se 1 (by rfl) ⟨1062458, by rfl⟩ : syracuseStep 1416611 = 2124917) B2124917
theorem B1416627 : Blo 1415527 1416627 := bstep (se 1 (by rfl) ⟨1062470, by rfl⟩ : syracuseStep 1416627 = 2124941) B2124941
theorem B3448259 : Blo 1415527 3448259 := bstep (se 1 (by rfl) ⟨2586194, by rfl⟩ : syracuseStep 3448259 = 5172389) B5172389
theorem B1416643 : Blo 1415527 1416643 := bstep (se 1 (by rfl) ⟨1062482, by rfl⟩ : syracuseStep 1416643 = 2124965) B2124965
theorem B2391491 : Blo 1415527 2391491 := bstep (se 1 (by rfl) ⟨1793618, by rfl⟩ : syracuseStep 2391491 = 3587237) B3587237
theorem B1416659 : Blo 1415527 1416659 := bstep (se 1 (by rfl) ⟨1062494, by rfl⟩ : syracuseStep 1416659 = 2124989) B2124989
theorem B1416675 : Blo 1415527 1416675 := bstep (se 1 (by rfl) ⟨1062506, by rfl⟩ : syracuseStep 1416675 = 2125013) B2125013
theorem B16145891 : Blo 1415527 16145891 := bstep (se 1 (by rfl) ⟨12109418, by rfl⟩ : syracuseStep 16145891 = 24218837) B24218837
theorem B3186161 : Blo 1415527 3186161 := bstep (se 2 (by rfl) ⟨1194810, by rfl⟩ : syracuseStep 3186161 = 2389621) B2389621
theorem B1416691 : Blo 1415527 1416691 := bstep (se 1 (by rfl) ⟨1062518, by rfl⟩ : syracuseStep 1416691 = 2125037) B2125037
theorem B3186179 : Blo 1415527 3186179 := bstep (se 1 (by rfl) ⟨2389634, by rfl⟩ : syracuseStep 3186179 = 4779269) B4779269
theorem B1416707 : Blo 1415527 1416707 := bstep (se 1 (by rfl) ⟨1062530, by rfl⟩ : syracuseStep 1416707 = 2125061) B2125061
theorem B1416723 : Blo 1415527 1416723 := bstep (se 1 (by rfl) ⟨1062542, by rfl⟩ : syracuseStep 1416723 = 2125085) B2125085
theorem B1416739 : Blo 1415527 1416739 := bstep (se 1 (by rfl) ⟨1062554, by rfl⟩ : syracuseStep 1416739 = 2125109) B2125109
theorem B1416755 : Blo 1415527 1416755 := bstep (se 1 (by rfl) ⟨1062566, by rfl⟩ : syracuseStep 1416755 = 2125133) B2125133
theorem B1416771 : Blo 1415527 1416771 := bstep (se 1 (by rfl) ⟨1062578, by rfl⟩ : syracuseStep 1416771 = 2125157) B2125157
theorem B1793603 : Blo 1415527 1793603 := bstep (se 1 (by rfl) ⟨1345202, by rfl⟩ : syracuseStep 1793603 = 2690405) B2690405
theorem B2391619 : Blo 1415527 2391619 := bstep (se 1 (by rfl) ⟨1793714, by rfl⟩ : syracuseStep 2391619 = 3587429) B3587429
theorem B8289869 : Blo 1415527 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B4783697 : Blo 1415527 4783697 := bstep (se 2 (by rfl) ⟨1793886, by rfl⟩ : syracuseStep 4783697 = 3587773) B3587773
theorem B1416787 : Blo 1415527 1416787 := bstep (se 1 (by rfl) ⟨1062590, by rfl⟩ : syracuseStep 1416787 = 2125181) B2125181
theorem B1416803 : Blo 1415527 1416803 := bstep (se 1 (by rfl) ⟨1062602, by rfl⟩ : syracuseStep 1416803 = 2125205) B2125205
theorem B1416819 : Blo 1415527 1416819 := bstep (se 1 (by rfl) ⟨1062614, by rfl⟩ : syracuseStep 1416819 = 2125229) B2125229
theorem B1416835 : Blo 1415527 1416835 := bstep (se 1 (by rfl) ⟨1062626, by rfl⟩ : syracuseStep 1416835 = 2125253) B2125253
theorem B1416851 : Blo 1415527 1416851 := bstep (se 1 (by rfl) ⟨1062638, by rfl⟩ : syracuseStep 1416851 = 2125277) B2125277
theorem B1416867 : Blo 1415527 1416867 := bstep (se 1 (by rfl) ⟨1062650, by rfl⟩ : syracuseStep 1416867 = 2125301) B2125301
theorem B1416883 : Blo 1415527 1416883 := bstep (se 1 (by rfl) ⟨1062662, by rfl⟩ : syracuseStep 1416883 = 2125325) B2125325
theorem B1416899 : Blo 1415527 1416899 := bstep (se 1 (by rfl) ⟨1062674, by rfl⟩ : syracuseStep 1416899 = 2125349) B2125349
theorem B2391761 : Blo 1415527 2391761 := bstep (se 2 (by rfl) ⟨896910, by rfl⟩ : syracuseStep 2391761 = 1793821) B1793821
theorem B1416915 : Blo 1415527 1416915 := bstep (se 1 (by rfl) ⟨1062686, by rfl⟩ : syracuseStep 1416915 = 2125373) B2125373
theorem B1416931 : Blo 1415527 1416931 := bstep (se 1 (by rfl) ⟨1062698, by rfl⟩ : syracuseStep 1416931 = 2125397) B2125397
theorem B5381873 : Blo 1415527 5381873 := bstep (se 2 (by rfl) ⟨2018202, by rfl⟩ : syracuseStep 5381873 = 4036405) B4036405
theorem B1416947 : Blo 1415527 1416947 := bstep (se 1 (by rfl) ⟨1062710, by rfl⟩ : syracuseStep 1416947 = 2125421) B2125421
theorem B1416963 : Blo 1415527 1416963 := bstep (se 1 (by rfl) ⟨1062722, by rfl⟩ : syracuseStep 1416963 = 2125445) B2125445
theorem B3186449 : Blo 1415527 3186449 := bstep (se 2 (by rfl) ⟨1194918, by rfl⟩ : syracuseStep 3186449 = 2389837) B2389837
theorem B1416979 : Blo 1415527 1416979 := bstep (se 1 (by rfl) ⟨1062734, by rfl⟩ : syracuseStep 1416979 = 2125469) B2125469
theorem B3186467 : Blo 1415527 3186467 := bstep (se 1 (by rfl) ⟨2389850, by rfl⟩ : syracuseStep 3186467 = 4779701) B4779701
theorem B1416995 : Blo 1415527 1416995 := bstep (se 1 (by rfl) ⟨1062746, by rfl⟩ : syracuseStep 1416995 = 2125493) B2125493
theorem B9076529 : Blo 1415527 9076529 := bstep (se 2 (by rfl) ⟨3403698, by rfl⟩ : syracuseStep 9076529 = 6807397) B6807397
theorem B1417011 : Blo 1415527 1417011 := bstep (se 1 (by rfl) ⟨1062758, by rfl⟩ : syracuseStep 1417011 = 2125517) B2125517
theorem B1417027 : Blo 1415527 1417027 := bstep (se 1 (by rfl) ⟨1062770, by rfl⟩ : syracuseStep 1417027 = 2125541) B2125541
theorem B2391889 : Blo 1415527 2391889 := bstep (se 2 (by rfl) ⟨896958, by rfl⟩ : syracuseStep 2391889 = 1793917) B1793917
theorem B1417043 : Blo 1415527 1417043 := bstep (se 1 (by rfl) ⟨1062782, by rfl⟩ : syracuseStep 1417043 = 2125565) B2125565
theorem B1417059 : Blo 1415527 1417059 := bstep (se 1 (by rfl) ⟨1062794, by rfl⟩ : syracuseStep 1417059 = 2125589) B2125589
theorem B1417075 : Blo 1415527 1417075 := bstep (se 1 (by rfl) ⟨1062806, by rfl⟩ : syracuseStep 1417075 = 2125613) B2125613
theorem B2391923 : Blo 1415527 2391923 := bstep (se 1 (by rfl) ⟨1793942, by rfl⟩ : syracuseStep 2391923 = 3587885) B3587885
theorem B1417091 : Blo 1415527 1417091 := bstep (se 1 (by rfl) ⟨1062818, by rfl⟩ : syracuseStep 1417091 = 2125637) B2125637
theorem B1417107 : Blo 1415527 1417107 := bstep (se 1 (by rfl) ⟨1062830, by rfl⟩ : syracuseStep 1417107 = 2125661) B2125661
theorem B1417123 : Blo 1415527 1417123 := bstep (se 1 (by rfl) ⟨1062842, by rfl⟩ : syracuseStep 1417123 = 2125685) B2125685
theorem B7176113 : Blo 1415527 7176113 := bstep (se 2 (by rfl) ⟨2691042, by rfl⟩ : syracuseStep 7176113 = 5382085) B5382085
theorem B1417139 : Blo 1415527 1417139 := bstep (se 1 (by rfl) ⟨1062854, by rfl⟩ : syracuseStep 1417139 = 2125709) B2125709
theorem B1417155 : Blo 1415527 1417155 := bstep (se 1 (by rfl) ⟨1062866, by rfl⟩ : syracuseStep 1417155 = 2125733) B2125733
theorem B8617925 : Blo 1415527 8617925 := bstep (se 4 (by rfl) ⟨807930, by rfl⟩ : syracuseStep 8617925 = 1615861) B1615861
theorem B1417171 : Blo 1415527 1417171 := bstep (se 1 (by rfl) ⟨1062878, by rfl⟩ : syracuseStep 1417171 = 2125757) B2125757
theorem B5103587 : Blo 1415527 5103587 := bstep (se 1 (by rfl) ⟨3827690, by rfl⟩ : syracuseStep 5103587 = 7655381) B7655381
theorem B1417187 : Blo 1415527 1417187 := bstep (se 1 (by rfl) ⟨1062890, by rfl⟩ : syracuseStep 1417187 = 2125781) B2125781
theorem B1417203 : Blo 1415527 1417203 := bstep (se 1 (by rfl) ⟨1062902, by rfl⟩ : syracuseStep 1417203 = 2125805) B2125805
theorem B2392051 : Blo 1415527 2392051 := bstep (se 1 (by rfl) ⟨1794038, by rfl⟩ : syracuseStep 2392051 = 3588077) B3588077
theorem B1417227 : Blo 1415527 1417227 := bstep (se 1 (by rfl) ⟨1062920, by rfl⟩ : syracuseStep 1417227 = 2125841) B2125841
theorem B1417239 : Blo 1415527 1417239 := bstep (se 1 (by rfl) ⟨1062929, by rfl⟩ : syracuseStep 1417239 = 2125859) B2125859
theorem B1417259 : Blo 1415527 1417259 := bstep (se 1 (by rfl) ⟨1062944, by rfl⟩ : syracuseStep 1417259 = 2125889) B2125889
theorem B8069165 : Blo 1415527 8069165 := bstep (se 3 (by rfl) ⟨1512968, by rfl⟩ : syracuseStep 8069165 = 3025937) B3025937
theorem B1417271 : Blo 1415527 1417271 := bstep (se 1 (by rfl) ⟨1062953, by rfl⟩ : syracuseStep 1417271 = 2125907) B2125907
theorem B1417291 : Blo 1415527 1417291 := bstep (se 1 (by rfl) ⟨1062968, by rfl⟩ : syracuseStep 1417291 = 2125937) B2125937
theorem B1417303 : Blo 1415527 1417303 := bstep (se 1 (by rfl) ⟨1062977, by rfl⟩ : syracuseStep 1417303 = 2125955) B2125955
theorem B1417323 : Blo 1415527 1417323 := bstep (se 1 (by rfl) ⟨1062992, by rfl⟩ : syracuseStep 1417323 = 2125985) B2125985
theorem B1417335 : Blo 1415527 1417335 := bstep (se 1 (by rfl) ⟨1063001, by rfl⟩ : syracuseStep 1417335 = 2126003) B2126003
theorem B3186827 : Blo 1415527 3186827 := bstep (se 1 (by rfl) ⟨2390120, by rfl⟩ : syracuseStep 3186827 = 4780241) B4780241
theorem B1417355 : Blo 1415527 1417355 := bstep (se 1 (by rfl) ⟨1063016, by rfl⟩ : syracuseStep 1417355 = 2126033) B2126033
theorem B1417367 : Blo 1415527 1417367 := bstep (se 1 (by rfl) ⟨1063025, by rfl⟩ : syracuseStep 1417367 = 2126051) B2126051
theorem B1417387 : Blo 1415527 1417387 := bstep (se 1 (by rfl) ⟨1063040, by rfl⟩ : syracuseStep 1417387 = 2126081) B2126081
theorem B6054061 : Blo 1415527 6054061 := bstep (se 3 (by rfl) ⟨1135136, by rfl⟩ : syracuseStep 6054061 = 2270273) B2270273
theorem B1417399 : Blo 1415527 1417399 := bstep (se 1 (by rfl) ⟨1063049, by rfl⟩ : syracuseStep 1417399 = 2126099) B2126099
theorem B3186881 : Blo 1415527 3186881 := bstep (se 2 (by rfl) ⟨1195080, by rfl⟩ : syracuseStep 3186881 = 2390161) B2390161
theorem B1417419 : Blo 1415527 1417419 := bstep (se 1 (by rfl) ⟨1063064, by rfl⟩ : syracuseStep 1417419 = 2126129) B2126129
theorem B1417431 : Blo 1415527 1417431 := bstep (se 1 (by rfl) ⟨1063073, by rfl⟩ : syracuseStep 1417431 = 2126147) B2126147
theorem B1417451 : Blo 1415527 1417451 := bstep (se 1 (by rfl) ⟨1063088, by rfl⟩ : syracuseStep 1417451 = 2126177) B2126177
theorem B1417463 : Blo 1415527 1417463 := bstep (se 1 (by rfl) ⟨1063097, by rfl⟩ : syracuseStep 1417463 = 2126195) B2126195
theorem B1417483 : Blo 1415527 1417483 := bstep (se 1 (by rfl) ⟨1063112, by rfl⟩ : syracuseStep 1417483 = 2126225) B2126225
theorem B1417495 : Blo 1415527 1417495 := bstep (se 1 (by rfl) ⟨1063121, by rfl⟩ : syracuseStep 1417495 = 2126243) B2126243
theorem B1417515 : Blo 1415527 1417515 := bstep (se 1 (by rfl) ⟨1063136, by rfl⟩ : syracuseStep 1417515 = 2126273) B2126273
theorem B4538675 : Blo 1415527 4538675 := bstep (se 1 (by rfl) ⟨3404006, by rfl⟩ : syracuseStep 4538675 = 6808013) B6808013
theorem B1417527 : Blo 1415527 1417527 := bstep (se 1 (by rfl) ⟨1063145, by rfl⟩ : syracuseStep 1417527 = 2126291) B2126291
theorem B3187097 : Blo 1415527 3187097 := bstep (se 2 (by rfl) ⟨1195161, by rfl⟩ : syracuseStep 3187097 = 2390323) B2390323
theorem B3187187 : Blo 1415527 3187187 := bstep (se 1 (by rfl) ⟨2390390, by rfl⟩ : syracuseStep 3187187 = 4780781) B4780781
theorem B2687489 : Blo 1415527 2687489 := bstep (se 2 (by rfl) ⟨1007808, by rfl⟩ : syracuseStep 2687489 = 2015617) B2015617
theorem B5104151 : Blo 1415527 5104151 := bstep (se 1 (by rfl) ⟨3828113, by rfl⟩ : syracuseStep 5104151 = 7656227) B7656227
theorem B3187223 : Blo 1415527 3187223 := bstep (se 1 (by rfl) ⟨2390417, by rfl⟩ : syracuseStep 3187223 = 4780835) B4780835
theorem B4539073 : Blo 1415527 4539073 := bstep (se 2 (by rfl) ⟨1702152, by rfl⟩ : syracuseStep 4539073 = 3404305) B3404305
theorem B3187403 : Blo 1415527 3187403 := bstep (se 1 (by rfl) ⟨2390552, by rfl⟩ : syracuseStep 3187403 = 4781105) B4781105
theorem B12124889 : Blo 1415527 12124889 := bstep (se 2 (by rfl) ⟨4546833, by rfl⟩ : syracuseStep 12124889 = 9093667) B9093667
theorem B3187457 : Blo 1415527 3187457 := bstep (se 2 (by rfl) ⟨1195296, by rfl⟩ : syracuseStep 3187457 = 2390593) B2390593
theorem B2687755 : Blo 1415527 2687755 := bstep (se 1 (by rfl) ⟨2015816, by rfl⟩ : syracuseStep 2687755 = 4031633) B4031633
theorem B4539187 : Blo 1415527 4539187 := bstep (se 1 (by rfl) ⟨3404390, by rfl⟩ : syracuseStep 4539187 = 6808781) B6808781
theorem B5374795 : Blo 1415527 5374795 := bstep (se 1 (by rfl) ⟨4031096, by rfl⟩ : syracuseStep 5374795 = 8062193) B8062193
theorem B3023767 : Blo 1415527 3023767 := bstep (se 1 (by rfl) ⟨2267825, by rfl⟩ : syracuseStep 3023767 = 4535651) B4535651
theorem B8061875 : Blo 1415527 8061875 := bstep (se 1 (by rfl) ⟨6046406, by rfl⟩ : syracuseStep 8061875 = 12092813) B12092813
theorem B7168985 : Blo 1415527 7168985 := bstep (se 2 (by rfl) ⟨2688369, by rfl⟩ : syracuseStep 7168985 = 5376739) B5376739
theorem B3187673 : Blo 1415527 3187673 := bstep (se 2 (by rfl) ⟨1195377, by rfl⟩ : syracuseStep 3187673 = 2390755) B2390755
theorem B3187763 : Blo 1415527 3187763 := bstep (se 1 (by rfl) ⟨2390822, by rfl⟩ : syracuseStep 3187763 = 4781645) B4781645
theorem B3187799 : Blo 1415527 3187799 := bstep (se 1 (by rfl) ⟨2390849, by rfl⟩ : syracuseStep 3187799 = 4781699) B4781699
theorem B5375069 : Blo 1415527 5375069 := bstep (se 3 (by rfl) ⟨1007825, by rfl⟩ : syracuseStep 5375069 = 2015651) B2015651
theorem B2016409 : Blo 1415527 2016409 := bstep (se 2 (by rfl) ⟨756153, by rfl⟩ : syracuseStep 2016409 = 1512307) B1512307
theorem B2688203 : Blo 1415527 2688203 := bstep (se 1 (by rfl) ⟨2016152, by rfl⟩ : syracuseStep 2688203 = 4032305) B4032305
theorem B3187979 : Blo 1415527 3187979 := bstep (se 1 (by rfl) ⟨2390984, by rfl⟩ : syracuseStep 3187979 = 4781969) B4781969
theorem B3188033 : Blo 1415527 3188033 := bstep (se 2 (by rfl) ⟨1195512, by rfl⟩ : syracuseStep 3188033 = 2391025) B2391025
theorem B2688385 : Blo 1415527 2688385 := bstep (se 2 (by rfl) ⟨1008144, by rfl⟩ : syracuseStep 2688385 = 2016289) B2016289
theorem B1533335 : Blo 1415527 1533335 := bstep (se 1 (by rfl) ⟨1150001, by rfl⟩ : syracuseStep 1533335 = 2300003) B2300003
theorem B4777433 : Blo 1415527 4777433 := bstep (se 2 (by rfl) ⟨1791537, by rfl⟩ : syracuseStep 4777433 = 3583075) B3583075
theorem B3188249 : Blo 1415527 3188249 := bstep (se 2 (by rfl) ⟨1195593, by rfl⟩ : syracuseStep 3188249 = 2391187) B2391187
theorem B2123339 : Blo 1415527 2123339 := bstep (se 1 (by rfl) ⟨1592504, by rfl⟩ : syracuseStep 2123339 = 3185009) B3185009
theorem B2123351 : Blo 1415527 2123351 := bstep (se 1 (by rfl) ⟨1592513, by rfl⟩ : syracuseStep 2123351 = 3185027) B3185027
theorem B4032089 : Blo 1415527 4032089 := bstep (se 2 (by rfl) ⟨1512033, by rfl⟩ : syracuseStep 4032089 = 3024067) B3024067
theorem B36308573 : Blo 1415527 36308573 := bstep (se 3 (by rfl) ⟨6807857, by rfl⟩ : syracuseStep 36308573 = 13615715) B13615715
theorem B8611429 : Blo 1415527 8611429 := bstep (se 4 (by rfl) ⟨807321, by rfl⟩ : syracuseStep 8611429 = 1614643) B1614643
theorem B3188339 : Blo 1415527 3188339 := bstep (se 1 (by rfl) ⟨2391254, by rfl⟩ : syracuseStep 3188339 = 4782509) B4782509
theorem B5392003 : Blo 1415527 5392003 := bstep (se 1 (by rfl) ⟨4044002, by rfl⟩ : syracuseStep 5392003 = 8088005) B8088005
theorem B3188375 : Blo 1415527 3188375 := bstep (se 1 (by rfl) ⟨2391281, by rfl⟩ : syracuseStep 3188375 = 4782563) B4782563
theorem B2123417 : Blo 1415527 2123417 := bstep (se 2 (by rfl) ⟨796281, by rfl⟩ : syracuseStep 2123417 = 1592563) B1592563
theorem B3024587 : Blo 1415527 3024587 := bstep (se 1 (by rfl) ⟨2268440, by rfl⟩ : syracuseStep 3024587 = 4536881) B4536881
theorem B2688727 : Blo 1415527 2688727 := bstep (se 1 (by rfl) ⟨2016545, by rfl⟩ : syracuseStep 2688727 = 4033091) B4033091
theorem B2123531 : Blo 1415527 2123531 := bstep (se 1 (by rfl) ⟨1592648, by rfl⟩ : syracuseStep 2123531 = 3185297) B3185297
theorem B2123543 : Blo 1415527 2123543 := bstep (se 1 (by rfl) ⟨1592657, by rfl⟩ : syracuseStep 2123543 = 3185315) B3185315
theorem B5375767 : Blo 1415527 5375767 := bstep (se 1 (by rfl) ⟨4031825, by rfl⟩ : syracuseStep 5375767 = 8063651) B8063651
theorem B3188555 : Blo 1415527 3188555 := bstep (se 1 (by rfl) ⟨2391416, by rfl⟩ : syracuseStep 3188555 = 4782833) B4782833
theorem B2123609 : Blo 1415527 2123609 := bstep (se 2 (by rfl) ⟨796353, by rfl⟩ : syracuseStep 2123609 = 1592707) B1592707
theorem B12109661 : Blo 1415527 12109661 := bstep (se 3 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 12109661 = 4541123) B4541123
theorem B3188609 : Blo 1415527 3188609 := bstep (se 2 (by rfl) ⟨1195728, by rfl⟩ : syracuseStep 3188609 = 2391457) B2391457
theorem B2688947 : Blo 1415527 2688947 := bstep (se 1 (by rfl) ⟨2016710, by rfl⟩ : syracuseStep 2688947 = 4033421) B4033421
theorem B55232435 : Blo 1415527 55232435 := bstep (se 1 (by rfl) ⟨41424326, by rfl⟩ : syracuseStep 55232435 = 82848653) B82848653
theorem B2123723 : Blo 1415527 2123723 := bstep (se 1 (by rfl) ⟨1592792, by rfl⟩ : syracuseStep 2123723 = 3185585) B3185585
theorem B2123735 : Blo 1415527 2123735 := bstep (se 1 (by rfl) ⟨1592801, by rfl⟩ : syracuseStep 2123735 = 3185603) B3185603
theorem B2123801 : Blo 1415527 2123801 := bstep (se 2 (by rfl) ⟨796425, by rfl⟩ : syracuseStep 2123801 = 1592851) B1592851
theorem B3188825 : Blo 1415527 3188825 := bstep (se 2 (by rfl) ⟨1195809, by rfl⟩ : syracuseStep 3188825 = 2391619) B2391619
theorem B6047875 : Blo 1415527 6047875 := bstep (se 1 (by rfl) ⟨4535906, by rfl⟩ : syracuseStep 6047875 = 9071813) B9071813
theorem B2123915 : Blo 1415527 2123915 := bstep (se 1 (by rfl) ⟨1592936, by rfl⟩ : syracuseStep 2123915 = 3185873) B3185873
theorem B4778135 : Blo 1415527 4778135 := bstep (se 1 (by rfl) ⟨3583601, by rfl⟩ : syracuseStep 4778135 = 7167203) B7167203
theorem B2123927 : Blo 1415527 2123927 := bstep (se 1 (by rfl) ⟨1592945, by rfl⟩ : syracuseStep 2123927 = 3185891) B3185891
theorem B2689175 : Blo 1415527 2689175 := bstep (se 1 (by rfl) ⟨2016881, by rfl⟩ : syracuseStep 2689175 = 4033763) B4033763
theorem B5105837 : Blo 1415527 5105837 := bstep (se 3 (by rfl) ⟨957344, by rfl⟩ : syracuseStep 5105837 = 1914689) B1914689
theorem B3188915 : Blo 1415527 3188915 := bstep (se 1 (by rfl) ⟨2391686, by rfl⟩ : syracuseStep 3188915 = 4783373) B4783373
theorem B3188951 : Blo 1415527 3188951 := bstep (se 1 (by rfl) ⟨2391713, by rfl⟩ : syracuseStep 3188951 = 4783427) B4783427
theorem B2123993 : Blo 1415527 2123993 := bstep (se 2 (by rfl) ⟨796497, by rfl⟩ : syracuseStep 2123993 = 1592995) B1592995
theorem B2124107 : Blo 1415527 2124107 := bstep (se 1 (by rfl) ⟨1593080, by rfl⟩ : syracuseStep 2124107 = 3186161) B3186161
theorem B2124119 : Blo 1415527 2124119 := bstep (se 1 (by rfl) ⟨1593089, by rfl⟩ : syracuseStep 2124119 = 3186179) B3186179
theorem B8063333 : Blo 1415527 8063333 := bstep (se 4 (by rfl) ⟨755937, by rfl⟩ : syracuseStep 8063333 = 1511875) B1511875
theorem B3189131 : Blo 1415527 3189131 := bstep (se 1 (by rfl) ⟨2391848, by rfl⟩ : syracuseStep 3189131 = 4783697) B4783697
theorem B4032919 : Blo 1415527 4032919 := bstep (se 1 (by rfl) ⟨3024689, by rfl⟩ : syracuseStep 4032919 = 6049379) B6049379
theorem B2124185 : Blo 1415527 2124185 := bstep (se 2 (by rfl) ⟨796569, by rfl⟩ : syracuseStep 2124185 = 1593139) B1593139
theorem B2689433 : Blo 1415527 2689433 := bstep (se 2 (by rfl) ⟨1008537, by rfl⟩ : syracuseStep 2689433 = 2017075) B2017075
theorem B3189185 : Blo 1415527 3189185 := bstep (se 2 (by rfl) ⟨1195944, by rfl⟩ : syracuseStep 3189185 = 2391889) B2391889
theorem B2124299 : Blo 1415527 2124299 := bstep (se 1 (by rfl) ⟨1593224, by rfl⟩ : syracuseStep 2124299 = 3186449) B3186449
theorem B22981133 : Blo 1415527 22981133 := bstep (se 3 (by rfl) ⟨4308962, by rfl⟩ : syracuseStep 22981133 = 8617925) B8617925
theorem B2124311 : Blo 1415527 2124311 := bstep (se 1 (by rfl) ⟨1593233, by rfl⟩ : syracuseStep 2124311 = 3186467) B3186467
theorem B2214425 : Blo 1415527 2214425 := bstep (se 2 (by rfl) ⟨830409, by rfl⟩ : syracuseStep 2214425 = 1660819) B1660819
theorem B10209827 : Blo 1415527 10209827 := bstep (se 1 (by rfl) ⟨7657370, by rfl⟩ : syracuseStep 10209827 = 15314741) B15314741
theorem B5376557 : Blo 1415527 5376557 := bstep (se 3 (by rfl) ⟨1008104, by rfl⟩ : syracuseStep 5376557 = 2016209) B2016209
theorem B7170605 : Blo 1415527 7170605 := bstep (se 3 (by rfl) ⟨1344488, by rfl⟩ : syracuseStep 7170605 = 2688977) B2688977
theorem B2017867 : Blo 1415527 2017867 := bstep (se 1 (by rfl) ⟨1513400, by rfl⟩ : syracuseStep 2017867 = 3026801) B3026801
theorem B2124377 : Blo 1415527 2124377 := bstep (se 2 (by rfl) ⟨796641, by rfl⟩ : syracuseStep 2124377 = 1593283) B1593283
theorem B13609565 : Blo 1415527 13609565 := bstep (se 3 (by rfl) ⟨2551793, by rfl⟩ : syracuseStep 13609565 = 5103587) B5103587
theorem B3189401 : Blo 1415527 3189401 := bstep (se 2 (by rfl) ⟨1196025, by rfl⟩ : syracuseStep 3189401 = 2392051) B2392051
theorem B4778675 : Blo 1415527 4778675 := bstep (se 1 (by rfl) ⟨3584006, by rfl⟩ : syracuseStep 4778675 = 7168013) B7168013
theorem B2124491 : Blo 1415527 2124491 := bstep (se 1 (by rfl) ⟨1593368, by rfl⟩ : syracuseStep 2124491 = 3186737) B3186737
theorem B2124503 : Blo 1415527 2124503 := bstep (se 1 (by rfl) ⟨1593377, by rfl⟩ : syracuseStep 2124503 = 3186755) B3186755
theorem B9685777 : Blo 1415527 9685777 := bstep (se 2 (by rfl) ⟨3632166, by rfl⟩ : syracuseStep 9685777 = 7264333) B7264333
theorem B5745431 : Blo 1415527 5745431 := bstep (se 1 (by rfl) ⟨4309073, by rfl⟩ : syracuseStep 5745431 = 8618147) B8618147
theorem B2124569 : Blo 1415527 2124569 := bstep (se 2 (by rfl) ⟨796713, by rfl⟩ : syracuseStep 2124569 = 1593427) B1593427
theorem B2689843 : Blo 1415527 2689843 := bstep (se 1 (by rfl) ⟨2017382, by rfl⟩ : syracuseStep 2689843 = 4034765) B4034765
theorem B11209537 : Blo 1415527 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B2124683 : Blo 1415527 2124683 := bstep (se 1 (by rfl) ⟨1593512, by rfl⟩ : syracuseStep 2124683 = 3187025) B3187025
theorem B2124695 : Blo 1415527 2124695 := bstep (se 1 (by rfl) ⟨1593521, by rfl⟩ : syracuseStep 2124695 = 3187043) B3187043
theorem B4778945 : Blo 1415527 4778945 := bstep (se 2 (by rfl) ⟨1792104, by rfl⟩ : syracuseStep 4778945 = 3584209) B3584209
theorem B2124761 : Blo 1415527 2124761 := bstep (se 2 (by rfl) ⟨796785, by rfl⟩ : syracuseStep 2124761 = 1593571) B1593571
theorem B2124875 : Blo 1415527 2124875 := bstep (se 1 (by rfl) ⟨1593656, by rfl⟩ : syracuseStep 2124875 = 3187313) B3187313
theorem B2124887 : Blo 1415527 2124887 := bstep (se 1 (by rfl) ⟨1593665, by rfl⟩ : syracuseStep 2124887 = 3187331) B3187331
theorem B3230849 : Blo 1415527 3230849 := bstep (se 2 (by rfl) ⟨1211568, by rfl⟩ : syracuseStep 3230849 = 2423137) B2423137
theorem B2550923 : Blo 1415527 2550923 := bstep (se 1 (by rfl) ⟨1913192, by rfl⟩ : syracuseStep 2550923 = 3826385) B3826385
theorem B18656407 : Blo 1415527 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B2124953 : Blo 1415527 2124953 := bstep (se 2 (by rfl) ⟨796857, by rfl⟩ : syracuseStep 2124953 = 1593715) B1593715
theorem B1592491 : Blo 1415527 1592491 := bstep (se 1 (by rfl) ⟨1194368, by rfl⟩ : syracuseStep 1592491 = 2388737) B2388737
theorem B4033739 : Blo 1415527 4033739 := bstep (se 1 (by rfl) ⟨3025304, by rfl⟩ : syracuseStep 4033739 = 6050609) B6050609
theorem B16141517 : Blo 1415527 16141517 := bstep (se 3 (by rfl) ⟨3026534, by rfl⟩ : syracuseStep 16141517 = 6053069) B6053069
theorem B2125067 : Blo 1415527 2125067 := bstep (se 1 (by rfl) ⟨1593800, by rfl⟩ : syracuseStep 2125067 = 3187601) B3187601
theorem B1592599 : Blo 1415527 1592599 := bstep (se 1 (by rfl) ⟨1194449, by rfl⟩ : syracuseStep 1592599 = 2388899) B2388899
theorem B2125079 : Blo 1415527 2125079 := bstep (se 1 (by rfl) ⟨1593809, by rfl⟩ : syracuseStep 2125079 = 3187619) B3187619
theorem B2690329 : Blo 1415527 2690329 := bstep (se 2 (by rfl) ⟨1008873, by rfl⟩ : syracuseStep 2690329 = 2017747) B2017747
theorem B2125145 : Blo 1415527 2125145 := bstep (se 2 (by rfl) ⟨796929, by rfl⟩ : syracuseStep 2125145 = 1593859) B1593859
theorem B6131123 : Blo 1415527 6131123 := bstep (se 1 (by rfl) ⟨4598342, by rfl⟩ : syracuseStep 6131123 = 9196685) B9196685
theorem B1592779 : Blo 1415527 1592779 := bstep (se 1 (by rfl) ⟨1194584, by rfl⟩ : syracuseStep 1592779 = 2389169) B2389169
theorem B2125259 : Blo 1415527 2125259 := bstep (se 1 (by rfl) ⟨1593944, by rfl⟩ : syracuseStep 2125259 = 3187889) B3187889
theorem B2125271 : Blo 1415527 2125271 := bstep (se 1 (by rfl) ⟨1593953, by rfl⟩ : syracuseStep 2125271 = 3187907) B3187907
theorem B13102553 : Blo 1415527 13102553 := bstep (se 2 (by rfl) ⟨4913457, by rfl⟩ : syracuseStep 13102553 = 9826915) B9826915
theorem B4779485 : Blo 1415527 4779485 := bstep (se 3 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 4779485 = 1792307) B1792307
theorem B3583511 : Blo 1415527 3583511 := bstep (se 1 (by rfl) ⟨2687633, by rfl⟩ : syracuseStep 3583511 = 5375267) B5375267
theorem B2125337 : Blo 1415527 2125337 := bstep (se 2 (by rfl) ⟨797001, by rfl⟩ : syracuseStep 2125337 = 1594003) B1594003
theorem B1592887 : Blo 1415527 1592887 := bstep (se 1 (by rfl) ⟨1194665, by rfl⟩ : syracuseStep 1592887 = 2389331) B2389331
theorem B2125451 : Blo 1415527 2125451 := bstep (se 1 (by rfl) ⟨1594088, by rfl⟩ : syracuseStep 2125451 = 3188177) B3188177
theorem B2125463 : Blo 1415527 2125463 := bstep (se 1 (by rfl) ⟨1594097, by rfl⟩ : syracuseStep 2125463 = 3188195) B3188195
theorem B8072855 : Blo 1415527 8072855 := bstep (se 1 (by rfl) ⟨6054641, by rfl⟩ : syracuseStep 8072855 = 12109283) B12109283
theorem B2125529 : Blo 1415527 2125529 := bstep (se 2 (by rfl) ⟨797073, by rfl⟩ : syracuseStep 2125529 = 1594147) B1594147
theorem B1593067 : Blo 1415527 1593067 := bstep (se 1 (by rfl) ⟨1194800, by rfl⟩ : syracuseStep 1593067 = 2389601) B2389601
theorem B2125643 : Blo 1415527 2125643 := bstep (se 1 (by rfl) ⟨1594232, by rfl⟩ : syracuseStep 2125643 = 3188465) B3188465
theorem B2690891 : Blo 1415527 2690891 := bstep (se 1 (by rfl) ⟨2018168, by rfl⟩ : syracuseStep 2690891 = 4036337) B4036337
theorem B1593175 : Blo 1415527 1593175 := bstep (se 1 (by rfl) ⟨1194881, by rfl⟩ : syracuseStep 1593175 = 2389763) B2389763
theorem B2125655 : Blo 1415527 2125655 := bstep (se 1 (by rfl) ⟨1594241, by rfl⟩ : syracuseStep 2125655 = 3188483) B3188483
theorem B6049687 : Blo 1415527 6049687 := bstep (se 1 (by rfl) ⟨4537265, by rfl⟩ : syracuseStep 6049687 = 9074531) B9074531
theorem B2125721 : Blo 1415527 2125721 := bstep (se 2 (by rfl) ⟨797145, by rfl⟩ : syracuseStep 2125721 = 1594291) B1594291
theorem B17239985 : Blo 1415527 17239985 := bstep (se 2 (by rfl) ⟨6464994, by rfl⟩ : syracuseStep 17239985 = 12929989) B12929989
theorem B5377985 : Blo 1415527 5377985 := bstep (se 2 (by rfl) ⟨2016744, by rfl⟩ : syracuseStep 5377985 = 4033489) B4033489
theorem B3026945 : Blo 1415527 3026945 := bstep (se 2 (by rfl) ⟨1135104, by rfl⟩ : syracuseStep 3026945 = 2270209) B2270209
theorem B2691073 : Blo 1415527 2691073 := bstep (se 2 (by rfl) ⟨1009152, by rfl⟩ : syracuseStep 2691073 = 2018305) B2018305
theorem B10899461 : Blo 1415527 10899461 := bstep (se 4 (by rfl) ⟨1021824, by rfl⟩ : syracuseStep 10899461 = 2043649) B2043649
theorem B1593355 : Blo 1415527 1593355 := bstep (se 1 (by rfl) ⟨1195016, by rfl⟩ : syracuseStep 1593355 = 2390033) B2390033
theorem B2125835 : Blo 1415527 2125835 := bstep (se 1 (by rfl) ⟨1594376, by rfl⟩ : syracuseStep 2125835 = 3188753) B3188753
theorem B2125847 : Blo 1415527 2125847 := bstep (se 1 (by rfl) ⟨1594385, by rfl⟩ : syracuseStep 2125847 = 3188771) B3188771
theorem B2125913 : Blo 1415527 2125913 := bstep (se 2 (by rfl) ⟨797217, by rfl⟩ : syracuseStep 2125913 = 1594435) B1594435
theorem B3829853 : Blo 1415527 3829853 := bstep (se 3 (by rfl) ⟨718097, by rfl⟩ : syracuseStep 3829853 = 1436195) B1436195
theorem B1593463 : Blo 1415527 1593463 := bstep (se 1 (by rfl) ⟨1195097, by rfl⟩ : syracuseStep 1593463 = 2390195) B2390195
theorem B1511627 : Blo 1415527 1511627 := bstep (se 1 (by rfl) ⟨1133720, by rfl⟩ : syracuseStep 1511627 = 2267441) B2267441
theorem B2126027 : Blo 1415527 2126027 := bstep (se 1 (by rfl) ⟨1594520, by rfl⟩ : syracuseStep 2126027 = 3189041) B3189041
theorem B22106317 : Blo 1415527 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B2126039 : Blo 1415527 2126039 := bstep (se 1 (by rfl) ⟨1594529, by rfl⟩ : syracuseStep 2126039 = 3189059) B3189059
theorem B3232025 : Blo 1415527 3232025 := bstep (se 2 (by rfl) ⟨1212009, by rfl⟩ : syracuseStep 3232025 = 2424019) B2424019
theorem B2126105 : Blo 1415527 2126105 := bstep (se 2 (by rfl) ⟨797289, by rfl⟩ : syracuseStep 2126105 = 1594579) B1594579
theorem B1593643 : Blo 1415527 1593643 := bstep (se 1 (by rfl) ⟨1195232, by rfl⟩ : syracuseStep 1593643 = 2390465) B2390465
theorem B3584321 : Blo 1415527 3584321 := bstep (se 2 (by rfl) ⟨1344120, by rfl⟩ : syracuseStep 3584321 = 2688241) B2688241
theorem B3027287 : Blo 1415527 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B3830105 : Blo 1415527 3830105 := bstep (se 2 (by rfl) ⟨1436289, by rfl⟩ : syracuseStep 3830105 = 2872579) B2872579
theorem B2126219 : Blo 1415527 2126219 := bstep (se 1 (by rfl) ⟨1594664, by rfl⟩ : syracuseStep 2126219 = 3189329) B3189329
theorem B1593751 : Blo 1415527 1593751 := bstep (se 1 (by rfl) ⟨1195313, by rfl⟩ : syracuseStep 1593751 = 2390627) B2390627
theorem B2126231 : Blo 1415527 2126231 := bstep (se 1 (by rfl) ⟨1594673, by rfl⟩ : syracuseStep 2126231 = 3189347) B3189347
theorem B1913305 : Blo 1415527 1913305 := bstep (se 2 (by rfl) ⟨717489, by rfl⟩ : syracuseStep 1913305 = 1434979) B1434979
theorem B6050321 : Blo 1415527 6050321 := bstep (se 2 (by rfl) ⟨2268870, by rfl⟩ : syracuseStep 6050321 = 4537741) B4537741
theorem B3232307 : Blo 1415527 3232307 := bstep (se 1 (by rfl) ⟨2424230, by rfl⟩ : syracuseStep 3232307 = 4848461) B4848461
theorem B4780619 : Blo 1415527 4780619 := bstep (se 1 (by rfl) ⟨3585464, by rfl⟩ : syracuseStep 4780619 = 7170929) B7170929
theorem B1593931 : Blo 1415527 1593931 := bstep (se 1 (by rfl) ⟨1195448, by rfl⟩ : syracuseStep 1593931 = 2390897) B2390897
theorem B15323741 : Blo 1415527 15323741 := bstep (se 3 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 15323741 = 5746403) B5746403
theorem B1594039 : Blo 1415527 1594039 := bstep (se 1 (by rfl) ⟨1195529, by rfl⟩ : syracuseStep 1594039 = 2391059) B2391059
theorem B2552537 : Blo 1415527 2552537 := bstep (se 2 (by rfl) ⟨957201, by rfl⟩ : syracuseStep 2552537 = 1914403) B1914403
theorem B9073453 : Blo 1415527 9073453 := bstep (se 3 (by rfl) ⟨1701272, by rfl⟩ : syracuseStep 9073453 = 3402545) B3402545
theorem B2388811 : Blo 1415527 2388811 := bstep (se 1 (by rfl) ⟨1791608, by rfl⟩ : syracuseStep 2388811 = 3583217) B3583217
theorem B3584857 : Blo 1415527 3584857 := bstep (se 2 (by rfl) ⟨1344321, by rfl⟩ : syracuseStep 3584857 = 2688643) B2688643
theorem B4780889 : Blo 1415527 4780889 := bstep (se 2 (by rfl) ⟨1792833, by rfl⟩ : syracuseStep 4780889 = 3585667) B3585667
theorem B1594219 : Blo 1415527 1594219 := bstep (se 1 (by rfl) ⟨1195664, by rfl⟩ : syracuseStep 1594219 = 2391329) B2391329
theorem B11482033 : Blo 1415527 11482033 := bstep (se 2 (by rfl) ⟨4305762, by rfl⟩ : syracuseStep 11482033 = 8611525) B8611525
theorem B2298839 : Blo 1415527 2298839 := bstep (se 1 (by rfl) ⟨1724129, by rfl⟩ : syracuseStep 2298839 = 3448259) B3448259
theorem B1594327 : Blo 1415527 1594327 := bstep (se 1 (by rfl) ⟨1195745, by rfl⟩ : syracuseStep 1594327 = 2391491) B2391491
theorem B2388953 : Blo 1415527 2388953 := bstep (se 2 (by rfl) ⟨895857, by rfl⟩ : syracuseStep 2388953 = 1791715) B1791715
theorem B16126937 : Blo 1415527 16126937 := bstep (se 2 (by rfl) ⟨6047601, by rfl⟩ : syracuseStep 16126937 = 12095203) B12095203
theorem B10204177 : Blo 1415527 10204177 := bstep (se 2 (by rfl) ⟨3826566, by rfl⟩ : syracuseStep 10204177 = 7653133) B7653133
theorem B2389081 : Blo 1415527 2389081 := bstep (se 2 (by rfl) ⟨895905, by rfl⟩ : syracuseStep 2389081 = 1791811) B1791811
theorem B1594507 : Blo 1415527 1594507 := bstep (se 1 (by rfl) ⟨1195880, by rfl⟩ : syracuseStep 1594507 = 2391761) B2391761
theorem B41989261 : Blo 1415527 41989261 := bstep (se 3 (by rfl) ⟨7872986, by rfl⟩ : syracuseStep 41989261 = 15745973) B15745973
theorem B6051019 : Blo 1415527 6051019 := bstep (se 1 (by rfl) ⟨4538264, by rfl⟩ : syracuseStep 6051019 = 9076529) B9076529
theorem B12104909 : Blo 1415527 12104909 := bstep (se 3 (by rfl) ⟨2269670, by rfl⟩ : syracuseStep 12104909 = 4539341) B4539341
theorem B1594615 : Blo 1415527 1594615 := bstep (se 1 (by rfl) ⟨1195961, by rfl⟩ : syracuseStep 1594615 = 2391923) B2391923
theorem B13612333 : Blo 1415527 13612333 := bstep (se 3 (by rfl) ⟨2552312, by rfl⟩ : syracuseStep 13612333 = 5104625) B5104625
theorem B5379473 : Blo 1415527 5379473 := bstep (se 2 (by rfl) ⟨2017302, by rfl⟩ : syracuseStep 5379473 = 4034605) B4034605
theorem B40850837 : Blo 1415527 40850837 := bstep (se 6 (by rfl) ⟨957441, by rfl⟩ : syracuseStep 40850837 = 1914883) B1914883
theorem B1660343 : Blo 1415527 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B6051293 : Blo 1415527 6051293 := bstep (se 3 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 6051293 = 2269235) B2269235
theorem B4535831 : Blo 1415527 4535831 := bstep (se 1 (by rfl) ⟨3401873, by rfl⟩ : syracuseStep 4535831 = 6803747) B6803747
theorem B4781591 : Blo 1415527 4781591 := bstep (se 1 (by rfl) ⟨3586193, by rfl⟩ : syracuseStep 4781591 = 7172387) B7172387
theorem B6460979 : Blo 1415527 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B4036189 : Blo 1415527 4036189 := bstep (se 3 (by rfl) ⟨756785, by rfl⟩ : syracuseStep 4036189 = 1513571) B1513571
theorem B4535959 : Blo 1415527 4535959 := bstep (se 1 (by rfl) ⟨3401969, by rfl⟩ : syracuseStep 4535959 = 6803939) B6803939
theorem B2389655 : Blo 1415527 2389655 := bstep (se 1 (by rfl) ⟨1792241, by rfl⟩ : syracuseStep 2389655 = 3584483) B3584483
theorem B2389783 : Blo 1415527 2389783 := bstep (se 1 (by rfl) ⟨1792337, by rfl⟩ : syracuseStep 2389783 = 3584675) B3584675
theorem B6051635 : Blo 1415527 6051635 := bstep (se 1 (by rfl) ⟨4538726, by rfl⟩ : syracuseStep 6051635 = 9077453) B9077453
theorem B5379929 : Blo 1415527 5379929 := bstep (se 2 (by rfl) ⟨2017473, by rfl⟩ : syracuseStep 5379929 = 4034947) B4034947
theorem B4536215 : Blo 1415527 4536215 := bstep (se 1 (by rfl) ⟨3402161, by rfl⟩ : syracuseStep 4536215 = 6804323) B6804323
theorem B1513387 : Blo 1415527 1513387 := bstep (se 1 (by rfl) ⟨1135040, by rfl⟩ : syracuseStep 1513387 = 2270081) B2270081
theorem B3585971 : Blo 1415527 3585971 := bstep (se 1 (by rfl) ⟨2689478, by rfl⟩ : syracuseStep 3585971 = 5378957) B5378957
theorem B2873291 : Blo 1415527 2873291 := bstep (se 1 (by rfl) ⟨2154968, by rfl⟩ : syracuseStep 2873291 = 4309937) B4309937
theorem B1456151 : Blo 1415527 1456151 := bstep (se 1 (by rfl) ⟨1092113, by rfl⟩ : syracuseStep 1456151 = 2184227) B2184227
theorem B5380141 : Blo 1415527 5380141 := bstep (se 3 (by rfl) ⟨1008776, by rfl⟩ : syracuseStep 5380141 = 2017553) B2017553
theorem B4782131 : Blo 1415527 4782131 := bstep (se 1 (by rfl) ⟨3586598, by rfl⟩ : syracuseStep 4782131 = 7173197) B7173197
theorem B9328819 : Blo 1415527 9328819 := bstep (se 1 (by rfl) ⟨6996614, by rfl⟩ : syracuseStep 9328819 = 13993229) B13993229
theorem B3586265 : Blo 1415527 3586265 := bstep (se 2 (by rfl) ⟨1344849, by rfl⟩ : syracuseStep 3586265 = 2689699) B2689699
theorem B49715461 : Blo 1415527 49715461 := bstep (se 4 (by rfl) ⟨4660824, by rfl⟩ : syracuseStep 49715461 = 9321649) B9321649
theorem B15309121 : Blo 1415527 15309121 := bstep (se 2 (by rfl) ⟨5740920, by rfl⟩ : syracuseStep 15309121 = 11481841) B11481841
theorem B4782401 : Blo 1415527 4782401 := bstep (se 2 (by rfl) ⟨1793400, by rfl⟩ : syracuseStep 4782401 = 3586801) B3586801
theorem B5380445 : Blo 1415527 5380445 := bstep (se 3 (by rfl) ⟨1008833, by rfl⟩ : syracuseStep 5380445 = 2017667) B2017667
theorem B7174493 : Blo 1415527 7174493 := bstep (se 3 (by rfl) ⟨1345217, by rfl⟩ : syracuseStep 7174493 = 2690435) B2690435
theorem B1415531 : Blo 1415527 1415531 := bstep (se 1 (by rfl) ⟨1061648, by rfl⟩ : syracuseStep 1415531 = 2123297) B2123297
theorem B1415543 : Blo 1415527 1415543 := bstep (se 1 (by rfl) ⟨1061657, by rfl⟩ : syracuseStep 1415543 = 2123315) B2123315
theorem B1415563 : Blo 1415527 1415563 := bstep (se 1 (by rfl) ⟨1061672, by rfl⟩ : syracuseStep 1415563 = 2123345) B2123345
theorem B2390411 : Blo 1415527 2390411 := bstep (se 1 (by rfl) ⟨1792808, by rfl⟩ : syracuseStep 2390411 = 3585617) B3585617
theorem B1415575 : Blo 1415527 1415575 := bstep (se 1 (by rfl) ⟨1061681, by rfl⟩ : syracuseStep 1415575 = 2123363) B2123363
theorem B1415595 : Blo 1415527 1415595 := bstep (se 1 (by rfl) ⟨1061696, by rfl⟩ : syracuseStep 1415595 = 2123393) B2123393
theorem B1415607 : Blo 1415527 1415607 := bstep (se 1 (by rfl) ⟨1061705, by rfl⟩ : syracuseStep 1415607 = 2123411) B2123411
theorem B3185099 : Blo 1415527 3185099 := bstep (se 1 (by rfl) ⟨2388824, by rfl⟩ : syracuseStep 3185099 = 4777649) B4777649
theorem B1415627 : Blo 1415527 1415627 := bstep (se 1 (by rfl) ⟨1061720, by rfl⟩ : syracuseStep 1415627 = 2123441) B2123441
theorem B1792459 : Blo 1415527 1792459 := bstep (se 1 (by rfl) ⟨1344344, by rfl⟩ : syracuseStep 1792459 = 2688689) B2688689
theorem B1415639 : Blo 1415527 1415639 := bstep (se 1 (by rfl) ⟨1061729, by rfl⟩ : syracuseStep 1415639 = 2123459) B2123459
theorem B1415659 : Blo 1415527 1415659 := bstep (se 1 (by rfl) ⟨1061744, by rfl⟩ : syracuseStep 1415659 = 2123489) B2123489
theorem B1415671 : Blo 1415527 1415671 := bstep (se 1 (by rfl) ⟨1061753, by rfl⟩ : syracuseStep 1415671 = 2123507) B2123507
theorem B3185153 : Blo 1415527 3185153 := bstep (se 2 (by rfl) ⟨1194432, by rfl⟩ : syracuseStep 3185153 = 2388865) B2388865
theorem B1415691 : Blo 1415527 1415691 := bstep (se 1 (by rfl) ⟨1061768, by rfl⟩ : syracuseStep 1415691 = 2123537) B2123537
theorem B2390539 : Blo 1415527 2390539 := bstep (se 1 (by rfl) ⟨1792904, by rfl⟩ : syracuseStep 2390539 = 3585809) B3585809
theorem B1415703 : Blo 1415527 1415703 := bstep (se 1 (by rfl) ⟨1061777, by rfl⟩ : syracuseStep 1415703 = 2123555) B2123555
theorem B1415723 : Blo 1415527 1415723 := bstep (se 1 (by rfl) ⟨1061792, by rfl⟩ : syracuseStep 1415723 = 2123585) B2123585
theorem B1415735 : Blo 1415527 1415735 := bstep (se 1 (by rfl) ⟨1061801, by rfl⟩ : syracuseStep 1415735 = 2123603) B2123603
theorem B2267723 : Blo 1415527 2267723 := bstep (se 1 (by rfl) ⟨1700792, by rfl⟩ : syracuseStep 2267723 = 3401585) B3401585
theorem B1415755 : Blo 1415527 1415755 := bstep (se 1 (by rfl) ⟨1061816, by rfl⟩ : syracuseStep 1415755 = 2123633) B2123633
theorem B1415767 : Blo 1415527 1415767 := bstep (se 1 (by rfl) ⟨1061825, by rfl⟩ : syracuseStep 1415767 = 2123651) B2123651
theorem B1636951 : Blo 1415527 1636951 := bstep (se 1 (by rfl) ⟨1227713, by rfl⟩ : syracuseStep 1636951 = 2455427) B2455427
theorem B1415787 : Blo 1415527 1415787 := bstep (se 1 (by rfl) ⟨1061840, by rfl⟩ : syracuseStep 1415787 = 2123681) B2123681
theorem B1415799 : Blo 1415527 1415799 := bstep (se 1 (by rfl) ⟨1061849, by rfl⟩ : syracuseStep 1415799 = 2123699) B2123699
theorem B1415819 : Blo 1415527 1415819 := bstep (se 1 (by rfl) ⟨1061864, by rfl⟩ : syracuseStep 1415819 = 2123729) B2123729
theorem B1415831 : Blo 1415527 1415831 := bstep (se 1 (by rfl) ⟨1061873, by rfl⟩ : syracuseStep 1415831 = 2123747) B2123747
theorem B2390681 : Blo 1415527 2390681 := bstep (se 2 (by rfl) ⟨896505, by rfl⟩ : syracuseStep 2390681 = 1793011) B1793011
theorem B1415851 : Blo 1415527 1415851 := bstep (se 1 (by rfl) ⟨1061888, by rfl⟩ : syracuseStep 1415851 = 2123777) B2123777
theorem B1415863 : Blo 1415527 1415863 := bstep (se 1 (by rfl) ⟨1061897, by rfl⟩ : syracuseStep 1415863 = 2123795) B2123795
theorem B1415883 : Blo 1415527 1415883 := bstep (se 1 (by rfl) ⟨1061912, by rfl⟩ : syracuseStep 1415883 = 2123825) B2123825
theorem B1415895 : Blo 1415527 1415895 := bstep (se 1 (by rfl) ⟨1061921, by rfl⟩ : syracuseStep 1415895 = 2123843) B2123843
theorem B3185369 : Blo 1415527 3185369 := bstep (se 2 (by rfl) ⟨1194513, by rfl⟩ : syracuseStep 3185369 = 2389027) B2389027
theorem B1415915 : Blo 1415527 1415915 := bstep (se 1 (by rfl) ⟨1061936, by rfl⟩ : syracuseStep 1415915 = 2123873) B2123873
theorem B1415927 : Blo 1415527 1415927 := bstep (se 1 (by rfl) ⟨1061945, by rfl⟩ : syracuseStep 1415927 = 2123891) B2123891
theorem B1415947 : Blo 1415527 1415947 := bstep (se 1 (by rfl) ⟨1061960, by rfl⟩ : syracuseStep 1415947 = 2123921) B2123921
theorem B1702667 : Blo 1415527 1702667 := bstep (se 1 (by rfl) ⟨1277000, by rfl⟩ : syracuseStep 1702667 = 2554001) B2554001
theorem B1415959 : Blo 1415527 1415959 := bstep (se 1 (by rfl) ⟨1061969, by rfl⟩ : syracuseStep 1415959 = 2123939) B2123939
theorem B2390809 : Blo 1415527 2390809 := bstep (se 2 (by rfl) ⟨896553, by rfl⟩ : syracuseStep 2390809 = 1793107) B1793107
theorem B1415979 : Blo 1415527 1415979 := bstep (se 1 (by rfl) ⟨1061984, by rfl⟩ : syracuseStep 1415979 = 2123969) B2123969
theorem B3185459 : Blo 1415527 3185459 := bstep (se 1 (by rfl) ⟨2389094, by rfl⟩ : syracuseStep 3185459 = 4778189) B4778189
theorem B1415991 : Blo 1415527 1415991 := bstep (se 1 (by rfl) ⟨1061993, by rfl⟩ : syracuseStep 1415991 = 2123987) B2123987
theorem B1416011 : Blo 1415527 1416011 := bstep (se 1 (by rfl) ⟨1062008, by rfl⟩ : syracuseStep 1416011 = 2124017) B2124017
theorem B3185495 : Blo 1415527 3185495 := bstep (se 1 (by rfl) ⟨2389121, by rfl⟩ : syracuseStep 3185495 = 4778243) B4778243
theorem B1416023 : Blo 1415527 1416023 := bstep (se 1 (by rfl) ⟨1062017, by rfl⟩ : syracuseStep 1416023 = 2124035) B2124035
theorem B4848473 : Blo 1415527 4848473 := bstep (se 2 (by rfl) ⟨1818177, by rfl⟩ : syracuseStep 4848473 = 3636355) B3636355
theorem B4782941 : Blo 1415527 4782941 := bstep (se 3 (by rfl) ⟨896801, by rfl⟩ : syracuseStep 4782941 = 1793603) B1793603
theorem B1416043 : Blo 1415527 1416043 := bstep (se 1 (by rfl) ⟨1062032, by rfl⟩ : syracuseStep 1416043 = 2124065) B2124065
theorem B1416055 : Blo 1415527 1416055 := bstep (se 1 (by rfl) ⟨1062041, by rfl⟩ : syracuseStep 1416055 = 2124083) B2124083
theorem B1416075 : Blo 1415527 1416075 := bstep (se 1 (by rfl) ⟨1062056, by rfl⟩ : syracuseStep 1416075 = 2124113) B2124113
theorem B1416087 : Blo 1415527 1416087 := bstep (se 1 (by rfl) ⟨1062065, by rfl⟩ : syracuseStep 1416087 = 2124131) B2124131
theorem B1416107 : Blo 1415527 1416107 := bstep (se 1 (by rfl) ⟨1062080, by rfl⟩ : syracuseStep 1416107 = 2124161) B2124161
theorem B1416119 : Blo 1415527 1416119 := bstep (se 1 (by rfl) ⟨1062089, by rfl⟩ : syracuseStep 1416119 = 2124179) B2124179
theorem B1416139 : Blo 1415527 1416139 := bstep (se 1 (by rfl) ⟨1062104, by rfl⟩ : syracuseStep 1416139 = 2124209) B2124209
theorem B4537291 : Blo 1415527 4537291 := bstep (se 1 (by rfl) ⟨3402968, by rfl⟩ : syracuseStep 4537291 = 6805937) B6805937
theorem B1416151 : Blo 1415527 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B38763481 : Blo 1415527 38763481 := bstep (se 2 (by rfl) ⟨14536305, by rfl⟩ : syracuseStep 38763481 = 29072611) B29072611
theorem B1416171 : Blo 1415527 1416171 := bstep (se 1 (by rfl) ⟨1062128, by rfl⟩ : syracuseStep 1416171 = 2124257) B2124257
theorem B1416183 : Blo 1415527 1416183 := bstep (se 1 (by rfl) ⟨1062137, by rfl⟩ : syracuseStep 1416183 = 2124275) B2124275
theorem B3185675 : Blo 1415527 3185675 := bstep (se 1 (by rfl) ⟨2389256, by rfl⟩ : syracuseStep 3185675 = 4778513) B4778513
theorem B1416203 : Blo 1415527 1416203 := bstep (se 1 (by rfl) ⟨1062152, by rfl⟩ : syracuseStep 1416203 = 2124305) B2124305
theorem B1416215 : Blo 1415527 1416215 := bstep (se 1 (by rfl) ⟨1062161, by rfl⟩ : syracuseStep 1416215 = 2124323) B2124323
theorem B1416235 : Blo 1415527 1416235 := bstep (se 1 (by rfl) ⟨1062176, by rfl⟩ : syracuseStep 1416235 = 2124353) B2124353
theorem B1416247 : Blo 1415527 1416247 := bstep (se 1 (by rfl) ⟨1062185, by rfl⟩ : syracuseStep 1416247 = 2124371) B2124371
theorem B7167041 : Blo 1415527 7167041 := bstep (se 2 (by rfl) ⟨2687640, by rfl⟩ : syracuseStep 7167041 = 5375281) B5375281
theorem B3185729 : Blo 1415527 3185729 := bstep (se 2 (by rfl) ⟨1194648, by rfl⟩ : syracuseStep 3185729 = 2389297) B2389297
theorem B1416267 : Blo 1415527 1416267 := bstep (se 1 (by rfl) ⟨1062200, by rfl⟩ : syracuseStep 1416267 = 2124401) B2124401
theorem B1416279 : Blo 1415527 1416279 := bstep (se 1 (by rfl) ⟨1062209, by rfl⟩ : syracuseStep 1416279 = 2124419) B2124419
theorem B4537433 : Blo 1415527 4537433 := bstep (se 2 (by rfl) ⟨1701537, by rfl⟩ : syracuseStep 4537433 = 3403075) B3403075
theorem B1416299 : Blo 1415527 1416299 := bstep (se 1 (by rfl) ⟨1062224, by rfl⟩ : syracuseStep 1416299 = 2124449) B2124449
theorem B1416311 : Blo 1415527 1416311 := bstep (se 1 (by rfl) ⟨1062233, by rfl⟩ : syracuseStep 1416311 = 2124467) B2124467
theorem B1416331 : Blo 1415527 1416331 := bstep (se 1 (by rfl) ⟨1062248, by rfl⟩ : syracuseStep 1416331 = 2124497) B2124497
theorem B1416343 : Blo 1415527 1416343 := bstep (se 1 (by rfl) ⟨1062257, by rfl⟩ : syracuseStep 1416343 = 2124515) B2124515
theorem B1416363 : Blo 1415527 1416363 := bstep (se 1 (by rfl) ⟨1062272, by rfl⟩ : syracuseStep 1416363 = 2124545) B2124545
theorem B10763441 : Blo 1415527 10763441 := bstep (se 2 (by rfl) ⟨4036290, by rfl⟩ : syracuseStep 10763441 = 8072581) B8072581
theorem B1416375 : Blo 1415527 1416375 := bstep (se 1 (by rfl) ⟨1062281, by rfl⟩ : syracuseStep 1416375 = 2124563) B2124563
theorem B4537547 : Blo 1415527 4537547 := bstep (se 1 (by rfl) ⟨3403160, by rfl⟩ : syracuseStep 4537547 = 6806321) B6806321
theorem B1416395 : Blo 1415527 1416395 := bstep (se 1 (by rfl) ⟨1062296, by rfl⟩ : syracuseStep 1416395 = 2124593) B2124593
theorem B1416407 : Blo 1415527 1416407 := bstep (se 1 (by rfl) ⟨1062305, by rfl⟩ : syracuseStep 1416407 = 2124611) B2124611
theorem B4308185 : Blo 1415527 4308185 := bstep (se 2 (by rfl) ⟨1615569, by rfl⟩ : syracuseStep 4308185 = 3231139) B3231139
theorem B1416427 : Blo 1415527 1416427 := bstep (se 1 (by rfl) ⟨1062320, by rfl⟩ : syracuseStep 1416427 = 2124641) B2124641
theorem B1416439 : Blo 1415527 1416439 := bstep (se 1 (by rfl) ⟨1062329, by rfl⟩ : syracuseStep 1416439 = 2124659) B2124659
theorem B1416459 : Blo 1415527 1416459 := bstep (se 1 (by rfl) ⟨1062344, by rfl⟩ : syracuseStep 1416459 = 2124689) B2124689
theorem B1416471 : Blo 1415527 1416471 := bstep (se 1 (by rfl) ⟨1062353, by rfl⟩ : syracuseStep 1416471 = 2124707) B2124707
theorem B3185945 : Blo 1415527 3185945 := bstep (se 2 (by rfl) ⟨1194729, by rfl⟩ : syracuseStep 3185945 = 2389459) B2389459
theorem B1416491 : Blo 1415527 1416491 := bstep (se 1 (by rfl) ⟨1062368, by rfl⟩ : syracuseStep 1416491 = 2124737) B2124737
theorem B1416503 : Blo 1415527 1416503 := bstep (se 1 (by rfl) ⟨1062377, by rfl⟩ : syracuseStep 1416503 = 2124755) B2124755
theorem B1416523 : Blo 1415527 1416523 := bstep (se 1 (by rfl) ⟨1062392, by rfl⟩ : syracuseStep 1416523 = 2124785) B2124785
theorem B1416535 : Blo 1415527 1416535 := bstep (se 1 (by rfl) ⟨1062401, by rfl⟩ : syracuseStep 1416535 = 2124803) B2124803
theorem B2391383 : Blo 1415527 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B1416555 : Blo 1415527 1416555 := bstep (se 1 (by rfl) ⟨1062416, by rfl⟩ : syracuseStep 1416555 = 2124833) B2124833
theorem B3186035 : Blo 1415527 3186035 := bstep (se 1 (by rfl) ⟨2389526, by rfl⟩ : syracuseStep 3186035 = 4779053) B4779053
theorem B1416567 : Blo 1415527 1416567 := bstep (se 1 (by rfl) ⟨1062425, by rfl⟩ : syracuseStep 1416567 = 2124851) B2124851
theorem B1416587 : Blo 1415527 1416587 := bstep (se 1 (by rfl) ⟨1062440, by rfl⟩ : syracuseStep 1416587 = 2124881) B2124881
theorem B3186071 : Blo 1415527 3186071 := bstep (se 1 (by rfl) ⟨2389553, by rfl⟩ : syracuseStep 3186071 = 4779107) B4779107
theorem B1416599 : Blo 1415527 1416599 := bstep (se 1 (by rfl) ⟨1062449, by rfl⟩ : syracuseStep 1416599 = 2124899) B2124899
theorem B2268569 : Blo 1415527 2268569 := bstep (se 2 (by rfl) ⟨850713, by rfl⟩ : syracuseStep 2268569 = 1701427) B1701427
theorem B1793431 : Blo 1415527 1793431 := bstep (se 1 (by rfl) ⟨1345073, by rfl⟩ : syracuseStep 1793431 = 2690147) B2690147
theorem B1416619 : Blo 1415527 1416619 := bstep (se 1 (by rfl) ⟨1062464, by rfl⟩ : syracuseStep 1416619 = 2124929) B2124929
theorem B1416631 : Blo 1415527 1416631 := bstep (se 1 (by rfl) ⟨1062473, by rfl⟩ : syracuseStep 1416631 = 2124947) B2124947
theorem B1416651 : Blo 1415527 1416651 := bstep (se 1 (by rfl) ⟨1062488, by rfl⟩ : syracuseStep 1416651 = 2124977) B2124977
theorem B1416663 : Blo 1415527 1416663 := bstep (se 1 (by rfl) ⟨1062497, by rfl⟩ : syracuseStep 1416663 = 2124995) B2124995
theorem B2391511 : Blo 1415527 2391511 := bstep (se 1 (by rfl) ⟨1793633, by rfl⟩ : syracuseStep 2391511 = 3587267) B3587267
theorem B1416683 : Blo 1415527 1416683 := bstep (se 1 (by rfl) ⟨1062512, by rfl⟩ : syracuseStep 1416683 = 2125025) B2125025
theorem B1416695 : Blo 1415527 1416695 := bstep (se 1 (by rfl) ⟨1062521, by rfl⟩ : syracuseStep 1416695 = 2125043) B2125043
theorem B1416715 : Blo 1415527 1416715 := bstep (se 1 (by rfl) ⟨1062536, by rfl⟩ : syracuseStep 1416715 = 2125073) B2125073
theorem B1416727 : Blo 1415527 1416727 := bstep (se 1 (by rfl) ⟨1062545, by rfl⟩ : syracuseStep 1416727 = 2125091) B2125091
theorem B1416747 : Blo 1415527 1416747 := bstep (se 1 (by rfl) ⟨1062560, by rfl⟩ : syracuseStep 1416747 = 2125121) B2125121
theorem B4537907 : Blo 1415527 4537907 := bstep (se 1 (by rfl) ⟨3403430, by rfl⟩ : syracuseStep 4537907 = 6806861) B6806861
theorem B1416759 : Blo 1415527 1416759 := bstep (se 1 (by rfl) ⟨1062569, by rfl⟩ : syracuseStep 1416759 = 2125139) B2125139
theorem B3186251 : Blo 1415527 3186251 := bstep (se 1 (by rfl) ⟨2389688, by rfl⟩ : syracuseStep 3186251 = 4779377) B4779377
theorem B1416779 : Blo 1415527 1416779 := bstep (se 1 (by rfl) ⟨1062584, by rfl⟩ : syracuseStep 1416779 = 2125169) B2125169
theorem B1416791 : Blo 1415527 1416791 := bstep (se 1 (by rfl) ⟨1062593, by rfl⟩ : syracuseStep 1416791 = 2125187) B2125187
theorem B1416811 : Blo 1415527 1416811 := bstep (se 1 (by rfl) ⟨1062608, by rfl⟩ : syracuseStep 1416811 = 2125217) B2125217
theorem B1416823 : Blo 1415527 1416823 := bstep (se 1 (by rfl) ⟨1062617, by rfl⟩ : syracuseStep 1416823 = 2125235) B2125235
theorem B3186305 : Blo 1415527 3186305 := bstep (se 2 (by rfl) ⟨1194864, by rfl⟩ : syracuseStep 3186305 = 2389729) B2389729
theorem B1416843 : Blo 1415527 1416843 := bstep (se 1 (by rfl) ⟨1062632, by rfl⟩ : syracuseStep 1416843 = 2125265) B2125265
theorem B1416855 : Blo 1415527 1416855 := bstep (se 1 (by rfl) ⟨1062641, by rfl⟩ : syracuseStep 1416855 = 2125283) B2125283
theorem B10763927 : Blo 1415527 10763927 := bstep (se 1 (by rfl) ⟨8072945, by rfl⟩ : syracuseStep 10763927 = 16145891) B16145891
theorem B1416875 : Blo 1415527 1416875 := bstep (se 1 (by rfl) ⟨1062656, by rfl⟩ : syracuseStep 1416875 = 2125313) B2125313
theorem B1416887 : Blo 1415527 1416887 := bstep (se 1 (by rfl) ⟨1062665, by rfl⟩ : syracuseStep 1416887 = 2125331) B2125331
theorem B1416907 : Blo 1415527 1416907 := bstep (se 1 (by rfl) ⟨1062680, by rfl⟩ : syracuseStep 1416907 = 2125361) B2125361
theorem B1416919 : Blo 1415527 1416919 := bstep (se 1 (by rfl) ⟨1062689, by rfl⟩ : syracuseStep 1416919 = 2125379) B2125379
theorem B1416939 : Blo 1415527 1416939 := bstep (se 1 (by rfl) ⟨1062704, by rfl⟩ : syracuseStep 1416939 = 2125409) B2125409
theorem B1416951 : Blo 1415527 1416951 := bstep (se 1 (by rfl) ⟨1062713, by rfl⟩ : syracuseStep 1416951 = 2125427) B2125427
theorem B1416971 : Blo 1415527 1416971 := bstep (se 1 (by rfl) ⟨1062728, by rfl⟩ : syracuseStep 1416971 = 2125457) B2125457
theorem B1416983 : Blo 1415527 1416983 := bstep (se 1 (by rfl) ⟨1062737, by rfl⟩ : syracuseStep 1416983 = 2125475) B2125475
theorem B1417003 : Blo 1415527 1417003 := bstep (se 1 (by rfl) ⟨1062752, by rfl⟩ : syracuseStep 1417003 = 2125505) B2125505
theorem B1417015 : Blo 1415527 1417015 := bstep (se 1 (by rfl) ⟨1062761, by rfl⟩ : syracuseStep 1417015 = 2125523) B2125523
theorem B1417035 : Blo 1415527 1417035 := bstep (se 1 (by rfl) ⟨1062776, by rfl⟩ : syracuseStep 1417035 = 2125553) B2125553
theorem B3587915 : Blo 1415527 3587915 := bstep (se 1 (by rfl) ⟨2690936, by rfl⟩ : syracuseStep 3587915 = 5381873) B5381873
theorem B1417047 : Blo 1415527 1417047 := bstep (se 1 (by rfl) ⟨1062785, by rfl⟩ : syracuseStep 1417047 = 2125571) B2125571
theorem B3186521 : Blo 1415527 3186521 := bstep (se 2 (by rfl) ⟨1194945, by rfl⟩ : syracuseStep 3186521 = 2389891) B2389891
theorem B1417067 : Blo 1415527 1417067 := bstep (se 1 (by rfl) ⟨1062800, by rfl⟩ : syracuseStep 1417067 = 2125601) B2125601
theorem B1417079 : Blo 1415527 1417079 := bstep (se 1 (by rfl) ⟨1062809, by rfl⟩ : syracuseStep 1417079 = 2125619) B2125619
theorem B1417099 : Blo 1415527 1417099 := bstep (se 1 (by rfl) ⟨1062824, by rfl⟩ : syracuseStep 1417099 = 2125649) B2125649
theorem B1417111 : Blo 1415527 1417111 := bstep (se 1 (by rfl) ⟨1062833, by rfl⟩ : syracuseStep 1417111 = 2125667) B2125667
theorem B2269081 : Blo 1415527 2269081 := bstep (se 2 (by rfl) ⟨850905, by rfl⟩ : syracuseStep 2269081 = 1701811) B1701811
theorem B1417131 : Blo 1415527 1417131 := bstep (se 1 (by rfl) ⟨1062848, by rfl⟩ : syracuseStep 1417131 = 2125697) B2125697
theorem B3186611 : Blo 1415527 3186611 := bstep (se 1 (by rfl) ⟨2389958, by rfl⟩ : syracuseStep 3186611 = 4779917) B4779917
theorem B1417143 : Blo 1415527 1417143 := bstep (se 1 (by rfl) ⟨1062857, by rfl⟩ : syracuseStep 1417143 = 2125715) B2125715
theorem B1417163 : Blo 1415527 1417163 := bstep (se 1 (by rfl) ⟨1062872, by rfl⟩ : syracuseStep 1417163 = 2125745) B2125745
theorem B4784075 : Blo 1415527 4784075 := bstep (se 1 (by rfl) ⟨3588056, by rfl⟩ : syracuseStep 4784075 = 7176113) B7176113
theorem B3186647 : Blo 1415527 3186647 := bstep (se 1 (by rfl) ⟨2389985, by rfl⟩ : syracuseStep 3186647 = 4779971) B4779971
theorem B1417175 : Blo 1415527 1417175 := bstep (se 1 (by rfl) ⟨1062881, by rfl⟩ : syracuseStep 1417175 = 2125763) B2125763
theorem B36282329 : Blo 1415527 36282329 := bstep (se 2 (by rfl) ⟨13605873, by rfl⟩ : syracuseStep 36282329 = 27211747) B27211747
theorem B11640793 : Blo 1415527 11640793 := bstep (se 2 (by rfl) ⟨4365297, by rfl⟩ : syracuseStep 11640793 = 8730595) B8730595
theorem B1417195 : Blo 1415527 1417195 := bstep (se 1 (by rfl) ⟨1062896, by rfl⟩ : syracuseStep 1417195 = 2125793) B2125793
theorem B1417207 : Blo 1415527 1417207 := bstep (se 1 (by rfl) ⟨1062905, by rfl⟩ : syracuseStep 1417207 = 2125811) B2125811
theorem B3588097 : Blo 1415527 3588097 := bstep (se 2 (by rfl) ⟨1345536, by rfl⟩ : syracuseStep 3588097 = 2691073) B2691073
theorem B1417223 : Blo 1415527 1417223 := bstep (se 1 (by rfl) ⟨1062917, by rfl⟩ : syracuseStep 1417223 = 2125835) B2125835
theorem B29065229 : Blo 1415527 29065229 := bstep (se 3 (by rfl) ⟨5449730, by rfl⟩ : syracuseStep 29065229 = 10899461) B10899461
theorem B1417231 : Blo 1415527 1417231 := bstep (se 1 (by rfl) ⟨1062923, by rfl⟩ : syracuseStep 1417231 = 2125847) B2125847
theorem B1417275 : Blo 1415527 1417275 := bstep (se 1 (by rfl) ⟨1062956, by rfl⟩ : syracuseStep 1417275 = 2125913) B2125913
theorem B3883069 : Blo 1415527 3883069 := bstep (se 3 (by rfl) ⟨728075, by rfl⟩ : syracuseStep 3883069 = 1456151) B1456151
theorem B1417351 : Blo 1415527 1417351 := bstep (se 1 (by rfl) ⟨1063013, by rfl⟩ : syracuseStep 1417351 = 2126027) B2126027
theorem B1417359 : Blo 1415527 1417359 := bstep (se 1 (by rfl) ⟨1063019, by rfl⟩ : syracuseStep 1417359 = 2126039) B2126039
theorem B2154683 : Blo 1415527 2154683 := bstep (se 1 (by rfl) ⟨1616012, by rfl⟩ : syracuseStep 2154683 = 3232025) B3232025
theorem B1417403 : Blo 1415527 1417403 := bstep (se 1 (by rfl) ⟨1063052, by rfl⟩ : syracuseStep 1417403 = 2126105) B2126105
theorem B1417479 : Blo 1415527 1417479 := bstep (se 1 (by rfl) ⟨1063109, by rfl⟩ : syracuseStep 1417479 = 2126219) B2126219
theorem B1417487 : Blo 1415527 1417487 := bstep (se 1 (by rfl) ⟨1063115, by rfl⟩ : syracuseStep 1417487 = 2126231) B2126231
theorem B29475089 : Blo 1415527 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B2154871 : Blo 1415527 2154871 := bstep (se 1 (by rfl) ⟨1616153, by rfl⟩ : syracuseStep 2154871 = 3232307) B3232307
theorem B3187079 : Blo 1415527 3187079 := bstep (se 1 (by rfl) ⟨2390309, by rfl⟩ : syracuseStep 3187079 = 4780619) B4780619
theorem B10215827 : Blo 1415527 10215827 := bstep (se 1 (by rfl) ⟨7661870, by rfl⟩ : syracuseStep 10215827 = 15323741) B15323741
theorem B10756637 : Blo 1415527 10756637 := bstep (se 3 (by rfl) ⟨2016869, by rfl⟩ : syracuseStep 10756637 = 4033739) B4033739
theorem B3187259 : Blo 1415527 3187259 := bstep (se 1 (by rfl) ⟨2390444, by rfl⟩ : syracuseStep 3187259 = 4780889) B4780889
theorem B5374583 : Blo 1415527 5374583 := bstep (se 1 (by rfl) ⟨4030937, by rfl⟩ : syracuseStep 5374583 = 8061875) B8061875
theorem B3187385 : Blo 1415527 3187385 := bstep (se 2 (by rfl) ⟨1195269, by rfl⟩ : syracuseStep 3187385 = 2390539) B2390539
theorem B8069939 : Blo 1415527 8069939 := bstep (se 1 (by rfl) ⟨6052454, by rfl⟩ : syracuseStep 8069939 = 12104909) B12104909
theorem B3023887 : Blo 1415527 3023887 := bstep (se 1 (by rfl) ⟨2267915, by rfl⟩ : syracuseStep 3023887 = 4535831) B4535831
theorem B3187727 : Blo 1415527 3187727 := bstep (se 1 (by rfl) ⟨2390795, by rfl⟩ : syracuseStep 3187727 = 4781591) B4781591
theorem B3187745 : Blo 1415527 3187745 := bstep (se 2 (by rfl) ⟨1195404, by rfl⟩ : syracuseStep 3187745 = 2390809) B2390809
theorem B2688059 : Blo 1415527 2688059 := bstep (se 1 (by rfl) ⟨2016044, by rfl⟩ : syracuseStep 2688059 = 4032089) B4032089
theorem B4088893 : Blo 1415527 4088893 := bstep (se 3 (by rfl) ⟨766667, by rfl⟩ : syracuseStep 4088893 = 1533335) B1533335
theorem B4031689 : Blo 1415527 4031689 := bstep (se 2 (by rfl) ⟨1511883, by rfl⟩ : syracuseStep 4031689 = 3023767) B3023767
theorem B3024143 : Blo 1415527 3024143 := bstep (se 1 (by rfl) ⟨2268107, by rfl⟩ : syracuseStep 3024143 = 4536215) B4536215
theorem B51684641 : Blo 1415527 51684641 := bstep (se 2 (by rfl) ⟨19381740, by rfl⟩ : syracuseStep 51684641 = 38763481) B38763481
theorem B3188087 : Blo 1415527 3188087 := bstep (se 1 (by rfl) ⟨2391065, by rfl⟩ : syracuseStep 3188087 = 4782131) B4782131
theorem B17229277 : Blo 1415527 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B55985681 : Blo 1415527 55985681 := bstep (se 2 (by rfl) ⟨20994630, by rfl⟩ : syracuseStep 55985681 = 41989261) B41989261
theorem B6047261 : Blo 1415527 6047261 := bstep (se 3 (by rfl) ⟨1133861, by rfl⟩ : syracuseStep 6047261 = 2267723) B2267723
theorem B2688545 : Blo 1415527 2688545 := bstep (se 2 (by rfl) ⟨1008204, by rfl⟩ : syracuseStep 2688545 = 2016409) B2016409
theorem B3188267 : Blo 1415527 3188267 := bstep (se 1 (by rfl) ⟨2391200, by rfl⟩ : syracuseStep 3188267 = 4782401) B4782401
theorem B2123321 : Blo 1415527 2123321 := bstep (se 2 (by rfl) ⟨796245, by rfl⟩ : syracuseStep 2123321 = 1592491) B1592491
theorem B5375555 : Blo 1415527 5375555 := bstep (se 1 (by rfl) ⟨4031666, by rfl⟩ : syracuseStep 5375555 = 8063333) B8063333
theorem B2123399 : Blo 1415527 2123399 := bstep (se 1 (by rfl) ⟨1592549, by rfl⟩ : syracuseStep 2123399 = 3185099) B3185099
theorem B2123435 : Blo 1415527 2123435 := bstep (se 1 (by rfl) ⟨1592576, by rfl⟩ : syracuseStep 2123435 = 3185153) B3185153
theorem B15320755 : Blo 1415527 15320755 := bstep (se 1 (by rfl) ⟨11490566, by rfl⟩ : syracuseStep 15320755 = 22981133) B22981133
theorem B2123465 : Blo 1415527 2123465 := bstep (se 2 (by rfl) ⟨796299, by rfl⟩ : syracuseStep 2123465 = 1592599) B1592599
theorem B2123579 : Blo 1415527 2123579 := bstep (se 1 (by rfl) ⟨1592684, by rfl⟩ : syracuseStep 2123579 = 3185369) B3185369
theorem B2123639 : Blo 1415527 2123639 := bstep (se 1 (by rfl) ⟨1592729, by rfl⟩ : syracuseStep 2123639 = 3185459) B3185459
theorem B2123663 : Blo 1415527 2123663 := bstep (se 1 (by rfl) ⟨1592747, by rfl⟩ : syracuseStep 2123663 = 3185495) B3185495
theorem B3188627 : Blo 1415527 3188627 := bstep (se 1 (by rfl) ⟨2391470, by rfl⟩ : syracuseStep 3188627 = 4782941) B4782941
theorem B2123705 : Blo 1415527 2123705 := bstep (se 2 (by rfl) ⟨796389, by rfl⟩ : syracuseStep 2123705 = 1592779) B1592779
theorem B3188681 : Blo 1415527 3188681 := bstep (se 2 (by rfl) ⟨1195755, by rfl⟩ : syracuseStep 3188681 = 2391511) B2391511
theorem B2123783 : Blo 1415527 2123783 := bstep (se 1 (by rfl) ⟨1592837, by rfl⟩ : syracuseStep 2123783 = 3185675) B3185675
theorem B4540445 : Blo 1415527 4540445 := bstep (se 3 (by rfl) ⟨851333, by rfl⟩ : syracuseStep 4540445 = 1702667) B1702667
theorem B4778027 : Blo 1415527 4778027 := bstep (se 1 (by rfl) ⟨3583520, by rfl⟩ : syracuseStep 4778027 = 7167041) B7167041
theorem B2123819 : Blo 1415527 2123819 := bstep (se 1 (by rfl) ⟨1592864, by rfl⟩ : syracuseStep 2123819 = 3185729) B3185729
theorem B3024955 : Blo 1415527 3024955 := bstep (se 1 (by rfl) ⟨2268716, by rfl⟩ : syracuseStep 3024955 = 4537433) B4537433
theorem B2123849 : Blo 1415527 2123849 := bstep (se 2 (by rfl) ⟨796443, by rfl⟩ : syracuseStep 2123849 = 1592887) B1592887
theorem B16124021 : Blo 1415527 16124021 := bstep (se 5 (by rfl) ⟨755813, by rfl⟩ : syracuseStep 16124021 = 1511627) B1511627
theorem B3025031 : Blo 1415527 3025031 := bstep (se 1 (by rfl) ⟨2268773, by rfl⟩ : syracuseStep 3025031 = 4537547) B4537547
theorem B2123963 : Blo 1415527 2123963 := bstep (se 1 (by rfl) ⟨1592972, by rfl⟩ : syracuseStep 2123963 = 3185945) B3185945
theorem B6047945 : Blo 1415527 6047945 := bstep (se 2 (by rfl) ⟨2267979, by rfl⟩ : syracuseStep 6047945 = 4535959) B4535959
theorem B8071397 : Blo 1415527 8071397 := bstep (se 4 (by rfl) ⟨756693, by rfl⟩ : syracuseStep 8071397 = 1513387) B1513387
theorem B2124023 : Blo 1415527 2124023 := bstep (se 1 (by rfl) ⟨1593017, by rfl⟩ : syracuseStep 2124023 = 3186035) B3186035
theorem B2124047 : Blo 1415527 2124047 := bstep (se 1 (by rfl) ⟨1593035, by rfl⟩ : syracuseStep 2124047 = 3186071) B3186071
theorem B2124089 : Blo 1415527 2124089 := bstep (se 2 (by rfl) ⟨796533, by rfl⟩ : syracuseStep 2124089 = 1593067) B1593067
theorem B8735035 : Blo 1415527 8735035 := bstep (se 1 (by rfl) ⟨6551276, by rfl⟩ : syracuseStep 8735035 = 13102553) B13102553
theorem B3025271 : Blo 1415527 3025271 := bstep (se 1 (by rfl) ⟨2268953, by rfl⟩ : syracuseStep 3025271 = 4537907) B4537907
theorem B2124167 : Blo 1415527 2124167 := bstep (se 1 (by rfl) ⟨1593125, by rfl⟩ : syracuseStep 2124167 = 3186251) B3186251
theorem B2124203 : Blo 1415527 2124203 := bstep (se 1 (by rfl) ⟨1593152, by rfl⟩ : syracuseStep 2124203 = 3186305) B3186305
theorem B2124233 : Blo 1415527 2124233 := bstep (se 2 (by rfl) ⟨796587, by rfl⟩ : syracuseStep 2124233 = 1593175) B1593175
theorem B7662109 : Blo 1415527 7662109 := bstep (se 3 (by rfl) ⟨1436645, by rfl⟩ : syracuseStep 7662109 = 2873291) B2873291
theorem B3025441 : Blo 1415527 3025441 := bstep (se 2 (by rfl) ⟨1134540, by rfl⟩ : syracuseStep 3025441 = 2269081) B2269081
theorem B2124347 : Blo 1415527 2124347 := bstep (se 1 (by rfl) ⟨1593260, by rfl⟩ : syracuseStep 2124347 = 3186521) B3186521
theorem B6130237 : Blo 1415527 6130237 := bstep (se 3 (by rfl) ⟨1149419, by rfl⟩ : syracuseStep 6130237 = 2298839) B2298839
theorem B2124407 : Blo 1415527 2124407 := bstep (se 1 (by rfl) ⟨1593305, by rfl⟩ : syracuseStep 2124407 = 3186611) B3186611
theorem B3189383 : Blo 1415527 3189383 := bstep (se 1 (by rfl) ⟨2392037, by rfl⟩ : syracuseStep 3189383 = 4784075) B4784075
theorem B2124431 : Blo 1415527 2124431 := bstep (se 1 (by rfl) ⟨1593323, by rfl⟩ : syracuseStep 2124431 = 3186647) B3186647
theorem B2017963 : Blo 1415527 2017963 := bstep (se 1 (by rfl) ⟨1513472, by rfl⟩ : syracuseStep 2017963 = 3026945) B3026945
theorem B2124473 : Blo 1415527 2124473 := bstep (se 2 (by rfl) ⟨796677, by rfl⟩ : syracuseStep 2124473 = 1593355) B1593355
theorem B2124551 : Blo 1415527 2124551 := bstep (se 1 (by rfl) ⟨1593413, by rfl⟩ : syracuseStep 2124551 = 3186827) B3186827
theorem B2124587 : Blo 1415527 2124587 := bstep (se 1 (by rfl) ⟨1593440, by rfl⟩ : syracuseStep 2124587 = 3186881) B3186881
theorem B2124617 : Blo 1415527 2124617 := bstep (se 2 (by rfl) ⟨796731, by rfl⟩ : syracuseStep 2124617 = 1593463) B1593463
theorem B8063833 : Blo 1415527 8063833 := bstep (se 2 (by rfl) ⟨3023937, by rfl⟩ : syracuseStep 8063833 = 6047875) B6047875
theorem B3025783 : Blo 1415527 3025783 := bstep (se 1 (by rfl) ⟨2269337, by rfl⟩ : syracuseStep 3025783 = 4538675) B4538675
theorem B2018191 : Blo 1415527 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B8072081 : Blo 1415527 8072081 := bstep (se 2 (by rfl) ⟨3027030, by rfl⟩ : syracuseStep 8072081 = 6054061) B6054061
theorem B12438425 : Blo 1415527 12438425 := bstep (se 2 (by rfl) ⟨4664409, by rfl⟩ : syracuseStep 12438425 = 9328819) B9328819
theorem B2124731 : Blo 1415527 2124731 := bstep (se 1 (by rfl) ⟨1593548, by rfl⟩ : syracuseStep 2124731 = 3187097) B3187097
theorem B2124791 : Blo 1415527 2124791 := bstep (se 1 (by rfl) ⟨1593593, by rfl⟩ : syracuseStep 2124791 = 3187187) B3187187
theorem B4033547 : Blo 1415527 4033547 := bstep (se 1 (by rfl) ⟨3025160, by rfl⟩ : syracuseStep 4033547 = 6050321) B6050321
theorem B3402767 : Blo 1415527 3402767 := bstep (se 1 (by rfl) ⟨2552075, by rfl⟩ : syracuseStep 3402767 = 5104151) B5104151
theorem B2124815 : Blo 1415527 2124815 := bstep (se 1 (by rfl) ⟨1593611, by rfl⟩ : syracuseStep 2124815 = 3187223) B3187223
theorem B2124857 : Blo 1415527 2124857 := bstep (se 2 (by rfl) ⟨796821, by rfl⟩ : syracuseStep 2124857 = 1593643) B1593643
theorem B2124935 : Blo 1415527 2124935 := bstep (se 1 (by rfl) ⟨1593701, by rfl⟩ : syracuseStep 2124935 = 3187403) B3187403
theorem B2124971 : Blo 1415527 2124971 := bstep (se 1 (by rfl) ⟨1593728, by rfl⟩ : syracuseStep 2124971 = 3187457) B3187457
theorem B5377225 : Blo 1415527 5377225 := bstep (se 2 (by rfl) ⟨2016459, by rfl⟩ : syracuseStep 5377225 = 4032919) B4032919
theorem B2125001 : Blo 1415527 2125001 := bstep (se 2 (by rfl) ⟨796875, by rfl⟩ : syracuseStep 2125001 = 1593751) B1593751
theorem B11488493 : Blo 1415527 11488493 := bstep (se 3 (by rfl) ⟨2154092, by rfl⟩ : syracuseStep 11488493 = 4308185) B4308185
theorem B2551073 : Blo 1415527 2551073 := bstep (se 2 (by rfl) ⟨956652, by rfl⟩ : syracuseStep 2551073 = 1913305) B1913305
theorem B1592635 : Blo 1415527 1592635 := bstep (se 1 (by rfl) ⟨1194476, by rfl⟩ : syracuseStep 1592635 = 2388953) B2388953
theorem B10751291 : Blo 1415527 10751291 := bstep (se 1 (by rfl) ⟨8063468, by rfl⟩ : syracuseStep 10751291 = 16126937) B16126937
theorem B4779323 : Blo 1415527 4779323 := bstep (se 1 (by rfl) ⟨3584492, by rfl⟩ : syracuseStep 4779323 = 7168985) B7168985
theorem B2125115 : Blo 1415527 2125115 := bstep (se 1 (by rfl) ⟨1593836, by rfl⟩ : syracuseStep 2125115 = 3187673) B3187673
theorem B2125175 : Blo 1415527 2125175 := bstep (se 1 (by rfl) ⟨1593881, by rfl⟩ : syracuseStep 2125175 = 3187763) B3187763
theorem B2125199 : Blo 1415527 2125199 := bstep (se 1 (by rfl) ⟨1593899, by rfl⟩ : syracuseStep 2125199 = 3187799) B3187799
theorem B3583379 : Blo 1415527 3583379 := bstep (se 1 (by rfl) ⟨2687534, by rfl⟩ : syracuseStep 3583379 = 5375069) B5375069
theorem B2125241 : Blo 1415527 2125241 := bstep (se 2 (by rfl) ⟨796965, by rfl⟩ : syracuseStep 2125241 = 1593931) B1593931
theorem B2690489 : Blo 1415527 2690489 := bstep (se 2 (by rfl) ⟨1008933, by rfl⟩ : syracuseStep 2690489 = 2017867) B2017867
theorem B2182601 : Blo 1415527 2182601 := bstep (se 2 (by rfl) ⟨818475, by rfl⟩ : syracuseStep 2182601 = 1636951) B1636951
theorem B2125319 : Blo 1415527 2125319 := bstep (se 1 (by rfl) ⟨1593989, by rfl⟩ : syracuseStep 2125319 = 3187979) B3187979
theorem B2125355 : Blo 1415527 2125355 := bstep (se 1 (by rfl) ⟨1594016, by rfl⟩ : syracuseStep 2125355 = 3188033) B3188033
theorem B2125385 : Blo 1415527 2125385 := bstep (se 2 (by rfl) ⟨797019, by rfl⟩ : syracuseStep 2125385 = 1594039) B1594039
theorem B27233891 : Blo 1415527 27233891 := bstep (se 1 (by rfl) ⟨20425418, by rfl⟩ : syracuseStep 27233891 = 40850837) B40850837
theorem B4034195 : Blo 1415527 4034195 := bstep (se 1 (by rfl) ⟨3025646, by rfl⟩ : syracuseStep 4034195 = 6051293) B6051293
theorem B3583673 : Blo 1415527 3583673 := bstep (se 2 (by rfl) ⟨1343877, by rfl⟩ : syracuseStep 3583673 = 2687755) B2687755
theorem B2125499 : Blo 1415527 2125499 := bstep (se 1 (by rfl) ⟨1594124, by rfl⟩ : syracuseStep 2125499 = 3188249) B3188249
theorem B12914369 : Blo 1415527 12914369 := bstep (se 2 (by rfl) ⟨4842888, by rfl⟩ : syracuseStep 12914369 = 9685777) B9685777
theorem B2125559 : Blo 1415527 2125559 := bstep (se 1 (by rfl) ⟨1594169, by rfl⟩ : syracuseStep 2125559 = 3188339) B3188339
theorem B14946049 : Blo 1415527 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B1593103 : Blo 1415527 1593103 := bstep (se 1 (by rfl) ⟨1194827, by rfl⟩ : syracuseStep 1593103 = 2389655) B2389655
theorem B2125583 : Blo 1415527 2125583 := bstep (se 1 (by rfl) ⟨1594187, by rfl⟩ : syracuseStep 2125583 = 3188375) B3188375
theorem B4779809 : Blo 1415527 4779809 := bstep (se 2 (by rfl) ⟨1792428, by rfl⟩ : syracuseStep 4779809 = 3584857) B3584857
theorem B2125625 : Blo 1415527 2125625 := bstep (se 2 (by rfl) ⟨797109, by rfl⟩ : syracuseStep 2125625 = 1594219) B1594219
theorem B4427581 : Blo 1415527 4427581 := bstep (se 3 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 4427581 = 1660343) B1660343
theorem B4034423 : Blo 1415527 4034423 := bstep (se 1 (by rfl) ⟨3025817, by rfl⟩ : syracuseStep 4034423 = 6051635) B6051635
theorem B2125703 : Blo 1415527 2125703 := bstep (se 1 (by rfl) ⟨1594277, by rfl⟩ : syracuseStep 2125703 = 3188555) B3188555
theorem B8073107 : Blo 1415527 8073107 := bstep (se 1 (by rfl) ⟨6054830, by rfl⟩ : syracuseStep 8073107 = 12109661) B12109661
theorem B2125739 : Blo 1415527 2125739 := bstep (se 1 (by rfl) ⟨1594304, by rfl⟩ : syracuseStep 2125739 = 3188609) B3188609
theorem B6049721 : Blo 1415527 6049721 := bstep (se 2 (by rfl) ⟨2268645, by rfl⟩ : syracuseStep 6049721 = 4537291) B4537291
theorem B2125769 : Blo 1415527 2125769 := bstep (se 2 (by rfl) ⟨797163, by rfl⟩ : syracuseStep 2125769 = 1594327) B1594327
theorem B2125883 : Blo 1415527 2125883 := bstep (se 1 (by rfl) ⟨1594412, by rfl⟩ : syracuseStep 2125883 = 3188825) B3188825
theorem B27226205 : Blo 1415527 27226205 := bstep (se 3 (by rfl) ⟨5104913, by rfl⟩ : syracuseStep 27226205 = 10209827) B10209827
theorem B3403891 : Blo 1415527 3403891 := bstep (se 1 (by rfl) ⟨2552918, by rfl⟩ : syracuseStep 3403891 = 5105837) B5105837
theorem B2125943 : Blo 1415527 2125943 := bstep (se 1 (by rfl) ⟨1594457, by rfl⟩ : syracuseStep 2125943 = 3188915) B3188915
theorem B2125967 : Blo 1415527 2125967 := bstep (se 1 (by rfl) ⟨1594475, by rfl⟩ : syracuseStep 2125967 = 3188951) B3188951
theorem B2126009 : Blo 1415527 2126009 := bstep (se 2 (by rfl) ⟨797253, by rfl⟩ : syracuseStep 2126009 = 1594507) B1594507
theorem B24875209 : Blo 1415527 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B1593607 : Blo 1415527 1593607 := bstep (se 1 (by rfl) ⟨1195205, by rfl⟩ : syracuseStep 1593607 = 2390411) B2390411
theorem B2126087 : Blo 1415527 2126087 := bstep (se 1 (by rfl) ⟨1594565, by rfl⟩ : syracuseStep 2126087 = 3189131) B3189131
theorem B2126123 : Blo 1415527 2126123 := bstep (se 1 (by rfl) ⟨1594592, by rfl⟩ : syracuseStep 2126123 = 3189185) B3189185
theorem B2126153 : Blo 1415527 2126153 := bstep (se 2 (by rfl) ⟨797307, by rfl⟩ : syracuseStep 2126153 = 1594615) B1594615
theorem B3584371 : Blo 1415527 3584371 := bstep (se 1 (by rfl) ⟨2688278, by rfl⟩ : syracuseStep 3584371 = 5376557) B5376557
theorem B4780403 : Blo 1415527 4780403 := bstep (se 1 (by rfl) ⟨3585302, by rfl⟩ : syracuseStep 4780403 = 7170605) B7170605
theorem B18149777 : Blo 1415527 18149777 := bstep (se 2 (by rfl) ⟨6806166, by rfl⟩ : syracuseStep 18149777 = 13612333) B13612333
theorem B9073043 : Blo 1415527 9073043 := bstep (se 1 (by rfl) ⟨6804782, by rfl⟩ : syracuseStep 9073043 = 13609565) B13609565
theorem B1593787 : Blo 1415527 1593787 := bstep (se 1 (by rfl) ⟨1195340, by rfl⟩ : syracuseStep 1593787 = 2390681) B2390681
theorem B2126267 : Blo 1415527 2126267 := bstep (se 1 (by rfl) ⟨1594700, by rfl⟩ : syracuseStep 2126267 = 3189401) B3189401
theorem B3584513 : Blo 1415527 3584513 := bstep (se 2 (by rfl) ⟨1344192, by rfl⟩ : syracuseStep 3584513 = 2688385) B2688385
theorem B3830287 : Blo 1415527 3830287 := bstep (se 1 (by rfl) ⟨2872715, by rfl⟩ : syracuseStep 3830287 = 5745431) B5745431
theorem B8065565 : Blo 1415527 8065565 := bstep (se 3 (by rfl) ⟨1512293, by rfl⟩ : syracuseStep 8065565 = 3024587) B3024587
theorem B3232315 : Blo 1415527 3232315 := bstep (se 1 (by rfl) ⟨2424236, by rfl⟩ : syracuseStep 3232315 = 4848473) B4848473
theorem B1700615 : Blo 1415527 1700615 := bstep (se 1 (by rfl) ⟨1275461, by rfl⟩ : syracuseStep 1700615 = 2550923) B2550923
theorem B11481905 : Blo 1415527 11481905 := bstep (se 2 (by rfl) ⟨4305714, by rfl⟩ : syracuseStep 11481905 = 8611429) B8611429
theorem B10761011 : Blo 1415527 10761011 := bstep (se 1 (by rfl) ⟨8070758, by rfl⟩ : syracuseStep 10761011 = 16141517) B16141517
theorem B7189337 : Blo 1415527 7189337 := bstep (se 2 (by rfl) ⟨2696001, by rfl⟩ : syracuseStep 7189337 = 5392003) B5392003
theorem B1594255 : Blo 1415527 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B1512379 : Blo 1415527 1512379 := bstep (se 1 (by rfl) ⟨1134284, by rfl⟩ : syracuseStep 1512379 = 2268569) B2268569
theorem B3584969 : Blo 1415527 3584969 := bstep (se 2 (by rfl) ⟨1344363, by rfl⟩ : syracuseStep 3584969 = 2688727) B2688727
theorem B2389007 : Blo 1415527 2389007 := bstep (se 1 (by rfl) ⟨1791755, by rfl⟩ : syracuseStep 2389007 = 3583511) B3583511
theorem B8066249 : Blo 1415527 8066249 := bstep (se 2 (by rfl) ⟨3024843, by rfl⟩ : syracuseStep 8066249 = 6049687) B6049687
theorem B15521057 : Blo 1415527 15521057 := bstep (se 2 (by rfl) ⟨5820396, by rfl⟩ : syracuseStep 15521057 = 11640793) B11640793
theorem B3585323 : Blo 1415527 3585323 := bstep (se 1 (by rfl) ⟨2688992, by rfl⟩ : syracuseStep 3585323 = 5377985) B5377985
theorem B24188219 : Blo 1415527 24188219 := bstep (se 1 (by rfl) ⟨18141164, by rfl⟩ : syracuseStep 24188219 = 36282329) B36282329
theorem B5379443 : Blo 1415527 5379443 := bstep (se 1 (by rfl) ⟨4034582, by rfl⟩ : syracuseStep 5379443 = 8069165) B8069165
theorem B7173521 : Blo 1415527 7173521 := bstep (se 2 (by rfl) ⟨2690070, by rfl⟩ : syracuseStep 7173521 = 5380141) B5380141
theorem B2389547 : Blo 1415527 2389547 := bstep (se 1 (by rfl) ⟨1792160, by rfl⟩ : syracuseStep 2389547 = 3584321) B3584321
theorem B2553403 : Blo 1415527 2553403 := bstep (se 1 (by rfl) ⟨1915052, by rfl⟩ : syracuseStep 2553403 = 3830105) B3830105
theorem B10212941 : Blo 1415527 10212941 := bstep (se 3 (by rfl) ⟨1914926, by rfl⟩ : syracuseStep 10212941 = 3829853) B3829853
theorem B1791659 : Blo 1415527 1791659 := bstep (se 1 (by rfl) ⟨1343744, by rfl⟩ : syracuseStep 1791659 = 2687489) B2687489
theorem B20412161 : Blo 1415527 20412161 := bstep (se 2 (by rfl) ⟨7654560, by rfl⟩ : syracuseStep 20412161 = 15309121) B15309121
theorem B8083259 : Blo 1415527 8083259 := bstep (se 1 (by rfl) ⟨6062444, by rfl⟩ : syracuseStep 8083259 = 12124889) B12124889
theorem B1701691 : Blo 1415527 1701691 := bstep (se 1 (by rfl) ⟨1276268, by rfl⟩ : syracuseStep 1701691 = 2552537) B2552537
theorem B2389945 : Blo 1415527 2389945 := bstep (se 2 (by rfl) ⟨896229, by rfl⟩ : syracuseStep 2389945 = 1792459) B1792459
theorem B1792135 : Blo 1415527 1792135 := bstep (se 1 (by rfl) ⟨1344101, by rfl⟩ : syracuseStep 1792135 = 2688203) B2688203
theorem B6052097 : Blo 1415527 6052097 := bstep (se 2 (by rfl) ⟨2269536, by rfl⟩ : syracuseStep 6052097 = 4539073) B4539073
theorem B3586315 : Blo 1415527 3586315 := bstep (se 1 (by rfl) ⟨2689736, by rfl⟩ : syracuseStep 3586315 = 5379473) B5379473
theorem B3184955 : Blo 1415527 3184955 := bstep (se 1 (by rfl) ⟨2388716, by rfl⟩ : syracuseStep 3184955 = 4777433) B4777433
theorem B1415559 : Blo 1415527 1415559 := bstep (se 1 (by rfl) ⟨1061669, by rfl⟩ : syracuseStep 1415559 = 2123339) B2123339
theorem B1415567 : Blo 1415527 1415567 := bstep (se 1 (by rfl) ⟨1061675, by rfl⟩ : syracuseStep 1415567 = 2123351) B2123351
theorem B12097937 : Blo 1415527 12097937 := bstep (se 2 (by rfl) ⟨4536726, by rfl⟩ : syracuseStep 12097937 = 9073453) B9073453
theorem B24205715 : Blo 1415527 24205715 := bstep (se 1 (by rfl) ⟨18154286, by rfl⟩ : syracuseStep 24205715 = 36308573) B36308573
theorem B3586457 : Blo 1415527 3586457 := bstep (se 2 (by rfl) ⟨1344921, by rfl⟩ : syracuseStep 3586457 = 2689843) B2689843
theorem B6052249 : Blo 1415527 6052249 := bstep (se 2 (by rfl) ⟨2269593, by rfl⟩ : syracuseStep 6052249 = 4539187) B4539187
theorem B7166393 : Blo 1415527 7166393 := bstep (se 2 (by rfl) ⟨2687397, by rfl⟩ : syracuseStep 7166393 = 5374795) B5374795
theorem B3185081 : Blo 1415527 3185081 := bstep (se 2 (by rfl) ⟨1194405, by rfl⟩ : syracuseStep 3185081 = 2388811) B2388811
theorem B1415611 : Blo 1415527 1415611 := bstep (se 1 (by rfl) ⟨1061708, by rfl⟩ : syracuseStep 1415611 = 2123417) B2123417
theorem B1415687 : Blo 1415527 1415687 := bstep (se 1 (by rfl) ⟨1061765, by rfl⟩ : syracuseStep 1415687 = 2123531) B2123531
theorem B1415695 : Blo 1415527 1415695 := bstep (se 1 (by rfl) ⟨1061771, by rfl⟩ : syracuseStep 1415695 = 2123543) B2123543
theorem B1415739 : Blo 1415527 1415739 := bstep (se 1 (by rfl) ⟨1061804, by rfl⟩ : syracuseStep 1415739 = 2123609) B2123609
theorem B3586619 : Blo 1415527 3586619 := bstep (se 1 (by rfl) ⟨2689964, by rfl⟩ : syracuseStep 3586619 = 5379929) B5379929
theorem B15309377 : Blo 1415527 15309377 := bstep (se 2 (by rfl) ⟨5741016, by rfl⟩ : syracuseStep 15309377 = 11482033) B11482033
theorem B1792631 : Blo 1415527 1792631 := bstep (se 1 (by rfl) ⟨1344473, by rfl⟩ : syracuseStep 1792631 = 2688947) B2688947
theorem B2390647 : Blo 1415527 2390647 := bstep (se 1 (by rfl) ⟨1792985, by rfl⟩ : syracuseStep 2390647 = 3585971) B3585971
theorem B36821623 : Blo 1415527 36821623 := bstep (se 1 (by rfl) ⟨27616217, by rfl⟩ : syracuseStep 36821623 = 55232435) B55232435
theorem B1415815 : Blo 1415527 1415815 := bstep (se 1 (by rfl) ⟨1061861, by rfl⟩ : syracuseStep 1415815 = 2123723) B2123723
theorem B1415823 : Blo 1415527 1415823 := bstep (se 1 (by rfl) ⟨1061867, by rfl⟩ : syracuseStep 1415823 = 2123735) B2123735
theorem B1415867 : Blo 1415527 1415867 := bstep (se 1 (by rfl) ⟨1061900, by rfl⟩ : syracuseStep 1415867 = 2123801) B2123801
theorem B13605569 : Blo 1415527 13605569 := bstep (se 2 (by rfl) ⟨5102088, by rfl⟩ : syracuseStep 13605569 = 10204177) B10204177
theorem B265149125 : Blo 1415527 265149125 := bstep (se 4 (by rfl) ⟨24857730, by rfl⟩ : syracuseStep 265149125 = 49715461) B49715461
theorem B5905133 : Blo 1415527 5905133 := bstep (se 3 (by rfl) ⟨1107212, by rfl⟩ : syracuseStep 5905133 = 2214425) B2214425
theorem B1415943 : Blo 1415527 1415943 := bstep (se 1 (by rfl) ⟨1061957, by rfl⟩ : syracuseStep 1415943 = 2123915) B2123915
theorem B3185423 : Blo 1415527 3185423 := bstep (se 1 (by rfl) ⟨2389067, by rfl⟩ : syracuseStep 3185423 = 4778135) B4778135
theorem B1415951 : Blo 1415527 1415951 := bstep (se 1 (by rfl) ⟨1061963, by rfl⟩ : syracuseStep 1415951 = 2123927) B2123927
theorem B1792783 : Blo 1415527 1792783 := bstep (se 1 (by rfl) ⟨1344587, by rfl⟩ : syracuseStep 1792783 = 2689175) B2689175
theorem B3185441 : Blo 1415527 3185441 := bstep (se 2 (by rfl) ⟨1194540, by rfl⟩ : syracuseStep 3185441 = 2389081) B2389081
theorem B1415995 : Blo 1415527 1415995 := bstep (se 1 (by rfl) ⟨1061996, by rfl⟩ : syracuseStep 1415995 = 2123993) B2123993
theorem B2390843 : Blo 1415527 2390843 := bstep (se 1 (by rfl) ⟨1793132, by rfl⟩ : syracuseStep 2390843 = 3586265) B3586265
theorem B1416071 : Blo 1415527 1416071 := bstep (se 1 (by rfl) ⟨1062053, by rfl⟩ : syracuseStep 1416071 = 2124107) B2124107
theorem B1416079 : Blo 1415527 1416079 := bstep (se 1 (by rfl) ⟨1062059, by rfl⟩ : syracuseStep 1416079 = 2124119) B2124119
theorem B3586963 : Blo 1415527 3586963 := bstep (se 1 (by rfl) ⟨2690222, by rfl⟩ : syracuseStep 3586963 = 5380445) B5380445
theorem B4782995 : Blo 1415527 4782995 := bstep (se 1 (by rfl) ⟨3587246, by rfl⟩ : syracuseStep 4782995 = 7174493) B7174493
theorem B8068025 : Blo 1415527 8068025 := bstep (se 2 (by rfl) ⟨3025509, by rfl⟩ : syracuseStep 8068025 = 6051019) B6051019
theorem B1416123 : Blo 1415527 1416123 := bstep (se 1 (by rfl) ⟨1062092, by rfl⟩ : syracuseStep 1416123 = 2124185) B2124185
theorem B1792955 : Blo 1415527 1792955 := bstep (se 1 (by rfl) ⟨1344716, by rfl⟩ : syracuseStep 1792955 = 2689433) B2689433
theorem B1416199 : Blo 1415527 1416199 := bstep (se 1 (by rfl) ⟨1062149, by rfl⟩ : syracuseStep 1416199 = 2124299) B2124299
theorem B1416207 : Blo 1415527 1416207 := bstep (se 1 (by rfl) ⟨1062155, by rfl⟩ : syracuseStep 1416207 = 2124311) B2124311
theorem B3587105 : Blo 1415527 3587105 := bstep (se 2 (by rfl) ⟨1345164, by rfl⟩ : syracuseStep 3587105 = 2690329) B2690329
theorem B1416251 : Blo 1415527 1416251 := bstep (se 1 (by rfl) ⟨1062188, by rfl⟩ : syracuseStep 1416251 = 2124377) B2124377
theorem B3185783 : Blo 1415527 3185783 := bstep (se 1 (by rfl) ⟨2389337, by rfl⟩ : syracuseStep 3185783 = 4778675) B4778675
theorem B1416327 : Blo 1415527 1416327 := bstep (se 1 (by rfl) ⟨1062245, by rfl⟩ : syracuseStep 1416327 = 2124491) B2124491
theorem B1416335 : Blo 1415527 1416335 := bstep (se 1 (by rfl) ⟨1062251, by rfl⟩ : syracuseStep 1416335 = 2124503) B2124503
theorem B1416379 : Blo 1415527 1416379 := bstep (se 1 (by rfl) ⟨1062284, by rfl⟩ : syracuseStep 1416379 = 2124569) B2124569
theorem B2391241 : Blo 1415527 2391241 := bstep (se 2 (by rfl) ⟨896715, by rfl⟩ : syracuseStep 2391241 = 1793431) B1793431
theorem B1416455 : Blo 1415527 1416455 := bstep (se 1 (by rfl) ⟨1062341, by rfl⟩ : syracuseStep 1416455 = 2124683) B2124683
theorem B1416463 : Blo 1415527 1416463 := bstep (se 1 (by rfl) ⟨1062347, by rfl⟩ : syracuseStep 1416463 = 2124695) B2124695
theorem B3185963 : Blo 1415527 3185963 := bstep (se 1 (by rfl) ⟨2389472, by rfl⟩ : syracuseStep 3185963 = 4778945) B4778945
theorem B1416507 : Blo 1415527 1416507 := bstep (se 1 (by rfl) ⟨1062380, by rfl⟩ : syracuseStep 1416507 = 2124761) B2124761
theorem B1416583 : Blo 1415527 1416583 := bstep (se 1 (by rfl) ⟨1062437, by rfl⟩ : syracuseStep 1416583 = 2124875) B2124875
theorem B1416591 : Blo 1415527 1416591 := bstep (se 1 (by rfl) ⟨1062443, by rfl⟩ : syracuseStep 1416591 = 2124887) B2124887
theorem B2153899 : Blo 1415527 2153899 := bstep (se 1 (by rfl) ⟨1615424, by rfl⟩ : syracuseStep 2153899 = 3230849) B3230849
theorem B1416635 : Blo 1415527 1416635 := bstep (se 1 (by rfl) ⟨1062476, by rfl⟩ : syracuseStep 1416635 = 2124953) B2124953
theorem B7175627 : Blo 1415527 7175627 := bstep (se 1 (by rfl) ⟨5381720, by rfl⟩ : syracuseStep 7175627 = 10763441) B10763441
theorem B5381585 : Blo 1415527 5381585 := bstep (se 2 (by rfl) ⟨2018094, by rfl⟩ : syracuseStep 5381585 = 4036189) B4036189
theorem B1416711 : Blo 1415527 1416711 := bstep (se 1 (by rfl) ⟨1062533, by rfl⟩ : syracuseStep 1416711 = 2125067) B2125067
theorem B1416719 : Blo 1415527 1416719 := bstep (se 1 (by rfl) ⟨1062539, by rfl⟩ : syracuseStep 1416719 = 2125079) B2125079
theorem B1416763 : Blo 1415527 1416763 := bstep (se 1 (by rfl) ⟨1062572, by rfl⟩ : syracuseStep 1416763 = 2125145) B2125145
theorem B4087415 : Blo 1415527 4087415 := bstep (se 1 (by rfl) ⟨3065561, by rfl⟩ : syracuseStep 4087415 = 6131123) B6131123
theorem B1416839 : Blo 1415527 1416839 := bstep (se 1 (by rfl) ⟨1062629, by rfl⟩ : syracuseStep 1416839 = 2125259) B2125259
theorem B1416847 : Blo 1415527 1416847 := bstep (se 1 (by rfl) ⟨1062635, by rfl⟩ : syracuseStep 1416847 = 2125271) B2125271
theorem B3186323 : Blo 1415527 3186323 := bstep (se 1 (by rfl) ⟨2389742, by rfl⟩ : syracuseStep 3186323 = 4779485) B4779485
theorem B1416891 : Blo 1415527 1416891 := bstep (se 1 (by rfl) ⟨1062668, by rfl⟩ : syracuseStep 1416891 = 2125337) B2125337
theorem B7167689 : Blo 1415527 7167689 := bstep (se 2 (by rfl) ⟨2687883, by rfl⟩ : syracuseStep 7167689 = 5375767) B5375767
theorem B3186377 : Blo 1415527 3186377 := bstep (se 2 (by rfl) ⟨1194891, by rfl⟩ : syracuseStep 3186377 = 2389783) B2389783
theorem B1416967 : Blo 1415527 1416967 := bstep (se 1 (by rfl) ⟨1062725, by rfl⟩ : syracuseStep 1416967 = 2125451) B2125451
theorem B1416975 : Blo 1415527 1416975 := bstep (se 1 (by rfl) ⟨1062731, by rfl⟩ : syracuseStep 1416975 = 2125463) B2125463
theorem B5381903 : Blo 1415527 5381903 := bstep (se 1 (by rfl) ⟨4036427, by rfl⟩ : syracuseStep 5381903 = 8072855) B8072855
theorem B7175951 : Blo 1415527 7175951 := bstep (se 1 (by rfl) ⟨5381963, by rfl⟩ : syracuseStep 7175951 = 10763927) B10763927
theorem B1417019 : Blo 1415527 1417019 := bstep (se 1 (by rfl) ⟨1062764, by rfl⟩ : syracuseStep 1417019 = 2125529) B2125529
theorem B1417095 : Blo 1415527 1417095 := bstep (se 1 (by rfl) ⟨1062821, by rfl⟩ : syracuseStep 1417095 = 2125643) B2125643
theorem B1793927 : Blo 1415527 1793927 := bstep (se 1 (by rfl) ⟨1345445, by rfl⟩ : syracuseStep 1793927 = 2690891) B2690891
theorem B2391943 : Blo 1415527 2391943 := bstep (se 1 (by rfl) ⟨1793957, by rfl⟩ : syracuseStep 2391943 = 3587915) B3587915
theorem B1417103 : Blo 1415527 1417103 := bstep (se 1 (by rfl) ⟨1062827, by rfl⟩ : syracuseStep 1417103 = 2125655) B2125655
theorem B1417147 : Blo 1415527 1417147 := bstep (se 1 (by rfl) ⟨1062860, by rfl⟩ : syracuseStep 1417147 = 2125721) B2125721
theorem B11493323 : Blo 1415527 11493323 := bstep (se 1 (by rfl) ⟨8619992, by rfl⟩ : syracuseStep 11493323 = 17239985) B17239985
theorem B4784129 : Blo 1415527 4784129 := bstep (se 2 (by rfl) ⟨1794048, by rfl⟩ : syracuseStep 4784129 = 3588097) B3588097
theorem B1417255 : Blo 1415527 1417255 := bstep (se 1 (by rfl) ⟨1062941, by rfl⟩ : syracuseStep 1417255 = 2125883) B2125883
theorem B1417295 : Blo 1415527 1417295 := bstep (se 1 (by rfl) ⟨1062971, by rfl⟩ : syracuseStep 1417295 = 2125943) B2125943
theorem B1417311 : Blo 1415527 1417311 := bstep (se 1 (by rfl) ⟨1062983, by rfl⟩ : syracuseStep 1417311 = 2125967) B2125967
theorem B1417339 : Blo 1415527 1417339 := bstep (se 1 (by rfl) ⟨1063004, by rfl⟩ : syracuseStep 1417339 = 2126009) B2126009
theorem B4538521 : Blo 1415527 4538521 := bstep (se 2 (by rfl) ⟨1701945, by rfl⟩ : syracuseStep 4538521 = 3403891) B3403891
theorem B1417391 : Blo 1415527 1417391 := bstep (se 1 (by rfl) ⟨1063043, by rfl⟩ : syracuseStep 1417391 = 2126087) B2126087
theorem B1417415 : Blo 1415527 1417415 := bstep (se 1 (by rfl) ⟨1063061, by rfl⟩ : syracuseStep 1417415 = 2126123) B2126123
theorem B1417435 : Blo 1415527 1417435 := bstep (se 1 (by rfl) ⟨1063076, by rfl⟩ : syracuseStep 1417435 = 2126153) B2126153
theorem B3186935 : Blo 1415527 3186935 := bstep (se 1 (by rfl) ⟨2390201, by rfl⟩ : syracuseStep 3186935 = 4780403) B4780403
theorem B12099851 : Blo 1415527 12099851 := bstep (se 1 (by rfl) ⟨9074888, by rfl⟩ : syracuseStep 12099851 = 18149777) B18149777
theorem B1417511 : Blo 1415527 1417511 := bstep (se 1 (by rfl) ⟨1063133, by rfl⟩ : syracuseStep 1417511 = 2126267) B2126267
theorem B20709701 : Blo 1415527 20709701 := bstep (se 4 (by rfl) ⟨1941534, by rfl⟩ : syracuseStep 20709701 = 3883069) B3883069
theorem B8069665 : Blo 1415527 8069665 := bstep (se 2 (by rfl) ⟨3026124, by rfl⟩ : syracuseStep 8069665 = 6052249) B6052249
theorem B4792891 : Blo 1415527 4792891 := bstep (se 1 (by rfl) ⟨3594668, by rfl⟩ : syracuseStep 4792891 = 7189337) B7189337
theorem B10216145 : Blo 1415527 10216145 := bstep (se 2 (by rfl) ⟨3831054, by rfl⟩ : syracuseStep 10216145 = 7662109) B7662109
theorem B3187529 : Blo 1415527 3187529 := bstep (se 2 (by rfl) ⟨1195323, by rfl⟩ : syracuseStep 3187529 = 2390647) B2390647
theorem B49095497 : Blo 1415527 49095497 := bstep (se 2 (by rfl) ⟨18410811, by rfl⟩ : syracuseStep 49095497 = 36821623) B36821623
theorem B2016095 : Blo 1415527 2016095 := bstep (se 1 (by rfl) ⟨1512071, by rfl⟩ : syracuseStep 2016095 = 3024143) B3024143
theorem B10347371 : Blo 1415527 10347371 := bstep (se 1 (by rfl) ⟨7760528, by rfl⟩ : syracuseStep 10347371 = 15521057) B15521057
theorem B34456427 : Blo 1415527 34456427 := bstep (se 1 (by rfl) ⟨25842320, by rfl⟩ : syracuseStep 34456427 = 51684641) B51684641
theorem B37323787 : Blo 1415527 37323787 := bstep (se 1 (by rfl) ⟨27992840, by rfl⟩ : syracuseStep 37323787 = 55985681) B55985681
theorem B4031507 : Blo 1415527 4031507 := bstep (se 1 (by rfl) ⟨3023630, by rfl⟩ : syracuseStep 4031507 = 6047261) B6047261
theorem B6808627 : Blo 1415527 6808627 := bstep (se 1 (by rfl) ⟨5106470, by rfl⟩ : syracuseStep 6808627 = 10212941) B10212941
theorem B13608107 : Blo 1415527 13608107 := bstep (se 1 (by rfl) ⟨10206080, by rfl⟩ : syracuseStep 13608107 = 20412161) B20412161
theorem B2016505 : Blo 1415527 2016505 := bstep (se 2 (by rfl) ⟨756189, by rfl⟩ : syracuseStep 2016505 = 1512379) B1512379
theorem B4031849 : Blo 1415527 4031849 := bstep (se 2 (by rfl) ⟨1511943, by rfl⟩ : syracuseStep 4031849 = 3023887) B3023887
theorem B10749347 : Blo 1415527 10749347 := bstep (se 1 (by rfl) ⟨8062010, by rfl⟩ : syracuseStep 10749347 = 16124021) B16124021
theorem B4031963 : Blo 1415527 4031963 := bstep (se 1 (by rfl) ⟨3023972, by rfl⟩ : syracuseStep 4031963 = 6047945) B6047945
theorem B2123303 : Blo 1415527 2123303 := bstep (se 1 (by rfl) ⟨1592477, by rfl⟩ : syracuseStep 2123303 = 3184955) B3184955
theorem B2016847 : Blo 1415527 2016847 := bstep (se 1 (by rfl) ⟨1512635, by rfl⟩ : syracuseStep 2016847 = 3025271) B3025271
theorem B5375585 : Blo 1415527 5375585 := bstep (se 2 (by rfl) ⟨2015844, by rfl⟩ : syracuseStep 5375585 = 4031689) B4031689
theorem B7169633 : Blo 1415527 7169633 := bstep (se 2 (by rfl) ⟨2688612, by rfl⟩ : syracuseStep 7169633 = 5377225) B5377225
theorem B3188321 : Blo 1415527 3188321 := bstep (se 2 (by rfl) ⟨1195620, by rfl⟩ : syracuseStep 3188321 = 2391241) B2391241
theorem B4777595 : Blo 1415527 4777595 := bstep (se 1 (by rfl) ⟨3583196, by rfl⟩ : syracuseStep 4777595 = 7166393) B7166393
theorem B2123387 : Blo 1415527 2123387 := bstep (se 1 (by rfl) ⟨1592540, by rfl⟩ : syracuseStep 2123387 = 3185081) B3185081
theorem B2123513 : Blo 1415527 2123513 := bstep (se 2 (by rfl) ⟨796317, by rfl⟩ : syracuseStep 2123513 = 1592635) B1592635
theorem B4777757 : Blo 1415527 4777757 := bstep (se 3 (by rfl) ⟨895829, by rfl⟩ : syracuseStep 4777757 = 1791659) B1791659
theorem B9070379 : Blo 1415527 9070379 := bstep (se 1 (by rfl) ⟨6802784, by rfl⟩ : syracuseStep 9070379 = 13605569) B13605569
theorem B2123615 : Blo 1415527 2123615 := bstep (se 1 (by rfl) ⟨1592711, by rfl⟩ : syracuseStep 2123615 = 3185423) B3185423
theorem B2123627 : Blo 1415527 2123627 := bstep (se 1 (by rfl) ⟨1592720, by rfl⟩ : syracuseStep 2123627 = 3185441) B3185441
theorem B3188663 : Blo 1415527 3188663 := bstep (se 1 (by rfl) ⟨2391497, by rfl⟩ : syracuseStep 3188663 = 4782995) B4782995
theorem B22972369 : Blo 1415527 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B2689031 : Blo 1415527 2689031 := bstep (se 1 (by rfl) ⟨2016773, by rfl⟩ : syracuseStep 2689031 = 4033547) B4033547
theorem B2123855 : Blo 1415527 2123855 := bstep (se 1 (by rfl) ⟨1592891, by rfl⟩ : syracuseStep 2123855 = 3185783) B3185783
theorem B2123975 : Blo 1415527 2123975 := bstep (se 1 (by rfl) ⟨1592981, by rfl⟩ : syracuseStep 2123975 = 3185963) B3185963
theorem B2124137 : Blo 1415527 2124137 := bstep (se 2 (by rfl) ⟨796551, by rfl⟩ : syracuseStep 2124137 = 1593103) B1593103
theorem B18155927 : Blo 1415527 18155927 := bstep (se 1 (by rfl) ⟨13616945, by rfl⟩ : syracuseStep 18155927 = 27233891) B27233891
theorem B2124215 : Blo 1415527 2124215 := bstep (se 1 (by rfl) ⟨1593161, by rfl⟩ : syracuseStep 2124215 = 3186323) B3186323
theorem B2689463 : Blo 1415527 2689463 := bstep (se 1 (by rfl) ⟨2017097, by rfl⟩ : syracuseStep 2689463 = 4034195) B4034195
theorem B4778459 : Blo 1415527 4778459 := bstep (se 1 (by rfl) ⟨3583844, by rfl⟩ : syracuseStep 4778459 = 7167689) B7167689
theorem B2124251 : Blo 1415527 2124251 := bstep (se 1 (by rfl) ⟨1593188, by rfl⟩ : syracuseStep 2124251 = 3186377) B3186377
theorem B3189257 : Blo 1415527 3189257 := bstep (se 2 (by rfl) ⟨1195971, by rfl⟩ : syracuseStep 3189257 = 2391943) B2391943
theorem B2689615 : Blo 1415527 2689615 := bstep (se 1 (by rfl) ⟨2017211, by rfl⟩ : syracuseStep 2689615 = 4034423) B4034423
theorem B4033147 : Blo 1415527 4033147 := bstep (se 1 (by rfl) ⟨3024860, by rfl⟩ : syracuseStep 4033147 = 6049721) B6049721
theorem B7662215 : Blo 1415527 7662215 := bstep (se 1 (by rfl) ⟨5746661, by rfl⟩ : syracuseStep 7662215 = 11493323) B11493323
theorem B19376819 : Blo 1415527 19376819 := bstep (se 1 (by rfl) ⟨14532614, by rfl⟩ : syracuseStep 19376819 = 29065229) B29065229
theorem B4033273 : Blo 1415527 4033273 := bstep (se 2 (by rfl) ⟨1512477, by rfl⟩ : syracuseStep 4033273 = 3024955) B3024955
theorem B1436455 : Blo 1415527 1436455 := bstep (se 1 (by rfl) ⟨1077341, by rfl⟩ : syracuseStep 1436455 = 2154683) B2154683
theorem B2124719 : Blo 1415527 2124719 := bstep (se 1 (by rfl) ⟨1593539, by rfl⟩ : syracuseStep 2124719 = 3187079) B3187079
theorem B6048695 : Blo 1415527 6048695 := bstep (se 1 (by rfl) ⟨4536521, by rfl⟩ : syracuseStep 6048695 = 9073043) B9073043
theorem B6810551 : Blo 1415527 6810551 := bstep (se 1 (by rfl) ⟨5107913, by rfl⟩ : syracuseStep 6810551 = 10215827) B10215827
theorem B17239013 : Blo 1415527 17239013 := bstep (se 4 (by rfl) ⟨1616157, by rfl⟩ : syracuseStep 17239013 = 3232315) B3232315
theorem B2124809 : Blo 1415527 2124809 := bstep (se 2 (by rfl) ⟨796803, by rfl⟩ : syracuseStep 2124809 = 1593607) B1593607
theorem B5377043 : Blo 1415527 5377043 := bstep (se 1 (by rfl) ⟨4032782, by rfl⟩ : syracuseStep 5377043 = 8065565) B8065565
theorem B7171091 : Blo 1415527 7171091 := bstep (se 1 (by rfl) ⟨5378318, by rfl⟩ : syracuseStep 7171091 = 10756637) B10756637
theorem B2124839 : Blo 1415527 2124839 := bstep (se 1 (by rfl) ⟨1593629, by rfl⟩ : syracuseStep 2124839 = 3187259) B3187259
theorem B3583055 : Blo 1415527 3583055 := bstep (se 1 (by rfl) ⟨2687291, by rfl⟩ : syracuseStep 3583055 = 5374583) B5374583
theorem B2124923 : Blo 1415527 2124923 := bstep (se 1 (by rfl) ⟨1593692, by rfl⟩ : syracuseStep 2124923 = 3187385) B3187385
theorem B4779161 : Blo 1415527 4779161 := bstep (se 2 (by rfl) ⟨1792185, by rfl⟩ : syracuseStep 4779161 = 3584371) B3584371
theorem B7654603 : Blo 1415527 7654603 := bstep (se 1 (by rfl) ⟨5740952, by rfl⟩ : syracuseStep 7654603 = 11481905) B11481905
theorem B2125049 : Blo 1415527 2125049 := bstep (se 2 (by rfl) ⟨796893, by rfl⟩ : syracuseStep 2125049 = 1593787) B1593787
theorem B1592671 : Blo 1415527 1592671 := bstep (se 1 (by rfl) ⟨1194503, by rfl⟩ : syracuseStep 1592671 = 2389007) B2389007
theorem B2125151 : Blo 1415527 2125151 := bstep (se 1 (by rfl) ⟨1593863, by rfl⟩ : syracuseStep 2125151 = 3187727) B3187727
theorem B5107049 : Blo 1415527 5107049 := bstep (se 2 (by rfl) ⟨1915143, by rfl⟩ : syracuseStep 5107049 = 3830287) B3830287
theorem B2125163 : Blo 1415527 2125163 := bstep (se 1 (by rfl) ⟨1593872, by rfl⟩ : syracuseStep 2125163 = 3187745) B3187745
theorem B6802861 : Blo 1415527 6802861 := bstep (se 3 (by rfl) ⟨1275536, by rfl⟩ : syracuseStep 6802861 = 2551073) B2551073
theorem B5377499 : Blo 1415527 5377499 := bstep (se 1 (by rfl) ⟨4033124, by rfl⟩ : syracuseStep 5377499 = 8066249) B8066249
theorem B16125479 : Blo 1415527 16125479 := bstep (se 1 (by rfl) ⟨12094109, by rfl⟩ : syracuseStep 16125479 = 24188219) B24188219
theorem B2125391 : Blo 1415527 2125391 := bstep (se 1 (by rfl) ⟨1594043, by rfl⟩ : syracuseStep 2125391 = 3188087) B3188087
theorem B1593031 : Blo 1415527 1593031 := bstep (se 1 (by rfl) ⟨1194773, by rfl⟩ : syracuseStep 1593031 = 2389547) B2389547
theorem B2125511 : Blo 1415527 2125511 := bstep (se 1 (by rfl) ⟨1594133, by rfl⟩ : syracuseStep 2125511 = 3188267) B3188267
theorem B3583703 : Blo 1415527 3583703 := bstep (se 1 (by rfl) ⟨2687777, by rfl⟩ : syracuseStep 3583703 = 5375555) B5375555
theorem B10751777 : Blo 1415527 10751777 := bstep (se 2 (by rfl) ⟨4031916, by rfl⟩ : syracuseStep 10751777 = 8063833) B8063833
theorem B4034377 : Blo 1415527 4034377 := bstep (se 2 (by rfl) ⟨1512891, by rfl⟩ : syracuseStep 4034377 = 3025783) B3025783
theorem B2125673 : Blo 1415527 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B2690921 : Blo 1415527 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B2125751 : Blo 1415527 2125751 := bstep (se 1 (by rfl) ⟨1594313, by rfl⟩ : syracuseStep 2125751 = 3188627) B3188627
theorem B2125787 : Blo 1415527 2125787 := bstep (se 1 (by rfl) ⟨1594340, by rfl⟩ : syracuseStep 2125787 = 3188681) B3188681
theorem B3026963 : Blo 1415527 3026963 := bstep (se 1 (by rfl) ⟨2270222, by rfl⟩ : syracuseStep 3026963 = 4540445) B4540445
theorem B5451857 : Blo 1415527 5451857 := bstep (se 2 (by rfl) ⟨2044446, by rfl⟩ : syracuseStep 5451857 = 4088893) B4088893
theorem B4034731 : Blo 1415527 4034731 := bstep (se 1 (by rfl) ⟨3026048, by rfl⟩ : syracuseStep 4034731 = 6052097) B6052097
theorem B8065291 : Blo 1415527 8065291 := bstep (se 1 (by rfl) ⟨6048968, by rfl⟩ : syracuseStep 8065291 = 12097937) B12097937
theorem B4780349 : Blo 1415527 4780349 := bstep (se 3 (by rfl) ⟨896315, by rfl⟩ : syracuseStep 4780349 = 1792631) B1792631
theorem B2126255 : Blo 1415527 2126255 := bstep (se 1 (by rfl) ⟨1594691, by rfl⟩ : syracuseStep 2126255 = 3189383) B3189383
theorem B3936755 : Blo 1415527 3936755 := bstep (se 1 (by rfl) ⟨2952566, by rfl⟩ : syracuseStep 3936755 = 5905133) B5905133
theorem B1593895 : Blo 1415527 1593895 := bstep (se 1 (by rfl) ⟨1195421, by rfl⟩ : syracuseStep 1593895 = 2390843) B2390843
theorem B2871865 : Blo 1415527 2871865 := bstep (se 2 (by rfl) ⟨1076949, by rfl⟩ : syracuseStep 2871865 = 2153899) B2153899
theorem B5378683 : Blo 1415527 5378683 := bstep (se 1 (by rfl) ⟨4034012, by rfl⟩ : syracuseStep 5378683 = 8068025) B8068025
theorem B4534973 : Blo 1415527 4534973 := bstep (se 3 (by rfl) ⟨850307, by rfl⟩ : syracuseStep 4534973 = 1700615) B1700615
theorem B3404537 : Blo 1415527 3404537 := bstep (se 2 (by rfl) ⟨1276701, by rfl⟩ : syracuseStep 3404537 = 2553403) B2553403
theorem B20427673 : Blo 1415527 20427673 := bstep (se 2 (by rfl) ⟨7660377, by rfl⟩ : syracuseStep 20427673 = 15320755) B15320755
theorem B2388919 : Blo 1415527 2388919 := bstep (se 1 (by rfl) ⟨1791689, by rfl⟩ : syracuseStep 2388919 = 3583379) B3583379
theorem B1455067 : Blo 1415527 1455067 := bstep (se 1 (by rfl) ⟨1091300, by rfl⟩ : syracuseStep 1455067 = 2182601) B2182601
theorem B19928065 : Blo 1415527 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B2724943 : Blo 1415527 2724943 := bstep (se 1 (by rfl) ⟨2043707, by rfl⟩ : syracuseStep 2724943 = 4087415) B4087415
theorem B5903441 : Blo 1415527 5903441 := bstep (se 2 (by rfl) ⟨2213790, by rfl⟩ : syracuseStep 5903441 = 4427581) B4427581
theorem B2389115 : Blo 1415527 2389115 := bstep (se 1 (by rfl) ⟨1791836, by rfl⟩ : syracuseStep 2389115 = 3583673) B3583673
theorem B4781213 : Blo 1415527 4781213 := bstep (se 3 (by rfl) ⟨896477, by rfl⟩ : syracuseStep 4781213 = 1792955) B1792955
theorem B9074045 : Blo 1415527 9074045 := bstep (se 3 (by rfl) ⟨1701383, by rfl⟩ : syracuseStep 9074045 = 3402767) B3402767
theorem B18150803 : Blo 1415527 18150803 := bstep (se 1 (by rfl) ⟨13613102, by rfl⟩ : syracuseStep 18150803 = 27226205) B27226205
theorem B16135685 : Blo 1415527 16135685 := bstep (se 4 (by rfl) ⟨1512720, by rfl⟩ : syracuseStep 16135685 = 3025441) B3025441
theorem B2389513 : Blo 1415527 2389513 := bstep (se 2 (by rfl) ⟨896067, by rfl⟩ : syracuseStep 2389513 = 1792135) B1792135
theorem B19650059 : Blo 1415527 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B33166945 : Blo 1415527 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B2389675 : Blo 1415527 2389675 := bstep (se 1 (by rfl) ⟨1792256, by rfl⟩ : syracuseStep 2389675 = 3584513) B3584513
theorem B4781753 : Blo 1415527 4781753 := bstep (se 2 (by rfl) ⟨1793157, by rfl⟩ : syracuseStep 4781753 = 3586315) B3586315
theorem B8066749 : Blo 1415527 8066749 := bstep (se 3 (by rfl) ⟨1512515, by rfl⟩ : syracuseStep 8066749 = 3025031) B3025031
theorem B11646713 : Blo 1415527 11646713 := bstep (se 2 (by rfl) ⟨4367517, by rfl⟩ : syracuseStep 11646713 = 8735035) B8735035
theorem B2873161 : Blo 1415527 2873161 := bstep (se 2 (by rfl) ⟨1077435, by rfl⟩ : syracuseStep 2873161 = 2154871) B2154871
theorem B5379959 : Blo 1415527 5379959 := bstep (se 1 (by rfl) ⟨4034969, by rfl⟩ : syracuseStep 5379959 = 8069939) B8069939
theorem B7174007 : Blo 1415527 7174007 := bstep (se 1 (by rfl) ⟨5380505, by rfl⟩ : syracuseStep 7174007 = 10761011) B10761011
theorem B2389979 : Blo 1415527 2389979 := bstep (se 1 (by rfl) ⟨1792484, by rfl⟩ : syracuseStep 2389979 = 3584969) B3584969
theorem B1792039 : Blo 1415527 1792039 := bstep (se 1 (by rfl) ⟨1344029, by rfl⟩ : syracuseStep 1792039 = 2688059) B2688059
theorem B8173649 : Blo 1415527 8173649 := bstep (se 2 (by rfl) ⟨3065118, by rfl⟩ : syracuseStep 8173649 = 6130237) B6130237
theorem B2390215 : Blo 1415527 2390215 := bstep (se 1 (by rfl) ⟨1792661, by rfl⟩ : syracuseStep 2390215 = 3585323) B3585323
theorem B10762469 : Blo 1415527 10762469 := bstep (se 4 (by rfl) ⟨1008981, by rfl⟩ : syracuseStep 10762469 = 2017963) B2017963
theorem B3586295 : Blo 1415527 3586295 := bstep (se 1 (by rfl) ⟨2689721, by rfl⟩ : syracuseStep 3586295 = 5379443) B5379443
theorem B4782347 : Blo 1415527 4782347 := bstep (se 1 (by rfl) ⟨3586760, by rfl⟩ : syracuseStep 4782347 = 7173521) B7173521
theorem B2390377 : Blo 1415527 2390377 := bstep (se 2 (by rfl) ⟨896391, by rfl⟩ : syracuseStep 2390377 = 1792783) B1792783
theorem B1792363 : Blo 1415527 1792363 := bstep (se 1 (by rfl) ⟨1344272, by rfl⟩ : syracuseStep 1792363 = 2688545) B2688545
theorem B1415547 : Blo 1415527 1415547 := bstep (se 1 (by rfl) ⟨1061660, by rfl⟩ : syracuseStep 1415547 = 2123321) B2123321
theorem B1415599 : Blo 1415527 1415599 := bstep (se 1 (by rfl) ⟨1061699, by rfl⟩ : syracuseStep 1415599 = 2123399) B2123399
theorem B1415623 : Blo 1415527 1415623 := bstep (se 1 (by rfl) ⟨1061717, by rfl⟩ : syracuseStep 1415623 = 2123435) B2123435
theorem B1415643 : Blo 1415527 1415643 := bstep (se 1 (by rfl) ⟨1061732, by rfl⟩ : syracuseStep 1415643 = 2123465) B2123465
theorem B4782617 : Blo 1415527 4782617 := bstep (se 2 (by rfl) ⟨1793481, by rfl⟩ : syracuseStep 4782617 = 3586963) B3586963
theorem B1415719 : Blo 1415527 1415719 := bstep (se 1 (by rfl) ⟨1061789, by rfl⟩ : syracuseStep 1415719 = 2123579) B2123579
theorem B5388839 : Blo 1415527 5388839 := bstep (se 1 (by rfl) ⟨4041629, by rfl⟩ : syracuseStep 5388839 = 8083259) B8083259
theorem B1415759 : Blo 1415527 1415759 := bstep (se 1 (by rfl) ⟨1061819, by rfl⟩ : syracuseStep 1415759 = 2123639) B2123639
theorem B1415775 : Blo 1415527 1415775 := bstep (se 1 (by rfl) ⟨1061831, by rfl⟩ : syracuseStep 1415775 = 2123663) B2123663
theorem B1415803 : Blo 1415527 1415803 := bstep (se 1 (by rfl) ⟨1061852, by rfl⟩ : syracuseStep 1415803 = 2123705) B2123705
theorem B1415855 : Blo 1415527 1415855 := bstep (se 1 (by rfl) ⟨1061891, by rfl⟩ : syracuseStep 1415855 = 2123783) B2123783
theorem B3185351 : Blo 1415527 3185351 := bstep (se 1 (by rfl) ⟨2389013, by rfl⟩ : syracuseStep 3185351 = 4778027) B4778027
theorem B1415879 : Blo 1415527 1415879 := bstep (se 1 (by rfl) ⟨1061909, by rfl⟩ : syracuseStep 1415879 = 2123819) B2123819
theorem B1415899 : Blo 1415527 1415899 := bstep (se 1 (by rfl) ⟨1061924, by rfl⟩ : syracuseStep 1415899 = 2123849) B2123849
theorem B1415975 : Blo 1415527 1415975 := bstep (se 1 (by rfl) ⟨1061981, by rfl⟩ : syracuseStep 1415975 = 2123963) B2123963
theorem B5380931 : Blo 1415527 5380931 := bstep (se 1 (by rfl) ⟨4035698, by rfl⟩ : syracuseStep 5380931 = 8071397) B8071397
theorem B1416015 : Blo 1415527 1416015 := bstep (se 1 (by rfl) ⟨1062011, by rfl⟩ : syracuseStep 1416015 = 2124023) B2124023
theorem B1416031 : Blo 1415527 1416031 := bstep (se 1 (by rfl) ⟨1062023, by rfl⟩ : syracuseStep 1416031 = 2124047) B2124047
theorem B1416059 : Blo 1415527 1416059 := bstep (se 1 (by rfl) ⟨1062044, by rfl⟩ : syracuseStep 1416059 = 2124089) B2124089
theorem B1416111 : Blo 1415527 1416111 := bstep (se 1 (by rfl) ⟨1062083, by rfl⟩ : syracuseStep 1416111 = 2124167) B2124167
theorem B16137143 : Blo 1415527 16137143 := bstep (se 1 (by rfl) ⟨12102857, by rfl⟩ : syracuseStep 16137143 = 24205715) B24205715
theorem B2390971 : Blo 1415527 2390971 := bstep (se 1 (by rfl) ⟨1793228, by rfl⟩ : syracuseStep 2390971 = 3586457) B3586457
theorem B1416135 : Blo 1415527 1416135 := bstep (se 1 (by rfl) ⟨1062101, by rfl⟩ : syracuseStep 1416135 = 2124203) B2124203
theorem B1416155 : Blo 1415527 1416155 := bstep (se 1 (by rfl) ⟨1062116, by rfl⟩ : syracuseStep 1416155 = 2124233) B2124233
theorem B9075685 : Blo 1415527 9075685 := bstep (se 4 (by rfl) ⟨850845, by rfl⟩ : syracuseStep 9075685 = 1701691) B1701691
theorem B1416231 : Blo 1415527 1416231 := bstep (se 1 (by rfl) ⟨1062173, by rfl⟩ : syracuseStep 1416231 = 2124347) B2124347
theorem B2391079 : Blo 1415527 2391079 := bstep (se 1 (by rfl) ⟨1793309, by rfl⟩ : syracuseStep 2391079 = 3586619) B3586619
theorem B10206251 : Blo 1415527 10206251 := bstep (se 1 (by rfl) ⟨7654688, by rfl⟩ : syracuseStep 10206251 = 15309377) B15309377
theorem B1416271 : Blo 1415527 1416271 := bstep (se 1 (by rfl) ⟨1062203, by rfl⟩ : syracuseStep 1416271 = 2124407) B2124407
theorem B1416287 : Blo 1415527 1416287 := bstep (se 1 (by rfl) ⟨1062215, by rfl⟩ : syracuseStep 1416287 = 2124431) B2124431
theorem B1416315 : Blo 1415527 1416315 := bstep (se 1 (by rfl) ⟨1062236, by rfl⟩ : syracuseStep 1416315 = 2124473) B2124473
theorem B176766083 : Blo 1415527 176766083 := bstep (se 1 (by rfl) ⟨132574562, by rfl⟩ : syracuseStep 176766083 = 265149125) B265149125
theorem B1416367 : Blo 1415527 1416367 := bstep (se 1 (by rfl) ⟨1062275, by rfl⟩ : syracuseStep 1416367 = 2124551) B2124551
theorem B1416391 : Blo 1415527 1416391 := bstep (se 1 (by rfl) ⟨1062293, by rfl⟩ : syracuseStep 1416391 = 2124587) B2124587
theorem B1416411 : Blo 1415527 1416411 := bstep (se 1 (by rfl) ⟨1062308, by rfl⟩ : syracuseStep 1416411 = 2124617) B2124617
theorem B5381387 : Blo 1415527 5381387 := bstep (se 1 (by rfl) ⟨4036040, by rfl⟩ : syracuseStep 5381387 = 8072081) B8072081
theorem B1416487 : Blo 1415527 1416487 := bstep (se 1 (by rfl) ⟨1062365, by rfl⟩ : syracuseStep 1416487 = 2124731) B2124731
theorem B1416527 : Blo 1415527 1416527 := bstep (se 1 (by rfl) ⟨1062395, by rfl⟩ : syracuseStep 1416527 = 2124791) B2124791
theorem B1416543 : Blo 1415527 1416543 := bstep (se 1 (by rfl) ⟨1062407, by rfl⟩ : syracuseStep 1416543 = 2124815) B2124815
theorem B2391403 : Blo 1415527 2391403 := bstep (se 1 (by rfl) ⟨1793552, by rfl⟩ : syracuseStep 2391403 = 3587105) B3587105
theorem B1416571 : Blo 1415527 1416571 := bstep (se 1 (by rfl) ⟨1062428, by rfl⟩ : syracuseStep 1416571 = 2124857) B2124857
theorem B1416623 : Blo 1415527 1416623 := bstep (se 1 (by rfl) ⟨1062467, by rfl⟩ : syracuseStep 1416623 = 2124935) B2124935
theorem B1416647 : Blo 1415527 1416647 := bstep (se 1 (by rfl) ⟨1062485, by rfl⟩ : syracuseStep 1416647 = 2124971) B2124971
theorem B1416667 : Blo 1415527 1416667 := bstep (se 1 (by rfl) ⟨1062500, by rfl⟩ : syracuseStep 1416667 = 2125001) B2125001
theorem B7658995 : Blo 1415527 7658995 := bstep (se 1 (by rfl) ⟨5744246, by rfl⟩ : syracuseStep 7658995 = 11488493) B11488493
theorem B7167527 : Blo 1415527 7167527 := bstep (se 1 (by rfl) ⟨5375645, by rfl⟩ : syracuseStep 7167527 = 10751291) B10751291
theorem B3186215 : Blo 1415527 3186215 := bstep (se 1 (by rfl) ⟨2389661, by rfl⟩ : syracuseStep 3186215 = 4779323) B4779323
theorem B1416743 : Blo 1415527 1416743 := bstep (se 1 (by rfl) ⟨1062557, by rfl⟩ : syracuseStep 1416743 = 2125115) B2125115
theorem B1416783 : Blo 1415527 1416783 := bstep (se 1 (by rfl) ⟨1062587, by rfl⟩ : syracuseStep 1416783 = 2125175) B2125175
theorem B1416799 : Blo 1415527 1416799 := bstep (se 1 (by rfl) ⟨1062599, by rfl⟩ : syracuseStep 1416799 = 2125199) B2125199
theorem B1416827 : Blo 1415527 1416827 := bstep (se 1 (by rfl) ⟨1062620, by rfl⟩ : syracuseStep 1416827 = 2125241) B2125241
theorem B1793659 : Blo 1415527 1793659 := bstep (se 1 (by rfl) ⟨1345244, by rfl⟩ : syracuseStep 1793659 = 2690489) B2690489
theorem B4783751 : Blo 1415527 4783751 := bstep (se 1 (by rfl) ⟨3587813, by rfl⟩ : syracuseStep 4783751 = 7175627) B7175627
theorem B3587723 : Blo 1415527 3587723 := bstep (se 1 (by rfl) ⟨2690792, by rfl⟩ : syracuseStep 3587723 = 5381585) B5381585
theorem B1416879 : Blo 1415527 1416879 := bstep (se 1 (by rfl) ⟨1062659, by rfl⟩ : syracuseStep 1416879 = 2125319) B2125319
theorem B4783805 : Blo 1415527 4783805 := bstep (se 3 (by rfl) ⟨896963, by rfl⟩ : syracuseStep 4783805 = 1793927) B1793927
theorem B1416903 : Blo 1415527 1416903 := bstep (se 1 (by rfl) ⟨1062677, by rfl⟩ : syracuseStep 1416903 = 2125355) B2125355
theorem B1416923 : Blo 1415527 1416923 := bstep (se 1 (by rfl) ⟨1062692, by rfl⟩ : syracuseStep 1416923 = 2125385) B2125385
theorem B33169133 : Blo 1415527 33169133 := bstep (se 3 (by rfl) ⟨6219212, by rfl⟩ : syracuseStep 33169133 = 12438425) B12438425
theorem B1416999 : Blo 1415527 1416999 := bstep (se 1 (by rfl) ⟨1062749, by rfl⟩ : syracuseStep 1416999 = 2125499) B2125499
theorem B8609579 : Blo 1415527 8609579 := bstep (se 1 (by rfl) ⟨6457184, by rfl⟩ : syracuseStep 8609579 = 12914369) B12914369
theorem B1417039 : Blo 1415527 1417039 := bstep (se 1 (by rfl) ⟨1062779, by rfl⟩ : syracuseStep 1417039 = 2125559) B2125559
theorem B1417055 : Blo 1415527 1417055 := bstep (se 1 (by rfl) ⟨1062791, by rfl⟩ : syracuseStep 1417055 = 2125583) B2125583
theorem B3587935 : Blo 1415527 3587935 := bstep (se 1 (by rfl) ⟨2690951, by rfl⟩ : syracuseStep 3587935 = 5381903) B5381903
theorem B4783967 : Blo 1415527 4783967 := bstep (se 1 (by rfl) ⟨3587975, by rfl⟩ : syracuseStep 4783967 = 7175951) B7175951
theorem B3186539 : Blo 1415527 3186539 := bstep (se 1 (by rfl) ⟨2389904, by rfl⟩ : syracuseStep 3186539 = 4779809) B4779809
theorem B1417083 : Blo 1415527 1417083 := bstep (se 1 (by rfl) ⟨1062812, by rfl⟩ : syracuseStep 1417083 = 2125625) B2125625
theorem B3186593 : Blo 1415527 3186593 := bstep (se 2 (by rfl) ⟨1194972, by rfl⟩ : syracuseStep 3186593 = 2389945) B2389945
theorem B1417135 : Blo 1415527 1417135 := bstep (se 1 (by rfl) ⟨1062851, by rfl⟩ : syracuseStep 1417135 = 2125703) B2125703
theorem B5382071 : Blo 1415527 5382071 := bstep (se 1 (by rfl) ⟨4036553, by rfl⟩ : syracuseStep 5382071 = 8073107) B8073107
theorem B1417159 : Blo 1415527 1417159 := bstep (se 1 (by rfl) ⟨1062869, by rfl⟩ : syracuseStep 1417159 = 2125739) B2125739
theorem B1417179 : Blo 1415527 1417179 := bstep (se 1 (by rfl) ⟨1062884, by rfl⟩ : syracuseStep 1417179 = 2125769) B2125769
theorem B3186899 : Blo 1415527 3186899 := bstep (se 1 (by rfl) ⟨2390174, by rfl⟩ : syracuseStep 3186899 = 4780349) B4780349
theorem B3186953 : Blo 1415527 3186953 := bstep (se 2 (by rfl) ⟨1195107, by rfl⟩ : syracuseStep 3186953 = 2390215) B2390215
theorem B1417503 : Blo 1415527 1417503 := bstep (se 1 (by rfl) ⟨1063127, by rfl⟩ : syracuseStep 1417503 = 2126255) B2126255
theorem B3023315 : Blo 1415527 3023315 := bstep (se 1 (by rfl) ⟨2267486, by rfl⟩ : syracuseStep 3023315 = 4534973) B4534973
theorem B3187169 : Blo 1415527 3187169 := bstep (se 2 (by rfl) ⟨1195188, by rfl⟩ : syracuseStep 3187169 = 2390377) B2390377
theorem B2269691 : Blo 1415527 2269691 := bstep (se 1 (by rfl) ⟨1702268, by rfl⟩ : syracuseStep 2269691 = 3404537) B3404537
theorem B6898247 : Blo 1415527 6898247 := bstep (se 1 (by rfl) ⟨5173685, by rfl⟩ : syracuseStep 6898247 = 10347371) B10347371
theorem B22970951 : Blo 1415527 22970951 := bstep (se 1 (by rfl) ⟨17228213, by rfl⟩ : syracuseStep 22970951 = 34456427) B34456427
theorem B2687671 : Blo 1415527 2687671 := bstep (se 1 (by rfl) ⟨2015753, by rfl⟩ : syracuseStep 2687671 = 4031507) B4031507
theorem B6390521 : Blo 1415527 6390521 := bstep (se 2 (by rfl) ⟨2396445, by rfl⟩ : syracuseStep 6390521 = 4792891) B4792891
theorem B3187475 : Blo 1415527 3187475 := bstep (se 1 (by rfl) ⟨2390606, by rfl⟩ : syracuseStep 3187475 = 4781213) B4781213
theorem B2687899 : Blo 1415527 2687899 := bstep (se 1 (by rfl) ⟨2015924, by rfl⟩ : syracuseStep 2687899 = 4031849) B4031849
theorem B12100535 : Blo 1415527 12100535 := bstep (se 1 (by rfl) ⟨9075401, by rfl⟩ : syracuseStep 12100535 = 18150803) B18150803
theorem B2687975 : Blo 1415527 2687975 := bstep (se 1 (by rfl) ⟨2015981, by rfl⟩ : syracuseStep 2687975 = 4031963) B4031963
theorem B10757123 : Blo 1415527 10757123 := bstep (se 1 (by rfl) ⟨8067842, by rfl⟩ : syracuseStep 10757123 = 16135685) B16135685
theorem B13100039 : Blo 1415527 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B3187835 : Blo 1415527 3187835 := bstep (se 1 (by rfl) ⟨2390876, by rfl⟩ : syracuseStep 3187835 = 4781753) B4781753
theorem B6046919 : Blo 1415527 6046919 := bstep (se 1 (by rfl) ⟨4535189, by rfl⟩ : syracuseStep 6046919 = 9070379) B9070379
theorem B3187961 : Blo 1415527 3187961 := bstep (se 2 (by rfl) ⟨1195485, by rfl⟩ : syracuseStep 3187961 = 2390971) B2390971
theorem B12100913 : Blo 1415527 12100913 := bstep (se 2 (by rfl) ⟨4537842, by rfl⟩ : syracuseStep 12100913 = 9075685) B9075685
theorem B3188105 : Blo 1415527 3188105 := bstep (se 2 (by rfl) ⟨1195539, by rfl⟩ : syracuseStep 3188105 = 2391079) B2391079
theorem B5449099 : Blo 1415527 5449099 := bstep (se 1 (by rfl) ⟨4086824, by rfl⟩ : syracuseStep 5449099 = 8173649) B8173649
theorem B9078169 : Blo 1415527 9078169 := bstep (se 2 (by rfl) ⟨3404313, by rfl⟩ : syracuseStep 9078169 = 6808627) B6808627
theorem B3188231 : Blo 1415527 3188231 := bstep (se 1 (by rfl) ⟨2391173, by rfl⟩ : syracuseStep 3188231 = 4782347) B4782347
theorem B3188411 : Blo 1415527 3188411 := bstep (se 1 (by rfl) ⟨2391308, by rfl⟩ : syracuseStep 3188411 = 4782617) B4782617
theorem B20432573 : Blo 1415527 20432573 := bstep (se 3 (by rfl) ⟨3831107, by rfl⟩ : syracuseStep 20432573 = 7662215) B7662215
theorem B2123561 : Blo 1415527 2123561 := bstep (se 2 (by rfl) ⟨796335, by rfl⟩ : syracuseStep 2123561 = 1592671) B1592671
theorem B2123567 : Blo 1415527 2123567 := bstep (se 1 (by rfl) ⟨1592675, by rfl⟩ : syracuseStep 2123567 = 3185351) B3185351
theorem B3188537 : Blo 1415527 3188537 := bstep (se 2 (by rfl) ⟨1195701, by rfl⟩ : syracuseStep 3188537 = 2391403) B2391403
theorem B9070481 : Blo 1415527 9070481 := bstep (se 2 (by rfl) ⟨3401430, by rfl⟩ : syracuseStep 9070481 = 6802861) B6802861
theorem B88451021 : Blo 1415527 88451021 := bstep (se 3 (by rfl) ⟨16584566, by rfl⟩ : syracuseStep 88451021 = 33169133) B33169133
theorem B10758095 : Blo 1415527 10758095 := bstep (se 1 (by rfl) ⟨8068571, by rfl⟩ : syracuseStep 10758095 = 16137143) B16137143
theorem B4540367 : Blo 1415527 4540367 := bstep (se 1 (by rfl) ⟨3405275, by rfl⟩ : syracuseStep 4540367 = 6810551) B6810551
theorem B31057901 : Blo 1415527 31057901 := bstep (se 3 (by rfl) ⟨5823356, by rfl⟩ : syracuseStep 31057901 = 11646713) B11646713
theorem B117844055 : Blo 1415527 117844055 := bstep (se 1 (by rfl) ⟨88383041, by rfl⟩ : syracuseStep 117844055 = 176766083) B176766083
theorem B2689129 : Blo 1415527 2689129 := bstep (se 2 (by rfl) ⟨1008423, by rfl⟩ : syracuseStep 2689129 = 2016847) B2016847
theorem B44222593 : Blo 1415527 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B5376253 : Blo 1415527 5376253 := bstep (se 3 (by rfl) ⟨1008047, by rfl⟩ : syracuseStep 5376253 = 2016095) B2016095
theorem B2124041 : Blo 1415527 2124041 := bstep (se 2 (by rfl) ⟨796515, by rfl⟩ : syracuseStep 2124041 = 1593031) B1593031
theorem B10750319 : Blo 1415527 10750319 := bstep (se 1 (by rfl) ⟨8062739, by rfl⟩ : syracuseStep 10750319 = 16125479) B16125479
theorem B4778351 : Blo 1415527 4778351 := bstep (se 1 (by rfl) ⟨3583763, by rfl⟩ : syracuseStep 4778351 = 7167527) B7167527
theorem B2124143 : Blo 1415527 2124143 := bstep (se 1 (by rfl) ⟨1593107, by rfl⟩ : syracuseStep 2124143 = 3186215) B3186215
theorem B3189167 : Blo 1415527 3189167 := bstep (se 1 (by rfl) ⟨2391875, by rfl⟩ : syracuseStep 3189167 = 4783751) B4783751
theorem B3189203 : Blo 1415527 3189203 := bstep (se 1 (by rfl) ⟨2391902, by rfl⟩ : syracuseStep 3189203 = 4783805) B4783805
theorem B3189311 : Blo 1415527 3189311 := bstep (se 1 (by rfl) ⟨2391983, by rfl⟩ : syracuseStep 3189311 = 4783967) B4783967
theorem B2124359 : Blo 1415527 2124359 := bstep (se 1 (by rfl) ⟨1593269, by rfl⟩ : syracuseStep 2124359 = 3186539) B3186539
theorem B2124395 : Blo 1415527 2124395 := bstep (se 1 (by rfl) ⟨1593296, by rfl⟩ : syracuseStep 2124395 = 3186593) B3186593
theorem B3189419 : Blo 1415527 3189419 := bstep (se 1 (by rfl) ⟨2392064, by rfl⟩ : syracuseStep 3189419 = 4784129) B4784129
theorem B2017975 : Blo 1415527 2017975 := bstep (se 1 (by rfl) ⟨1513481, by rfl⟩ : syracuseStep 2017975 = 3026963) B3026963
theorem B2124623 : Blo 1415527 2124623 := bstep (se 1 (by rfl) ⟨1593467, by rfl⟩ : syracuseStep 2124623 = 3186935) B3186935
theorem B13806467 : Blo 1415527 13806467 := bstep (se 1 (by rfl) ⟨10354850, by rfl⟩ : syracuseStep 13806467 = 20709701) B20709701
theorem B2624503 : Blo 1415527 2624503 := bstep (se 1 (by rfl) ⟨1968377, by rfl⟩ : syracuseStep 2624503 = 3936755) B3936755
theorem B6810763 : Blo 1415527 6810763 := bstep (se 1 (by rfl) ⟨5108072, by rfl⟩ : syracuseStep 6810763 = 10216145) B10216145
theorem B2125019 : Blo 1415527 2125019 := bstep (se 1 (by rfl) ⟨1593764, by rfl⟩ : syracuseStep 2125019 = 3187529) B3187529
theorem B32730331 : Blo 1415527 32730331 := bstep (se 1 (by rfl) ⟨24547748, by rfl⟩ : syracuseStep 32730331 = 49095497) B49095497
theorem B10759553 : Blo 1415527 10759553 := bstep (se 2 (by rfl) ⟨4034832, by rfl⟩ : syracuseStep 10759553 = 8069665) B8069665
theorem B2125193 : Blo 1415527 2125193 := bstep (se 2 (by rfl) ⟨796947, by rfl⟩ : syracuseStep 2125193 = 1593895) B1593895
theorem B3935627 : Blo 1415527 3935627 := bstep (se 1 (by rfl) ⟨2951720, by rfl⟩ : syracuseStep 3935627 = 5903441) B5903441
theorem B3829153 : Blo 1415527 3829153 := bstep (se 2 (by rfl) ⟨1435932, by rfl⟩ : syracuseStep 3829153 = 2871865) B2871865
theorem B1592743 : Blo 1415527 1592743 := bstep (se 1 (by rfl) ⟨1194557, by rfl⟩ : syracuseStep 1592743 = 2389115) B2389115
theorem B9072071 : Blo 1415527 9072071 := bstep (se 1 (by rfl) ⟨6804053, by rfl⟩ : syracuseStep 9072071 = 13608107) B13608107
theorem B5377529 : Blo 1415527 5377529 := bstep (se 2 (by rfl) ⟨2016573, by rfl⟩ : syracuseStep 5377529 = 4033147) B4033147
theorem B7171577 : Blo 1415527 7171577 := bstep (se 2 (by rfl) ⟨2689341, by rfl⟩ : syracuseStep 7171577 = 5378683) B5378683
theorem B6049363 : Blo 1415527 6049363 := bstep (se 1 (by rfl) ⟨4537022, by rfl⟩ : syracuseStep 6049363 = 9074045) B9074045
theorem B5377697 : Blo 1415527 5377697 := bstep (se 2 (by rfl) ⟨2016636, by rfl⟩ : syracuseStep 5377697 = 4033273) B4033273
theorem B3583723 : Blo 1415527 3583723 := bstep (se 1 (by rfl) ⟨2687792, by rfl⟩ : syracuseStep 3583723 = 5375585) B5375585
theorem B4779755 : Blo 1415527 4779755 := bstep (se 1 (by rfl) ⟨3584816, by rfl⟩ : syracuseStep 4779755 = 7169633) B7169633
theorem B2125547 : Blo 1415527 2125547 := bstep (se 1 (by rfl) ⟨1594160, by rfl⟩ : syracuseStep 2125547 = 3188321) B3188321
theorem B7171901 : Blo 1415527 7171901 := bstep (se 3 (by rfl) ⟨1344731, by rfl⟩ : syracuseStep 7171901 = 2689463) B2689463
theorem B2125775 : Blo 1415527 2125775 := bstep (se 1 (by rfl) ⟨1594331, by rfl⟩ : syracuseStep 2125775 = 3188663) B3188663
theorem B1593319 : Blo 1415527 1593319 := bstep (se 1 (by rfl) ⟨1194989, by rfl⟩ : syracuseStep 1593319 = 2389979) B2389979
theorem B26570753 : Blo 1415527 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B3633257 : Blo 1415527 3633257 := bstep (se 2 (by rfl) ⟨1362471, by rfl⟩ : syracuseStep 3633257 = 2724943) B2724943
theorem B12103951 : Blo 1415527 12103951 := bstep (se 1 (by rfl) ⟨9077963, by rfl⟩ : syracuseStep 12103951 = 18155927) B18155927
theorem B2126171 : Blo 1415527 2126171 := bstep (se 1 (by rfl) ⟨1594628, by rfl⟩ : syracuseStep 2126171 = 3189257) B3189257
theorem B3592559 : Blo 1415527 3592559 := bstep (se 1 (by rfl) ⟨2694419, by rfl⟩ : syracuseStep 3592559 = 5388839) B5388839
theorem B15323525 : Blo 1415527 15323525 := bstep (se 4 (by rfl) ⟨1436580, by rfl⟩ : syracuseStep 15323525 = 2873161) B2873161
theorem B10211993 : Blo 1415527 10211993 := bstep (se 2 (by rfl) ⟨3829497, by rfl⟩ : syracuseStep 10211993 = 7658995) B7658995
theorem B3584695 : Blo 1415527 3584695 := bstep (se 1 (by rfl) ⟨2688521, by rfl⟩ : syracuseStep 3584695 = 5377043) B5377043
theorem B4780727 : Blo 1415527 4780727 := bstep (se 1 (by rfl) ⟨3585545, by rfl⟩ : syracuseStep 4780727 = 7171091) B7171091
theorem B6804167 : Blo 1415527 6804167 := bstep (se 1 (by rfl) ⟨5103125, by rfl⟩ : syracuseStep 6804167 = 10206251) B10206251
theorem B2388703 : Blo 1415527 2388703 := bstep (se 1 (by rfl) ⟨1791527, by rfl⟩ : syracuseStep 2388703 = 3583055) B3583055
theorem B3404699 : Blo 1415527 3404699 := bstep (se 1 (by rfl) ⟨2553524, by rfl⟩ : syracuseStep 3404699 = 5107049) B5107049
theorem B3584999 : Blo 1415527 3584999 := bstep (se 1 (by rfl) ⟨2688749, by rfl⟩ : syracuseStep 3584999 = 5377499) B5377499
theorem B5379169 : Blo 1415527 5379169 := bstep (se 2 (by rfl) ⟨2017188, by rfl⟩ : syracuseStep 5379169 = 4034377) B4034377
theorem B2389135 : Blo 1415527 2389135 := bstep (se 1 (by rfl) ⟨1791851, by rfl⟩ : syracuseStep 2389135 = 3583703) B3583703
theorem B5739719 : Blo 1415527 5739719 := bstep (se 1 (by rfl) ⟨4304789, by rfl⟩ : syracuseStep 5739719 = 8609579) B8609579
theorem B2389385 : Blo 1415527 2389385 := bstep (se 2 (by rfl) ⟨896019, by rfl⟩ : syracuseStep 2389385 = 1792039) B1792039
theorem B3634571 : Blo 1415527 3634571 := bstep (se 1 (by rfl) ⟨2725928, by rfl⟩ : syracuseStep 3634571 = 5451857) B5451857
theorem B8066567 : Blo 1415527 8066567 := bstep (se 1 (by rfl) ⟨6049925, by rfl⟩ : syracuseStep 8066567 = 12099851) B12099851
theorem B6051361 : Blo 1415527 6051361 := bstep (se 2 (by rfl) ⟨2269260, by rfl⟩ : syracuseStep 6051361 = 4538521) B4538521
theorem B5379641 : Blo 1415527 5379641 := bstep (se 2 (by rfl) ⟨2017365, by rfl⟩ : syracuseStep 5379641 = 4034731) B4034731
theorem B10753721 : Blo 1415527 10753721 := bstep (se 2 (by rfl) ⟨4032645, by rfl⟩ : syracuseStep 10753721 = 8065291) B8065291
theorem B2389817 : Blo 1415527 2389817 := bstep (se 2 (by rfl) ⟨896181, by rfl⟩ : syracuseStep 2389817 = 1792363) B1792363
theorem B3586153 : Blo 1415527 3586153 := bstep (se 2 (by rfl) ⟨1344807, by rfl⟩ : syracuseStep 3586153 = 2689615) B2689615
theorem B7166231 : Blo 1415527 7166231 := bstep (se 1 (by rfl) ⟨5374673, by rfl⟩ : syracuseStep 7166231 = 10749347) B10749347
theorem B1415535 : Blo 1415527 1415535 := bstep (se 1 (by rfl) ⟨1061651, by rfl⟩ : syracuseStep 1415535 = 2123303) B2123303
theorem B1915273 : Blo 1415527 1915273 := bstep (se 2 (by rfl) ⟨718227, by rfl⟩ : syracuseStep 1915273 = 1436455) B1436455
theorem B3185063 : Blo 1415527 3185063 := bstep (se 1 (by rfl) ⟨2388797, by rfl⟩ : syracuseStep 3185063 = 4777595) B4777595
theorem B1415591 : Blo 1415527 1415591 := bstep (se 1 (by rfl) ⟨1061693, by rfl⟩ : syracuseStep 1415591 = 2123387) B2123387
theorem B1415675 : Blo 1415527 1415675 := bstep (se 1 (by rfl) ⟨1061756, by rfl⟩ : syracuseStep 1415675 = 2123513) B2123513
theorem B3185171 : Blo 1415527 3185171 := bstep (se 1 (by rfl) ⟨2388878, by rfl⟩ : syracuseStep 3185171 = 4777757) B4777757
theorem B27236897 : Blo 1415527 27236897 := bstep (se 2 (by rfl) ⟨10213836, by rfl⟩ : syracuseStep 27236897 = 20427673) B20427673
theorem B1415743 : Blo 1415527 1415743 := bstep (se 1 (by rfl) ⟨1061807, by rfl⟩ : syracuseStep 1415743 = 2123615) B2123615
theorem B1415751 : Blo 1415527 1415751 := bstep (se 1 (by rfl) ⟨1061813, by rfl⟩ : syracuseStep 1415751 = 2123627) B2123627
theorem B3185225 : Blo 1415527 3185225 := bstep (se 2 (by rfl) ⟨1194459, by rfl⟩ : syracuseStep 3185225 = 2388919) B2388919
theorem B3586639 : Blo 1415527 3586639 := bstep (se 1 (by rfl) ⟨2689979, by rfl⟩ : syracuseStep 3586639 = 5379959) B5379959
theorem B4782671 : Blo 1415527 4782671 := bstep (se 1 (by rfl) ⟨3587003, by rfl⟩ : syracuseStep 4782671 = 7174007) B7174007
theorem B1940089 : Blo 1415527 1940089 := bstep (se 2 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 1940089 = 1455067) B1455067
theorem B10754693 : Blo 1415527 10754693 := bstep (se 4 (by rfl) ⟨1008252, by rfl⟩ : syracuseStep 10754693 = 2016505) B2016505
theorem B1792687 : Blo 1415527 1792687 := bstep (se 1 (by rfl) ⟨1344515, by rfl⟩ : syracuseStep 1792687 = 2689031) B2689031
theorem B49765049 : Blo 1415527 49765049 := bstep (se 2 (by rfl) ⟨18661893, by rfl⟩ : syracuseStep 49765049 = 37323787) B37323787
theorem B1415903 : Blo 1415527 1415903 := bstep (se 1 (by rfl) ⟨1061927, by rfl⟩ : syracuseStep 1415903 = 2123855) B2123855
theorem B1415983 : Blo 1415527 1415983 := bstep (se 1 (by rfl) ⟨1061987, by rfl⟩ : syracuseStep 1415983 = 2123975) B2123975
theorem B7174979 : Blo 1415527 7174979 := bstep (se 1 (by rfl) ⟨5381234, by rfl⟩ : syracuseStep 7174979 = 10762469) B10762469
theorem B2390863 : Blo 1415527 2390863 := bstep (se 1 (by rfl) ⟨1793147, by rfl⟩ : syracuseStep 2390863 = 3586295) B3586295
theorem B1416091 : Blo 1415527 1416091 := bstep (se 1 (by rfl) ⟨1062068, by rfl⟩ : syracuseStep 1416091 = 2124137) B2124137
theorem B10206137 : Blo 1415527 10206137 := bstep (se 2 (by rfl) ⟨3827301, by rfl⟩ : syracuseStep 10206137 = 7654603) B7654603
theorem B1416143 : Blo 1415527 1416143 := bstep (se 1 (by rfl) ⟨1062107, by rfl⟩ : syracuseStep 1416143 = 2124215) B2124215
theorem B3185639 : Blo 1415527 3185639 := bstep (se 1 (by rfl) ⟨2389229, by rfl⟩ : syracuseStep 3185639 = 4778459) B4778459
theorem B1416167 : Blo 1415527 1416167 := bstep (se 1 (by rfl) ⟨1062125, by rfl⟩ : syracuseStep 1416167 = 2124251) B2124251
theorem B12917879 : Blo 1415527 12917879 := bstep (se 1 (by rfl) ⟨9688409, by rfl⟩ : syracuseStep 12917879 = 19376819) B19376819
theorem B3587287 : Blo 1415527 3587287 := bstep (se 1 (by rfl) ⟨2690465, by rfl⟩ : syracuseStep 3587287 = 5380931) B5380931
theorem B1416479 : Blo 1415527 1416479 := bstep (se 1 (by rfl) ⟨1062359, by rfl⟩ : syracuseStep 1416479 = 2124719) B2124719
theorem B11492675 : Blo 1415527 11492675 := bstep (se 1 (by rfl) ⟨8619506, by rfl⟩ : syracuseStep 11492675 = 17239013) B17239013
theorem B1416539 : Blo 1415527 1416539 := bstep (se 1 (by rfl) ⟨1062404, by rfl⟩ : syracuseStep 1416539 = 2124809) B2124809
theorem B3186017 : Blo 1415527 3186017 := bstep (se 2 (by rfl) ⟨1194756, by rfl⟩ : syracuseStep 3186017 = 2389513) B2389513
theorem B1416559 : Blo 1415527 1416559 := bstep (se 1 (by rfl) ⟨1062419, by rfl⟩ : syracuseStep 1416559 = 2124839) B2124839
theorem B1416615 : Blo 1415527 1416615 := bstep (se 1 (by rfl) ⟨1062461, by rfl⟩ : syracuseStep 1416615 = 2124923) B2124923
theorem B3186107 : Blo 1415527 3186107 := bstep (se 1 (by rfl) ⟨2389580, by rfl⟩ : syracuseStep 3186107 = 4779161) B4779161
theorem B2391545 : Blo 1415527 2391545 := bstep (se 2 (by rfl) ⟨896829, by rfl⟩ : syracuseStep 2391545 = 1793659) B1793659
theorem B1416699 : Blo 1415527 1416699 := bstep (se 1 (by rfl) ⟨1062524, by rfl⟩ : syracuseStep 1416699 = 2125049) B2125049
theorem B3587591 : Blo 1415527 3587591 := bstep (se 1 (by rfl) ⟨2690693, by rfl⟩ : syracuseStep 3587591 = 5381387) B5381387
theorem B3186233 : Blo 1415527 3186233 := bstep (se 2 (by rfl) ⟨1194837, by rfl⟩ : syracuseStep 3186233 = 2389675) B2389675
theorem B1416767 : Blo 1415527 1416767 := bstep (se 1 (by rfl) ⟨1062575, by rfl⟩ : syracuseStep 1416767 = 2125151) B2125151
theorem B1416775 : Blo 1415527 1416775 := bstep (se 1 (by rfl) ⟨1062581, by rfl⟩ : syracuseStep 1416775 = 2125163) B2125163
theorem B10755665 : Blo 1415527 10755665 := bstep (se 2 (by rfl) ⟨4033374, by rfl⟩ : syracuseStep 10755665 = 8066749) B8066749
theorem B7175789 : Blo 1415527 7175789 := bstep (se 3 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 7175789 = 2690921) B2690921
theorem B1416927 : Blo 1415527 1416927 := bstep (se 1 (by rfl) ⟨1062695, by rfl⟩ : syracuseStep 1416927 = 2125391) B2125391
theorem B2391815 : Blo 1415527 2391815 := bstep (se 1 (by rfl) ⟨1793861, by rfl⟩ : syracuseStep 2391815 = 3587723) B3587723
theorem B4783913 : Blo 1415527 4783913 := bstep (se 2 (by rfl) ⟨1793967, by rfl⟩ : syracuseStep 4783913 = 3587935) B3587935
theorem B1417007 : Blo 1415527 1417007 := bstep (se 1 (by rfl) ⟨1062755, by rfl⟩ : syracuseStep 1417007 = 2125511) B2125511
theorem B16129853 : Blo 1415527 16129853 := bstep (se 3 (by rfl) ⟨3024347, by rfl⟩ : syracuseStep 16129853 = 6048695) B6048695
theorem B7167851 : Blo 1415527 7167851 := bstep (se 1 (by rfl) ⟨5375888, by rfl⟩ : syracuseStep 7167851 = 10751777) B10751777
theorem B1417115 : Blo 1415527 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B30629825 : Blo 1415527 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B1417167 : Blo 1415527 1417167 := bstep (se 1 (by rfl) ⟨1062875, by rfl⟩ : syracuseStep 1417167 = 2125751) B2125751
theorem B3588047 : Blo 1415527 3588047 := bstep (se 1 (by rfl) ⟨2691035, by rfl⟩ : syracuseStep 3588047 = 5382071) B5382071
theorem B1417191 : Blo 1415527 1417191 := bstep (se 1 (by rfl) ⟨1062893, by rfl⟩ : syracuseStep 1417191 = 2125787) B2125787
theorem B1417447 : Blo 1415527 1417447 := bstep (se 1 (by rfl) ⟨1063085, by rfl⟩ : syracuseStep 1417447 = 2126171) B2126171
theorem B10215683 : Blo 1415527 10215683 := bstep (se 1 (by rfl) ⟨7661762, by rfl⟩ : syracuseStep 10215683 = 15323525) B15323525
theorem B2015543 : Blo 1415527 2015543 := bstep (se 1 (by rfl) ⟨1511657, by rfl⟩ : syracuseStep 2015543 = 3023315) B3023315
theorem B7168337 : Blo 1415527 7168337 := bstep (se 2 (by rfl) ⟨2688126, by rfl⟩ : syracuseStep 7168337 = 5376253) B5376253
theorem B16138601 : Blo 1415527 16138601 := bstep (se 2 (by rfl) ⟨6051975, by rfl⟩ : syracuseStep 16138601 = 12103951) B12103951
theorem B6807995 : Blo 1415527 6807995 := bstep (se 1 (by rfl) ⟨5105996, by rfl⟩ : syracuseStep 6807995 = 10211993) B10211993
theorem B3187151 : Blo 1415527 3187151 := bstep (se 1 (by rfl) ⟨2390363, by rfl⟩ : syracuseStep 3187151 = 4780727) B4780727
theorem B4260347 : Blo 1415527 4260347 := bstep (se 1 (by rfl) ⟨3195260, by rfl⟩ : syracuseStep 4260347 = 6390521) B6390521
theorem B2269799 : Blo 1415527 2269799 := bstep (se 1 (by rfl) ⟨1702349, by rfl⟩ : syracuseStep 2269799 = 3404699) B3404699
theorem B8733359 : Blo 1415527 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B4031279 : Blo 1415527 4031279 := bstep (se 1 (by rfl) ⟨3023459, by rfl⟩ : syracuseStep 4031279 = 6046919) B6046919
theorem B3187817 : Blo 1415527 3187817 := bstep (se 2 (by rfl) ⟨1195431, by rfl⟩ : syracuseStep 3187817 = 2390863) B2390863
theorem B7169147 : Blo 1415527 7169147 := bstep (se 1 (by rfl) ⟨5376860, by rfl⟩ : syracuseStep 7169147 = 10753721) B10753721
theorem B6046987 : Blo 1415527 6046987 := bstep (se 1 (by rfl) ⟨4535240, by rfl⟩ : syracuseStep 6046987 = 9070481) B9070481
theorem B58967347 : Blo 1415527 58967347 := bstep (se 1 (by rfl) ⟨44225510, by rfl⟩ : syracuseStep 58967347 = 88451021) B88451021
theorem B3499337 : Blo 1415527 3499337 := bstep (se 2 (by rfl) ⟨1312251, by rfl⟩ : syracuseStep 3499337 = 2624503) B2624503
theorem B78562703 : Blo 1415527 78562703 := bstep (se 1 (by rfl) ⟨58922027, by rfl⟩ : syracuseStep 78562703 = 117844055) B117844055
theorem B4777487 : Blo 1415527 4777487 := bstep (se 1 (by rfl) ⟨3583115, by rfl⟩ : syracuseStep 4777487 = 7166231) B7166231
theorem B2123375 : Blo 1415527 2123375 := bstep (se 1 (by rfl) ⟨1592531, by rfl⟩ : syracuseStep 2123375 = 3185063) B3185063
theorem B43640441 : Blo 1415527 43640441 := bstep (se 2 (by rfl) ⟨16365165, by rfl⟩ : syracuseStep 43640441 = 32730331) B32730331
theorem B2123447 : Blo 1415527 2123447 := bstep (se 1 (by rfl) ⟨1592585, by rfl⟩ : syracuseStep 2123447 = 3185171) B3185171
theorem B2123483 : Blo 1415527 2123483 := bstep (se 1 (by rfl) ⟨1592612, by rfl⟩ : syracuseStep 2123483 = 3185225) B3185225
theorem B3188447 : Blo 1415527 3188447 := bstep (se 1 (by rfl) ⟨2391335, by rfl⟩ : syracuseStep 3188447 = 4782671) B4782671
theorem B7169795 : Blo 1415527 7169795 := bstep (se 1 (by rfl) ⟨5377346, by rfl⟩ : syracuseStep 7169795 = 10754693) B10754693
theorem B5105537 : Blo 1415527 5105537 := bstep (se 2 (by rfl) ⟨1914576, by rfl⟩ : syracuseStep 5105537 = 3829153) B3829153
theorem B2123657 : Blo 1415527 2123657 := bstep (se 2 (by rfl) ⟨796371, by rfl⟩ : syracuseStep 2123657 = 1592743) B1592743
theorem B2123759 : Blo 1415527 2123759 := bstep (se 1 (by rfl) ⟨1592819, by rfl⟩ : syracuseStep 2123759 = 3185639) B3185639
theorem B8611919 : Blo 1415527 8611919 := bstep (se 1 (by rfl) ⟨6458939, by rfl⟩ : syracuseStep 8611919 = 12917879) B12917879
theorem B7661783 : Blo 1415527 7661783 := bstep (se 1 (by rfl) ⟨5746337, by rfl⟩ : syracuseStep 7661783 = 11492675) B11492675
theorem B2124011 : Blo 1415527 2124011 := bstep (se 1 (by rfl) ⟨1593008, by rfl⟩ : syracuseStep 2124011 = 3186017) B3186017
theorem B2623751 : Blo 1415527 2623751 := bstep (se 1 (by rfl) ⟨1967813, by rfl⟩ : syracuseStep 2623751 = 3935627) B3935627
theorem B2124071 : Blo 1415527 2124071 := bstep (se 1 (by rfl) ⟨1593053, by rfl⟩ : syracuseStep 2124071 = 3186107) B3186107
theorem B6048047 : Blo 1415527 6048047 := bstep (se 1 (by rfl) ⟨4536035, by rfl⟩ : syracuseStep 6048047 = 9072071) B9072071
theorem B4778297 : Blo 1415527 4778297 := bstep (se 2 (by rfl) ⟨1791861, by rfl⟩ : syracuseStep 4778297 = 3583723) B3583723
theorem B2124155 : Blo 1415527 2124155 := bstep (se 1 (by rfl) ⟨1593116, by rfl⟩ : syracuseStep 2124155 = 3186233) B3186233
theorem B7170443 : Blo 1415527 7170443 := bstep (se 1 (by rfl) ⟨5377832, by rfl⟩ : syracuseStep 7170443 = 10755665) B10755665
theorem B41388565 : Blo 1415527 41388565 := bstep (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) B1940089
theorem B3189275 : Blo 1415527 3189275 := bstep (se 1 (by rfl) ⟨2391956, by rfl⟩ : syracuseStep 3189275 = 4783913) B4783913
theorem B4778567 : Blo 1415527 4778567 := bstep (se 1 (by rfl) ⟨3583925, by rfl⟩ : syracuseStep 4778567 = 7167851) B7167851
theorem B2124425 : Blo 1415527 2124425 := bstep (se 2 (by rfl) ⟨796659, by rfl⟩ : syracuseStep 2124425 = 1593319) B1593319
theorem B17713835 : Blo 1415527 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B2124599 : Blo 1415527 2124599 := bstep (se 1 (by rfl) ⟨1593449, by rfl⟩ : syracuseStep 2124599 = 3186899) B3186899
theorem B2124635 : Blo 1415527 2124635 := bstep (se 1 (by rfl) ⟨1593476, by rfl⟩ : syracuseStep 2124635 = 3186953) B3186953
theorem B2124779 : Blo 1415527 2124779 := bstep (se 1 (by rfl) ⟨1593584, by rfl⟩ : syracuseStep 2124779 = 3187169) B3187169
theorem B4598831 : Blo 1415527 4598831 := bstep (se 1 (by rfl) ⟨3449123, by rfl⟩ : syracuseStep 4598831 = 6898247) B6898247
theorem B15313967 : Blo 1415527 15313967 := bstep (se 1 (by rfl) ⟨11485475, by rfl⟩ : syracuseStep 15313967 = 22970951) B22970951
theorem B2124983 : Blo 1415527 2124983 := bstep (se 1 (by rfl) ⟨1593737, by rfl⟩ : syracuseStep 2124983 = 3187475) B3187475
theorem B15305917 : Blo 1415527 15305917 := bstep (se 3 (by rfl) ⟨2869859, by rfl⟩ : syracuseStep 15305917 = 5739719) B5739719
theorem B7171415 : Blo 1415527 7171415 := bstep (se 1 (by rfl) ⟨5378561, by rfl⟩ : syracuseStep 7171415 = 10757123) B10757123
theorem B2125223 : Blo 1415527 2125223 := bstep (se 1 (by rfl) ⟨1593917, by rfl⟩ : syracuseStep 2125223 = 3187835) B3187835
theorem B2125307 : Blo 1415527 2125307 := bstep (se 1 (by rfl) ⟨1593980, by rfl⟩ : syracuseStep 2125307 = 3187961) B3187961
theorem B3583561 : Blo 1415527 3583561 := bstep (se 2 (by rfl) ⟨1343835, by rfl⟩ : syracuseStep 3583561 = 2687671) B2687671
theorem B4779593 : Blo 1415527 4779593 := bstep (se 2 (by rfl) ⟨1792347, by rfl⟩ : syracuseStep 4779593 = 3584695) B3584695
theorem B2690633 : Blo 1415527 2690633 := bstep (se 2 (by rfl) ⟨1008987, by rfl⟩ : syracuseStep 2690633 = 2017975) B2017975
theorem B1592923 : Blo 1415527 1592923 := bstep (se 1 (by rfl) ⟨1194692, by rfl⟩ : syracuseStep 1592923 = 2389385) B2389385
theorem B2125403 : Blo 1415527 2125403 := bstep (se 1 (by rfl) ⟨1594052, by rfl⟩ : syracuseStep 2125403 = 3188105) B3188105
theorem B9580157 : Blo 1415527 9580157 := bstep (se 3 (by rfl) ⟨1796279, by rfl⟩ : syracuseStep 9580157 = 3592559) B3592559
theorem B5377711 : Blo 1415527 5377711 := bstep (se 1 (by rfl) ⟨4033283, by rfl⟩ : syracuseStep 5377711 = 8066567) B8066567
theorem B2125487 : Blo 1415527 2125487 := bstep (se 1 (by rfl) ⟨1594115, by rfl⟩ : syracuseStep 2125487 = 3188231) B3188231
theorem B2125607 : Blo 1415527 2125607 := bstep (se 1 (by rfl) ⟨1594205, by rfl⟩ : syracuseStep 2125607 = 3188411) B3188411
theorem B3583865 : Blo 1415527 3583865 := bstep (se 2 (by rfl) ⟨1343949, by rfl⟩ : syracuseStep 3583865 = 2687899) B2687899
theorem B1593211 : Blo 1415527 1593211 := bstep (se 1 (by rfl) ⟨1194908, by rfl⟩ : syracuseStep 1593211 = 2389817) B2389817
theorem B2125691 : Blo 1415527 2125691 := bstep (se 1 (by rfl) ⟨1594268, by rfl⟩ : syracuseStep 2125691 = 3188537) B3188537
theorem B7172063 : Blo 1415527 7172063 := bstep (se 1 (by rfl) ⟨5379047, by rfl⟩ : syracuseStep 7172063 = 10758095) B10758095
theorem B3026911 : Blo 1415527 3026911 := bstep (se 1 (by rfl) ⟨2270183, by rfl⟩ : syracuseStep 3026911 = 4540367) B4540367
theorem B20705267 : Blo 1415527 20705267 := bstep (se 1 (by rfl) ⟨15528950, by rfl⟩ : syracuseStep 20705267 = 31057901) B31057901
theorem B7172225 : Blo 1415527 7172225 := bstep (se 2 (by rfl) ⟨2689584, by rfl⟩ : syracuseStep 7172225 = 5379169) B5379169
theorem B9081017 : Blo 1415527 9081017 := bstep (se 2 (by rfl) ⟨3405381, by rfl⟩ : syracuseStep 9081017 = 6810763) B6810763
theorem B2126111 : Blo 1415527 2126111 := bstep (se 1 (by rfl) ⟨1594583, by rfl⟩ : syracuseStep 2126111 = 3189167) B3189167
theorem B2126135 : Blo 1415527 2126135 := bstep (se 1 (by rfl) ⟨1594601, by rfl⟩ : syracuseStep 2126135 = 3189203) B3189203
theorem B18157931 : Blo 1415527 18157931 := bstep (se 1 (by rfl) ⟨13618448, by rfl⟩ : syracuseStep 18157931 = 27236897) B27236897
theorem B2126207 : Blo 1415527 2126207 := bstep (se 1 (by rfl) ⟨1594655, by rfl⟩ : syracuseStep 2126207 = 3189311) B3189311
theorem B2126279 : Blo 1415527 2126279 := bstep (se 1 (by rfl) ⟨1594709, by rfl⟩ : syracuseStep 2126279 = 3189419) B3189419
theorem B12104225 : Blo 1415527 12104225 := bstep (se 2 (by rfl) ⟨4539084, by rfl⟩ : syracuseStep 12104225 = 9078169) B9078169
theorem B9204311 : Blo 1415527 9204311 := bstep (se 1 (by rfl) ⟨6903233, by rfl⟩ : syracuseStep 9204311 = 13806467) B13806467
theorem B6804091 : Blo 1415527 6804091 := bstep (se 1 (by rfl) ⟨5103068, by rfl⟩ : syracuseStep 6804091 = 10206137) B10206137
theorem B8065817 : Blo 1415527 8065817 := bstep (se 2 (by rfl) ⟨3024681, by rfl⟩ : syracuseStep 8065817 = 6049363) B6049363
theorem B7173035 : Blo 1415527 7173035 := bstep (se 1 (by rfl) ⟨5379776, by rfl⟩ : syracuseStep 7173035 = 10759553) B10759553
theorem B3585019 : Blo 1415527 3585019 := bstep (se 1 (by rfl) ⟨2688764, by rfl⟩ : syracuseStep 3585019 = 5377529) B5377529
theorem B4781051 : Blo 1415527 4781051 := bstep (se 1 (by rfl) ⟨3585788, by rfl⟩ : syracuseStep 4781051 = 7171577) B7171577
theorem B1594363 : Blo 1415527 1594363 := bstep (se 1 (by rfl) ⟨1195772, by rfl⟩ : syracuseStep 1594363 = 2391545) B2391545
theorem B3585131 : Blo 1415527 3585131 := bstep (se 1 (by rfl) ⟨2688848, by rfl⟩ : syracuseStep 3585131 = 5377697) B5377697
theorem B1594543 : Blo 1415527 1594543 := bstep (se 1 (by rfl) ⟨1195907, by rfl⟩ : syracuseStep 1594543 = 2391815) B2391815
theorem B10753235 : Blo 1415527 10753235 := bstep (se 1 (by rfl) ⟨8064926, by rfl⟩ : syracuseStep 10753235 = 16129853) B16129853
theorem B4781267 : Blo 1415527 4781267 := bstep (se 1 (by rfl) ⟨3585950, by rfl⟩ : syracuseStep 4781267 = 7171901) B7171901
theorem B20419883 : Blo 1415527 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B2422171 : Blo 1415527 2422171 := bstep (se 1 (by rfl) ⟨1816628, by rfl⟩ : syracuseStep 2422171 = 3633257) B3633257
theorem B3585505 : Blo 1415527 3585505 := bstep (se 2 (by rfl) ⟨1344564, by rfl⟩ : syracuseStep 3585505 = 2689129) B2689129
theorem B4781537 : Blo 1415527 4781537 := bstep (se 2 (by rfl) ⟨1793076, by rfl⟩ : syracuseStep 4781537 = 3586153) B3586153
theorem B58963457 : Blo 1415527 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B1513127 : Blo 1415527 1513127 := bstep (se 1 (by rfl) ⟨1134845, by rfl⟩ : syracuseStep 1513127 = 2269691) B2269691
theorem B2553697 : Blo 1415527 2553697 := bstep (se 2 (by rfl) ⟨957636, by rfl⟩ : syracuseStep 2553697 = 1915273) B1915273
theorem B8067023 : Blo 1415527 8067023 := bstep (se 1 (by rfl) ⟨6050267, by rfl⟩ : syracuseStep 8067023 = 12100535) B12100535
theorem B1791983 : Blo 1415527 1791983 := bstep (se 1 (by rfl) ⟨1343987, by rfl⟩ : syracuseStep 1791983 = 2687975) B2687975
theorem B2389999 : Blo 1415527 2389999 := bstep (se 1 (by rfl) ⟨1792499, by rfl⟩ : syracuseStep 2389999 = 3584999) B3584999
theorem B4782185 : Blo 1415527 4782185 := bstep (se 2 (by rfl) ⟨1793319, by rfl⟩ : syracuseStep 4782185 = 3586639) B3586639
theorem B8067275 : Blo 1415527 8067275 := bstep (se 1 (by rfl) ⟨6050456, by rfl⟩ : syracuseStep 8067275 = 12100913) B12100913
theorem B2390249 : Blo 1415527 2390249 := bstep (se 2 (by rfl) ⟨896343, by rfl⟩ : syracuseStep 2390249 = 1792687) B1792687
theorem B2423047 : Blo 1415527 2423047 := bstep (se 1 (by rfl) ⟨1817285, by rfl⟩ : syracuseStep 2423047 = 3634571) B3634571
theorem B3184937 : Blo 1415527 3184937 := bstep (se 2 (by rfl) ⟨1194351, by rfl⟩ : syracuseStep 3184937 = 2388703) B2388703
theorem B3586427 : Blo 1415527 3586427 := bstep (se 1 (by rfl) ⟨2689820, by rfl⟩ : syracuseStep 3586427 = 5379641) B5379641
theorem B13621715 : Blo 1415527 13621715 := bstep (se 1 (by rfl) ⟨10216286, by rfl⟩ : syracuseStep 13621715 = 20432573) B20432573
theorem B1415707 : Blo 1415527 1415707 := bstep (se 1 (by rfl) ⟨1061780, by rfl⟩ : syracuseStep 1415707 = 2123561) B2123561
theorem B1415711 : Blo 1415527 1415711 := bstep (se 1 (by rfl) ⟨1061783, by rfl⟩ : syracuseStep 1415711 = 2123567) B2123567
theorem B1416027 : Blo 1415527 1416027 := bstep (se 1 (by rfl) ⟨1062020, by rfl⟩ : syracuseStep 1416027 = 2124041) B2124041
theorem B3185513 : Blo 1415527 3185513 := bstep (se 2 (by rfl) ⟨1194567, by rfl⟩ : syracuseStep 3185513 = 2389135) B2389135
theorem B7166879 : Blo 1415527 7166879 := bstep (se 1 (by rfl) ⟨5375159, by rfl⟩ : syracuseStep 7166879 = 10750319) B10750319
theorem B3185567 : Blo 1415527 3185567 := bstep (se 1 (by rfl) ⟨2389175, by rfl⟩ : syracuseStep 3185567 = 4778351) B4778351
theorem B1416095 : Blo 1415527 1416095 := bstep (se 1 (by rfl) ⟨1062071, by rfl⟩ : syracuseStep 1416095 = 2124143) B2124143
theorem B4783049 : Blo 1415527 4783049 := bstep (se 2 (by rfl) ⟨1793643, by rfl⟩ : syracuseStep 4783049 = 3587287) B3587287
theorem B1416239 : Blo 1415527 1416239 := bstep (se 1 (by rfl) ⟨1062179, by rfl⟩ : syracuseStep 1416239 = 2124359) B2124359
theorem B1416263 : Blo 1415527 1416263 := bstep (se 1 (by rfl) ⟨1062197, by rfl⟩ : syracuseStep 1416263 = 2124395) B2124395
theorem B33176699 : Blo 1415527 33176699 := bstep (se 1 (by rfl) ⟨24882524, by rfl⟩ : syracuseStep 33176699 = 49765049) B49765049
theorem B7265465 : Blo 1415527 7265465 := bstep (se 2 (by rfl) ⟨2724549, by rfl⟩ : syracuseStep 7265465 = 5449099) B5449099
theorem B18144445 : Blo 1415527 18144445 := bstep (se 3 (by rfl) ⟨3402083, by rfl⟩ : syracuseStep 18144445 = 6804167) B6804167
theorem B4783319 : Blo 1415527 4783319 := bstep (se 1 (by rfl) ⟨3587489, by rfl⟩ : syracuseStep 4783319 = 7174979) B7174979
theorem B1416415 : Blo 1415527 1416415 := bstep (se 1 (by rfl) ⟨1062311, by rfl⟩ : syracuseStep 1416415 = 2124623) B2124623
theorem B8068481 : Blo 1415527 8068481 := bstep (se 2 (by rfl) ⟨3025680, by rfl⟩ : syracuseStep 8068481 = 6051361) B6051361
theorem B1416679 : Blo 1415527 1416679 := bstep (se 1 (by rfl) ⟨1062509, by rfl⟩ : syracuseStep 1416679 = 2125019) B2125019
theorem B1416795 : Blo 1415527 1416795 := bstep (se 1 (by rfl) ⟨1062596, by rfl⟩ : syracuseStep 1416795 = 2125193) B2125193
theorem B2391727 : Blo 1415527 2391727 := bstep (se 1 (by rfl) ⟨1793795, by rfl⟩ : syracuseStep 2391727 = 3587591) B3587591
theorem B4783859 : Blo 1415527 4783859 := bstep (se 1 (by rfl) ⟨3587894, by rfl⟩ : syracuseStep 4783859 = 7175789) B7175789
theorem B3186503 : Blo 1415527 3186503 := bstep (se 1 (by rfl) ⟨2389877, by rfl⟩ : syracuseStep 3186503 = 4779755) B4779755
theorem B1417031 : Blo 1415527 1417031 := bstep (se 1 (by rfl) ⟨1062773, by rfl⟩ : syracuseStep 1417031 = 2125547) B2125547
theorem B1417183 : Blo 1415527 1417183 := bstep (se 1 (by rfl) ⟨1062887, by rfl⟩ : syracuseStep 1417183 = 2125775) B2125775
theorem B2392031 : Blo 1415527 2392031 := bstep (se 1 (by rfl) ⟨1794023, by rfl⟩ : syracuseStep 2392031 = 3588047) B3588047
theorem B6054011 : Blo 1415527 6054011 := bstep (se 1 (by rfl) ⟨4540508, by rfl⟩ : syracuseStep 6054011 = 9081017) B9081017
theorem B1417407 : Blo 1415527 1417407 := bstep (se 1 (by rfl) ⟨1063055, by rfl⟩ : syracuseStep 1417407 = 2126111) B2126111
theorem B1417423 : Blo 1415527 1417423 := bstep (se 1 (by rfl) ⟨1063067, by rfl⟩ : syracuseStep 1417423 = 2126135) B2126135
theorem B1417471 : Blo 1415527 1417471 := bstep (se 1 (by rfl) ⟨1063103, by rfl⟩ : syracuseStep 1417471 = 2126207) B2126207
theorem B4538663 : Blo 1415527 4538663 := bstep (se 1 (by rfl) ⟨3403997, by rfl⟩ : syracuseStep 4538663 = 6807995) B6807995
theorem B1417519 : Blo 1415527 1417519 := bstep (se 1 (by rfl) ⟨1063139, by rfl⟩ : syracuseStep 1417519 = 2126279) B2126279
theorem B8069483 : Blo 1415527 8069483 := bstep (se 1 (by rfl) ⟨6052112, by rfl⟩ : syracuseStep 8069483 = 12104225) B12104225
theorem B2687519 : Blo 1415527 2687519 := bstep (se 1 (by rfl) ⟨2015639, by rfl⟩ : syracuseStep 2687519 = 4031279) B4031279
theorem B3187367 : Blo 1415527 3187367 := bstep (se 1 (by rfl) ⟨2390525, by rfl⟩ : syracuseStep 3187367 = 4781051) B4781051
theorem B7168823 : Blo 1415527 7168823 := bstep (se 1 (by rfl) ⟨5376617, by rfl⟩ : syracuseStep 7168823 = 10753235) B10753235
theorem B3187511 : Blo 1415527 3187511 := bstep (se 1 (by rfl) ⟨2390633, by rfl⟩ : syracuseStep 3187511 = 4781267) B4781267
theorem B5374781 : Blo 1415527 5374781 := bstep (se 3 (by rfl) ⟨1007771, by rfl⟩ : syracuseStep 5374781 = 2015543) B2015543
theorem B3187691 : Blo 1415527 3187691 := bstep (se 1 (by rfl) ⟨2390768, by rfl⟩ : syracuseStep 3187691 = 4781537) B4781537
theorem B3188123 : Blo 1415527 3188123 := bstep (se 1 (by rfl) ⟨2391092, by rfl⟩ : syracuseStep 3188123 = 4782185) B4782185
theorem B2123291 : Blo 1415527 2123291 := bstep (se 1 (by rfl) ⟨1592468, by rfl⟩ : syracuseStep 2123291 = 3184937) B3184937
theorem B4032031 : Blo 1415527 4032031 := bstep (se 1 (by rfl) ⟨3024023, by rfl⟩ : syracuseStep 4032031 = 6048047) B6048047
theorem B24544829 : Blo 1415527 24544829 := bstep (se 3 (by rfl) ⟨4602155, by rfl⟩ : syracuseStep 24544829 = 9204311) B9204311
theorem B20407889 : Blo 1415527 20407889 := bstep (se 2 (by rfl) ⟨7652958, by rfl⟩ : syracuseStep 20407889 = 15305917) B15305917
theorem B24192593 : Blo 1415527 24192593 := bstep (se 2 (by rfl) ⟨9072222, by rfl⟩ : syracuseStep 24192593 = 18144445) B18144445
theorem B8062649 : Blo 1415527 8062649 := bstep (se 2 (by rfl) ⟨3023493, by rfl⟩ : syracuseStep 8062649 = 6046987) B6046987
theorem B3229561 : Blo 1415527 3229561 := bstep (se 2 (by rfl) ⟨1211085, by rfl⟩ : syracuseStep 3229561 = 2422171) B2422171
theorem B2123675 : Blo 1415527 2123675 := bstep (se 1 (by rfl) ⟨1592756, by rfl⟩ : syracuseStep 2123675 = 3185513) B3185513
theorem B4777919 : Blo 1415527 4777919 := bstep (se 1 (by rfl) ⟨3583439, by rfl⟩ : syracuseStep 4777919 = 7166879) B7166879
theorem B2123711 : Blo 1415527 2123711 := bstep (se 1 (by rfl) ⟨1592783, by rfl⟩ : syracuseStep 2123711 = 3185567) B3185567
theorem B3188699 : Blo 1415527 3188699 := bstep (se 1 (by rfl) ⟨2391524, by rfl⟩ : syracuseStep 3188699 = 4783049) B4783049
theorem B3065887 : Blo 1415527 3065887 := bstep (se 1 (by rfl) ⟨2299415, by rfl⟩ : syracuseStep 3065887 = 4598831) B4598831
theorem B10209311 : Blo 1415527 10209311 := bstep (se 1 (by rfl) ⟨7656983, by rfl⟩ : syracuseStep 10209311 = 15313967) B15313967
theorem B4778081 : Blo 1415527 4778081 := bstep (se 2 (by rfl) ⟨1791780, by rfl⟩ : syracuseStep 4778081 = 3583561) B3583561
theorem B2123897 : Blo 1415527 2123897 := bstep (se 2 (by rfl) ⟨796461, by rfl⟩ : syracuseStep 2123897 = 1592923) B1592923
theorem B4843643 : Blo 1415527 4843643 := bstep (se 1 (by rfl) ⟨3632732, by rfl⟩ : syracuseStep 4843643 = 7265465) B7265465
theorem B3188879 : Blo 1415527 3188879 := bstep (se 1 (by rfl) ⟨2391659, by rfl⟩ : syracuseStep 3188879 = 4783319) B4783319
theorem B7170281 : Blo 1415527 7170281 := bstep (se 2 (by rfl) ⟨2688855, by rfl⟩ : syracuseStep 7170281 = 5377711) B5377711
theorem B3188969 : Blo 1415527 3188969 := bstep (se 2 (by rfl) ⟨1195863, by rfl⟩ : syracuseStep 3188969 = 2391727) B2391727
theorem B3189239 : Blo 1415527 3189239 := bstep (se 1 (by rfl) ⟨2391929, by rfl⟩ : syracuseStep 3189239 = 4783859) B4783859
theorem B2124281 : Blo 1415527 2124281 := bstep (se 2 (by rfl) ⟨796605, by rfl⟩ : syracuseStep 2124281 = 1593211) B1593211
theorem B2124335 : Blo 1415527 2124335 := bstep (se 1 (by rfl) ⟨1593251, by rfl⟩ : syracuseStep 2124335 = 3186503) B3186503
theorem B4778621 : Blo 1415527 4778621 := bstep (se 3 (by rfl) ⟨895991, by rfl⟩ : syracuseStep 4778621 = 1791983) B1791983
theorem B6810455 : Blo 1415527 6810455 := bstep (se 1 (by rfl) ⟨5107841, by rfl⟩ : syracuseStep 6810455 = 10215683) B10215683
theorem B4778891 : Blo 1415527 4778891 := bstep (se 1 (by rfl) ⟨3584168, by rfl⟩ : syracuseStep 4778891 = 7168337) B7168337
theorem B10759067 : Blo 1415527 10759067 := bstep (se 1 (by rfl) ⟨8069300, by rfl⟩ : syracuseStep 10759067 = 16138601) B16138601
theorem B2124767 : Blo 1415527 2124767 := bstep (se 1 (by rfl) ⟨1593575, by rfl⟩ : syracuseStep 2124767 = 3187151) B3187151
theorem B3230729 : Blo 1415527 3230729 := bstep (se 2 (by rfl) ⟨1211523, by rfl⟩ : syracuseStep 3230729 = 2423047) B2423047
theorem B5377211 : Blo 1415527 5377211 := bstep (se 1 (by rfl) ⟨4032908, by rfl⟩ : syracuseStep 5377211 = 8065817) B8065817
theorem B55184753 : Blo 1415527 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B2125211 : Blo 1415527 2125211 := bstep (se 1 (by rfl) ⟨1593908, by rfl⟩ : syracuseStep 2125211 = 3187817) B3187817
theorem B4779431 : Blo 1415527 4779431 := bstep (se 1 (by rfl) ⟨3584573, by rfl⟩ : syracuseStep 4779431 = 7169147) B7169147
theorem B9072121 : Blo 1415527 9072121 := bstep (se 2 (by rfl) ⟨3402045, by rfl⟩ : syracuseStep 9072121 = 6804091) B6804091
theorem B52375135 : Blo 1415527 52375135 := bstep (se 1 (by rfl) ⟨39281351, by rfl⟩ : syracuseStep 52375135 = 78562703) B78562703
theorem B39308971 : Blo 1415527 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B29093627 : Blo 1415527 29093627 := bstep (se 1 (by rfl) ⟨21820220, by rfl⟩ : syracuseStep 29093627 = 43640441) B43640441
theorem B2125631 : Blo 1415527 2125631 := bstep (se 1 (by rfl) ⟨1594223, by rfl⟩ : syracuseStep 2125631 = 3188447) B3188447
theorem B4779863 : Blo 1415527 4779863 := bstep (se 1 (by rfl) ⟨3584897, by rfl⟩ : syracuseStep 4779863 = 7169795) B7169795
theorem B3403691 : Blo 1415527 3403691 := bstep (se 1 (by rfl) ⟨2552768, by rfl⟩ : syracuseStep 3403691 = 5105537) B5105537
theorem B5378015 : Blo 1415527 5378015 := bstep (se 1 (by rfl) ⟨4033511, by rfl⟩ : syracuseStep 5378015 = 8067023) B8067023
theorem B4780025 : Blo 1415527 4780025 := bstep (se 2 (by rfl) ⟨1792509, by rfl⟩ : syracuseStep 4780025 = 3585019) B3585019
theorem B2125817 : Blo 1415527 2125817 := bstep (se 2 (by rfl) ⟨797181, by rfl⟩ : syracuseStep 2125817 = 1594363) B1594363
theorem B5378183 : Blo 1415527 5378183 := bstep (se 1 (by rfl) ⟨4033637, by rfl⟩ : syracuseStep 5378183 = 8067275) B8067275
theorem B5107855 : Blo 1415527 5107855 := bstep (se 1 (by rfl) ⟨3830891, by rfl⟩ : syracuseStep 5107855 = 7661783) B7661783
theorem B1593499 : Blo 1415527 1593499 := bstep (se 1 (by rfl) ⟨1195124, by rfl⟩ : syracuseStep 1593499 = 2390249) B2390249
theorem B1749167 : Blo 1415527 1749167 := bstep (se 1 (by rfl) ⟨1311875, by rfl⟩ : syracuseStep 1749167 = 2623751) B2623751
theorem B2126057 : Blo 1415527 2126057 := bstep (se 2 (by rfl) ⟨797271, by rfl⟩ : syracuseStep 2126057 = 1594543) B1594543
theorem B4780295 : Blo 1415527 4780295 := bstep (se 1 (by rfl) ⟨3585221, by rfl⟩ : syracuseStep 4780295 = 7170443) B7170443
theorem B9081143 : Blo 1415527 9081143 := bstep (se 1 (by rfl) ⟨6810857, by rfl⟩ : syracuseStep 9081143 = 13621715) B13621715
theorem B2126183 : Blo 1415527 2126183 := bstep (se 1 (by rfl) ⟨1594637, by rfl⟩ : syracuseStep 2126183 = 3189275) B3189275
theorem B78623129 : Blo 1415527 78623129 := bstep (se 2 (by rfl) ⟨29483673, by rfl⟩ : syracuseStep 78623129 = 58967347) B58967347
theorem B4035005 : Blo 1415527 4035005 := bstep (se 3 (by rfl) ⟨756563, by rfl⟩ : syracuseStep 4035005 = 1513127) B1513127
theorem B11809223 : Blo 1415527 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B4780673 : Blo 1415527 4780673 := bstep (se 2 (by rfl) ⟨1792752, by rfl⟩ : syracuseStep 4780673 = 3585505) B3585505
theorem B4780943 : Blo 1415527 4780943 := bstep (se 1 (by rfl) ⟨3585707, by rfl⟩ : syracuseStep 4780943 = 7171415) B7171415
theorem B5378987 : Blo 1415527 5378987 := bstep (se 1 (by rfl) ⟨4034240, by rfl⟩ : syracuseStep 5378987 = 8068481) B8068481
theorem B6386771 : Blo 1415527 6386771 := bstep (se 1 (by rfl) ⟨4790078, by rfl⟩ : syracuseStep 6386771 = 9580157) B9580157
theorem B3404929 : Blo 1415527 3404929 := bstep (se 2 (by rfl) ⟨1276848, by rfl⟩ : syracuseStep 3404929 = 2553697) B2553697
theorem B2389243 : Blo 1415527 2389243 := bstep (se 1 (by rfl) ⟨1791932, by rfl⟩ : syracuseStep 2389243 = 3583865) B3583865
theorem B4035881 : Blo 1415527 4035881 := bstep (se 2 (by rfl) ⟨1513455, by rfl⟩ : syracuseStep 4035881 = 3026911) B3026911
theorem B4781375 : Blo 1415527 4781375 := bstep (se 1 (by rfl) ⟨3586031, by rfl⟩ : syracuseStep 4781375 = 7172063) B7172063
theorem B1594687 : Blo 1415527 1594687 := bstep (se 1 (by rfl) ⟨1196015, by rfl⟩ : syracuseStep 1594687 = 2392031) B2392031
theorem B4781483 : Blo 1415527 4781483 := bstep (se 1 (by rfl) ⟨3586112, by rfl⟩ : syracuseStep 4781483 = 7172225) B7172225
theorem B12105287 : Blo 1415527 12105287 := bstep (se 1 (by rfl) ⟨9078965, by rfl⟩ : syracuseStep 12105287 = 18157931) B18157931
theorem B2840231 : Blo 1415527 2840231 := bstep (se 1 (by rfl) ⟨2130173, by rfl⟩ : syracuseStep 2840231 = 4260347) B4260347
theorem B1513199 : Blo 1415527 1513199 := bstep (se 1 (by rfl) ⟨1134899, by rfl⟩ : syracuseStep 1513199 = 2269799) B2269799
theorem B5822239 : Blo 1415527 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B4782023 : Blo 1415527 4782023 := bstep (se 1 (by rfl) ⟨3586517, by rfl⟩ : syracuseStep 4782023 = 7173035) B7173035
theorem B2390087 : Blo 1415527 2390087 := bstep (se 1 (by rfl) ⟨1792565, by rfl⟩ : syracuseStep 2390087 = 3585131) B3585131
theorem B13613255 : Blo 1415527 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B2332891 : Blo 1415527 2332891 := bstep (se 1 (by rfl) ⟨1749668, by rfl⟩ : syracuseStep 2332891 = 3499337) B3499337
theorem B3184991 : Blo 1415527 3184991 := bstep (se 1 (by rfl) ⟨2388743, by rfl⟩ : syracuseStep 3184991 = 4777487) B4777487
theorem B1415583 : Blo 1415527 1415583 := bstep (se 1 (by rfl) ⟨1061687, by rfl⟩ : syracuseStep 1415583 = 2123375) B2123375
theorem B1415631 : Blo 1415527 1415631 := bstep (se 1 (by rfl) ⟨1061723, by rfl⟩ : syracuseStep 1415631 = 2123447) B2123447
theorem B1415655 : Blo 1415527 1415655 := bstep (se 1 (by rfl) ⟨1061741, by rfl⟩ : syracuseStep 1415655 = 2123483) B2123483
theorem B1415771 : Blo 1415527 1415771 := bstep (se 1 (by rfl) ⟨1061828, by rfl⟩ : syracuseStep 1415771 = 2123657) B2123657
theorem B1415839 : Blo 1415527 1415839 := bstep (se 1 (by rfl) ⟨1061879, by rfl⟩ : syracuseStep 1415839 = 2123759) B2123759
theorem B5741279 : Blo 1415527 5741279 := bstep (se 1 (by rfl) ⟨4305959, by rfl⟩ : syracuseStep 5741279 = 8611919) B8611919
theorem B1416007 : Blo 1415527 1416007 := bstep (se 1 (by rfl) ⟨1062005, by rfl⟩ : syracuseStep 1416007 = 2124011) B2124011
theorem B1416047 : Blo 1415527 1416047 := bstep (se 1 (by rfl) ⟨1062035, by rfl⟩ : syracuseStep 1416047 = 2124071) B2124071
theorem B3185531 : Blo 1415527 3185531 := bstep (se 1 (by rfl) ⟨2389148, by rfl⟩ : syracuseStep 3185531 = 4778297) B4778297
theorem B1416103 : Blo 1415527 1416103 := bstep (se 1 (by rfl) ⟨1062077, by rfl⟩ : syracuseStep 1416103 = 2124155) B2124155
theorem B2390951 : Blo 1415527 2390951 := bstep (se 1 (by rfl) ⟨1793213, by rfl⟩ : syracuseStep 2390951 = 3586427) B3586427
theorem B3185711 : Blo 1415527 3185711 := bstep (se 1 (by rfl) ⟨2389283, by rfl⟩ : syracuseStep 3185711 = 4778567) B4778567
theorem B1416283 : Blo 1415527 1416283 := bstep (se 1 (by rfl) ⟨1062212, by rfl⟩ : syracuseStep 1416283 = 2124425) B2124425
theorem B1416399 : Blo 1415527 1416399 := bstep (se 1 (by rfl) ⟨1062299, by rfl⟩ : syracuseStep 1416399 = 2124599) B2124599
theorem B1416423 : Blo 1415527 1416423 := bstep (se 1 (by rfl) ⟨1062317, by rfl⟩ : syracuseStep 1416423 = 2124635) B2124635
theorem B1416519 : Blo 1415527 1416519 := bstep (se 1 (by rfl) ⟨1062389, by rfl⟩ : syracuseStep 1416519 = 2124779) B2124779
theorem B22117799 : Blo 1415527 22117799 := bstep (se 1 (by rfl) ⟨16588349, by rfl⟩ : syracuseStep 22117799 = 33176699) B33176699
theorem B1416655 : Blo 1415527 1416655 := bstep (se 1 (by rfl) ⟨1062491, by rfl⟩ : syracuseStep 1416655 = 2124983) B2124983
theorem B1416815 : Blo 1415527 1416815 := bstep (se 1 (by rfl) ⟨1062611, by rfl⟩ : syracuseStep 1416815 = 2125223) B2125223
theorem B1416871 : Blo 1415527 1416871 := bstep (se 1 (by rfl) ⟨1062653, by rfl⟩ : syracuseStep 1416871 = 2125307) B2125307
theorem B3186395 : Blo 1415527 3186395 := bstep (se 1 (by rfl) ⟨2389796, by rfl⟩ : syracuseStep 3186395 = 4779593) B4779593
theorem B1793755 : Blo 1415527 1793755 := bstep (se 1 (by rfl) ⟨1345316, by rfl⟩ : syracuseStep 1793755 = 2690633) B2690633
theorem B1416935 : Blo 1415527 1416935 := bstep (se 1 (by rfl) ⟨1062701, by rfl⟩ : syracuseStep 1416935 = 2125403) B2125403
theorem B1416991 : Blo 1415527 1416991 := bstep (se 1 (by rfl) ⟨1062743, by rfl⟩ : syracuseStep 1416991 = 2125487) B2125487
theorem B1417071 : Blo 1415527 1417071 := bstep (se 1 (by rfl) ⟨1062803, by rfl⟩ : syracuseStep 1417071 = 2125607) B2125607
theorem B1417127 : Blo 1415527 1417127 := bstep (se 1 (by rfl) ⟨1062845, by rfl⟩ : syracuseStep 1417127 = 2125691) B2125691
theorem B55214045 : Blo 1415527 55214045 := bstep (se 3 (by rfl) ⟨10352633, by rfl⟩ : syracuseStep 55214045 = 20705267) B20705267
theorem B3186665 : Blo 1415527 3186665 := bstep (se 2 (by rfl) ⟨1194999, by rfl⟩ : syracuseStep 3186665 = 2389999) B2389999
theorem B4087849 : Blo 1415527 4087849 := bstep (se 2 (by rfl) ⟨1532943, by rfl⟩ : syracuseStep 4087849 = 3065887) B3065887
theorem B1417371 : Blo 1415527 1417371 := bstep (se 1 (by rfl) ⟨1063028, by rfl⟩ : syracuseStep 1417371 = 2126057) B2126057
theorem B3186863 : Blo 1415527 3186863 := bstep (se 1 (by rfl) ⟨2390147, by rfl⟩ : syracuseStep 3186863 = 4780295) B4780295
theorem B6054095 : Blo 1415527 6054095 := bstep (se 1 (by rfl) ⟨4540571, by rfl⟩ : syracuseStep 6054095 = 9081143) B9081143
theorem B17031389 : Blo 1415527 17031389 := bstep (se 3 (by rfl) ⟨3193385, by rfl⟩ : syracuseStep 17031389 = 6386771) B6386771
theorem B1417455 : Blo 1415527 1417455 := bstep (se 1 (by rfl) ⟨1063091, by rfl⟩ : syracuseStep 1417455 = 2126183) B2126183
theorem B7872815 : Blo 1415527 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B3187115 : Blo 1415527 3187115 := bstep (se 1 (by rfl) ⟨2390336, by rfl⟩ : syracuseStep 3187115 = 4780673) B4780673
theorem B3187295 : Blo 1415527 3187295 := bstep (se 1 (by rfl) ⟨2390471, by rfl⟩ : syracuseStep 3187295 = 4780943) B4780943
theorem B3187583 : Blo 1415527 3187583 := bstep (se 1 (by rfl) ⟨2390687, by rfl⟩ : syracuseStep 3187583 = 4781375) B4781375
theorem B3187655 : Blo 1415527 3187655 := bstep (se 1 (by rfl) ⟨2390741, by rfl⟩ : syracuseStep 3187655 = 4781483) B4781483
theorem B8070191 : Blo 1415527 8070191 := bstep (se 1 (by rfl) ⟨6052643, by rfl⟩ : syracuseStep 8070191 = 12105287) B12105287
theorem B5375099 : Blo 1415527 5375099 := bstep (se 1 (by rfl) ⟨4031324, by rfl⟩ : syracuseStep 5375099 = 8062649) B8062649
theorem B3188015 : Blo 1415527 3188015 := bstep (se 1 (by rfl) ⟨2391011, by rfl⟩ : syracuseStep 3188015 = 4782023) B4782023
theorem B4539905 : Blo 1415527 4539905 := bstep (se 2 (by rfl) ⟨1702464, by rfl⟩ : syracuseStep 4539905 = 3404929) B3404929
theorem B2123327 : Blo 1415527 2123327 := bstep (se 1 (by rfl) ⟨1592495, by rfl⟩ : syracuseStep 2123327 = 3184991) B3184991
theorem B3827519 : Blo 1415527 3827519 := bstep (se 1 (by rfl) ⟨2870639, by rfl⟩ : syracuseStep 3827519 = 5741279) B5741279
theorem B4540303 : Blo 1415527 4540303 := bstep (se 1 (by rfl) ⟨3405227, by rfl⟩ : syracuseStep 4540303 = 6810455) B6810455
theorem B2123687 : Blo 1415527 2123687 := bstep (se 1 (by rfl) ⟨1592765, by rfl⟩ : syracuseStep 2123687 = 3185531) B3185531
theorem B74631125 : Blo 1415527 74631125 := bstep (se 7 (by rfl) ⟨874583, by rfl⟩ : syracuseStep 74631125 = 1749167) B1749167
theorem B2123807 : Blo 1415527 2123807 := bstep (se 1 (by rfl) ⟨1592855, by rfl⟩ : syracuseStep 2123807 = 3185711) B3185711
theorem B5376041 : Blo 1415527 5376041 := bstep (se 2 (by rfl) ⟨2016015, by rfl⟩ : syracuseStep 5376041 = 4032031) B4032031
theorem B2124263 : Blo 1415527 2124263 := bstep (se 1 (by rfl) ⟨1593197, by rfl⟩ : syracuseStep 2124263 = 3186395) B3186395
theorem B36809363 : Blo 1415527 36809363 := bstep (se 1 (by rfl) ⟨27607022, by rfl⟩ : syracuseStep 36809363 = 55214045) B55214045
theorem B2124443 : Blo 1415527 2124443 := bstep (se 1 (by rfl) ⟨1593332, by rfl⟩ : syracuseStep 2124443 = 3186665) B3186665
theorem B6810473 : Blo 1415527 6810473 := bstep (se 2 (by rfl) ⟨2553927, by rfl⟩ : syracuseStep 6810473 = 5107855) B5107855
theorem B3025775 : Blo 1415527 3025775 := bstep (se 1 (by rfl) ⟨2269331, by rfl⟩ : syracuseStep 3025775 = 4538663) B4538663
theorem B2124665 : Blo 1415527 2124665 := bstep (se 2 (by rfl) ⟨796749, by rfl⟩ : syracuseStep 2124665 = 1593499) B1593499
theorem B52415419 : Blo 1415527 52415419 := bstep (se 1 (by rfl) ⟨39311564, by rfl⟩ : syracuseStep 52415419 = 78623129) B78623129
theorem B2690003 : Blo 1415527 2690003 := bstep (se 1 (by rfl) ⟨2017502, by rfl⟩ : syracuseStep 2690003 = 4035005) B4035005
theorem B2124911 : Blo 1415527 2124911 := bstep (se 1 (by rfl) ⟨1593683, by rfl⟩ : syracuseStep 2124911 = 3187367) B3187367
theorem B4779215 : Blo 1415527 4779215 := bstep (se 1 (by rfl) ⟨3584411, by rfl⟩ : syracuseStep 4779215 = 7168823) B7168823
theorem B2125007 : Blo 1415527 2125007 := bstep (se 1 (by rfl) ⟨1593755, by rfl⟩ : syracuseStep 2125007 = 3187511) B3187511
theorem B3583187 : Blo 1415527 3583187 := bstep (se 1 (by rfl) ⟨2687390, by rfl⟩ : syracuseStep 3583187 = 5374781) B5374781
theorem B1417211 : Blo 1415527 1417211 := bstep (se 1 (by rfl) ⟨1062908, by rfl⟩ : syracuseStep 1417211 = 2125817) B2125817
theorem B2125127 : Blo 1415527 2125127 := bstep (se 1 (by rfl) ⟨1593845, by rfl⟩ : syracuseStep 2125127 = 3187691) B3187691
theorem B2690587 : Blo 1415527 2690587 := bstep (se 1 (by rfl) ⟨2017940, by rfl⟩ : syracuseStep 2690587 = 4035881) B4035881
theorem B2125415 : Blo 1415527 2125415 := bstep (se 1 (by rfl) ⟨1594061, by rfl⟩ : syracuseStep 2125415 = 3188123) B3188123
theorem B2125799 : Blo 1415527 2125799 := bstep (se 1 (by rfl) ⟨1594349, by rfl⟩ : syracuseStep 2125799 = 3188699) B3188699
theorem B1593391 : Blo 1415527 1593391 := bstep (se 1 (by rfl) ⟨1195043, by rfl⟩ : syracuseStep 1593391 = 2390087) B2390087
theorem B2125919 : Blo 1415527 2125919 := bstep (se 1 (by rfl) ⟨1594439, by rfl⟩ : syracuseStep 2125919 = 3188879) B3188879
theorem B4780187 : Blo 1415527 4780187 := bstep (se 1 (by rfl) ⟨3585140, by rfl⟩ : syracuseStep 4780187 = 7170281) B7170281
theorem B2125979 : Blo 1415527 2125979 := bstep (se 1 (by rfl) ⟨1594484, by rfl⟩ : syracuseStep 2125979 = 3188969) B3188969
theorem B2126159 : Blo 1415527 2126159 := bstep (se 1 (by rfl) ⟨1594619, by rfl⟩ : syracuseStep 2126159 = 3189239) B3189239
theorem B2126249 : Blo 1415527 2126249 := bstep (se 2 (by rfl) ⟨797343, by rfl⟩ : syracuseStep 2126249 = 1594687) B1594687
theorem B7573949 : Blo 1415527 7573949 := bstep (se 3 (by rfl) ⟨1420115, by rfl⟩ : syracuseStep 7573949 = 2840231) B2840231
theorem B7172711 : Blo 1415527 7172711 := bstep (se 1 (by rfl) ⟨5379533, by rfl⟩ : syracuseStep 7172711 = 10759067) B10759067
theorem B1593967 : Blo 1415527 1593967 := bstep (se 1 (by rfl) ⟨1195475, by rfl⟩ : syracuseStep 1593967 = 2390951) B2390951
theorem B4035197 : Blo 1415527 4035197 := bstep (se 3 (by rfl) ⟨756599, by rfl⟩ : syracuseStep 4035197 = 1513199) B1513199
theorem B77583005 : Blo 1415527 77583005 := bstep (se 3 (by rfl) ⟨14546813, by rfl⟩ : syracuseStep 77583005 = 29093627) B29093627
theorem B12096161 : Blo 1415527 12096161 := bstep (se 2 (by rfl) ⟨4536060, by rfl⟩ : syracuseStep 12096161 = 9072121) B9072121
theorem B3584807 : Blo 1415527 3584807 := bstep (se 1 (by rfl) ⟨2688605, by rfl⟩ : syracuseStep 3584807 = 5377211) B5377211
theorem B69833513 : Blo 1415527 69833513 := bstep (se 2 (by rfl) ⟨26187567, by rfl⟩ : syracuseStep 69833513 = 52375135) B52375135
theorem B7762985 : Blo 1415527 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B4306081 : Blo 1415527 4306081 := bstep (se 2 (by rfl) ⟨1614780, by rfl⟩ : syracuseStep 4306081 = 3229561) B3229561
theorem B3585343 : Blo 1415527 3585343 := bstep (se 1 (by rfl) ⟨2689007, by rfl⟩ : syracuseStep 3585343 = 5378015) B5378015
theorem B4036007 : Blo 1415527 4036007 := bstep (se 1 (by rfl) ⟨3027005, by rfl⟩ : syracuseStep 4036007 = 6054011) B6054011
theorem B3585455 : Blo 1415527 3585455 := bstep (se 1 (by rfl) ⟨2689091, by rfl⟩ : syracuseStep 3585455 = 5378183) B5378183
theorem B5379655 : Blo 1415527 5379655 := bstep (se 1 (by rfl) ⟨4034741, by rfl⟩ : syracuseStep 5379655 = 8069483) B8069483
theorem B12916381 : Blo 1415527 12916381 := bstep (se 3 (by rfl) ⟨2421821, by rfl⟩ : syracuseStep 12916381 = 4843643) B4843643
theorem B3585991 : Blo 1415527 3585991 := bstep (se 1 (by rfl) ⟨2689493, by rfl⟩ : syracuseStep 3585991 = 5378987) B5378987
theorem B1415527 : Blo 1415527 1415527 := bstep (se 1 (by rfl) ⟨1061645, by rfl⟩ : syracuseStep 1415527 = 2123291) B2123291
theorem B13605259 : Blo 1415527 13605259 := bstep (se 1 (by rfl) ⟨10203944, by rfl⟩ : syracuseStep 13605259 = 20407889) B20407889
theorem B16128395 : Blo 1415527 16128395 := bstep (se 1 (by rfl) ⟨12096296, by rfl⟩ : syracuseStep 16128395 = 24192593) B24192593
theorem B12442085 : Blo 1415527 12442085 := bstep (se 4 (by rfl) ⟨1166445, by rfl⟩ : syracuseStep 12442085 = 2332891) B2332891
theorem B1415783 : Blo 1415527 1415783 := bstep (se 1 (by rfl) ⟨1061837, by rfl⟩ : syracuseStep 1415783 = 2123675) B2123675
theorem B3185279 : Blo 1415527 3185279 := bstep (se 1 (by rfl) ⟨2388959, by rfl⟩ : syracuseStep 3185279 = 4777919) B4777919
theorem B1415807 : Blo 1415527 1415807 := bstep (se 1 (by rfl) ⟨1061855, by rfl⟩ : syracuseStep 1415807 = 2123711) B2123711
theorem B6806207 : Blo 1415527 6806207 := bstep (se 1 (by rfl) ⟨5104655, by rfl⟩ : syracuseStep 6806207 = 10209311) B10209311
theorem B3185387 : Blo 1415527 3185387 := bstep (se 1 (by rfl) ⟨2389040, by rfl⟩ : syracuseStep 3185387 = 4778081) B4778081
theorem B1415931 : Blo 1415527 1415931 := bstep (se 1 (by rfl) ⟨1061948, by rfl⟩ : syracuseStep 1415931 = 2123897) B2123897
theorem B7166717 : Blo 1415527 7166717 := bstep (se 3 (by rfl) ⟨1343759, by rfl⟩ : syracuseStep 7166717 = 2687519) B2687519
theorem B9075503 : Blo 1415527 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B65452877 : Blo 1415527 65452877 := bstep (se 3 (by rfl) ⟨12272414, by rfl⟩ : syracuseStep 65452877 = 24544829) B24544829
theorem B3185657 : Blo 1415527 3185657 := bstep (se 2 (by rfl) ⟨1194621, by rfl⟩ : syracuseStep 3185657 = 2389243) B2389243
theorem B1416187 : Blo 1415527 1416187 := bstep (se 1 (by rfl) ⟨1062140, by rfl⟩ : syracuseStep 1416187 = 2124281) B2124281
theorem B1416223 : Blo 1415527 1416223 := bstep (se 1 (by rfl) ⟨1062167, by rfl⟩ : syracuseStep 1416223 = 2124335) B2124335
theorem B3185747 : Blo 1415527 3185747 := bstep (se 1 (by rfl) ⟨2389310, by rfl⟩ : syracuseStep 3185747 = 4778621) B4778621
theorem B3185927 : Blo 1415527 3185927 := bstep (se 1 (by rfl) ⟨2389445, by rfl⟩ : syracuseStep 3185927 = 4778891) B4778891
theorem B1416511 : Blo 1415527 1416511 := bstep (se 1 (by rfl) ⟨1062383, by rfl⟩ : syracuseStep 1416511 = 2124767) B2124767
theorem B2153819 : Blo 1415527 2153819 := bstep (se 1 (by rfl) ⟨1615364, by rfl⟩ : syracuseStep 2153819 = 3230729) B3230729
theorem B52411961 : Blo 1415527 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B36789835 : Blo 1415527 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B1416807 : Blo 1415527 1416807 := bstep (se 1 (by rfl) ⟨1062605, by rfl⟩ : syracuseStep 1416807 = 2125211) B2125211
theorem B3186287 : Blo 1415527 3186287 := bstep (se 1 (by rfl) ⟨2389715, by rfl⟩ : syracuseStep 3186287 = 4779431) B4779431
theorem B14745199 : Blo 1415527 14745199 := bstep (se 1 (by rfl) ⟨11058899, by rfl⟩ : syracuseStep 14745199 = 22117799) B22117799
theorem B2391673 : Blo 1415527 2391673 := bstep (se 2 (by rfl) ⟨896877, by rfl⟩ : syracuseStep 2391673 = 1793755) B1793755
theorem B1417087 : Blo 1415527 1417087 := bstep (se 1 (by rfl) ⟨1062815, by rfl⟩ : syracuseStep 1417087 = 2125631) B2125631
theorem B3186575 : Blo 1415527 3186575 := bstep (se 1 (by rfl) ⟨2389931, by rfl⟩ : syracuseStep 3186575 = 4779863) B4779863
theorem B2269127 : Blo 1415527 2269127 := bstep (se 1 (by rfl) ⟨1701845, by rfl⟩ : syracuseStep 2269127 = 3403691) B3403691
theorem B3186683 : Blo 1415527 3186683 := bstep (se 1 (by rfl) ⟨2390012, by rfl⟩ : syracuseStep 3186683 = 4780025) B4780025
theorem B1417279 : Blo 1415527 1417279 := bstep (se 1 (by rfl) ⟨1062959, by rfl⟩ : syracuseStep 1417279 = 2125919) B2125919
theorem B3186791 : Blo 1415527 3186791 := bstep (se 1 (by rfl) ⟨2390093, by rfl⟩ : syracuseStep 3186791 = 4780187) B4780187
theorem B1417319 : Blo 1415527 1417319 := bstep (se 1 (by rfl) ⟨1062989, by rfl⟩ : syracuseStep 1417319 = 2125979) B2125979
theorem B1417439 : Blo 1415527 1417439 := bstep (se 1 (by rfl) ⟨1063079, by rfl⟩ : syracuseStep 1417439 = 2126159) B2126159
theorem B1417499 : Blo 1415527 1417499 := bstep (se 1 (by rfl) ⟨1063124, by rfl⟩ : syracuseStep 1417499 = 2126249) B2126249
theorem B45417037 : Blo 1415527 45417037 := bstep (se 3 (by rfl) ⟨8515694, by rfl⟩ : syracuseStep 45417037 = 17031389) B17031389
theorem B69887225 : Blo 1415527 69887225 := bstep (se 2 (by rfl) ⟨26207709, by rfl⟩ : syracuseStep 69887225 = 52415419) B52415419
theorem B98158301 : Blo 1415527 98158301 := bstep (se 3 (by rfl) ⟨18404681, by rfl⟩ : syracuseStep 98158301 = 36809363) B36809363
theorem B2123519 : Blo 1415527 2123519 := bstep (se 1 (by rfl) ⟨1592639, by rfl⟩ : syracuseStep 2123519 = 3185279) B3185279
theorem B2123591 : Blo 1415527 2123591 := bstep (se 1 (by rfl) ⟨1592693, by rfl⟩ : syracuseStep 2123591 = 3185387) B3185387
theorem B4777811 : Blo 1415527 4777811 := bstep (se 1 (by rfl) ⟨3583358, by rfl⟩ : syracuseStep 4777811 = 7166717) B7166717
theorem B4540315 : Blo 1415527 4540315 := bstep (se 1 (by rfl) ⟨3405236, by rfl⟩ : syracuseStep 4540315 = 6810473) B6810473
theorem B2123771 : Blo 1415527 2123771 := bstep (se 1 (by rfl) ⟨1592828, by rfl⟩ : syracuseStep 2123771 = 3185657) B3185657
theorem B2123831 : Blo 1415527 2123831 := bstep (se 1 (by rfl) ⟨1592873, by rfl⟩ : syracuseStep 2123831 = 3185747) B3185747
theorem B186222701 : Blo 1415527 186222701 := bstep (se 3 (by rfl) ⟨34916756, by rfl⟩ : syracuseStep 186222701 = 69833513) B69833513
theorem B24201341 : Blo 1415527 24201341 := bstep (se 3 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 24201341 = 9075503) B9075503
theorem B3188897 : Blo 1415527 3188897 := bstep (se 2 (by rfl) ⟨1195836, by rfl⟩ : syracuseStep 3188897 = 2391673) B2391673
theorem B2123951 : Blo 1415527 2123951 := bstep (se 1 (by rfl) ⟨1592963, by rfl⟩ : syracuseStep 2123951 = 3185927) B3185927
theorem B17221841 : Blo 1415527 17221841 := bstep (se 2 (by rfl) ⟨6458190, by rfl⟩ : syracuseStep 17221841 = 12916381) B12916381
theorem B1435879 : Blo 1415527 1435879 := bstep (se 1 (by rfl) ⟨1076909, by rfl⟩ : syracuseStep 1435879 = 2153819) B2153819
theorem B34941307 : Blo 1415527 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B2124191 : Blo 1415527 2124191 := bstep (se 1 (by rfl) ⟨1593143, by rfl⟩ : syracuseStep 2124191 = 3186287) B3186287
theorem B2124383 : Blo 1415527 2124383 := bstep (se 1 (by rfl) ⟨1593287, by rfl⟩ : syracuseStep 2124383 = 3186575) B3186575
theorem B2124455 : Blo 1415527 2124455 := bstep (se 1 (by rfl) ⟨1593341, by rfl⟩ : syracuseStep 2124455 = 3186683) B3186683
theorem B2124521 : Blo 1415527 2124521 := bstep (se 2 (by rfl) ⟨796695, by rfl⟩ : syracuseStep 2124521 = 1593391) B1593391
theorem B2124575 : Blo 1415527 2124575 := bstep (se 1 (by rfl) ⟨1593431, by rfl⟩ : syracuseStep 2124575 = 3186863) B3186863
theorem B2124743 : Blo 1415527 2124743 := bstep (se 1 (by rfl) ⟨1593557, by rfl⟩ : syracuseStep 2124743 = 3187115) B3187115
theorem B5049299 : Blo 1415527 5049299 := bstep (se 1 (by rfl) ⟨3786974, by rfl⟩ : syracuseStep 5049299 = 7573949) B7573949
theorem B2124863 : Blo 1415527 2124863 := bstep (se 1 (by rfl) ⟨1593647, by rfl⟩ : syracuseStep 2124863 = 3187295) B3187295
theorem B8064107 : Blo 1415527 8064107 := bstep (se 1 (by rfl) ⟨6048080, by rfl⟩ : syracuseStep 8064107 = 12096161) B12096161
theorem B18140345 : Blo 1415527 18140345 := bstep (se 2 (by rfl) ⟨6802629, by rfl⟩ : syracuseStep 18140345 = 13605259) B13605259
theorem B2125055 : Blo 1415527 2125055 := bstep (se 1 (by rfl) ⟨1593791, by rfl⟩ : syracuseStep 2125055 = 3187583) B3187583
theorem B2125103 : Blo 1415527 2125103 := bstep (se 1 (by rfl) ⟨1593827, by rfl⟩ : syracuseStep 2125103 = 3187655) B3187655
theorem B3583399 : Blo 1415527 3583399 := bstep (se 1 (by rfl) ⟨2687549, by rfl⟩ : syracuseStep 3583399 = 5375099) B5375099
theorem B2125289 : Blo 1415527 2125289 := bstep (se 2 (by rfl) ⟨796983, by rfl⟩ : syracuseStep 2125289 = 1593967) B1593967
theorem B87207445 : Blo 1415527 87207445 := bstep (se 6 (by rfl) ⟨2043924, by rfl⟩ : syracuseStep 87207445 = 4087849) B4087849
theorem B2125343 : Blo 1415527 2125343 := bstep (se 1 (by rfl) ⟨1594007, by rfl⟩ : syracuseStep 2125343 = 3188015) B3188015
theorem B2690671 : Blo 1415527 2690671 := bstep (se 1 (by rfl) ⟨2018003, by rfl⟩ : syracuseStep 2690671 = 4036007) B4036007
theorem B3026603 : Blo 1415527 3026603 := bstep (se 1 (by rfl) ⟨2269952, by rfl⟩ : syracuseStep 3026603 = 4539905) B4539905
theorem B2551679 : Blo 1415527 2551679 := bstep (se 1 (by rfl) ⟨1913759, by rfl⟩ : syracuseStep 2551679 = 3827519) B3827519
theorem B49754083 : Blo 1415527 49754083 := bstep (se 1 (by rfl) ⟨37315562, by rfl⟩ : syracuseStep 49754083 = 74631125) B74631125
theorem B3584027 : Blo 1415527 3584027 := bstep (se 1 (by rfl) ⟨2688020, by rfl⟩ : syracuseStep 3584027 = 5376041) B5376041
theorem B10752263 : Blo 1415527 10752263 := bstep (se 1 (by rfl) ⟨8064197, by rfl⟩ : syracuseStep 10752263 = 16128395) B16128395
theorem B8294723 : Blo 1415527 8294723 := bstep (se 1 (by rfl) ⟨6221042, by rfl⟩ : syracuseStep 8294723 = 12442085) B12442085
theorem B10760525 : Blo 1415527 10760525 := bstep (se 3 (by rfl) ⟨2017598, by rfl⟩ : syracuseStep 10760525 = 4035197) B4035197
theorem B4780457 : Blo 1415527 4780457 := bstep (se 2 (by rfl) ⟨1792671, by rfl⟩ : syracuseStep 4780457 = 3585343) B3585343
theorem B43635251 : Blo 1415527 43635251 := bstep (se 1 (by rfl) ⟨32726438, by rfl⟩ : syracuseStep 43635251 = 65452877) B65452877
theorem B7172873 : Blo 1415527 7172873 := bstep (se 2 (by rfl) ⟨2689827, by rfl⟩ : syracuseStep 7172873 = 5379655) B5379655
theorem B2388791 : Blo 1415527 2388791 := bstep (se 1 (by rfl) ⟨1791593, by rfl⟩ : syracuseStep 2388791 = 3583187) B3583187
theorem B4781321 : Blo 1415527 4781321 := bstep (se 2 (by rfl) ⟨1792995, by rfl⟩ : syracuseStep 4781321 = 3585991) B3585991
theorem B1512751 : Blo 1415527 1512751 := bstep (se 1 (by rfl) ⟨1134563, by rfl⟩ : syracuseStep 1512751 = 2269127) B2269127
theorem B4036063 : Blo 1415527 4036063 := bstep (se 1 (by rfl) ⟨3027047, by rfl⟩ : syracuseStep 4036063 = 6054095) B6054095
theorem B5248543 : Blo 1415527 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B4781807 : Blo 1415527 4781807 := bstep (se 1 (by rfl) ⟨3586355, by rfl⟩ : syracuseStep 4781807 = 7172711) B7172711
theorem B51722003 : Blo 1415527 51722003 := bstep (se 1 (by rfl) ⟨38791502, by rfl⟩ : syracuseStep 51722003 = 77583005) B77583005
theorem B2389871 : Blo 1415527 2389871 := bstep (se 1 (by rfl) ⟨1792403, by rfl⟩ : syracuseStep 2389871 = 3584807) B3584807
theorem B5175323 : Blo 1415527 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B5380127 : Blo 1415527 5380127 := bstep (se 1 (by rfl) ⟨4035095, by rfl⟩ : syracuseStep 5380127 = 8070191) B8070191
theorem B2390303 : Blo 1415527 2390303 := bstep (se 1 (by rfl) ⟨1792727, by rfl⟩ : syracuseStep 2390303 = 3585455) B3585455
theorem B1415551 : Blo 1415527 1415551 := bstep (se 1 (by rfl) ⟨1061663, by rfl⟩ : syracuseStep 1415551 = 2123327) B2123327
theorem B1415791 : Blo 1415527 1415791 := bstep (se 1 (by rfl) ⟨1061843, by rfl⟩ : syracuseStep 1415791 = 2123687) B2123687
theorem B1415871 : Blo 1415527 1415871 := bstep (se 1 (by rfl) ⟨1061903, by rfl⟩ : syracuseStep 1415871 = 2123807) B2123807
theorem B5741441 : Blo 1415527 5741441 := bstep (se 2 (by rfl) ⟨2153040, by rfl⟩ : syracuseStep 5741441 = 4306081) B4306081
theorem B1416175 : Blo 1415527 1416175 := bstep (se 1 (by rfl) ⟨1062131, by rfl⟩ : syracuseStep 1416175 = 2124263) B2124263
theorem B1416295 : Blo 1415527 1416295 := bstep (se 1 (by rfl) ⟨1062221, by rfl⟩ : syracuseStep 1416295 = 2124443) B2124443
theorem B4537471 : Blo 1415527 4537471 := bstep (se 1 (by rfl) ⟨3403103, by rfl⟩ : syracuseStep 4537471 = 6806207) B6806207
theorem B1416443 : Blo 1415527 1416443 := bstep (se 1 (by rfl) ⟨1062332, by rfl⟩ : syracuseStep 1416443 = 2124665) B2124665
theorem B1793335 : Blo 1415527 1793335 := bstep (se 1 (by rfl) ⟨1345001, by rfl⟩ : syracuseStep 1793335 = 2690003) B2690003
theorem B3587449 : Blo 1415527 3587449 := bstep (se 2 (by rfl) ⟨1345293, by rfl⟩ : syracuseStep 3587449 = 2690587) B2690587
theorem B1416607 : Blo 1415527 1416607 := bstep (se 1 (by rfl) ⟨1062455, by rfl⟩ : syracuseStep 1416607 = 2124911) B2124911
theorem B49053113 : Blo 1415527 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B3186143 : Blo 1415527 3186143 := bstep (se 1 (by rfl) ⟨2389607, by rfl⟩ : syracuseStep 3186143 = 4779215) B4779215
theorem B1416671 : Blo 1415527 1416671 := bstep (se 1 (by rfl) ⟨1062503, by rfl⟩ : syracuseStep 1416671 = 2125007) B2125007
theorem B19660265 : Blo 1415527 19660265 := bstep (se 2 (by rfl) ⟨7372599, by rfl⟩ : syracuseStep 19660265 = 14745199) B14745199
theorem B1416751 : Blo 1415527 1416751 := bstep (se 1 (by rfl) ⟨1062563, by rfl⟩ : syracuseStep 1416751 = 2125127) B2125127
theorem B8068733 : Blo 1415527 8068733 := bstep (se 3 (by rfl) ⟨1512887, by rfl⟩ : syracuseStep 8068733 = 3025775) B3025775
theorem B1416943 : Blo 1415527 1416943 := bstep (se 1 (by rfl) ⟨1062707, by rfl⟩ : syracuseStep 1416943 = 2125415) B2125415
theorem B6053737 : Blo 1415527 6053737 := bstep (se 2 (by rfl) ⟨2270151, by rfl⟩ : syracuseStep 6053737 = 4540303) B4540303
theorem B1417199 : Blo 1415527 1417199 := bstep (se 1 (by rfl) ⟨1062899, by rfl⟩ : syracuseStep 1417199 = 2125799) B2125799
theorem B7168175 : Blo 1415527 7168175 := bstep (se 1 (by rfl) ⟨5376131, by rfl⟩ : syracuseStep 7168175 = 10752263) B10752263
theorem B5529815 : Blo 1415527 5529815 := bstep (se 1 (by rfl) ⟨4147361, by rfl⟩ : syracuseStep 5529815 = 8294723) B8294723
theorem B3186971 : Blo 1415527 3186971 := bstep (se 1 (by rfl) ⟨2390228, by rfl⟩ : syracuseStep 3186971 = 4780457) B4780457
theorem B29090167 : Blo 1415527 29090167 := bstep (se 1 (by rfl) ⟨21817625, by rfl⟩ : syracuseStep 29090167 = 43635251) B43635251
theorem B46588409 : Blo 1415527 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B60556049 : Blo 1415527 60556049 := bstep (se 2 (by rfl) ⟨22708518, by rfl⟩ : syracuseStep 60556049 = 45417037) B45417037
theorem B3187547 : Blo 1415527 3187547 := bstep (se 1 (by rfl) ⟨2390660, by rfl⟩ : syracuseStep 3187547 = 4781321) B4781321
theorem B65438867 : Blo 1415527 65438867 := bstep (se 1 (by rfl) ⟨49079150, by rfl⟩ : syracuseStep 65438867 = 98158301) B98158301
theorem B3187871 : Blo 1415527 3187871 := bstep (se 1 (by rfl) ⟨2390903, by rfl⟩ : syracuseStep 3187871 = 4781807) B4781807
theorem B34481335 : Blo 1415527 34481335 := bstep (se 1 (by rfl) ⟨25861001, by rfl⟩ : syracuseStep 34481335 = 51722003) B51722003
theorem B3450215 : Blo 1415527 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B2017001 : Blo 1415527 2017001 := bstep (se 2 (by rfl) ⟨756375, by rfl⟩ : syracuseStep 2017001 = 1512751) B1512751
theorem B8070941 : Blo 1415527 8070941 := bstep (se 3 (by rfl) ⟨1513301, by rfl⟩ : syracuseStep 8070941 = 3026603) B3026603
theorem B4777865 : Blo 1415527 4777865 := bstep (se 2 (by rfl) ⟨1791699, by rfl⟩ : syracuseStep 4777865 = 3583399) B3583399
theorem B3827627 : Blo 1415527 3827627 := bstep (se 1 (by rfl) ⟨2870720, by rfl⟩ : syracuseStep 3827627 = 5741441) B5741441
theorem B6998057 : Blo 1415527 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B5376071 : Blo 1415527 5376071 := bstep (se 1 (by rfl) ⟨4032053, by rfl⟩ : syracuseStep 5376071 = 8064107) B8064107
theorem B12093563 : Blo 1415527 12093563 := bstep (se 1 (by rfl) ⟨9070172, by rfl⟩ : syracuseStep 12093563 = 18140345) B18140345
theorem B2124095 : Blo 1415527 2124095 := bstep (se 1 (by rfl) ⟨1593071, by rfl⟩ : syracuseStep 2124095 = 3186143) B3186143
theorem B8071649 : Blo 1415527 8071649 := bstep (se 2 (by rfl) ⟨3026868, by rfl⟩ : syracuseStep 8071649 = 6053737) B6053737
theorem B2124527 : Blo 1415527 2124527 := bstep (se 1 (by rfl) ⟨1593395, by rfl⟩ : syracuseStep 2124527 = 3186791) B3186791
theorem B1592527 : Blo 1415527 1592527 := bstep (se 1 (by rfl) ⟨1194395, by rfl⟩ : syracuseStep 1592527 = 2388791) B2388791
theorem B46591483 : Blo 1415527 46591483 := bstep (se 1 (by rfl) ⟨34943612, by rfl⟩ : syracuseStep 46591483 = 69887225) B69887225
theorem B1593247 : Blo 1415527 1593247 := bstep (se 1 (by rfl) ⟨1194935, by rfl⟩ : syracuseStep 1593247 = 2389871) B2389871
theorem B16134227 : Blo 1415527 16134227 := bstep (se 1 (by rfl) ⟨12100670, by rfl⟩ : syracuseStep 16134227 = 24201341) B24201341
theorem B2125931 : Blo 1415527 2125931 := bstep (se 1 (by rfl) ⟨1594448, by rfl⟩ : syracuseStep 2125931 = 3188897) B3188897
theorem B11481227 : Blo 1415527 11481227 := bstep (se 1 (by rfl) ⟨8610920, by rfl⟩ : syracuseStep 11481227 = 17221841) B17221841
theorem B6049961 : Blo 1415527 6049961 := bstep (se 2 (by rfl) ⟨2268735, by rfl⟩ : syracuseStep 6049961 = 4537471) B4537471
theorem B1593535 : Blo 1415527 1593535 := bstep (se 1 (by rfl) ⟨1195151, by rfl⟩ : syracuseStep 1593535 = 2390303) B2390303
theorem B5379155 : Blo 1415527 5379155 := bstep (se 1 (by rfl) ⟨4034366, by rfl⟩ : syracuseStep 5379155 = 8068733) B8068733
theorem B13464797 : Blo 1415527 13464797 := bstep (se 3 (by rfl) ⟨2524649, by rfl⟩ : syracuseStep 13464797 = 5049299) B5049299
theorem B1701119 : Blo 1415527 1701119 := bstep (se 1 (by rfl) ⟨1275839, by rfl⟩ : syracuseStep 1701119 = 2551679) B2551679
theorem B2389351 : Blo 1415527 2389351 := bstep (se 1 (by rfl) ⟨1792013, by rfl⟩ : syracuseStep 2389351 = 3584027) B3584027
theorem B465106373 : Blo 1415527 465106373 := bstep (se 4 (by rfl) ⟨43603722, by rfl⟩ : syracuseStep 465106373 = 87207445) B87207445
theorem B7173683 : Blo 1415527 7173683 := bstep (se 1 (by rfl) ⟨5380262, by rfl⟩ : syracuseStep 7173683 = 10760525) B10760525
theorem B1914505 : Blo 1415527 1914505 := bstep (se 2 (by rfl) ⟨717939, by rfl⟩ : syracuseStep 1914505 = 1435879) B1435879
theorem B4781915 : Blo 1415527 4781915 := bstep (se 1 (by rfl) ⟨3586436, by rfl⟩ : syracuseStep 4781915 = 7172873) B7172873
theorem B1415679 : Blo 1415527 1415679 := bstep (se 1 (by rfl) ⟨1061759, by rfl⟩ : syracuseStep 1415679 = 2123519) B2123519
theorem B1415727 : Blo 1415527 1415727 := bstep (se 1 (by rfl) ⟨1061795, by rfl⟩ : syracuseStep 1415727 = 2123591) B2123591
theorem B3185207 : Blo 1415527 3185207 := bstep (se 1 (by rfl) ⟨2388905, by rfl⟩ : syracuseStep 3185207 = 4777811) B4777811
theorem B1415847 : Blo 1415527 1415847 := bstep (se 1 (by rfl) ⟨1061885, by rfl⟩ : syracuseStep 1415847 = 2123771) B2123771
theorem B3586751 : Blo 1415527 3586751 := bstep (se 1 (by rfl) ⟨2690063, by rfl⟩ : syracuseStep 3586751 = 5380127) B5380127
theorem B1415887 : Blo 1415527 1415887 := bstep (se 1 (by rfl) ⟨1061915, by rfl⟩ : syracuseStep 1415887 = 2123831) B2123831
theorem B124148467 : Blo 1415527 124148467 := bstep (se 1 (by rfl) ⟨93111350, by rfl⟩ : syracuseStep 124148467 = 186222701) B186222701
theorem B1415967 : Blo 1415527 1415967 := bstep (se 1 (by rfl) ⟨1061975, by rfl⟩ : syracuseStep 1415967 = 2123951) B2123951
theorem B1416127 : Blo 1415527 1416127 := bstep (se 1 (by rfl) ⟨1062095, by rfl⟩ : syracuseStep 1416127 = 2124191) B2124191
theorem B1416255 : Blo 1415527 1416255 := bstep (se 1 (by rfl) ⟨1062191, by rfl⟩ : syracuseStep 1416255 = 2124383) B2124383
theorem B2391113 : Blo 1415527 2391113 := bstep (se 2 (by rfl) ⟨896667, by rfl⟩ : syracuseStep 2391113 = 1793335) B1793335
theorem B1416303 : Blo 1415527 1416303 := bstep (se 1 (by rfl) ⟨1062227, by rfl⟩ : syracuseStep 1416303 = 2124455) B2124455
theorem B1416347 : Blo 1415527 1416347 := bstep (se 1 (by rfl) ⟨1062260, by rfl⟩ : syracuseStep 1416347 = 2124521) B2124521
theorem B4783265 : Blo 1415527 4783265 := bstep (se 2 (by rfl) ⟨1793724, by rfl⟩ : syracuseStep 4783265 = 3587449) B3587449
theorem B1416383 : Blo 1415527 1416383 := bstep (se 1 (by rfl) ⟨1062287, by rfl⟩ : syracuseStep 1416383 = 2124575) B2124575
theorem B5381417 : Blo 1415527 5381417 := bstep (se 2 (by rfl) ⟨2018031, by rfl⟩ : syracuseStep 5381417 = 4036063) B4036063
theorem B1416495 : Blo 1415527 1416495 := bstep (se 1 (by rfl) ⟨1062371, by rfl⟩ : syracuseStep 1416495 = 2124743) B2124743
theorem B1416575 : Blo 1415527 1416575 := bstep (se 1 (by rfl) ⟨1062431, by rfl⟩ : syracuseStep 1416575 = 2124863) B2124863
theorem B3587561 : Blo 1415527 3587561 := bstep (se 2 (by rfl) ⟨1345335, by rfl⟩ : syracuseStep 3587561 = 2690671) B2690671
theorem B1416703 : Blo 1415527 1416703 := bstep (se 1 (by rfl) ⟨1062527, by rfl⟩ : syracuseStep 1416703 = 2125055) B2125055
theorem B1416735 : Blo 1415527 1416735 := bstep (se 1 (by rfl) ⟨1062551, by rfl⟩ : syracuseStep 1416735 = 2125103) B2125103
theorem B32702075 : Blo 1415527 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B1416859 : Blo 1415527 1416859 := bstep (se 1 (by rfl) ⟨1062644, by rfl⟩ : syracuseStep 1416859 = 2125289) B2125289
theorem B13106843 : Blo 1415527 13106843 := bstep (se 1 (by rfl) ⟨9830132, by rfl⟩ : syracuseStep 13106843 = 19660265) B19660265
theorem B1416895 : Blo 1415527 1416895 := bstep (se 1 (by rfl) ⟨1062671, by rfl⟩ : syracuseStep 1416895 = 2125343) B2125343
theorem B6053753 : Blo 1415527 6053753 := bstep (se 2 (by rfl) ⟨2270157, by rfl⟩ : syracuseStep 6053753 = 4540315) B4540315
theorem B66338777 : Blo 1415527 66338777 := bstep (se 2 (by rfl) ⟨24877041, by rfl⟩ : syracuseStep 66338777 = 49754083) B49754083
theorem B10756151 : Blo 1415527 10756151 := bstep (se 1 (by rfl) ⟨8067113, by rfl⟩ : syracuseStep 10756151 = 16134227) B16134227
theorem B1417287 : Blo 1415527 1417287 := bstep (se 1 (by rfl) ⟨1062965, by rfl⟩ : syracuseStep 1417287 = 2125931) B2125931
theorem B3686543 : Blo 1415527 3686543 := bstep (se 1 (by rfl) ⟨2764907, by rfl⟩ : syracuseStep 3686543 = 5529815) B5529815
theorem B40370699 : Blo 1415527 40370699 := bstep (se 1 (by rfl) ⟨30278024, by rfl⟩ : syracuseStep 40370699 = 60556049) B60556049
theorem B35906125 : Blo 1415527 35906125 := bstep (se 3 (by rfl) ⟨6732398, by rfl⟩ : syracuseStep 35906125 = 13464797) B13464797
theorem B3187943 : Blo 1415527 3187943 := bstep (se 1 (by rfl) ⟨2390957, by rfl⟩ : syracuseStep 3187943 = 4781915) B4781915
theorem B8062375 : Blo 1415527 8062375 := bstep (se 1 (by rfl) ⟨6046781, by rfl⟩ : syracuseStep 8062375 = 12093563) B12093563
theorem B45975113 : Blo 1415527 45975113 := bstep (se 2 (by rfl) ⟨17240667, by rfl⟩ : syracuseStep 45975113 = 34481335) B34481335
theorem B2123369 : Blo 1415527 2123369 := bstep (se 2 (by rfl) ⟨796263, by rfl⟩ : syracuseStep 2123369 = 1592527) B1592527
theorem B2123471 : Blo 1415527 2123471 := bstep (se 1 (by rfl) ⟨1592603, by rfl⟩ : syracuseStep 2123471 = 3185207) B3185207
theorem B62121977 : Blo 1415527 62121977 := bstep (se 2 (by rfl) ⟨23295741, by rfl⟩ : syracuseStep 62121977 = 46591483) B46591483
theorem B3188843 : Blo 1415527 3188843 := bstep (se 1 (by rfl) ⟨2391632, by rfl⟩ : syracuseStep 3188843 = 4783265) B4783265
theorem B21801383 : Blo 1415527 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B2124329 : Blo 1415527 2124329 := bstep (se 2 (by rfl) ⟨796623, by rfl⟩ : syracuseStep 2124329 = 1593247) B1593247
theorem B7654151 : Blo 1415527 7654151 := bstep (se 1 (by rfl) ⟨5740613, by rfl⟩ : syracuseStep 7654151 = 11481227) B11481227
theorem B4033307 : Blo 1415527 4033307 := bstep (se 1 (by rfl) ⟨3024980, by rfl⟩ : syracuseStep 4033307 = 6049961) B6049961
theorem B4778783 : Blo 1415527 4778783 := bstep (se 1 (by rfl) ⟨3584087, by rfl⟩ : syracuseStep 4778783 = 7168175) B7168175
theorem B2124647 : Blo 1415527 2124647 := bstep (se 1 (by rfl) ⟨1593485, by rfl⟩ : syracuseStep 2124647 = 3186971) B3186971
theorem B2124713 : Blo 1415527 2124713 := bstep (se 2 (by rfl) ⟨796767, by rfl⟩ : syracuseStep 2124713 = 1593535) B1593535
theorem B31058939 : Blo 1415527 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B2125031 : Blo 1415527 2125031 := bstep (se 1 (by rfl) ⟨1593773, by rfl⟩ : syracuseStep 2125031 = 3187547) B3187547
theorem B10210693 : Blo 1415527 10210693 := bstep (se 4 (by rfl) ⟨957252, by rfl⟩ : syracuseStep 10210693 = 1914505) B1914505
theorem B43625911 : Blo 1415527 43625911 := bstep (se 1 (by rfl) ⟨32719433, by rfl⟩ : syracuseStep 43625911 = 65438867) B65438867
theorem B2125247 : Blo 1415527 2125247 := bstep (se 1 (by rfl) ⟨1593935, by rfl⟩ : syracuseStep 2125247 = 3187871) B3187871
theorem B310070915 : Blo 1415527 310070915 := bstep (se 1 (by rfl) ⟨232553186, by rfl⟩ : syracuseStep 310070915 = 465106373) B465106373
theorem B165531289 : Blo 1415527 165531289 := bstep (se 2 (by rfl) ⟨62074233, by rfl⟩ : syracuseStep 165531289 = 124148467) B124148467
theorem B2551751 : Blo 1415527 2551751 := bstep (se 1 (by rfl) ⟨1913813, by rfl⟩ : syracuseStep 2551751 = 3827627) B3827627
theorem B4665371 : Blo 1415527 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B3584047 : Blo 1415527 3584047 := bstep (se 1 (by rfl) ⟨2688035, by rfl⟩ : syracuseStep 3584047 = 5376071) B5376071
theorem B5378669 : Blo 1415527 5378669 := bstep (se 3 (by rfl) ⟨1008500, by rfl⟩ : syracuseStep 5378669 = 2017001) B2017001
theorem B1594075 : Blo 1415527 1594075 := bstep (se 1 (by rfl) ⟨1195556, by rfl⟩ : syracuseStep 1594075 = 2391113) B2391113
theorem B8737895 : Blo 1415527 8737895 := bstep (se 1 (by rfl) ⟨6553421, by rfl⟩ : syracuseStep 8737895 = 13106843) B13106843
theorem B4035835 : Blo 1415527 4035835 := bstep (se 1 (by rfl) ⟨3026876, by rfl⟩ : syracuseStep 4035835 = 6053753) B6053753
theorem B44225851 : Blo 1415527 44225851 := bstep (se 1 (by rfl) ⟨33169388, by rfl⟩ : syracuseStep 44225851 = 66338777) B66338777
theorem B4536317 : Blo 1415527 4536317 := bstep (se 3 (by rfl) ⟨850559, by rfl⟩ : syracuseStep 4536317 = 1701119) B1701119
theorem B3586103 : Blo 1415527 3586103 := bstep (se 1 (by rfl) ⟨2689577, by rfl⟩ : syracuseStep 3586103 = 5379155) B5379155
theorem B2300143 : Blo 1415527 2300143 := bstep (se 1 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 2300143 = 3450215) B3450215
theorem B4782455 : Blo 1415527 4782455 := bstep (se 1 (by rfl) ⟨3586841, by rfl⟩ : syracuseStep 4782455 = 7173683) B7173683
theorem B5380627 : Blo 1415527 5380627 := bstep (se 1 (by rfl) ⟨4035470, by rfl⟩ : syracuseStep 5380627 = 8070941) B8070941
theorem B3185243 : Blo 1415527 3185243 := bstep (se 1 (by rfl) ⟨2388932, by rfl⟩ : syracuseStep 3185243 = 4777865) B4777865
theorem B1416063 : Blo 1415527 1416063 := bstep (se 1 (by rfl) ⟨1062047, by rfl⟩ : syracuseStep 1416063 = 2124095) B2124095
theorem B5381099 : Blo 1415527 5381099 := bstep (se 1 (by rfl) ⟨4035824, by rfl⟩ : syracuseStep 5381099 = 8071649) B8071649
theorem B2391167 : Blo 1415527 2391167 := bstep (se 1 (by rfl) ⟨1793375, by rfl⟩ : syracuseStep 2391167 = 3586751) B3586751
theorem B3185801 : Blo 1415527 3185801 := bstep (se 2 (by rfl) ⟨1194675, by rfl⟩ : syracuseStep 3185801 = 2389351) B2389351
theorem B1416351 : Blo 1415527 1416351 := bstep (se 1 (by rfl) ⟨1062263, by rfl⟩ : syracuseStep 1416351 = 2124527) B2124527
theorem B155147557 : Blo 1415527 155147557 := bstep (se 4 (by rfl) ⟨14545083, by rfl⟩ : syracuseStep 155147557 = 29090167) B29090167
theorem B3587611 : Blo 1415527 3587611 := bstep (se 1 (by rfl) ⟨2690708, by rfl⟩ : syracuseStep 3587611 = 5381417) B5381417
theorem B2391707 : Blo 1415527 2391707 := bstep (se 1 (by rfl) ⟨1793780, by rfl⟩ : syracuseStep 2391707 = 3587561) B3587561
theorem B2457695 : Blo 1415527 2457695 := bstep (se 1 (by rfl) ⟨1843271, by rfl⟩ : syracuseStep 2457695 = 3686543) B3686543
theorem B5825263 : Blo 1415527 5825263 := bstep (se 1 (by rfl) ⟨4368947, by rfl⟩ : syracuseStep 5825263 = 8737895) B8737895
theorem B47874833 : Blo 1415527 47874833 := bstep (se 2 (by rfl) ⟨17953062, by rfl⟩ : syracuseStep 47874833 = 35906125) B35906125
theorem B3024211 : Blo 1415527 3024211 := bstep (se 1 (by rfl) ⟨2268158, by rfl⟩ : syracuseStep 3024211 = 4536317) B4536317
theorem B3188303 : Blo 1415527 3188303 := bstep (se 1 (by rfl) ⟨2391227, by rfl⟩ : syracuseStep 3188303 = 4782455) B4782455
theorem B14534255 : Blo 1415527 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B2123495 : Blo 1415527 2123495 := bstep (se 1 (by rfl) ⟨1592621, by rfl⟩ : syracuseStep 2123495 = 3185243) B3185243
theorem B58967801 : Blo 1415527 58967801 := bstep (se 2 (by rfl) ⟨22112925, by rfl⟩ : syracuseStep 58967801 = 44225851) B44225851
theorem B2688871 : Blo 1415527 2688871 := bstep (se 1 (by rfl) ⟨2016653, by rfl⟩ : syracuseStep 2688871 = 4033307) B4033307
theorem B10749833 : Blo 1415527 10749833 := bstep (se 2 (by rfl) ⟨4031187, by rfl⟩ : syracuseStep 10749833 = 8062375) B8062375
theorem B2123867 : Blo 1415527 2123867 := bstep (se 1 (by rfl) ⟨1592900, by rfl⟩ : syracuseStep 2123867 = 3185801) B3185801
theorem B7170767 : Blo 1415527 7170767 := bstep (se 1 (by rfl) ⟨5378075, by rfl⟩ : syracuseStep 7170767 = 10756151) B10756151
theorem B4778729 : Blo 1415527 4778729 := bstep (se 2 (by rfl) ⟨1792023, by rfl⟩ : syracuseStep 4778729 = 3584047) B3584047
theorem B3066857 : Blo 1415527 3066857 := bstep (se 2 (by rfl) ⟨1150071, by rfl⟩ : syracuseStep 3066857 = 2300143) B2300143
theorem B26913799 : Blo 1415527 26913799 := bstep (se 1 (by rfl) ⟨20185349, by rfl⟩ : syracuseStep 26913799 = 40370699) B40370699
theorem B2125295 : Blo 1415527 2125295 := bstep (se 1 (by rfl) ⟨1593971, by rfl⟩ : syracuseStep 2125295 = 3187943) B3187943
theorem B2125433 : Blo 1415527 2125433 := bstep (se 2 (by rfl) ⟨797037, by rfl⟩ : syracuseStep 2125433 = 1594075) B1594075
theorem B30650075 : Blo 1415527 30650075 := bstep (se 1 (by rfl) ⟨22987556, by rfl⟩ : syracuseStep 30650075 = 45975113) B45975113
theorem B41414651 : Blo 1415527 41414651 := bstep (se 1 (by rfl) ⟨31060988, by rfl⟩ : syracuseStep 41414651 = 62121977) B62121977
theorem B2125895 : Blo 1415527 2125895 := bstep (se 1 (by rfl) ⟨1594421, by rfl⟩ : syracuseStep 2125895 = 3188843) B3188843
theorem B58167881 : Blo 1415527 58167881 := bstep (se 2 (by rfl) ⟨21812955, by rfl⟩ : syracuseStep 58167881 = 43625911) B43625911
theorem B20705959 : Blo 1415527 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B1594111 : Blo 1415527 1594111 := bstep (se 1 (by rfl) ⟨1195583, by rfl⟩ : syracuseStep 1594111 = 2391167) B2391167
theorem B206713943 : Blo 1415527 206713943 := bstep (se 1 (by rfl) ⟨155035457, by rfl⟩ : syracuseStep 206713943 = 310070915) B310070915
theorem B1594471 : Blo 1415527 1594471 := bstep (se 1 (by rfl) ⟨1195853, by rfl⟩ : syracuseStep 1594471 = 2391707) B2391707
theorem B1701167 : Blo 1415527 1701167 := bstep (se 1 (by rfl) ⟨1275875, by rfl⟩ : syracuseStep 1701167 = 2551751) B2551751
theorem B12440989 : Blo 1415527 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B3585779 : Blo 1415527 3585779 := bstep (se 1 (by rfl) ⟨2689334, by rfl⟩ : syracuseStep 3585779 = 5378669) B5378669
theorem B7174169 : Blo 1415527 7174169 := bstep (se 2 (by rfl) ⟨2690313, by rfl⟩ : syracuseStep 7174169 = 5380627) B5380627
theorem B1415579 : Blo 1415527 1415579 := bstep (se 1 (by rfl) ⟨1061684, by rfl⟩ : syracuseStep 1415579 = 2123369) B2123369
theorem B1415647 : Blo 1415527 1415647 := bstep (se 1 (by rfl) ⟨1061735, by rfl⟩ : syracuseStep 1415647 = 2123471) B2123471
theorem B2390735 : Blo 1415527 2390735 := bstep (se 1 (by rfl) ⟨1793051, by rfl⟩ : syracuseStep 2390735 = 3586103) B3586103
theorem B5381113 : Blo 1415527 5381113 := bstep (se 2 (by rfl) ⟨2017917, by rfl⟩ : syracuseStep 5381113 = 4035835) B4035835
theorem B1416219 : Blo 1415527 1416219 := bstep (se 1 (by rfl) ⟨1062164, by rfl⟩ : syracuseStep 1416219 = 2124329) B2124329
theorem B206863409 : Blo 1415527 206863409 := bstep (se 2 (by rfl) ⟨77573778, by rfl⟩ : syracuseStep 206863409 = 155147557) B155147557
theorem B5102767 : Blo 1415527 5102767 := bstep (se 1 (by rfl) ⟨3827075, by rfl⟩ : syracuseStep 5102767 = 7654151) B7654151
theorem B13614257 : Blo 1415527 13614257 := bstep (se 2 (by rfl) ⟨5105346, by rfl⟩ : syracuseStep 13614257 = 10210693) B10210693
theorem B3185855 : Blo 1415527 3185855 := bstep (se 1 (by rfl) ⟨2389391, by rfl⟩ : syracuseStep 3185855 = 4778783) B4778783
theorem B1416431 : Blo 1415527 1416431 := bstep (se 1 (by rfl) ⟨1062323, by rfl⟩ : syracuseStep 1416431 = 2124647) B2124647
theorem B1416475 : Blo 1415527 1416475 := bstep (se 1 (by rfl) ⟨1062356, by rfl⟩ : syracuseStep 1416475 = 2124713) B2124713
theorem B3587399 : Blo 1415527 3587399 := bstep (se 1 (by rfl) ⟨2690549, by rfl⟩ : syracuseStep 3587399 = 5381099) B5381099
theorem B4783481 : Blo 1415527 4783481 := bstep (se 2 (by rfl) ⟨1793805, by rfl⟩ : syracuseStep 4783481 = 3587611) B3587611
theorem B1416687 : Blo 1415527 1416687 := bstep (se 1 (by rfl) ⟨1062515, by rfl⟩ : syracuseStep 1416687 = 2125031) B2125031
theorem B220708385 : Blo 1415527 220708385 := bstep (se 2 (by rfl) ⟨82765644, by rfl⟩ : syracuseStep 220708385 = 165531289) B165531289
theorem B1416831 : Blo 1415527 1416831 := bstep (se 1 (by rfl) ⟨1062623, by rfl⟩ : syracuseStep 1416831 = 2125247) B2125247
theorem B143540261 : Blo 1415527 143540261 := bstep (se 4 (by rfl) ⟨13456899, by rfl⟩ : syracuseStep 143540261 = 26913799) B26913799
theorem B1417263 : Blo 1415527 1417263 := bstep (se 1 (by rfl) ⟨1062947, by rfl⟩ : syracuseStep 1417263 = 2125895) B2125895
theorem B1638463 : Blo 1415527 1638463 := bstep (se 1 (by rfl) ⟨1228847, by rfl⟩ : syracuseStep 1638463 = 2457695) B2457695
theorem B18145781 : Blo 1415527 18145781 := bstep (se 5 (by rfl) ⟨850583, by rfl⟩ : syracuseStep 18145781 = 1701167) B1701167
theorem B31916555 : Blo 1415527 31916555 := bstep (se 1 (by rfl) ⟨23937416, by rfl⟩ : syracuseStep 31916555 = 47874833) B47874833
theorem B27607945 : Blo 1415527 27607945 := bstep (se 2 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 27607945 = 20705959) B20705959
theorem B7767017 : Blo 1415527 7767017 := bstep (se 2 (by rfl) ⟨2912631, by rfl⟩ : syracuseStep 7767017 = 5825263) B5825263
theorem B38758013 : Blo 1415527 38758013 := bstep (se 3 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 38758013 = 14534255) B14534255
theorem B4032281 : Blo 1415527 4032281 := bstep (se 2 (by rfl) ⟨1512105, by rfl⟩ : syracuseStep 4032281 = 3024211) B3024211
theorem B2123903 : Blo 1415527 2123903 := bstep (se 1 (by rfl) ⟨1592927, by rfl⟩ : syracuseStep 2123903 = 3185855) B3185855
theorem B3188987 : Blo 1415527 3188987 := bstep (se 1 (by rfl) ⟨2391740, by rfl⟩ : syracuseStep 3188987 = 4783481) B4783481
theorem B147138923 : Blo 1415527 147138923 := bstep (se 1 (by rfl) ⟨110354192, by rfl⟩ : syracuseStep 147138923 = 220708385) B220708385
theorem B32713141 : Blo 1415527 32713141 := bstep (se 5 (by rfl) ⟨1533428, by rfl⟩ : syracuseStep 32713141 = 3066857) B3066857
theorem B20433383 : Blo 1415527 20433383 := bstep (se 1 (by rfl) ⟨15325037, by rfl⟩ : syracuseStep 20433383 = 30650075) B30650075
theorem B27609767 : Blo 1415527 27609767 := bstep (se 1 (by rfl) ⟨20707325, by rfl⟩ : syracuseStep 27609767 = 41414651) B41414651
theorem B137809295 : Blo 1415527 137809295 := bstep (se 1 (by rfl) ⟨103356971, by rfl⟩ : syracuseStep 137809295 = 206713943) B206713943
theorem B2125481 : Blo 1415527 2125481 := bstep (se 2 (by rfl) ⟨797055, by rfl⟩ : syracuseStep 2125481 = 1594111) B1594111
theorem B2125535 : Blo 1415527 2125535 := bstep (se 1 (by rfl) ⟨1594151, by rfl⟩ : syracuseStep 2125535 = 3188303) B3188303
theorem B2125961 : Blo 1415527 2125961 := bstep (se 2 (by rfl) ⟨797235, by rfl⟩ : syracuseStep 2125961 = 1594471) B1594471
theorem B6803689 : Blo 1415527 6803689 := bstep (se 2 (by rfl) ⟨2551383, by rfl⟩ : syracuseStep 6803689 = 5102767) B5102767
theorem B4780511 : Blo 1415527 4780511 := bstep (se 1 (by rfl) ⟨3585383, by rfl⟩ : syracuseStep 4780511 = 7170767) B7170767
theorem B1593823 : Blo 1415527 1593823 := bstep (se 1 (by rfl) ⟨1195367, by rfl⟩ : syracuseStep 1593823 = 2390735) B2390735
theorem B137908939 : Blo 1415527 137908939 := bstep (se 1 (by rfl) ⟨103431704, by rfl⟩ : syracuseStep 137908939 = 206863409) B206863409
theorem B3585161 : Blo 1415527 3585161 := bstep (se 2 (by rfl) ⟨1344435, by rfl⟩ : syracuseStep 3585161 = 2688871) B2688871
theorem B38778587 : Blo 1415527 38778587 := bstep (se 1 (by rfl) ⟨29083940, by rfl⟩ : syracuseStep 38778587 = 58167881) B58167881
theorem B1415663 : Blo 1415527 1415663 := bstep (se 1 (by rfl) ⟨1061747, by rfl⟩ : syracuseStep 1415663 = 2123495) B2123495
theorem B2390519 : Blo 1415527 2390519 := bstep (se 1 (by rfl) ⟨1792889, by rfl⟩ : syracuseStep 2390519 = 3585779) B3585779
theorem B39311867 : Blo 1415527 39311867 := bstep (se 1 (by rfl) ⟨29483900, by rfl⟩ : syracuseStep 39311867 = 58967801) B58967801
theorem B7166555 : Blo 1415527 7166555 := bstep (se 1 (by rfl) ⟨5374916, by rfl⟩ : syracuseStep 7166555 = 10749833) B10749833
theorem B7174817 : Blo 1415527 7174817 := bstep (se 2 (by rfl) ⟨2690556, by rfl⟩ : syracuseStep 7174817 = 5381113) B5381113
theorem B4782779 : Blo 1415527 4782779 := bstep (se 1 (by rfl) ⟨3587084, by rfl⟩ : syracuseStep 4782779 = 7174169) B7174169
theorem B1415911 : Blo 1415527 1415911 := bstep (se 1 (by rfl) ⟨1061933, by rfl⟩ : syracuseStep 1415911 = 2123867) B2123867
theorem B3185819 : Blo 1415527 3185819 := bstep (se 1 (by rfl) ⟨2389364, by rfl⟩ : syracuseStep 3185819 = 4778729) B4778729
theorem B16587985 : Blo 1415527 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B9076171 : Blo 1415527 9076171 := bstep (se 1 (by rfl) ⟨6807128, by rfl⟩ : syracuseStep 9076171 = 13614257) B13614257
theorem B2391599 : Blo 1415527 2391599 := bstep (se 1 (by rfl) ⟨1793699, by rfl⟩ : syracuseStep 2391599 = 3587399) B3587399
theorem B1416863 : Blo 1415527 1416863 := bstep (se 1 (by rfl) ⟨1062647, by rfl⟩ : syracuseStep 1416863 = 2125295) B2125295
theorem B1416955 : Blo 1415527 1416955 := bstep (se 1 (by rfl) ⟨1062716, by rfl⟩ : syracuseStep 1416955 = 2125433) B2125433
theorem B1417307 : Blo 1415527 1417307 := bstep (se 1 (by rfl) ⟨1062980, by rfl⟩ : syracuseStep 1417307 = 2125961) B2125961
theorem B3187007 : Blo 1415527 3187007 := bstep (se 1 (by rfl) ⟨2390255, by rfl⟩ : syracuseStep 3187007 = 4780511) B4780511
theorem B5178011 : Blo 1415527 5178011 := bstep (se 1 (by rfl) ⟨3883508, by rfl⟩ : syracuseStep 5178011 = 7767017) B7767017
theorem B183878585 : Blo 1415527 183878585 := bstep (se 2 (by rfl) ⟨68954469, by rfl⟩ : syracuseStep 183878585 = 137908939) B137908939
theorem B25838675 : Blo 1415527 25838675 := bstep (se 1 (by rfl) ⟨19379006, by rfl⟩ : syracuseStep 25838675 = 38758013) B38758013
theorem B98092615 : Blo 1415527 98092615 := bstep (se 1 (by rfl) ⟨73569461, by rfl⟩ : syracuseStep 98092615 = 147138923) B147138923
theorem B26207911 : Blo 1415527 26207911 := bstep (se 1 (by rfl) ⟨19655933, by rfl⟩ : syracuseStep 26207911 = 39311867) B39311867
theorem B4777703 : Blo 1415527 4777703 := bstep (se 1 (by rfl) ⟨3583277, by rfl⟩ : syracuseStep 4777703 = 7166555) B7166555
theorem B3188519 : Blo 1415527 3188519 := bstep (se 1 (by rfl) ⟨2391389, by rfl⟩ : syracuseStep 3188519 = 4782779) B4782779
theorem B12101561 : Blo 1415527 12101561 := bstep (se 2 (by rfl) ⟨4538085, by rfl⟩ : syracuseStep 12101561 = 9076171) B9076171
theorem B2123879 : Blo 1415527 2123879 := bstep (se 1 (by rfl) ⟨1592909, by rfl⟩ : syracuseStep 2123879 = 3185819) B3185819
theorem B95693507 : Blo 1415527 95693507 := bstep (se 1 (by rfl) ⟨71770130, by rfl⟩ : syracuseStep 95693507 = 143540261) B143540261
theorem B9071585 : Blo 1415527 9071585 := bstep (se 2 (by rfl) ⟨3401844, by rfl⟩ : syracuseStep 9071585 = 6803689) B6803689
theorem B21277703 : Blo 1415527 21277703 := bstep (se 1 (by rfl) ⟨15958277, by rfl⟩ : syracuseStep 21277703 = 31916555) B31916555
theorem B43617521 : Blo 1415527 43617521 := bstep (se 2 (by rfl) ⟨16356570, by rfl⟩ : syracuseStep 43617521 = 32713141) B32713141
theorem B2125097 : Blo 1415527 2125097 := bstep (se 2 (by rfl) ⟨796911, by rfl⟩ : syracuseStep 2125097 = 1593823) B1593823
theorem B36810593 : Blo 1415527 36810593 := bstep (se 2 (by rfl) ⟨13803972, by rfl⟩ : syracuseStep 36810593 = 27607945) B27607945
theorem B2125991 : Blo 1415527 2125991 := bstep (se 1 (by rfl) ⟨1594493, by rfl⟩ : syracuseStep 2125991 = 3188987) B3188987
theorem B1593679 : Blo 1415527 1593679 := bstep (se 1 (by rfl) ⟨1195259, by rfl⟩ : syracuseStep 1593679 = 2390519) B2390519
theorem B10752749 : Blo 1415527 10752749 := bstep (se 3 (by rfl) ⟨2016140, by rfl⟩ : syracuseStep 10752749 = 4032281) B4032281
theorem B1594399 : Blo 1415527 1594399 := bstep (se 1 (by rfl) ⟨1195799, by rfl⟩ : syracuseStep 1594399 = 2391599) B2391599
theorem B2184617 : Blo 1415527 2184617 := bstep (se 2 (by rfl) ⟨819231, by rfl⟩ : syracuseStep 2184617 = 1638463) B1638463
theorem B12097187 : Blo 1415527 12097187 := bstep (se 1 (by rfl) ⟨9072890, by rfl⟩ : syracuseStep 12097187 = 18145781) B18145781
theorem B2390107 : Blo 1415527 2390107 := bstep (se 1 (by rfl) ⟨1792580, by rfl⟩ : syracuseStep 2390107 = 3585161) B3585161
theorem B25852391 : Blo 1415527 25852391 := bstep (se 1 (by rfl) ⟨19389293, by rfl⟩ : syracuseStep 25852391 = 38778587) B38778587
theorem B1415935 : Blo 1415527 1415935 := bstep (se 1 (by rfl) ⟨1061951, by rfl⟩ : syracuseStep 1415935 = 2123903) B2123903
theorem B22117313 : Blo 1415527 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B13622255 : Blo 1415527 13622255 := bstep (se 1 (by rfl) ⟨10216691, by rfl⟩ : syracuseStep 13622255 = 20433383) B20433383
theorem B4783211 : Blo 1415527 4783211 := bstep (se 1 (by rfl) ⟨3587408, by rfl⟩ : syracuseStep 4783211 = 7174817) B7174817
theorem B18406511 : Blo 1415527 18406511 := bstep (se 1 (by rfl) ⟨13804883, by rfl⟩ : syracuseStep 18406511 = 27609767) B27609767
theorem B91872863 : Blo 1415527 91872863 := bstep (se 1 (by rfl) ⟨68904647, by rfl⟩ : syracuseStep 91872863 = 137809295) B137809295
theorem B1416987 : Blo 1415527 1416987 := bstep (se 1 (by rfl) ⟨1062740, by rfl⟩ : syracuseStep 1416987 = 2125481) B2125481
theorem B1417023 : Blo 1415527 1417023 := bstep (se 1 (by rfl) ⟨1062767, by rfl⟩ : syracuseStep 1417023 = 2125535) B2125535
theorem B1417327 : Blo 1415527 1417327 := bstep (se 1 (by rfl) ⟨1062995, by rfl⟩ : syracuseStep 1417327 = 2125991) B2125991
theorem B3186809 : Blo 1415527 3186809 := bstep (se 2 (by rfl) ⟨1195053, by rfl⟩ : syracuseStep 3186809 = 2390107) B2390107
theorem B7168499 : Blo 1415527 7168499 := bstep (se 1 (by rfl) ⟨5376374, by rfl⟩ : syracuseStep 7168499 = 10752749) B10752749
theorem B122585723 : Blo 1415527 122585723 := bstep (se 1 (by rfl) ⟨91939292, by rfl⟩ : syracuseStep 122585723 = 183878585) B183878585
theorem B5825645 : Blo 1415527 5825645 := bstep (se 3 (by rfl) ⟨1092308, by rfl⟩ : syracuseStep 5825645 = 2184617) B2184617
theorem B55232117 : Blo 1415527 55232117 := bstep (se 5 (by rfl) ⟨2589005, by rfl⟩ : syracuseStep 55232117 = 5178011) B5178011
theorem B6047723 : Blo 1415527 6047723 := bstep (se 1 (by rfl) ⟨4535792, by rfl⟩ : syracuseStep 6047723 = 9071585) B9071585
theorem B3188807 : Blo 1415527 3188807 := bstep (se 1 (by rfl) ⟨2391605, by rfl⟩ : syracuseStep 3188807 = 4783211) B4783211
theorem B2124671 : Blo 1415527 2124671 := bstep (se 1 (by rfl) ⟨1593503, by rfl⟩ : syracuseStep 2124671 = 3187007) B3187007
theorem B2124905 : Blo 1415527 2124905 := bstep (se 2 (by rfl) ⟨796839, by rfl⟩ : syracuseStep 2124905 = 1593679) B1593679
theorem B8064791 : Blo 1415527 8064791 := bstep (se 1 (by rfl) ⟨6048593, by rfl⟩ : syracuseStep 8064791 = 12097187) B12097187
theorem B2125679 : Blo 1415527 2125679 := bstep (se 1 (by rfl) ⟨1594259, by rfl⟩ : syracuseStep 2125679 = 3188519) B3188519
theorem B2125865 : Blo 1415527 2125865 := bstep (se 2 (by rfl) ⟨797199, by rfl⟩ : syracuseStep 2125865 = 1594399) B1594399
theorem B63795671 : Blo 1415527 63795671 := bstep (se 1 (by rfl) ⟨47846753, by rfl⟩ : syracuseStep 63795671 = 95693507) B95693507
theorem B9081503 : Blo 1415527 9081503 := bstep (se 1 (by rfl) ⟨6811127, by rfl⟩ : syracuseStep 9081503 = 13622255) B13622255
theorem B14185135 : Blo 1415527 14185135 := bstep (se 1 (by rfl) ⟨10638851, by rfl⟩ : syracuseStep 14185135 = 21277703) B21277703
theorem B130790153 : Blo 1415527 130790153 := bstep (se 2 (by rfl) ⟨49046307, by rfl⟩ : syracuseStep 130790153 = 98092615) B98092615
theorem B29078347 : Blo 1415527 29078347 := bstep (se 1 (by rfl) ⟨21808760, by rfl⟩ : syracuseStep 29078347 = 43617521) B43617521
theorem B34943881 : Blo 1415527 34943881 := bstep (se 2 (by rfl) ⟨13103955, by rfl⟩ : syracuseStep 34943881 = 26207911) B26207911
theorem B61248575 : Blo 1415527 61248575 := bstep (se 1 (by rfl) ⟨45936431, by rfl⟩ : syracuseStep 61248575 = 91872863) B91872863
theorem B17225783 : Blo 1415527 17225783 := bstep (se 1 (by rfl) ⟨12919337, by rfl⟩ : syracuseStep 17225783 = 25838675) B25838675
theorem B3185135 : Blo 1415527 3185135 := bstep (se 1 (by rfl) ⟨2388851, by rfl⟩ : syracuseStep 3185135 = 4777703) B4777703
theorem B8067707 : Blo 1415527 8067707 := bstep (se 1 (by rfl) ⟨6050780, by rfl⟩ : syracuseStep 8067707 = 12101561) B12101561
theorem B1570585301 : Blo 1415527 1570585301 := bstep (se 7 (by rfl) ⟨18405296, by rfl⟩ : syracuseStep 1570585301 = 36810593) B36810593
theorem B1415919 : Blo 1415527 1415919 := bstep (se 1 (by rfl) ⟨1061939, by rfl⟩ : syracuseStep 1415919 = 2123879) B2123879
theorem B17234927 : Blo 1415527 17234927 := bstep (se 1 (by rfl) ⟨12926195, by rfl⟩ : syracuseStep 17234927 = 25852391) B25852391
theorem B14744875 : Blo 1415527 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B12271007 : Blo 1415527 12271007 := bstep (se 1 (by rfl) ⟨9203255, by rfl⟩ : syracuseStep 12271007 = 18406511) B18406511
theorem B1416731 : Blo 1415527 1416731 := bstep (se 1 (by rfl) ⟨1062548, by rfl⟩ : syracuseStep 1416731 = 2125097) B2125097
theorem B1417243 : Blo 1415527 1417243 := bstep (se 1 (by rfl) ⟨1062932, by rfl⟩ : syracuseStep 1417243 = 2125865) B2125865
theorem B81723815 : Blo 1415527 81723815 := bstep (se 1 (by rfl) ⟨61292861, by rfl⟩ : syracuseStep 81723815 = 122585723) B122585723
theorem B6054335 : Blo 1415527 6054335 := bstep (se 1 (by rfl) ⟨4540751, by rfl⟩ : syracuseStep 6054335 = 9081503) B9081503
theorem B3883763 : Blo 1415527 3883763 := bstep (se 1 (by rfl) ⟨2912822, by rfl⟩ : syracuseStep 3883763 = 5825645) B5825645
theorem B4031815 : Blo 1415527 4031815 := bstep (se 1 (by rfl) ⟨3023861, by rfl⟩ : syracuseStep 4031815 = 6047723) B6047723
theorem B2123423 : Blo 1415527 2123423 := bstep (se 1 (by rfl) ⟨1592567, by rfl⟩ : syracuseStep 2123423 = 3185135) B3185135
theorem B5376527 : Blo 1415527 5376527 := bstep (se 1 (by rfl) ⟨4032395, by rfl⟩ : syracuseStep 5376527 = 8064791) B8064791
theorem B2124539 : Blo 1415527 2124539 := bstep (se 1 (by rfl) ⟨1593404, by rfl⟩ : syracuseStep 2124539 = 3186809) B3186809
theorem B4778999 : Blo 1415527 4778999 := bstep (se 1 (by rfl) ⟨3584249, by rfl⟩ : syracuseStep 4778999 = 7168499) B7168499
theorem B40832383 : Blo 1415527 40832383 := bstep (se 1 (by rfl) ⟨30624287, by rfl⟩ : syracuseStep 40832383 = 61248575) B61248575
theorem B46591841 : Blo 1415527 46591841 := bstep (se 2 (by rfl) ⟨17471940, by rfl⟩ : syracuseStep 46591841 = 34943881) B34943881
theorem B2125871 : Blo 1415527 2125871 := bstep (se 1 (by rfl) ⟨1594403, by rfl⟩ : syracuseStep 2125871 = 3188807) B3188807
theorem B5378471 : Blo 1415527 5378471 := bstep (se 1 (by rfl) ⟨4033853, by rfl⟩ : syracuseStep 5378471 = 8067707) B8067707
theorem B1047056867 : Blo 1415527 1047056867 := bstep (se 1 (by rfl) ⟨785292650, by rfl⟩ : syracuseStep 1047056867 = 1570585301) B1570585301
theorem B11489951 : Blo 1415527 11489951 := bstep (se 1 (by rfl) ⟨8617463, by rfl⟩ : syracuseStep 11489951 = 17234927) B17234927
theorem B8180671 : Blo 1415527 8180671 := bstep (se 1 (by rfl) ⟨6135503, by rfl⟩ : syracuseStep 8180671 = 12271007) B12271007
theorem B42530447 : Blo 1415527 42530447 := bstep (se 1 (by rfl) ⟨31897835, by rfl⟩ : syracuseStep 42530447 = 63795671) B63795671
theorem B87193435 : Blo 1415527 87193435 := bstep (se 1 (by rfl) ⟨65395076, by rfl⟩ : syracuseStep 87193435 = 130790153) B130790153
theorem B18913513 : Blo 1415527 18913513 := bstep (se 2 (by rfl) ⟨7092567, by rfl⟩ : syracuseStep 18913513 = 14185135) B14185135
theorem B36821411 : Blo 1415527 36821411 := bstep (se 1 (by rfl) ⟨27616058, by rfl⟩ : syracuseStep 36821411 = 55232117) B55232117
theorem B38771129 : Blo 1415527 38771129 := bstep (se 2 (by rfl) ⟨14539173, by rfl⟩ : syracuseStep 38771129 = 29078347) B29078347
theorem B11483855 : Blo 1415527 11483855 := bstep (se 1 (by rfl) ⟨8612891, by rfl⟩ : syracuseStep 11483855 = 17225783) B17225783
theorem B19659833 : Blo 1415527 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B1416447 : Blo 1415527 1416447 := bstep (se 1 (by rfl) ⟨1062335, by rfl⟩ : syracuseStep 1416447 = 2124671) B2124671
theorem B1416603 : Blo 1415527 1416603 := bstep (se 1 (by rfl) ⟨1062452, by rfl⟩ : syracuseStep 1416603 = 2124905) B2124905
theorem B1417119 : Blo 1415527 1417119 := bstep (se 1 (by rfl) ⟨1062839, by rfl⟩ : syracuseStep 1417119 = 2125679) B2125679
theorem B1417247 : Blo 1415527 1417247 := bstep (se 1 (by rfl) ⟨1062935, by rfl⟩ : syracuseStep 1417247 = 2125871) B2125871
theorem B2589175 : Blo 1415527 2589175 := bstep (se 1 (by rfl) ⟨1941881, by rfl⟩ : syracuseStep 2589175 = 3883763) B3883763
theorem B25847419 : Blo 1415527 25847419 := bstep (se 1 (by rfl) ⟨19385564, by rfl⟩ : syracuseStep 25847419 = 38771129) B38771129
theorem B30639869 : Blo 1415527 30639869 := bstep (se 3 (by rfl) ⟨5744975, by rfl⟩ : syracuseStep 30639869 = 11489951) B11489951
theorem B5375753 : Blo 1415527 5375753 := bstep (se 2 (by rfl) ⟨2015907, by rfl⟩ : syracuseStep 5375753 = 4031815) B4031815
theorem B25218017 : Blo 1415527 25218017 := bstep (se 2 (by rfl) ⟨9456756, by rfl⟩ : syracuseStep 25218017 = 18913513) B18913513
theorem B10907561 : Blo 1415527 10907561 := bstep (se 2 (by rfl) ⟨4090335, by rfl⟩ : syracuseStep 10907561 = 8180671) B8180671
theorem B24547607 : Blo 1415527 24547607 := bstep (se 1 (by rfl) ⟨18410705, by rfl⟩ : syracuseStep 24547607 = 36821411) B36821411
theorem B3584351 : Blo 1415527 3584351 := bstep (se 1 (by rfl) ⟨2688263, by rfl⟩ : syracuseStep 3584351 = 5376527) B5376527
theorem B113414525 : Blo 1415527 113414525 := bstep (se 3 (by rfl) ⟨21265223, by rfl⟩ : syracuseStep 113414525 = 42530447) B42530447
theorem B7655903 : Blo 1415527 7655903 := bstep (se 1 (by rfl) ⟨5741927, by rfl⟩ : syracuseStep 7655903 = 11483855) B11483855
theorem B116257913 : Blo 1415527 116257913 := bstep (se 2 (by rfl) ⟨43596717, by rfl⟩ : syracuseStep 116257913 = 87193435) B87193435
theorem B31061227 : Blo 1415527 31061227 := bstep (se 1 (by rfl) ⟨23295920, by rfl⟩ : syracuseStep 31061227 = 46591841) B46591841
theorem B3585647 : Blo 1415527 3585647 := bstep (se 1 (by rfl) ⟨2689235, by rfl⟩ : syracuseStep 3585647 = 5378471) B5378471
theorem B54482543 : Blo 1415527 54482543 := bstep (se 1 (by rfl) ⟨40861907, by rfl⟩ : syracuseStep 54482543 = 81723815) B81723815
theorem B4036223 : Blo 1415527 4036223 := bstep (se 1 (by rfl) ⟨3027167, by rfl⟩ : syracuseStep 4036223 = 6054335) B6054335
theorem B698037911 : Blo 1415527 698037911 := bstep (se 1 (by rfl) ⟨523528433, by rfl⟩ : syracuseStep 698037911 = 1047056867) B1047056867
theorem B1415615 : Blo 1415527 1415615 := bstep (se 1 (by rfl) ⟨1061711, by rfl⟩ : syracuseStep 1415615 = 2123423) B2123423
theorem B1416359 : Blo 1415527 1416359 := bstep (se 1 (by rfl) ⟨1062269, by rfl⟩ : syracuseStep 1416359 = 2124539) B2124539
theorem B54443177 : Blo 1415527 54443177 := bstep (se 2 (by rfl) ⟨20416191, by rfl⟩ : syracuseStep 54443177 = 40832383) B40832383
theorem B3185999 : Blo 1415527 3185999 := bstep (se 1 (by rfl) ⟨2389499, by rfl⟩ : syracuseStep 3185999 = 4778999) B4778999
theorem B13106555 : Blo 1415527 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B5103935 : Blo 1415527 5103935 := bstep (se 1 (by rfl) ⟨3827951, by rfl⟩ : syracuseStep 5103935 = 7655903) B7655903
theorem B77505275 : Blo 1415527 77505275 := bstep (se 1 (by rfl) ⟨58128956, by rfl⟩ : syracuseStep 77505275 = 116257913) B116257913
theorem B16812011 : Blo 1415527 16812011 := bstep (se 1 (by rfl) ⟨12609008, by rfl⟩ : syracuseStep 16812011 = 25218017) B25218017
theorem B2123999 : Blo 1415527 2123999 := bstep (se 1 (by rfl) ⟨1592999, by rfl⟩ : syracuseStep 2123999 = 3185999) B3185999
theorem B2690815 : Blo 1415527 2690815 := bstep (se 1 (by rfl) ⟨2018111, by rfl⟩ : syracuseStep 2690815 = 4036223) B4036223
theorem B465358607 : Blo 1415527 465358607 := bstep (se 1 (by rfl) ⟨349018955, by rfl⟩ : syracuseStep 465358607 = 698037911) B698037911
theorem B20426579 : Blo 1415527 20426579 := bstep (se 1 (by rfl) ⟨15319934, by rfl⟩ : syracuseStep 20426579 = 30639869) B30639869
theorem B3583835 : Blo 1415527 3583835 := bstep (se 1 (by rfl) ⟨2687876, by rfl⟩ : syracuseStep 3583835 = 5375753) B5375753
theorem B41414969 : Blo 1415527 41414969 := bstep (se 2 (by rfl) ⟨15530613, by rfl⟩ : syracuseStep 41414969 = 31061227) B31061227
theorem B36295451 : Blo 1415527 36295451 := bstep (se 1 (by rfl) ⟨27221588, by rfl⟩ : syracuseStep 36295451 = 54443177) B54443177
theorem B8737703 : Blo 1415527 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B7271707 : Blo 1415527 7271707 := bstep (se 1 (by rfl) ⟨5453780, by rfl⟩ : syracuseStep 7271707 = 10907561) B10907561
theorem B13808933 : Blo 1415527 13808933 := bstep (se 4 (by rfl) ⟨1294587, by rfl⟩ : syracuseStep 13808933 = 2589175) B2589175
theorem B16365071 : Blo 1415527 16365071 := bstep (se 1 (by rfl) ⟨12273803, by rfl⟩ : syracuseStep 16365071 = 24547607) B24547607
theorem B2389567 : Blo 1415527 2389567 := bstep (se 1 (by rfl) ⟨1792175, by rfl⟩ : syracuseStep 2389567 = 3584351) B3584351
theorem B75609683 : Blo 1415527 75609683 := bstep (se 1 (by rfl) ⟨56707262, by rfl⟩ : syracuseStep 75609683 = 113414525) B113414525
theorem B2390431 : Blo 1415527 2390431 := bstep (se 1 (by rfl) ⟨1792823, by rfl⟩ : syracuseStep 2390431 = 3585647) B3585647
theorem B36321695 : Blo 1415527 36321695 := bstep (se 1 (by rfl) ⟨27241271, by rfl⟩ : syracuseStep 36321695 = 54482543) B54482543
theorem B34463225 : Blo 1415527 34463225 := bstep (se 2 (by rfl) ⟨12923709, by rfl⟩ : syracuseStep 34463225 = 25847419) B25847419
theorem B3187241 : Blo 1415527 3187241 := bstep (se 2 (by rfl) ⟨1195215, by rfl⟩ : syracuseStep 3187241 = 2390431) B2390431
theorem B5825135 : Blo 1415527 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B50406455 : Blo 1415527 50406455 := bstep (se 1 (by rfl) ⟨37804841, by rfl⟩ : syracuseStep 50406455 = 75609683) B75609683
theorem B11208007 : Blo 1415527 11208007 := bstep (se 1 (by rfl) ⟨8406005, by rfl⟩ : syracuseStep 11208007 = 16812011) B16812011
theorem B13617719 : Blo 1415527 13617719 := bstep (se 1 (by rfl) ⟨10213289, by rfl⟩ : syracuseStep 13617719 = 20426579) B20426579
theorem B27609979 : Blo 1415527 27609979 := bstep (se 1 (by rfl) ⟨20707484, by rfl⟩ : syracuseStep 27609979 = 41414969) B41414969
theorem B3402623 : Blo 1415527 3402623 := bstep (se 1 (by rfl) ⟨2551967, by rfl⟩ : syracuseStep 3402623 = 5103935) B5103935
theorem B51670183 : Blo 1415527 51670183 := bstep (se 1 (by rfl) ⟨38752637, by rfl⟩ : syracuseStep 51670183 = 77505275) B77505275
theorem B9695609 : Blo 1415527 9695609 := bstep (se 2 (by rfl) ⟨3635853, by rfl⟩ : syracuseStep 9695609 = 7271707) B7271707
theorem B22975483 : Blo 1415527 22975483 := bstep (se 1 (by rfl) ⟨17231612, by rfl⟩ : syracuseStep 22975483 = 34463225) B34463225
theorem B2389223 : Blo 1415527 2389223 := bstep (se 1 (by rfl) ⟨1791917, by rfl⟩ : syracuseStep 2389223 = 3583835) B3583835
theorem B24196967 : Blo 1415527 24196967 := bstep (se 1 (by rfl) ⟨18147725, by rfl⟩ : syracuseStep 24196967 = 36295451) B36295451
theorem B9205955 : Blo 1415527 9205955 := bstep (se 1 (by rfl) ⟨6904466, by rfl⟩ : syracuseStep 9205955 = 13808933) B13808933
theorem B10910047 : Blo 1415527 10910047 := bstep (se 1 (by rfl) ⟨8182535, by rfl⟩ : syracuseStep 10910047 = 16365071) B16365071
theorem B1415999 : Blo 1415527 1415999 := bstep (se 1 (by rfl) ⟨1061999, by rfl⟩ : syracuseStep 1415999 = 2123999) B2123999
theorem B24214463 : Blo 1415527 24214463 := bstep (se 1 (by rfl) ⟨18160847, by rfl⟩ : syracuseStep 24214463 = 36321695) B36321695
theorem B3186089 : Blo 1415527 3186089 := bstep (se 2 (by rfl) ⟨1194783, by rfl⟩ : syracuseStep 3186089 = 2389567) B2389567
theorem B3587753 : Blo 1415527 3587753 := bstep (se 2 (by rfl) ⟨1345407, by rfl⟩ : syracuseStep 3587753 = 2690815) B2690815
theorem B310239071 : Blo 1415527 310239071 := bstep (se 1 (by rfl) ⟨232679303, by rfl⟩ : syracuseStep 310239071 = 465358607) B465358607
theorem B6463739 : Blo 1415527 6463739 := bstep (se 1 (by rfl) ⟨4847804, by rfl⟩ : syracuseStep 6463739 = 9695609) B9695609
theorem B33604303 : Blo 1415527 33604303 := bstep (se 1 (by rfl) ⟨25203227, by rfl⟩ : syracuseStep 33604303 = 50406455) B50406455
theorem B16131311 : Blo 1415527 16131311 := bstep (se 1 (by rfl) ⟨12098483, by rfl⟩ : syracuseStep 16131311 = 24196967) B24196967
theorem B6137303 : Blo 1415527 6137303 := bstep (se 1 (by rfl) ⟨4602977, by rfl⟩ : syracuseStep 6137303 = 9205955) B9205955
theorem B15533693 : Blo 1415527 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B9078479 : Blo 1415527 9078479 := bstep (se 1 (by rfl) ⟨6808859, by rfl⟩ : syracuseStep 9078479 = 13617719) B13617719
theorem B14944009 : Blo 1415527 14944009 := bstep (se 2 (by rfl) ⟨5604003, by rfl⟩ : syracuseStep 14944009 = 11208007) B11208007
theorem B2124059 : Blo 1415527 2124059 := bstep (se 1 (by rfl) ⟨1593044, by rfl⟩ : syracuseStep 2124059 = 3186089) B3186089
theorem B206826047 : Blo 1415527 206826047 := bstep (se 1 (by rfl) ⟨155119535, by rfl⟩ : syracuseStep 206826047 = 310239071) B310239071
theorem B2124827 : Blo 1415527 2124827 := bstep (se 1 (by rfl) ⟨1593620, by rfl⟩ : syracuseStep 2124827 = 3187241) B3187241
theorem B1592815 : Blo 1415527 1592815 := bstep (se 1 (by rfl) ⟨1194611, by rfl⟩ : syracuseStep 1592815 = 2389223) B2389223
theorem B30633977 : Blo 1415527 30633977 := bstep (se 2 (by rfl) ⟨11487741, by rfl⟩ : syracuseStep 30633977 = 22975483) B22975483
theorem B16142975 : Blo 1415527 16142975 := bstep (se 1 (by rfl) ⟨12107231, by rfl⟩ : syracuseStep 16142975 = 24214463) B24214463
theorem B14546729 : Blo 1415527 14546729 := bstep (se 2 (by rfl) ⟨5455023, by rfl⟩ : syracuseStep 14546729 = 10910047) B10910047
theorem B36813305 : Blo 1415527 36813305 := bstep (se 2 (by rfl) ⟨13804989, by rfl⟩ : syracuseStep 36813305 = 27609979) B27609979
theorem B68893577 : Blo 1415527 68893577 := bstep (se 2 (by rfl) ⟨25835091, by rfl⟩ : syracuseStep 68893577 = 51670183) B51670183
theorem B2268415 : Blo 1415527 2268415 := bstep (se 1 (by rfl) ⟨1701311, by rfl⟩ : syracuseStep 2268415 = 3402623) B3402623
theorem B2391835 : Blo 1415527 2391835 := bstep (se 1 (by rfl) ⟨1793876, by rfl⟩ : syracuseStep 2391835 = 3587753) B3587753
theorem B17236637 : Blo 1415527 17236637 := bstep (se 3 (by rfl) ⟨3231869, by rfl⟩ : syracuseStep 17236637 = 6463739) B6463739
theorem B10355795 : Blo 1415527 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B3024553 : Blo 1415527 3024553 := bstep (se 2 (by rfl) ⟨1134207, by rfl⟩ : syracuseStep 3024553 = 2268415) B2268415
theorem B2123753 : Blo 1415527 2123753 := bstep (se 2 (by rfl) ⟨796407, by rfl⟩ : syracuseStep 2123753 = 1592815) B1592815
theorem B19925345 : Blo 1415527 19925345 := bstep (se 2 (by rfl) ⟨7472004, by rfl⟩ : syracuseStep 19925345 = 14944009) B14944009
theorem B3189113 : Blo 1415527 3189113 := bstep (se 2 (by rfl) ⟨1195917, by rfl⟩ : syracuseStep 3189113 = 2391835) B2391835
theorem B44805737 : Blo 1415527 44805737 := bstep (se 2 (by rfl) ⟨16802151, by rfl⟩ : syracuseStep 44805737 = 33604303) B33604303
theorem B137884031 : Blo 1415527 137884031 := bstep (se 1 (by rfl) ⟨103413023, by rfl⟩ : syracuseStep 137884031 = 206826047) B206826047
theorem B45929051 : Blo 1415527 45929051 := bstep (se 1 (by rfl) ⟨34446788, by rfl⟩ : syracuseStep 45929051 = 68893577) B68893577
theorem B10761983 : Blo 1415527 10761983 := bstep (se 1 (by rfl) ⟨8071487, by rfl⟩ : syracuseStep 10761983 = 16142975) B16142975
theorem B10754207 : Blo 1415527 10754207 := bstep (se 1 (by rfl) ⟨8065655, by rfl⟩ : syracuseStep 10754207 = 16131311) B16131311
theorem B6052319 : Blo 1415527 6052319 := bstep (se 1 (by rfl) ⟨4539239, by rfl⟩ : syracuseStep 6052319 = 9078479) B9078479
theorem B9697819 : Blo 1415527 9697819 := bstep (se 1 (by rfl) ⟨7273364, by rfl⟩ : syracuseStep 9697819 = 14546729) B14546729
theorem B16366141 : Blo 1415527 16366141 := bstep (se 3 (by rfl) ⟨3068651, by rfl⟩ : syracuseStep 16366141 = 6137303) B6137303
theorem B1416039 : Blo 1415527 1416039 := bstep (se 1 (by rfl) ⟨1062029, by rfl⟩ : syracuseStep 1416039 = 2124059) B2124059
theorem B24542203 : Blo 1415527 24542203 := bstep (se 1 (by rfl) ⟨18406652, by rfl⟩ : syracuseStep 24542203 = 36813305) B36813305
theorem B20422651 : Blo 1415527 20422651 := bstep (se 1 (by rfl) ⟨15316988, by rfl⟩ : syracuseStep 20422651 = 30633977) B30633977
theorem B1416551 : Blo 1415527 1416551 := bstep (se 1 (by rfl) ⟨1062413, by rfl⟩ : syracuseStep 1416551 = 2124827) B2124827
theorem B91922687 : Blo 1415527 91922687 := bstep (se 1 (by rfl) ⟨68942015, by rfl⟩ : syracuseStep 91922687 = 137884031) B137884031
theorem B7169471 : Blo 1415527 7169471 := bstep (se 1 (by rfl) ⟨5377103, by rfl⟩ : syracuseStep 7169471 = 10754207) B10754207
theorem B4032737 : Blo 1415527 4032737 := bstep (se 2 (by rfl) ⟨1512276, by rfl⟩ : syracuseStep 4032737 = 3024553) B3024553
theorem B29870491 : Blo 1415527 29870491 := bstep (se 1 (by rfl) ⟨22402868, by rfl⟩ : syracuseStep 29870491 = 44805737) B44805737
theorem B12930425 : Blo 1415527 12930425 := bstep (se 2 (by rfl) ⟨4848909, by rfl⟩ : syracuseStep 12930425 = 9697819) B9697819
theorem B32722937 : Blo 1415527 32722937 := bstep (se 2 (by rfl) ⟨12271101, by rfl⟩ : syracuseStep 32722937 = 24542203) B24542203
theorem B13283563 : Blo 1415527 13283563 := bstep (se 1 (by rfl) ⟨9962672, by rfl⟩ : syracuseStep 13283563 = 19925345) B19925345
theorem B2126075 : Blo 1415527 2126075 := bstep (se 1 (by rfl) ⟨1594556, by rfl⟩ : syracuseStep 2126075 = 3189113) B3189113
theorem B4034879 : Blo 1415527 4034879 := bstep (se 1 (by rfl) ⟨3026159, by rfl⟩ : syracuseStep 4034879 = 6052319) B6052319
theorem B30619367 : Blo 1415527 30619367 := bstep (se 1 (by rfl) ⟨22964525, by rfl⟩ : syracuseStep 30619367 = 45929051) B45929051
theorem B11491091 : Blo 1415527 11491091 := bstep (se 1 (by rfl) ⟨8618318, by rfl⟩ : syracuseStep 11491091 = 17236637) B17236637
theorem B6903863 : Blo 1415527 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B21821521 : Blo 1415527 21821521 := bstep (se 2 (by rfl) ⟨8183070, by rfl⟩ : syracuseStep 21821521 = 16366141) B16366141
theorem B7174655 : Blo 1415527 7174655 := bstep (se 1 (by rfl) ⟨5380991, by rfl⟩ : syracuseStep 7174655 = 10761983) B10761983
theorem B1415835 : Blo 1415527 1415835 := bstep (se 1 (by rfl) ⟨1061876, by rfl⟩ : syracuseStep 1415835 = 2123753) B2123753
theorem B27230201 : Blo 1415527 27230201 := bstep (se 2 (by rfl) ⟨10211325, by rfl⟩ : syracuseStep 27230201 = 20422651) B20422651
theorem B1417383 : Blo 1415527 1417383 := bstep (se 1 (by rfl) ⟨1063037, by rfl⟩ : syracuseStep 1417383 = 2126075) B2126075
theorem B17711417 : Blo 1415527 17711417 := bstep (se 2 (by rfl) ⟨6641781, by rfl⟩ : syracuseStep 17711417 = 13283563) B13283563
theorem B7660727 : Blo 1415527 7660727 := bstep (se 1 (by rfl) ⟨5745545, by rfl⟩ : syracuseStep 7660727 = 11491091) B11491091
theorem B2688491 : Blo 1415527 2688491 := bstep (se 1 (by rfl) ⟨2016368, by rfl⟩ : syracuseStep 2688491 = 4032737) B4032737
theorem B21815291 : Blo 1415527 21815291 := bstep (se 1 (by rfl) ⟨16361468, by rfl⟩ : syracuseStep 21815291 = 32722937) B32722937
theorem B18153467 : Blo 1415527 18153467 := bstep (se 1 (by rfl) ⟨13615100, by rfl⟩ : syracuseStep 18153467 = 27230201) B27230201
theorem B8620283 : Blo 1415527 8620283 := bstep (se 1 (by rfl) ⟨6465212, by rfl⟩ : syracuseStep 8620283 = 12930425) B12930425
theorem B2689919 : Blo 1415527 2689919 := bstep (se 1 (by rfl) ⟨2017439, by rfl⟩ : syracuseStep 2689919 = 4034879) B4034879
theorem B4779647 : Blo 1415527 4779647 := bstep (se 1 (by rfl) ⟨3584735, by rfl⟩ : syracuseStep 4779647 = 7169471) B7169471
theorem B29095361 : Blo 1415527 29095361 := bstep (se 2 (by rfl) ⟨10910760, by rfl⟩ : syracuseStep 29095361 = 21821521) B21821521
theorem B61281791 : Blo 1415527 61281791 := bstep (se 1 (by rfl) ⟨45961343, by rfl⟩ : syracuseStep 61281791 = 91922687) B91922687
theorem B39827321 : Blo 1415527 39827321 := bstep (se 2 (by rfl) ⟨14935245, by rfl⟩ : syracuseStep 39827321 = 29870491) B29870491
theorem B20412911 : Blo 1415527 20412911 := bstep (se 1 (by rfl) ⟨15309683, by rfl⟩ : syracuseStep 20412911 = 30619367) B30619367
theorem B4602575 : Blo 1415527 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B4783103 : Blo 1415527 4783103 := bstep (se 1 (by rfl) ⟨3587327, by rfl⟩ : syracuseStep 4783103 = 7174655) B7174655
theorem B22987421 : Blo 1415527 22987421 := bstep (se 3 (by rfl) ⟨4310141, by rfl⟩ : syracuseStep 22987421 = 8620283) B8620283
theorem B40854527 : Blo 1415527 40854527 := bstep (se 1 (by rfl) ⟨30640895, by rfl⟩ : syracuseStep 40854527 = 61281791) B61281791
theorem B26551547 : Blo 1415527 26551547 := bstep (se 1 (by rfl) ⟨19913660, by rfl⟩ : syracuseStep 26551547 = 39827321) B39827321
theorem B7169309 : Blo 1415527 7169309 := bstep (se 3 (by rfl) ⟨1344245, by rfl⟩ : syracuseStep 7169309 = 2688491) B2688491
theorem B13608607 : Blo 1415527 13608607 := bstep (se 1 (by rfl) ⟨10206455, by rfl⟩ : syracuseStep 13608607 = 20412911) B20412911
theorem B3188735 : Blo 1415527 3188735 := bstep (se 1 (by rfl) ⟨2391551, by rfl⟩ : syracuseStep 3188735 = 4783103) B4783103
theorem B58174109 : Blo 1415527 58174109 := bstep (se 3 (by rfl) ⟨10907645, by rfl⟩ : syracuseStep 58174109 = 21815291) B21815291
theorem B12102311 : Blo 1415527 12102311 := bstep (se 1 (by rfl) ⟨9076733, by rfl⟩ : syracuseStep 12102311 = 18153467) B18153467
theorem B5107151 : Blo 1415527 5107151 := bstep (se 1 (by rfl) ⟨3830363, by rfl⟩ : syracuseStep 5107151 = 7660727) B7660727
theorem B47230445 : Blo 1415527 47230445 := bstep (se 3 (by rfl) ⟨8855708, by rfl⟩ : syracuseStep 47230445 = 17711417) B17711417
theorem B3068383 : Blo 1415527 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B19396907 : Blo 1415527 19396907 := bstep (se 1 (by rfl) ⟨14547680, by rfl⟩ : syracuseStep 19396907 = 29095361) B29095361
theorem B1793279 : Blo 1415527 1793279 := bstep (se 1 (by rfl) ⟨1344959, by rfl⟩ : syracuseStep 1793279 = 2689919) B2689919
theorem B3186431 : Blo 1415527 3186431 := bstep (se 1 (by rfl) ⟨2389823, by rfl⟩ : syracuseStep 3186431 = 4779647) B4779647
theorem B38782739 : Blo 1415527 38782739 := bstep (se 1 (by rfl) ⟨29087054, by rfl⟩ : syracuseStep 38782739 = 58174109) B58174109
theorem B2124287 : Blo 1415527 2124287 := bstep (se 1 (by rfl) ⟨1593215, by rfl⟩ : syracuseStep 2124287 = 3186431) B3186431
theorem B4091177 : Blo 1415527 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B4779539 : Blo 1415527 4779539 := bstep (se 1 (by rfl) ⟨3584654, by rfl⟩ : syracuseStep 4779539 = 7169309) B7169309
theorem B2125823 : Blo 1415527 2125823 := bstep (se 1 (by rfl) ⟨1594367, by rfl⟩ : syracuseStep 2125823 = 3188735) B3188735
theorem B12931271 : Blo 1415527 12931271 := bstep (se 1 (by rfl) ⟨9698453, by rfl⟩ : syracuseStep 12931271 = 19396907) B19396907
theorem B3404767 : Blo 1415527 3404767 := bstep (se 1 (by rfl) ⟨2553575, by rfl⟩ : syracuseStep 3404767 = 5107151) B5107151
theorem B31486963 : Blo 1415527 31486963 := bstep (se 1 (by rfl) ⟨23615222, by rfl⟩ : syracuseStep 31486963 = 47230445) B47230445
theorem B15324947 : Blo 1415527 15324947 := bstep (se 1 (by rfl) ⟨11493710, by rfl⟩ : syracuseStep 15324947 = 22987421) B22987421
theorem B4782077 : Blo 1415527 4782077 := bstep (se 3 (by rfl) ⟨896639, by rfl⟩ : syracuseStep 4782077 = 1793279) B1793279
theorem B27236351 : Blo 1415527 27236351 := bstep (se 1 (by rfl) ⟨20427263, by rfl⟩ : syracuseStep 27236351 = 40854527) B40854527
theorem B17701031 : Blo 1415527 17701031 := bstep (se 1 (by rfl) ⟨13275773, by rfl⟩ : syracuseStep 17701031 = 26551547) B26551547
theorem B8068207 : Blo 1415527 8068207 := bstep (se 1 (by rfl) ⟨6051155, by rfl⟩ : syracuseStep 8068207 = 12102311) B12102311
theorem B18144809 : Blo 1415527 18144809 := bstep (se 2 (by rfl) ⟨6804303, by rfl⟩ : syracuseStep 18144809 = 13608607) B13608607
theorem B25855159 : Blo 1415527 25855159 := bstep (se 1 (by rfl) ⟨19391369, by rfl⟩ : syracuseStep 25855159 = 38782739) B38782739
theorem B10216631 : Blo 1415527 10216631 := bstep (se 1 (by rfl) ⟨7662473, by rfl⟩ : syracuseStep 10216631 = 15324947) B15324947
theorem B4539689 : Blo 1415527 4539689 := bstep (se 2 (by rfl) ⟨1702383, by rfl⟩ : syracuseStep 4539689 = 3404767) B3404767
theorem B3188051 : Blo 1415527 3188051 := bstep (se 1 (by rfl) ⟨2391038, by rfl⟩ : syracuseStep 3188051 = 4782077) B4782077
theorem B10757609 : Blo 1415527 10757609 := bstep (se 2 (by rfl) ⟨4034103, by rfl⟩ : syracuseStep 10757609 = 8068207) B8068207
theorem B8620847 : Blo 1415527 8620847 := bstep (se 1 (by rfl) ⟨6465635, by rfl⟩ : syracuseStep 8620847 = 12931271) B12931271
theorem B18157567 : Blo 1415527 18157567 := bstep (se 1 (by rfl) ⟨13618175, by rfl⟩ : syracuseStep 18157567 = 27236351) B27236351
theorem B11800687 : Blo 1415527 11800687 := bstep (se 1 (by rfl) ⟨8850515, by rfl⟩ : syracuseStep 11800687 = 17701031) B17701031
theorem B12096539 : Blo 1415527 12096539 := bstep (se 1 (by rfl) ⟨9072404, by rfl⟩ : syracuseStep 12096539 = 18144809) B18144809
theorem B41982617 : Blo 1415527 41982617 := bstep (se 2 (by rfl) ⟨15743481, by rfl⟩ : syracuseStep 41982617 = 31486963) B31486963
theorem B1416191 : Blo 1415527 1416191 := bstep (se 1 (by rfl) ⟨1062143, by rfl⟩ : syracuseStep 1416191 = 2124287) B2124287
theorem B2727451 : Blo 1415527 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B3186359 : Blo 1415527 3186359 := bstep (se 1 (by rfl) ⟨2389769, by rfl⟩ : syracuseStep 3186359 = 4779539) B4779539
theorem B1417215 : Blo 1415527 1417215 := bstep (se 1 (by rfl) ⟨1062911, by rfl⟩ : syracuseStep 1417215 = 2125823) B2125823
theorem B34473545 : Blo 1415527 34473545 := bstep (se 2 (by rfl) ⟨12927579, by rfl⟩ : syracuseStep 34473545 = 25855159) B25855159
theorem B2124239 : Blo 1415527 2124239 := bstep (se 1 (by rfl) ⟨1593179, by rfl⟩ : syracuseStep 2124239 = 3186359) B3186359
theorem B24210089 : Blo 1415527 24210089 := bstep (se 2 (by rfl) ⟨9078783, by rfl⟩ : syracuseStep 24210089 = 18157567) B18157567
theorem B8064359 : Blo 1415527 8064359 := bstep (se 1 (by rfl) ⟨6048269, by rfl⟩ : syracuseStep 8064359 = 12096539) B12096539
theorem B3026459 : Blo 1415527 3026459 := bstep (se 1 (by rfl) ⟨2269844, by rfl⟩ : syracuseStep 3026459 = 4539689) B4539689
theorem B2125367 : Blo 1415527 2125367 := bstep (se 1 (by rfl) ⟨1594025, by rfl⟩ : syracuseStep 2125367 = 3188051) B3188051
theorem B7171739 : Blo 1415527 7171739 := bstep (se 1 (by rfl) ⟨5378804, by rfl⟩ : syracuseStep 7171739 = 10757609) B10757609
theorem B27988411 : Blo 1415527 27988411 := bstep (se 1 (by rfl) ⟨20991308, by rfl⟩ : syracuseStep 27988411 = 41982617) B41982617
theorem B5747231 : Blo 1415527 5747231 := bstep (se 1 (by rfl) ⟨4310423, by rfl⟩ : syracuseStep 5747231 = 8620847) B8620847
theorem B14546405 : Blo 1415527 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B15734249 : Blo 1415527 15734249 := bstep (se 2 (by rfl) ⟨5900343, by rfl⟩ : syracuseStep 15734249 = 11800687) B11800687
theorem B27244349 : Blo 1415527 27244349 := bstep (se 3 (by rfl) ⟨5108315, by rfl⟩ : syracuseStep 27244349 = 10216631) B10216631
theorem B18162899 : Blo 1415527 18162899 := bstep (se 1 (by rfl) ⟨13622174, by rfl⟩ : syracuseStep 18162899 = 27244349) B27244349
theorem B16140059 : Blo 1415527 16140059 := bstep (se 1 (by rfl) ⟨12105044, by rfl⟩ : syracuseStep 16140059 = 24210089) B24210089
theorem B5376239 : Blo 1415527 5376239 := bstep (se 1 (by rfl) ⟨4032179, by rfl⟩ : syracuseStep 5376239 = 8064359) B8064359
theorem B2017639 : Blo 1415527 2017639 := bstep (se 1 (by rfl) ⟨1513229, by rfl⟩ : syracuseStep 2017639 = 3026459) B3026459
theorem B37317881 : Blo 1415527 37317881 := bstep (se 2 (by rfl) ⟨13994205, by rfl⟩ : syracuseStep 37317881 = 27988411) B27988411
theorem B10489499 : Blo 1415527 10489499 := bstep (se 1 (by rfl) ⟨7867124, by rfl⟩ : syracuseStep 10489499 = 15734249) B15734249
theorem B22982363 : Blo 1415527 22982363 := bstep (se 1 (by rfl) ⟨17236772, by rfl⟩ : syracuseStep 22982363 = 34473545) B34473545
theorem B4781159 : Blo 1415527 4781159 := bstep (se 1 (by rfl) ⟨3585869, by rfl⟩ : syracuseStep 4781159 = 7171739) B7171739
theorem B9697603 : Blo 1415527 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B15325949 : Blo 1415527 15325949 := bstep (se 3 (by rfl) ⟨2873615, by rfl⟩ : syracuseStep 15325949 = 5747231) B5747231
theorem B1416159 : Blo 1415527 1416159 := bstep (se 1 (by rfl) ⟨1062119, by rfl⟩ : syracuseStep 1416159 = 2124239) B2124239
theorem B1416911 : Blo 1415527 1416911 := bstep (se 1 (by rfl) ⟨1062683, by rfl⟩ : syracuseStep 1416911 = 2125367) B2125367
theorem B3187439 : Blo 1415527 3187439 := bstep (se 1 (by rfl) ⟨2390579, by rfl⟩ : syracuseStep 3187439 = 4781159) B4781159
theorem B12108599 : Blo 1415527 12108599 := bstep (se 1 (by rfl) ⟨9081449, by rfl⟩ : syracuseStep 12108599 = 18162899) B18162899
theorem B10217299 : Blo 1415527 10217299 := bstep (se 1 (by rfl) ⟨7662974, by rfl⟩ : syracuseStep 10217299 = 15325949) B15325949
theorem B15321575 : Blo 1415527 15321575 := bstep (se 1 (by rfl) ⟨11491181, by rfl⟩ : syracuseStep 15321575 = 22982363) B22982363
theorem B12930137 : Blo 1415527 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B2690185 : Blo 1415527 2690185 := bstep (se 2 (by rfl) ⟨1008819, by rfl⟩ : syracuseStep 2690185 = 2017639) B2017639
theorem B10760039 : Blo 1415527 10760039 := bstep (se 1 (by rfl) ⟨8070029, by rfl⟩ : syracuseStep 10760039 = 16140059) B16140059
theorem B3584159 : Blo 1415527 3584159 := bstep (se 1 (by rfl) ⟨2688119, by rfl⟩ : syracuseStep 3584159 = 5376239) B5376239
theorem B6992999 : Blo 1415527 6992999 := bstep (se 1 (by rfl) ⟨5244749, by rfl⟩ : syracuseStep 6992999 = 10489499) B10489499
theorem B24878587 : Blo 1415527 24878587 := bstep (se 1 (by rfl) ⟨18658940, by rfl⟩ : syracuseStep 24878587 = 37317881) B37317881
theorem B4661999 : Blo 1415527 4661999 := bstep (se 1 (by rfl) ⟨3496499, by rfl⟩ : syracuseStep 4661999 = 6992999) B6992999
theorem B33171449 : Blo 1415527 33171449 := bstep (se 2 (by rfl) ⟨12439293, by rfl⟩ : syracuseStep 33171449 = 24878587) B24878587
theorem B8620091 : Blo 1415527 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B2124959 : Blo 1415527 2124959 := bstep (se 1 (by rfl) ⟨1593719, by rfl⟩ : syracuseStep 2124959 = 3187439) B3187439
theorem B8072399 : Blo 1415527 8072399 := bstep (se 1 (by rfl) ⟨6054299, by rfl⟩ : syracuseStep 8072399 = 12108599) B12108599
theorem B40857533 : Blo 1415527 40857533 := bstep (se 3 (by rfl) ⟨7660787, by rfl⟩ : syracuseStep 40857533 = 15321575) B15321575
theorem B7173359 : Blo 1415527 7173359 := bstep (se 1 (by rfl) ⟨5380019, by rfl⟩ : syracuseStep 7173359 = 10760039) B10760039
theorem B2389439 : Blo 1415527 2389439 := bstep (se 1 (by rfl) ⟨1792079, by rfl⟩ : syracuseStep 2389439 = 3584159) B3584159
theorem B3586913 : Blo 1415527 3586913 := bstep (se 2 (by rfl) ⟨1345092, by rfl⟩ : syracuseStep 3586913 = 2690185) B2690185
theorem B13623065 : Blo 1415527 13623065 := bstep (se 2 (by rfl) ⟨5108649, by rfl⟩ : syracuseStep 13623065 = 10217299) B10217299
theorem B3107999 : Blo 1415527 3107999 := bstep (se 1 (by rfl) ⟨2330999, by rfl⟩ : syracuseStep 3107999 = 4661999) B4661999
theorem B1592959 : Blo 1415527 1592959 := bstep (se 1 (by rfl) ⟨1194719, by rfl⟩ : syracuseStep 1592959 = 2389439) B2389439
theorem B5746727 : Blo 1415527 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B9082043 : Blo 1415527 9082043 := bstep (se 1 (by rfl) ⟨6811532, by rfl⟩ : syracuseStep 9082043 = 13623065) B13623065
theorem B4782239 : Blo 1415527 4782239 := bstep (se 1 (by rfl) ⟨3586679, by rfl⟩ : syracuseStep 4782239 = 7173359) B7173359
theorem B2391275 : Blo 1415527 2391275 := bstep (se 1 (by rfl) ⟨1793456, by rfl⟩ : syracuseStep 2391275 = 3586913) B3586913
theorem B1416639 : Blo 1415527 1416639 := bstep (se 1 (by rfl) ⟨1062479, by rfl⟩ : syracuseStep 1416639 = 2124959) B2124959
theorem B5381599 : Blo 1415527 5381599 := bstep (se 1 (by rfl) ⟨4036199, by rfl⟩ : syracuseStep 5381599 = 8072399) B8072399
theorem B27238355 : Blo 1415527 27238355 := bstep (se 1 (by rfl) ⟨20428766, by rfl⟩ : syracuseStep 27238355 = 40857533) B40857533
theorem B88457197 : Blo 1415527 88457197 := bstep (se 3 (by rfl) ⟨16585724, by rfl⟩ : syracuseStep 88457197 = 33171449) B33171449
theorem B6054695 : Blo 1415527 6054695 := bstep (se 1 (by rfl) ⟨4541021, by rfl⟩ : syracuseStep 6054695 = 9082043) B9082043
theorem B3188159 : Blo 1415527 3188159 := bstep (se 1 (by rfl) ⟨2391119, by rfl⟩ : syracuseStep 3188159 = 4782239) B4782239
theorem B2123945 : Blo 1415527 2123945 := bstep (se 2 (by rfl) ⟨796479, by rfl⟩ : syracuseStep 2123945 = 1592959) B1592959
theorem B117942929 : Blo 1415527 117942929 := bstep (se 2 (by rfl) ⟨44228598, by rfl⟩ : syracuseStep 117942929 = 88457197) B88457197
theorem B1594183 : Blo 1415527 1594183 := bstep (se 1 (by rfl) ⟨1195637, by rfl⟩ : syracuseStep 1594183 = 2391275) B2391275
theorem B18158903 : Blo 1415527 18158903 := bstep (se 1 (by rfl) ⟨13619177, by rfl⟩ : syracuseStep 18158903 = 27238355) B27238355
theorem B3831151 : Blo 1415527 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B7175465 : Blo 1415527 7175465 := bstep (se 2 (by rfl) ⟨2690799, by rfl⟩ : syracuseStep 7175465 = 5381599) B5381599
theorem B2071999 : Blo 1415527 2071999 := bstep (se 1 (by rfl) ⟨1553999, by rfl⟩ : syracuseStep 2071999 = 3107999) B3107999
theorem B78628619 : Blo 1415527 78628619 := bstep (se 1 (by rfl) ⟨58971464, by rfl⟩ : syracuseStep 78628619 = 117942929) B117942929
theorem B2125439 : Blo 1415527 2125439 := bstep (se 1 (by rfl) ⟨1594079, by rfl⟩ : syracuseStep 2125439 = 3188159) B3188159
theorem B2125577 : Blo 1415527 2125577 := bstep (se 2 (by rfl) ⟨797091, by rfl⟩ : syracuseStep 2125577 = 1594183) B1594183
theorem B5108201 : Blo 1415527 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B4036463 : Blo 1415527 4036463 := bstep (se 1 (by rfl) ⟨3027347, by rfl⟩ : syracuseStep 4036463 = 6054695) B6054695
theorem B12105935 : Blo 1415527 12105935 := bstep (se 1 (by rfl) ⟨9079451, by rfl⟩ : syracuseStep 12105935 = 18158903) B18158903
theorem B1415963 : Blo 1415527 1415963 := bstep (se 1 (by rfl) ⟨1061972, by rfl⟩ : syracuseStep 1415963 = 2123945) B2123945
theorem B4783643 : Blo 1415527 4783643 := bstep (se 1 (by rfl) ⟨3587732, by rfl⟩ : syracuseStep 4783643 = 7175465) B7175465
theorem B11050661 : Blo 1415527 11050661 := bstep (se 4 (by rfl) ⟨1035999, by rfl⟩ : syracuseStep 11050661 = 2071999) B2071999
theorem B8070623 : Blo 1415527 8070623 := bstep (se 1 (by rfl) ⟨6052967, by rfl⟩ : syracuseStep 8070623 = 12105935) B12105935
theorem B3189095 : Blo 1415527 3189095 := bstep (se 1 (by rfl) ⟨2391821, by rfl⟩ : syracuseStep 3189095 = 4783643) B4783643
theorem B7367107 : Blo 1415527 7367107 := bstep (se 1 (by rfl) ⟨5525330, by rfl⟩ : syracuseStep 7367107 = 11050661) B11050661
theorem B2690975 : Blo 1415527 2690975 := bstep (se 1 (by rfl) ⟨2018231, by rfl⟩ : syracuseStep 2690975 = 4036463) B4036463
theorem B3405467 : Blo 1415527 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B52419079 : Blo 1415527 52419079 := bstep (se 1 (by rfl) ⟨39314309, by rfl⟩ : syracuseStep 52419079 = 78628619) B78628619
theorem B1416959 : Blo 1415527 1416959 := bstep (se 1 (by rfl) ⟨1062719, by rfl⟩ : syracuseStep 1416959 = 2125439) B2125439
theorem B1417051 : Blo 1415527 1417051 := bstep (se 1 (by rfl) ⟨1062788, by rfl⟩ : syracuseStep 1417051 = 2125577) B2125577
theorem B9822809 : Blo 1415527 9822809 := bstep (se 2 (by rfl) ⟨3683553, by rfl⟩ : syracuseStep 9822809 = 7367107) B7367107
theorem B2270311 : Blo 1415527 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B2126063 : Blo 1415527 2126063 := bstep (se 1 (by rfl) ⟨1594547, by rfl⟩ : syracuseStep 2126063 = 3189095) B3189095
theorem B69892105 : Blo 1415527 69892105 := bstep (se 2 (by rfl) ⟨26209539, by rfl⟩ : syracuseStep 69892105 = 52419079) B52419079
theorem B5380415 : Blo 1415527 5380415 := bstep (se 1 (by rfl) ⟨4035311, by rfl⟩ : syracuseStep 5380415 = 8070623) B8070623
theorem B1793983 : Blo 1415527 1793983 := bstep (se 1 (by rfl) ⟨1345487, by rfl⟩ : syracuseStep 1793983 = 2690975) B2690975
theorem B1417375 : Blo 1415527 1417375 := bstep (se 1 (by rfl) ⟨1063031, by rfl⟩ : syracuseStep 1417375 = 2126063) B2126063
theorem B12108325 : Blo 1415527 12108325 := bstep (se 4 (by rfl) ⟨1135155, by rfl⟩ : syracuseStep 12108325 = 2270311) B2270311
theorem B6548539 : Blo 1415527 6548539 := bstep (se 1 (by rfl) ⟨4911404, by rfl⟩ : syracuseStep 6548539 = 9822809) B9822809
theorem B93189473 : Blo 1415527 93189473 := bstep (se 2 (by rfl) ⟨34946052, by rfl⟩ : syracuseStep 93189473 = 69892105) B69892105
theorem B3586943 : Blo 1415527 3586943 := bstep (se 1 (by rfl) ⟨2690207, by rfl⟩ : syracuseStep 3586943 = 5380415) B5380415
theorem B2391977 : Blo 1415527 2391977 := bstep (se 2 (by rfl) ⟨896991, by rfl⟩ : syracuseStep 2391977 = 1793983) B1793983
theorem B1594651 : Blo 1415527 1594651 := bstep (se 1 (by rfl) ⟨1195988, by rfl⟩ : syracuseStep 1594651 = 2391977) B2391977
theorem B16144433 : Blo 1415527 16144433 := bstep (se 2 (by rfl) ⟨6054162, by rfl⟩ : syracuseStep 16144433 = 12108325) B12108325
theorem B62126315 : Blo 1415527 62126315 := bstep (se 1 (by rfl) ⟨46594736, by rfl⟩ : syracuseStep 62126315 = 93189473) B93189473
theorem B8731385 : Blo 1415527 8731385 := bstep (se 2 (by rfl) ⟨3274269, by rfl⟩ : syracuseStep 8731385 = 6548539) B6548539
theorem B2391295 : Blo 1415527 2391295 := bstep (se 1 (by rfl) ⟨1793471, by rfl⟩ : syracuseStep 2391295 = 3586943) B3586943
theorem B3188393 : Blo 1415527 3188393 := bstep (se 2 (by rfl) ⟨1195647, by rfl⟩ : syracuseStep 3188393 = 2391295) B2391295
theorem B2126201 : Blo 1415527 2126201 := bstep (se 2 (by rfl) ⟨797325, by rfl⟩ : syracuseStep 2126201 = 1594651) B1594651
theorem B5820923 : Blo 1415527 5820923 := bstep (se 1 (by rfl) ⟨4365692, by rfl⟩ : syracuseStep 5820923 = 8731385) B8731385
theorem B10762955 : Blo 1415527 10762955 := bstep (se 1 (by rfl) ⟨8072216, by rfl⟩ : syracuseStep 10762955 = 16144433) B16144433
theorem B41417543 : Blo 1415527 41417543 := bstep (se 1 (by rfl) ⟨31063157, by rfl⟩ : syracuseStep 41417543 = 62126315) B62126315
theorem B1417467 : Blo 1415527 1417467 := bstep (se 1 (by rfl) ⟨1063100, by rfl⟩ : syracuseStep 1417467 = 2126201) B2126201
theorem B2125595 : Blo 1415527 2125595 := bstep (se 1 (by rfl) ⟨1594196, by rfl⟩ : syracuseStep 2125595 = 3188393) B3188393
theorem B27611695 : Blo 1415527 27611695 := bstep (se 1 (by rfl) ⟨20708771, by rfl⟩ : syracuseStep 27611695 = 41417543) B41417543
theorem B15522461 : Blo 1415527 15522461 := bstep (se 3 (by rfl) ⟨2910461, by rfl⟩ : syracuseStep 15522461 = 5820923) B5820923
theorem B7175303 : Blo 1415527 7175303 := bstep (se 1 (by rfl) ⟨5381477, by rfl⟩ : syracuseStep 7175303 = 10762955) B10762955
theorem B36815593 : Blo 1415527 36815593 := bstep (se 2 (by rfl) ⟨13805847, by rfl⟩ : syracuseStep 36815593 = 27611695) B27611695
theorem B10348307 : Blo 1415527 10348307 := bstep (se 1 (by rfl) ⟨7761230, by rfl⟩ : syracuseStep 10348307 = 15522461) B15522461
theorem B4783535 : Blo 1415527 4783535 := bstep (se 1 (by rfl) ⟨3587651, by rfl⟩ : syracuseStep 4783535 = 7175303) B7175303
theorem B1417063 : Blo 1415527 1417063 := bstep (se 1 (by rfl) ⟨1062797, by rfl⟩ : syracuseStep 1417063 = 2125595) B2125595
theorem B49087457 : Blo 1415527 49087457 := bstep (se 2 (by rfl) ⟨18407796, by rfl⟩ : syracuseStep 49087457 = 36815593) B36815593
theorem B6898871 : Blo 1415527 6898871 := bstep (se 1 (by rfl) ⟨5174153, by rfl⟩ : syracuseStep 6898871 = 10348307) B10348307
theorem B3189023 : Blo 1415527 3189023 := bstep (se 1 (by rfl) ⟨2391767, by rfl⟩ : syracuseStep 3189023 = 4783535) B4783535
theorem B2126015 : Blo 1415527 2126015 := bstep (se 1 (by rfl) ⟨1594511, by rfl⟩ : syracuseStep 2126015 = 3189023) B3189023
theorem B18396989 : Blo 1415527 18396989 := bstep (se 3 (by rfl) ⟨3449435, by rfl⟩ : syracuseStep 18396989 = 6898871) B6898871
theorem B32724971 : Blo 1415527 32724971 := bstep (se 1 (by rfl) ⟨24543728, by rfl⟩ : syracuseStep 32724971 = 49087457) B49087457
theorem B1417343 : Blo 1415527 1417343 := bstep (se 1 (by rfl) ⟨1063007, by rfl⟩ : syracuseStep 1417343 = 2126015) B2126015
theorem B12264659 : Blo 1415527 12264659 := bstep (se 1 (by rfl) ⟨9198494, by rfl⟩ : syracuseStep 12264659 = 18396989) B18396989
theorem B21816647 : Blo 1415527 21816647 := bstep (se 1 (by rfl) ⟨16362485, by rfl⟩ : syracuseStep 21816647 = 32724971) B32724971
theorem B8176439 : Blo 1415527 8176439 := bstep (se 1 (by rfl) ⟨6132329, by rfl⟩ : syracuseStep 8176439 = 12264659) B12264659
theorem B14544431 : Blo 1415527 14544431 := bstep (se 1 (by rfl) ⟨10908323, by rfl⟩ : syracuseStep 14544431 = 21816647) B21816647
theorem B5450959 : Blo 1415527 5450959 := bstep (se 1 (by rfl) ⟨4088219, by rfl⟩ : syracuseStep 5450959 = 8176439) B8176439
theorem B9696287 : Blo 1415527 9696287 := bstep (se 1 (by rfl) ⟨7272215, by rfl⟩ : syracuseStep 9696287 = 14544431) B14544431
theorem B25856765 : Blo 1415527 25856765 := bstep (se 3 (by rfl) ⟨4848143, by rfl⟩ : syracuseStep 25856765 = 9696287) B9696287
theorem B29071781 : Blo 1415527 29071781 := bstep (se 4 (by rfl) ⟨2725479, by rfl⟩ : syracuseStep 29071781 = 5450959) B5450959
theorem B17237843 : Blo 1415527 17237843 := bstep (se 1 (by rfl) ⟨12928382, by rfl⟩ : syracuseStep 17237843 = 25856765) B25856765
theorem B19381187 : Blo 1415527 19381187 := bstep (se 1 (by rfl) ⟨14535890, by rfl⟩ : syracuseStep 19381187 = 29071781) B29071781
theorem B12920791 : Blo 1415527 12920791 := bstep (se 1 (by rfl) ⟨9690593, by rfl⟩ : syracuseStep 12920791 = 19381187) B19381187
theorem B11491895 : Blo 1415527 11491895 := bstep (se 1 (by rfl) ⟨8618921, by rfl⟩ : syracuseStep 11491895 = 17237843) B17237843
theorem B7661263 : Blo 1415527 7661263 := bstep (se 1 (by rfl) ⟨5745947, by rfl⟩ : syracuseStep 7661263 = 11491895) B11491895
theorem B17227721 : Blo 1415527 17227721 := bstep (se 2 (by rfl) ⟨6460395, by rfl⟩ : syracuseStep 17227721 = 12920791) B12920791
theorem B10215017 : Blo 1415527 10215017 := bstep (se 2 (by rfl) ⟨3830631, by rfl⟩ : syracuseStep 10215017 = 7661263) B7661263
theorem B11485147 : Blo 1415527 11485147 := bstep (se 1 (by rfl) ⟨8613860, by rfl⟩ : syracuseStep 11485147 = 17227721) B17227721
theorem B6810011 : Blo 1415527 6810011 := bstep (se 1 (by rfl) ⟨5107508, by rfl⟩ : syracuseStep 6810011 = 10215017) B10215017
theorem B15313529 : Blo 1415527 15313529 := bstep (se 2 (by rfl) ⟨5742573, by rfl⟩ : syracuseStep 15313529 = 11485147) B11485147
theorem B4540007 : Blo 1415527 4540007 := bstep (se 1 (by rfl) ⟨3405005, by rfl⟩ : syracuseStep 4540007 = 6810011) B6810011
theorem B10209019 : Blo 1415527 10209019 := bstep (se 1 (by rfl) ⟨7656764, by rfl⟩ : syracuseStep 10209019 = 15313529) B15313529
theorem B13612025 : Blo 1415527 13612025 := bstep (se 2 (by rfl) ⟨5104509, by rfl⟩ : syracuseStep 13612025 = 10209019) B10209019
theorem B12106685 : Blo 1415527 12106685 := bstep (se 3 (by rfl) ⟨2270003, by rfl⟩ : syracuseStep 12106685 = 4540007) B4540007
theorem B8071123 : Blo 1415527 8071123 := bstep (se 1 (by rfl) ⟨6053342, by rfl⟩ : syracuseStep 8071123 = 12106685) B12106685
theorem B9074683 : Blo 1415527 9074683 := bstep (se 1 (by rfl) ⟨6806012, by rfl⟩ : syracuseStep 9074683 = 13612025) B13612025
theorem B10761497 : Blo 1415527 10761497 := bstep (se 2 (by rfl) ⟨4035561, by rfl⟩ : syracuseStep 10761497 = 8071123) B8071123
theorem B12099577 : Blo 1415527 12099577 := bstep (se 2 (by rfl) ⟨4537341, by rfl⟩ : syracuseStep 12099577 = 9074683) B9074683
theorem B16132769 : Blo 1415527 16132769 := bstep (se 2 (by rfl) ⟨6049788, by rfl⟩ : syracuseStep 16132769 = 12099577) B12099577
theorem B7174331 : Blo 1415527 7174331 := bstep (se 1 (by rfl) ⟨5380748, by rfl⟩ : syracuseStep 7174331 = 10761497) B10761497
theorem B4782887 : Blo 1415527 4782887 := bstep (se 1 (by rfl) ⟨3587165, by rfl⟩ : syracuseStep 4782887 = 7174331) B7174331
theorem B10755179 : Blo 1415527 10755179 := bstep (se 1 (by rfl) ⟨8066384, by rfl⟩ : syracuseStep 10755179 = 16132769) B16132769
theorem B3188591 : Blo 1415527 3188591 := bstep (se 1 (by rfl) ⟨2391443, by rfl⟩ : syracuseStep 3188591 = 4782887) B4782887
theorem B7170119 : Blo 1415527 7170119 := bstep (se 1 (by rfl) ⟨5377589, by rfl⟩ : syracuseStep 7170119 = 10755179) B10755179
theorem B2125727 : Blo 1415527 2125727 := bstep (se 1 (by rfl) ⟨1594295, by rfl⟩ : syracuseStep 2125727 = 3188591) B3188591
theorem B4780079 : Blo 1415527 4780079 := bstep (se 1 (by rfl) ⟨3585059, by rfl⟩ : syracuseStep 4780079 = 7170119) B7170119
theorem B3186719 : Blo 1415527 3186719 := bstep (se 1 (by rfl) ⟨2390039, by rfl⟩ : syracuseStep 3186719 = 4780079) B4780079
theorem B1417151 : Blo 1415527 1417151 := bstep (se 1 (by rfl) ⟨1062863, by rfl⟩ : syracuseStep 1417151 = 2125727) B2125727
theorem B2124479 : Blo 1415527 2124479 := bstep (se 1 (by rfl) ⟨1593359, by rfl⟩ : syracuseStep 2124479 = 3186719) B3186719
theorem B1416319 : Blo 1415527 1416319 := bstep (se 1 (by rfl) ⟨1062239, by rfl⟩ : syracuseStep 1416319 = 2124479) B2124479

theorem C0 (j : ℕ) (h1 : 353881 ≤ j) (h2 : j ≤ 354381) : Blo 1415527 (4 * j + 3) := by
  interval_cases j
  · exact B1415527
  · exact B1415531
  · exact B1415535
  · exact B1415539
  · exact B1415543
  · exact B1415547
  · exact B1415551
  · exact B1415555
  · exact B1415559
  · exact B1415563
  · exact B1415567
  · exact B1415571
  · exact B1415575
  · exact B1415579
  · exact B1415583
  · exact B1415587
  · exact B1415591
  · exact B1415595
  · exact B1415599
  · exact B1415603
  · exact B1415607
  · exact B1415611
  · exact B1415615
  · exact B1415619
  · exact B1415623
  · exact B1415627
  · exact B1415631
  · exact B1415635
  · exact B1415639
  · exact B1415643
  · exact B1415647
  · exact B1415651
  · exact B1415655
  · exact B1415659
  · exact B1415663
  · exact B1415667
  · exact B1415671
  · exact B1415675
  · exact B1415679
  · exact B1415683
  · exact B1415687
  · exact B1415691
  · exact B1415695
  · exact B1415699
  · exact B1415703
  · exact B1415707
  · exact B1415711
  · exact B1415715
  · exact B1415719
  · exact B1415723
  · exact B1415727
  · exact B1415731
  · exact B1415735
  · exact B1415739
  · exact B1415743
  · exact B1415747
  · exact B1415751
  · exact B1415755
  · exact B1415759
  · exact B1415763
  · exact B1415767
  · exact B1415771
  · exact B1415775
  · exact B1415779
  · exact B1415783
  · exact B1415787
  · exact B1415791
  · exact B1415795
  · exact B1415799
  · exact B1415803
  · exact B1415807
  · exact B1415811
  · exact B1415815
  · exact B1415819
  · exact B1415823
  · exact B1415827
  · exact B1415831
  · exact B1415835
  · exact B1415839
  · exact B1415843
  · exact B1415847
  · exact B1415851
  · exact B1415855
  · exact B1415859
  · exact B1415863
  · exact B1415867
  · exact B1415871
  · exact B1415875
  · exact B1415879
  · exact B1415883
  · exact B1415887
  · exact B1415891
  · exact B1415895
  · exact B1415899
  · exact B1415903
  · exact B1415907
  · exact B1415911
  · exact B1415915
  · exact B1415919
  · exact B1415923
  · exact B1415927
  · exact B1415931
  · exact B1415935
  · exact B1415939
  · exact B1415943
  · exact B1415947
  · exact B1415951
  · exact B1415955
  · exact B1415959
  · exact B1415963
  · exact B1415967
  · exact B1415971
  · exact B1415975
  · exact B1415979
  · exact B1415983
  · exact B1415987
  · exact B1415991
  · exact B1415995
  · exact B1415999
  · exact B1416003
  · exact B1416007
  · exact B1416011
  · exact B1416015
  · exact B1416019
  · exact B1416023
  · exact B1416027
  · exact B1416031
  · exact B1416035
  · exact B1416039
  · exact B1416043
  · exact B1416047
  · exact B1416051
  · exact B1416055
  · exact B1416059
  · exact B1416063
  · exact B1416067
  · exact B1416071
  · exact B1416075
  · exact B1416079
  · exact B1416083
  · exact B1416087
  · exact B1416091
  · exact B1416095
  · exact B1416099
  · exact B1416103
  · exact B1416107
  · exact B1416111
  · exact B1416115
  · exact B1416119
  · exact B1416123
  · exact B1416127
  · exact B1416131
  · exact B1416135
  · exact B1416139
  · exact B1416143
  · exact B1416147
  · exact B1416151
  · exact B1416155
  · exact B1416159
  · exact B1416163
  · exact B1416167
  · exact B1416171
  · exact B1416175
  · exact B1416179
  · exact B1416183
  · exact B1416187
  · exact B1416191
  · exact B1416195
  · exact B1416199
  · exact B1416203
  · exact B1416207
  · exact B1416211
  · exact B1416215
  · exact B1416219
  · exact B1416223
  · exact B1416227
  · exact B1416231
  · exact B1416235
  · exact B1416239
  · exact B1416243
  · exact B1416247
  · exact B1416251
  · exact B1416255
  · exact B1416259
  · exact B1416263
  · exact B1416267
  · exact B1416271
  · exact B1416275
  · exact B1416279
  · exact B1416283
  · exact B1416287
  · exact B1416291
  · exact B1416295
  · exact B1416299
  · exact B1416303
  · exact B1416307
  · exact B1416311
  · exact B1416315
  · exact B1416319
  · exact B1416323
  · exact B1416327
  · exact B1416331
  · exact B1416335
  · exact B1416339
  · exact B1416343
  · exact B1416347
  · exact B1416351
  · exact B1416355
  · exact B1416359
  · exact B1416363
  · exact B1416367
  · exact B1416371
  · exact B1416375
  · exact B1416379
  · exact B1416383
  · exact B1416387
  · exact B1416391
  · exact B1416395
  · exact B1416399
  · exact B1416403
  · exact B1416407
  · exact B1416411
  · exact B1416415
  · exact B1416419
  · exact B1416423
  · exact B1416427
  · exact B1416431
  · exact B1416435
  · exact B1416439
  · exact B1416443
  · exact B1416447
  · exact B1416451
  · exact B1416455
  · exact B1416459
  · exact B1416463
  · exact B1416467
  · exact B1416471
  · exact B1416475
  · exact B1416479
  · exact B1416483
  · exact B1416487
  · exact B1416491
  · exact B1416495
  · exact B1416499
  · exact B1416503
  · exact B1416507
  · exact B1416511
  · exact B1416515
  · exact B1416519
  · exact B1416523
  · exact B1416527
  · exact B1416531
  · exact B1416535
  · exact B1416539
  · exact B1416543
  · exact B1416547
  · exact B1416551
  · exact B1416555
  · exact B1416559
  · exact B1416563
  · exact B1416567
  · exact B1416571
  · exact B1416575
  · exact B1416579
  · exact B1416583
  · exact B1416587
  · exact B1416591
  · exact B1416595
  · exact B1416599
  · exact B1416603
  · exact B1416607
  · exact B1416611
  · exact B1416615
  · exact B1416619
  · exact B1416623
  · exact B1416627
  · exact B1416631
  · exact B1416635
  · exact B1416639
  · exact B1416643
  · exact B1416647
  · exact B1416651
  · exact B1416655
  · exact B1416659
  · exact B1416663
  · exact B1416667
  · exact B1416671
  · exact B1416675
  · exact B1416679
  · exact B1416683
  · exact B1416687
  · exact B1416691
  · exact B1416695
  · exact B1416699
  · exact B1416703
  · exact B1416707
  · exact B1416711
  · exact B1416715
  · exact B1416719
  · exact B1416723
  · exact B1416727
  · exact B1416731
  · exact B1416735
  · exact B1416739
  · exact B1416743
  · exact B1416747
  · exact B1416751
  · exact B1416755
  · exact B1416759
  · exact B1416763
  · exact B1416767
  · exact B1416771
  · exact B1416775
  · exact B1416779
  · exact B1416783
  · exact B1416787
  · exact B1416791
  · exact B1416795
  · exact B1416799
  · exact B1416803
  · exact B1416807
  · exact B1416811
  · exact B1416815
  · exact B1416819
  · exact B1416823
  · exact B1416827
  · exact B1416831
  · exact B1416835
  · exact B1416839
  · exact B1416843
  · exact B1416847
  · exact B1416851
  · exact B1416855
  · exact B1416859
  · exact B1416863
  · exact B1416867
  · exact B1416871
  · exact B1416875
  · exact B1416879
  · exact B1416883
  · exact B1416887
  · exact B1416891
  · exact B1416895
  · exact B1416899
  · exact B1416903
  · exact B1416907
  · exact B1416911
  · exact B1416915
  · exact B1416919
  · exact B1416923
  · exact B1416927
  · exact B1416931
  · exact B1416935
  · exact B1416939
  · exact B1416943
  · exact B1416947
  · exact B1416951
  · exact B1416955
  · exact B1416959
  · exact B1416963
  · exact B1416967
  · exact B1416971
  · exact B1416975
  · exact B1416979
  · exact B1416983
  · exact B1416987
  · exact B1416991
  · exact B1416995
  · exact B1416999
  · exact B1417003
  · exact B1417007
  · exact B1417011
  · exact B1417015
  · exact B1417019
  · exact B1417023
  · exact B1417027
  · exact B1417031
  · exact B1417035
  · exact B1417039
  · exact B1417043
  · exact B1417047
  · exact B1417051
  · exact B1417055
  · exact B1417059
  · exact B1417063
  · exact B1417067
  · exact B1417071
  · exact B1417075
  · exact B1417079
  · exact B1417083
  · exact B1417087
  · exact B1417091
  · exact B1417095
  · exact B1417099
  · exact B1417103
  · exact B1417107
  · exact B1417111
  · exact B1417115
  · exact B1417119
  · exact B1417123
  · exact B1417127
  · exact B1417131
  · exact B1417135
  · exact B1417139
  · exact B1417143
  · exact B1417147
  · exact B1417151
  · exact B1417155
  · exact B1417159
  · exact B1417163
  · exact B1417167
  · exact B1417171
  · exact B1417175
  · exact B1417179
  · exact B1417183
  · exact B1417187
  · exact B1417191
  · exact B1417195
  · exact B1417199
  · exact B1417203
  · exact B1417207
  · exact B1417211
  · exact B1417215
  · exact B1417219
  · exact B1417223
  · exact B1417227
  · exact B1417231
  · exact B1417235
  · exact B1417239
  · exact B1417243
  · exact B1417247
  · exact B1417251
  · exact B1417255
  · exact B1417259
  · exact B1417263
  · exact B1417267
  · exact B1417271
  · exact B1417275
  · exact B1417279
  · exact B1417283
  · exact B1417287
  · exact B1417291
  · exact B1417295
  · exact B1417299
  · exact B1417303
  · exact B1417307
  · exact B1417311
  · exact B1417315
  · exact B1417319
  · exact B1417323
  · exact B1417327
  · exact B1417331
  · exact B1417335
  · exact B1417339
  · exact B1417343
  · exact B1417347
  · exact B1417351
  · exact B1417355
  · exact B1417359
  · exact B1417363
  · exact B1417367
  · exact B1417371
  · exact B1417375
  · exact B1417379
  · exact B1417383
  · exact B1417387
  · exact B1417391
  · exact B1417395
  · exact B1417399
  · exact B1417403
  · exact B1417407
  · exact B1417411
  · exact B1417415
  · exact B1417419
  · exact B1417423
  · exact B1417427
  · exact B1417431
  · exact B1417435
  · exact B1417439
  · exact B1417443
  · exact B1417447
  · exact B1417451
  · exact B1417455
  · exact B1417459
  · exact B1417463
  · exact B1417467
  · exact B1417471
  · exact B1417475
  · exact B1417479
  · exact B1417483
  · exact B1417487
  · exact B1417491
  · exact B1417495
  · exact B1417499
  · exact B1417503
  · exact B1417507
  · exact B1417511
  · exact B1417515
  · exact B1417519
  · exact B1417523
  · exact B1417527

theorem solution (m : ℕ) (hlo : 1415527 ≤ m) (hhi : m ≤ 1417527) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 353881 ≤ j := by omega
    have hj2 : j ≤ 354381 := by omega
    have hb : Blo 1415527 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
