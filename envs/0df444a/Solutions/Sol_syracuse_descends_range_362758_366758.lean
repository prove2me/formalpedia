-- Prove2me | solution 1 for syracuse_descends_range_362758_366758
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:39.260549+00:00
-- url     : https://prove2.me/submissions/484601b5-f99a-432b-a871-eef9372619b9

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


theorem B819269 : Blo 362758 819269 := bbase (se 4 (by rfl) ⟨76806, by rfl⟩ : syracuseStep 819269 = 153613) (by norm_num)
theorem B819341 : Blo 362758 819341 := bbase (se 3 (by rfl) ⟨153626, by rfl⟩ : syracuseStep 819341 = 307253) (by norm_num)
theorem B819413 : Blo 362758 819413 := bbase (se 7 (by rfl) ⟨9602, by rfl⟩ : syracuseStep 819413 = 19205) (by norm_num)
theorem B819485 : Blo 362758 819485 := bbase (se 3 (by rfl) ⟨153653, by rfl⟩ : syracuseStep 819485 = 307307) (by norm_num)
theorem B1311061 : Blo 362758 1311061 := bbase (se 10 (by rfl) ⟨1920, by rfl⟩ : syracuseStep 1311061 = 3841) (by norm_num)
theorem B491869 : Blo 362758 491869 := bbase (se 3 (by rfl) ⟨92225, by rfl⟩ : syracuseStep 491869 = 184451) (by norm_num)
theorem B819557 : Blo 362758 819557 := bbase (se 4 (by rfl) ⟨76833, by rfl⟩ : syracuseStep 819557 = 153667) (by norm_num)
theorem B819629 : Blo 362758 819629 := bbase (se 3 (by rfl) ⟨153680, by rfl⟩ : syracuseStep 819629 = 307361) (by norm_num)
theorem B459209 : Blo 362758 459209 := bbase (se 2 (by rfl) ⟨172203, by rfl⟩ : syracuseStep 459209 = 344407) (by norm_num)
theorem B819701 : Blo 362758 819701 := bbase (se 5 (by rfl) ⟨38423, by rfl⟩ : syracuseStep 819701 = 76847) (by norm_num)
theorem B459265 : Blo 362758 459265 := bbase (se 2 (by rfl) ⟨172224, by rfl⟩ : syracuseStep 459265 = 344449) (by norm_num)
theorem B819773 : Blo 362758 819773 := bbase (se 3 (by rfl) ⟨153707, by rfl⟩ : syracuseStep 819773 = 307415) (by norm_num)
theorem B459361 : Blo 362758 459361 := bbase (se 2 (by rfl) ⟨172260, by rfl⟩ : syracuseStep 459361 = 344521) (by norm_num)
theorem B819845 : Blo 362758 819845 := bbase (se 4 (by rfl) ⟨76860, by rfl⟩ : syracuseStep 819845 = 153721) (by norm_num)
theorem B688837 : Blo 362758 688837 := bbase (se 4 (by rfl) ⟨64578, by rfl⟩ : syracuseStep 688837 = 129157) (by norm_num)
theorem B819917 : Blo 362758 819917 := bbase (se 3 (by rfl) ⟨153734, by rfl⟩ : syracuseStep 819917 = 307469) (by norm_num)
theorem B459533 : Blo 362758 459533 := bbase (se 3 (by rfl) ⟨86162, by rfl⟩ : syracuseStep 459533 = 172325) (by norm_num)
theorem B819989 : Blo 362758 819989 := bbase (se 6 (by rfl) ⟨19218, by rfl⟩ : syracuseStep 819989 = 38437) (by norm_num)
theorem B918317 : Blo 362758 918317 := bbase (se 3 (by rfl) ⟨172184, by rfl⟩ : syracuseStep 918317 = 344369) (by norm_num)
theorem B459589 : Blo 362758 459589 := bbase (se 4 (by rfl) ⟨43086, by rfl⟩ : syracuseStep 459589 = 86173) (by norm_num)
theorem B688981 : Blo 362758 688981 := bbase (se 9 (by rfl) ⟨2018, by rfl⟩ : syracuseStep 688981 = 4037) (by norm_num)
theorem B820061 : Blo 362758 820061 := bbase (se 3 (by rfl) ⟨153761, by rfl⟩ : syracuseStep 820061 = 307523) (by norm_num)
theorem B2327413 : Blo 362758 2327413 := bbase (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) (by norm_num)
theorem B459685 : Blo 362758 459685 := bbase (se 4 (by rfl) ⟨43095, by rfl⟩ : syracuseStep 459685 = 86191) (by norm_num)
theorem B820133 : Blo 362758 820133 := bbase (se 4 (by rfl) ⟨76887, by rfl⟩ : syracuseStep 820133 = 153775) (by norm_num)
theorem B820205 : Blo 362758 820205 := bbase (se 3 (by rfl) ⟨153788, by rfl⟩ : syracuseStep 820205 = 307577) (by norm_num)
theorem B689141 : Blo 362758 689141 := bbase (se 5 (by rfl) ⟨32303, by rfl⟩ : syracuseStep 689141 = 64607) (by norm_num)
theorem B820277 : Blo 362758 820277 := bbase (se 5 (by rfl) ⟨38450, by rfl⟩ : syracuseStep 820277 = 76901) (by norm_num)
theorem B459857 : Blo 362758 459857 := bbase (se 2 (by rfl) ⟨172446, by rfl⟩ : syracuseStep 459857 = 344893) (by norm_num)
theorem B820349 : Blo 362758 820349 := bbase (se 3 (by rfl) ⟨153815, by rfl⟩ : syracuseStep 820349 = 307631) (by norm_num)
theorem B918661 : Blo 362758 918661 := bbase (se 4 (by rfl) ⟨86124, by rfl⟩ : syracuseStep 918661 = 172249) (by norm_num)
theorem B689285 : Blo 362758 689285 := bbase (se 4 (by rfl) ⟨64620, by rfl⟩ : syracuseStep 689285 = 129241) (by norm_num)
theorem B459913 : Blo 362758 459913 := bbase (se 2 (by rfl) ⟨172467, by rfl⟩ : syracuseStep 459913 = 344935) (by norm_num)
theorem B525461 : Blo 362758 525461 := bbase (se 6 (by rfl) ⟨12315, by rfl⟩ : syracuseStep 525461 = 24631) (by norm_num)
theorem B1377445 : Blo 362758 1377445 := bbase (se 4 (by rfl) ⟨129135, by rfl⟩ : syracuseStep 1377445 = 258271) (by norm_num)
theorem B394433 : Blo 362758 394433 := bbase (se 2 (by rfl) ⟨147912, by rfl⟩ : syracuseStep 394433 = 295825) (by norm_num)
theorem B820421 : Blo 362758 820421 := bbase (se 4 (by rfl) ⟨76914, by rfl⟩ : syracuseStep 820421 = 153829) (by norm_num)
theorem B460009 : Blo 362758 460009 := bbase (se 2 (by rfl) ⟨172503, by rfl⟩ : syracuseStep 460009 = 345007) (by norm_num)
theorem B918773 : Blo 362758 918773 := bbase (se 5 (by rfl) ⟨43067, by rfl⟩ : syracuseStep 918773 = 86135) (by norm_num)
theorem B1049861 : Blo 362758 1049861 := bbase (se 4 (by rfl) ⟨98424, by rfl⟩ : syracuseStep 1049861 = 196849) (by norm_num)
theorem B820493 : Blo 362758 820493 := bbase (se 3 (by rfl) ⟨153842, by rfl⟩ : syracuseStep 820493 = 307685) (by norm_num)
theorem B820565 : Blo 362758 820565 := bbase (se 12 (by rfl) ⟨300, by rfl⟩ : syracuseStep 820565 = 601) (by norm_num)
theorem B1246565 : Blo 362758 1246565 := bbase (se 4 (by rfl) ⟨116865, by rfl⟩ : syracuseStep 1246565 = 233731) (by norm_num)
theorem B460181 : Blo 362758 460181 := bbase (se 6 (by rfl) ⟨10785, by rfl⟩ : syracuseStep 460181 = 21571) (by norm_num)
theorem B820637 : Blo 362758 820637 := bbase (se 3 (by rfl) ⟨153869, by rfl⟩ : syracuseStep 820637 = 307739) (by norm_num)
theorem B689573 : Blo 362758 689573 := bbase (se 4 (by rfl) ⟨64647, by rfl⟩ : syracuseStep 689573 = 129295) (by norm_num)
theorem B918965 : Blo 362758 918965 := bbase (se 5 (by rfl) ⟨43076, by rfl⟩ : syracuseStep 918965 = 86153) (by norm_num)
theorem B460237 : Blo 362758 460237 := bbase (se 3 (by rfl) ⟨86294, by rfl⟩ : syracuseStep 460237 = 172589) (by norm_num)
theorem B1377749 : Blo 362758 1377749 := bbase (se 7 (by rfl) ⟨16145, by rfl⟩ : syracuseStep 1377749 = 32291) (by norm_num)
theorem B820709 : Blo 362758 820709 := bbase (se 4 (by rfl) ⟨76941, by rfl⟩ : syracuseStep 820709 = 153883) (by norm_num)
theorem B624109 : Blo 362758 624109 := bbase (se 3 (by rfl) ⟨117020, by rfl⟩ : syracuseStep 624109 = 234041) (by norm_num)
theorem B624125 : Blo 362758 624125 := bbase (se 3 (by rfl) ⟨117023, by rfl⟩ : syracuseStep 624125 = 234047) (by norm_num)
theorem B460333 : Blo 362758 460333 := bbase (se 3 (by rfl) ⟨86312, by rfl⟩ : syracuseStep 460333 = 172625) (by norm_num)
theorem B820781 : Blo 362758 820781 := bbase (se 3 (by rfl) ⟨153896, by rfl⟩ : syracuseStep 820781 = 307793) (by norm_num)
theorem B689725 : Blo 362758 689725 := bbase (se 3 (by rfl) ⟨129323, by rfl⟩ : syracuseStep 689725 = 258647) (by norm_num)
theorem B820853 : Blo 362758 820853 := bbase (se 5 (by rfl) ⟨38477, by rfl⟩ : syracuseStep 820853 = 76955) (by norm_num)
theorem B820925 : Blo 362758 820925 := bbase (se 3 (by rfl) ⟨153923, by rfl⟩ : syracuseStep 820925 = 307847) (by norm_num)
theorem B460505 : Blo 362758 460505 := bbase (se 2 (by rfl) ⟨172689, by rfl⟩ : syracuseStep 460505 = 345379) (by norm_num)
theorem B820997 : Blo 362758 820997 := bbase (se 4 (by rfl) ⟨76968, by rfl⟩ : syracuseStep 820997 = 153937) (by norm_num)
theorem B919309 : Blo 362758 919309 := bbase (se 3 (by rfl) ⟨172370, by rfl⟩ : syracuseStep 919309 = 344741) (by norm_num)
theorem B460561 : Blo 362758 460561 := bbase (se 2 (by rfl) ⟨172710, by rfl⟩ : syracuseStep 460561 = 345421) (by norm_num)
theorem B821069 : Blo 362758 821069 := bbase (se 3 (by rfl) ⟨153950, by rfl⟩ : syracuseStep 821069 = 307901) (by norm_num)
theorem B690029 : Blo 362758 690029 := bbase (se 3 (by rfl) ⟨129380, by rfl⟩ : syracuseStep 690029 = 258761) (by norm_num)
theorem B460657 : Blo 362758 460657 := bbase (se 2 (by rfl) ⟨172746, by rfl⟩ : syracuseStep 460657 = 345493) (by norm_num)
theorem B1836917 : Blo 362758 1836917 := bbase (se 5 (by rfl) ⟨86105, by rfl⟩ : syracuseStep 1836917 = 172211) (by norm_num)
theorem B919421 : Blo 362758 919421 := bbase (se 3 (by rfl) ⟨172391, by rfl⟩ : syracuseStep 919421 = 344783) (by norm_num)
theorem B821141 : Blo 362758 821141 := bbase (se 6 (by rfl) ⟨19245, by rfl⟩ : syracuseStep 821141 = 38491) (by norm_num)
theorem B657325 : Blo 362758 657325 := bbase (se 3 (by rfl) ⟨123248, by rfl⟩ : syracuseStep 657325 = 246497) (by norm_num)
theorem B821213 : Blo 362758 821213 := bbase (se 3 (by rfl) ⟨153977, by rfl⟩ : syracuseStep 821213 = 307955) (by norm_num)
theorem B460829 : Blo 362758 460829 := bbase (se 3 (by rfl) ⟨86405, by rfl⟩ : syracuseStep 460829 = 172811) (by norm_num)
theorem B821285 : Blo 362758 821285 := bbase (se 4 (by rfl) ⟨76995, by rfl⟩ : syracuseStep 821285 = 153991) (by norm_num)
theorem B919613 : Blo 362758 919613 := bbase (se 3 (by rfl) ⟨172427, by rfl⟩ : syracuseStep 919613 = 344855) (by norm_num)
theorem B460885 : Blo 362758 460885 := bbase (se 8 (by rfl) ⟨2700, by rfl⟩ : syracuseStep 460885 = 5401) (by norm_num)
theorem B821357 : Blo 362758 821357 := bbase (se 3 (by rfl) ⟨154004, by rfl⟩ : syracuseStep 821357 = 308009) (by norm_num)
theorem B460981 : Blo 362758 460981 := bbase (se 5 (by rfl) ⟨21608, by rfl⟩ : syracuseStep 460981 = 43217) (by norm_num)
theorem B821429 : Blo 362758 821429 := bbase (se 5 (by rfl) ⟨38504, by rfl⟩ : syracuseStep 821429 = 77009) (by norm_num)
theorem B1411253 : Blo 362758 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B821501 : Blo 362758 821501 := bbase (se 3 (by rfl) ⟨154031, by rfl⟩ : syracuseStep 821501 = 308063) (by norm_num)
theorem B821573 : Blo 362758 821573 := bbase (se 4 (by rfl) ⟨77022, by rfl⟩ : syracuseStep 821573 = 154045) (by norm_num)
theorem B461153 : Blo 362758 461153 := bbase (se 2 (by rfl) ⟨172932, by rfl⟩ : syracuseStep 461153 = 345865) (by norm_num)
theorem B3115381 : Blo 362758 3115381 := bbase (se 5 (by rfl) ⟨146033, by rfl⟩ : syracuseStep 3115381 = 292067) (by norm_num)
theorem B821645 : Blo 362758 821645 := bbase (se 3 (by rfl) ⟨154058, by rfl⟩ : syracuseStep 821645 = 308117) (by norm_num)
theorem B919957 : Blo 362758 919957 := bbase (se 6 (by rfl) ⟨21561, by rfl⟩ : syracuseStep 919957 = 43123) (by norm_num)
theorem B461209 : Blo 362758 461209 := bbase (se 2 (by rfl) ⟨172953, by rfl⟩ : syracuseStep 461209 = 345907) (by norm_num)
theorem B821717 : Blo 362758 821717 := bbase (se 7 (by rfl) ⟨9629, by rfl⟩ : syracuseStep 821717 = 19259) (by norm_num)
theorem B461305 : Blo 362758 461305 := bbase (se 2 (by rfl) ⟨172989, by rfl⟩ : syracuseStep 461305 = 345979) (by norm_num)
theorem B920069 : Blo 362758 920069 := bbase (se 4 (by rfl) ⟨86256, by rfl⟩ : syracuseStep 920069 = 172513) (by norm_num)
theorem B821789 : Blo 362758 821789 := bbase (se 3 (by rfl) ⟨154085, by rfl⟩ : syracuseStep 821789 = 308171) (by norm_num)
theorem B690781 : Blo 362758 690781 := bbase (se 3 (by rfl) ⟨129521, by rfl⟩ : syracuseStep 690781 = 259043) (by norm_num)
theorem B821861 : Blo 362758 821861 := bbase (se 4 (by rfl) ⟨77049, by rfl⟩ : syracuseStep 821861 = 154099) (by norm_num)
theorem B461477 : Blo 362758 461477 := bbase (se 4 (by rfl) ⟨43263, by rfl⟩ : syracuseStep 461477 = 86527) (by norm_num)
theorem B821933 : Blo 362758 821933 := bbase (se 3 (by rfl) ⟨154112, by rfl⟩ : syracuseStep 821933 = 308225) (by norm_num)
theorem B920261 : Blo 362758 920261 := bbase (se 4 (by rfl) ⟨86274, by rfl⟩ : syracuseStep 920261 = 172549) (by norm_num)
theorem B985813 : Blo 362758 985813 := bbase (se 7 (by rfl) ⟨11552, by rfl⟩ : syracuseStep 985813 = 23105) (by norm_num)
theorem B461533 : Blo 362758 461533 := bbase (se 3 (by rfl) ⟨86537, by rfl⟩ : syracuseStep 461533 = 173075) (by norm_num)
theorem B690925 : Blo 362758 690925 := bbase (se 3 (by rfl) ⟨129548, by rfl⟩ : syracuseStep 690925 = 259097) (by norm_num)
theorem B822005 : Blo 362758 822005 := bbase (se 5 (by rfl) ⟨38531, by rfl⟩ : syracuseStep 822005 = 77063) (by norm_num)
theorem B658189 : Blo 362758 658189 := bbase (se 3 (by rfl) ⟨123410, by rfl⟩ : syracuseStep 658189 = 246821) (by norm_num)
theorem B461629 : Blo 362758 461629 := bbase (se 3 (by rfl) ⟨86555, by rfl⟩ : syracuseStep 461629 = 173111) (by norm_num)
theorem B822077 : Blo 362758 822077 := bbase (se 3 (by rfl) ⟨154139, by rfl⟩ : syracuseStep 822077 = 308279) (by norm_num)
theorem B822149 : Blo 362758 822149 := bbase (se 4 (by rfl) ⟨77076, by rfl⟩ : syracuseStep 822149 = 154153) (by norm_num)
theorem B691085 : Blo 362758 691085 := bbase (se 3 (by rfl) ⟨129578, by rfl⟩ : syracuseStep 691085 = 259157) (by norm_num)
theorem B822221 : Blo 362758 822221 := bbase (se 3 (by rfl) ⟨154166, by rfl⟩ : syracuseStep 822221 = 308333) (by norm_num)
theorem B461801 : Blo 362758 461801 := bbase (se 2 (by rfl) ⟨173175, by rfl⟩ : syracuseStep 461801 = 346351) (by norm_num)
theorem B822293 : Blo 362758 822293 := bbase (se 6 (by rfl) ⟨19272, by rfl⟩ : syracuseStep 822293 = 38545) (by norm_num)
theorem B920605 : Blo 362758 920605 := bbase (se 3 (by rfl) ⟨172613, by rfl⟩ : syracuseStep 920605 = 345227) (by norm_num)
theorem B691229 : Blo 362758 691229 := bbase (se 3 (by rfl) ⟨129605, by rfl⟩ : syracuseStep 691229 = 259211) (by norm_num)
theorem B461857 : Blo 362758 461857 := bbase (se 2 (by rfl) ⟨173196, by rfl⟩ : syracuseStep 461857 = 346393) (by norm_num)
theorem B1575973 : Blo 362758 1575973 := bbase (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) (by norm_num)
theorem B822365 : Blo 362758 822365 := bbase (se 3 (by rfl) ⟨154193, by rfl⟩ : syracuseStep 822365 = 308387) (by norm_num)
theorem B461953 : Blo 362758 461953 := bbase (se 2 (by rfl) ⟨173232, by rfl⟩ : syracuseStep 461953 = 346465) (by norm_num)
theorem B1838213 : Blo 362758 1838213 := bbase (se 4 (by rfl) ⟨172332, by rfl⟩ : syracuseStep 1838213 = 344665) (by norm_num)
theorem B920717 : Blo 362758 920717 := bbase (se 3 (by rfl) ⟨172634, by rfl⟩ : syracuseStep 920717 = 345269) (by norm_num)
theorem B2067605 : Blo 362758 2067605 := bbase (se 6 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 2067605 = 96919) (by norm_num)
theorem B1313957 : Blo 362758 1313957 := bbase (se 4 (by rfl) ⟨123183, by rfl⟩ : syracuseStep 1313957 = 246367) (by norm_num)
theorem B822437 : Blo 362758 822437 := bbase (se 4 (by rfl) ⟨77103, by rfl⟩ : syracuseStep 822437 = 154207) (by norm_num)
theorem B822509 : Blo 362758 822509 := bbase (se 3 (by rfl) ⟨154220, by rfl⟩ : syracuseStep 822509 = 308441) (by norm_num)
theorem B658709 : Blo 362758 658709 := bbase (se 6 (by rfl) ⟨15438, by rfl⟩ : syracuseStep 658709 = 30877) (by norm_num)
theorem B462125 : Blo 362758 462125 := bbase (se 3 (by rfl) ⟨86648, by rfl⟩ : syracuseStep 462125 = 173297) (by norm_num)
theorem B822581 : Blo 362758 822581 := bbase (se 5 (by rfl) ⟨38558, by rfl⟩ : syracuseStep 822581 = 77117) (by norm_num)
theorem B691517 : Blo 362758 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B920909 : Blo 362758 920909 := bbase (se 3 (by rfl) ⟨172670, by rfl⟩ : syracuseStep 920909 = 345341) (by norm_num)
theorem B462181 : Blo 362758 462181 := bbase (se 4 (by rfl) ⟨43329, by rfl⟩ : syracuseStep 462181 = 86659) (by norm_num)
theorem B822653 : Blo 362758 822653 := bbase (se 3 (by rfl) ⟨154247, by rfl⟩ : syracuseStep 822653 = 308495) (by norm_num)
theorem B396677 : Blo 362758 396677 := bbase (se 4 (by rfl) ⟨37188, by rfl⟩ : syracuseStep 396677 = 74377) (by norm_num)
theorem B822725 : Blo 362758 822725 := bbase (se 4 (by rfl) ⟨77130, by rfl⟩ : syracuseStep 822725 = 154261) (by norm_num)
theorem B1314245 : Blo 362758 1314245 := bbase (se 4 (by rfl) ⟨123210, by rfl⟩ : syracuseStep 1314245 = 246421) (by norm_num)
theorem B462277 : Blo 362758 462277 := bbase (se 4 (by rfl) ⟨43338, by rfl⟩ : syracuseStep 462277 = 86677) (by norm_num)
theorem B691669 : Blo 362758 691669 := bbase (se 7 (by rfl) ⟨8105, by rfl⟩ : syracuseStep 691669 = 16211) (by norm_num)
theorem B822797 : Blo 362758 822797 := bbase (se 3 (by rfl) ⟨154274, by rfl⟩ : syracuseStep 822797 = 308549) (by norm_num)
theorem B1379861 : Blo 362758 1379861 := bbase (se 6 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 1379861 = 64681) (by norm_num)
theorem B1248821 : Blo 362758 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B822869 : Blo 362758 822869 := bbase (se 8 (by rfl) ⟨4821, by rfl⟩ : syracuseStep 822869 = 9643) (by norm_num)
theorem B1052261 : Blo 362758 1052261 := bbase (se 4 (by rfl) ⟨98649, by rfl⟩ : syracuseStep 1052261 = 197299) (by norm_num)
theorem B462449 : Blo 362758 462449 := bbase (se 2 (by rfl) ⟨173418, by rfl⟩ : syracuseStep 462449 = 346837) (by norm_num)
theorem B888461 : Blo 362758 888461 := bbase (se 3 (by rfl) ⟨166586, by rfl⟩ : syracuseStep 888461 = 333173) (by norm_num)
theorem B495253 : Blo 362758 495253 := bbase (se 6 (by rfl) ⟨11607, by rfl⟩ : syracuseStep 495253 = 23215) (by norm_num)
theorem B822941 : Blo 362758 822941 := bbase (se 3 (by rfl) ⟨154301, by rfl⟩ : syracuseStep 822941 = 308603) (by norm_num)
theorem B921253 : Blo 362758 921253 := bbase (se 4 (by rfl) ⟨86367, by rfl⟩ : syracuseStep 921253 = 172735) (by norm_num)
theorem B462505 : Blo 362758 462505 := bbase (se 2 (by rfl) ⟨173439, by rfl⟩ : syracuseStep 462505 = 346879) (by norm_num)
theorem B823013 : Blo 362758 823013 := bbase (se 4 (by rfl) ⟨77157, by rfl⟩ : syracuseStep 823013 = 154315) (by norm_num)
theorem B691973 : Blo 362758 691973 := bbase (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) (by norm_num)
theorem B462601 : Blo 362758 462601 := bbase (se 2 (by rfl) ⟨173475, by rfl⟩ : syracuseStep 462601 = 346951) (by norm_num)
theorem B921365 : Blo 362758 921365 := bbase (se 6 (by rfl) ⟨21594, by rfl⟩ : syracuseStep 921365 = 43189) (by norm_num)
theorem B823085 : Blo 362758 823085 := bbase (se 3 (by rfl) ⟨154328, by rfl⟩ : syracuseStep 823085 = 308657) (by norm_num)
theorem B1380149 : Blo 362758 1380149 := bbase (se 5 (by rfl) ⟨64694, by rfl⟩ : syracuseStep 1380149 = 129389) (by norm_num)
theorem B823157 : Blo 362758 823157 := bbase (se 5 (by rfl) ⟨38585, by rfl⟩ : syracuseStep 823157 = 77171) (by norm_num)
theorem B1576853 : Blo 362758 1576853 := bbase (se 6 (by rfl) ⟨36957, by rfl⟩ : syracuseStep 1576853 = 73915) (by norm_num)
theorem B462773 : Blo 362758 462773 := bbase (se 5 (by rfl) ⟨21692, by rfl⟩ : syracuseStep 462773 = 43385) (by norm_num)
theorem B823229 : Blo 362758 823229 := bbase (se 3 (by rfl) ⟨154355, by rfl⟩ : syracuseStep 823229 = 308711) (by norm_num)
theorem B921557 : Blo 362758 921557 := bbase (se 7 (by rfl) ⟨10799, by rfl⟩ : syracuseStep 921557 = 21599) (by norm_num)
theorem B2625493 : Blo 362758 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B462829 : Blo 362758 462829 := bbase (se 3 (by rfl) ⟨86780, by rfl⟩ : syracuseStep 462829 = 173561) (by norm_num)
theorem B823301 : Blo 362758 823301 := bbase (se 4 (by rfl) ⟨77184, by rfl⟩ : syracuseStep 823301 = 154369) (by norm_num)
theorem B462925 : Blo 362758 462925 := bbase (se 3 (by rfl) ⟨86798, by rfl⟩ : syracuseStep 462925 = 173597) (by norm_num)
theorem B823373 : Blo 362758 823373 := bbase (se 3 (by rfl) ⟨154382, by rfl⟩ : syracuseStep 823373 = 308765) (by norm_num)
theorem B987221 : Blo 362758 987221 := bbase (se 8 (by rfl) ⟨5784, by rfl⟩ : syracuseStep 987221 = 11569) (by norm_num)
theorem B21139541 : Blo 362758 21139541 := bbase (se 8 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 21139541 = 247729) (by norm_num)
theorem B823445 : Blo 362758 823445 := bbase (se 6 (by rfl) ⟨19299, by rfl⟩ : syracuseStep 823445 = 38599) (by norm_num)
theorem B9539797 : Blo 362758 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B823517 : Blo 362758 823517 := bbase (se 3 (by rfl) ⟨154409, by rfl⟩ : syracuseStep 823517 = 308819) (by norm_num)
theorem B463097 : Blo 362758 463097 := bbase (se 2 (by rfl) ⟨173661, by rfl⟩ : syracuseStep 463097 = 347323) (by norm_num)
theorem B889093 : Blo 362758 889093 := bbase (se 4 (by rfl) ⟨83352, by rfl⟩ : syracuseStep 889093 = 166705) (by norm_num)
theorem B823589 : Blo 362758 823589 := bbase (se 4 (by rfl) ⟨77211, by rfl⟩ : syracuseStep 823589 = 154423) (by norm_num)
theorem B921901 : Blo 362758 921901 := bbase (se 3 (by rfl) ⟨172856, by rfl⟩ : syracuseStep 921901 = 345713) (by norm_num)
theorem B463153 : Blo 362758 463153 := bbase (se 2 (by rfl) ⟨173682, by rfl⟩ : syracuseStep 463153 = 347365) (by norm_num)
theorem B3117365 : Blo 362758 3117365 := bbase (se 5 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 3117365 = 292253) (by norm_num)
theorem B823661 : Blo 362758 823661 := bbase (se 3 (by rfl) ⟨154436, by rfl⟩ : syracuseStep 823661 = 308873) (by norm_num)
theorem B463249 : Blo 362758 463249 := bbase (se 2 (by rfl) ⟨173718, by rfl⟩ : syracuseStep 463249 = 347437) (by norm_num)
theorem B1839509 : Blo 362758 1839509 := bbase (se 6 (by rfl) ⟨43113, by rfl⟩ : syracuseStep 1839509 = 86227) (by norm_num)
theorem B922013 : Blo 362758 922013 := bbase (se 3 (by rfl) ⟨172877, by rfl⟩ : syracuseStep 922013 = 345755) (by norm_num)
theorem B823733 : Blo 362758 823733 := bbase (se 5 (by rfl) ⟨38612, by rfl⟩ : syracuseStep 823733 = 77225) (by norm_num)
theorem B2757077 : Blo 362758 2757077 := bbase (se 7 (by rfl) ⟨32309, by rfl⟩ : syracuseStep 2757077 = 64619) (by norm_num)
theorem B692725 : Blo 362758 692725 := bbase (se 5 (by rfl) ⟨32471, by rfl⟩ : syracuseStep 692725 = 64943) (by norm_num)
theorem B823805 : Blo 362758 823805 := bbase (se 3 (by rfl) ⟨154463, by rfl⟩ : syracuseStep 823805 = 308927) (by norm_num)
theorem B987653 : Blo 362758 987653 := bbase (se 4 (by rfl) ⟨92592, by rfl⟩ : syracuseStep 987653 = 185185) (by norm_num)
theorem B463421 : Blo 362758 463421 := bbase (se 3 (by rfl) ⟨86891, by rfl⟩ : syracuseStep 463421 = 173783) (by norm_num)
theorem B823877 : Blo 362758 823877 := bbase (se 4 (by rfl) ⟨77238, by rfl⟩ : syracuseStep 823877 = 154477) (by norm_num)
theorem B1184341 : Blo 362758 1184341 := bbase (se 8 (by rfl) ⟨6939, by rfl⟩ : syracuseStep 1184341 = 13879) (by norm_num)
theorem B922205 : Blo 362758 922205 := bbase (se 3 (by rfl) ⟨172913, by rfl⟩ : syracuseStep 922205 = 345827) (by norm_num)
theorem B463477 : Blo 362758 463477 := bbase (se 5 (by rfl) ⟨21725, by rfl⟩ : syracuseStep 463477 = 43451) (by norm_num)
theorem B692869 : Blo 362758 692869 := bbase (se 4 (by rfl) ⟨64956, by rfl⟩ : syracuseStep 692869 = 129913) (by norm_num)
theorem B823949 : Blo 362758 823949 := bbase (se 3 (by rfl) ⟨154490, by rfl⟩ : syracuseStep 823949 = 308981) (by norm_num)
theorem B824021 : Blo 362758 824021 := bbase (se 7 (by rfl) ⟨9656, by rfl⟩ : syracuseStep 824021 = 19313) (by norm_num)
theorem B463573 : Blo 362758 463573 := bbase (se 7 (by rfl) ⟨5432, by rfl⟩ : syracuseStep 463573 = 10865) (by norm_num)
theorem B824093 : Blo 362758 824093 := bbase (se 3 (by rfl) ⟨154517, by rfl⟩ : syracuseStep 824093 = 309035) (by norm_num)
theorem B693029 : Blo 362758 693029 := bbase (se 4 (by rfl) ⟨64971, by rfl⟩ : syracuseStep 693029 = 129943) (by norm_num)
theorem B529237 : Blo 362758 529237 := bbase (se 9 (by rfl) ⟨1550, by rfl⟩ : syracuseStep 529237 = 3101) (by norm_num)
theorem B824165 : Blo 362758 824165 := bbase (se 4 (by rfl) ⟨77265, by rfl⟩ : syracuseStep 824165 = 154531) (by norm_num)
theorem B889717 : Blo 362758 889717 := bbase (se 5 (by rfl) ⟨41705, by rfl⟩ : syracuseStep 889717 = 83411) (by norm_num)
theorem B463745 : Blo 362758 463745 := bbase (se 2 (by rfl) ⟨173904, by rfl⟩ : syracuseStep 463745 = 347809) (by norm_num)
theorem B824237 : Blo 362758 824237 := bbase (se 3 (by rfl) ⟨154544, by rfl⟩ : syracuseStep 824237 = 309089) (by norm_num)
theorem B922549 : Blo 362758 922549 := bbase (se 5 (by rfl) ⟨43244, by rfl⟩ : syracuseStep 922549 = 86489) (by norm_num)
theorem B1872821 : Blo 362758 1872821 := bbase (se 5 (by rfl) ⟨87788, by rfl⟩ : syracuseStep 1872821 = 175577) (by norm_num)
theorem B693173 : Blo 362758 693173 := bbase (se 5 (by rfl) ⟨32492, by rfl⟩ : syracuseStep 693173 = 64985) (by norm_num)
theorem B463801 : Blo 362758 463801 := bbase (se 2 (by rfl) ⟨173925, by rfl⟩ : syracuseStep 463801 = 347851) (by norm_num)
theorem B1381333 : Blo 362758 1381333 := bbase (se 7 (by rfl) ⟨16187, by rfl⟩ : syracuseStep 1381333 = 32375) (by norm_num)
theorem B824309 : Blo 362758 824309 := bbase (se 5 (by rfl) ⟨38639, by rfl⟩ : syracuseStep 824309 = 77279) (by norm_num)
theorem B463897 : Blo 362758 463897 := bbase (se 2 (by rfl) ⟨173961, by rfl⟩ : syracuseStep 463897 = 347923) (by norm_num)
theorem B922661 : Blo 362758 922661 := bbase (se 4 (by rfl) ⟨86499, by rfl⟩ : syracuseStep 922661 = 172999) (by norm_num)
theorem B824381 : Blo 362758 824381 := bbase (se 3 (by rfl) ⟨154571, by rfl⟩ : syracuseStep 824381 = 309143) (by norm_num)
theorem B824453 : Blo 362758 824453 := bbase (se 4 (by rfl) ⟨77292, by rfl⟩ : syracuseStep 824453 = 154585) (by norm_num)
theorem B464069 : Blo 362758 464069 := bbase (se 4 (by rfl) ⟨43506, by rfl⟩ : syracuseStep 464069 = 87013) (by norm_num)
theorem B824525 : Blo 362758 824525 := bbase (se 3 (by rfl) ⟨154598, by rfl⟩ : syracuseStep 824525 = 309197) (by norm_num)
theorem B693461 : Blo 362758 693461 := bbase (se 7 (by rfl) ⟨8126, by rfl⟩ : syracuseStep 693461 = 16253) (by norm_num)
theorem B922853 : Blo 362758 922853 := bbase (se 4 (by rfl) ⟨86517, by rfl⟩ : syracuseStep 922853 = 173035) (by norm_num)
theorem B464125 : Blo 362758 464125 := bbase (se 3 (by rfl) ⟨87023, by rfl⟩ : syracuseStep 464125 = 174047) (by norm_num)
theorem B1381637 : Blo 362758 1381637 := bbase (se 4 (by rfl) ⟨129528, by rfl⟩ : syracuseStep 1381637 = 259057) (by norm_num)
theorem B824597 : Blo 362758 824597 := bbase (se 6 (by rfl) ⟨19326, by rfl⟩ : syracuseStep 824597 = 38653) (by norm_num)
theorem B2069813 : Blo 362758 2069813 := bbase (se 5 (by rfl) ⟨97022, by rfl⟩ : syracuseStep 2069813 = 194045) (by norm_num)
theorem B824669 : Blo 362758 824669 := bbase (se 3 (by rfl) ⟨154625, by rfl⟩ : syracuseStep 824669 = 309251) (by norm_num)
theorem B693613 : Blo 362758 693613 := bbase (se 3 (by rfl) ⟨130052, by rfl⟩ : syracuseStep 693613 = 260105) (by norm_num)
theorem B824741 : Blo 362758 824741 := bbase (se 4 (by rfl) ⟨77319, by rfl⟩ : syracuseStep 824741 = 154639) (by norm_num)
theorem B824813 : Blo 362758 824813 := bbase (se 3 (by rfl) ⟨154652, by rfl⟩ : syracuseStep 824813 = 309305) (by norm_num)
theorem B824885 : Blo 362758 824885 := bbase (se 5 (by rfl) ⟨38666, by rfl⟩ : syracuseStep 824885 = 77333) (by norm_num)
theorem B923197 : Blo 362758 923197 := bbase (se 3 (by rfl) ⟨173099, by rfl⟩ : syracuseStep 923197 = 346199) (by norm_num)
theorem B988757 : Blo 362758 988757 := bbase (se 8 (by rfl) ⟨5793, by rfl⟩ : syracuseStep 988757 = 11587) (by norm_num)
theorem B824957 : Blo 362758 824957 := bbase (se 3 (by rfl) ⟨154679, by rfl⟩ : syracuseStep 824957 = 309359) (by norm_num)
theorem B3511957 : Blo 362758 3511957 := bbase (se 6 (by rfl) ⟨82311, by rfl⟩ : syracuseStep 3511957 = 164623) (by norm_num)
theorem B693917 : Blo 362758 693917 := bbase (se 3 (by rfl) ⟨130109, by rfl⟩ : syracuseStep 693917 = 260219) (by norm_num)
theorem B1840805 : Blo 362758 1840805 := bbase (se 4 (by rfl) ⟨172575, by rfl⟩ : syracuseStep 1840805 = 345151) (by norm_num)
theorem B923309 : Blo 362758 923309 := bbase (se 3 (by rfl) ⟨173120, by rfl⟩ : syracuseStep 923309 = 346241) (by norm_num)
theorem B562877 : Blo 362758 562877 := bbase (se 3 (by rfl) ⟨105539, by rfl⟩ : syracuseStep 562877 = 211079) (by norm_num)
theorem B825029 : Blo 362758 825029 := bbase (se 4 (by rfl) ⟨77346, by rfl⟩ : syracuseStep 825029 = 154693) (by norm_num)
theorem B825101 : Blo 362758 825101 := bbase (se 3 (by rfl) ⟨154706, by rfl⟩ : syracuseStep 825101 = 309413) (by norm_num)
theorem B825173 : Blo 362758 825173 := bbase (se 9 (by rfl) ⟨2417, by rfl⟩ : syracuseStep 825173 = 4835) (by norm_num)
theorem B923501 : Blo 362758 923501 := bbase (se 3 (by rfl) ⟨173156, by rfl⟩ : syracuseStep 923501 = 346313) (by norm_num)
theorem B923845 : Blo 362758 923845 := bbase (se 4 (by rfl) ⟨86610, by rfl⟩ : syracuseStep 923845 = 173221) (by norm_num)
theorem B923957 : Blo 362758 923957 := bbase (se 5 (by rfl) ⟨43310, by rfl⟩ : syracuseStep 923957 = 86621) (by norm_num)
theorem B694669 : Blo 362758 694669 := bbase (se 3 (by rfl) ⟨130250, by rfl⟩ : syracuseStep 694669 = 260501) (by norm_num)
theorem B989621 : Blo 362758 989621 := bbase (se 5 (by rfl) ⟨46388, by rfl⟩ : syracuseStep 989621 = 92777) (by norm_num)
theorem B924149 : Blo 362758 924149 := bbase (se 5 (by rfl) ⟨43319, by rfl⟩ : syracuseStep 924149 = 86639) (by norm_num)
theorem B694813 : Blo 362758 694813 := bbase (se 3 (by rfl) ⟨130277, by rfl⟩ : syracuseStep 694813 = 260555) (by norm_num)
theorem B694973 : Blo 362758 694973 := bbase (se 3 (by rfl) ⟨130307, by rfl⟩ : syracuseStep 694973 = 260615) (by norm_num)
theorem B2333461 : Blo 362758 2333461 := bbase (se 6 (by rfl) ⟨54690, by rfl⟩ : syracuseStep 2333461 = 109381) (by norm_num)
theorem B924493 : Blo 362758 924493 := bbase (se 3 (by rfl) ⟨173342, by rfl⟩ : syracuseStep 924493 = 346685) (by norm_num)
theorem B695117 : Blo 362758 695117 := bbase (se 3 (by rfl) ⟨130334, by rfl⟩ : syracuseStep 695117 = 260669) (by norm_num)
theorem B990053 : Blo 362758 990053 := bbase (se 4 (by rfl) ⟨92817, by rfl⟩ : syracuseStep 990053 = 185635) (by norm_num)
theorem B1842101 : Blo 362758 1842101 := bbase (se 5 (by rfl) ⟨86348, by rfl⟩ : syracuseStep 1842101 = 172697) (by norm_num)
theorem B924605 : Blo 362758 924605 := bbase (se 3 (by rfl) ⟨173363, by rfl⟩ : syracuseStep 924605 = 346727) (by norm_num)
theorem B695405 : Blo 362758 695405 := bbase (se 3 (by rfl) ⟨130388, by rfl⟩ : syracuseStep 695405 = 260777) (by norm_num)
theorem B924797 : Blo 362758 924797 := bbase (se 3 (by rfl) ⟨173399, by rfl⟩ : syracuseStep 924797 = 346799) (by norm_num)
theorem B1023205 : Blo 362758 1023205 := bbase (se 4 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 1023205 = 191851) (by norm_num)
theorem B695557 : Blo 362758 695557 := bbase (se 4 (by rfl) ⟨65208, by rfl⟩ : syracuseStep 695557 = 130417) (by norm_num)
theorem B1383749 : Blo 362758 1383749 := bbase (se 4 (by rfl) ⟨129726, by rfl⟩ : syracuseStep 1383749 = 259453) (by norm_num)
theorem B23928149 : Blo 362758 23928149 := bbase (se 11 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 23928149 = 35051) (by norm_num)
theorem B925141 : Blo 362758 925141 := bbase (se 7 (by rfl) ⟨10841, by rfl⟩ : syracuseStep 925141 = 21683) (by norm_num)
theorem B3317269 : Blo 362758 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B695861 : Blo 362758 695861 := bbase (se 5 (by rfl) ⟨32618, by rfl⟩ : syracuseStep 695861 = 65237) (by norm_num)
theorem B925253 : Blo 362758 925253 := bbase (se 4 (by rfl) ⟨86742, by rfl⟩ : syracuseStep 925253 = 173485) (by norm_num)
theorem B1384037 : Blo 362758 1384037 := bbase (se 4 (by rfl) ⟨129753, by rfl⟩ : syracuseStep 1384037 = 259507) (by norm_num)
theorem B368249 : Blo 362758 368249 := bbase (se 2 (by rfl) ⟨138093, by rfl⟩ : syracuseStep 368249 = 276187) (by norm_num)
theorem B1482421 : Blo 362758 1482421 := bbase (se 5 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 1482421 = 138977) (by norm_num)
theorem B2989781 : Blo 362758 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B925445 : Blo 362758 925445 := bbase (se 4 (by rfl) ⟨86760, by rfl⟩ : syracuseStep 925445 = 173521) (by norm_num)
theorem B4202389 : Blo 362758 4202389 := bbase (se 6 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 4202389 = 196987) (by norm_num)
theorem B925789 : Blo 362758 925789 := bbase (se 3 (by rfl) ⟨173585, by rfl⟩ : syracuseStep 925789 = 347171) (by norm_num)
theorem B1843397 : Blo 362758 1843397 := bbase (se 4 (by rfl) ⟨172818, by rfl⟩ : syracuseStep 1843397 = 345637) (by norm_num)
theorem B925901 : Blo 362758 925901 := bbase (se 3 (by rfl) ⟨173606, by rfl⟩ : syracuseStep 925901 = 347213) (by norm_num)
theorem B926093 : Blo 362758 926093 := bbase (se 3 (by rfl) ⟨173642, by rfl⟩ : syracuseStep 926093 = 347285) (by norm_num)
theorem B1745621 : Blo 362758 1745621 := bbase (se 7 (by rfl) ⟨20456, by rfl⟩ : syracuseStep 1745621 = 40913) (by norm_num)
theorem B926437 : Blo 362758 926437 := bbase (se 4 (by rfl) ⟨86853, by rfl⟩ : syracuseStep 926437 = 173707) (by norm_num)
theorem B1385221 : Blo 362758 1385221 := bbase (se 4 (by rfl) ⟨129864, by rfl⟩ : syracuseStep 1385221 = 259729) (by norm_num)
theorem B926549 : Blo 362758 926549 := bbase (se 9 (by rfl) ⟨2714, by rfl⟩ : syracuseStep 926549 = 5429) (by norm_num)
theorem B664453 : Blo 362758 664453 := bbase (se 4 (by rfl) ⟨62292, by rfl⟩ : syracuseStep 664453 = 124585) (by norm_num)
theorem B926741 : Blo 362758 926741 := bbase (se 6 (by rfl) ⟨21720, by rfl⟩ : syracuseStep 926741 = 43441) (by norm_num)
theorem B1385525 : Blo 362758 1385525 := bbase (se 5 (by rfl) ⟨64946, by rfl⟩ : syracuseStep 1385525 = 129893) (by norm_num)
theorem B370013 : Blo 362758 370013 := bbase (se 3 (by rfl) ⟨69377, by rfl⟩ : syracuseStep 370013 = 138755) (by norm_num)
theorem B927085 : Blo 362758 927085 := bbase (se 3 (by rfl) ⟨173828, by rfl⟩ : syracuseStep 927085 = 347657) (by norm_num)
theorem B664949 : Blo 362758 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B1844693 : Blo 362758 1844693 := bbase (se 7 (by rfl) ⟨21617, by rfl⟩ : syracuseStep 1844693 = 43235) (by norm_num)
theorem B927197 : Blo 362758 927197 := bbase (se 3 (by rfl) ⟨173849, by rfl⟩ : syracuseStep 927197 = 347699) (by norm_num)
theorem B2336309 : Blo 362758 2336309 := bbase (se 5 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 2336309 = 219029) (by norm_num)
theorem B534101 : Blo 362758 534101 := bbase (se 8 (by rfl) ⟨3129, by rfl⟩ : syracuseStep 534101 = 6259) (by norm_num)
theorem B927389 : Blo 362758 927389 := bbase (se 3 (by rfl) ⟨173885, by rfl⟩ : syracuseStep 927389 = 347771) (by norm_num)
theorem B3516149 : Blo 362758 3516149 := bbase (se 5 (by rfl) ⟨164819, by rfl⟩ : syracuseStep 3516149 = 329639) (by norm_num)
theorem B436045 : Blo 362758 436045 := bbase (se 3 (by rfl) ⟨81758, by rfl⟩ : syracuseStep 436045 = 163517) (by norm_num)
theorem B436213 : Blo 362758 436213 := bbase (se 5 (by rfl) ⟨20447, by rfl⟩ : syracuseStep 436213 = 40895) (by norm_num)
theorem B927733 : Blo 362758 927733 := bbase (se 5 (by rfl) ⟨43487, by rfl⟩ : syracuseStep 927733 = 86975) (by norm_num)
theorem B927845 : Blo 362758 927845 := bbase (se 4 (by rfl) ⟨86985, by rfl⟩ : syracuseStep 927845 = 173971) (by norm_num)
theorem B1321109 : Blo 362758 1321109 := bbase (se 6 (by rfl) ⟨30963, by rfl⟩ : syracuseStep 1321109 = 61927) (by norm_num)
theorem B370865 : Blo 362758 370865 := bbase (se 2 (by rfl) ⟨139074, by rfl⟩ : syracuseStep 370865 = 278149) (by norm_num)
theorem B436409 : Blo 362758 436409 := bbase (se 2 (by rfl) ⟨163653, by rfl⟩ : syracuseStep 436409 = 327307) (by norm_num)
theorem B1583381 : Blo 362758 1583381 := bbase (se 6 (by rfl) ⟨37110, by rfl⟩ : syracuseStep 1583381 = 74221) (by norm_num)
theorem B928037 : Blo 362758 928037 := bbase (se 4 (by rfl) ⟨87003, by rfl⟩ : syracuseStep 928037 = 174007) (by norm_num)
theorem B9382229 : Blo 362758 9382229 := bbase (se 10 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 9382229 = 27487) (by norm_num)
theorem B567685 : Blo 362758 567685 := bbase (se 4 (by rfl) ⟨53220, by rfl⟩ : syracuseStep 567685 = 106441) (by norm_num)
theorem B1321397 : Blo 362758 1321397 := bbase (se 5 (by rfl) ⟨61940, by rfl⟩ : syracuseStep 1321397 = 123881) (by norm_num)
theorem B1550789 : Blo 362758 1550789 := bbase (se 4 (by rfl) ⟨145386, by rfl⟩ : syracuseStep 1550789 = 290773) (by norm_num)
theorem B371237 : Blo 362758 371237 := bbase (se 4 (by rfl) ⟨34803, by rfl⟩ : syracuseStep 371237 = 69607) (by norm_num)
theorem B1845989 : Blo 362758 1845989 := bbase (se 4 (by rfl) ⟨173061, by rfl⟩ : syracuseStep 1845989 = 346123) (by norm_num)
theorem B830213 : Blo 362758 830213 := bbase (se 4 (by rfl) ⟨77832, by rfl⟩ : syracuseStep 830213 = 155665) (by norm_num)
theorem B1682309 : Blo 362758 1682309 := bbase (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) (by norm_num)
theorem B1387637 : Blo 362758 1387637 := bbase (se 5 (by rfl) ⟨65045, by rfl⟩ : syracuseStep 1387637 = 130091) (by norm_num)
theorem B1486021 : Blo 362758 1486021 := bbase (se 4 (by rfl) ⟨139314, by rfl⟩ : syracuseStep 1486021 = 278629) (by norm_num)
theorem B1387925 : Blo 362758 1387925 := bbase (se 6 (by rfl) ⟨32529, by rfl⟩ : syracuseStep 1387925 = 65059) (by norm_num)
theorem B1748405 : Blo 362758 1748405 := bbase (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) (by norm_num)
theorem B1224341 : Blo 362758 1224341 := bbase (se 6 (by rfl) ⟨28695, by rfl⟩ : syracuseStep 1224341 = 57391) (by norm_num)
theorem B437981 : Blo 362758 437981 := bbase (se 3 (by rfl) ⟨82121, by rfl⟩ : syracuseStep 437981 = 164243) (by norm_num)
theorem B438005 : Blo 362758 438005 := bbase (se 5 (by rfl) ⟨20531, by rfl⟩ : syracuseStep 438005 = 41063) (by norm_num)
theorem B1847285 : Blo 362758 1847285 := bbase (se 5 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 1847285 = 173183) (by norm_num)
theorem B438313 : Blo 362758 438313 := bbase (se 2 (by rfl) ⟨164367, by rfl⟩ : syracuseStep 438313 = 328735) (by norm_num)
theorem B2764853 : Blo 362758 2764853 := bbase (se 5 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 2764853 = 259205) (by norm_num)
theorem B1781813 : Blo 362758 1781813 := bbase (se 5 (by rfl) ⟨83522, by rfl⟩ : syracuseStep 1781813 = 167045) (by norm_num)
theorem B1224773 : Blo 362758 1224773 := bbase (se 4 (by rfl) ⟨114822, by rfl⟩ : syracuseStep 1224773 = 229645) (by norm_num)
theorem B438485 : Blo 362758 438485 := bbase (se 7 (by rfl) ⟨5138, by rfl⟩ : syracuseStep 438485 = 10277) (by norm_num)
theorem B438601 : Blo 362758 438601 := bbase (se 2 (by rfl) ⟨164475, by rfl⟩ : syracuseStep 438601 = 328951) (by norm_num)
theorem B438697 : Blo 362758 438697 := bbase (se 2 (by rfl) ⟨164511, by rfl⟩ : syracuseStep 438697 = 329023) (by norm_num)
theorem B602581 : Blo 362758 602581 := bbase (se 7 (by rfl) ⟨7061, by rfl⟩ : syracuseStep 602581 = 14123) (by norm_num)
theorem B1225205 : Blo 362758 1225205 := bbase (se 5 (by rfl) ⟨57431, by rfl⟩ : syracuseStep 1225205 = 114863) (by norm_num)
theorem B1389109 : Blo 362758 1389109 := bbase (se 5 (by rfl) ⟨65114, by rfl⟩ : syracuseStep 1389109 = 130229) (by norm_num)
theorem B438841 : Blo 362758 438841 := bbase (se 2 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 438841 = 329131) (by norm_num)
theorem B1389413 : Blo 362758 1389413 := bbase (se 4 (by rfl) ⟨130257, by rfl⟩ : syracuseStep 1389413 = 260515) (by norm_num)
theorem B1225637 : Blo 362758 1225637 := bbase (se 4 (by rfl) ⟨114903, by rfl⟩ : syracuseStep 1225637 = 229807) (by norm_num)
theorem B12530645 : Blo 362758 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B1848581 : Blo 362758 1848581 := bbase (se 4 (by rfl) ⟨173304, by rfl⟩ : syracuseStep 1848581 = 346609) (by norm_num)
theorem B1226069 : Blo 362758 1226069 := bbase (se 13 (by rfl) ⟨224, by rfl⟩ : syracuseStep 1226069 = 449) (by norm_num)
theorem B1226501 : Blo 362758 1226501 := bbase (se 4 (by rfl) ⟨114984, by rfl⟩ : syracuseStep 1226501 = 229969) (by norm_num)
theorem B1718101 : Blo 362758 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B1718261 : Blo 362758 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B1226933 : Blo 362758 1226933 := bbase (se 5 (by rfl) ⟨57512, by rfl⟩ : syracuseStep 1226933 = 115025) (by norm_num)
theorem B669917 : Blo 362758 669917 := bbase (se 3 (by rfl) ⟨125609, by rfl⟩ : syracuseStep 669917 = 251219) (by norm_num)
theorem B440561 : Blo 362758 440561 := bbase (se 2 (by rfl) ⟨165210, by rfl⟩ : syracuseStep 440561 = 330421) (by norm_num)
theorem B375053 : Blo 362758 375053 := bbase (se 3 (by rfl) ⟨70322, by rfl⟩ : syracuseStep 375053 = 140645) (by norm_num)
theorem B440641 : Blo 362758 440641 := bbase (se 2 (by rfl) ⟨165240, by rfl⟩ : syracuseStep 440641 = 330481) (by norm_num)
theorem B1554821 : Blo 362758 1554821 := bbase (se 4 (by rfl) ⟨145764, by rfl⟩ : syracuseStep 1554821 = 291529) (by norm_num)
theorem B833989 : Blo 362758 833989 := bbase (se 4 (by rfl) ⟨78186, by rfl⟩ : syracuseStep 833989 = 156373) (by norm_num)
theorem B1849877 : Blo 362758 1849877 := bbase (se 6 (by rfl) ⟨43356, by rfl⟩ : syracuseStep 1849877 = 86713) (by norm_num)
theorem B1325605 : Blo 362758 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B408109 : Blo 362758 408109 := bbase (se 3 (by rfl) ⟨76520, by rfl⟩ : syracuseStep 408109 = 153041) (by norm_num)
theorem B408145 : Blo 362758 408145 := bbase (se 2 (by rfl) ⟨153054, by rfl⟩ : syracuseStep 408145 = 306109) (by norm_num)
theorem B1227365 : Blo 362758 1227365 := bbase (se 4 (by rfl) ⟨115065, by rfl⟩ : syracuseStep 1227365 = 230131) (by norm_num)
theorem B408181 : Blo 362758 408181 := bbase (se 5 (by rfl) ⟨19133, by rfl⟩ : syracuseStep 408181 = 38267) (by norm_num)
theorem B408217 : Blo 362758 408217 := bbase (se 2 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 408217 = 306163) (by norm_num)
theorem B408253 : Blo 362758 408253 := bbase (se 3 (by rfl) ⟨76547, by rfl⟩ : syracuseStep 408253 = 153095) (by norm_num)
theorem B408289 : Blo 362758 408289 := bbase (se 2 (by rfl) ⟨153108, by rfl⟩ : syracuseStep 408289 = 306217) (by norm_num)
theorem B408325 : Blo 362758 408325 := bbase (se 4 (by rfl) ⟨38280, by rfl⟩ : syracuseStep 408325 = 76561) (by norm_num)
theorem B408361 : Blo 362758 408361 := bbase (se 2 (by rfl) ⟨153135, by rfl⟩ : syracuseStep 408361 = 306271) (by norm_num)
theorem B408397 : Blo 362758 408397 := bbase (se 3 (by rfl) ⟨76574, by rfl⟩ : syracuseStep 408397 = 153149) (by norm_num)
theorem B408433 : Blo 362758 408433 := bbase (se 2 (by rfl) ⟨153162, by rfl⟩ : syracuseStep 408433 = 306325) (by norm_num)
theorem B408469 : Blo 362758 408469 := bbase (se 6 (by rfl) ⟨9573, by rfl⟩ : syracuseStep 408469 = 19147) (by norm_num)
theorem B1391525 : Blo 362758 1391525 := bbase (se 4 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 1391525 = 260911) (by norm_num)
theorem B932789 : Blo 362758 932789 := bbase (se 5 (by rfl) ⟨43724, by rfl⟩ : syracuseStep 932789 = 87449) (by norm_num)
theorem B408505 : Blo 362758 408505 := bbase (se 2 (by rfl) ⟨153189, by rfl⟩ : syracuseStep 408505 = 306379) (by norm_num)
theorem B2079701 : Blo 362758 2079701 := bbase (se 7 (by rfl) ⟨24371, by rfl⟩ : syracuseStep 2079701 = 48743) (by norm_num)
theorem B408541 : Blo 362758 408541 := bbase (se 3 (by rfl) ⟨76601, by rfl⟩ : syracuseStep 408541 = 153203) (by norm_num)
theorem B1260533 : Blo 362758 1260533 := bbase (se 5 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 1260533 = 118175) (by norm_num)
theorem B703477 : Blo 362758 703477 := bbase (se 5 (by rfl) ⟨32975, by rfl⟩ : syracuseStep 703477 = 65951) (by norm_num)
theorem B408577 : Blo 362758 408577 := bbase (se 2 (by rfl) ⟨153216, by rfl⟩ : syracuseStep 408577 = 306433) (by norm_num)
theorem B1227797 : Blo 362758 1227797 := bbase (se 6 (by rfl) ⟨28776, by rfl⟩ : syracuseStep 1227797 = 57553) (by norm_num)
theorem B408613 : Blo 362758 408613 := bbase (se 4 (by rfl) ⟨38307, by rfl⟩ : syracuseStep 408613 = 76615) (by norm_num)
theorem B408649 : Blo 362758 408649 := bbase (se 2 (by rfl) ⟨153243, by rfl⟩ : syracuseStep 408649 = 306487) (by norm_num)
theorem B408685 : Blo 362758 408685 := bbase (se 3 (by rfl) ⟨76628, by rfl⟩ : syracuseStep 408685 = 153257) (by norm_num)
theorem B408721 : Blo 362758 408721 := bbase (se 2 (by rfl) ⟨153270, by rfl⟩ : syracuseStep 408721 = 306541) (by norm_num)
theorem B408757 : Blo 362758 408757 := bbase (se 5 (by rfl) ⟨19160, by rfl⟩ : syracuseStep 408757 = 38321) (by norm_num)
theorem B1391813 : Blo 362758 1391813 := bbase (se 4 (by rfl) ⟨130482, by rfl⟩ : syracuseStep 1391813 = 260965) (by norm_num)
theorem B408793 : Blo 362758 408793 := bbase (se 2 (by rfl) ⟨153297, by rfl⟩ : syracuseStep 408793 = 306595) (by norm_num)
theorem B408829 : Blo 362758 408829 := bbase (se 3 (by rfl) ⟨76655, by rfl⟩ : syracuseStep 408829 = 153311) (by norm_num)
theorem B408865 : Blo 362758 408865 := bbase (se 2 (by rfl) ⟨153324, by rfl⟩ : syracuseStep 408865 = 306649) (by norm_num)
theorem B408901 : Blo 362758 408901 := bbase (se 4 (by rfl) ⟨38334, by rfl⟩ : syracuseStep 408901 = 76669) (by norm_num)
theorem B736589 : Blo 362758 736589 := bbase (se 3 (by rfl) ⟨138110, by rfl⟩ : syracuseStep 736589 = 276221) (by norm_num)
theorem B408937 : Blo 362758 408937 := bbase (se 2 (by rfl) ⟨153351, by rfl⟩ : syracuseStep 408937 = 306703) (by norm_num)
theorem B408973 : Blo 362758 408973 := bbase (se 3 (by rfl) ⟨76682, by rfl⟩ : syracuseStep 408973 = 153365) (by norm_num)
theorem B409009 : Blo 362758 409009 := bbase (se 2 (by rfl) ⟨153378, by rfl⟩ : syracuseStep 409009 = 306757) (by norm_num)
theorem B1228229 : Blo 362758 1228229 := bbase (se 4 (by rfl) ⟨115146, by rfl⟩ : syracuseStep 1228229 = 230293) (by norm_num)
theorem B409045 : Blo 362758 409045 := bbase (se 7 (by rfl) ⟨4793, by rfl⟩ : syracuseStep 409045 = 9587) (by norm_num)
theorem B409081 : Blo 362758 409081 := bbase (se 2 (by rfl) ⟨153405, by rfl⟩ : syracuseStep 409081 = 306811) (by norm_num)
theorem B409117 : Blo 362758 409117 := bbase (se 3 (by rfl) ⟨76709, by rfl⟩ : syracuseStep 409117 = 153419) (by norm_num)
theorem B409153 : Blo 362758 409153 := bbase (se 2 (by rfl) ⟨153432, by rfl⟩ : syracuseStep 409153 = 306865) (by norm_num)
theorem B933445 : Blo 362758 933445 := bbase (se 4 (by rfl) ⟨87510, by rfl⟩ : syracuseStep 933445 = 175021) (by norm_num)
theorem B835157 : Blo 362758 835157 := bbase (se 8 (by rfl) ⟨4893, by rfl⟩ : syracuseStep 835157 = 9787) (by norm_num)
theorem B409189 : Blo 362758 409189 := bbase (se 4 (by rfl) ⟨38361, by rfl⟩ : syracuseStep 409189 = 76723) (by norm_num)
theorem B1523333 : Blo 362758 1523333 := bbase (se 4 (by rfl) ⟨142812, by rfl⟩ : syracuseStep 1523333 = 285625) (by norm_num)
theorem B409225 : Blo 362758 409225 := bbase (se 2 (by rfl) ⟨153459, by rfl⟩ : syracuseStep 409225 = 306919) (by norm_num)
theorem B442013 : Blo 362758 442013 := bbase (se 3 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 442013 = 165755) (by norm_num)
theorem B409261 : Blo 362758 409261 := bbase (se 3 (by rfl) ⟨76736, by rfl⟩ : syracuseStep 409261 = 153473) (by norm_num)
theorem B409297 : Blo 362758 409297 := bbase (se 2 (by rfl) ⟨153486, by rfl⟩ : syracuseStep 409297 = 306973) (by norm_num)
theorem B409333 : Blo 362758 409333 := bbase (se 5 (by rfl) ⟨19187, by rfl⟩ : syracuseStep 409333 = 38375) (by norm_num)
theorem B409369 : Blo 362758 409369 := bbase (se 2 (by rfl) ⟨153513, by rfl⟩ : syracuseStep 409369 = 307027) (by norm_num)
theorem B1851173 : Blo 362758 1851173 := bbase (se 4 (by rfl) ⟨173547, by rfl⟩ : syracuseStep 1851173 = 347095) (by norm_num)
theorem B409405 : Blo 362758 409405 := bbase (se 3 (by rfl) ⟨76763, by rfl⟩ : syracuseStep 409405 = 153527) (by norm_num)
theorem B409441 : Blo 362758 409441 := bbase (se 2 (by rfl) ⟨153540, by rfl⟩ : syracuseStep 409441 = 307081) (by norm_num)
theorem B1228661 : Blo 362758 1228661 := bbase (se 5 (by rfl) ⟨57593, by rfl⟩ : syracuseStep 1228661 = 115187) (by norm_num)
theorem B409477 : Blo 362758 409477 := bbase (se 4 (by rfl) ⟨38388, by rfl⟩ : syracuseStep 409477 = 76777) (by norm_num)
theorem B409513 : Blo 362758 409513 := bbase (se 2 (by rfl) ⟨153567, by rfl⟩ : syracuseStep 409513 = 307135) (by norm_num)
theorem B409549 : Blo 362758 409549 := bbase (se 3 (by rfl) ⟨76790, by rfl⟩ : syracuseStep 409549 = 153581) (by norm_num)
theorem B409585 : Blo 362758 409585 := bbase (se 2 (by rfl) ⟨153594, by rfl⟩ : syracuseStep 409585 = 307189) (by norm_num)
theorem B409621 : Blo 362758 409621 := bbase (se 6 (by rfl) ⟨9600, by rfl⟩ : syracuseStep 409621 = 19201) (by norm_num)
theorem B409657 : Blo 362758 409657 := bbase (se 2 (by rfl) ⟨153621, by rfl⟩ : syracuseStep 409657 = 307243) (by norm_num)
theorem B409693 : Blo 362758 409693 := bbase (se 3 (by rfl) ⟨76817, by rfl⟩ : syracuseStep 409693 = 153635) (by norm_num)
theorem B1556597 : Blo 362758 1556597 := bbase (se 5 (by rfl) ⟨72965, by rfl⟩ : syracuseStep 1556597 = 145931) (by norm_num)
theorem B3129461 : Blo 362758 3129461 := bbase (se 5 (by rfl) ⟨146693, by rfl⟩ : syracuseStep 3129461 = 293387) (by norm_num)
theorem B409729 : Blo 362758 409729 := bbase (se 2 (by rfl) ⟨153648, by rfl⟩ : syracuseStep 409729 = 307297) (by norm_num)
theorem B409765 : Blo 362758 409765 := bbase (se 4 (by rfl) ⟨38415, by rfl⟩ : syracuseStep 409765 = 76831) (by norm_num)
theorem B409801 : Blo 362758 409801 := bbase (se 2 (by rfl) ⟨153675, by rfl⟩ : syracuseStep 409801 = 307351) (by norm_num)
theorem B1163477 : Blo 362758 1163477 := bbase (se 7 (by rfl) ⟨13634, by rfl⟩ : syracuseStep 1163477 = 27269) (by norm_num)
theorem B409837 : Blo 362758 409837 := bbase (se 3 (by rfl) ⟨76844, by rfl⟩ : syracuseStep 409837 = 153689) (by norm_num)
theorem B409873 : Blo 362758 409873 := bbase (se 2 (by rfl) ⟨153702, by rfl⟩ : syracuseStep 409873 = 307405) (by norm_num)
theorem B1229093 : Blo 362758 1229093 := bbase (se 4 (by rfl) ⟨115227, by rfl⟩ : syracuseStep 1229093 = 230455) (by norm_num)
theorem B409909 : Blo 362758 409909 := bbase (se 5 (by rfl) ⟨19214, by rfl⟩ : syracuseStep 409909 = 38429) (by norm_num)
theorem B1163605 : Blo 362758 1163605 := bbase (se 10 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 1163605 = 3409) (by norm_num)
theorem B409945 : Blo 362758 409945 := bbase (se 2 (by rfl) ⟨153729, by rfl⟩ : syracuseStep 409945 = 307459) (by norm_num)
theorem B409981 : Blo 362758 409981 := bbase (se 3 (by rfl) ⟨76871, by rfl⟩ : syracuseStep 409981 = 153743) (by norm_num)
theorem B410017 : Blo 362758 410017 := bbase (se 2 (by rfl) ⟨153756, by rfl⟩ : syracuseStep 410017 = 307513) (by norm_num)
theorem B442813 : Blo 362758 442813 := bbase (se 3 (by rfl) ⟨83027, by rfl⟩ : syracuseStep 442813 = 166055) (by norm_num)
theorem B410053 : Blo 362758 410053 := bbase (se 4 (by rfl) ⟨38442, by rfl⟩ : syracuseStep 410053 = 76885) (by norm_num)
theorem B934357 : Blo 362758 934357 := bbase (se 7 (by rfl) ⟨10949, by rfl⟩ : syracuseStep 934357 = 21899) (by norm_num)
theorem B410089 : Blo 362758 410089 := bbase (se 2 (by rfl) ⟨153783, by rfl⟩ : syracuseStep 410089 = 307567) (by norm_num)
theorem B3228149 : Blo 362758 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B410125 : Blo 362758 410125 := bbase (se 3 (by rfl) ⟨76898, by rfl⟩ : syracuseStep 410125 = 153797) (by norm_num)
theorem B410161 : Blo 362758 410161 := bbase (se 2 (by rfl) ⟨153810, by rfl⟩ : syracuseStep 410161 = 307621) (by norm_num)
theorem B1163861 : Blo 362758 1163861 := bbase (se 8 (by rfl) ⟨6819, by rfl⟩ : syracuseStep 1163861 = 13639) (by norm_num)
theorem B410197 : Blo 362758 410197 := bbase (se 8 (by rfl) ⟨2403, by rfl⟩ : syracuseStep 410197 = 4807) (by norm_num)
theorem B410233 : Blo 362758 410233 := bbase (se 2 (by rfl) ⟨153837, by rfl⟩ : syracuseStep 410233 = 307675) (by norm_num)
theorem B410269 : Blo 362758 410269 := bbase (se 3 (by rfl) ⟨76925, by rfl⟩ : syracuseStep 410269 = 153851) (by norm_num)
theorem B410305 : Blo 362758 410305 := bbase (se 2 (by rfl) ⟨153864, by rfl⟩ : syracuseStep 410305 = 307729) (by norm_num)
theorem B1229525 : Blo 362758 1229525 := bbase (se 7 (by rfl) ⟨14408, by rfl⟩ : syracuseStep 1229525 = 28817) (by norm_num)
theorem B410341 : Blo 362758 410341 := bbase (se 4 (by rfl) ⟨38469, by rfl⟩ : syracuseStep 410341 = 76939) (by norm_num)
theorem B410377 : Blo 362758 410377 := bbase (se 2 (by rfl) ⟨153891, by rfl⟩ : syracuseStep 410377 = 307783) (by norm_num)
theorem B410413 : Blo 362758 410413 := bbase (se 3 (by rfl) ⟨76952, by rfl⟩ : syracuseStep 410413 = 153905) (by norm_num)
theorem B508717 : Blo 362758 508717 := bbase (se 3 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 508717 = 190769) (by norm_num)
theorem B410449 : Blo 362758 410449 := bbase (se 2 (by rfl) ⟨153918, by rfl⟩ : syracuseStep 410449 = 307837) (by norm_num)
theorem B410485 : Blo 362758 410485 := bbase (se 5 (by rfl) ⟨19241, by rfl⟩ : syracuseStep 410485 = 38483) (by norm_num)
theorem B410521 : Blo 362758 410521 := bbase (se 2 (by rfl) ⟨153945, by rfl⟩ : syracuseStep 410521 = 307891) (by norm_num)
theorem B410557 : Blo 362758 410557 := bbase (se 3 (by rfl) ⟨76979, by rfl⟩ : syracuseStep 410557 = 153959) (by norm_num)
theorem B410593 : Blo 362758 410593 := bbase (se 2 (by rfl) ⟨153972, by rfl⟩ : syracuseStep 410593 = 307945) (by norm_num)
theorem B410629 : Blo 362758 410629 := bbase (se 4 (by rfl) ⟨38496, by rfl⟩ : syracuseStep 410629 = 76993) (by norm_num)
theorem B410665 : Blo 362758 410665 := bbase (se 2 (by rfl) ⟨153999, by rfl⟩ : syracuseStep 410665 = 307999) (by norm_num)
theorem B1852469 : Blo 362758 1852469 := bbase (se 5 (by rfl) ⟨86834, by rfl⟩ : syracuseStep 1852469 = 173669) (by norm_num)
theorem B410701 : Blo 362758 410701 := bbase (se 3 (by rfl) ⟨77006, by rfl⟩ : syracuseStep 410701 = 154013) (by norm_num)
theorem B1557589 : Blo 362758 1557589 := bbase (se 8 (by rfl) ⟨9126, by rfl⟩ : syracuseStep 1557589 = 18253) (by norm_num)
theorem B410737 : Blo 362758 410737 := bbase (se 2 (by rfl) ⟨154026, by rfl⟩ : syracuseStep 410737 = 308053) (by norm_num)
theorem B1229957 : Blo 362758 1229957 := bbase (se 4 (by rfl) ⟨115308, by rfl⟩ : syracuseStep 1229957 = 230617) (by norm_num)
theorem B410773 : Blo 362758 410773 := bbase (se 6 (by rfl) ⟨9627, by rfl⟩ : syracuseStep 410773 = 19255) (by norm_num)
theorem B738485 : Blo 362758 738485 := bbase (se 5 (by rfl) ⟨34616, by rfl⟩ : syracuseStep 738485 = 69233) (by norm_num)
theorem B410809 : Blo 362758 410809 := bbase (se 2 (by rfl) ⟨154053, by rfl⟩ : syracuseStep 410809 = 308107) (by norm_num)
theorem B410845 : Blo 362758 410845 := bbase (se 3 (by rfl) ⟨77033, by rfl⟩ : syracuseStep 410845 = 154067) (by norm_num)
theorem B410881 : Blo 362758 410881 := bbase (se 2 (by rfl) ⟨154080, by rfl⟩ : syracuseStep 410881 = 308161) (by norm_num)
theorem B410917 : Blo 362758 410917 := bbase (se 4 (by rfl) ⟨38523, by rfl⟩ : syracuseStep 410917 = 77047) (by norm_num)
theorem B410953 : Blo 362758 410953 := bbase (se 2 (by rfl) ⟨154107, by rfl⟩ : syracuseStep 410953 = 308215) (by norm_num)
theorem B410989 : Blo 362758 410989 := bbase (se 3 (by rfl) ⟨77060, by rfl⟩ : syracuseStep 410989 = 154121) (by norm_num)
theorem B411025 : Blo 362758 411025 := bbase (se 2 (by rfl) ⟨154134, by rfl⟩ : syracuseStep 411025 = 308269) (by norm_num)
theorem B411061 : Blo 362758 411061 := bbase (se 5 (by rfl) ⟨19268, by rfl⟩ : syracuseStep 411061 = 38537) (by norm_num)
theorem B411097 : Blo 362758 411097 := bbase (se 2 (by rfl) ⟨154161, by rfl⟩ : syracuseStep 411097 = 308323) (by norm_num)
theorem B411133 : Blo 362758 411133 := bbase (se 3 (by rfl) ⟨77087, by rfl⟩ : syracuseStep 411133 = 154175) (by norm_num)
theorem B411169 : Blo 362758 411169 := bbase (se 2 (by rfl) ⟨154188, by rfl⟩ : syracuseStep 411169 = 308377) (by norm_num)
theorem B1230389 : Blo 362758 1230389 := bbase (se 5 (by rfl) ⟨57674, by rfl⟩ : syracuseStep 1230389 = 115349) (by norm_num)
theorem B1754693 : Blo 362758 1754693 := bbase (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) (by norm_num)
theorem B411205 : Blo 362758 411205 := bbase (se 4 (by rfl) ⟨38550, by rfl⟩ : syracuseStep 411205 = 77101) (by norm_num)
theorem B1033813 : Blo 362758 1033813 := bbase (se 8 (by rfl) ⟨6057, by rfl⟩ : syracuseStep 1033813 = 12115) (by norm_num)
theorem B411241 : Blo 362758 411241 := bbase (se 2 (by rfl) ⟨154215, by rfl⟩ : syracuseStep 411241 = 308431) (by norm_num)
theorem B411277 : Blo 362758 411277 := bbase (se 3 (by rfl) ⟨77114, by rfl⟩ : syracuseStep 411277 = 154229) (by norm_num)
theorem B411313 : Blo 362758 411313 := bbase (se 2 (by rfl) ⟨154242, by rfl⟩ : syracuseStep 411313 = 308485) (by norm_num)
theorem B411349 : Blo 362758 411349 := bbase (se 7 (by rfl) ⟨4820, by rfl⟩ : syracuseStep 411349 = 9641) (by norm_num)
theorem B411385 : Blo 362758 411385 := bbase (se 2 (by rfl) ⟨154269, by rfl⟩ : syracuseStep 411385 = 308539) (by norm_num)
theorem B411421 : Blo 362758 411421 := bbase (se 3 (by rfl) ⟨77141, by rfl⟩ : syracuseStep 411421 = 154283) (by norm_num)
theorem B411457 : Blo 362758 411457 := bbase (se 2 (by rfl) ⟨154296, by rfl⟩ : syracuseStep 411457 = 308593) (by norm_num)
theorem B411493 : Blo 362758 411493 := bbase (se 4 (by rfl) ⟨38577, by rfl⟩ : syracuseStep 411493 = 77155) (by norm_num)
theorem B411529 : Blo 362758 411529 := bbase (se 2 (by rfl) ⟨154323, by rfl⟩ : syracuseStep 411529 = 308647) (by norm_num)
theorem B411565 : Blo 362758 411565 := bbase (se 3 (by rfl) ⟨77168, by rfl⟩ : syracuseStep 411565 = 154337) (by norm_num)
theorem B411601 : Blo 362758 411601 := bbase (se 2 (by rfl) ⟨154350, by rfl⟩ : syracuseStep 411601 = 308701) (by norm_num)
theorem B1230821 : Blo 362758 1230821 := bbase (se 4 (by rfl) ⟨115389, by rfl⟩ : syracuseStep 1230821 = 230779) (by norm_num)
theorem B411637 : Blo 362758 411637 := bbase (se 5 (by rfl) ⟨19295, by rfl⟩ : syracuseStep 411637 = 38591) (by norm_num)
theorem B411673 : Blo 362758 411673 := bbase (se 2 (by rfl) ⟨154377, by rfl⟩ : syracuseStep 411673 = 308755) (by norm_num)
theorem B411709 : Blo 362758 411709 := bbase (se 3 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 411709 = 154391) (by norm_num)
theorem B411745 : Blo 362758 411745 := bbase (se 2 (by rfl) ⟨154404, by rfl⟩ : syracuseStep 411745 = 308809) (by norm_num)
theorem B411781 : Blo 362758 411781 := bbase (se 4 (by rfl) ⟨38604, by rfl⟩ : syracuseStep 411781 = 77209) (by norm_num)
theorem B411817 : Blo 362758 411817 := bbase (se 2 (by rfl) ⟨154431, by rfl⟩ : syracuseStep 411817 = 308863) (by norm_num)
theorem B411853 : Blo 362758 411853 := bbase (se 3 (by rfl) ⟨77222, by rfl⟩ : syracuseStep 411853 = 154445) (by norm_num)
theorem B411889 : Blo 362758 411889 := bbase (se 2 (by rfl) ⟨154458, by rfl⟩ : syracuseStep 411889 = 308917) (by norm_num)
theorem B411925 : Blo 362758 411925 := bbase (se 6 (by rfl) ⟨9654, by rfl⟩ : syracuseStep 411925 = 19309) (by norm_num)
theorem B739613 : Blo 362758 739613 := bbase (se 3 (by rfl) ⟨138677, by rfl⟩ : syracuseStep 739613 = 277355) (by norm_num)
theorem B411961 : Blo 362758 411961 := bbase (se 2 (by rfl) ⟨154485, by rfl⟩ : syracuseStep 411961 = 308971) (by norm_num)
theorem B1853765 : Blo 362758 1853765 := bbase (se 4 (by rfl) ⟨173790, by rfl⟩ : syracuseStep 1853765 = 347581) (by norm_num)
theorem B411997 : Blo 362758 411997 := bbase (se 3 (by rfl) ⟨77249, by rfl⟩ : syracuseStep 411997 = 154499) (by norm_num)
theorem B412033 : Blo 362758 412033 := bbase (se 2 (by rfl) ⟨154512, by rfl⟩ : syracuseStep 412033 = 309025) (by norm_num)
theorem B1231253 : Blo 362758 1231253 := bbase (se 6 (by rfl) ⟨28857, by rfl⟩ : syracuseStep 1231253 = 57715) (by norm_num)
theorem B412069 : Blo 362758 412069 := bbase (se 4 (by rfl) ⟨38631, by rfl⟩ : syracuseStep 412069 = 77263) (by norm_num)
theorem B412105 : Blo 362758 412105 := bbase (se 2 (by rfl) ⟨154539, by rfl⟩ : syracuseStep 412105 = 309079) (by norm_num)
theorem B412141 : Blo 362758 412141 := bbase (se 3 (by rfl) ⟨77276, by rfl⟩ : syracuseStep 412141 = 154553) (by norm_num)
theorem B412177 : Blo 362758 412177 := bbase (se 2 (by rfl) ⟨154566, by rfl⟩ : syracuseStep 412177 = 309133) (by norm_num)
theorem B412213 : Blo 362758 412213 := bbase (se 5 (by rfl) ⟨19322, by rfl⟩ : syracuseStep 412213 = 38645) (by norm_num)
theorem B3099221 : Blo 362758 3099221 := bbase (se 8 (by rfl) ⟨18159, by rfl⟩ : syracuseStep 3099221 = 36319) (by norm_num)
theorem B412249 : Blo 362758 412249 := bbase (se 2 (by rfl) ⟨154593, by rfl⟩ : syracuseStep 412249 = 309187) (by norm_num)
theorem B412285 : Blo 362758 412285 := bbase (se 3 (by rfl) ⟨77303, by rfl⟩ : syracuseStep 412285 = 154607) (by norm_num)
theorem B412321 : Blo 362758 412321 := bbase (se 2 (by rfl) ⟨154620, by rfl⟩ : syracuseStep 412321 = 309241) (by norm_num)
theorem B412357 : Blo 362758 412357 := bbase (se 4 (by rfl) ⟨38658, by rfl⟩ : syracuseStep 412357 = 77317) (by norm_num)
theorem B412393 : Blo 362758 412393 := bbase (se 2 (by rfl) ⟨154647, by rfl⟩ : syracuseStep 412393 = 309295) (by norm_num)
theorem B412429 : Blo 362758 412429 := bbase (se 3 (by rfl) ⟨77330, by rfl⟩ : syracuseStep 412429 = 154661) (by norm_num)
theorem B412465 : Blo 362758 412465 := bbase (se 2 (by rfl) ⟨154674, by rfl⟩ : syracuseStep 412465 = 309349) (by norm_num)
theorem B1231685 : Blo 362758 1231685 := bbase (se 4 (by rfl) ⟨115470, by rfl⟩ : syracuseStep 1231685 = 230941) (by norm_num)
theorem B412501 : Blo 362758 412501 := bbase (se 9 (by rfl) ⟨1208, by rfl⟩ : syracuseStep 412501 = 2417) (by norm_num)
theorem B412537 : Blo 362758 412537 := bbase (se 2 (by rfl) ⟨154701, by rfl⟩ : syracuseStep 412537 = 309403) (by norm_num)
theorem B412573 : Blo 362758 412573 := bbase (se 3 (by rfl) ⟨77357, by rfl⟩ : syracuseStep 412573 = 154715) (by norm_num)
theorem B1166309 : Blo 362758 1166309 := bbase (se 4 (by rfl) ⟨109341, by rfl⟩ : syracuseStep 1166309 = 218683) (by norm_num)
theorem B740333 : Blo 362758 740333 := bbase (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) (by norm_num)
theorem B1035317 : Blo 362758 1035317 := bbase (se 5 (by rfl) ⟨48530, by rfl⟩ : syracuseStep 1035317 = 97061) (by norm_num)
theorem B1232117 : Blo 362758 1232117 := bbase (se 5 (by rfl) ⟨57755, by rfl⟩ : syracuseStep 1232117 = 115511) (by norm_num)
theorem B544157 : Blo 362758 544157 := bbase (se 3 (by rfl) ⟨102029, by rfl⟩ : syracuseStep 544157 = 204059) (by norm_num)
theorem B544181 : Blo 362758 544181 := bbase (se 5 (by rfl) ⟨25508, by rfl⟩ : syracuseStep 544181 = 51017) (by norm_num)
theorem B544205 : Blo 362758 544205 := bbase (se 3 (by rfl) ⟨102038, by rfl⟩ : syracuseStep 544205 = 204077) (by norm_num)
theorem B544229 : Blo 362758 544229 := bbase (se 4 (by rfl) ⟨51021, by rfl⟩ : syracuseStep 544229 = 102043) (by norm_num)
theorem B544253 : Blo 362758 544253 := bbase (se 3 (by rfl) ⟨102047, by rfl⟩ : syracuseStep 544253 = 204095) (by norm_num)
theorem B544277 : Blo 362758 544277 := bbase (se 6 (by rfl) ⟨12756, by rfl⟩ : syracuseStep 544277 = 25513) (by norm_num)
theorem B871973 : Blo 362758 871973 := bbase (se 4 (by rfl) ⟨81747, by rfl⟩ : syracuseStep 871973 = 163495) (by norm_num)
theorem B544301 : Blo 362758 544301 := bbase (se 3 (by rfl) ⟨102056, by rfl⟩ : syracuseStep 544301 = 204113) (by norm_num)
theorem B544325 : Blo 362758 544325 := bbase (se 4 (by rfl) ⟨51030, by rfl⟩ : syracuseStep 544325 = 102061) (by norm_num)
theorem B1855061 : Blo 362758 1855061 := bbase (se 8 (by rfl) ⟨10869, by rfl⟩ : syracuseStep 1855061 = 21739) (by norm_num)
theorem B544349 : Blo 362758 544349 := bbase (se 3 (by rfl) ⟨102065, by rfl⟩ : syracuseStep 544349 = 204131) (by norm_num)
theorem B544373 : Blo 362758 544373 := bbase (se 5 (by rfl) ⟨25517, by rfl⟩ : syracuseStep 544373 = 51035) (by norm_num)
theorem B544397 : Blo 362758 544397 := bbase (se 3 (by rfl) ⟨102074, by rfl⟩ : syracuseStep 544397 = 204149) (by norm_num)
theorem B2772629 : Blo 362758 2772629 := bbase (se 6 (by rfl) ⟨64983, by rfl⟩ : syracuseStep 2772629 = 129967) (by norm_num)
theorem B544421 : Blo 362758 544421 := bbase (se 4 (by rfl) ⟨51039, by rfl⟩ : syracuseStep 544421 = 102079) (by norm_num)
theorem B1232549 : Blo 362758 1232549 := bbase (se 4 (by rfl) ⟨115551, by rfl⟩ : syracuseStep 1232549 = 231103) (by norm_num)
theorem B544445 : Blo 362758 544445 := bbase (se 3 (by rfl) ⟨102083, by rfl⟩ : syracuseStep 544445 = 204167) (by norm_num)
theorem B544469 : Blo 362758 544469 := bbase (se 7 (by rfl) ⟨6380, by rfl⟩ : syracuseStep 544469 = 12761) (by norm_num)
theorem B872165 : Blo 362758 872165 := bbase (se 4 (by rfl) ⟨81765, by rfl⟩ : syracuseStep 872165 = 163531) (by norm_num)
theorem B544493 : Blo 362758 544493 := bbase (se 3 (by rfl) ⟨102092, by rfl⟩ : syracuseStep 544493 = 204185) (by norm_num)
theorem B544517 : Blo 362758 544517 := bbase (se 4 (by rfl) ⟨51048, by rfl⟩ : syracuseStep 544517 = 102097) (by norm_num)
theorem B544541 : Blo 362758 544541 := bbase (se 3 (by rfl) ⟨102101, by rfl⟩ : syracuseStep 544541 = 204203) (by norm_num)
theorem B544565 : Blo 362758 544565 := bbase (se 5 (by rfl) ⟨25526, by rfl⟩ : syracuseStep 544565 = 51053) (by norm_num)
theorem B544589 : Blo 362758 544589 := bbase (se 3 (by rfl) ⟨102110, by rfl⟩ : syracuseStep 544589 = 204221) (by norm_num)
theorem B544613 : Blo 362758 544613 := bbase (se 4 (by rfl) ⟨51057, by rfl⟩ : syracuseStep 544613 = 102115) (by norm_num)
theorem B544637 : Blo 362758 544637 := bbase (se 3 (by rfl) ⟨102119, by rfl⟩ : syracuseStep 544637 = 204239) (by norm_num)
theorem B544661 : Blo 362758 544661 := bbase (se 6 (by rfl) ⟨12765, by rfl⟩ : syracuseStep 544661 = 25531) (by norm_num)
theorem B544685 : Blo 362758 544685 := bbase (se 3 (by rfl) ⟨102128, by rfl⟩ : syracuseStep 544685 = 204257) (by norm_num)
theorem B544709 : Blo 362758 544709 := bbase (se 4 (by rfl) ⟨51066, by rfl⟩ : syracuseStep 544709 = 102133) (by norm_num)
theorem B544733 : Blo 362758 544733 := bbase (se 3 (by rfl) ⟨102137, by rfl⟩ : syracuseStep 544733 = 204275) (by norm_num)
theorem B544757 : Blo 362758 544757 := bbase (se 5 (by rfl) ⟨25535, by rfl⟩ : syracuseStep 544757 = 51071) (by norm_num)
theorem B544781 : Blo 362758 544781 := bbase (se 3 (by rfl) ⟨102146, by rfl⟩ : syracuseStep 544781 = 204293) (by norm_num)
theorem B544805 : Blo 362758 544805 := bbase (se 4 (by rfl) ⟨51075, by rfl⟩ : syracuseStep 544805 = 102151) (by norm_num)
theorem B544829 : Blo 362758 544829 := bbase (se 3 (by rfl) ⟨102155, by rfl⟩ : syracuseStep 544829 = 204311) (by norm_num)
theorem B544853 : Blo 362758 544853 := bbase (se 8 (by rfl) ⟨3192, by rfl⟩ : syracuseStep 544853 = 6385) (by norm_num)
theorem B1232981 : Blo 362758 1232981 := bbase (se 8 (by rfl) ⟨7224, by rfl⟩ : syracuseStep 1232981 = 14449) (by norm_num)
theorem B544877 : Blo 362758 544877 := bbase (se 3 (by rfl) ⟨102164, by rfl⟩ : syracuseStep 544877 = 204329) (by norm_num)
theorem B544901 : Blo 362758 544901 := bbase (se 4 (by rfl) ⟨51084, by rfl⟩ : syracuseStep 544901 = 102169) (by norm_num)
theorem B544925 : Blo 362758 544925 := bbase (se 3 (by rfl) ⟨102173, by rfl⟩ : syracuseStep 544925 = 204347) (by norm_num)
theorem B544949 : Blo 362758 544949 := bbase (se 5 (by rfl) ⟨25544, by rfl⟩ : syracuseStep 544949 = 51089) (by norm_num)
theorem B544973 : Blo 362758 544973 := bbase (se 3 (by rfl) ⟨102182, by rfl⟩ : syracuseStep 544973 = 204365) (by norm_num)
theorem B544997 : Blo 362758 544997 := bbase (se 4 (by rfl) ⟨51093, by rfl⟩ : syracuseStep 544997 = 102187) (by norm_num)
theorem B545021 : Blo 362758 545021 := bbase (se 3 (by rfl) ⟨102191, by rfl⟩ : syracuseStep 545021 = 204383) (by norm_num)
theorem B545045 : Blo 362758 545045 := bbase (se 6 (by rfl) ⟨12774, by rfl⟩ : syracuseStep 545045 = 25549) (by norm_num)
theorem B1167653 : Blo 362758 1167653 := bbase (se 4 (by rfl) ⟨109467, by rfl⟩ : syracuseStep 1167653 = 218935) (by norm_num)
theorem B1757477 : Blo 362758 1757477 := bbase (se 4 (by rfl) ⟨164763, by rfl⟩ : syracuseStep 1757477 = 329527) (by norm_num)
theorem B545069 : Blo 362758 545069 := bbase (se 3 (by rfl) ⟨102200, by rfl⟩ : syracuseStep 545069 = 204401) (by norm_num)
theorem B545093 : Blo 362758 545093 := bbase (se 4 (by rfl) ⟨51102, by rfl⟩ : syracuseStep 545093 = 102205) (by norm_num)
theorem B545117 : Blo 362758 545117 := bbase (se 3 (by rfl) ⟨102209, by rfl⟩ : syracuseStep 545117 = 204419) (by norm_num)
theorem B545141 : Blo 362758 545141 := bbase (se 5 (by rfl) ⟨25553, by rfl⟩ : syracuseStep 545141 = 51107) (by norm_num)
theorem B414085 : Blo 362758 414085 := bbase (se 4 (by rfl) ⟨38820, by rfl⟩ : syracuseStep 414085 = 77641) (by norm_num)
theorem B545165 : Blo 362758 545165 := bbase (se 3 (by rfl) ⟨102218, by rfl⟩ : syracuseStep 545165 = 204437) (by norm_num)
theorem B545189 : Blo 362758 545189 := bbase (se 4 (by rfl) ⟨51111, by rfl⟩ : syracuseStep 545189 = 102223) (by norm_num)
theorem B545213 : Blo 362758 545213 := bbase (se 3 (by rfl) ⟨102227, by rfl⟩ : syracuseStep 545213 = 204455) (by norm_num)
theorem B545237 : Blo 362758 545237 := bbase (se 7 (by rfl) ⟨6389, by rfl⟩ : syracuseStep 545237 = 12779) (by norm_num)
theorem B545261 : Blo 362758 545261 := bbase (se 3 (by rfl) ⟨102236, by rfl⟩ : syracuseStep 545261 = 204473) (by norm_num)
theorem B545285 : Blo 362758 545285 := bbase (se 4 (by rfl) ⟨51120, by rfl⟩ : syracuseStep 545285 = 102241) (by norm_num)
theorem B1233413 : Blo 362758 1233413 := bbase (se 4 (by rfl) ⟨115632, by rfl⟩ : syracuseStep 1233413 = 231265) (by norm_num)
theorem B545309 : Blo 362758 545309 := bbase (se 3 (by rfl) ⟨102245, by rfl⟩ : syracuseStep 545309 = 204491) (by norm_num)
theorem B545333 : Blo 362758 545333 := bbase (se 5 (by rfl) ⟨25562, by rfl⟩ : syracuseStep 545333 = 51125) (by norm_num)
theorem B545357 : Blo 362758 545357 := bbase (se 3 (by rfl) ⟨102254, by rfl⟩ : syracuseStep 545357 = 204509) (by norm_num)
theorem B545381 : Blo 362758 545381 := bbase (se 4 (by rfl) ⟨51129, by rfl⟩ : syracuseStep 545381 = 102259) (by norm_num)
theorem B1036901 : Blo 362758 1036901 := bbase (se 4 (by rfl) ⟨97209, by rfl⟩ : syracuseStep 1036901 = 194419) (by norm_num)
theorem B545405 : Blo 362758 545405 := bbase (se 3 (by rfl) ⟨102263, by rfl⟩ : syracuseStep 545405 = 204527) (by norm_num)
theorem B545429 : Blo 362758 545429 := bbase (se 6 (by rfl) ⟨12783, by rfl⟩ : syracuseStep 545429 = 25567) (by norm_num)
theorem B545453 : Blo 362758 545453 := bbase (se 3 (by rfl) ⟨102272, by rfl⟩ : syracuseStep 545453 = 204545) (by norm_num)
theorem B545477 : Blo 362758 545477 := bbase (se 4 (by rfl) ⟨51138, by rfl⟩ : syracuseStep 545477 = 102277) (by norm_num)
theorem B545501 : Blo 362758 545501 := bbase (se 3 (by rfl) ⟨102281, by rfl⟩ : syracuseStep 545501 = 204563) (by norm_num)
theorem B545525 : Blo 362758 545525 := bbase (se 5 (by rfl) ⟨25571, by rfl⟩ : syracuseStep 545525 = 51143) (by norm_num)
theorem B545549 : Blo 362758 545549 := bbase (se 3 (by rfl) ⟨102290, by rfl⟩ : syracuseStep 545549 = 204581) (by norm_num)
theorem B545573 : Blo 362758 545573 := bbase (se 4 (by rfl) ⟨51147, by rfl⟩ : syracuseStep 545573 = 102295) (by norm_num)
theorem B545597 : Blo 362758 545597 := bbase (se 3 (by rfl) ⟨102299, by rfl⟩ : syracuseStep 545597 = 204599) (by norm_num)
theorem B545621 : Blo 362758 545621 := bbase (se 9 (by rfl) ⟨1598, by rfl⟩ : syracuseStep 545621 = 3197) (by norm_num)
theorem B1856357 : Blo 362758 1856357 := bbase (se 4 (by rfl) ⟨174033, by rfl⟩ : syracuseStep 1856357 = 348067) (by norm_num)
theorem B545645 : Blo 362758 545645 := bbase (se 3 (by rfl) ⟨102308, by rfl⟩ : syracuseStep 545645 = 204617) (by norm_num)
theorem B545669 : Blo 362758 545669 := bbase (se 4 (by rfl) ⟨51156, by rfl⟩ : syracuseStep 545669 = 102313) (by norm_num)
theorem B545693 : Blo 362758 545693 := bbase (se 3 (by rfl) ⟨102317, by rfl⟩ : syracuseStep 545693 = 204635) (by norm_num)
theorem B545717 : Blo 362758 545717 := bbase (se 5 (by rfl) ⟨25580, by rfl⟩ : syracuseStep 545717 = 51161) (by norm_num)
theorem B1233845 : Blo 362758 1233845 := bbase (se 5 (by rfl) ⟨57836, by rfl⟩ : syracuseStep 1233845 = 115673) (by norm_num)
theorem B545741 : Blo 362758 545741 := bbase (se 3 (by rfl) ⟨102326, by rfl⟩ : syracuseStep 545741 = 204653) (by norm_num)
theorem B545765 : Blo 362758 545765 := bbase (se 4 (by rfl) ⟨51165, by rfl⟩ : syracuseStep 545765 = 102331) (by norm_num)
theorem B545789 : Blo 362758 545789 := bbase (se 3 (by rfl) ⟨102335, by rfl⟩ : syracuseStep 545789 = 204671) (by norm_num)
theorem B414733 : Blo 362758 414733 := bbase (se 3 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 414733 = 155525) (by norm_num)
theorem B545813 : Blo 362758 545813 := bbase (se 6 (by rfl) ⟨12792, by rfl⟩ : syracuseStep 545813 = 25585) (by norm_num)
theorem B939037 : Blo 362758 939037 := bbase (se 3 (by rfl) ⟨176069, by rfl⟩ : syracuseStep 939037 = 352139) (by norm_num)
theorem B545837 : Blo 362758 545837 := bbase (se 3 (by rfl) ⟨102344, by rfl⟩ : syracuseStep 545837 = 204689) (by norm_num)
theorem B545861 : Blo 362758 545861 := bbase (se 4 (by rfl) ⟨51174, by rfl⟩ : syracuseStep 545861 = 102349) (by norm_num)
theorem B545885 : Blo 362758 545885 := bbase (se 3 (by rfl) ⟨102353, by rfl⟩ : syracuseStep 545885 = 204707) (by norm_num)
theorem B545909 : Blo 362758 545909 := bbase (se 5 (by rfl) ⟨25589, by rfl⟩ : syracuseStep 545909 = 51179) (by norm_num)
theorem B545933 : Blo 362758 545933 := bbase (se 3 (by rfl) ⟨102362, by rfl⟩ : syracuseStep 545933 = 204725) (by norm_num)
theorem B545957 : Blo 362758 545957 := bbase (se 4 (by rfl) ⟨51183, by rfl⟩ : syracuseStep 545957 = 102367) (by norm_num)
theorem B545981 : Blo 362758 545981 := bbase (se 3 (by rfl) ⟨102371, by rfl⟩ : syracuseStep 545981 = 204743) (by norm_num)
theorem B546005 : Blo 362758 546005 := bbase (se 7 (by rfl) ⟨6398, by rfl⟩ : syracuseStep 546005 = 12797) (by norm_num)
theorem B742621 : Blo 362758 742621 := bbase (se 3 (by rfl) ⟨139241, by rfl⟩ : syracuseStep 742621 = 278483) (by norm_num)
theorem B546029 : Blo 362758 546029 := bbase (se 3 (by rfl) ⟨102380, by rfl⟩ : syracuseStep 546029 = 204761) (by norm_num)
theorem B546053 : Blo 362758 546053 := bbase (se 4 (by rfl) ⟨51192, by rfl⟩ : syracuseStep 546053 = 102385) (by norm_num)
theorem B1037573 : Blo 362758 1037573 := bbase (se 4 (by rfl) ⟨97272, by rfl⟩ : syracuseStep 1037573 = 194545) (by norm_num)
theorem B546077 : Blo 362758 546077 := bbase (se 3 (by rfl) ⟨102389, by rfl⟩ : syracuseStep 546077 = 204779) (by norm_num)
theorem B546101 : Blo 362758 546101 := bbase (se 5 (by rfl) ⟨25598, by rfl⟩ : syracuseStep 546101 = 51197) (by norm_num)
theorem B546125 : Blo 362758 546125 := bbase (se 3 (by rfl) ⟨102398, by rfl⟩ : syracuseStep 546125 = 204797) (by norm_num)
theorem B546149 : Blo 362758 546149 := bbase (se 4 (by rfl) ⟨51201, by rfl⟩ : syracuseStep 546149 = 102403) (by norm_num)
theorem B1234277 : Blo 362758 1234277 := bbase (se 4 (by rfl) ⟨115713, by rfl⟩ : syracuseStep 1234277 = 231427) (by norm_num)
theorem B546173 : Blo 362758 546173 := bbase (se 3 (by rfl) ⟨102407, by rfl⟩ : syracuseStep 546173 = 204815) (by norm_num)
theorem B546197 : Blo 362758 546197 := bbase (se 6 (by rfl) ⟨12801, by rfl⟩ : syracuseStep 546197 = 25603) (by norm_num)
theorem B546221 : Blo 362758 546221 := bbase (se 3 (by rfl) ⟨102416, by rfl⟩ : syracuseStep 546221 = 204833) (by norm_num)
theorem B546245 : Blo 362758 546245 := bbase (se 4 (by rfl) ⟨51210, by rfl⟩ : syracuseStep 546245 = 102421) (by norm_num)
theorem B546269 : Blo 362758 546269 := bbase (se 3 (by rfl) ⟨102425, by rfl⟩ : syracuseStep 546269 = 204851) (by norm_num)
theorem B546293 : Blo 362758 546293 := bbase (se 5 (by rfl) ⟨25607, by rfl⟩ : syracuseStep 546293 = 51215) (by norm_num)
theorem B546317 : Blo 362758 546317 := bbase (se 3 (by rfl) ⟨102434, by rfl⟩ : syracuseStep 546317 = 204869) (by norm_num)
theorem B415253 : Blo 362758 415253 := bbase (se 6 (by rfl) ⟨9732, by rfl⟩ : syracuseStep 415253 = 19465) (by norm_num)
theorem B546341 : Blo 362758 546341 := bbase (se 4 (by rfl) ⟨51219, by rfl⟩ : syracuseStep 546341 = 102439) (by norm_num)
theorem B546365 : Blo 362758 546365 := bbase (se 3 (by rfl) ⟨102443, by rfl⟩ : syracuseStep 546365 = 204887) (by norm_num)
theorem B546389 : Blo 362758 546389 := bbase (se 8 (by rfl) ⟨3201, by rfl⟩ : syracuseStep 546389 = 6403) (by norm_num)
theorem B546413 : Blo 362758 546413 := bbase (se 3 (by rfl) ⟨102452, by rfl⟩ : syracuseStep 546413 = 204905) (by norm_num)
theorem B546437 : Blo 362758 546437 := bbase (se 4 (by rfl) ⟨51228, by rfl⟩ : syracuseStep 546437 = 102457) (by norm_num)
theorem B546461 : Blo 362758 546461 := bbase (se 3 (by rfl) ⟨102461, by rfl⟩ : syracuseStep 546461 = 204923) (by norm_num)
theorem B874165 : Blo 362758 874165 := bbase (se 5 (by rfl) ⟨40976, by rfl⟩ : syracuseStep 874165 = 81953) (by norm_num)
theorem B546485 : Blo 362758 546485 := bbase (se 5 (by rfl) ⟨25616, by rfl⟩ : syracuseStep 546485 = 51233) (by norm_num)
theorem B1038005 : Blo 362758 1038005 := bbase (se 5 (by rfl) ⟨48656, by rfl⟩ : syracuseStep 1038005 = 97313) (by norm_num)
theorem B546509 : Blo 362758 546509 := bbase (se 3 (by rfl) ⟨102470, by rfl⟩ : syracuseStep 546509 = 204941) (by norm_num)
theorem B546533 : Blo 362758 546533 := bbase (se 4 (by rfl) ⟨51237, by rfl⟩ : syracuseStep 546533 = 102475) (by norm_num)
theorem B546557 : Blo 362758 546557 := bbase (se 3 (by rfl) ⟨102479, by rfl⟩ : syracuseStep 546557 = 204959) (by norm_num)
theorem B546581 : Blo 362758 546581 := bbase (se 6 (by rfl) ⟨12810, by rfl⟩ : syracuseStep 546581 = 25621) (by norm_num)
theorem B1234709 : Blo 362758 1234709 := bbase (se 6 (by rfl) ⟨28938, by rfl⟩ : syracuseStep 1234709 = 57877) (by norm_num)
theorem B546605 : Blo 362758 546605 := bbase (se 3 (by rfl) ⟨102488, by rfl⟩ : syracuseStep 546605 = 204977) (by norm_num)
theorem B612157 : Blo 362758 612157 := bbase (se 3 (by rfl) ⟨114779, by rfl⟩ : syracuseStep 612157 = 229559) (by norm_num)
theorem B546629 : Blo 362758 546629 := bbase (se 4 (by rfl) ⟨51246, by rfl⟩ : syracuseStep 546629 = 102493) (by norm_num)
theorem B546653 : Blo 362758 546653 := bbase (se 3 (by rfl) ⟨102497, by rfl⟩ : syracuseStep 546653 = 204995) (by norm_num)
theorem B546677 : Blo 362758 546677 := bbase (se 5 (by rfl) ⟨25625, by rfl⟩ : syracuseStep 546677 = 51251) (by norm_num)
theorem B546701 : Blo 362758 546701 := bbase (se 3 (by rfl) ⟨102506, by rfl⟩ : syracuseStep 546701 = 205013) (by norm_num)
theorem B612245 : Blo 362758 612245 := bbase (se 6 (by rfl) ⟨14349, by rfl⟩ : syracuseStep 612245 = 28699) (by norm_num)
theorem B546725 : Blo 362758 546725 := bbase (se 4 (by rfl) ⟨51255, by rfl⟩ : syracuseStep 546725 = 102511) (by norm_num)
theorem B546749 : Blo 362758 546749 := bbase (se 3 (by rfl) ⟨102515, by rfl⟩ : syracuseStep 546749 = 205031) (by norm_num)
theorem B1103813 : Blo 362758 1103813 := bbase (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) (by norm_num)
theorem B546773 : Blo 362758 546773 := bbase (se 7 (by rfl) ⟨6407, by rfl⟩ : syracuseStep 546773 = 12815) (by norm_num)
theorem B1562597 : Blo 362758 1562597 := bbase (se 4 (by rfl) ⟨146493, by rfl⟩ : syracuseStep 1562597 = 292987) (by norm_num)
theorem B546797 : Blo 362758 546797 := bbase (se 3 (by rfl) ⟨102524, by rfl⟩ : syracuseStep 546797 = 205049) (by norm_num)
theorem B546821 : Blo 362758 546821 := bbase (se 4 (by rfl) ⟨51264, by rfl⟩ : syracuseStep 546821 = 102529) (by norm_num)
theorem B612373 : Blo 362758 612373 := bbase (se 6 (by rfl) ⟨14352, by rfl⟩ : syracuseStep 612373 = 28705) (by norm_num)
theorem B546845 : Blo 362758 546845 := bbase (se 3 (by rfl) ⟨102533, by rfl⟩ : syracuseStep 546845 = 205067) (by norm_num)
theorem B546869 : Blo 362758 546869 := bbase (se 5 (by rfl) ⟨25634, by rfl⟩ : syracuseStep 546869 = 51269) (by norm_num)
theorem B546893 : Blo 362758 546893 := bbase (se 3 (by rfl) ⟨102542, by rfl⟩ : syracuseStep 546893 = 205085) (by norm_num)
theorem B546917 : Blo 362758 546917 := bbase (se 4 (by rfl) ⟨51273, by rfl⟩ : syracuseStep 546917 = 102547) (by norm_num)
theorem B612461 : Blo 362758 612461 := bbase (se 3 (by rfl) ⟨114836, by rfl⟩ : syracuseStep 612461 = 229673) (by norm_num)
theorem B776317 : Blo 362758 776317 := bbase (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) (by norm_num)
theorem B546941 : Blo 362758 546941 := bbase (se 3 (by rfl) ⟨102551, by rfl⟩ : syracuseStep 546941 = 205103) (by norm_num)
theorem B546965 : Blo 362758 546965 := bbase (se 6 (by rfl) ⟨12819, by rfl⟩ : syracuseStep 546965 = 25639) (by norm_num)
theorem B546989 : Blo 362758 546989 := bbase (se 3 (by rfl) ⟨102560, by rfl⟩ : syracuseStep 546989 = 205121) (by norm_num)
theorem B547013 : Blo 362758 547013 := bbase (se 4 (by rfl) ⟨51282, by rfl⟩ : syracuseStep 547013 = 102565) (by norm_num)
theorem B1235141 : Blo 362758 1235141 := bbase (se 4 (by rfl) ⟨115794, by rfl⟩ : syracuseStep 1235141 = 231589) (by norm_num)
theorem B547037 : Blo 362758 547037 := bbase (se 3 (by rfl) ⟨102569, by rfl⟩ : syracuseStep 547037 = 205139) (by norm_num)
theorem B612589 : Blo 362758 612589 := bbase (se 3 (by rfl) ⟨114860, by rfl⟩ : syracuseStep 612589 = 229721) (by norm_num)
theorem B874741 : Blo 362758 874741 := bbase (se 5 (by rfl) ⟨41003, by rfl⟩ : syracuseStep 874741 = 82007) (by norm_num)
theorem B547061 : Blo 362758 547061 := bbase (se 5 (by rfl) ⟨25643, by rfl⟩ : syracuseStep 547061 = 51287) (by norm_num)
theorem B1169653 : Blo 362758 1169653 := bbase (se 5 (by rfl) ⟨54827, by rfl⟩ : syracuseStep 1169653 = 109655) (by norm_num)
theorem B1562885 : Blo 362758 1562885 := bbase (se 4 (by rfl) ⟨146520, by rfl⟩ : syracuseStep 1562885 = 293041) (by norm_num)
theorem B547085 : Blo 362758 547085 := bbase (se 3 (by rfl) ⟨102578, by rfl⟩ : syracuseStep 547085 = 205157) (by norm_num)
theorem B547109 : Blo 362758 547109 := bbase (se 4 (by rfl) ⟨51291, by rfl⟩ : syracuseStep 547109 = 102583) (by norm_num)
theorem B547133 : Blo 362758 547133 := bbase (se 3 (by rfl) ⟨102587, by rfl⟩ : syracuseStep 547133 = 205175) (by norm_num)
theorem B612677 : Blo 362758 612677 := bbase (se 4 (by rfl) ⟨57438, by rfl⟩ : syracuseStep 612677 = 114877) (by norm_num)
theorem B547157 : Blo 362758 547157 := bbase (se 10 (by rfl) ⟨801, by rfl⟩ : syracuseStep 547157 = 1603) (by norm_num)
theorem B547181 : Blo 362758 547181 := bbase (se 3 (by rfl) ⟨102596, by rfl⟩ : syracuseStep 547181 = 205193) (by norm_num)
theorem B547205 : Blo 362758 547205 := bbase (se 4 (by rfl) ⟨51300, by rfl⟩ : syracuseStep 547205 = 102601) (by norm_num)
theorem B547229 : Blo 362758 547229 := bbase (se 3 (by rfl) ⟨102605, by rfl⟩ : syracuseStep 547229 = 205211) (by norm_num)
theorem B1038757 : Blo 362758 1038757 := bbase (se 4 (by rfl) ⟨97383, by rfl⟩ : syracuseStep 1038757 = 194767) (by norm_num)
theorem B547253 : Blo 362758 547253 := bbase (se 5 (by rfl) ⟨25652, by rfl⟩ : syracuseStep 547253 = 51305) (by norm_num)
theorem B612805 : Blo 362758 612805 := bbase (se 4 (by rfl) ⟨57450, by rfl⟩ : syracuseStep 612805 = 114901) (by norm_num)
theorem B547277 : Blo 362758 547277 := bbase (se 3 (by rfl) ⟨102614, by rfl⟩ : syracuseStep 547277 = 205229) (by norm_num)
theorem B547301 : Blo 362758 547301 := bbase (se 4 (by rfl) ⟨51309, by rfl⟩ : syracuseStep 547301 = 102619) (by norm_num)
theorem B2349557 : Blo 362758 2349557 := bbase (se 5 (by rfl) ⟨110135, by rfl⟩ : syracuseStep 2349557 = 220271) (by norm_num)
theorem B547325 : Blo 362758 547325 := bbase (se 3 (by rfl) ⟨102623, by rfl⟩ : syracuseStep 547325 = 205247) (by norm_num)
theorem B547349 : Blo 362758 547349 := bbase (se 6 (by rfl) ⟨12828, by rfl⟩ : syracuseStep 547349 = 25657) (by norm_num)
theorem B612893 : Blo 362758 612893 := bbase (se 3 (by rfl) ⟨114917, by rfl⟩ : syracuseStep 612893 = 229835) (by norm_num)
theorem B547373 : Blo 362758 547373 := bbase (se 3 (by rfl) ⟨102632, by rfl⟩ : syracuseStep 547373 = 205265) (by norm_num)
theorem B875069 : Blo 362758 875069 := bbase (se 3 (by rfl) ⟨164075, by rfl⟩ : syracuseStep 875069 = 328151) (by norm_num)
theorem B547397 : Blo 362758 547397 := bbase (se 4 (by rfl) ⟨51318, by rfl⟩ : syracuseStep 547397 = 102637) (by norm_num)
theorem B547421 : Blo 362758 547421 := bbase (se 3 (by rfl) ⟨102641, by rfl⟩ : syracuseStep 547421 = 205283) (by norm_num)
theorem B875125 : Blo 362758 875125 := bbase (se 5 (by rfl) ⟨41021, by rfl⟩ : syracuseStep 875125 = 82043) (by norm_num)
theorem B547445 : Blo 362758 547445 := bbase (se 5 (by rfl) ⟨25661, by rfl⟩ : syracuseStep 547445 = 51323) (by norm_num)
theorem B1235573 : Blo 362758 1235573 := bbase (se 5 (by rfl) ⟨57917, by rfl⟩ : syracuseStep 1235573 = 115835) (by norm_num)
theorem B547469 : Blo 362758 547469 := bbase (se 3 (by rfl) ⟨102650, by rfl⟩ : syracuseStep 547469 = 205301) (by norm_num)
theorem B7002773 : Blo 362758 7002773 := bbase (se 6 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 7002773 = 328255) (by norm_num)
theorem B613021 : Blo 362758 613021 := bbase (se 3 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 613021 = 229883) (by norm_num)
theorem B547493 : Blo 362758 547493 := bbase (se 4 (by rfl) ⟨51327, by rfl⟩ : syracuseStep 547493 = 102655) (by norm_num)
theorem B547517 : Blo 362758 547517 := bbase (se 3 (by rfl) ⟨102659, by rfl⟩ : syracuseStep 547517 = 205319) (by norm_num)
theorem B547541 : Blo 362758 547541 := bbase (se 7 (by rfl) ⟨6416, by rfl⟩ : syracuseStep 547541 = 12833) (by norm_num)
theorem B2251477 : Blo 362758 2251477 := bbase (se 7 (by rfl) ⟨26384, by rfl⟩ : syracuseStep 2251477 = 52769) (by norm_num)
theorem B547565 : Blo 362758 547565 := bbase (se 3 (by rfl) ⟨102668, by rfl⟩ : syracuseStep 547565 = 205337) (by norm_num)
theorem B613109 : Blo 362758 613109 := bbase (se 5 (by rfl) ⟨28739, by rfl⟩ : syracuseStep 613109 = 57479) (by norm_num)
theorem B547589 : Blo 362758 547589 := bbase (se 4 (by rfl) ⟨51336, by rfl⟩ : syracuseStep 547589 = 102673) (by norm_num)
theorem B547613 : Blo 362758 547613 := bbase (se 3 (by rfl) ⟨102677, by rfl⟩ : syracuseStep 547613 = 205355) (by norm_num)
theorem B547637 : Blo 362758 547637 := bbase (se 5 (by rfl) ⟨25670, by rfl⟩ : syracuseStep 547637 = 51341) (by norm_num)
theorem B547661 : Blo 362758 547661 := bbase (se 3 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 547661 = 205373) (by norm_num)
theorem B4447061 : Blo 362758 4447061 := bbase (se 9 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 4447061 = 26057) (by norm_num)
theorem B2087765 : Blo 362758 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B875357 : Blo 362758 875357 := bbase (se 3 (by rfl) ⟨164129, by rfl⟩ : syracuseStep 875357 = 328259) (by norm_num)
theorem B547685 : Blo 362758 547685 := bbase (se 4 (by rfl) ⟨51345, by rfl⟩ : syracuseStep 547685 = 102691) (by norm_num)
theorem B416621 : Blo 362758 416621 := bbase (se 3 (by rfl) ⟨78116, by rfl⟩ : syracuseStep 416621 = 156233) (by norm_num)
theorem B613237 : Blo 362758 613237 := bbase (se 5 (by rfl) ⟨28745, by rfl⟩ : syracuseStep 613237 = 57491) (by norm_num)
theorem B547709 : Blo 362758 547709 := bbase (se 3 (by rfl) ⟨102695, by rfl⟩ : syracuseStep 547709 = 205391) (by norm_num)
theorem B547733 : Blo 362758 547733 := bbase (se 6 (by rfl) ⟨12837, by rfl⟩ : syracuseStep 547733 = 25675) (by norm_num)
theorem B547757 : Blo 362758 547757 := bbase (se 3 (by rfl) ⟨102704, by rfl⟩ : syracuseStep 547757 = 205409) (by norm_num)
theorem B547781 : Blo 362758 547781 := bbase (se 4 (by rfl) ⟨51354, by rfl⟩ : syracuseStep 547781 = 102709) (by norm_num)
theorem B613325 : Blo 362758 613325 := bbase (se 3 (by rfl) ⟨114998, by rfl⟩ : syracuseStep 613325 = 229997) (by norm_num)
theorem B547805 : Blo 362758 547805 := bbase (se 3 (by rfl) ⟨102713, by rfl⟩ : syracuseStep 547805 = 205427) (by norm_num)
theorem B777205 : Blo 362758 777205 := bbase (se 5 (by rfl) ⟨36431, by rfl⟩ : syracuseStep 777205 = 72863) (by norm_num)
theorem B547829 : Blo 362758 547829 := bbase (se 5 (by rfl) ⟨25679, by rfl⟩ : syracuseStep 547829 = 51359) (by norm_num)
theorem B1563637 : Blo 362758 1563637 := bbase (se 5 (by rfl) ⟨73295, by rfl⟩ : syracuseStep 1563637 = 146591) (by norm_num)
theorem B547853 : Blo 362758 547853 := bbase (se 3 (by rfl) ⟨102722, by rfl⟩ : syracuseStep 547853 = 205445) (by norm_num)
theorem B875549 : Blo 362758 875549 := bbase (se 3 (by rfl) ⟨164165, by rfl⟩ : syracuseStep 875549 = 328331) (by norm_num)
theorem B547877 : Blo 362758 547877 := bbase (se 4 (by rfl) ⟨51363, by rfl⟩ : syracuseStep 547877 = 102727) (by norm_num)
theorem B1236005 : Blo 362758 1236005 := bbase (se 4 (by rfl) ⟨115875, by rfl⟩ : syracuseStep 1236005 = 231751) (by norm_num)
theorem B547901 : Blo 362758 547901 := bbase (se 3 (by rfl) ⟨102731, by rfl⟩ : syracuseStep 547901 = 205463) (by norm_num)
theorem B613453 : Blo 362758 613453 := bbase (se 3 (by rfl) ⟨115022, by rfl⟩ : syracuseStep 613453 = 230045) (by norm_num)
theorem B547925 : Blo 362758 547925 := bbase (se 8 (by rfl) ⟨3210, by rfl⟩ : syracuseStep 547925 = 6421) (by norm_num)
theorem B547949 : Blo 362758 547949 := bbase (se 3 (by rfl) ⟨102740, by rfl⟩ : syracuseStep 547949 = 205481) (by norm_num)
theorem B547973 : Blo 362758 547973 := bbase (se 4 (by rfl) ⟨51372, by rfl⟩ : syracuseStep 547973 = 102745) (by norm_num)
theorem B547997 : Blo 362758 547997 := bbase (se 3 (by rfl) ⟨102749, by rfl⟩ : syracuseStep 547997 = 205499) (by norm_num)
theorem B613541 : Blo 362758 613541 := bbase (se 4 (by rfl) ⟨57519, by rfl⟩ : syracuseStep 613541 = 115039) (by norm_num)
theorem B548021 : Blo 362758 548021 := bbase (se 5 (by rfl) ⟨25688, by rfl⟩ : syracuseStep 548021 = 51377) (by norm_num)
theorem B548045 : Blo 362758 548045 := bbase (se 3 (by rfl) ⟨102758, by rfl⟩ : syracuseStep 548045 = 205517) (by norm_num)
theorem B548069 : Blo 362758 548069 := bbase (se 4 (by rfl) ⟨51381, by rfl⟩ : syracuseStep 548069 = 102763) (by norm_num)
theorem B548093 : Blo 362758 548093 := bbase (se 3 (by rfl) ⟨102767, by rfl⟩ : syracuseStep 548093 = 205535) (by norm_num)
theorem B548117 : Blo 362758 548117 := bbase (se 6 (by rfl) ⟨12846, by rfl⟩ : syracuseStep 548117 = 25693) (by norm_num)
theorem B613669 : Blo 362758 613669 := bbase (se 4 (by rfl) ⟨57531, by rfl⟩ : syracuseStep 613669 = 115063) (by norm_num)
theorem B548141 : Blo 362758 548141 := bbase (se 3 (by rfl) ⟨102776, by rfl⟩ : syracuseStep 548141 = 205553) (by norm_num)
theorem B548165 : Blo 362758 548165 := bbase (se 4 (by rfl) ⟨51390, by rfl⟩ : syracuseStep 548165 = 102781) (by norm_num)
theorem B57105749 : Blo 362758 57105749 := bbase (se 11 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 57105749 = 83651) (by norm_num)
theorem B548189 : Blo 362758 548189 := bbase (se 3 (by rfl) ⟨102785, by rfl⟩ : syracuseStep 548189 = 205571) (by norm_num)
theorem B548213 : Blo 362758 548213 := bbase (se 5 (by rfl) ⟨25697, by rfl⟩ : syracuseStep 548213 = 51395) (by norm_num)
theorem B613757 : Blo 362758 613757 := bbase (se 3 (by rfl) ⟨115079, by rfl⟩ : syracuseStep 613757 = 230159) (by norm_num)
theorem B548237 : Blo 362758 548237 := bbase (se 3 (by rfl) ⟨102794, by rfl⟩ : syracuseStep 548237 = 205589) (by norm_num)
theorem B548261 : Blo 362758 548261 := bbase (se 4 (by rfl) ⟨51399, by rfl⟩ : syracuseStep 548261 = 102799) (by norm_num)
theorem B548285 : Blo 362758 548285 := bbase (se 3 (by rfl) ⟨102803, by rfl⟩ : syracuseStep 548285 = 205607) (by norm_num)
theorem B548309 : Blo 362758 548309 := bbase (se 7 (by rfl) ⟨6425, by rfl⟩ : syracuseStep 548309 = 12851) (by norm_num)
theorem B1236437 : Blo 362758 1236437 := bbase (se 7 (by rfl) ⟨14489, by rfl⟩ : syracuseStep 1236437 = 28979) (by norm_num)
theorem B777701 : Blo 362758 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B548333 : Blo 362758 548333 := bbase (se 3 (by rfl) ⟨102812, by rfl⟩ : syracuseStep 548333 = 205625) (by norm_num)
theorem B613885 : Blo 362758 613885 := bbase (se 3 (by rfl) ⟨115103, by rfl⟩ : syracuseStep 613885 = 230207) (by norm_num)
theorem B548357 : Blo 362758 548357 := bbase (se 4 (by rfl) ⟨51408, by rfl⟩ : syracuseStep 548357 = 102817) (by norm_num)
theorem B548381 : Blo 362758 548381 := bbase (se 3 (by rfl) ⟨102821, by rfl⟩ : syracuseStep 548381 = 205643) (by norm_num)
theorem B548405 : Blo 362758 548405 := bbase (se 5 (by rfl) ⟨25706, by rfl⟩ : syracuseStep 548405 = 51413) (by norm_num)
theorem B548429 : Blo 362758 548429 := bbase (se 3 (by rfl) ⟨102830, by rfl⟩ : syracuseStep 548429 = 205661) (by norm_num)
theorem B613973 : Blo 362758 613973 := bbase (se 8 (by rfl) ⟨3597, by rfl⟩ : syracuseStep 613973 = 7195) (by norm_num)
theorem B548453 : Blo 362758 548453 := bbase (se 4 (by rfl) ⟨51417, by rfl⟩ : syracuseStep 548453 = 102835) (by norm_num)
theorem B548477 : Blo 362758 548477 := bbase (se 3 (by rfl) ⟨102839, by rfl⟩ : syracuseStep 548477 = 205679) (by norm_num)
theorem B548501 : Blo 362758 548501 := bbase (se 6 (by rfl) ⟨12855, by rfl⟩ : syracuseStep 548501 = 25711) (by norm_num)
theorem B548525 : Blo 362758 548525 := bbase (se 3 (by rfl) ⟨102848, by rfl⟩ : syracuseStep 548525 = 205697) (by norm_num)
theorem B548549 : Blo 362758 548549 := bbase (se 4 (by rfl) ⟨51426, by rfl⟩ : syracuseStep 548549 = 102853) (by norm_num)
theorem B614101 : Blo 362758 614101 := bbase (se 7 (by rfl) ⟨7196, by rfl⟩ : syracuseStep 614101 = 14393) (by norm_num)
theorem B1564373 : Blo 362758 1564373 := bbase (se 7 (by rfl) ⟨18332, by rfl⟩ : syracuseStep 1564373 = 36665) (by norm_num)
theorem B548573 : Blo 362758 548573 := bbase (se 3 (by rfl) ⟨102857, by rfl⟩ : syracuseStep 548573 = 205715) (by norm_num)
theorem B548597 : Blo 362758 548597 := bbase (se 5 (by rfl) ⟨25715, by rfl⟩ : syracuseStep 548597 = 51431) (by norm_num)
theorem B548621 : Blo 362758 548621 := bbase (se 3 (by rfl) ⟨102866, by rfl⟩ : syracuseStep 548621 = 205733) (by norm_num)
theorem B548645 : Blo 362758 548645 := bbase (se 4 (by rfl) ⟨51435, by rfl⟩ : syracuseStep 548645 = 102871) (by norm_num)
theorem B614189 : Blo 362758 614189 := bbase (se 3 (by rfl) ⟨115160, by rfl⟩ : syracuseStep 614189 = 230321) (by norm_num)
theorem B548669 : Blo 362758 548669 := bbase (se 3 (by rfl) ⟨102875, by rfl⟩ : syracuseStep 548669 = 205751) (by norm_num)
theorem B417605 : Blo 362758 417605 := bbase (se 4 (by rfl) ⟨39150, by rfl⟩ : syracuseStep 417605 = 78301) (by norm_num)
theorem B548693 : Blo 362758 548693 := bbase (se 9 (by rfl) ⟨1607, by rfl⟩ : syracuseStep 548693 = 3215) (by norm_num)
theorem B548717 : Blo 362758 548717 := bbase (se 3 (by rfl) ⟨102884, by rfl⟩ : syracuseStep 548717 = 205769) (by norm_num)
theorem B548741 : Blo 362758 548741 := bbase (se 4 (by rfl) ⟨51444, by rfl⟩ : syracuseStep 548741 = 102889) (by norm_num)
theorem B1236869 : Blo 362758 1236869 := bbase (se 4 (by rfl) ⟨115956, by rfl⟩ : syracuseStep 1236869 = 231913) (by norm_num)
theorem B548765 : Blo 362758 548765 := bbase (se 3 (by rfl) ⟨102893, by rfl⟩ : syracuseStep 548765 = 205787) (by norm_num)
theorem B1105829 : Blo 362758 1105829 := bbase (se 4 (by rfl) ⟨103671, by rfl⟩ : syracuseStep 1105829 = 207343) (by norm_num)
theorem B614317 : Blo 362758 614317 := bbase (se 3 (by rfl) ⟨115184, by rfl⟩ : syracuseStep 614317 = 230369) (by norm_num)
theorem B548789 : Blo 362758 548789 := bbase (se 5 (by rfl) ⟨25724, by rfl⟩ : syracuseStep 548789 = 51449) (by norm_num)
theorem B548813 : Blo 362758 548813 := bbase (se 3 (by rfl) ⟨102902, by rfl⟩ : syracuseStep 548813 = 205805) (by norm_num)
theorem B876509 : Blo 362758 876509 := bbase (se 3 (by rfl) ⟨164345, by rfl⟩ : syracuseStep 876509 = 328691) (by norm_num)
theorem B548837 : Blo 362758 548837 := bbase (se 4 (by rfl) ⟨51453, by rfl⟩ : syracuseStep 548837 = 102907) (by norm_num)
theorem B548861 : Blo 362758 548861 := bbase (se 3 (by rfl) ⟨102911, by rfl⟩ : syracuseStep 548861 = 205823) (by norm_num)
theorem B614405 : Blo 362758 614405 := bbase (se 4 (by rfl) ⟨57600, by rfl⟩ : syracuseStep 614405 = 115201) (by norm_num)
theorem B548885 : Blo 362758 548885 := bbase (se 6 (by rfl) ⟨12864, by rfl⟩ : syracuseStep 548885 = 25729) (by norm_num)
theorem B548909 : Blo 362758 548909 := bbase (se 3 (by rfl) ⟨102920, by rfl⟩ : syracuseStep 548909 = 205841) (by norm_num)
theorem B548933 : Blo 362758 548933 := bbase (se 4 (by rfl) ⟨51462, by rfl⟩ : syracuseStep 548933 = 102925) (by norm_num)
theorem B581725 : Blo 362758 581725 := bbase (se 3 (by rfl) ⟨109073, by rfl⟩ : syracuseStep 581725 = 218147) (by norm_num)
theorem B548957 : Blo 362758 548957 := bbase (se 3 (by rfl) ⟨102929, by rfl⟩ : syracuseStep 548957 = 205859) (by norm_num)
theorem B548981 : Blo 362758 548981 := bbase (se 5 (by rfl) ⟨25733, by rfl⟩ : syracuseStep 548981 = 51467) (by norm_num)
theorem B614533 : Blo 362758 614533 := bbase (se 4 (by rfl) ⟨57612, by rfl⟩ : syracuseStep 614533 = 115225) (by norm_num)
theorem B549005 : Blo 362758 549005 := bbase (se 3 (by rfl) ⟨102938, by rfl⟩ : syracuseStep 549005 = 205877) (by norm_num)
theorem B549029 : Blo 362758 549029 := bbase (se 4 (by rfl) ⟨51471, by rfl⟩ : syracuseStep 549029 = 102943) (by norm_num)
theorem B549053 : Blo 362758 549053 := bbase (se 3 (by rfl) ⟨102947, by rfl⟩ : syracuseStep 549053 = 205895) (by norm_num)
theorem B549077 : Blo 362758 549077 := bbase (se 7 (by rfl) ⟨6434, by rfl⟩ : syracuseStep 549077 = 12869) (by norm_num)
theorem B614621 : Blo 362758 614621 := bbase (se 3 (by rfl) ⟨115241, by rfl⟩ : syracuseStep 614621 = 230483) (by norm_num)
theorem B549101 : Blo 362758 549101 := bbase (se 3 (by rfl) ⟨102956, by rfl⟩ : syracuseStep 549101 = 205913) (by norm_num)
theorem B549125 : Blo 362758 549125 := bbase (se 4 (by rfl) ⟨51480, by rfl⟩ : syracuseStep 549125 = 102961) (by norm_num)
theorem B549149 : Blo 362758 549149 := bbase (se 3 (by rfl) ⟨102965, by rfl⟩ : syracuseStep 549149 = 205931) (by norm_num)
theorem B549173 : Blo 362758 549173 := bbase (se 5 (by rfl) ⟨25742, by rfl⟩ : syracuseStep 549173 = 51485) (by norm_num)
theorem B1237301 : Blo 362758 1237301 := bbase (se 5 (by rfl) ⟨57998, by rfl⟩ : syracuseStep 1237301 = 115997) (by norm_num)
theorem B778565 : Blo 362758 778565 := bbase (se 4 (by rfl) ⟨72990, by rfl⟩ : syracuseStep 778565 = 145981) (by norm_num)
theorem B418117 : Blo 362758 418117 := bbase (se 4 (by rfl) ⟨39198, by rfl⟩ : syracuseStep 418117 = 78397) (by norm_num)
theorem B549197 : Blo 362758 549197 := bbase (se 3 (by rfl) ⟨102974, by rfl⟩ : syracuseStep 549197 = 205949) (by norm_num)
theorem B614749 : Blo 362758 614749 := bbase (se 3 (by rfl) ⟨115265, by rfl⟩ : syracuseStep 614749 = 230531) (by norm_num)
theorem B549221 : Blo 362758 549221 := bbase (se 4 (by rfl) ⟨51489, by rfl⟩ : syracuseStep 549221 = 102979) (by norm_num)
theorem B549245 : Blo 362758 549245 := bbase (se 3 (by rfl) ⟨102983, by rfl⟩ : syracuseStep 549245 = 205967) (by norm_num)
theorem B549269 : Blo 362758 549269 := bbase (se 6 (by rfl) ⟨12873, by rfl⟩ : syracuseStep 549269 = 25747) (by norm_num)
theorem B549293 : Blo 362758 549293 := bbase (se 3 (by rfl) ⟨102992, by rfl⟩ : syracuseStep 549293 = 205985) (by norm_num)
theorem B614837 : Blo 362758 614837 := bbase (se 5 (by rfl) ⟨28820, by rfl⟩ : syracuseStep 614837 = 57641) (by norm_num)
theorem B549317 : Blo 362758 549317 := bbase (se 4 (by rfl) ⟨51498, by rfl⟩ : syracuseStep 549317 = 102997) (by norm_num)
theorem B516565 : Blo 362758 516565 := bbase (se 7 (by rfl) ⟨6053, by rfl⟩ : syracuseStep 516565 = 12107) (by norm_num)
theorem B778709 : Blo 362758 778709 := bbase (se 7 (by rfl) ⟨9125, by rfl⟩ : syracuseStep 778709 = 18251) (by norm_num)
theorem B549341 : Blo 362758 549341 := bbase (se 3 (by rfl) ⟨103001, by rfl⟩ : syracuseStep 549341 = 206003) (by norm_num)
theorem B549365 : Blo 362758 549365 := bbase (se 5 (by rfl) ⟨25751, by rfl⟩ : syracuseStep 549365 = 51503) (by norm_num)
theorem B582149 : Blo 362758 582149 := bbase (se 4 (by rfl) ⟨54576, by rfl⟩ : syracuseStep 582149 = 109153) (by norm_num)
theorem B549389 : Blo 362758 549389 := bbase (se 3 (by rfl) ⟨103010, by rfl⟩ : syracuseStep 549389 = 206021) (by norm_num)
theorem B549413 : Blo 362758 549413 := bbase (se 4 (by rfl) ⟨51507, by rfl⟩ : syracuseStep 549413 = 103015) (by norm_num)
theorem B614965 : Blo 362758 614965 := bbase (se 5 (by rfl) ⟨28826, by rfl⟩ : syracuseStep 614965 = 57653) (by norm_num)
theorem B549437 : Blo 362758 549437 := bbase (se 3 (by rfl) ⟨103019, by rfl⟩ : syracuseStep 549437 = 206039) (by norm_num)
theorem B549461 : Blo 362758 549461 := bbase (se 8 (by rfl) ⟨3219, by rfl⟩ : syracuseStep 549461 = 6439) (by norm_num)
theorem B451165 : Blo 362758 451165 := bbase (se 3 (by rfl) ⟨84593, by rfl⟩ : syracuseStep 451165 = 169187) (by norm_num)
theorem B549485 : Blo 362758 549485 := bbase (se 3 (by rfl) ⟨103028, by rfl⟩ : syracuseStep 549485 = 206057) (by norm_num)
theorem B549509 : Blo 362758 549509 := bbase (se 4 (by rfl) ⟨51516, by rfl⟩ : syracuseStep 549509 = 103033) (by norm_num)
theorem B615053 : Blo 362758 615053 := bbase (se 3 (by rfl) ⟨115322, by rfl⟩ : syracuseStep 615053 = 230645) (by norm_num)
theorem B549533 : Blo 362758 549533 := bbase (se 3 (by rfl) ⟨103037, by rfl⟩ : syracuseStep 549533 = 206075) (by norm_num)
theorem B549557 : Blo 362758 549557 := bbase (se 5 (by rfl) ⟨25760, by rfl⟩ : syracuseStep 549557 = 51521) (by norm_num)
theorem B549581 : Blo 362758 549581 := bbase (se 3 (by rfl) ⟨103046, by rfl⟩ : syracuseStep 549581 = 206093) (by norm_num)
theorem B549605 : Blo 362758 549605 := bbase (se 4 (by rfl) ⟨51525, by rfl⟩ : syracuseStep 549605 = 103051) (by norm_num)
theorem B1237733 : Blo 362758 1237733 := bbase (se 4 (by rfl) ⟨116037, by rfl⟩ : syracuseStep 1237733 = 232075) (by norm_num)
theorem B549629 : Blo 362758 549629 := bbase (se 3 (by rfl) ⟨103055, by rfl⟩ : syracuseStep 549629 = 206111) (by norm_num)
theorem B615181 : Blo 362758 615181 := bbase (se 3 (by rfl) ⟨115346, by rfl⟩ : syracuseStep 615181 = 230693) (by norm_num)
theorem B549653 : Blo 362758 549653 := bbase (se 6 (by rfl) ⟨12882, by rfl⟩ : syracuseStep 549653 = 25765) (by norm_num)
theorem B582437 : Blo 362758 582437 := bbase (se 4 (by rfl) ⟨54603, by rfl⟩ : syracuseStep 582437 = 109207) (by norm_num)
theorem B549677 : Blo 362758 549677 := bbase (se 3 (by rfl) ⟨103064, by rfl⟩ : syracuseStep 549677 = 206129) (by norm_num)
theorem B549701 : Blo 362758 549701 := bbase (se 4 (by rfl) ⟨51534, by rfl⟩ : syracuseStep 549701 = 103069) (by norm_num)
theorem B549725 : Blo 362758 549725 := bbase (se 3 (by rfl) ⟨103073, by rfl⟩ : syracuseStep 549725 = 206147) (by norm_num)
theorem B615269 : Blo 362758 615269 := bbase (se 4 (by rfl) ⟨57681, by rfl⟩ : syracuseStep 615269 = 115363) (by norm_num)
theorem B549749 : Blo 362758 549749 := bbase (se 5 (by rfl) ⟨25769, by rfl⟩ : syracuseStep 549749 = 51539) (by norm_num)
theorem B549773 : Blo 362758 549773 := bbase (se 3 (by rfl) ⟨103082, by rfl⟩ : syracuseStep 549773 = 206165) (by norm_num)
theorem B549797 : Blo 362758 549797 := bbase (se 4 (by rfl) ⟨51543, by rfl⟩ : syracuseStep 549797 = 103087) (by norm_num)
theorem B549821 : Blo 362758 549821 := bbase (se 3 (by rfl) ⟨103091, by rfl⟩ : syracuseStep 549821 = 206183) (by norm_num)
theorem B549845 : Blo 362758 549845 := bbase (se 7 (by rfl) ⟨6443, by rfl⟩ : syracuseStep 549845 = 12887) (by norm_num)
theorem B615397 : Blo 362758 615397 := bbase (se 4 (by rfl) ⟨57693, by rfl⟩ : syracuseStep 615397 = 115387) (by norm_num)
theorem B549869 : Blo 362758 549869 := bbase (se 3 (by rfl) ⟨103100, by rfl⟩ : syracuseStep 549869 = 206201) (by norm_num)
theorem B582661 : Blo 362758 582661 := bbase (se 4 (by rfl) ⟨54624, by rfl⟩ : syracuseStep 582661 = 109249) (by norm_num)
theorem B549893 : Blo 362758 549893 := bbase (se 4 (by rfl) ⟨51552, by rfl⟩ : syracuseStep 549893 = 103105) (by norm_num)
theorem B549917 : Blo 362758 549917 := bbase (se 3 (by rfl) ⟨103109, by rfl⟩ : syracuseStep 549917 = 206219) (by norm_num)
theorem B549941 : Blo 362758 549941 := bbase (se 5 (by rfl) ⟨25778, by rfl⟩ : syracuseStep 549941 = 51557) (by norm_num)
theorem B615485 : Blo 362758 615485 := bbase (se 3 (by rfl) ⟨115403, by rfl⟩ : syracuseStep 615485 = 230807) (by norm_num)
theorem B549965 : Blo 362758 549965 := bbase (se 3 (by rfl) ⟨103118, by rfl⟩ : syracuseStep 549965 = 206237) (by norm_num)
theorem B549989 : Blo 362758 549989 := bbase (se 4 (by rfl) ⟨51561, by rfl⟩ : syracuseStep 549989 = 103123) (by norm_num)
theorem B550013 : Blo 362758 550013 := bbase (se 3 (by rfl) ⟨103127, by rfl⟩ : syracuseStep 550013 = 206255) (by norm_num)
theorem B550037 : Blo 362758 550037 := bbase (se 6 (by rfl) ⟨12891, by rfl⟩ : syracuseStep 550037 = 25783) (by norm_num)
theorem B550061 : Blo 362758 550061 := bbase (se 3 (by rfl) ⟨103136, by rfl⟩ : syracuseStep 550061 = 206273) (by norm_num)
theorem B615613 : Blo 362758 615613 := bbase (se 3 (by rfl) ⟨115427, by rfl⟩ : syracuseStep 615613 = 230855) (by norm_num)
theorem B779453 : Blo 362758 779453 := bbase (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) (by norm_num)
theorem B1041605 : Blo 362758 1041605 := bbase (se 4 (by rfl) ⟨97650, by rfl⟩ : syracuseStep 1041605 = 195301) (by norm_num)
theorem B1172677 : Blo 362758 1172677 := bbase (se 4 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 1172677 = 219877) (by norm_num)
theorem B550085 : Blo 362758 550085 := bbase (se 4 (by rfl) ⟨51570, by rfl⟩ : syracuseStep 550085 = 103141) (by norm_num)
theorem B550109 : Blo 362758 550109 := bbase (se 3 (by rfl) ⟨103145, by rfl⟩ : syracuseStep 550109 = 206291) (by norm_num)
theorem B517357 : Blo 362758 517357 := bbase (se 3 (by rfl) ⟨97004, by rfl⟩ : syracuseStep 517357 = 194009) (by norm_num)
theorem B550133 : Blo 362758 550133 := bbase (se 5 (by rfl) ⟨25787, by rfl⟩ : syracuseStep 550133 = 51575) (by norm_num)
theorem B615701 : Blo 362758 615701 := bbase (se 6 (by rfl) ⟨14430, by rfl⟩ : syracuseStep 615701 = 28861) (by norm_num)
theorem B615829 : Blo 362758 615829 := bbase (se 6 (by rfl) ⟨14433, by rfl⟩ : syracuseStep 615829 = 28867) (by norm_num)
theorem B615917 : Blo 362758 615917 := bbase (se 3 (by rfl) ⟨115484, by rfl⟩ : syracuseStep 615917 = 230969) (by norm_num)
theorem B517693 : Blo 362758 517693 := bbase (se 3 (by rfl) ⟨97067, by rfl⟩ : syracuseStep 517693 = 194135) (by norm_num)
theorem B616045 : Blo 362758 616045 := bbase (se 3 (by rfl) ⟨115508, by rfl⟩ : syracuseStep 616045 = 231017) (by norm_num)
theorem B1926805 : Blo 362758 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B616133 : Blo 362758 616133 := bbase (se 4 (by rfl) ⟨57762, by rfl⟩ : syracuseStep 616133 = 115525) (by norm_num)
theorem B517909 : Blo 362758 517909 := bbase (se 6 (by rfl) ⟨12138, by rfl⟩ : syracuseStep 517909 = 24277) (by norm_num)
theorem B1402645 : Blo 362758 1402645 := bbase (se 6 (by rfl) ⟨32874, by rfl⟩ : syracuseStep 1402645 = 65749) (by norm_num)
theorem B616261 : Blo 362758 616261 := bbase (se 4 (by rfl) ⟨57774, by rfl⟩ : syracuseStep 616261 = 115549) (by norm_num)
theorem B616349 : Blo 362758 616349 := bbase (se 3 (by rfl) ⟨115565, by rfl⟩ : syracuseStep 616349 = 231131) (by norm_num)
theorem B780205 : Blo 362758 780205 := bbase (se 3 (by rfl) ⟨146288, by rfl⟩ : syracuseStep 780205 = 292577) (by norm_num)
theorem B7858133 : Blo 362758 7858133 := bbase (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) (by norm_num)
theorem B616477 : Blo 362758 616477 := bbase (se 3 (by rfl) ⟨115589, by rfl⟩ : syracuseStep 616477 = 231179) (by norm_num)
theorem B780349 : Blo 362758 780349 := bbase (se 3 (by rfl) ⟨146315, by rfl⟩ : syracuseStep 780349 = 292631) (by norm_num)
theorem B583789 : Blo 362758 583789 := bbase (se 3 (by rfl) ⟨109460, by rfl⟩ : syracuseStep 583789 = 218921) (by norm_num)
theorem B616565 : Blo 362758 616565 := bbase (se 5 (by rfl) ⟨28901, by rfl⟩ : syracuseStep 616565 = 57803) (by norm_num)
theorem B518285 : Blo 362758 518285 := bbase (se 3 (by rfl) ⟨97178, by rfl⟩ : syracuseStep 518285 = 194357) (by norm_num)
theorem B1861861 : Blo 362758 1861861 := bbase (se 4 (by rfl) ⟨174549, by rfl⟩ : syracuseStep 1861861 = 349099) (by norm_num)
theorem B616693 : Blo 362758 616693 := bbase (se 5 (by rfl) ⟨28907, by rfl⟩ : syracuseStep 616693 = 57815) (by norm_num)
theorem B616781 : Blo 362758 616781 := bbase (se 3 (by rfl) ⟨115646, by rfl⟩ : syracuseStep 616781 = 231293) (by norm_num)
theorem B1042789 : Blo 362758 1042789 := bbase (se 4 (by rfl) ⟨97761, by rfl⟩ : syracuseStep 1042789 = 195523) (by norm_num)
theorem B1010053 : Blo 362758 1010053 := bbase (se 4 (by rfl) ⟨94692, by rfl⟩ : syracuseStep 1010053 = 189385) (by norm_num)
theorem B387509 : Blo 362758 387509 := bbase (se 5 (by rfl) ⟨18164, by rfl⟩ : syracuseStep 387509 = 36329) (by norm_num)
theorem B780725 : Blo 362758 780725 := bbase (se 5 (by rfl) ⟨36596, by rfl⟩ : syracuseStep 780725 = 73193) (by norm_num)
theorem B616909 : Blo 362758 616909 := bbase (se 3 (by rfl) ⟨115670, by rfl⟩ : syracuseStep 616909 = 231341) (by norm_num)
theorem B1042949 : Blo 362758 1042949 := bbase (se 4 (by rfl) ⟨97776, by rfl⟩ : syracuseStep 1042949 = 195553) (by norm_num)
theorem B616997 : Blo 362758 616997 := bbase (se 4 (by rfl) ⟨57843, by rfl⟩ : syracuseStep 616997 = 115687) (by norm_num)
theorem B584237 : Blo 362758 584237 := bbase (se 3 (by rfl) ⟨109544, by rfl⟩ : syracuseStep 584237 = 219089) (by norm_num)
theorem B617125 : Blo 362758 617125 := bbase (se 4 (by rfl) ⟨57855, by rfl⟩ : syracuseStep 617125 = 115711) (by norm_num)
theorem B387757 : Blo 362758 387757 := bbase (se 3 (by rfl) ⟨72704, by rfl⟩ : syracuseStep 387757 = 145409) (by norm_num)
theorem B879277 : Blo 362758 879277 := bbase (se 3 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 879277 = 329729) (by norm_num)
theorem B1043189 : Blo 362758 1043189 := bbase (se 5 (by rfl) ⟨48899, by rfl⟩ : syracuseStep 1043189 = 97799) (by norm_num)
theorem B617213 : Blo 362758 617213 := bbase (se 3 (by rfl) ⟨115727, by rfl⟩ : syracuseStep 617213 = 231455) (by norm_num)
theorem B781093 : Blo 362758 781093 := bbase (se 4 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 781093 = 146455) (by norm_num)
theorem B617341 : Blo 362758 617341 := bbase (se 3 (by rfl) ⟨115751, by rfl⟩ : syracuseStep 617341 = 231503) (by norm_num)
theorem B1043381 : Blo 362758 1043381 := bbase (se 5 (by rfl) ⟨48908, by rfl⟩ : syracuseStep 1043381 = 97817) (by norm_num)
theorem B617429 : Blo 362758 617429 := bbase (se 7 (by rfl) ⟨7235, by rfl⟩ : syracuseStep 617429 = 14471) (by norm_num)
theorem B551941 : Blo 362758 551941 := bbase (se 4 (by rfl) ⟨51744, by rfl⟩ : syracuseStep 551941 = 103489) (by norm_num)
theorem B879653 : Blo 362758 879653 := bbase (se 4 (by rfl) ⟨82467, by rfl⟩ : syracuseStep 879653 = 164935) (by norm_num)
theorem B617557 : Blo 362758 617557 := bbase (se 8 (by rfl) ⟨3618, by rfl⟩ : syracuseStep 617557 = 7237) (by norm_num)
theorem B388189 : Blo 362758 388189 := bbase (se 3 (by rfl) ⟨72785, by rfl⟩ : syracuseStep 388189 = 145571) (by norm_num)
theorem B388261 : Blo 362758 388261 := bbase (se 4 (by rfl) ⟨36399, by rfl⟩ : syracuseStep 388261 = 72799) (by norm_num)
theorem B617645 : Blo 362758 617645 := bbase (se 3 (by rfl) ⟨115808, by rfl⟩ : syracuseStep 617645 = 231617) (by norm_num)
theorem B1109189 : Blo 362758 1109189 := bbase (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) (by norm_num)
theorem B1666261 : Blo 362758 1666261 := bbase (se 7 (by rfl) ⟨19526, by rfl⟩ : syracuseStep 1666261 = 39053) (by norm_num)
theorem B421085 : Blo 362758 421085 := bbase (se 3 (by rfl) ⟨78953, by rfl⟩ : syracuseStep 421085 = 157907) (by norm_num)
theorem B2780405 : Blo 362758 2780405 := bbase (se 5 (by rfl) ⟨130331, by rfl⟩ : syracuseStep 2780405 = 260663) (by norm_num)
theorem B1109285 : Blo 362758 1109285 := bbase (se 4 (by rfl) ⟨103995, by rfl⟩ : syracuseStep 1109285 = 207991) (by norm_num)
theorem B617773 : Blo 362758 617773 := bbase (se 3 (by rfl) ⟨115832, by rfl⟩ : syracuseStep 617773 = 231665) (by norm_num)
theorem B4156757 : Blo 362758 4156757 := bbase (se 11 (by rfl) ⟨3044, by rfl⟩ : syracuseStep 4156757 = 6089) (by norm_num)
theorem B617861 : Blo 362758 617861 := bbase (se 4 (by rfl) ⟨57924, by rfl⟩ : syracuseStep 617861 = 115849) (by norm_num)
theorem B880085 : Blo 362758 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B617989 : Blo 362758 617989 := bbase (se 4 (by rfl) ⟨57936, by rfl⟩ : syracuseStep 617989 = 115873) (by norm_num)
theorem B388633 : Blo 362758 388633 := bbase (se 2 (by rfl) ⟨145737, by rfl⟩ : syracuseStep 388633 = 291475) (by norm_num)
theorem B519709 : Blo 362758 519709 := bbase (se 3 (by rfl) ⟨97445, by rfl⟩ : syracuseStep 519709 = 194891) (by norm_num)
theorem B421465 : Blo 362758 421465 := bbase (se 2 (by rfl) ⟨158049, by rfl⟩ : syracuseStep 421465 = 316099) (by norm_num)
theorem B618077 : Blo 362758 618077 := bbase (se 3 (by rfl) ⟨115889, by rfl⟩ : syracuseStep 618077 = 231779) (by norm_num)
theorem B618205 : Blo 362758 618205 := bbase (se 3 (by rfl) ⟨115913, by rfl⟩ : syracuseStep 618205 = 231827) (by norm_num)
theorem B1863461 : Blo 362758 1863461 := bbase (se 4 (by rfl) ⟨174699, by rfl⟩ : syracuseStep 1863461 = 349399) (by norm_num)
theorem B618293 : Blo 362758 618293 := bbase (se 5 (by rfl) ⟨28982, by rfl⟩ : syracuseStep 618293 = 57965) (by norm_num)
theorem B389009 : Blo 362758 389009 := bbase (se 2 (by rfl) ⟨145878, by rfl⟩ : syracuseStep 389009 = 291757) (by norm_num)
theorem B1044373 : Blo 362758 1044373 := bbase (se 6 (by rfl) ⟨24477, by rfl⟩ : syracuseStep 1044373 = 48955) (by norm_num)
theorem B618421 : Blo 362758 618421 := bbase (se 5 (by rfl) ⟨28988, by rfl⟩ : syracuseStep 618421 = 57977) (by norm_num)
theorem B1142741 : Blo 362758 1142741 := bbase (se 7 (by rfl) ⟨13391, by rfl⟩ : syracuseStep 1142741 = 26783) (by norm_num)
theorem B389081 : Blo 362758 389081 := bbase (se 2 (by rfl) ⟨145905, by rfl⟩ : syracuseStep 389081 = 291811) (by norm_num)
theorem B618509 : Blo 362758 618509 := bbase (se 3 (by rfl) ⟨115970, by rfl⟩ : syracuseStep 618509 = 231941) (by norm_num)
theorem B585749 : Blo 362758 585749 := bbase (se 6 (by rfl) ⟨13728, by rfl⟩ : syracuseStep 585749 = 27457) (by norm_num)
theorem B880661 : Blo 362758 880661 := bbase (se 6 (by rfl) ⟨20640, by rfl⟩ : syracuseStep 880661 = 41281) (by norm_num)
theorem B520301 : Blo 362758 520301 := bbase (se 3 (by rfl) ⟨97556, by rfl⟩ : syracuseStep 520301 = 195113) (by norm_num)
theorem B618637 : Blo 362758 618637 := bbase (se 3 (by rfl) ⟨115994, by rfl⟩ : syracuseStep 618637 = 231989) (by norm_num)
theorem B553109 : Blo 362758 553109 := bbase (se 6 (by rfl) ⟨12963, by rfl⟩ : syracuseStep 553109 = 25927) (by norm_num)
theorem B389269 : Blo 362758 389269 := bbase (se 6 (by rfl) ⟨9123, by rfl⟩ : syracuseStep 389269 = 18247) (by norm_num)
theorem B585877 : Blo 362758 585877 := bbase (se 6 (by rfl) ⟨13731, by rfl⟩ : syracuseStep 585877 = 27463) (by norm_num)
theorem B520381 : Blo 362758 520381 := bbase (se 3 (by rfl) ⟨97571, by rfl⟩ : syracuseStep 520381 = 195143) (by norm_num)
theorem B618725 : Blo 362758 618725 := bbase (se 4 (by rfl) ⟨58005, by rfl⟩ : syracuseStep 618725 = 116011) (by norm_num)
theorem B782597 : Blo 362758 782597 := bbase (se 4 (by rfl) ⟨73368, by rfl⟩ : syracuseStep 782597 = 146737) (by norm_num)
theorem B520501 : Blo 362758 520501 := bbase (se 5 (by rfl) ⟨24398, by rfl⟩ : syracuseStep 520501 = 48797) (by norm_num)
theorem B389453 : Blo 362758 389453 := bbase (se 3 (by rfl) ⟨73022, by rfl⟩ : syracuseStep 389453 = 146045) (by norm_num)
theorem B618853 : Blo 362758 618853 := bbase (se 4 (by rfl) ⟨58017, by rfl⟩ : syracuseStep 618853 = 116035) (by norm_num)
theorem B520597 : Blo 362758 520597 := bbase (se 6 (by rfl) ⟨12201, by rfl⟩ : syracuseStep 520597 = 24403) (by norm_num)
theorem B782741 : Blo 362758 782741 := bbase (se 6 (by rfl) ⟨18345, by rfl⟩ : syracuseStep 782741 = 36691) (by norm_num)
theorem B488141 : Blo 362758 488141 := bbase (se 3 (by rfl) ⟨91526, by rfl⟩ : syracuseStep 488141 = 183053) (by norm_num)
theorem B783101 : Blo 362758 783101 := bbase (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) (by norm_num)
theorem B553853 : Blo 362758 553853 := bbase (se 3 (by rfl) ⟨103847, by rfl⟩ : syracuseStep 553853 = 207695) (by norm_num)
theorem B521093 : Blo 362758 521093 := bbase (se 4 (by rfl) ⟨48852, by rfl⟩ : syracuseStep 521093 = 97705) (by norm_num)
theorem B390205 : Blo 362758 390205 := bbase (se 3 (by rfl) ⟨73163, by rfl⟩ : syracuseStep 390205 = 146327) (by norm_num)
theorem B816245 : Blo 362758 816245 := bbase (se 5 (by rfl) ⟨38261, by rfl⟩ : syracuseStep 816245 = 76523) (by norm_num)
theorem B390277 : Blo 362758 390277 := bbase (se 4 (by rfl) ⟨36588, by rfl⟩ : syracuseStep 390277 = 73177) (by norm_num)
theorem B2225333 : Blo 362758 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B816317 : Blo 362758 816317 := bbase (se 3 (by rfl) ⟨153059, by rfl⟩ : syracuseStep 816317 = 306119) (by norm_num)
theorem B816389 : Blo 362758 816389 := bbase (se 4 (by rfl) ⟨76536, by rfl⟩ : syracuseStep 816389 = 153073) (by norm_num)
theorem B390457 : Blo 362758 390457 := bbase (se 2 (by rfl) ⟨146421, by rfl⟩ : syracuseStep 390457 = 292843) (by norm_num)
theorem B816461 : Blo 362758 816461 := bbase (se 3 (by rfl) ⟨153086, by rfl⟩ : syracuseStep 816461 = 306173) (by norm_num)
theorem B816533 : Blo 362758 816533 := bbase (se 6 (by rfl) ⟨19137, by rfl⟩ : syracuseStep 816533 = 38275) (by norm_num)
theorem B521645 : Blo 362758 521645 := bbase (se 3 (by rfl) ⟨97808, by rfl⟩ : syracuseStep 521645 = 195617) (by norm_num)
theorem B816605 : Blo 362758 816605 := bbase (se 3 (by rfl) ⟨153113, by rfl⟩ : syracuseStep 816605 = 306227) (by norm_num)
theorem B587261 : Blo 362758 587261 := bbase (se 3 (by rfl) ⟨110111, by rfl⟩ : syracuseStep 587261 = 220223) (by norm_num)
theorem B816677 : Blo 362758 816677 := bbase (se 4 (by rfl) ⟨76563, by rfl⟩ : syracuseStep 816677 = 153127) (by norm_num)
theorem B816749 : Blo 362758 816749 := bbase (se 3 (by rfl) ⟨153140, by rfl⟩ : syracuseStep 816749 = 306281) (by norm_num)
theorem B816821 : Blo 362758 816821 := bbase (se 5 (by rfl) ⟨38288, by rfl⟩ : syracuseStep 816821 = 76577) (by norm_num)
theorem B390901 : Blo 362758 390901 := bbase (se 5 (by rfl) ⟨18323, by rfl⟩ : syracuseStep 390901 = 36647) (by norm_num)
theorem B816893 : Blo 362758 816893 := bbase (se 3 (by rfl) ⟨153167, by rfl⟩ : syracuseStep 816893 = 306335) (by norm_num)
theorem B816965 : Blo 362758 816965 := bbase (se 4 (by rfl) ⟨76590, by rfl⟩ : syracuseStep 816965 = 153181) (by norm_num)
theorem B1242965 : Blo 362758 1242965 := bbase (se 9 (by rfl) ⟨3641, by rfl⟩ : syracuseStep 1242965 = 7283) (by norm_num)
theorem B391025 : Blo 362758 391025 := bbase (se 2 (by rfl) ⟨146634, by rfl⟩ : syracuseStep 391025 = 293269) (by norm_num)
theorem B817037 : Blo 362758 817037 := bbase (se 3 (by rfl) ⟨153194, by rfl⟩ : syracuseStep 817037 = 306389) (by norm_num)
theorem B817109 : Blo 362758 817109 := bbase (se 7 (by rfl) ⟨9575, by rfl⟩ : syracuseStep 817109 = 19151) (by norm_num)
theorem B817181 : Blo 362758 817181 := bbase (se 3 (by rfl) ⟨153221, by rfl⟩ : syracuseStep 817181 = 306443) (by norm_num)
theorem B817253 : Blo 362758 817253 := bbase (se 4 (by rfl) ⟨76617, by rfl⟩ : syracuseStep 817253 = 153235) (by norm_num)
theorem B391277 : Blo 362758 391277 := bbase (se 3 (by rfl) ⟨73364, by rfl⟩ : syracuseStep 391277 = 146729) (by norm_num)
theorem B817325 : Blo 362758 817325 := bbase (se 3 (by rfl) ⟨153248, by rfl⟩ : syracuseStep 817325 = 306497) (by norm_num)
theorem B1308869 : Blo 362758 1308869 := bbase (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) (by norm_num)
theorem B620765 : Blo 362758 620765 := bbase (se 3 (by rfl) ⟨116393, by rfl⟩ : syracuseStep 620765 = 232787) (by norm_num)
theorem B817397 : Blo 362758 817397 := bbase (se 5 (by rfl) ⟨38315, by rfl⟩ : syracuseStep 817397 = 76631) (by norm_num)
theorem B817469 : Blo 362758 817469 := bbase (se 3 (by rfl) ⟨153275, by rfl⟩ : syracuseStep 817469 = 306551) (by norm_num)
theorem B1308997 : Blo 362758 1308997 := bbase (se 4 (by rfl) ⟨122718, by rfl⟩ : syracuseStep 1308997 = 245437) (by norm_num)
theorem B555373 : Blo 362758 555373 := bbase (se 3 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 555373 = 208265) (by norm_num)
theorem B1964405 : Blo 362758 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B817541 : Blo 362758 817541 := bbase (se 4 (by rfl) ⟨76644, by rfl⟩ : syracuseStep 817541 = 153289) (by norm_num)
theorem B817613 : Blo 362758 817613 := bbase (se 3 (by rfl) ⟨153302, by rfl⟩ : syracuseStep 817613 = 306605) (by norm_num)
theorem B817685 : Blo 362758 817685 := bbase (se 6 (by rfl) ⟨19164, by rfl⟩ : syracuseStep 817685 = 38329) (by norm_num)
theorem B817757 : Blo 362758 817757 := bbase (se 3 (by rfl) ⟨153329, by rfl⟩ : syracuseStep 817757 = 306659) (by norm_num)
theorem B817829 : Blo 362758 817829 := bbase (se 4 (by rfl) ⟨76671, by rfl⟩ : syracuseStep 817829 = 153343) (by norm_num)
theorem B654037 : Blo 362758 654037 := bbase (se 7 (by rfl) ⟨7664, by rfl⟩ : syracuseStep 654037 = 15329) (by norm_num)
theorem B817901 : Blo 362758 817901 := bbase (se 3 (by rfl) ⟨153356, by rfl⟩ : syracuseStep 817901 = 306713) (by norm_num)
theorem B817973 : Blo 362758 817973 := bbase (se 5 (by rfl) ⟨38342, by rfl⟩ : syracuseStep 817973 = 76685) (by norm_num)
theorem B555877 : Blo 362758 555877 := bbase (se 4 (by rfl) ⟨52113, by rfl⟩ : syracuseStep 555877 = 104227) (by norm_num)
theorem B818045 : Blo 362758 818045 := bbase (se 3 (by rfl) ⟨153383, by rfl⟩ : syracuseStep 818045 = 306767) (by norm_num)
theorem B818117 : Blo 362758 818117 := bbase (se 4 (by rfl) ⟨76698, by rfl⟩ : syracuseStep 818117 = 153397) (by norm_num)
theorem B818189 : Blo 362758 818189 := bbase (se 3 (by rfl) ⟨153410, by rfl⟩ : syracuseStep 818189 = 306821) (by norm_num)
theorem B818261 : Blo 362758 818261 := bbase (se 8 (by rfl) ⟨4794, by rfl⟩ : syracuseStep 818261 = 9589) (by norm_num)
theorem B818333 : Blo 362758 818333 := bbase (se 3 (by rfl) ⟨153437, by rfl⟩ : syracuseStep 818333 = 306875) (by norm_num)
theorem B818405 : Blo 362758 818405 := bbase (se 4 (by rfl) ⟨76725, by rfl⟩ : syracuseStep 818405 = 153451) (by norm_num)
theorem B818477 : Blo 362758 818477 := bbase (se 3 (by rfl) ⟨153464, by rfl⟩ : syracuseStep 818477 = 306929) (by norm_num)
theorem B818549 : Blo 362758 818549 := bbase (se 5 (by rfl) ⟨38369, by rfl⟩ : syracuseStep 818549 = 76739) (by norm_num)
theorem B818621 : Blo 362758 818621 := bbase (se 3 (by rfl) ⟨153491, by rfl⟩ : syracuseStep 818621 = 306983) (by norm_num)
theorem B556541 : Blo 362758 556541 := bbase (se 3 (by rfl) ⟨104351, by rfl⟩ : syracuseStep 556541 = 208703) (by norm_num)
theorem B818693 : Blo 362758 818693 := bbase (se 4 (by rfl) ⟨76752, by rfl⟩ : syracuseStep 818693 = 153505) (by norm_num)
theorem B818765 : Blo 362758 818765 := bbase (se 3 (by rfl) ⟨153518, by rfl⟩ : syracuseStep 818765 = 307037) (by norm_num)
theorem B1638005 : Blo 362758 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B818837 : Blo 362758 818837 := bbase (se 6 (by rfl) ⟨19191, by rfl⟩ : syracuseStep 818837 = 38383) (by norm_num)
theorem B818909 : Blo 362758 818909 := bbase (se 3 (by rfl) ⟨153545, by rfl⟩ : syracuseStep 818909 = 307091) (by norm_num)
theorem B655133 : Blo 362758 655133 := bbase (se 3 (by rfl) ⟨122837, by rfl⟩ : syracuseStep 655133 = 245675) (by norm_num)
theorem B1703717 : Blo 362758 1703717 := bbase (se 4 (by rfl) ⟨159723, by rfl⟩ : syracuseStep 1703717 = 319447) (by norm_num)
theorem B818981 : Blo 362758 818981 := bbase (se 4 (by rfl) ⟨76779, by rfl⟩ : syracuseStep 818981 = 153559) (by norm_num)
theorem B3211093 : Blo 362758 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B819053 : Blo 362758 819053 := bbase (se 3 (by rfl) ⟨153572, by rfl⟩ : syracuseStep 819053 = 307145) (by norm_num)
theorem B819125 : Blo 362758 819125 := bbase (se 5 (by rfl) ⟨38396, by rfl⟩ : syracuseStep 819125 = 76793) (by norm_num)
theorem B2621429 : Blo 362758 2621429 := bbase (se 5 (by rfl) ⟨122879, by rfl⟩ : syracuseStep 2621429 = 245759) (by norm_num)
theorem B819197 : Blo 362758 819197 := bbase (se 3 (by rfl) ⟨153599, by rfl⟩ : syracuseStep 819197 = 307199) (by norm_num)
theorem B819377 : Blo 362758 819377 := bstep (se 2 (by rfl) ⟨307266, by rfl⟩ : syracuseStep 819377 = 614533) B614533
theorem B819395 : Blo 362758 819395 := bstep (se 1 (by rfl) ⟨614546, by rfl⟩ : syracuseStep 819395 = 1229093) B1229093
theorem B1474957 : Blo 362758 1474957 := bstep (se 3 (by rfl) ⟨276554, by rfl⟩ : syracuseStep 1474957 = 553109) B553109
theorem B557489 : Blo 362758 557489 := bstep (se 2 (by rfl) ⟨209058, by rfl⟩ : syracuseStep 557489 = 418117) B418117
theorem B655825 : Blo 362758 655825 := bstep (se 2 (by rfl) ⟨245934, by rfl⟩ : syracuseStep 655825 = 491869) B491869
theorem B819665 : Blo 362758 819665 := bstep (se 2 (by rfl) ⟨307374, by rfl⟩ : syracuseStep 819665 = 614749) B614749
theorem B819683 : Blo 362758 819683 := bstep (se 1 (by rfl) ⟨614762, by rfl⟩ : syracuseStep 819683 = 1229525) B1229525
theorem B590417 : Blo 362758 590417 := bstep (se 2 (by rfl) ⟨221406, by rfl⟩ : syracuseStep 590417 = 442813) B442813
theorem B688753 : Blo 362758 688753 := bstep (se 2 (by rfl) ⟨258282, by rfl⟩ : syracuseStep 688753 = 516565) B516565
theorem B1245809 : Blo 362758 1245809 := bstep (se 2 (by rfl) ⟨467178, by rfl⟩ : syracuseStep 1245809 = 934357) B934357
theorem B459427 : Blo 362758 459427 := bstep (se 1 (by rfl) ⟨344570, by rfl⟩ : syracuseStep 459427 = 689141) B689141
theorem B819953 : Blo 362758 819953 := bstep (se 2 (by rfl) ⟨307482, by rfl⟩ : syracuseStep 819953 = 614965) B614965
theorem B459523 : Blo 362758 459523 := bstep (se 1 (by rfl) ⟨344642, by rfl⟩ : syracuseStep 459523 = 689285) B689285
theorem B819971 : Blo 362758 819971 := bstep (se 1 (by rfl) ⟨614978, by rfl⟩ : syracuseStep 819971 = 1229957) B1229957
theorem B3113741 : Blo 362758 3113741 := bstep (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) B1167653
theorem B4686605 : Blo 362758 4686605 := bstep (se 3 (by rfl) ⟨878738, by rfl⟩ : syracuseStep 4686605 = 1757477) B1757477
theorem B492323 : Blo 362758 492323 := bstep (se 1 (by rfl) ⟨369242, by rfl⟩ : syracuseStep 492323 = 738485) B738485
theorem B918449 : Blo 362758 918449 := bstep (se 2 (by rfl) ⟨344418, by rfl⟩ : syracuseStep 918449 = 688837) B688837
theorem B918499 : Blo 362758 918499 := bstep (se 1 (by rfl) ⟨688874, by rfl⟩ : syracuseStep 918499 = 1377749) B1377749
theorem B820241 : Blo 362758 820241 := bstep (se 2 (by rfl) ⟨307590, by rfl⟩ : syracuseStep 820241 = 615181) B615181
theorem B820259 : Blo 362758 820259 := bstep (se 1 (by rfl) ⟨615194, by rfl⟩ : syracuseStep 820259 = 1230389) B1230389
theorem B918641 : Blo 362758 918641 := bstep (se 2 (by rfl) ⟨344490, by rfl⟩ : syracuseStep 918641 = 688981) B688981
theorem B885937 : Blo 362758 885937 := bstep (se 2 (by rfl) ⟨332226, by rfl⟩ : syracuseStep 885937 = 664453) B664453
theorem B460019 : Blo 362758 460019 := bstep (se 1 (by rfl) ⟨345014, by rfl⟩ : syracuseStep 460019 = 690029) B690029
theorem B820529 : Blo 362758 820529 := bstep (se 2 (by rfl) ⟨307698, by rfl⟩ : syracuseStep 820529 = 615397) B615397
theorem B820547 : Blo 362758 820547 := bstep (se 1 (by rfl) ⟨615410, by rfl⟩ : syracuseStep 820547 = 1230821) B1230821
theorem B493075 : Blo 362758 493075 := bstep (se 1 (by rfl) ⟨369806, by rfl⟩ : syracuseStep 493075 = 739613) B739613
theorem B1836593 : Blo 362758 1836593 := bstep (se 2 (by rfl) ⟨688722, by rfl⟩ : syracuseStep 1836593 = 1377445) B1377445
theorem B820817 : Blo 362758 820817 := bstep (se 2 (by rfl) ⟨307806, by rfl⟩ : syracuseStep 820817 = 615613) B615613
theorem B820835 : Blo 362758 820835 := bstep (se 1 (by rfl) ⟨615626, by rfl⟩ : syracuseStep 820835 = 1231253) B1231253
theorem B689809 : Blo 362758 689809 := bstep (se 2 (by rfl) ⟨258678, by rfl⟩ : syracuseStep 689809 = 517357) B517357
theorem B2066147 : Blo 362758 2066147 := bstep (se 1 (by rfl) ⟨1549610, by rfl⟩ : syracuseStep 2066147 = 3099221) B3099221
theorem B821105 : Blo 362758 821105 := bstep (se 2 (by rfl) ⟨307914, by rfl⟩ : syracuseStep 821105 = 615829) B615829
theorem B821123 : Blo 362758 821123 := bstep (se 1 (by rfl) ⟨615842, by rfl⟩ : syracuseStep 821123 = 1231685) B1231685
theorem B460723 : Blo 362758 460723 := bstep (se 1 (by rfl) ⟨345542, by rfl⟩ : syracuseStep 460723 = 691085) B691085
theorem B4655029 : Blo 362758 4655029 := bstep (se 5 (by rfl) ⟨218204, by rfl⟩ : syracuseStep 4655029 = 436409) B436409
theorem B460819 : Blo 362758 460819 := bstep (se 1 (by rfl) ⟨345614, by rfl⟩ : syracuseStep 460819 = 691229) B691229
theorem B690211 : Blo 362758 690211 := bstep (se 1 (by rfl) ⟨517658, by rfl⟩ : syracuseStep 690211 = 1035317) B1035317
theorem B919633 : Blo 362758 919633 := bstep (se 2 (by rfl) ⟨344862, by rfl⟩ : syracuseStep 919633 = 689725) B689725
theorem B690257 : Blo 362758 690257 := bstep (se 2 (by rfl) ⟨258846, by rfl⟩ : syracuseStep 690257 = 517693) B517693
theorem B1378403 : Blo 362758 1378403 := bstep (se 1 (by rfl) ⟨1033802, by rfl⟩ : syracuseStep 1378403 = 2067605) B2067605
theorem B1378417 : Blo 362758 1378417 := bstep (se 2 (by rfl) ⟨516906, by rfl⟩ : syracuseStep 1378417 = 1033813) B1033813
theorem B821393 : Blo 362758 821393 := bstep (se 2 (by rfl) ⟨308022, by rfl⟩ : syracuseStep 821393 = 616045) B616045
theorem B821411 : Blo 362758 821411 := bstep (se 1 (by rfl) ⟨616058, by rfl⟩ : syracuseStep 821411 = 1232117) B1232117
theorem B362771 : Blo 362758 362771 := bstep (se 1 (by rfl) ⟨272078, by rfl⟩ : syracuseStep 362771 = 544157) B544157
theorem B362787 : Blo 362758 362787 := bstep (se 1 (by rfl) ⟨272090, by rfl⟩ : syracuseStep 362787 = 544181) B544181
theorem B362803 : Blo 362758 362803 := bstep (se 1 (by rfl) ⟨272102, by rfl⟩ : syracuseStep 362803 = 544205) B544205
theorem B362819 : Blo 362758 362819 := bstep (se 1 (by rfl) ⟨272114, by rfl⟩ : syracuseStep 362819 = 544229) B544229
theorem B362835 : Blo 362758 362835 := bstep (se 1 (by rfl) ⟨272126, by rfl⟩ : syracuseStep 362835 = 544253) B544253
theorem B362851 : Blo 362758 362851 := bstep (se 1 (by rfl) ⟨272138, by rfl⟩ : syracuseStep 362851 = 544277) B544277
theorem B919907 : Blo 362758 919907 := bstep (se 1 (by rfl) ⟨689930, by rfl⟩ : syracuseStep 919907 = 1379861) B1379861
theorem B690545 : Blo 362758 690545 := bstep (se 2 (by rfl) ⟨258954, by rfl⟩ : syracuseStep 690545 = 517909) B517909
theorem B1870193 : Blo 362758 1870193 := bstep (se 2 (by rfl) ⟨701322, by rfl⟩ : syracuseStep 1870193 = 1402645) B1402645
theorem B362867 : Blo 362758 362867 := bstep (se 1 (by rfl) ⟨272150, by rfl⟩ : syracuseStep 362867 = 544301) B544301
theorem B362883 : Blo 362758 362883 := bstep (se 1 (by rfl) ⟨272162, by rfl⟩ : syracuseStep 362883 = 544325) B544325
theorem B362899 : Blo 362758 362899 := bstep (se 1 (by rfl) ⟨272174, by rfl⟩ : syracuseStep 362899 = 544349) B544349
theorem B362915 : Blo 362758 362915 := bstep (se 1 (by rfl) ⟨272186, by rfl⟩ : syracuseStep 362915 = 544373) B544373
theorem B821681 : Blo 362758 821681 := bstep (se 2 (by rfl) ⟨308130, by rfl⟩ : syracuseStep 821681 = 616261) B616261
theorem B362931 : Blo 362758 362931 := bstep (se 1 (by rfl) ⟨272198, by rfl⟩ : syracuseStep 362931 = 544397) B544397
theorem B592307 : Blo 362758 592307 := bstep (se 1 (by rfl) ⟨444230, by rfl⟩ : syracuseStep 592307 = 888461) B888461
theorem B362947 : Blo 362758 362947 := bstep (se 1 (by rfl) ⟨272210, by rfl⟩ : syracuseStep 362947 = 544421) B544421
theorem B821699 : Blo 362758 821699 := bstep (se 1 (by rfl) ⟨616274, by rfl⟩ : syracuseStep 821699 = 1232549) B1232549
theorem B362963 : Blo 362758 362963 := bstep (se 1 (by rfl) ⟨272222, by rfl⟩ : syracuseStep 362963 = 544445) B544445
theorem B362979 : Blo 362758 362979 := bstep (se 1 (by rfl) ⟨272234, by rfl⟩ : syracuseStep 362979 = 544469) B544469
theorem B362995 : Blo 362758 362995 := bstep (se 1 (by rfl) ⟨272246, by rfl⟩ : syracuseStep 362995 = 544493) B544493
theorem B363011 : Blo 362758 363011 := bstep (se 1 (by rfl) ⟨272258, by rfl⟩ : syracuseStep 363011 = 544517) B544517
theorem B461315 : Blo 362758 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B363027 : Blo 362758 363027 := bstep (se 1 (by rfl) ⟨272270, by rfl⟩ : syracuseStep 363027 = 544541) B544541
theorem B363043 : Blo 362758 363043 := bstep (se 1 (by rfl) ⟨272282, by rfl⟩ : syracuseStep 363043 = 544565) B544565
theorem B920099 : Blo 362758 920099 := bstep (se 1 (by rfl) ⟨690074, by rfl⟩ : syracuseStep 920099 = 1380149) B1380149
theorem B363059 : Blo 362758 363059 := bstep (se 1 (by rfl) ⟨272294, by rfl⟩ : syracuseStep 363059 = 544589) B544589
theorem B363075 : Blo 362758 363075 := bstep (se 1 (by rfl) ⟨272306, by rfl⟩ : syracuseStep 363075 = 544613) B544613
theorem B363091 : Blo 362758 363091 := bstep (se 1 (by rfl) ⟨272318, by rfl⟩ : syracuseStep 363091 = 544637) B544637
theorem B363107 : Blo 362758 363107 := bstep (se 1 (by rfl) ⟨272330, by rfl⟩ : syracuseStep 363107 = 544661) B544661
theorem B1051235 : Blo 362758 1051235 := bstep (se 1 (by rfl) ⟨788426, by rfl⟩ : syracuseStep 1051235 = 1576853) B1576853
theorem B363123 : Blo 362758 363123 := bstep (se 1 (by rfl) ⟨272342, by rfl⟩ : syracuseStep 363123 = 544685) B544685
theorem B363139 : Blo 362758 363139 := bstep (se 1 (by rfl) ⟨272354, by rfl⟩ : syracuseStep 363139 = 544709) B544709
theorem B363155 : Blo 362758 363155 := bstep (se 1 (by rfl) ⟨272366, by rfl⟩ : syracuseStep 363155 = 544733) B544733
theorem B363171 : Blo 362758 363171 := bstep (se 1 (by rfl) ⟨272378, by rfl⟩ : syracuseStep 363171 = 544757) B544757
theorem B363187 : Blo 362758 363187 := bstep (se 1 (by rfl) ⟨272390, by rfl⟩ : syracuseStep 363187 = 544781) B544781
theorem B363203 : Blo 362758 363203 := bstep (se 1 (by rfl) ⟨272402, by rfl⟩ : syracuseStep 363203 = 544805) B544805
theorem B821969 : Blo 362758 821969 := bstep (se 2 (by rfl) ⟨308238, by rfl⟩ : syracuseStep 821969 = 616477) B616477
theorem B363219 : Blo 362758 363219 := bstep (se 1 (by rfl) ⟨272414, by rfl⟩ : syracuseStep 363219 = 544829) B544829
theorem B363235 : Blo 362758 363235 := bstep (se 1 (by rfl) ⟨272426, by rfl⟩ : syracuseStep 363235 = 544853) B544853
theorem B658147 : Blo 362758 658147 := bstep (se 1 (by rfl) ⟨493610, by rfl⟩ : syracuseStep 658147 = 987221) B987221
theorem B821987 : Blo 362758 821987 := bstep (se 1 (by rfl) ⟨616490, by rfl⟩ : syracuseStep 821987 = 1232981) B1232981
theorem B14093027 : Blo 362758 14093027 := bstep (se 1 (by rfl) ⟨10569770, by rfl⟩ : syracuseStep 14093027 = 21139541) B21139541
theorem B363251 : Blo 362758 363251 := bstep (se 1 (by rfl) ⟨272438, by rfl⟩ : syracuseStep 363251 = 544877) B544877
theorem B363267 : Blo 362758 363267 := bstep (se 1 (by rfl) ⟨272450, by rfl⟩ : syracuseStep 363267 = 544901) B544901
theorem B363283 : Blo 362758 363283 := bstep (se 1 (by rfl) ⟨272462, by rfl⟩ : syracuseStep 363283 = 544925) B544925
theorem B363299 : Blo 362758 363299 := bstep (se 1 (by rfl) ⟨272474, by rfl⟩ : syracuseStep 363299 = 544949) B544949
theorem B363315 : Blo 362758 363315 := bstep (se 1 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 363315 = 544973) B544973
theorem B4000565 : Blo 362758 4000565 := bstep (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) B375053
theorem B363331 : Blo 362758 363331 := bstep (se 1 (by rfl) ⟨272498, by rfl⟩ : syracuseStep 363331 = 544997) B544997
theorem B363347 : Blo 362758 363347 := bstep (se 1 (by rfl) ⟨272510, by rfl⟩ : syracuseStep 363347 = 545021) B545021
theorem B363363 : Blo 362758 363363 := bstep (se 1 (by rfl) ⟨272522, by rfl⟩ : syracuseStep 363363 = 545045) B545045
theorem B363379 : Blo 362758 363379 := bstep (se 1 (by rfl) ⟨272534, by rfl⟩ : syracuseStep 363379 = 545069) B545069
theorem B363395 : Blo 362758 363395 := bstep (se 1 (by rfl) ⟨272546, by rfl⟩ : syracuseStep 363395 = 545093) B545093
theorem B363411 : Blo 362758 363411 := bstep (se 1 (by rfl) ⟨272558, by rfl⟩ : syracuseStep 363411 = 545117) B545117
theorem B363427 : Blo 362758 363427 := bstep (se 1 (by rfl) ⟨272570, by rfl⟩ : syracuseStep 363427 = 545141) B545141
theorem B363443 : Blo 362758 363443 := bstep (se 1 (by rfl) ⟨272582, by rfl⟩ : syracuseStep 363443 = 545165) B545165
theorem B363459 : Blo 362758 363459 := bstep (se 1 (by rfl) ⟨272594, by rfl⟩ : syracuseStep 363459 = 545189) B545189
theorem B363475 : Blo 362758 363475 := bstep (se 1 (by rfl) ⟨272606, by rfl⟩ : syracuseStep 363475 = 545213) B545213
theorem B1838051 : Blo 362758 1838051 := bstep (se 1 (by rfl) ⟨1378538, by rfl⟩ : syracuseStep 1838051 = 2757077) B2757077
theorem B363491 : Blo 362758 363491 := bstep (se 1 (by rfl) ⟨272618, by rfl⟩ : syracuseStep 363491 = 545237) B545237
theorem B822257 : Blo 362758 822257 := bstep (se 2 (by rfl) ⟨308346, by rfl⟩ : syracuseStep 822257 = 616693) B616693
theorem B363507 : Blo 362758 363507 := bstep (se 1 (by rfl) ⟨272630, by rfl⟩ : syracuseStep 363507 = 545261) B545261
theorem B363523 : Blo 362758 363523 := bstep (se 1 (by rfl) ⟨272642, by rfl⟩ : syracuseStep 363523 = 545285) B545285
theorem B822275 : Blo 362758 822275 := bstep (se 1 (by rfl) ⟨616706, by rfl⟩ : syracuseStep 822275 = 1233413) B1233413
theorem B363539 : Blo 362758 363539 := bstep (se 1 (by rfl) ⟨272654, by rfl⟩ : syracuseStep 363539 = 545309) B545309
theorem B363555 : Blo 362758 363555 := bstep (se 1 (by rfl) ⟨272666, by rfl⟩ : syracuseStep 363555 = 545333) B545333
theorem B363571 : Blo 362758 363571 := bstep (se 1 (by rfl) ⟨272678, by rfl⟩ : syracuseStep 363571 = 545357) B545357
theorem B363587 : Blo 362758 363587 := bstep (se 1 (by rfl) ⟨272690, by rfl⟩ : syracuseStep 363587 = 545381) B545381
theorem B691267 : Blo 362758 691267 := bstep (se 1 (by rfl) ⟨518450, by rfl⟩ : syracuseStep 691267 = 1036901) B1036901
theorem B363603 : Blo 362758 363603 := bstep (se 1 (by rfl) ⟨272702, by rfl⟩ : syracuseStep 363603 = 545405) B545405
theorem B363619 : Blo 362758 363619 := bstep (se 1 (by rfl) ⟨272714, by rfl⟩ : syracuseStep 363619 = 545429) B545429
theorem B363635 : Blo 362758 363635 := bstep (se 1 (by rfl) ⟨272726, by rfl⟩ : syracuseStep 363635 = 545453) B545453
theorem B363651 : Blo 362758 363651 := bstep (se 1 (by rfl) ⟨272738, by rfl⟩ : syracuseStep 363651 = 545477) B545477
theorem B5934221 : Blo 362758 5934221 := bstep (se 3 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 5934221 = 2225333) B2225333
theorem B363667 : Blo 362758 363667 := bstep (se 1 (by rfl) ⟨272750, by rfl⟩ : syracuseStep 363667 = 545501) B545501
theorem B363683 : Blo 362758 363683 := bstep (se 1 (by rfl) ⟨272762, by rfl⟩ : syracuseStep 363683 = 545525) B545525
theorem B756913 : Blo 362758 756913 := bstep (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) B567685
theorem B1346737 : Blo 362758 1346737 := bstep (se 2 (by rfl) ⟨505026, by rfl⟩ : syracuseStep 1346737 = 1010053) B1010053
theorem B363699 : Blo 362758 363699 := bstep (se 1 (by rfl) ⟨272774, by rfl⟩ : syracuseStep 363699 = 545549) B545549
theorem B363715 : Blo 362758 363715 := bstep (se 1 (by rfl) ⟨272786, by rfl⟩ : syracuseStep 363715 = 545573) B545573
theorem B462019 : Blo 362758 462019 := bstep (se 1 (by rfl) ⟨346514, by rfl⟩ : syracuseStep 462019 = 693029) B693029
theorem B363731 : Blo 362758 363731 := bstep (se 1 (by rfl) ⟨272798, by rfl⟩ : syracuseStep 363731 = 545597) B545597
theorem B363747 : Blo 362758 363747 := bstep (se 1 (by rfl) ⟨272810, by rfl⟩ : syracuseStep 363747 = 545621) B545621
theorem B363763 : Blo 362758 363763 := bstep (se 1 (by rfl) ⟨272822, by rfl⟩ : syracuseStep 363763 = 545645) B545645
theorem B363779 : Blo 362758 363779 := bstep (se 1 (by rfl) ⟨272834, by rfl⟩ : syracuseStep 363779 = 545669) B545669
theorem B822545 : Blo 362758 822545 := bstep (se 2 (by rfl) ⟨308454, by rfl⟩ : syracuseStep 822545 = 616909) B616909
theorem B363795 : Blo 362758 363795 := bstep (se 1 (by rfl) ⟨272846, by rfl⟩ : syracuseStep 363795 = 545693) B545693
theorem B363811 : Blo 362758 363811 := bstep (se 1 (by rfl) ⟨272858, by rfl⟩ : syracuseStep 363811 = 545717) B545717
theorem B1248547 : Blo 362758 1248547 := bstep (se 1 (by rfl) ⟨936410, by rfl⟩ : syracuseStep 1248547 = 1872821) B1872821
theorem B462115 : Blo 362758 462115 := bstep (se 1 (by rfl) ⟨346586, by rfl⟩ : syracuseStep 462115 = 693173) B693173
theorem B822563 : Blo 362758 822563 := bstep (se 1 (by rfl) ⟨616922, by rfl⟩ : syracuseStep 822563 = 1233845) B1233845
theorem B363827 : Blo 362758 363827 := bstep (se 1 (by rfl) ⟨272870, by rfl⟩ : syracuseStep 363827 = 545741) B545741
theorem B363843 : Blo 362758 363843 := bstep (se 1 (by rfl) ⟨272882, by rfl⟩ : syracuseStep 363843 = 545765) B545765
theorem B363859 : Blo 362758 363859 := bstep (se 1 (by rfl) ⟨272894, by rfl⟩ : syracuseStep 363859 = 545789) B545789
theorem B363875 : Blo 362758 363875 := bstep (se 1 (by rfl) ⟨272906, by rfl⟩ : syracuseStep 363875 = 545813) B545813
theorem B363891 : Blo 362758 363891 := bstep (se 1 (by rfl) ⟨272918, by rfl⟩ : syracuseStep 363891 = 545837) B545837
theorem B363907 : Blo 362758 363907 := bstep (se 1 (by rfl) ⟨272930, by rfl⟩ : syracuseStep 363907 = 545861) B545861
theorem B363923 : Blo 362758 363923 := bstep (se 1 (by rfl) ⟨272942, by rfl⟩ : syracuseStep 363923 = 545885) B545885
theorem B363939 : Blo 362758 363939 := bstep (se 1 (by rfl) ⟨272954, by rfl⟩ : syracuseStep 363939 = 545909) B545909
theorem B363955 : Blo 362758 363955 := bstep (se 1 (by rfl) ⟨272966, by rfl⟩ : syracuseStep 363955 = 545933) B545933
theorem B363971 : Blo 362758 363971 := bstep (se 1 (by rfl) ⟨272978, by rfl⟩ : syracuseStep 363971 = 545957) B545957
theorem B921041 : Blo 362758 921041 := bstep (se 2 (by rfl) ⟨345390, by rfl⟩ : syracuseStep 921041 = 690781) B690781
theorem B363987 : Blo 362758 363987 := bstep (se 1 (by rfl) ⟨272990, by rfl⟩ : syracuseStep 363987 = 545981) B545981
theorem B364003 : Blo 362758 364003 := bstep (se 1 (by rfl) ⟨273002, by rfl⟩ : syracuseStep 364003 = 546005) B546005
theorem B364019 : Blo 362758 364019 := bstep (se 1 (by rfl) ⟨273014, by rfl⟩ : syracuseStep 364019 = 546029) B546029
theorem B921091 : Blo 362758 921091 := bstep (se 1 (by rfl) ⟨690818, by rfl⟩ : syracuseStep 921091 = 1381637) B1381637
theorem B364035 : Blo 362758 364035 := bstep (se 1 (by rfl) ⟨273026, by rfl⟩ : syracuseStep 364035 = 546053) B546053
theorem B691715 : Blo 362758 691715 := bstep (se 1 (by rfl) ⟨518786, by rfl⟩ : syracuseStep 691715 = 1037573) B1037573
theorem B364051 : Blo 362758 364051 := bstep (se 1 (by rfl) ⟨273038, by rfl⟩ : syracuseStep 364051 = 546077) B546077
theorem B1379875 : Blo 362758 1379875 := bstep (se 1 (by rfl) ⟨1034906, by rfl⟩ : syracuseStep 1379875 = 2069813) B2069813
theorem B364067 : Blo 362758 364067 := bstep (se 1 (by rfl) ⟨273050, by rfl⟩ : syracuseStep 364067 = 546101) B546101
theorem B822833 : Blo 362758 822833 := bstep (se 2 (by rfl) ⟨308562, by rfl⟩ : syracuseStep 822833 = 617125) B617125
theorem B364083 : Blo 362758 364083 := bstep (se 1 (by rfl) ⟨273062, by rfl⟩ : syracuseStep 364083 = 546125) B546125
theorem B364099 : Blo 362758 364099 := bstep (se 1 (by rfl) ⟨273074, by rfl⟩ : syracuseStep 364099 = 546149) B546149
theorem B822851 : Blo 362758 822851 := bstep (se 1 (by rfl) ⟨617138, by rfl⟩ : syracuseStep 822851 = 1234277) B1234277
theorem B2068037 : Blo 362758 2068037 := bstep (se 4 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 2068037 = 387757) B387757
theorem B364115 : Blo 362758 364115 := bstep (se 1 (by rfl) ⟨273086, by rfl⟩ : syracuseStep 364115 = 546173) B546173
theorem B364131 : Blo 362758 364131 := bstep (se 1 (by rfl) ⟨273098, by rfl⟩ : syracuseStep 364131 = 546197) B546197
theorem B364147 : Blo 362758 364147 := bstep (se 1 (by rfl) ⟨273110, by rfl⟩ : syracuseStep 364147 = 546221) B546221
theorem B364163 : Blo 362758 364163 := bstep (se 1 (by rfl) ⟨273122, by rfl⟩ : syracuseStep 364163 = 546245) B546245
theorem B1773197 : Blo 362758 1773197 := bstep (se 3 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 1773197 = 664949) B664949
theorem B921233 : Blo 362758 921233 := bstep (se 2 (by rfl) ⟨345462, by rfl⟩ : syracuseStep 921233 = 690925) B690925
theorem B364179 : Blo 362758 364179 := bstep (se 1 (by rfl) ⟨273134, by rfl⟩ : syracuseStep 364179 = 546269) B546269
theorem B364195 : Blo 362758 364195 := bstep (se 1 (by rfl) ⟨273146, by rfl⟩ : syracuseStep 364195 = 546293) B546293
theorem B364211 : Blo 362758 364211 := bstep (se 1 (by rfl) ⟨273158, by rfl⟩ : syracuseStep 364211 = 546317) B546317
theorem B364227 : Blo 362758 364227 := bstep (se 1 (by rfl) ⟨273170, by rfl⟩ : syracuseStep 364227 = 546341) B546341
theorem B364243 : Blo 362758 364243 := bstep (se 1 (by rfl) ⟨273182, by rfl⟩ : syracuseStep 364243 = 546365) B546365
theorem B364259 : Blo 362758 364259 := bstep (se 1 (by rfl) ⟨273194, by rfl⟩ : syracuseStep 364259 = 546389) B546389
theorem B659171 : Blo 362758 659171 := bstep (se 1 (by rfl) ⟨494378, by rfl⟩ : syracuseStep 659171 = 988757) B988757
theorem B364275 : Blo 362758 364275 := bstep (se 1 (by rfl) ⟨273206, by rfl⟩ : syracuseStep 364275 = 546413) B546413
theorem B364291 : Blo 362758 364291 := bstep (se 1 (by rfl) ⟨273218, by rfl⟩ : syracuseStep 364291 = 546437) B546437
theorem B1838861 : Blo 362758 1838861 := bstep (se 3 (by rfl) ⟨344786, by rfl⟩ : syracuseStep 1838861 = 689573) B689573
theorem B364307 : Blo 362758 364307 := bstep (se 1 (by rfl) ⟨273230, by rfl⟩ : syracuseStep 364307 = 546461) B546461
theorem B462611 : Blo 362758 462611 := bstep (se 1 (by rfl) ⟨346958, by rfl⟩ : syracuseStep 462611 = 693917) B693917
theorem B364323 : Blo 362758 364323 := bstep (se 1 (by rfl) ⟨273242, by rfl⟩ : syracuseStep 364323 = 546485) B546485
theorem B692003 : Blo 362758 692003 := bstep (se 1 (by rfl) ⟨519002, by rfl⟩ : syracuseStep 692003 = 1038005) B1038005
theorem B364339 : Blo 362758 364339 := bstep (se 1 (by rfl) ⟨273254, by rfl⟩ : syracuseStep 364339 = 546509) B546509
theorem B364355 : Blo 362758 364355 := bstep (se 1 (by rfl) ⟨273266, by rfl⟩ : syracuseStep 364355 = 546533) B546533
theorem B823121 : Blo 362758 823121 := bstep (se 2 (by rfl) ⟨308670, by rfl⟩ : syracuseStep 823121 = 617341) B617341
theorem B364371 : Blo 362758 364371 := bstep (se 1 (by rfl) ⟨273278, by rfl⟩ : syracuseStep 364371 = 546557) B546557
theorem B364387 : Blo 362758 364387 := bstep (se 1 (by rfl) ⟨273290, by rfl⟩ : syracuseStep 364387 = 546581) B546581
theorem B823139 : Blo 362758 823139 := bstep (se 1 (by rfl) ⟨617354, by rfl⟩ : syracuseStep 823139 = 1234709) B1234709
theorem B364403 : Blo 362758 364403 := bstep (se 1 (by rfl) ⟨273302, by rfl⟩ : syracuseStep 364403 = 546605) B546605
theorem B364419 : Blo 362758 364419 := bstep (se 1 (by rfl) ⟨273314, by rfl⟩ : syracuseStep 364419 = 546629) B546629
theorem B364435 : Blo 362758 364435 := bstep (se 1 (by rfl) ⟨273326, by rfl⟩ : syracuseStep 364435 = 546653) B546653
theorem B364451 : Blo 362758 364451 := bstep (se 1 (by rfl) ⟨273338, by rfl⟩ : syracuseStep 364451 = 546677) B546677
theorem B364467 : Blo 362758 364467 := bstep (se 1 (by rfl) ⟨273350, by rfl⟩ : syracuseStep 364467 = 546701) B546701
theorem B364483 : Blo 362758 364483 := bstep (se 1 (by rfl) ⟨273362, by rfl⟩ : syracuseStep 364483 = 546725) B546725
theorem B364499 : Blo 362758 364499 := bstep (se 1 (by rfl) ⟨273374, by rfl⟩ : syracuseStep 364499 = 546749) B546749
theorem B364515 : Blo 362758 364515 := bstep (se 1 (by rfl) ⟨273386, by rfl⟩ : syracuseStep 364515 = 546773) B546773
theorem B364531 : Blo 362758 364531 := bstep (se 1 (by rfl) ⟨273398, by rfl⟩ : syracuseStep 364531 = 546797) B546797
theorem B364547 : Blo 362758 364547 := bstep (se 1 (by rfl) ⟨273410, by rfl⟩ : syracuseStep 364547 = 546821) B546821
theorem B364563 : Blo 362758 364563 := bstep (se 1 (by rfl) ⟨273422, by rfl⟩ : syracuseStep 364563 = 546845) B546845
theorem B364579 : Blo 362758 364579 := bstep (se 1 (by rfl) ⟨273434, by rfl⟩ : syracuseStep 364579 = 546869) B546869
theorem B2101297 : Blo 362758 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B364595 : Blo 362758 364595 := bstep (se 1 (by rfl) ⟨273446, by rfl⟩ : syracuseStep 364595 = 546893) B546893
theorem B364611 : Blo 362758 364611 := bstep (se 1 (by rfl) ⟨273458, by rfl⟩ : syracuseStep 364611 = 546917) B546917
theorem B3510341 : Blo 362758 3510341 := bstep (se 4 (by rfl) ⟨329094, by rfl⟩ : syracuseStep 3510341 = 658189) B658189
theorem B364627 : Blo 362758 364627 := bstep (se 1 (by rfl) ⟨273470, by rfl⟩ : syracuseStep 364627 = 546941) B546941
theorem B364643 : Blo 362758 364643 := bstep (se 1 (by rfl) ⟨273482, by rfl⟩ : syracuseStep 364643 = 546965) B546965
theorem B823409 : Blo 362758 823409 := bstep (se 2 (by rfl) ⟨308778, by rfl⟩ : syracuseStep 823409 = 617557) B617557
theorem B364659 : Blo 362758 364659 := bstep (se 1 (by rfl) ⟨273494, by rfl⟩ : syracuseStep 364659 = 546989) B546989
theorem B364675 : Blo 362758 364675 := bstep (se 1 (by rfl) ⟨273506, by rfl⟩ : syracuseStep 364675 = 547013) B547013
theorem B823427 : Blo 362758 823427 := bstep (se 1 (by rfl) ⟨617570, by rfl⟩ : syracuseStep 823427 = 1235141) B1235141
theorem B364691 : Blo 362758 364691 := bstep (se 1 (by rfl) ⟨273518, by rfl⟩ : syracuseStep 364691 = 547037) B547037
theorem B364707 : Blo 362758 364707 := bstep (se 1 (by rfl) ⟨273530, by rfl⟩ : syracuseStep 364707 = 547061) B547061
theorem B364723 : Blo 362758 364723 := bstep (se 1 (by rfl) ⟨273542, by rfl⟩ : syracuseStep 364723 = 547085) B547085
theorem B364739 : Blo 362758 364739 := bstep (se 1 (by rfl) ⟨273554, by rfl⟩ : syracuseStep 364739 = 547109) B547109
theorem B364755 : Blo 362758 364755 := bstep (se 1 (by rfl) ⟨273566, by rfl⟩ : syracuseStep 364755 = 547133) B547133
theorem B364771 : Blo 362758 364771 := bstep (se 1 (by rfl) ⟨273578, by rfl⟩ : syracuseStep 364771 = 547157) B547157
theorem B364787 : Blo 362758 364787 := bstep (se 1 (by rfl) ⟨273590, by rfl⟩ : syracuseStep 364787 = 547181) B547181
theorem B364803 : Blo 362758 364803 := bstep (se 1 (by rfl) ⟨273602, by rfl⟩ : syracuseStep 364803 = 547205) B547205
theorem B364819 : Blo 362758 364819 := bstep (se 1 (by rfl) ⟨273614, by rfl⟩ : syracuseStep 364819 = 547229) B547229
theorem B364835 : Blo 362758 364835 := bstep (se 1 (by rfl) ⟨273626, by rfl⟩ : syracuseStep 364835 = 547253) B547253
theorem B659747 : Blo 362758 659747 := bstep (se 1 (by rfl) ⟨494810, by rfl⟩ : syracuseStep 659747 = 989621) B989621
theorem B364851 : Blo 362758 364851 := bstep (se 1 (by rfl) ⟨273638, by rfl⟩ : syracuseStep 364851 = 547277) B547277
theorem B364867 : Blo 362758 364867 := bstep (se 1 (by rfl) ⟨273650, by rfl⟩ : syracuseStep 364867 = 547301) B547301
theorem B364883 : Blo 362758 364883 := bstep (se 1 (by rfl) ⟨273662, by rfl⟩ : syracuseStep 364883 = 547325) B547325
theorem B364899 : Blo 362758 364899 := bstep (se 1 (by rfl) ⟨273674, by rfl⟩ : syracuseStep 364899 = 547349) B547349
theorem B364915 : Blo 362758 364915 := bstep (se 1 (by rfl) ⟨273686, by rfl⟩ : syracuseStep 364915 = 547373) B547373
theorem B364931 : Blo 362758 364931 := bstep (se 1 (by rfl) ⟨273698, by rfl⟩ : syracuseStep 364931 = 547397) B547397
theorem B823697 : Blo 362758 823697 := bstep (se 2 (by rfl) ⟨308886, by rfl⟩ : syracuseStep 823697 = 617773) B617773
theorem B364947 : Blo 362758 364947 := bstep (se 1 (by rfl) ⟨273710, by rfl⟩ : syracuseStep 364947 = 547421) B547421
theorem B364963 : Blo 362758 364963 := bstep (se 1 (by rfl) ⟨273722, by rfl⟩ : syracuseStep 364963 = 547445) B547445
theorem B823715 : Blo 362758 823715 := bstep (se 1 (by rfl) ⟨617786, by rfl⟩ : syracuseStep 823715 = 1235573) B1235573
theorem B364979 : Blo 362758 364979 := bstep (se 1 (by rfl) ⟨273734, by rfl⟩ : syracuseStep 364979 = 547469) B547469
theorem B364995 : Blo 362758 364995 := bstep (se 1 (by rfl) ⟨273746, by rfl⟩ : syracuseStep 364995 = 547493) B547493
theorem B2822597 : Blo 362758 2822597 := bstep (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) B529237
theorem B365011 : Blo 362758 365011 := bstep (se 1 (by rfl) ⟨273758, by rfl⟩ : syracuseStep 365011 = 547517) B547517
theorem B463315 : Blo 362758 463315 := bstep (se 1 (by rfl) ⟨347486, by rfl⟩ : syracuseStep 463315 = 694973) B694973
theorem B365027 : Blo 362758 365027 := bstep (se 1 (by rfl) ⟨273770, by rfl⟩ : syracuseStep 365027 = 547541) B547541
theorem B365043 : Blo 362758 365043 := bstep (se 1 (by rfl) ⟨273782, by rfl⟩ : syracuseStep 365043 = 547565) B547565
theorem B365059 : Blo 362758 365059 := bstep (se 1 (by rfl) ⟨273794, by rfl⟩ : syracuseStep 365059 = 547589) B547589
theorem B365075 : Blo 362758 365075 := bstep (se 1 (by rfl) ⟨273806, by rfl⟩ : syracuseStep 365075 = 547613) B547613
theorem B365091 : Blo 362758 365091 := bstep (se 1 (by rfl) ⟨273818, by rfl⟩ : syracuseStep 365091 = 547637) B547637
theorem B365107 : Blo 362758 365107 := bstep (se 1 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 365107 = 547661) B547661
theorem B463411 : Blo 362758 463411 := bstep (se 1 (by rfl) ⟨347558, by rfl⟩ : syracuseStep 463411 = 695117) B695117
theorem B4133429 : Blo 362758 4133429 := bstep (se 5 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 4133429 = 387509) B387509
theorem B365123 : Blo 362758 365123 := bstep (se 1 (by rfl) ⟨273842, by rfl⟩ : syracuseStep 365123 = 547685) B547685
theorem B660035 : Blo 362758 660035 := bstep (se 1 (by rfl) ⟨495026, by rfl⟩ : syracuseStep 660035 = 990053) B990053
theorem B365139 : Blo 362758 365139 := bstep (se 1 (by rfl) ⟨273854, by rfl⟩ : syracuseStep 365139 = 547709) B547709
theorem B365155 : Blo 362758 365155 := bstep (se 1 (by rfl) ⟨273866, by rfl⟩ : syracuseStep 365155 = 547733) B547733
theorem B922225 : Blo 362758 922225 := bstep (se 2 (by rfl) ⟨345834, by rfl⟩ : syracuseStep 922225 = 691669) B691669
theorem B365171 : Blo 362758 365171 := bstep (se 1 (by rfl) ⟨273878, by rfl⟩ : syracuseStep 365171 = 547757) B547757
theorem B365187 : Blo 362758 365187 := bstep (se 1 (by rfl) ⟨273890, by rfl⟩ : syracuseStep 365187 = 547781) B547781
theorem B365203 : Blo 362758 365203 := bstep (se 1 (by rfl) ⟨273902, by rfl⟩ : syracuseStep 365203 = 547805) B547805
theorem B365219 : Blo 362758 365219 := bstep (se 1 (by rfl) ⟨273914, by rfl⟩ : syracuseStep 365219 = 547829) B547829
theorem B823985 : Blo 362758 823985 := bstep (se 2 (by rfl) ⟨308994, by rfl⟩ : syracuseStep 823985 = 617989) B617989
theorem B365235 : Blo 362758 365235 := bstep (se 1 (by rfl) ⟨273926, by rfl⟩ : syracuseStep 365235 = 547853) B547853
theorem B365251 : Blo 362758 365251 := bstep (se 1 (by rfl) ⟨273938, by rfl⟩ : syracuseStep 365251 = 547877) B547877
theorem B824003 : Blo 362758 824003 := bstep (se 1 (by rfl) ⟨618002, by rfl⟩ : syracuseStep 824003 = 1236005) B1236005
theorem B692945 : Blo 362758 692945 := bstep (se 2 (by rfl) ⟨259854, by rfl⟩ : syracuseStep 692945 = 519709) B519709
theorem B365267 : Blo 362758 365267 := bstep (se 1 (by rfl) ⟨273950, by rfl⟩ : syracuseStep 365267 = 547901) B547901
theorem B365283 : Blo 362758 365283 := bstep (se 1 (by rfl) ⟨273962, by rfl⟩ : syracuseStep 365283 = 547925) B547925
theorem B365299 : Blo 362758 365299 := bstep (se 1 (by rfl) ⟨273974, by rfl⟩ : syracuseStep 365299 = 547949) B547949
theorem B365315 : Blo 362758 365315 := bstep (se 1 (by rfl) ⟨273986, by rfl⟩ : syracuseStep 365315 = 547973) B547973
theorem B365331 : Blo 362758 365331 := bstep (se 1 (by rfl) ⟨273998, by rfl⟩ : syracuseStep 365331 = 547997) B547997
theorem B561953 : Blo 362758 561953 := bstep (se 2 (by rfl) ⟨210732, by rfl⟩ : syracuseStep 561953 = 421465) B421465
theorem B365347 : Blo 362758 365347 := bstep (se 1 (by rfl) ⟨274010, by rfl⟩ : syracuseStep 365347 = 548021) B548021
theorem B365363 : Blo 362758 365363 := bstep (se 1 (by rfl) ⟨274022, by rfl⟩ : syracuseStep 365363 = 548045) B548045
theorem B365379 : Blo 362758 365379 := bstep (se 1 (by rfl) ⟨274034, by rfl⟩ : syracuseStep 365379 = 548069) B548069
theorem B365395 : Blo 362758 365395 := bstep (se 1 (by rfl) ⟨274046, by rfl⟩ : syracuseStep 365395 = 548093) B548093
theorem B365411 : Blo 362758 365411 := bstep (se 1 (by rfl) ⟨274058, by rfl⟩ : syracuseStep 365411 = 548117) B548117
theorem B365427 : Blo 362758 365427 := bstep (se 1 (by rfl) ⟨274070, by rfl⟩ : syracuseStep 365427 = 548141) B548141
theorem B922499 : Blo 362758 922499 := bstep (se 1 (by rfl) ⟨691874, by rfl⟩ : syracuseStep 922499 = 1383749) B1383749
theorem B365443 : Blo 362758 365443 := bstep (se 1 (by rfl) ⟨274082, by rfl⟩ : syracuseStep 365443 = 548165) B548165
theorem B365459 : Blo 362758 365459 := bstep (se 1 (by rfl) ⟨274094, by rfl⟩ : syracuseStep 365459 = 548189) B548189
theorem B365475 : Blo 362758 365475 := bstep (se 1 (by rfl) ⟨274106, by rfl⟩ : syracuseStep 365475 = 548213) B548213
theorem B365491 : Blo 362758 365491 := bstep (se 1 (by rfl) ⟨274118, by rfl⟩ : syracuseStep 365491 = 548237) B548237
theorem B365507 : Blo 362758 365507 := bstep (se 1 (by rfl) ⟨274130, by rfl⟩ : syracuseStep 365507 = 548261) B548261
theorem B824273 : Blo 362758 824273 := bstep (se 2 (by rfl) ⟨309102, by rfl⟩ : syracuseStep 824273 = 618205) B618205
theorem B365523 : Blo 362758 365523 := bstep (se 1 (by rfl) ⟨274142, by rfl⟩ : syracuseStep 365523 = 548285) B548285
theorem B365539 : Blo 362758 365539 := bstep (se 1 (by rfl) ⟨274154, by rfl⟩ : syracuseStep 365539 = 548309) B548309
theorem B824291 : Blo 362758 824291 := bstep (se 1 (by rfl) ⟨618218, by rfl⟩ : syracuseStep 824291 = 1236437) B1236437
theorem B365555 : Blo 362758 365555 := bstep (se 1 (by rfl) ⟨274166, by rfl⟩ : syracuseStep 365555 = 548333) B548333
theorem B365571 : Blo 362758 365571 := bstep (se 1 (by rfl) ⟨274178, by rfl⟩ : syracuseStep 365571 = 548357) B548357
theorem B365587 : Blo 362758 365587 := bstep (se 1 (by rfl) ⟨274190, by rfl⟩ : syracuseStep 365587 = 548381) B548381
theorem B365603 : Blo 362758 365603 := bstep (se 1 (by rfl) ⟨274202, by rfl⟩ : syracuseStep 365603 = 548405) B548405
theorem B463907 : Blo 362758 463907 := bstep (se 1 (by rfl) ⟨347930, by rfl⟩ : syracuseStep 463907 = 695861) B695861
theorem B365619 : Blo 362758 365619 := bstep (se 1 (by rfl) ⟨274214, by rfl⟩ : syracuseStep 365619 = 548429) B548429
theorem B922691 : Blo 362758 922691 := bstep (se 1 (by rfl) ⟨692018, by rfl⟩ : syracuseStep 922691 = 1384037) B1384037
theorem B365635 : Blo 362758 365635 := bstep (se 1 (by rfl) ⟨274226, by rfl⟩ : syracuseStep 365635 = 548453) B548453
theorem B365651 : Blo 362758 365651 := bstep (se 1 (by rfl) ⟨274238, by rfl⟩ : syracuseStep 365651 = 548477) B548477
theorem B365667 : Blo 362758 365667 := bstep (se 1 (by rfl) ⟨274250, by rfl⟩ : syracuseStep 365667 = 548501) B548501
theorem B365683 : Blo 362758 365683 := bstep (se 1 (by rfl) ⟨274262, by rfl⟩ : syracuseStep 365683 = 548525) B548525
theorem B365699 : Blo 362758 365699 := bstep (se 1 (by rfl) ⟨274274, by rfl⟩ : syracuseStep 365699 = 548549) B548549
theorem B365715 : Blo 362758 365715 := bstep (se 1 (by rfl) ⟨274286, by rfl⟩ : syracuseStep 365715 = 548573) B548573
theorem B365731 : Blo 362758 365731 := bstep (se 1 (by rfl) ⟨274298, by rfl⟩ : syracuseStep 365731 = 548597) B548597
theorem B365747 : Blo 362758 365747 := bstep (se 1 (by rfl) ⟨274310, by rfl⟩ : syracuseStep 365747 = 548621) B548621
theorem B365763 : Blo 362758 365763 := bstep (se 1 (by rfl) ⟨274322, by rfl⟩ : syracuseStep 365763 = 548645) B548645
theorem B365779 : Blo 362758 365779 := bstep (se 1 (by rfl) ⟨274334, by rfl⟩ : syracuseStep 365779 = 548669) B548669
theorem B365795 : Blo 362758 365795 := bstep (se 1 (by rfl) ⟨274346, by rfl⟩ : syracuseStep 365795 = 548693) B548693
theorem B824561 : Blo 362758 824561 := bstep (se 2 (by rfl) ⟨309210, by rfl⟩ : syracuseStep 824561 = 618421) B618421
theorem B365811 : Blo 362758 365811 := bstep (se 1 (by rfl) ⟨274358, by rfl⟩ : syracuseStep 365811 = 548717) B548717
theorem B365827 : Blo 362758 365827 := bstep (se 1 (by rfl) ⟨274370, by rfl⟩ : syracuseStep 365827 = 548741) B548741
theorem B824579 : Blo 362758 824579 := bstep (se 1 (by rfl) ⟨618434, by rfl⟩ : syracuseStep 824579 = 1236869) B1236869
theorem B365843 : Blo 362758 365843 := bstep (se 1 (by rfl) ⟨274382, by rfl⟩ : syracuseStep 365843 = 548765) B548765
theorem B365859 : Blo 362758 365859 := bstep (se 1 (by rfl) ⟨274394, by rfl⟩ : syracuseStep 365859 = 548789) B548789
theorem B365875 : Blo 362758 365875 := bstep (se 1 (by rfl) ⟨274406, by rfl⟩ : syracuseStep 365875 = 548813) B548813
theorem B365891 : Blo 362758 365891 := bstep (se 1 (by rfl) ⟨274418, by rfl⟩ : syracuseStep 365891 = 548837) B548837
theorem B365907 : Blo 362758 365907 := bstep (se 1 (by rfl) ⟨274430, by rfl⟩ : syracuseStep 365907 = 548861) B548861
theorem B365923 : Blo 362758 365923 := bstep (se 1 (by rfl) ⟨274442, by rfl⟩ : syracuseStep 365923 = 548885) B548885
theorem B365939 : Blo 362758 365939 := bstep (se 1 (by rfl) ⟨274454, by rfl⟩ : syracuseStep 365939 = 548909) B548909
theorem B365955 : Blo 362758 365955 := bstep (se 1 (by rfl) ⟨274466, by rfl⟩ : syracuseStep 365955 = 548933) B548933
theorem B365971 : Blo 362758 365971 := bstep (se 1 (by rfl) ⟨274478, by rfl⟩ : syracuseStep 365971 = 548957) B548957
theorem B365987 : Blo 362758 365987 := bstep (se 1 (by rfl) ⟨274490, by rfl⟩ : syracuseStep 365987 = 548981) B548981
theorem B366003 : Blo 362758 366003 := bstep (se 1 (by rfl) ⟨274502, by rfl⟩ : syracuseStep 366003 = 549005) B549005
theorem B366019 : Blo 362758 366019 := bstep (se 1 (by rfl) ⟨274514, by rfl⟩ : syracuseStep 366019 = 549029) B549029
theorem B366035 : Blo 362758 366035 := bstep (se 1 (by rfl) ⟨274526, by rfl⟩ : syracuseStep 366035 = 549053) B549053
theorem B366051 : Blo 362758 366051 := bstep (se 1 (by rfl) ⟨274538, by rfl⟩ : syracuseStep 366051 = 549077) B549077
theorem B366067 : Blo 362758 366067 := bstep (se 1 (by rfl) ⟨274550, by rfl⟩ : syracuseStep 366067 = 549101) B549101
theorem B366083 : Blo 362758 366083 := bstep (se 1 (by rfl) ⟨274562, by rfl⟩ : syracuseStep 366083 = 549125) B549125
theorem B824849 : Blo 362758 824849 := bstep (se 2 (by rfl) ⟨309318, by rfl⟩ : syracuseStep 824849 = 618637) B618637
theorem B366099 : Blo 362758 366099 := bstep (se 1 (by rfl) ⟨274574, by rfl⟩ : syracuseStep 366099 = 549149) B549149
theorem B366115 : Blo 362758 366115 := bstep (se 1 (by rfl) ⟨274586, by rfl⟩ : syracuseStep 366115 = 549173) B549173
theorem B824867 : Blo 362758 824867 := bstep (se 1 (by rfl) ⟨618650, by rfl⟩ : syracuseStep 824867 = 1237301) B1237301
theorem B366131 : Blo 362758 366131 := bstep (se 1 (by rfl) ⟨274598, by rfl⟩ : syracuseStep 366131 = 549197) B549197
theorem B366147 : Blo 362758 366147 := bstep (se 1 (by rfl) ⟨274610, by rfl⟩ : syracuseStep 366147 = 549221) B549221
theorem B693841 : Blo 362758 693841 := bstep (se 2 (by rfl) ⟨260190, by rfl⟩ : syracuseStep 693841 = 520381) B520381
theorem B366163 : Blo 362758 366163 := bstep (se 1 (by rfl) ⟨274622, by rfl⟩ : syracuseStep 366163 = 549245) B549245
theorem B366179 : Blo 362758 366179 := bstep (se 1 (by rfl) ⟨274634, by rfl⟩ : syracuseStep 366179 = 549269) B549269
theorem B12719729 : Blo 362758 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B366195 : Blo 362758 366195 := bstep (se 1 (by rfl) ⟨274646, by rfl⟩ : syracuseStep 366195 = 549293) B549293
theorem B366211 : Blo 362758 366211 := bstep (se 1 (by rfl) ⟨274658, by rfl⟩ : syracuseStep 366211 = 549317) B549317
theorem B366227 : Blo 362758 366227 := bstep (se 1 (by rfl) ⟨274670, by rfl⟩ : syracuseStep 366227 = 549341) B549341
theorem B366243 : Blo 362758 366243 := bstep (se 1 (by rfl) ⟨274682, by rfl⟩ : syracuseStep 366243 = 549365) B549365
theorem B1185457 : Blo 362758 1185457 := bstep (se 2 (by rfl) ⟨444546, by rfl⟩ : syracuseStep 1185457 = 889093) B889093
theorem B366259 : Blo 362758 366259 := bstep (se 1 (by rfl) ⟨274694, by rfl⟩ : syracuseStep 366259 = 549389) B549389
theorem B366275 : Blo 362758 366275 := bstep (se 1 (by rfl) ⟨274706, by rfl⟩ : syracuseStep 366275 = 549413) B549413
theorem B1382093 : Blo 362758 1382093 := bstep (se 3 (by rfl) ⟨259142, by rfl⟩ : syracuseStep 1382093 = 518285) B518285
theorem B366291 : Blo 362758 366291 := bstep (se 1 (by rfl) ⟨274718, by rfl⟩ : syracuseStep 366291 = 549437) B549437
theorem B366307 : Blo 362758 366307 := bstep (se 1 (by rfl) ⟨274730, by rfl⟩ : syracuseStep 366307 = 549461) B549461
theorem B694001 : Blo 362758 694001 := bstep (se 2 (by rfl) ⟨260250, by rfl⟩ : syracuseStep 694001 = 520501) B520501
theorem B366323 : Blo 362758 366323 := bstep (se 1 (by rfl) ⟨274742, by rfl⟩ : syracuseStep 366323 = 549485) B549485
theorem B366339 : Blo 362758 366339 := bstep (se 1 (by rfl) ⟨274754, by rfl⟩ : syracuseStep 366339 = 549509) B549509
theorem B366355 : Blo 362758 366355 := bstep (se 1 (by rfl) ⟨274766, by rfl⟩ : syracuseStep 366355 = 549533) B549533
theorem B366371 : Blo 362758 366371 := bstep (se 1 (by rfl) ⟨274778, by rfl⟩ : syracuseStep 366371 = 549557) B549557
theorem B988973 : Blo 362758 988973 := bstep (se 3 (by rfl) ⟨185432, by rfl⟩ : syracuseStep 988973 = 370865) B370865
theorem B825137 : Blo 362758 825137 := bstep (se 2 (by rfl) ⟨309426, by rfl⟩ : syracuseStep 825137 = 618853) B618853
theorem B366387 : Blo 362758 366387 := bstep (se 1 (by rfl) ⟨274790, by rfl⟩ : syracuseStep 366387 = 549581) B549581
theorem B366403 : Blo 362758 366403 := bstep (se 1 (by rfl) ⟨274802, by rfl⟩ : syracuseStep 366403 = 549605) B549605
theorem B825155 : Blo 362758 825155 := bstep (se 1 (by rfl) ⟨618866, by rfl⟩ : syracuseStep 825155 = 1237733) B1237733
theorem B366419 : Blo 362758 366419 := bstep (se 1 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 366419 = 549629) B549629
theorem B366435 : Blo 362758 366435 := bstep (se 1 (by rfl) ⟨274826, by rfl⟩ : syracuseStep 366435 = 549653) B549653
theorem B366451 : Blo 362758 366451 := bstep (se 1 (by rfl) ⟨274838, by rfl⟩ : syracuseStep 366451 = 549677) B549677
theorem B366467 : Blo 362758 366467 := bstep (se 1 (by rfl) ⟨274850, by rfl⟩ : syracuseStep 366467 = 549701) B549701
theorem B366483 : Blo 362758 366483 := bstep (se 1 (by rfl) ⟨274862, by rfl⟩ : syracuseStep 366483 = 549725) B549725
theorem B366499 : Blo 362758 366499 := bstep (se 1 (by rfl) ⟨274874, by rfl⟩ : syracuseStep 366499 = 549749) B549749
theorem B366515 : Blo 362758 366515 := bstep (se 1 (by rfl) ⟨274886, by rfl⟩ : syracuseStep 366515 = 549773) B549773
theorem B366531 : Blo 362758 366531 := bstep (se 1 (by rfl) ⟨274898, by rfl⟩ : syracuseStep 366531 = 549797) B549797
theorem B366547 : Blo 362758 366547 := bstep (se 1 (by rfl) ⟨274910, by rfl⟩ : syracuseStep 366547 = 549821) B549821
theorem B366563 : Blo 362758 366563 := bstep (se 1 (by rfl) ⟨274922, by rfl⟩ : syracuseStep 366563 = 549845) B549845
theorem B923633 : Blo 362758 923633 := bstep (se 2 (by rfl) ⟨346362, by rfl⟩ : syracuseStep 923633 = 692725) B692725
theorem B366579 : Blo 362758 366579 := bstep (se 1 (by rfl) ⟨274934, by rfl⟩ : syracuseStep 366579 = 549869) B549869
theorem B366595 : Blo 362758 366595 := bstep (se 1 (by rfl) ⟨274946, by rfl⟩ : syracuseStep 366595 = 549893) B549893
theorem B366611 : Blo 362758 366611 := bstep (se 1 (by rfl) ⟨274958, by rfl⟩ : syracuseStep 366611 = 549917) B549917
theorem B923683 : Blo 362758 923683 := bstep (se 1 (by rfl) ⟨692762, by rfl⟩ : syracuseStep 923683 = 1385525) B1385525
theorem B366627 : Blo 362758 366627 := bstep (se 1 (by rfl) ⟨274970, by rfl⟩ : syracuseStep 366627 = 549941) B549941
theorem B366643 : Blo 362758 366643 := bstep (se 1 (by rfl) ⟨274982, by rfl⟩ : syracuseStep 366643 = 549965) B549965
theorem B366659 : Blo 362758 366659 := bstep (se 1 (by rfl) ⟨274994, by rfl⟩ : syracuseStep 366659 = 549989) B549989
theorem B366675 : Blo 362758 366675 := bstep (se 1 (by rfl) ⟨275006, by rfl⟩ : syracuseStep 366675 = 550013) B550013
theorem B366691 : Blo 362758 366691 := bstep (se 1 (by rfl) ⟨275018, by rfl⟩ : syracuseStep 366691 = 550037) B550037
theorem B1579121 : Blo 362758 1579121 := bstep (se 2 (by rfl) ⟨592170, by rfl⟩ : syracuseStep 1579121 = 1184341) B1184341
theorem B366707 : Blo 362758 366707 := bstep (se 1 (by rfl) ⟨275030, by rfl⟩ : syracuseStep 366707 = 550061) B550061
theorem B694403 : Blo 362758 694403 := bstep (se 1 (by rfl) ⟨520802, by rfl⟩ : syracuseStep 694403 = 1041605) B1041605
theorem B366723 : Blo 362758 366723 := bstep (se 1 (by rfl) ⟨275042, by rfl⟩ : syracuseStep 366723 = 550085) B550085
theorem B366739 : Blo 362758 366739 := bstep (se 1 (by rfl) ⟨275054, by rfl⟩ : syracuseStep 366739 = 550109) B550109
theorem B366755 : Blo 362758 366755 := bstep (se 1 (by rfl) ⟨275066, by rfl⟩ : syracuseStep 366755 = 550133) B550133
theorem B923825 : Blo 362758 923825 := bstep (se 2 (by rfl) ⟨346434, by rfl⟩ : syracuseStep 923825 = 692869) B692869
theorem B1186289 : Blo 362758 1186289 := bstep (se 2 (by rfl) ⟨444858, by rfl⟩ : syracuseStep 1186289 = 889717) B889717
theorem B1841777 : Blo 362758 1841777 := bstep (se 2 (by rfl) ⟨690666, by rfl⟩ : syracuseStep 1841777 = 1381333) B1381333
theorem B1252049 : Blo 362758 1252049 := bstep (se 2 (by rfl) ⟨469518, by rfl⟩ : syracuseStep 1252049 = 939037) B939037
theorem B989965 : Blo 362758 989965 := bstep (se 3 (by rfl) ⟨185618, by rfl⟩ : syracuseStep 989965 = 371237) B371237
theorem B1055587 : Blo 362758 1055587 := bstep (se 1 (by rfl) ⟨791690, by rfl⟩ : syracuseStep 1055587 = 1583381) B1583381
theorem B990161 : Blo 362758 990161 := bstep (se 2 (by rfl) ⟨371310, by rfl⟩ : syracuseStep 990161 = 742621) B742621
theorem B695299 : Blo 362758 695299 := bstep (se 1 (by rfl) ⟨521474, by rfl⟩ : syracuseStep 695299 = 1042949) B1042949
theorem B924817 : Blo 362758 924817 := bstep (se 2 (by rfl) ⟨346806, by rfl⟩ : syracuseStep 924817 = 693613) B693613
theorem B695459 : Blo 362758 695459 := bstep (se 1 (by rfl) ⟨521594, by rfl⟩ : syracuseStep 695459 = 1043189) B1043189
theorem B1121539 : Blo 362758 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B925091 : Blo 362758 925091 := bstep (se 1 (by rfl) ⟨693818, by rfl⟩ : syracuseStep 925091 = 1387637) B1387637
theorem B925283 : Blo 362758 925283 := bstep (se 1 (by rfl) ⟨693962, by rfl⟩ : syracuseStep 925283 = 1387925) B1387925
theorem B1974221 : Blo 362758 1974221 := bstep (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) B740333
theorem B761827 : Blo 362758 761827 := bstep (se 1 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 761827 = 1142741) B1142741
theorem B1843235 : Blo 362758 1843235 := bstep (se 1 (by rfl) ⟨1382426, by rfl⟩ : syracuseStep 1843235 = 2764853) B2764853
theorem B1187875 : Blo 362758 1187875 := bstep (se 1 (by rfl) ⟨890906, by rfl⟩ : syracuseStep 1187875 = 1781813) B1781813
theorem B1745329 : Blo 362758 1745329 := bstep (se 2 (by rfl) ⟨654498, by rfl⟩ : syracuseStep 1745329 = 1308997) B1308997
theorem B926225 : Blo 362758 926225 := bstep (se 2 (by rfl) ⟨347334, by rfl⟩ : syracuseStep 926225 = 694669) B694669
theorem B1385009 : Blo 362758 1385009 := bstep (se 2 (by rfl) ⟨519378, by rfl⟩ : syracuseStep 1385009 = 1038757) B1038757
theorem B926275 : Blo 362758 926275 := bstep (se 1 (by rfl) ⟨694706, by rfl⟩ : syracuseStep 926275 = 1389413) B1389413
theorem B1122893 : Blo 362758 1122893 := bstep (se 3 (by rfl) ⟨210542, by rfl⟩ : syracuseStep 1122893 = 421085) B421085
theorem B369235 : Blo 362758 369235 := bstep (se 1 (by rfl) ⟨276926, by rfl⟩ : syracuseStep 369235 = 553853) B553853
theorem B926417 : Blo 362758 926417 := bstep (se 2 (by rfl) ⟨347406, by rfl⟩ : syracuseStep 926417 = 694813) B694813
theorem B1844045 : Blo 362758 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B1057805 : Blo 362758 1057805 := bstep (se 3 (by rfl) ⟨198338, by rfl⟩ : syracuseStep 1057805 = 396677) B396677
theorem B828643 : Blo 362758 828643 := bstep (se 1 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 828643 = 1242965) B1242965
theorem B2073869 : Blo 362758 2073869 := bstep (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) B777701
theorem B4368013 : Blo 362758 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B927409 : Blo 362758 927409 := bstep (se 2 (by rfl) ⟨347778, by rfl⟩ : syracuseStep 927409 = 695557) B695557
theorem B927683 : Blo 362758 927683 := bstep (se 1 (by rfl) ⟨695762, by rfl⟩ : syracuseStep 927683 = 1391525) B1391525
theorem B1386467 : Blo 362758 1386467 := bstep (se 1 (by rfl) ⟨1039850, by rfl⟩ : syracuseStep 1386467 = 2079701) B2079701
theorem B1747021 : Blo 362758 1747021 := bstep (se 3 (by rfl) ⟨327566, by rfl⟩ : syracuseStep 1747021 = 655133) B655133
theorem B927875 : Blo 362758 927875 := bstep (se 1 (by rfl) ⟨695906, by rfl⟩ : syracuseStep 927875 = 1391813) B1391813
theorem B1976561 : Blo 362758 1976561 := bstep (se 2 (by rfl) ⟨741210, by rfl⟩ : syracuseStep 1976561 = 1482421) B1482421
theorem B371027 : Blo 362758 371027 := bstep (se 1 (by rfl) ⟨278270, by rfl⟩ : syracuseStep 371027 = 556541) B556541
theorem B1747619 : Blo 362758 1747619 := bstep (se 1 (by rfl) ⟨1310714, by rfl⟩ : syracuseStep 1747619 = 2621429) B2621429
theorem B1387469 : Blo 362758 1387469 := bstep (se 3 (by rfl) ⟨260150, by rfl⟩ : syracuseStep 1387469 = 520301) B520301
theorem B1551473 : Blo 362758 1551473 := bstep (se 2 (by rfl) ⟨581802, by rfl⟩ : syracuseStep 1551473 = 1163605) B1163605
theorem B1748081 : Blo 362758 1748081 := bstep (se 2 (by rfl) ⟨655530, by rfl⟩ : syracuseStep 1748081 = 1311061) B1311061
theorem B2076101 : Blo 362758 2076101 := bstep (se 4 (by rfl) ⟨194634, by rfl⟩ : syracuseStep 2076101 = 389269) B389269
theorem B601553 : Blo 362758 601553 := bstep (se 2 (by rfl) ⟨225582, by rfl⟩ : syracuseStep 601553 = 451165) B451165
theorem B699907 : Blo 362758 699907 := bstep (se 1 (by rfl) ⟨524930, by rfl⟩ : syracuseStep 699907 = 1049861) B1049861
theorem B831043 : Blo 362758 831043 := bstep (se 1 (by rfl) ⟨623282, by rfl⟩ : syracuseStep 831043 = 1246565) B1246565
theorem B1846961 : Blo 362758 1846961 := bstep (se 2 (by rfl) ⟨692610, by rfl⟩ : syracuseStep 1846961 = 1385221) B1385221
theorem B1224557 : Blo 362758 1224557 := bstep (se 3 (by rfl) ⟨229604, by rfl⟩ : syracuseStep 1224557 = 459209) B459209
theorem B1224611 : Blo 362758 1224611 := bstep (se 1 (by rfl) ⟨918458, by rfl⟩ : syracuseStep 1224611 = 1836917) B1836917
theorem B2633741 : Blo 362758 2633741 := bstep (se 3 (by rfl) ⟨493826, by rfl⟩ : syracuseStep 2633741 = 987653) B987653
theorem B2076785 : Blo 362758 2076785 := bstep (se 2 (by rfl) ⟨778794, by rfl⟩ : syracuseStep 2076785 = 1557589) B1557589
theorem B1224881 : Blo 362758 1224881 := bstep (se 2 (by rfl) ⟨459330, by rfl⟩ : syracuseStep 1224881 = 918661) B918661
theorem B832145 : Blo 362758 832145 := bstep (se 2 (by rfl) ⟨312054, by rfl⟩ : syracuseStep 832145 = 624109) B624109
theorem B4207285 : Blo 362758 4207285 := bstep (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) B394433
theorem B1225421 : Blo 362758 1225421 := bstep (se 3 (by rfl) ⟨229766, by rfl⟩ : syracuseStep 1225421 = 459533) B459533
theorem B1225475 : Blo 362758 1225475 := bstep (se 1 (by rfl) ⟨919106, by rfl⟩ : syracuseStep 1225475 = 1838213) B1838213
theorem B1553165 : Blo 362758 1553165 := bstep (se 3 (by rfl) ⟨291218, by rfl⟩ : syracuseStep 1553165 = 582437) B582437
theorem B439139 : Blo 362758 439139 := bstep (se 1 (by rfl) ⟨329354, by rfl⟩ : syracuseStep 439139 = 658709) B658709
theorem B2569073 : Blo 362758 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B1389581 : Blo 362758 1389581 := bstep (se 3 (by rfl) ⟨260546, by rfl⟩ : syracuseStep 1389581 = 521093) B521093
theorem B1225745 : Blo 362758 1225745 := bstep (se 2 (by rfl) ⟨459654, by rfl⟩ : syracuseStep 1225745 = 919309) B919309
theorem B832547 : Blo 362758 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B701507 : Blo 362758 701507 := bstep (se 1 (by rfl) ⟨526130, by rfl⟩ : syracuseStep 701507 = 1052261) B1052261
theorem B1848419 : Blo 362758 1848419 := bstep (se 1 (by rfl) ⟨1386314, by rfl⟩ : syracuseStep 1848419 = 2772629) B2772629
theorem B2078243 : Blo 362758 2078243 := bstep (se 1 (by rfl) ⟨1558682, by rfl⟩ : syracuseStep 2078243 = 3117365) B3117365
theorem B1226285 : Blo 362758 1226285 := bstep (se 3 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 1226285 = 459857) B459857
theorem B1226339 : Blo 362758 1226339 := bstep (se 1 (by rfl) ⟨919754, by rfl⟩ : syracuseStep 1226339 = 1839509) B1839509
theorem B2340485 : Blo 362758 2340485 := bstep (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) B438841
theorem B1390385 : Blo 362758 1390385 := bstep (se 2 (by rfl) ⟨521394, by rfl⟩ : syracuseStep 1390385 = 1042789) B1042789
theorem B1226609 : Blo 362758 1226609 := bstep (se 2 (by rfl) ⟨459978, by rfl⟩ : syracuseStep 1226609 = 919957) B919957
theorem B1849229 : Blo 362758 1849229 := bstep (se 3 (by rfl) ⟨346730, by rfl⟩ : syracuseStep 1849229 = 693461) B693461
theorem B3946805 : Blo 362758 3946805 := bstep (se 5 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 3946805 = 370013) B370013
theorem B1227149 : Blo 362758 1227149 := bstep (se 3 (by rfl) ⟨230090, by rfl⟩ : syracuseStep 1227149 = 460181) B460181
theorem B1227203 : Blo 362758 1227203 := bstep (se 1 (by rfl) ⟨920402, by rfl⟩ : syracuseStep 1227203 = 1840805) B1840805
theorem B3488197 : Blo 362758 3488197 := bstep (se 4 (by rfl) ⟨327018, by rfl⟩ : syracuseStep 3488197 = 654037) B654037
theorem B5257669 : Blo 362758 5257669 := bstep (se 4 (by rfl) ⟨492906, by rfl⟩ : syracuseStep 5257669 = 985813) B985813
theorem B1391053 : Blo 362758 1391053 := bstep (se 3 (by rfl) ⟨260822, by rfl⟩ : syracuseStep 1391053 = 521645) B521645
theorem B375251 : Blo 362758 375251 := bstep (se 1 (by rfl) ⟨281438, by rfl⟩ : syracuseStep 375251 = 562877) B562877
theorem B408163 : Blo 362758 408163 := bstep (se 1 (by rfl) ⟨306122, by rfl⟩ : syracuseStep 408163 = 612245) B612245
theorem B735875 : Blo 362758 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B1227473 : Blo 362758 1227473 := bstep (se 2 (by rfl) ⟨460302, by rfl⟩ : syracuseStep 1227473 = 920605) B920605
theorem B408307 : Blo 362758 408307 := bstep (se 1 (by rfl) ⟨306230, by rfl⟩ : syracuseStep 408307 = 612461) B612461
theorem B408451 : Blo 362758 408451 := bstep (se 1 (by rfl) ⟨306338, by rfl⟩ : syracuseStep 408451 = 612677) B612677
theorem B1424269 : Blo 362758 1424269 := bstep (se 3 (by rfl) ⟨267050, by rfl⟩ : syracuseStep 1424269 = 534101) B534101
theorem B1981361 : Blo 362758 1981361 := bstep (se 2 (by rfl) ⟨743010, by rfl⟩ : syracuseStep 1981361 = 1486021) B1486021
theorem B408595 : Blo 362758 408595 := bstep (se 1 (by rfl) ⟨306446, by rfl⟩ : syracuseStep 408595 = 612893) B612893
theorem B4668515 : Blo 362758 4668515 := bstep (se 1 (by rfl) ⟨3501386, by rfl⟩ : syracuseStep 4668515 = 7002773) B7002773
theorem B408739 : Blo 362758 408739 := bstep (se 1 (by rfl) ⟨306554, by rfl⟩ : syracuseStep 408739 = 613109) B613109
theorem B2964707 : Blo 362758 2964707 := bstep (se 1 (by rfl) ⟨2223530, by rfl⟩ : syracuseStep 2964707 = 4447061) B4447061
theorem B1391843 : Blo 362758 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B1228013 : Blo 362758 1228013 := bstep (se 3 (by rfl) ⟨230252, by rfl⟩ : syracuseStep 1228013 = 460505) B460505
theorem B1228067 : Blo 362758 1228067 := bstep (se 1 (by rfl) ⟨921050, by rfl⟩ : syracuseStep 1228067 = 1842101) B1842101
theorem B408883 : Blo 362758 408883 := bstep (se 1 (by rfl) ⟨306662, by rfl⟩ : syracuseStep 408883 = 613325) B613325
theorem B409027 : Blo 362758 409027 := bstep (se 1 (by rfl) ⟨306770, by rfl⟩ : syracuseStep 409027 = 613541) B613541
theorem B1228337 : Blo 362758 1228337 := bstep (se 2 (by rfl) ⟨460626, by rfl⟩ : syracuseStep 1228337 = 921253) B921253
theorem B409171 : Blo 362758 409171 := bstep (se 1 (by rfl) ⟨306878, by rfl⟩ : syracuseStep 409171 = 613757) B613757
theorem B409315 : Blo 362758 409315 := bstep (se 1 (by rfl) ⟨306986, by rfl⟩ : syracuseStep 409315 = 613973) B613973
theorem B1392497 : Blo 362758 1392497 := bstep (se 2 (by rfl) ⟨522186, by rfl⟩ : syracuseStep 1392497 = 1044373) B1044373
theorem B409459 : Blo 362758 409459 := bstep (se 1 (by rfl) ⟨307094, by rfl⟩ : syracuseStep 409459 = 614189) B614189
theorem B737219 : Blo 362758 737219 := bstep (se 1 (by rfl) ⟨552914, by rfl⟩ : syracuseStep 737219 = 1105829) B1105829
theorem B4145093 : Blo 362758 4145093 := bstep (se 4 (by rfl) ⟨388602, by rfl⟩ : syracuseStep 4145093 = 777205) B777205
theorem B409603 : Blo 362758 409603 := bstep (se 1 (by rfl) ⟨307202, by rfl⟩ : syracuseStep 409603 = 614405) B614405
theorem B1228877 : Blo 362758 1228877 := bstep (se 3 (by rfl) ⟨230414, by rfl⟩ : syracuseStep 1228877 = 460829) B460829
theorem B1228931 : Blo 362758 1228931 := bstep (se 1 (by rfl) ⟨921698, by rfl⟩ : syracuseStep 1228931 = 1843397) B1843397
theorem B409747 : Blo 362758 409747 := bstep (se 1 (by rfl) ⟨307310, by rfl⟩ : syracuseStep 409747 = 614621) B614621
theorem B409891 : Blo 362758 409891 := bstep (se 1 (by rfl) ⟨307418, by rfl⟩ : syracuseStep 409891 = 614837) B614837
theorem B1229201 : Blo 362758 1229201 := bstep (se 2 (by rfl) ⟨460950, by rfl⟩ : syracuseStep 1229201 = 921901) B921901
theorem B410035 : Blo 362758 410035 := bstep (se 1 (by rfl) ⟨307526, by rfl⟩ : syracuseStep 410035 = 615053) B615053
theorem B1163747 : Blo 362758 1163747 := bstep (se 1 (by rfl) ⟨872810, by rfl⟩ : syracuseStep 1163747 = 1745621) B1745621
theorem B410179 : Blo 362758 410179 := bstep (se 1 (by rfl) ⟨307634, by rfl⟩ : syracuseStep 410179 = 615269) B615269
theorem B1786445 : Blo 362758 1786445 := bstep (se 3 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 1786445 = 669917) B669917
theorem B803441 : Blo 362758 803441 := bstep (se 2 (by rfl) ⟨301290, by rfl⟩ : syracuseStep 803441 = 602581) B602581
theorem B2081477 : Blo 362758 2081477 := bstep (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) B390277
theorem B410323 : Blo 362758 410323 := bstep (se 1 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 410323 = 615485) B615485
theorem B1852145 : Blo 362758 1852145 := bstep (se 2 (by rfl) ⟨694554, by rfl⟩ : syracuseStep 1852145 = 1389109) B1389109
theorem B410467 : Blo 362758 410467 := bstep (se 1 (by rfl) ⟨307850, by rfl⟩ : syracuseStep 410467 = 615701) B615701
theorem B1229741 : Blo 362758 1229741 := bstep (se 3 (by rfl) ⟨230576, by rfl⟩ : syracuseStep 1229741 = 461153) B461153
theorem B1229795 : Blo 362758 1229795 := bstep (se 1 (by rfl) ⟨922346, by rfl⟩ : syracuseStep 1229795 = 1844693) B1844693
theorem B410611 : Blo 362758 410611 := bstep (se 1 (by rfl) ⟨307958, by rfl⟩ : syracuseStep 410611 = 615917) B615917
theorem B1557539 : Blo 362758 1557539 := bstep (se 1 (by rfl) ⟨1168154, by rfl⟩ : syracuseStep 1557539 = 2336309) B2336309
theorem B410755 : Blo 362758 410755 := bstep (se 1 (by rfl) ⟨308066, by rfl⟩ : syracuseStep 410755 = 616133) B616133
theorem B2081933 : Blo 362758 2081933 := bstep (se 3 (by rfl) ⟨390362, by rfl⟩ : syracuseStep 2081933 = 780725) B780725
theorem B2344099 : Blo 362758 2344099 := bstep (se 1 (by rfl) ⟨1758074, by rfl⟩ : syracuseStep 2344099 = 3516149) B3516149
theorem B1230065 : Blo 362758 1230065 := bstep (se 2 (by rfl) ⟨461274, by rfl⟩ : syracuseStep 1230065 = 922549) B922549
theorem B410899 : Blo 362758 410899 := bstep (se 1 (by rfl) ⟨308174, by rfl⟩ : syracuseStep 410899 = 616349) B616349
theorem B411043 : Blo 362758 411043 := bstep (se 1 (by rfl) ⟨308282, by rfl⟩ : syracuseStep 411043 = 616565) B616565
theorem B411187 : Blo 362758 411187 := bstep (se 1 (by rfl) ⟨308390, by rfl⟩ : syracuseStep 411187 = 616781) B616781
theorem B1033859 : Blo 362758 1033859 := bstep (se 1 (by rfl) ⟨775394, by rfl⟩ : syracuseStep 1033859 = 1550789) B1550789
theorem B411331 : Blo 362758 411331 := bstep (se 1 (by rfl) ⟨308498, by rfl⟩ : syracuseStep 411331 = 616997) B616997
theorem B1230605 : Blo 362758 1230605 := bstep (se 3 (by rfl) ⟨230738, by rfl⟩ : syracuseStep 1230605 = 461477) B461477
theorem B1230659 : Blo 362758 1230659 := bstep (se 1 (by rfl) ⟨922994, by rfl⟩ : syracuseStep 1230659 = 1845989) B1845989
theorem B411475 : Blo 362758 411475 := bstep (se 1 (by rfl) ⟨308606, by rfl⟩ : syracuseStep 411475 = 617213) B617213
theorem B411619 : Blo 362758 411619 := bstep (se 1 (by rfl) ⟨308714, by rfl⟩ : syracuseStep 411619 = 617429) B617429
theorem B1230929 : Blo 362758 1230929 := bstep (se 2 (by rfl) ⟨461598, by rfl⟩ : syracuseStep 1230929 = 923197) B923197
theorem B411763 : Blo 362758 411763 := bstep (se 1 (by rfl) ⟨308822, by rfl⟩ : syracuseStep 411763 = 617645) B617645
theorem B739459 : Blo 362758 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B1853603 : Blo 362758 1853603 := bstep (se 1 (by rfl) ⟨1390202, by rfl⟩ : syracuseStep 1853603 = 2780405) B2780405
theorem B739523 : Blo 362758 739523 := bstep (se 1 (by rfl) ⟨554642, by rfl⟩ : syracuseStep 739523 = 1109285) B1109285
theorem B2771171 : Blo 362758 2771171 := bstep (se 1 (by rfl) ⟨2078378, by rfl⟩ : syracuseStep 2771171 = 4156757) B4156757
theorem B1165553 : Blo 362758 1165553 := bstep (se 2 (by rfl) ⟨437082, by rfl⟩ : syracuseStep 1165553 = 874165) B874165
theorem B411907 : Blo 362758 411907 := bstep (se 1 (by rfl) ⟨308930, by rfl⟩ : syracuseStep 411907 = 617861) B617861
theorem B1165603 : Blo 362758 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B412051 : Blo 362758 412051 := bstep (se 1 (by rfl) ⟨309038, by rfl⟩ : syracuseStep 412051 = 618077) B618077
theorem B412195 : Blo 362758 412195 := bstep (se 1 (by rfl) ⟨309146, by rfl⟩ : syracuseStep 412195 = 618293) B618293
theorem B1231469 : Blo 362758 1231469 := bstep (se 3 (by rfl) ⟨230900, by rfl⟩ : syracuseStep 1231469 = 461801) B461801
theorem B3361421 : Blo 362758 3361421 := bstep (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) B1260533
theorem B1231523 : Blo 362758 1231523 := bstep (se 1 (by rfl) ⟨923642, by rfl⟩ : syracuseStep 1231523 = 1847285) B1847285
theorem B412339 : Blo 362758 412339 := bstep (se 1 (by rfl) ⟨309254, by rfl⟩ : syracuseStep 412339 = 618509) B618509
theorem B412483 : Blo 362758 412483 := bstep (se 1 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 412483 = 618725) B618725
theorem B1035089 : Blo 362758 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B1231793 : Blo 362758 1231793 := bstep (se 2 (by rfl) ⟨461922, by rfl⟩ : syracuseStep 1231793 = 923845) B923845
theorem B1854413 : Blo 362758 1854413 := bstep (se 3 (by rfl) ⟨347702, by rfl⟩ : syracuseStep 1854413 = 695405) B695405
theorem B1166321 : Blo 362758 1166321 := bstep (se 2 (by rfl) ⟨437370, by rfl⟩ : syracuseStep 1166321 = 874741) B874741
theorem B1559537 : Blo 362758 1559537 := bstep (se 2 (by rfl) ⟨584826, by rfl⟩ : syracuseStep 1559537 = 1169653) B1169653
theorem B740497 : Blo 362758 740497 := bstep (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) B555373
theorem B544145 : Blo 362758 544145 := bstep (se 2 (by rfl) ⟨204054, by rfl⟩ : syracuseStep 544145 = 408109) B408109
theorem B544163 : Blo 362758 544163 := bstep (se 1 (by rfl) ⟨408122, by rfl⟩ : syracuseStep 544163 = 816245) B816245
theorem B544193 : Blo 362758 544193 := bstep (se 2 (by rfl) ⟨204072, by rfl⟩ : syracuseStep 544193 = 408145) B408145
theorem B2641349 : Blo 362758 2641349 := bstep (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) B495253
theorem B1232333 : Blo 362758 1232333 := bstep (se 3 (by rfl) ⟨231062, by rfl⟩ : syracuseStep 1232333 = 462125) B462125
theorem B544211 : Blo 362758 544211 := bstep (se 1 (by rfl) ⟨408158, by rfl⟩ : syracuseStep 544211 = 816317) B816317
theorem B544241 : Blo 362758 544241 := bstep (se 2 (by rfl) ⟨204090, by rfl⟩ : syracuseStep 544241 = 408181) B408181
theorem B1166833 : Blo 362758 1166833 := bstep (se 2 (by rfl) ⟨437562, by rfl⟩ : syracuseStep 1166833 = 875125) B875125
theorem B544259 : Blo 362758 544259 := bstep (se 1 (by rfl) ⟨408194, by rfl⟩ : syracuseStep 544259 = 816389) B816389
theorem B1232387 : Blo 362758 1232387 := bstep (se 1 (by rfl) ⟨924290, by rfl⟩ : syracuseStep 1232387 = 1848581) B1848581
theorem B544289 : Blo 362758 544289 := bstep (se 2 (by rfl) ⟨204108, by rfl⟩ : syracuseStep 544289 = 408217) B408217
theorem B544307 : Blo 362758 544307 := bstep (se 1 (by rfl) ⟨408230, by rfl⟩ : syracuseStep 544307 = 816461) B816461
theorem B544337 : Blo 362758 544337 := bstep (se 2 (by rfl) ⟨204126, by rfl⟩ : syracuseStep 544337 = 408253) B408253
theorem B544355 : Blo 362758 544355 := bstep (se 1 (by rfl) ⟨408266, by rfl⟩ : syracuseStep 544355 = 816533) B816533
theorem B3001969 : Blo 362758 3001969 := bstep (se 2 (by rfl) ⟨1125738, by rfl⟩ : syracuseStep 3001969 = 2251477) B2251477
theorem B544385 : Blo 362758 544385 := bstep (se 2 (by rfl) ⟨204144, by rfl⟩ : syracuseStep 544385 = 408289) B408289
theorem B544403 : Blo 362758 544403 := bstep (se 1 (by rfl) ⟨408302, by rfl⟩ : syracuseStep 544403 = 816605) B816605
theorem B544433 : Blo 362758 544433 := bstep (se 2 (by rfl) ⟨204162, by rfl⟩ : syracuseStep 544433 = 408325) B408325
theorem B544451 : Blo 362758 544451 := bstep (se 1 (by rfl) ⟨408338, by rfl⟩ : syracuseStep 544451 = 816677) B816677
theorem B544481 : Blo 362758 544481 := bstep (se 2 (by rfl) ⟨204180, by rfl⟩ : syracuseStep 544481 = 408361) B408361
theorem B544499 : Blo 362758 544499 := bstep (se 1 (by rfl) ⟨408374, by rfl⟩ : syracuseStep 544499 = 816749) B816749
theorem B544529 : Blo 362758 544529 := bstep (se 2 (by rfl) ⟨204198, by rfl⟩ : syracuseStep 544529 = 408397) B408397
theorem B1232657 : Blo 362758 1232657 := bstep (se 2 (by rfl) ⟨462246, by rfl⟩ : syracuseStep 1232657 = 924493) B924493
theorem B544547 : Blo 362758 544547 := bstep (se 1 (by rfl) ⟨408410, by rfl⟩ : syracuseStep 544547 = 816821) B816821
theorem B741169 : Blo 362758 741169 := bstep (se 2 (by rfl) ⟨277938, by rfl⟩ : syracuseStep 741169 = 555877) B555877
theorem B544577 : Blo 362758 544577 := bstep (se 2 (by rfl) ⟨204216, by rfl⟩ : syracuseStep 544577 = 408433) B408433
theorem B544595 : Blo 362758 544595 := bstep (se 1 (by rfl) ⟨408446, by rfl⟩ : syracuseStep 544595 = 816893) B816893
theorem B544625 : Blo 362758 544625 := bstep (se 2 (by rfl) ⟨204234, by rfl⟩ : syracuseStep 544625 = 408469) B408469
theorem B544643 : Blo 362758 544643 := bstep (se 1 (by rfl) ⟨408482, by rfl⟩ : syracuseStep 544643 = 816965) B816965
theorem B2346893 : Blo 362758 2346893 := bstep (se 3 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 2346893 = 880085) B880085
theorem B544673 : Blo 362758 544673 := bstep (se 2 (by rfl) ⟨204252, by rfl⟩ : syracuseStep 544673 = 408505) B408505
theorem B544691 : Blo 362758 544691 := bstep (se 1 (by rfl) ⟨408518, by rfl⟩ : syracuseStep 544691 = 817037) B817037
theorem B544721 : Blo 362758 544721 := bstep (se 2 (by rfl) ⟨204270, by rfl⟩ : syracuseStep 544721 = 408541) B408541
theorem B544739 : Blo 362758 544739 := bstep (se 1 (by rfl) ⟨408554, by rfl⟩ : syracuseStep 544739 = 817109) B817109
theorem B937969 : Blo 362758 937969 := bstep (se 2 (by rfl) ⟨351738, by rfl⟩ : syracuseStep 937969 = 703477) B703477
theorem B2084849 : Blo 362758 2084849 := bstep (se 2 (by rfl) ⟨781818, by rfl⟩ : syracuseStep 2084849 = 1563637) B1563637
theorem B544769 : Blo 362758 544769 := bstep (se 2 (by rfl) ⟨204288, by rfl⟩ : syracuseStep 544769 = 408577) B408577
theorem B544787 : Blo 362758 544787 := bstep (se 1 (by rfl) ⟨408590, by rfl⟩ : syracuseStep 544787 = 817181) B817181
theorem B544817 : Blo 362758 544817 := bstep (se 2 (by rfl) ⟨204306, by rfl⟩ : syracuseStep 544817 = 408613) B408613
theorem B544835 : Blo 362758 544835 := bstep (se 1 (by rfl) ⟨408626, by rfl⟩ : syracuseStep 544835 = 817253) B817253
theorem B544865 : Blo 362758 544865 := bstep (se 2 (by rfl) ⟨204324, by rfl⟩ : syracuseStep 544865 = 408649) B408649
theorem B544883 : Blo 362758 544883 := bstep (se 1 (by rfl) ⟨408662, by rfl⟩ : syracuseStep 544883 = 817325) B817325
theorem B872579 : Blo 362758 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B544913 : Blo 362758 544913 := bstep (se 2 (by rfl) ⟨204342, by rfl⟩ : syracuseStep 544913 = 408685) B408685
theorem B413843 : Blo 362758 413843 := bstep (se 1 (by rfl) ⟨310382, by rfl⟩ : syracuseStep 413843 = 620765) B620765
theorem B544931 : Blo 362758 544931 := bstep (se 1 (by rfl) ⟨408698, by rfl⟩ : syracuseStep 544931 = 817397) B817397
theorem B544961 : Blo 362758 544961 := bstep (se 2 (by rfl) ⟨204360, by rfl⟩ : syracuseStep 544961 = 408721) B408721
theorem B544979 : Blo 362758 544979 := bstep (se 1 (by rfl) ⟨408734, by rfl⟩ : syracuseStep 544979 = 817469) B817469
theorem B545009 : Blo 362758 545009 := bstep (se 2 (by rfl) ⟨204378, by rfl⟩ : syracuseStep 545009 = 408757) B408757
theorem B545027 : Blo 362758 545027 := bstep (se 1 (by rfl) ⟨408770, by rfl⟩ : syracuseStep 545027 = 817541) B817541
theorem B1036547 : Blo 362758 1036547 := bstep (se 1 (by rfl) ⟨777410, by rfl⟩ : syracuseStep 1036547 = 1554821) B1554821
theorem B545057 : Blo 362758 545057 := bstep (se 2 (by rfl) ⟨204396, by rfl⟩ : syracuseStep 545057 = 408793) B408793
theorem B1233197 : Blo 362758 1233197 := bstep (se 3 (by rfl) ⟨231224, by rfl⟩ : syracuseStep 1233197 = 462449) B462449
theorem B1364273 : Blo 362758 1364273 := bstep (se 2 (by rfl) ⟨511602, by rfl⟩ : syracuseStep 1364273 = 1023205) B1023205
theorem B545075 : Blo 362758 545075 := bstep (se 1 (by rfl) ⟨408806, by rfl⟩ : syracuseStep 545075 = 817613) B817613
theorem B545105 : Blo 362758 545105 := bstep (se 2 (by rfl) ⟨204414, by rfl⟩ : syracuseStep 545105 = 408829) B408829
theorem B545123 : Blo 362758 545123 := bstep (se 1 (by rfl) ⟨408842, by rfl⟩ : syracuseStep 545123 = 817685) B817685
theorem B1233251 : Blo 362758 1233251 := bstep (se 1 (by rfl) ⟨924938, by rfl⟩ : syracuseStep 1233251 = 1849877) B1849877
theorem B545153 : Blo 362758 545153 := bstep (se 2 (by rfl) ⟨204432, by rfl⟩ : syracuseStep 545153 = 408865) B408865
theorem B545171 : Blo 362758 545171 := bstep (se 1 (by rfl) ⟨408878, by rfl⟩ : syracuseStep 545171 = 817757) B817757
theorem B545201 : Blo 362758 545201 := bstep (se 2 (by rfl) ⟨204450, by rfl⟩ : syracuseStep 545201 = 408901) B408901
theorem B545219 : Blo 362758 545219 := bstep (se 1 (by rfl) ⟨408914, by rfl⟩ : syracuseStep 545219 = 817829) B817829
theorem B17125829 : Blo 362758 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B545249 : Blo 362758 545249 := bstep (se 2 (by rfl) ⟨204468, by rfl⟩ : syracuseStep 545249 = 408937) B408937
theorem B545267 : Blo 362758 545267 := bstep (se 1 (by rfl) ⟨408950, by rfl⟩ : syracuseStep 545267 = 817901) B817901
theorem B545297 : Blo 362758 545297 := bstep (se 2 (by rfl) ⟨204486, by rfl⟩ : syracuseStep 545297 = 408973) B408973
theorem B545315 : Blo 362758 545315 := bstep (se 1 (by rfl) ⟨408986, by rfl⟩ : syracuseStep 545315 = 817973) B817973
theorem B545345 : Blo 362758 545345 := bstep (se 2 (by rfl) ⟨204504, by rfl⟩ : syracuseStep 545345 = 409009) B409009
theorem B1167949 : Blo 362758 1167949 := bstep (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) B437981
theorem B545363 : Blo 362758 545363 := bstep (se 1 (by rfl) ⟨409022, by rfl⟩ : syracuseStep 545363 = 818045) B818045
theorem B545393 : Blo 362758 545393 := bstep (se 2 (by rfl) ⟨204522, by rfl⟩ : syracuseStep 545393 = 409045) B409045
theorem B1233521 : Blo 362758 1233521 := bstep (se 2 (by rfl) ⟨462570, by rfl⟩ : syracuseStep 1233521 = 925141) B925141
theorem B545411 : Blo 362758 545411 := bstep (se 1 (by rfl) ⟨409058, by rfl⟩ : syracuseStep 545411 = 818117) B818117
theorem B1168013 : Blo 362758 1168013 := bstep (se 3 (by rfl) ⟨219002, by rfl⟩ : syracuseStep 1168013 = 438005) B438005
theorem B545441 : Blo 362758 545441 := bstep (se 2 (by rfl) ⟨204540, by rfl⟩ : syracuseStep 545441 = 409081) B409081
theorem B545459 : Blo 362758 545459 := bstep (se 1 (by rfl) ⟨409094, by rfl⟩ : syracuseStep 545459 = 818189) B818189
theorem B545489 : Blo 362758 545489 := bstep (se 2 (by rfl) ⟨204558, by rfl⟩ : syracuseStep 545489 = 409117) B409117
theorem B545507 : Blo 362758 545507 := bstep (se 1 (by rfl) ⟨409130, by rfl⟩ : syracuseStep 545507 = 818261) B818261
theorem B545537 : Blo 362758 545537 := bstep (se 2 (by rfl) ⟨204576, by rfl⟩ : syracuseStep 545537 = 409153) B409153
theorem B545555 : Blo 362758 545555 := bstep (se 1 (by rfl) ⟨409166, by rfl⟩ : syracuseStep 545555 = 818333) B818333
theorem B545585 : Blo 362758 545585 := bstep (se 2 (by rfl) ⟨204594, by rfl⟩ : syracuseStep 545585 = 409189) B409189
theorem B545603 : Blo 362758 545603 := bstep (se 1 (by rfl) ⟨409202, by rfl⟩ : syracuseStep 545603 = 818405) B818405
theorem B545633 : Blo 362758 545633 := bstep (se 2 (by rfl) ⟨204612, by rfl⟩ : syracuseStep 545633 = 409225) B409225
theorem B545651 : Blo 362758 545651 := bstep (se 1 (by rfl) ⟨409238, by rfl⟩ : syracuseStep 545651 = 818477) B818477
theorem B545681 : Blo 362758 545681 := bstep (se 2 (by rfl) ⟨204630, by rfl⟩ : syracuseStep 545681 = 409261) B409261
theorem B545699 : Blo 362758 545699 := bstep (se 1 (by rfl) ⟨409274, by rfl⟩ : syracuseStep 545699 = 818549) B818549
theorem B545729 : Blo 362758 545729 := bstep (se 2 (by rfl) ⟨204648, by rfl⟩ : syracuseStep 545729 = 409297) B409297
theorem B545747 : Blo 362758 545747 := bstep (se 1 (by rfl) ⟨409310, by rfl⟩ : syracuseStep 545747 = 818621) B818621
theorem B545777 : Blo 362758 545777 := bstep (se 2 (by rfl) ⟨204666, by rfl⟩ : syracuseStep 545777 = 409333) B409333
theorem B545795 : Blo 362758 545795 := bstep (se 1 (by rfl) ⟨409346, by rfl⟩ : syracuseStep 545795 = 818693) B818693
theorem B545825 : Blo 362758 545825 := bstep (se 2 (by rfl) ⟨204684, by rfl⟩ : syracuseStep 545825 = 409369) B409369
theorem B1037357 : Blo 362758 1037357 := bstep (se 3 (by rfl) ⟨194504, by rfl⟩ : syracuseStep 1037357 = 389009) B389009
theorem B545843 : Blo 362758 545843 := bstep (se 1 (by rfl) ⟨409382, by rfl⟩ : syracuseStep 545843 = 818765) B818765
theorem B545873 : Blo 362758 545873 := bstep (se 2 (by rfl) ⟨204702, by rfl⟩ : syracuseStep 545873 = 409405) B409405
theorem B545891 : Blo 362758 545891 := bstep (se 1 (by rfl) ⟨409418, by rfl⟩ : syracuseStep 545891 = 818837) B818837
theorem B545921 : Blo 362758 545921 := bstep (se 2 (by rfl) ⟨204720, by rfl⟩ : syracuseStep 545921 = 409441) B409441
theorem B1234061 : Blo 362758 1234061 := bstep (se 3 (by rfl) ⟨231386, by rfl⟩ : syracuseStep 1234061 = 462773) B462773
theorem B545939 : Blo 362758 545939 := bstep (se 1 (by rfl) ⟨409454, by rfl⟩ : syracuseStep 545939 = 818909) B818909
theorem B545969 : Blo 362758 545969 := bstep (se 2 (by rfl) ⟨204738, by rfl⟩ : syracuseStep 545969 = 409477) B409477
theorem B1135811 : Blo 362758 1135811 := bstep (se 1 (by rfl) ⟨851858, by rfl⟩ : syracuseStep 1135811 = 1703717) B1703717
theorem B545987 : Blo 362758 545987 := bstep (se 1 (by rfl) ⟨409490, by rfl⟩ : syracuseStep 545987 = 818981) B818981
theorem B1234115 : Blo 362758 1234115 := bstep (se 1 (by rfl) ⟨925586, by rfl⟩ : syracuseStep 1234115 = 1851173) B1851173
theorem B546017 : Blo 362758 546017 := bstep (se 2 (by rfl) ⟨204756, by rfl⟩ : syracuseStep 546017 = 409513) B409513
theorem B1037549 : Blo 362758 1037549 := bstep (se 3 (by rfl) ⟨194540, by rfl⟩ : syracuseStep 1037549 = 389081) B389081
theorem B546035 : Blo 362758 546035 := bstep (se 1 (by rfl) ⟨409526, by rfl⟩ : syracuseStep 546035 = 819053) B819053
theorem B546065 : Blo 362758 546065 := bstep (se 2 (by rfl) ⟨204774, by rfl⟩ : syracuseStep 546065 = 409549) B409549
theorem B546083 : Blo 362758 546083 := bstep (se 1 (by rfl) ⟨409562, by rfl⟩ : syracuseStep 546083 = 819125) B819125
theorem B546113 : Blo 362758 546113 := bstep (se 2 (by rfl) ⟨204792, by rfl⟩ : syracuseStep 546113 = 409585) B409585
theorem B546131 : Blo 362758 546131 := bstep (se 1 (by rfl) ⟨409598, by rfl⟩ : syracuseStep 546131 = 819197) B819197
theorem B546161 : Blo 362758 546161 := bstep (se 2 (by rfl) ⟨204810, by rfl⟩ : syracuseStep 546161 = 409621) B409621
theorem B546179 : Blo 362758 546179 := bstep (se 1 (by rfl) ⟨409634, by rfl⟩ : syracuseStep 546179 = 819269) B819269
theorem B1561997 : Blo 362758 1561997 := bstep (se 3 (by rfl) ⟨292874, by rfl⟩ : syracuseStep 1561997 = 585749) B585749
theorem B546209 : Blo 362758 546209 := bstep (se 2 (by rfl) ⟨204828, by rfl⟩ : syracuseStep 546209 = 409657) B409657
theorem B2086307 : Blo 362758 2086307 := bstep (se 1 (by rfl) ⟨1564730, by rfl⟩ : syracuseStep 2086307 = 3129461) B3129461
theorem B546227 : Blo 362758 546227 := bstep (se 1 (by rfl) ⟨409670, by rfl⟩ : syracuseStep 546227 = 819341) B819341
theorem B546257 : Blo 362758 546257 := bstep (se 2 (by rfl) ⟨204846, by rfl⟩ : syracuseStep 546257 = 409693) B409693
theorem B1234385 : Blo 362758 1234385 := bstep (se 2 (by rfl) ⟨462894, by rfl⟩ : syracuseStep 1234385 = 925789) B925789
theorem B775651 : Blo 362758 775651 := bstep (se 1 (by rfl) ⟨581738, by rfl⟩ : syracuseStep 775651 = 1163477) B1163477
theorem B546275 : Blo 362758 546275 := bstep (se 1 (by rfl) ⟨409706, by rfl⟩ : syracuseStep 546275 = 819413) B819413
theorem B546305 : Blo 362758 546305 := bstep (se 2 (by rfl) ⟨204864, by rfl⟩ : syracuseStep 546305 = 409729) B409729
theorem B546323 : Blo 362758 546323 := bstep (se 1 (by rfl) ⟨409742, by rfl⟩ : syracuseStep 546323 = 819485) B819485
theorem B546353 : Blo 362758 546353 := bstep (se 2 (by rfl) ⟨204882, by rfl⟩ : syracuseStep 546353 = 409765) B409765
theorem B546371 : Blo 362758 546371 := bstep (se 1 (by rfl) ⟨409778, by rfl⟩ : syracuseStep 546371 = 819557) B819557
theorem B546401 : Blo 362758 546401 := bstep (se 2 (by rfl) ⟨204900, by rfl⟩ : syracuseStep 546401 = 409801) B409801
theorem B546419 : Blo 362758 546419 := bstep (se 1 (by rfl) ⟨409814, by rfl⟩ : syracuseStep 546419 = 819629) B819629
theorem B4150925 : Blo 362758 4150925 := bstep (se 3 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 4150925 = 1556597) B1556597
theorem B546449 : Blo 362758 546449 := bstep (se 2 (by rfl) ⟨204918, by rfl⟩ : syracuseStep 546449 = 409837) B409837
theorem B2152099 : Blo 362758 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B546467 : Blo 362758 546467 := bstep (se 1 (by rfl) ⟨409850, by rfl⟩ : syracuseStep 546467 = 819701) B819701
theorem B546497 : Blo 362758 546497 := bstep (se 2 (by rfl) ⟨204936, by rfl⟩ : syracuseStep 546497 = 409873) B409873
theorem B546515 : Blo 362758 546515 := bstep (se 1 (by rfl) ⟨409886, by rfl⟩ : syracuseStep 546515 = 819773) B819773
theorem B775907 : Blo 362758 775907 := bstep (se 1 (by rfl) ⟨581930, by rfl⟩ : syracuseStep 775907 = 1163861) B1163861
theorem B546545 : Blo 362758 546545 := bstep (se 2 (by rfl) ⟨204954, by rfl⟩ : syracuseStep 546545 = 409909) B409909
theorem B546563 : Blo 362758 546563 := bstep (se 1 (by rfl) ⟨409922, by rfl⟩ : syracuseStep 546563 = 819845) B819845
theorem B546593 : Blo 362758 546593 := bstep (se 2 (by rfl) ⟨204972, by rfl⟩ : syracuseStep 546593 = 409945) B409945
theorem B546611 : Blo 362758 546611 := bstep (se 1 (by rfl) ⟨409958, by rfl⟩ : syracuseStep 546611 = 819917) B819917
theorem B3102533 : Blo 362758 3102533 := bstep (se 4 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 3102533 = 581725) B581725
theorem B546641 : Blo 362758 546641 := bstep (se 2 (by rfl) ⟨204990, by rfl⟩ : syracuseStep 546641 = 409981) B409981
theorem B546659 : Blo 362758 546659 := bstep (se 1 (by rfl) ⟨409994, by rfl⟩ : syracuseStep 546659 = 819989) B819989
theorem B612211 : Blo 362758 612211 := bstep (se 1 (by rfl) ⟨459158, by rfl⟩ : syracuseStep 612211 = 918317) B918317
theorem B546689 : Blo 362758 546689 := bstep (se 2 (by rfl) ⟨205008, by rfl⟩ : syracuseStep 546689 = 410017) B410017
theorem B546707 : Blo 362758 546707 := bstep (se 1 (by rfl) ⟨410030, by rfl⟩ : syracuseStep 546707 = 820061) B820061
theorem B546737 : Blo 362758 546737 := bstep (se 2 (by rfl) ⟨205026, by rfl⟩ : syracuseStep 546737 = 410053) B410053
theorem B546755 : Blo 362758 546755 := bstep (se 1 (by rfl) ⟨410066, by rfl⟩ : syracuseStep 546755 = 820133) B820133
theorem B546785 : Blo 362758 546785 := bstep (se 2 (by rfl) ⟨205044, by rfl⟩ : syracuseStep 546785 = 410089) B410089
theorem B1234925 : Blo 362758 1234925 := bstep (se 3 (by rfl) ⟨231548, by rfl⟩ : syracuseStep 1234925 = 463097) B463097
theorem B546803 : Blo 362758 546803 := bstep (se 1 (by rfl) ⟨410102, by rfl⟩ : syracuseStep 546803 = 820205) B820205
theorem B612353 : Blo 362758 612353 := bstep (se 2 (by rfl) ⟨229632, by rfl⟩ : syracuseStep 612353 = 459265) B459265
theorem B546833 : Blo 362758 546833 := bstep (se 2 (by rfl) ⟨205062, by rfl⟩ : syracuseStep 546833 = 410125) B410125
theorem B546851 : Blo 362758 546851 := bstep (se 1 (by rfl) ⟨410138, by rfl⟩ : syracuseStep 546851 = 820277) B820277
theorem B1234979 : Blo 362758 1234979 := bstep (se 1 (by rfl) ⟨926234, by rfl⟩ : syracuseStep 1234979 = 1852469) B1852469
theorem B546881 : Blo 362758 546881 := bstep (se 2 (by rfl) ⟨205080, by rfl⟩ : syracuseStep 546881 = 410161) B410161
theorem B546899 : Blo 362758 546899 := bstep (se 1 (by rfl) ⟨410174, by rfl⟩ : syracuseStep 546899 = 820349) B820349
theorem B546929 : Blo 362758 546929 := bstep (se 2 (by rfl) ⟨205098, by rfl⟩ : syracuseStep 546929 = 410197) B410197
theorem B612481 : Blo 362758 612481 := bstep (se 2 (by rfl) ⟨229680, by rfl⟩ : syracuseStep 612481 = 459361) B459361
theorem B546947 : Blo 362758 546947 := bstep (se 1 (by rfl) ⟨410210, by rfl⟩ : syracuseStep 546947 = 820421) B820421
theorem B546977 : Blo 362758 546977 := bstep (se 2 (by rfl) ⟨205116, by rfl⟩ : syracuseStep 546977 = 410233) B410233
theorem B612515 : Blo 362758 612515 := bstep (se 1 (by rfl) ⟨459386, by rfl⟩ : syracuseStep 612515 = 918773) B918773
theorem B546995 : Blo 362758 546995 := bstep (se 1 (by rfl) ⟨410246, by rfl⟩ : syracuseStep 546995 = 820493) B820493
theorem B1038541 : Blo 362758 1038541 := bstep (se 3 (by rfl) ⟨194726, by rfl⟩ : syracuseStep 1038541 = 389453) B389453
theorem B547025 : Blo 362758 547025 := bstep (se 2 (by rfl) ⟨205134, by rfl⟩ : syracuseStep 547025 = 410269) B410269
theorem B547043 : Blo 362758 547043 := bstep (se 1 (by rfl) ⟨410282, by rfl⟩ : syracuseStep 547043 = 820565) B820565
theorem B547073 : Blo 362758 547073 := bstep (se 2 (by rfl) ⟨205152, by rfl⟩ : syracuseStep 547073 = 410305) B410305
theorem B547091 : Blo 362758 547091 := bstep (se 1 (by rfl) ⟨410318, by rfl⟩ : syracuseStep 547091 = 820637) B820637
theorem B612643 : Blo 362758 612643 := bstep (se 1 (by rfl) ⟨459482, by rfl⟩ : syracuseStep 612643 = 918965) B918965
theorem B547121 : Blo 362758 547121 := bstep (se 2 (by rfl) ⟨205170, by rfl⟩ : syracuseStep 547121 = 410341) B410341
theorem B1235249 : Blo 362758 1235249 := bstep (se 2 (by rfl) ⟨463218, by rfl⟩ : syracuseStep 1235249 = 926437) B926437
theorem B547139 : Blo 362758 547139 := bstep (se 1 (by rfl) ⟨410354, by rfl⟩ : syracuseStep 547139 = 820709) B820709
theorem B416083 : Blo 362758 416083 := bstep (se 1 (by rfl) ⟨312062, by rfl⟩ : syracuseStep 416083 = 624125) B624125
theorem B547169 : Blo 362758 547169 := bstep (se 2 (by rfl) ⟨205188, by rfl⟩ : syracuseStep 547169 = 410377) B410377
theorem B547187 : Blo 362758 547187 := bstep (se 1 (by rfl) ⟨410390, by rfl⟩ : syracuseStep 547187 = 820781) B820781
theorem B1169795 : Blo 362758 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B2087309 : Blo 362758 2087309 := bstep (se 3 (by rfl) ⟨391370, by rfl⟩ : syracuseStep 2087309 = 782741) B782741
theorem B547217 : Blo 362758 547217 := bstep (se 2 (by rfl) ⟨205206, by rfl⟩ : syracuseStep 547217 = 410413) B410413
theorem B678289 : Blo 362758 678289 := bstep (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) B508717
theorem B547235 : Blo 362758 547235 := bstep (se 1 (by rfl) ⟨410426, by rfl⟩ : syracuseStep 547235 = 820853) B820853
theorem B612785 : Blo 362758 612785 := bstep (se 2 (by rfl) ⟨229794, by rfl⟩ : syracuseStep 612785 = 459589) B459589
theorem B547265 : Blo 362758 547265 := bstep (se 2 (by rfl) ⟨205224, by rfl⟩ : syracuseStep 547265 = 410449) B410449
theorem B547283 : Blo 362758 547283 := bstep (se 1 (by rfl) ⟨410462, by rfl⟩ : syracuseStep 547283 = 820925) B820925
theorem B3103217 : Blo 362758 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B547313 : Blo 362758 547313 := bstep (se 2 (by rfl) ⟨205242, by rfl⟩ : syracuseStep 547313 = 410485) B410485
theorem B547331 : Blo 362758 547331 := bstep (se 1 (by rfl) ⟨410498, by rfl⟩ : syracuseStep 547331 = 820997) B820997
theorem B547361 : Blo 362758 547361 := bstep (se 2 (by rfl) ⟨205260, by rfl⟩ : syracuseStep 547361 = 410521) B410521
theorem B612913 : Blo 362758 612913 := bstep (se 2 (by rfl) ⟨229842, by rfl⟩ : syracuseStep 612913 = 459685) B459685
theorem B547379 : Blo 362758 547379 := bstep (se 1 (by rfl) ⟨410534, by rfl⟩ : syracuseStep 547379 = 821069) B821069
theorem B547409 : Blo 362758 547409 := bstep (se 2 (by rfl) ⟨205278, by rfl⟩ : syracuseStep 547409 = 410557) B410557
theorem B612947 : Blo 362758 612947 := bstep (se 1 (by rfl) ⟨459710, by rfl⟩ : syracuseStep 612947 = 919421) B919421
theorem B547427 : Blo 362758 547427 := bstep (se 1 (by rfl) ⟨410570, by rfl⟩ : syracuseStep 547427 = 821141) B821141
theorem B547457 : Blo 362758 547457 := bstep (se 2 (by rfl) ⟨205296, by rfl⟩ : syracuseStep 547457 = 410593) B410593
theorem B547475 : Blo 362758 547475 := bstep (se 1 (by rfl) ⟨410606, by rfl⟩ : syracuseStep 547475 = 821213) B821213
theorem B776881 : Blo 362758 776881 := bstep (se 2 (by rfl) ⟨291330, by rfl⟩ : syracuseStep 776881 = 582661) B582661
theorem B547505 : Blo 362758 547505 := bstep (se 2 (by rfl) ⟨205314, by rfl⟩ : syracuseStep 547505 = 410629) B410629
theorem B547523 : Blo 362758 547523 := bstep (se 1 (by rfl) ⟨410642, by rfl⟩ : syracuseStep 547523 = 821285) B821285
theorem B613075 : Blo 362758 613075 := bstep (se 1 (by rfl) ⟨459806, by rfl⟩ : syracuseStep 613075 = 919613) B919613
theorem B547553 : Blo 362758 547553 := bstep (se 2 (by rfl) ⟨205332, by rfl⟩ : syracuseStep 547553 = 410665) B410665
theorem B547571 : Blo 362758 547571 := bstep (se 1 (by rfl) ⟨410678, by rfl⟩ : syracuseStep 547571 = 821357) B821357
theorem B547601 : Blo 362758 547601 := bstep (se 2 (by rfl) ⟨205350, by rfl⟩ : syracuseStep 547601 = 410701) B410701
theorem B547619 : Blo 362758 547619 := bstep (se 1 (by rfl) ⟨410714, by rfl⟩ : syracuseStep 547619 = 821429) B821429
theorem B940835 : Blo 362758 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B547649 : Blo 362758 547649 := bstep (se 2 (by rfl) ⟨205368, by rfl⟩ : syracuseStep 547649 = 410737) B410737
theorem B1235789 : Blo 362758 1235789 := bstep (se 3 (by rfl) ⟨231710, by rfl⟩ : syracuseStep 1235789 = 463421) B463421
theorem B547667 : Blo 362758 547667 := bstep (se 1 (by rfl) ⟨410750, by rfl⟩ : syracuseStep 547667 = 821501) B821501
theorem B613217 : Blo 362758 613217 := bstep (se 2 (by rfl) ⟨229956, by rfl⟩ : syracuseStep 613217 = 459913) B459913
theorem B547697 : Blo 362758 547697 := bstep (se 2 (by rfl) ⟨205386, by rfl⟩ : syracuseStep 547697 = 410773) B410773
theorem B547715 : Blo 362758 547715 := bstep (se 1 (by rfl) ⟨410786, by rfl⟩ : syracuseStep 547715 = 821573) B821573
theorem B1235843 : Blo 362758 1235843 := bstep (se 1 (by rfl) ⟨926882, by rfl⟩ : syracuseStep 1235843 = 1853765) B1853765
theorem B547745 : Blo 362758 547745 := bstep (se 2 (by rfl) ⟨205404, by rfl⟩ : syracuseStep 547745 = 410809) B410809
theorem B1563569 : Blo 362758 1563569 := bstep (se 2 (by rfl) ⟨586338, by rfl⟩ : syracuseStep 1563569 = 1172677) B1172677
theorem B547763 : Blo 362758 547763 := bstep (se 1 (by rfl) ⟨410822, by rfl⟩ : syracuseStep 547763 = 821645) B821645
theorem B547793 : Blo 362758 547793 := bstep (se 2 (by rfl) ⟨205422, by rfl⟩ : syracuseStep 547793 = 410845) B410845
theorem B613345 : Blo 362758 613345 := bstep (se 2 (by rfl) ⟨230004, by rfl⟩ : syracuseStep 613345 = 460009) B460009
theorem B547811 : Blo 362758 547811 := bstep (se 1 (by rfl) ⟨410858, by rfl⟩ : syracuseStep 547811 = 821717) B821717
theorem B547841 : Blo 362758 547841 := bstep (se 2 (by rfl) ⟨205440, by rfl⟩ : syracuseStep 547841 = 410881) B410881
theorem B613379 : Blo 362758 613379 := bstep (se 1 (by rfl) ⟨460034, by rfl⟩ : syracuseStep 613379 = 920069) B920069
theorem B547859 : Blo 362758 547859 := bstep (se 1 (by rfl) ⟨410894, by rfl⟩ : syracuseStep 547859 = 821789) B821789
theorem B547889 : Blo 362758 547889 := bstep (se 2 (by rfl) ⟨205458, by rfl⟩ : syracuseStep 547889 = 410917) B410917
theorem B547907 : Blo 362758 547907 := bstep (se 1 (by rfl) ⟨410930, by rfl⟩ : syracuseStep 547907 = 821861) B821861
theorem B547937 : Blo 362758 547937 := bstep (se 2 (by rfl) ⟨205476, by rfl⟩ : syracuseStep 547937 = 410953) B410953
theorem B547955 : Blo 362758 547955 := bstep (se 1 (by rfl) ⟨410966, by rfl⟩ : syracuseStep 547955 = 821933) B821933
theorem B613507 : Blo 362758 613507 := bstep (se 1 (by rfl) ⟨460130, by rfl⟩ : syracuseStep 613507 = 920261) B920261
theorem B547985 : Blo 362758 547985 := bstep (se 2 (by rfl) ⟨205494, by rfl⟩ : syracuseStep 547985 = 410989) B410989
theorem B1236113 : Blo 362758 1236113 := bstep (se 2 (by rfl) ⟨463542, by rfl⟩ : syracuseStep 1236113 = 927085) B927085
theorem B548003 : Blo 362758 548003 := bstep (se 1 (by rfl) ⟨411002, by rfl⟩ : syracuseStep 548003 = 822005) B822005
theorem B548033 : Blo 362758 548033 := bstep (se 2 (by rfl) ⟨205512, by rfl⟩ : syracuseStep 548033 = 411025) B411025
theorem B548051 : Blo 362758 548051 := bstep (se 1 (by rfl) ⟨411038, by rfl⟩ : syracuseStep 548051 = 822077) B822077
theorem B548081 : Blo 362758 548081 := bstep (se 2 (by rfl) ⟨205530, by rfl⟩ : syracuseStep 548081 = 411061) B411061
theorem B548099 : Blo 362758 548099 := bstep (se 1 (by rfl) ⟨411074, by rfl⟩ : syracuseStep 548099 = 822149) B822149
theorem B613649 : Blo 362758 613649 := bstep (se 2 (by rfl) ⟨230118, by rfl⟩ : syracuseStep 613649 = 460237) B460237
theorem B548129 : Blo 362758 548129 := bstep (se 2 (by rfl) ⟨205548, by rfl⟩ : syracuseStep 548129 = 411097) B411097
theorem B548147 : Blo 362758 548147 := bstep (se 1 (by rfl) ⟨411110, by rfl⟩ : syracuseStep 548147 = 822221) B822221
theorem B777539 : Blo 362758 777539 := bstep (se 1 (by rfl) ⟨583154, by rfl⟩ : syracuseStep 777539 = 1166309) B1166309
theorem B548177 : Blo 362758 548177 := bstep (se 2 (by rfl) ⟨205566, by rfl⟩ : syracuseStep 548177 = 411133) B411133
theorem B548195 : Blo 362758 548195 := bstep (se 1 (by rfl) ⟨411146, by rfl⟩ : syracuseStep 548195 = 822293) B822293
theorem B548225 : Blo 362758 548225 := bstep (se 2 (by rfl) ⟨205584, by rfl⟩ : syracuseStep 548225 = 411169) B411169
theorem B613777 : Blo 362758 613777 := bstep (se 2 (by rfl) ⟨230166, by rfl⟩ : syracuseStep 613777 = 460333) B460333
theorem B548243 : Blo 362758 548243 := bstep (se 1 (by rfl) ⟨411182, by rfl⟩ : syracuseStep 548243 = 822365) B822365
theorem B548273 : Blo 362758 548273 := bstep (se 2 (by rfl) ⟨205602, by rfl⟩ : syracuseStep 548273 = 411205) B411205
theorem B613811 : Blo 362758 613811 := bstep (se 1 (by rfl) ⟨460358, by rfl⟩ : syracuseStep 613811 = 920717) B920717
theorem B875971 : Blo 362758 875971 := bstep (se 1 (by rfl) ⟨656978, by rfl⟩ : syracuseStep 875971 = 1313957) B1313957
theorem B548291 : Blo 362758 548291 := bstep (se 1 (by rfl) ⟨411218, by rfl⟩ : syracuseStep 548291 = 822437) B822437
theorem B2776517 : Blo 362758 2776517 := bstep (se 4 (by rfl) ⟨260298, by rfl⟩ : syracuseStep 2776517 = 520597) B520597
theorem B548321 : Blo 362758 548321 := bstep (se 2 (by rfl) ⟨205620, by rfl⟩ : syracuseStep 548321 = 411241) B411241
theorem B548339 : Blo 362758 548339 := bstep (se 1 (by rfl) ⟨411254, by rfl⟩ : syracuseStep 548339 = 822509) B822509
theorem B548369 : Blo 362758 548369 := bstep (se 2 (by rfl) ⟨205638, by rfl⟩ : syracuseStep 548369 = 411277) B411277
theorem B548387 : Blo 362758 548387 := bstep (se 1 (by rfl) ⟨411290, by rfl⟩ : syracuseStep 548387 = 822581) B822581
theorem B613939 : Blo 362758 613939 := bstep (se 1 (by rfl) ⟨460454, by rfl⟩ : syracuseStep 613939 = 920909) B920909
theorem B4677173 : Blo 362758 4677173 := bstep (se 5 (by rfl) ⟨219242, by rfl⟩ : syracuseStep 4677173 = 438485) B438485
theorem B548417 : Blo 362758 548417 := bstep (se 2 (by rfl) ⟨205656, by rfl⟩ : syracuseStep 548417 = 411313) B411313
theorem B548435 : Blo 362758 548435 := bstep (se 1 (by rfl) ⟨411326, by rfl⟩ : syracuseStep 548435 = 822653) B822653
theorem B548465 : Blo 362758 548465 := bstep (se 2 (by rfl) ⟨205674, by rfl⟩ : syracuseStep 548465 = 411349) B411349
theorem B548483 : Blo 362758 548483 := bstep (se 1 (by rfl) ⟨411362, by rfl⟩ : syracuseStep 548483 = 822725) B822725
theorem B548513 : Blo 362758 548513 := bstep (se 2 (by rfl) ⟨205692, by rfl⟩ : syracuseStep 548513 = 411385) B411385
theorem B1236653 : Blo 362758 1236653 := bstep (se 3 (by rfl) ⟨231872, by rfl⟩ : syracuseStep 1236653 = 463745) B463745
theorem B548531 : Blo 362758 548531 := bstep (se 1 (by rfl) ⟨411398, by rfl⟩ : syracuseStep 548531 = 822797) B822797
theorem B614081 : Blo 362758 614081 := bstep (se 2 (by rfl) ⟨230280, by rfl⟩ : syracuseStep 614081 = 460561) B460561
theorem B581315 : Blo 362758 581315 := bstep (se 1 (by rfl) ⟨435986, by rfl⟩ : syracuseStep 581315 = 871973) B871973
theorem B548561 : Blo 362758 548561 := bstep (se 2 (by rfl) ⟨205710, by rfl⟩ : syracuseStep 548561 = 411421) B411421
theorem B548579 : Blo 362758 548579 := bstep (se 1 (by rfl) ⟨411434, by rfl⟩ : syracuseStep 548579 = 822869) B822869
theorem B1236707 : Blo 362758 1236707 := bstep (se 1 (by rfl) ⟨927530, by rfl⟩ : syracuseStep 1236707 = 1855061) B1855061
theorem B548609 : Blo 362758 548609 := bstep (se 2 (by rfl) ⟨205728, by rfl⟩ : syracuseStep 548609 = 411457) B411457
theorem B581393 : Blo 362758 581393 := bstep (se 2 (by rfl) ⟨218022, by rfl⟩ : syracuseStep 581393 = 436045) B436045
theorem B548627 : Blo 362758 548627 := bstep (se 1 (by rfl) ⟨411470, by rfl⟩ : syracuseStep 548627 = 822941) B822941
theorem B548657 : Blo 362758 548657 := bstep (se 2 (by rfl) ⟨205746, by rfl⟩ : syracuseStep 548657 = 411493) B411493
theorem B614209 : Blo 362758 614209 := bstep (se 2 (by rfl) ⟨230328, by rfl⟩ : syracuseStep 614209 = 460657) B460657
theorem B548675 : Blo 362758 548675 := bstep (se 1 (by rfl) ⟨411506, by rfl⟩ : syracuseStep 548675 = 823013) B823013
theorem B548705 : Blo 362758 548705 := bstep (se 2 (by rfl) ⟨205764, by rfl⟩ : syracuseStep 548705 = 411529) B411529
theorem B614243 : Blo 362758 614243 := bstep (se 1 (by rfl) ⟨460682, by rfl⟩ : syracuseStep 614243 = 921365) B921365
theorem B548723 : Blo 362758 548723 := bstep (se 1 (by rfl) ⟨411542, by rfl⟩ : syracuseStep 548723 = 823085) B823085
theorem B876433 : Blo 362758 876433 := bstep (se 2 (by rfl) ⟨328662, by rfl⟩ : syracuseStep 876433 = 657325) B657325
theorem B1040273 : Blo 362758 1040273 := bstep (se 2 (by rfl) ⟨390102, by rfl⟩ : syracuseStep 1040273 = 780205) B780205
theorem B548753 : Blo 362758 548753 := bstep (se 2 (by rfl) ⟨205782, by rfl⟩ : syracuseStep 548753 = 411565) B411565
theorem B548771 : Blo 362758 548771 := bstep (se 1 (by rfl) ⟨411578, by rfl⟩ : syracuseStep 548771 = 823157) B823157
theorem B548801 : Blo 362758 548801 := bstep (se 2 (by rfl) ⟨205800, by rfl⟩ : syracuseStep 548801 = 411601) B411601
theorem B548819 : Blo 362758 548819 := bstep (se 1 (by rfl) ⟨411614, by rfl⟩ : syracuseStep 548819 = 823229) B823229
theorem B614371 : Blo 362758 614371 := bstep (se 1 (by rfl) ⟨460778, by rfl⟩ : syracuseStep 614371 = 921557) B921557
theorem B581617 : Blo 362758 581617 := bstep (se 2 (by rfl) ⟨218106, by rfl⟩ : syracuseStep 581617 = 436213) B436213
theorem B548849 : Blo 362758 548849 := bstep (se 2 (by rfl) ⟨205818, by rfl⟩ : syracuseStep 548849 = 411637) B411637
theorem B1236977 : Blo 362758 1236977 := bstep (se 2 (by rfl) ⟨463866, by rfl⟩ : syracuseStep 1236977 = 927733) B927733
theorem B548867 : Blo 362758 548867 := bstep (se 1 (by rfl) ⟨411650, by rfl⟩ : syracuseStep 548867 = 823301) B823301
theorem B548897 : Blo 362758 548897 := bstep (se 2 (by rfl) ⟨205836, by rfl⟩ : syracuseStep 548897 = 411673) B411673
theorem B548915 : Blo 362758 548915 := bstep (se 1 (by rfl) ⟨411686, by rfl⟩ : syracuseStep 548915 = 823373) B823373
theorem B1040465 : Blo 362758 1040465 := bstep (se 2 (by rfl) ⟨390174, by rfl⟩ : syracuseStep 1040465 = 780349) B780349
theorem B548945 : Blo 362758 548945 := bstep (se 2 (by rfl) ⟨205854, by rfl⟩ : syracuseStep 548945 = 411709) B411709
theorem B548963 : Blo 362758 548963 := bstep (se 1 (by rfl) ⟨411722, by rfl⟩ : syracuseStep 548963 = 823445) B823445
theorem B614513 : Blo 362758 614513 := bstep (se 2 (by rfl) ⟨230442, by rfl⟩ : syracuseStep 614513 = 460885) B460885
theorem B548993 : Blo 362758 548993 := bstep (se 2 (by rfl) ⟨205872, by rfl⟩ : syracuseStep 548993 = 411745) B411745
theorem B778385 : Blo 362758 778385 := bstep (se 2 (by rfl) ⟨291894, by rfl⟩ : syracuseStep 778385 = 583789) B583789
theorem B549011 : Blo 362758 549011 := bstep (se 1 (by rfl) ⟨411758, by rfl⟩ : syracuseStep 549011 = 823517) B823517
theorem B549041 : Blo 362758 549041 := bstep (se 2 (by rfl) ⟨205890, by rfl⟩ : syracuseStep 549041 = 411781) B411781
theorem B549059 : Blo 362758 549059 := bstep (se 1 (by rfl) ⟨411794, by rfl⟩ : syracuseStep 549059 = 823589) B823589
theorem B549089 : Blo 362758 549089 := bstep (se 2 (by rfl) ⟨205908, by rfl⟩ : syracuseStep 549089 = 411817) B411817
theorem B614641 : Blo 362758 614641 := bstep (se 2 (by rfl) ⟨230490, by rfl⟩ : syracuseStep 614641 = 460981) B460981
theorem B549107 : Blo 362758 549107 := bstep (se 1 (by rfl) ⟨411830, by rfl⟩ : syracuseStep 549107 = 823661) B823661
theorem B549137 : Blo 362758 549137 := bstep (se 2 (by rfl) ⟨205926, by rfl⟩ : syracuseStep 549137 = 411853) B411853
theorem B614675 : Blo 362758 614675 := bstep (se 1 (by rfl) ⟨461006, by rfl⟩ : syracuseStep 614675 = 922013) B922013
theorem B549155 : Blo 362758 549155 := bstep (se 1 (by rfl) ⟨411866, by rfl⟩ : syracuseStep 549155 = 823733) B823733
theorem B2482481 : Blo 362758 2482481 := bstep (se 2 (by rfl) ⟨930930, by rfl⟩ : syracuseStep 2482481 = 1861861) B1861861
theorem B549185 : Blo 362758 549185 := bstep (se 2 (by rfl) ⟨205944, by rfl⟩ : syracuseStep 549185 = 411889) B411889
theorem B549203 : Blo 362758 549203 := bstep (se 1 (by rfl) ⟨411902, by rfl⟩ : syracuseStep 549203 = 823805) B823805
theorem B549233 : Blo 362758 549233 := bstep (se 2 (by rfl) ⟨205962, by rfl⟩ : syracuseStep 549233 = 411925) B411925
theorem B549251 : Blo 362758 549251 := bstep (se 1 (by rfl) ⟨411938, by rfl⟩ : syracuseStep 549251 = 823877) B823877
theorem B1401229 : Blo 362758 1401229 := bstep (se 3 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 1401229 = 525461) B525461
theorem B614803 : Blo 362758 614803 := bstep (se 1 (by rfl) ⟨461102, by rfl⟩ : syracuseStep 614803 = 922205) B922205
theorem B549281 : Blo 362758 549281 := bstep (se 2 (by rfl) ⟨205980, by rfl⟩ : syracuseStep 549281 = 411961) B411961
theorem B549299 : Blo 362758 549299 := bstep (se 1 (by rfl) ⟨411974, by rfl⟩ : syracuseStep 549299 = 823949) B823949
theorem B549329 : Blo 362758 549329 := bstep (se 2 (by rfl) ⟨205998, by rfl⟩ : syracuseStep 549329 = 411997) B411997
theorem B549347 : Blo 362758 549347 := bstep (se 1 (by rfl) ⟨412010, by rfl⟩ : syracuseStep 549347 = 824021) B824021
theorem B4153841 : Blo 362758 4153841 := bstep (se 2 (by rfl) ⟨1557690, by rfl⟩ : syracuseStep 4153841 = 3115381) B3115381
theorem B549377 : Blo 362758 549377 := bstep (se 2 (by rfl) ⟨206016, by rfl⟩ : syracuseStep 549377 = 412033) B412033
theorem B1237517 : Blo 362758 1237517 := bstep (se 3 (by rfl) ⟨232034, by rfl⟩ : syracuseStep 1237517 = 464069) B464069
theorem B549395 : Blo 362758 549395 := bstep (se 1 (by rfl) ⟨412046, by rfl⟩ : syracuseStep 549395 = 824093) B824093
theorem B614945 : Blo 362758 614945 := bstep (se 2 (by rfl) ⟨230604, by rfl⟩ : syracuseStep 614945 = 461209) B461209
theorem B549425 : Blo 362758 549425 := bstep (se 2 (by rfl) ⟨206034, by rfl⟩ : syracuseStep 549425 = 412069) B412069
theorem B549443 : Blo 362758 549443 := bstep (se 1 (by rfl) ⟨412082, by rfl⟩ : syracuseStep 549443 = 824165) B824165
theorem B1237571 : Blo 362758 1237571 := bstep (se 1 (by rfl) ⟨928178, by rfl⟩ : syracuseStep 1237571 = 1856357) B1856357
theorem B549473 : Blo 362758 549473 := bstep (se 2 (by rfl) ⟨206052, by rfl⟩ : syracuseStep 549473 = 412105) B412105
theorem B549491 : Blo 362758 549491 := bstep (se 1 (by rfl) ⟨412118, by rfl⟩ : syracuseStep 549491 = 824237) B824237
theorem B549521 : Blo 362758 549521 := bstep (se 2 (by rfl) ⟨206070, by rfl⟩ : syracuseStep 549521 = 412141) B412141
theorem B615073 : Blo 362758 615073 := bstep (se 2 (by rfl) ⟨230652, by rfl⟩ : syracuseStep 615073 = 461305) B461305
theorem B549539 : Blo 362758 549539 := bstep (se 1 (by rfl) ⟨412154, by rfl⟩ : syracuseStep 549539 = 824309) B824309
theorem B549569 : Blo 362758 549569 := bstep (se 2 (by rfl) ⟨206088, by rfl⟩ : syracuseStep 549569 = 412177) B412177
theorem B615107 : Blo 362758 615107 := bstep (se 1 (by rfl) ⟨461330, by rfl⟩ : syracuseStep 615107 = 922661) B922661
theorem B549587 : Blo 362758 549587 := bstep (se 1 (by rfl) ⟨412190, by rfl⟩ : syracuseStep 549587 = 824381) B824381
theorem B549617 : Blo 362758 549617 := bstep (se 2 (by rfl) ⟨206106, by rfl⟩ : syracuseStep 549617 = 412213) B412213
theorem B549635 : Blo 362758 549635 := bstep (se 1 (by rfl) ⟨412226, by rfl⟩ : syracuseStep 549635 = 824453) B824453
theorem B549665 : Blo 362758 549665 := bstep (se 2 (by rfl) ⟨206124, by rfl⟩ : syracuseStep 549665 = 412249) B412249
theorem B549683 : Blo 362758 549683 := bstep (se 1 (by rfl) ⟨412262, by rfl⟩ : syracuseStep 549683 = 824525) B824525
theorem B615235 : Blo 362758 615235 := bstep (se 1 (by rfl) ⟨461426, by rfl⟩ : syracuseStep 615235 = 922853) B922853
theorem B549713 : Blo 362758 549713 := bstep (se 2 (by rfl) ⟨206142, by rfl⟩ : syracuseStep 549713 = 412285) B412285
theorem B549731 : Blo 362758 549731 := bstep (se 1 (by rfl) ⟨412298, by rfl⟩ : syracuseStep 549731 = 824597) B824597
theorem B549761 : Blo 362758 549761 := bstep (se 2 (by rfl) ⟨206160, by rfl⟩ : syracuseStep 549761 = 412321) B412321
theorem B1172369 : Blo 362758 1172369 := bstep (se 2 (by rfl) ⟨439638, by rfl⟩ : syracuseStep 1172369 = 879277) B879277
theorem B549779 : Blo 362758 549779 := bstep (se 1 (by rfl) ⟨412334, by rfl⟩ : syracuseStep 549779 = 824669) B824669
theorem B549809 : Blo 362758 549809 := bstep (se 2 (by rfl) ⟨206178, by rfl⟩ : syracuseStep 549809 = 412357) B412357
theorem B549827 : Blo 362758 549827 := bstep (se 1 (by rfl) ⟨412370, by rfl⟩ : syracuseStep 549827 = 824741) B824741
theorem B615377 : Blo 362758 615377 := bstep (se 2 (by rfl) ⟨230766, by rfl⟩ : syracuseStep 615377 = 461533) B461533
theorem B549857 : Blo 362758 549857 := bstep (se 2 (by rfl) ⟨206196, by rfl⟩ : syracuseStep 549857 = 412393) B412393
theorem B549875 : Blo 362758 549875 := bstep (se 1 (by rfl) ⟨412406, by rfl⟩ : syracuseStep 549875 = 824813) B824813
theorem B549905 : Blo 362758 549905 := bstep (se 2 (by rfl) ⟨206214, by rfl⟩ : syracuseStep 549905 = 412429) B412429
theorem B549923 : Blo 362758 549923 := bstep (se 1 (by rfl) ⟨412442, by rfl⟩ : syracuseStep 549923 = 824885) B824885
theorem B1041457 : Blo 362758 1041457 := bstep (se 2 (by rfl) ⟨390546, by rfl⟩ : syracuseStep 1041457 = 781093) B781093
theorem B549953 : Blo 362758 549953 := bstep (se 2 (by rfl) ⟨206232, by rfl⟩ : syracuseStep 549953 = 412465) B412465
theorem B615505 : Blo 362758 615505 := bstep (se 2 (by rfl) ⟨230814, by rfl⟩ : syracuseStep 615505 = 461629) B461629
theorem B549971 : Blo 362758 549971 := bstep (se 1 (by rfl) ⟨412478, by rfl⟩ : syracuseStep 549971 = 824957) B824957
theorem B550001 : Blo 362758 550001 := bstep (se 2 (by rfl) ⟨206250, by rfl⟩ : syracuseStep 550001 = 412501) B412501
theorem B615539 : Blo 362758 615539 := bstep (se 1 (by rfl) ⟨461654, by rfl⟩ : syracuseStep 615539 = 923309) B923309
theorem B550019 : Blo 362758 550019 := bstep (se 1 (by rfl) ⟨412514, by rfl⟩ : syracuseStep 550019 = 825029) B825029
theorem B550049 : Blo 362758 550049 := bstep (se 2 (by rfl) ⟨206268, by rfl⟩ : syracuseStep 550049 = 412537) B412537
theorem B550067 : Blo 362758 550067 := bstep (se 1 (by rfl) ⟨412550, by rfl⟩ : syracuseStep 550067 = 825101) B825101
theorem B550097 : Blo 362758 550097 := bstep (se 2 (by rfl) ⟨206286, by rfl⟩ : syracuseStep 550097 = 412573) B412573
theorem B550115 : Blo 362758 550115 := bstep (se 1 (by rfl) ⟨412586, by rfl⟩ : syracuseStep 550115 = 825173) B825173
theorem B615667 : Blo 362758 615667 := bstep (se 1 (by rfl) ⟨461750, by rfl⟩ : syracuseStep 615667 = 923501) B923501
theorem B1041731 : Blo 362758 1041731 := bstep (se 1 (by rfl) ⟨781298, by rfl⟩ : syracuseStep 1041731 = 1562597) B1562597
theorem B1566029 : Blo 362758 1566029 := bstep (se 3 (by rfl) ⟨293630, by rfl⟩ : syracuseStep 1566029 = 587261) B587261
theorem B615809 : Blo 362758 615809 := bstep (se 2 (by rfl) ⟨230928, by rfl⟩ : syracuseStep 615809 = 461857) B461857
theorem B1107341 : Blo 362758 1107341 := bstep (se 3 (by rfl) ⟨207626, by rfl⟩ : syracuseStep 1107341 = 415253) B415253
theorem B517585 : Blo 362758 517585 := bstep (se 2 (by rfl) ⟨194094, by rfl⟩ : syracuseStep 517585 = 388189) B388189
theorem B615937 : Blo 362758 615937 := bstep (se 2 (by rfl) ⟨230976, by rfl⟩ : syracuseStep 615937 = 461953) B461953
theorem B1041923 : Blo 362758 1041923 := bstep (se 1 (by rfl) ⟨781442, by rfl⟩ : syracuseStep 1041923 = 1562885) B1562885
theorem B615971 : Blo 362758 615971 := bstep (se 1 (by rfl) ⟨461978, by rfl⟩ : syracuseStep 615971 = 923957) B923957
theorem B517681 : Blo 362758 517681 := bstep (se 2 (by rfl) ⟨194130, by rfl⟩ : syracuseStep 517681 = 388261) B388261
theorem B2221681 : Blo 362758 2221681 := bstep (se 2 (by rfl) ⟨833130, by rfl⟩ : syracuseStep 2221681 = 1666261) B1666261
theorem B616099 : Blo 362758 616099 := bstep (se 1 (by rfl) ⟨462074, by rfl⟩ : syracuseStep 616099 = 924149) B924149
theorem B1566371 : Blo 362758 1566371 := bstep (se 1 (by rfl) ⟨1174778, by rfl⟩ : syracuseStep 1566371 = 2349557) B2349557
theorem B583379 : Blo 362758 583379 := bstep (se 1 (by rfl) ⟨437534, by rfl⟩ : syracuseStep 583379 = 875069) B875069
theorem B616241 : Blo 362758 616241 := bstep (se 2 (by rfl) ⟨231090, by rfl⟩ : syracuseStep 616241 = 462181) B462181
theorem B583571 : Blo 362758 583571 := bstep (se 1 (by rfl) ⟨437678, by rfl⟩ : syracuseStep 583571 = 875357) B875357
theorem B616369 : Blo 362758 616369 := bstep (se 2 (by rfl) ⟨231138, by rfl⟩ : syracuseStep 616369 = 462277) B462277
theorem B616403 : Blo 362758 616403 := bstep (se 1 (by rfl) ⟨462302, by rfl⟩ : syracuseStep 616403 = 924605) B924605
theorem B583699 : Blo 362758 583699 := bstep (se 1 (by rfl) ⟨437774, by rfl⟩ : syracuseStep 583699 = 875549) B875549
theorem B518177 : Blo 362758 518177 := bstep (se 2 (by rfl) ⟨194316, by rfl⟩ : syracuseStep 518177 = 388633) B388633
theorem B616531 : Blo 362758 616531 := bstep (se 1 (by rfl) ⟨462398, by rfl⟩ : syracuseStep 616531 = 924797) B924797
theorem B616673 : Blo 362758 616673 := bstep (se 2 (by rfl) ⟨231252, by rfl⟩ : syracuseStep 616673 = 462505) B462505
theorem B15952099 : Blo 362758 15952099 := bstep (se 1 (by rfl) ⟨11964074, by rfl⟩ : syracuseStep 15952099 = 23928149) B23928149
theorem B38070499 : Blo 362758 38070499 := bstep (se 1 (by rfl) ⟨28552874, by rfl⟩ : syracuseStep 38070499 = 57105749) B57105749
theorem B1042733 : Blo 362758 1042733 := bstep (se 3 (by rfl) ⟨195512, by rfl⟩ : syracuseStep 1042733 = 391025) B391025
theorem B616801 : Blo 362758 616801 := bstep (se 2 (by rfl) ⟨231300, by rfl⟩ : syracuseStep 616801 = 462601) B462601
theorem B616835 : Blo 362758 616835 := bstep (se 1 (by rfl) ⟨462626, by rfl⟩ : syracuseStep 616835 = 925253) B925253
theorem B1993187 : Blo 362758 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B1042915 : Blo 362758 1042915 := bstep (se 1 (by rfl) ⟨782186, by rfl⟩ : syracuseStep 1042915 = 1564373) B1564373
theorem B616963 : Blo 362758 616963 := bstep (se 1 (by rfl) ⟨462722, by rfl⟩ : syracuseStep 616963 = 925445) B925445
theorem B3500657 : Blo 362758 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B617105 : Blo 362758 617105 := bstep (se 2 (by rfl) ⟨231414, by rfl⟩ : syracuseStep 617105 = 462829) B462829
theorem B584339 : Blo 362758 584339 := bstep (se 1 (by rfl) ⟨438254, by rfl⟩ : syracuseStep 584339 = 876509) B876509
theorem B2943685 : Blo 362758 2943685 := bstep (se 4 (by rfl) ⟨275970, by rfl⟩ : syracuseStep 2943685 = 551941) B551941
theorem B584417 : Blo 362758 584417 := bstep (se 2 (by rfl) ⟨219156, by rfl⟩ : syracuseStep 584417 = 438313) B438313
theorem B617233 : Blo 362758 617233 := bstep (se 2 (by rfl) ⟨231462, by rfl⟩ : syracuseStep 617233 = 462925) B462925
theorem B617267 : Blo 362758 617267 := bstep (se 1 (by rfl) ⟨462950, by rfl⟩ : syracuseStep 617267 = 925901) B925901
theorem B781169 : Blo 362758 781169 := bstep (se 2 (by rfl) ⟨292938, by rfl⟩ : syracuseStep 781169 = 585877) B585877
theorem B519043 : Blo 362758 519043 := bstep (se 1 (by rfl) ⟨389282, by rfl⟩ : syracuseStep 519043 = 778565) B778565
theorem B617395 : Blo 362758 617395 := bstep (se 1 (by rfl) ⟨463046, by rfl⟩ : syracuseStep 617395 = 926093) B926093
theorem B1043405 : Blo 362758 1043405 := bstep (se 3 (by rfl) ⟨195638, by rfl⟩ : syracuseStep 1043405 = 391277) B391277
theorem B519139 : Blo 362758 519139 := bstep (se 1 (by rfl) ⟨389354, by rfl⟩ : syracuseStep 519139 = 778709) B778709
theorem B388099 : Blo 362758 388099 := bstep (se 1 (by rfl) ⟨291074, by rfl⟩ : syracuseStep 388099 = 582149) B582149
theorem B617537 : Blo 362758 617537 := bstep (se 2 (by rfl) ⟨231576, by rfl⟩ : syracuseStep 617537 = 463153) B463153
theorem B584801 : Blo 362758 584801 := bstep (se 2 (by rfl) ⟨219300, by rfl⟩ : syracuseStep 584801 = 438601) B438601
theorem B552113 : Blo 362758 552113 := bstep (se 2 (by rfl) ⟨207042, by rfl⟩ : syracuseStep 552113 = 414085) B414085
theorem B617665 : Blo 362758 617665 := bstep (se 2 (by rfl) ⟨231624, by rfl⟩ : syracuseStep 617665 = 463249) B463249
theorem B584929 : Blo 362758 584929 := bstep (se 2 (by rfl) ⟨219348, by rfl⟩ : syracuseStep 584929 = 438697) B438697
theorem B617699 : Blo 362758 617699 := bstep (se 1 (by rfl) ⟨463274, by rfl⟩ : syracuseStep 617699 = 926549) B926549
theorem B1174829 : Blo 362758 1174829 := bstep (se 3 (by rfl) ⟨220280, by rfl⟩ : syracuseStep 1174829 = 440561) B440561
theorem B617827 : Blo 362758 617827 := bstep (se 1 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 617827 = 926741) B926741
theorem B519635 : Blo 362758 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B617969 : Blo 362758 617969 := bstep (se 2 (by rfl) ⟨231738, by rfl⟩ : syracuseStep 617969 = 463477) B463477
theorem B618097 : Blo 362758 618097 := bstep (se 2 (by rfl) ⟨231786, by rfl⟩ : syracuseStep 618097 = 463573) B463573
theorem B618131 : Blo 362758 618131 := bstep (se 1 (by rfl) ⟨463598, by rfl⟩ : syracuseStep 618131 = 927197) B927197
theorem B618259 : Blo 362758 618259 := bstep (se 1 (by rfl) ⟨463694, by rfl⟩ : syracuseStep 618259 = 927389) B927389
theorem B618401 : Blo 362758 618401 := bstep (se 2 (by rfl) ⟨231900, by rfl⟩ : syracuseStep 618401 = 463801) B463801
theorem B3927989 : Blo 362758 3927989 := bstep (se 5 (by rfl) ⟨184124, by rfl⟩ : syracuseStep 3927989 = 368249) B368249
theorem B5238755 : Blo 362758 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B552977 : Blo 362758 552977 := bstep (se 2 (by rfl) ⟨207366, by rfl⟩ : syracuseStep 552977 = 414733) B414733
theorem B618529 : Blo 362758 618529 := bstep (se 2 (by rfl) ⟨231948, by rfl⟩ : syracuseStep 618529 = 463897) B463897
theorem B618563 : Blo 362758 618563 := bstep (se 1 (by rfl) ⟨463922, by rfl⟩ : syracuseStep 618563 = 927845) B927845
theorem B520273 : Blo 362758 520273 := bstep (se 2 (by rfl) ⟨195102, by rfl⟩ : syracuseStep 520273 = 390205) B390205
theorem B880739 : Blo 362758 880739 := bstep (se 1 (by rfl) ⟨660554, by rfl⟩ : syracuseStep 880739 = 1321109) B1321109
theorem B618691 : Blo 362758 618691 := bstep (se 1 (by rfl) ⟨464018, by rfl⟩ : syracuseStep 618691 = 928037) B928037
theorem B6254819 : Blo 362758 6254819 := bstep (se 1 (by rfl) ⟨4691114, by rfl⟩ : syracuseStep 6254819 = 9382229) B9382229
theorem B880931 : Blo 362758 880931 := bstep (se 1 (by rfl) ⟨660698, by rfl⟩ : syracuseStep 880931 = 1321397) B1321397
theorem B4714805 : Blo 362758 4714805 := bstep (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) B442013
theorem B618833 : Blo 362758 618833 := bstep (se 2 (by rfl) ⟨232062, by rfl⟩ : syracuseStep 618833 = 464125) B464125
theorem B389491 : Blo 362758 389491 := bstep (se 1 (by rfl) ⟨292118, by rfl⟩ : syracuseStep 389491 = 584237) B584237
theorem B520609 : Blo 362758 520609 := bstep (se 2 (by rfl) ⟨195228, by rfl⟩ : syracuseStep 520609 = 390457) B390457
theorem B553475 : Blo 362758 553475 := bstep (se 1 (by rfl) ⟨415106, by rfl⟩ : syracuseStep 553475 = 830213) B830213
theorem B586435 : Blo 362758 586435 := bstep (se 1 (by rfl) ⟨439826, by rfl⟩ : syracuseStep 586435 = 879653) B879653
theorem B5206837 : Blo 362758 5206837 := bstep (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) B488141
theorem B4682609 : Blo 362758 4682609 := bstep (se 2 (by rfl) ⟨1755978, by rfl⟩ : syracuseStep 4682609 = 3511957) B3511957
theorem B1110989 : Blo 362758 1110989 := bstep (se 3 (by rfl) ⟨208310, by rfl⟩ : syracuseStep 1110989 = 416621) B416621
theorem B521201 : Blo 362758 521201 := bstep (se 2 (by rfl) ⟨195450, by rfl⟩ : syracuseStep 521201 = 390901) B390901
theorem B816209 : Blo 362758 816209 := bstep (se 2 (by rfl) ⟨306078, by rfl⟩ : syracuseStep 816209 = 612157) B612157
theorem B816227 : Blo 362758 816227 := bstep (se 1 (by rfl) ⟨612170, by rfl⟩ : syracuseStep 816227 = 1224341) B1224341
theorem B2290801 : Blo 362758 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B2782349 : Blo 362758 2782349 := bstep (se 3 (by rfl) ⟨521690, by rfl⟩ : syracuseStep 2782349 = 1043381) B1043381
theorem B1242307 : Blo 362758 1242307 := bstep (se 1 (by rfl) ⟨931730, by rfl⟩ : syracuseStep 1242307 = 1863461) B1863461
theorem B587107 : Blo 362758 587107 := bstep (se 1 (by rfl) ⟨440330, by rfl⟩ : syracuseStep 587107 = 880661) B880661
theorem B816497 : Blo 362758 816497 := bstep (se 2 (by rfl) ⟨306186, by rfl⟩ : syracuseStep 816497 = 612373) B612373
theorem B816515 : Blo 362758 816515 := bstep (se 1 (by rfl) ⟨612386, by rfl⟩ : syracuseStep 816515 = 1224773) B1224773
theorem B521731 : Blo 362758 521731 := bstep (se 1 (by rfl) ⟨391298, by rfl⟩ : syracuseStep 521731 = 782597) B782597
theorem B816785 : Blo 362758 816785 := bstep (se 2 (by rfl) ⟨306294, by rfl⟩ : syracuseStep 816785 = 612589) B612589
theorem B816803 : Blo 362758 816803 := bstep (se 1 (by rfl) ⟨612602, by rfl⟩ : syracuseStep 816803 = 1225205) B1225205
theorem B587521 : Blo 362758 587521 := bstep (se 2 (by rfl) ⟨220320, by rfl⟩ : syracuseStep 587521 = 440641) B440641
theorem B522067 : Blo 362758 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B817073 : Blo 362758 817073 := bstep (se 2 (by rfl) ⟨306402, by rfl⟩ : syracuseStep 817073 = 612805) B612805
theorem B1111985 : Blo 362758 1111985 := bstep (se 2 (by rfl) ⟨416994, by rfl⟩ : syracuseStep 1111985 = 833989) B833989
theorem B817091 : Blo 362758 817091 := bstep (se 1 (by rfl) ⟨612818, by rfl⟩ : syracuseStep 817091 = 1225637) B1225637
theorem B8353763 : Blo 362758 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B1767473 : Blo 362758 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B4454453 : Blo 362758 4454453 := bstep (se 5 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 4454453 = 417605) B417605
theorem B817361 : Blo 362758 817361 := bstep (se 2 (by rfl) ⟨306510, by rfl⟩ : syracuseStep 817361 = 613021) B613021
theorem B817379 : Blo 362758 817379 := bstep (se 1 (by rfl) ⟨613034, by rfl⟩ : syracuseStep 817379 = 1226069) B1226069
theorem B3111281 : Blo 362758 3111281 := bstep (se 2 (by rfl) ⟨1166730, by rfl⟩ : syracuseStep 3111281 = 2333461) B2333461
theorem B817649 : Blo 362758 817649 := bstep (se 2 (by rfl) ⟨306618, by rfl⟩ : syracuseStep 817649 = 613237) B613237
theorem B817667 : Blo 362758 817667 := bstep (se 1 (by rfl) ⟨613250, by rfl⟩ : syracuseStep 817667 = 1226501) B1226501
theorem B3504653 : Blo 362758 3504653 := bstep (se 3 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 3504653 = 1314245) B1314245
theorem B1145507 : Blo 362758 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B817937 : Blo 362758 817937 := bstep (se 2 (by rfl) ⟨306726, by rfl⟩ : syracuseStep 817937 = 613453) B613453
theorem B817955 : Blo 362758 817955 := bstep (se 1 (by rfl) ⟨613466, by rfl⟩ : syracuseStep 817955 = 1226933) B1226933
theorem B2227085 : Blo 362758 2227085 := bstep (se 3 (by rfl) ⟨417578, by rfl⟩ : syracuseStep 2227085 = 835157) B835157
theorem B1309603 : Blo 362758 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B4062221 : Blo 362758 4062221 := bstep (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) B1523333
theorem B818225 : Blo 362758 818225 := bstep (se 2 (by rfl) ⟨306834, by rfl⟩ : syracuseStep 818225 = 613669) B613669
theorem B818243 : Blo 362758 818243 := bstep (se 1 (by rfl) ⟨613682, by rfl⟩ : syracuseStep 818243 = 1227365) B1227365
theorem B2325773 : Blo 362758 2325773 := bstep (se 3 (by rfl) ⟨436082, by rfl⟩ : syracuseStep 2325773 = 872165) B872165
theorem B621859 : Blo 362758 621859 := bstep (se 1 (by rfl) ⟨466394, by rfl⟩ : syracuseStep 621859 = 932789) B932789
theorem B818513 : Blo 362758 818513 := bstep (se 2 (by rfl) ⟨306942, by rfl⟩ : syracuseStep 818513 = 613885) B613885
theorem B818531 : Blo 362758 818531 := bstep (se 1 (by rfl) ⟨613898, by rfl⟩ : syracuseStep 818531 = 1227797) B1227797
theorem B4423025 : Blo 362758 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B1244593 : Blo 362758 1244593 := bstep (se 2 (by rfl) ⟨466722, by rfl⟩ : syracuseStep 1244593 = 933445) B933445
theorem B491059 : Blo 362758 491059 := bstep (se 1 (by rfl) ⟨368294, by rfl⟩ : syracuseStep 491059 = 736589) B736589
theorem B818801 : Blo 362758 818801 := bstep (se 2 (by rfl) ⟨307050, by rfl⟩ : syracuseStep 818801 = 614101) B614101
theorem B818819 : Blo 362758 818819 := bstep (se 1 (by rfl) ⟨614114, by rfl⟩ : syracuseStep 818819 = 1228229) B1228229
theorem B5603185 : Blo 362758 5603185 := bstep (se 2 (by rfl) ⟨2101194, by rfl⟩ : syracuseStep 5603185 = 4202389) B4202389
theorem B819089 : Blo 362758 819089 := bstep (se 2 (by rfl) ⟨307158, by rfl⟩ : syracuseStep 819089 = 614317) B614317
theorem B819107 : Blo 362758 819107 := bstep (se 1 (by rfl) ⟨614330, by rfl⟩ : syracuseStep 819107 = 1228661) B1228661
theorem B819251 : Blo 362758 819251 := bstep (se 1 (by rfl) ⟨614438, by rfl⟩ : syracuseStep 819251 = 1228877) B1228877
theorem B819287 : Blo 362758 819287 := bstep (se 1 (by rfl) ⟨614465, by rfl⟩ : syracuseStep 819287 = 1228931) B1228931
theorem B819467 : Blo 362758 819467 := bstep (se 1 (by rfl) ⟨614600, by rfl⟩ : syracuseStep 819467 = 1229201) B1229201
theorem B819521 : Blo 362758 819521 := bstep (se 2 (by rfl) ⟨307320, by rfl⟩ : syracuseStep 819521 = 614641) B614641
theorem B2326877 : Blo 362758 2326877 := bstep (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) B872579
theorem B393611 : Blo 362758 393611 := bstep (se 1 (by rfl) ⟨295208, by rfl⟩ : syracuseStep 393611 = 590417) B590417
theorem B1966609 : Blo 362758 1966609 := bstep (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) B1474957
theorem B819737 : Blo 362758 819737 := bstep (se 2 (by rfl) ⟨307401, by rfl⟩ : syracuseStep 819737 = 614803) B614803
theorem B2327105 : Blo 362758 2327105 := bstep (se 2 (by rfl) ⟨872664, by rfl⟩ : syracuseStep 2327105 = 1745329) B1745329
theorem B819827 : Blo 362758 819827 := bstep (se 1 (by rfl) ⟨614870, by rfl⟩ : syracuseStep 819827 = 1229741) B1229741
theorem B819863 : Blo 362758 819863 := bstep (se 1 (by rfl) ⟨614897, by rfl⟩ : syracuseStep 819863 = 1229795) B1229795
theorem B492313 : Blo 362758 492313 := bstep (se 2 (by rfl) ⟨184617, by rfl⟩ : syracuseStep 492313 = 369235) B369235
theorem B918337 : Blo 362758 918337 := bstep (se 2 (by rfl) ⟨344376, by rfl⟩ : syracuseStep 918337 = 688753) B688753
theorem B820043 : Blo 362758 820043 := bstep (se 1 (by rfl) ⟨615032, by rfl⟩ : syracuseStep 820043 = 1230065) B1230065
theorem B820097 : Blo 362758 820097 := bstep (se 2 (by rfl) ⟨307536, by rfl⟩ : syracuseStep 820097 = 615073) B615073
theorem B689239 : Blo 362758 689239 := bstep (se 1 (by rfl) ⟨516929, by rfl⟩ : syracuseStep 689239 = 1033859) B1033859
theorem B820313 : Blo 362758 820313 := bstep (se 2 (by rfl) ⟨307617, by rfl⟩ : syracuseStep 820313 = 615235) B615235
theorem B1377431 : Blo 362758 1377431 := bstep (se 1 (by rfl) ⟨1033073, by rfl⟩ : syracuseStep 1377431 = 2066147) B2066147
theorem B820403 : Blo 362758 820403 := bstep (se 1 (by rfl) ⟨615302, by rfl⟩ : syracuseStep 820403 = 1230605) B1230605
theorem B820439 : Blo 362758 820439 := bstep (se 1 (by rfl) ⟨615329, by rfl⟩ : syracuseStep 820439 = 1230659) B1230659
theorem B460171 : Blo 362758 460171 := bstep (se 1 (by rfl) ⟨345128, by rfl⟩ : syracuseStep 460171 = 690257) B690257
theorem B820619 : Blo 362758 820619 := bstep (se 1 (by rfl) ⟨615464, by rfl⟩ : syracuseStep 820619 = 1230929) B1230929
theorem B918935 : Blo 362758 918935 := bstep (se 1 (by rfl) ⟨689201, by rfl⟩ : syracuseStep 918935 = 1378403) B1378403
theorem B820673 : Blo 362758 820673 := bstep (se 2 (by rfl) ⟨307752, by rfl⟩ : syracuseStep 820673 = 615505) B615505
theorem B493015 : Blo 362758 493015 := bstep (se 1 (by rfl) ⟨369761, by rfl⟩ : syracuseStep 493015 = 739523) B739523
theorem B1181249 : Blo 362758 1181249 := bstep (se 2 (by rfl) ⟨442968, by rfl⟩ : syracuseStep 1181249 = 885937) B885937
theorem B1246795 : Blo 362758 1246795 := bstep (se 1 (by rfl) ⟨935096, by rfl⟩ : syracuseStep 1246795 = 1870193) B1870193
theorem B394871 : Blo 362758 394871 := bstep (se 1 (by rfl) ⟨296153, by rfl⟩ : syracuseStep 394871 = 592307) B592307
theorem B820889 : Blo 362758 820889 := bstep (se 2 (by rfl) ⟨307833, by rfl⟩ : syracuseStep 820889 = 615667) B615667
theorem B820979 : Blo 362758 820979 := bstep (se 1 (by rfl) ⟨615734, by rfl⟩ : syracuseStep 820979 = 1231469) B1231469
theorem B821015 : Blo 362758 821015 := bstep (se 1 (by rfl) ⟨615761, by rfl⟩ : syracuseStep 821015 = 1231523) B1231523
theorem B690059 : Blo 362758 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B690113 : Blo 362758 690113 := bstep (se 2 (by rfl) ⟨258792, by rfl⟩ : syracuseStep 690113 = 517585) B517585
theorem B821195 : Blo 362758 821195 := bstep (se 1 (by rfl) ⟨615896, by rfl⟩ : syracuseStep 821195 = 1231793) B1231793
theorem B821249 : Blo 362758 821249 := bstep (se 2 (by rfl) ⟨307968, by rfl⟩ : syracuseStep 821249 = 615937) B615937
theorem B657433 : Blo 362758 657433 := bstep (se 2 (by rfl) ⟨246537, by rfl⟩ : syracuseStep 657433 = 493075) B493075
theorem B7473221 : Blo 362758 7473221 := bstep (se 4 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 7473221 = 1401229) B1401229
theorem B1312861 : Blo 362758 1312861 := bstep (se 3 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 1312861 = 492323) B492323
theorem B919745 : Blo 362758 919745 := bstep (se 2 (by rfl) ⟨344904, by rfl⟩ : syracuseStep 919745 = 689809) B689809
theorem B821465 : Blo 362758 821465 := bstep (se 2 (by rfl) ⟨308049, by rfl⟩ : syracuseStep 821465 = 616099) B616099
theorem B362763 : Blo 362758 362763 := bstep (se 1 (by rfl) ⟨272072, by rfl⟩ : syracuseStep 362763 = 544145) B544145
theorem B362775 : Blo 362758 362775 := bstep (se 1 (by rfl) ⟨272081, by rfl⟩ : syracuseStep 362775 = 544163) B544163
theorem B362795 : Blo 362758 362795 := bstep (se 1 (by rfl) ⟨272096, by rfl⟩ : syracuseStep 362795 = 544193) B544193
theorem B6850861 : Blo 362758 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B821555 : Blo 362758 821555 := bstep (se 1 (by rfl) ⟨616166, by rfl⟩ : syracuseStep 821555 = 1232333) B1232333
theorem B362807 : Blo 362758 362807 := bstep (se 1 (by rfl) ⟨272105, by rfl⟩ : syracuseStep 362807 = 544211) B544211
theorem B362827 : Blo 362758 362827 := bstep (se 1 (by rfl) ⟨272120, by rfl⟩ : syracuseStep 362827 = 544241) B544241
theorem B362839 : Blo 362758 362839 := bstep (se 1 (by rfl) ⟨272129, by rfl⟩ : syracuseStep 362839 = 544259) B544259
theorem B461143 : Blo 362758 461143 := bstep (se 1 (by rfl) ⟨345857, by rfl⟩ : syracuseStep 461143 = 691715) B691715
theorem B821591 : Blo 362758 821591 := bstep (se 1 (by rfl) ⟨616193, by rfl⟩ : syracuseStep 821591 = 1232387) B1232387
theorem B362859 : Blo 362758 362859 := bstep (se 1 (by rfl) ⟨272144, by rfl⟩ : syracuseStep 362859 = 544289) B544289
theorem B362871 : Blo 362758 362871 := bstep (se 1 (by rfl) ⟨272153, by rfl⟩ : syracuseStep 362871 = 544307) B544307
theorem B1378691 : Blo 362758 1378691 := bstep (se 1 (by rfl) ⟨1034018, by rfl⟩ : syracuseStep 1378691 = 2068037) B2068037
theorem B362891 : Blo 362758 362891 := bstep (se 1 (by rfl) ⟨272168, by rfl⟩ : syracuseStep 362891 = 544337) B544337
theorem B362903 : Blo 362758 362903 := bstep (se 1 (by rfl) ⟨272177, by rfl⟩ : syracuseStep 362903 = 544355) B544355
theorem B362923 : Blo 362758 362923 := bstep (se 1 (by rfl) ⟨272192, by rfl⟩ : syracuseStep 362923 = 544385) B544385
theorem B1182131 : Blo 362758 1182131 := bstep (se 1 (by rfl) ⟨886598, by rfl⟩ : syracuseStep 1182131 = 1773197) B1773197
theorem B362935 : Blo 362758 362935 := bstep (se 1 (by rfl) ⟨272201, by rfl⟩ : syracuseStep 362935 = 544403) B544403
theorem B362955 : Blo 362758 362955 := bstep (se 1 (by rfl) ⟨272216, by rfl⟩ : syracuseStep 362955 = 544433) B544433
theorem B362967 : Blo 362758 362967 := bstep (se 1 (by rfl) ⟨272225, by rfl⟩ : syracuseStep 362967 = 544451) B544451
theorem B362987 : Blo 362758 362987 := bstep (se 1 (by rfl) ⟨272240, by rfl⟩ : syracuseStep 362987 = 544481) B544481
theorem B362999 : Blo 362758 362999 := bstep (se 1 (by rfl) ⟨272249, by rfl⟩ : syracuseStep 362999 = 544499) B544499
theorem B363019 : Blo 362758 363019 := bstep (se 1 (by rfl) ⟨272264, by rfl⟩ : syracuseStep 363019 = 544529) B544529
theorem B821771 : Blo 362758 821771 := bstep (se 1 (by rfl) ⟨616328, by rfl⟩ : syracuseStep 821771 = 1232657) B1232657
theorem B363031 : Blo 362758 363031 := bstep (se 1 (by rfl) ⟨272273, by rfl⟩ : syracuseStep 363031 = 544547) B544547
theorem B363051 : Blo 362758 363051 := bstep (se 1 (by rfl) ⟨272288, by rfl⟩ : syracuseStep 363051 = 544577) B544577
theorem B363063 : Blo 362758 363063 := bstep (se 1 (by rfl) ⟨272297, by rfl⟩ : syracuseStep 363063 = 544595) B544595
theorem B821825 : Blo 362758 821825 := bstep (se 2 (by rfl) ⟨308184, by rfl⟩ : syracuseStep 821825 = 616369) B616369
theorem B363083 : Blo 362758 363083 := bstep (se 1 (by rfl) ⟨272312, by rfl⟩ : syracuseStep 363083 = 544625) B544625
theorem B363095 : Blo 362758 363095 := bstep (se 1 (by rfl) ⟨272321, by rfl⟩ : syracuseStep 363095 = 544643) B544643
theorem B363115 : Blo 362758 363115 := bstep (se 1 (by rfl) ⟨272336, by rfl⟩ : syracuseStep 363115 = 544673) B544673
theorem B363127 : Blo 362758 363127 := bstep (se 1 (by rfl) ⟨272345, by rfl⟩ : syracuseStep 363127 = 544691) B544691
theorem B363147 : Blo 362758 363147 := bstep (se 1 (by rfl) ⟨272360, by rfl⟩ : syracuseStep 363147 = 544721) B544721
theorem B363159 : Blo 362758 363159 := bstep (se 1 (by rfl) ⟨272369, by rfl⟩ : syracuseStep 363159 = 544739) B544739
theorem B363179 : Blo 362758 363179 := bstep (se 1 (by rfl) ⟨272384, by rfl⟩ : syracuseStep 363179 = 544769) B544769
theorem B363191 : Blo 362758 363191 := bstep (se 1 (by rfl) ⟨272393, by rfl⟩ : syracuseStep 363191 = 544787) B544787
theorem B363211 : Blo 362758 363211 := bstep (se 1 (by rfl) ⟨272408, by rfl⟩ : syracuseStep 363211 = 544817) B544817
theorem B363223 : Blo 362758 363223 := bstep (se 1 (by rfl) ⟨272417, by rfl⟩ : syracuseStep 363223 = 544835) B544835
theorem B920281 : Blo 362758 920281 := bstep (se 2 (by rfl) ⟨345105, by rfl⟩ : syracuseStep 920281 = 690211) B690211
theorem B363243 : Blo 362758 363243 := bstep (se 1 (by rfl) ⟨272432, by rfl⟩ : syracuseStep 363243 = 544865) B544865
theorem B363255 : Blo 362758 363255 := bstep (se 1 (by rfl) ⟨272441, by rfl⟩ : syracuseStep 363255 = 544883) B544883
theorem B363275 : Blo 362758 363275 := bstep (se 1 (by rfl) ⟨272456, by rfl⟩ : syracuseStep 363275 = 544913) B544913
theorem B2329361 : Blo 362758 2329361 := bstep (se 2 (by rfl) ⟨873510, by rfl⟩ : syracuseStep 2329361 = 1747021) B1747021
theorem B363287 : Blo 362758 363287 := bstep (se 1 (by rfl) ⟨272465, by rfl⟩ : syracuseStep 363287 = 544931) B544931
theorem B822041 : Blo 362758 822041 := bstep (se 2 (by rfl) ⟨308265, by rfl⟩ : syracuseStep 822041 = 616531) B616531
theorem B363307 : Blo 362758 363307 := bstep (se 1 (by rfl) ⟨272480, by rfl⟩ : syracuseStep 363307 = 544961) B544961
theorem B363319 : Blo 362758 363319 := bstep (se 1 (by rfl) ⟨272489, by rfl⟩ : syracuseStep 363319 = 544979) B544979
theorem B1837889 : Blo 362758 1837889 := bstep (se 2 (by rfl) ⟨689208, by rfl⟩ : syracuseStep 1837889 = 1378417) B1378417
theorem B363339 : Blo 362758 363339 := bstep (se 1 (by rfl) ⟨272504, by rfl⟩ : syracuseStep 363339 = 545009) B545009
theorem B363351 : Blo 362758 363351 := bstep (se 1 (by rfl) ⟨272513, by rfl⟩ : syracuseStep 363351 = 545027) B545027
theorem B691031 : Blo 362758 691031 := bstep (se 1 (by rfl) ⟨518273, by rfl⟩ : syracuseStep 691031 = 1036547) B1036547
theorem B985945 : Blo 362758 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B363371 : Blo 362758 363371 := bstep (se 1 (by rfl) ⟨272528, by rfl⟩ : syracuseStep 363371 = 545057) B545057
theorem B822131 : Blo 362758 822131 := bstep (se 1 (by rfl) ⟨616598, by rfl⟩ : syracuseStep 822131 = 1233197) B1233197
theorem B363383 : Blo 362758 363383 := bstep (se 1 (by rfl) ⟨272537, by rfl⟩ : syracuseStep 363383 = 545075) B545075
theorem B363403 : Blo 362758 363403 := bstep (se 1 (by rfl) ⟨272552, by rfl⟩ : syracuseStep 363403 = 545105) B545105
theorem B363415 : Blo 362758 363415 := bstep (se 1 (by rfl) ⟨272561, by rfl⟩ : syracuseStep 363415 = 545123) B545123
theorem B822167 : Blo 362758 822167 := bstep (se 1 (by rfl) ⟨616625, by rfl⟩ : syracuseStep 822167 = 1233251) B1233251
theorem B363435 : Blo 362758 363435 := bstep (se 1 (by rfl) ⟨272576, by rfl⟩ : syracuseStep 363435 = 545153) B545153
theorem B363447 : Blo 362758 363447 := bstep (se 1 (by rfl) ⟨272585, by rfl⟩ : syracuseStep 363447 = 545171) B545171
theorem B363467 : Blo 362758 363467 := bstep (se 1 (by rfl) ⟨272600, by rfl⟩ : syracuseStep 363467 = 545201) B545201
theorem B363479 : Blo 362758 363479 := bstep (se 1 (by rfl) ⟨272609, by rfl⟩ : syracuseStep 363479 = 545219) B545219
theorem B21269465 : Blo 362758 21269465 := bstep (se 2 (by rfl) ⟨7976049, by rfl⟩ : syracuseStep 21269465 = 15952099) B15952099
theorem B50760665 : Blo 362758 50760665 := bstep (se 2 (by rfl) ⟨19035249, by rfl⟩ : syracuseStep 50760665 = 38070499) B38070499
theorem B363499 : Blo 362758 363499 := bstep (se 1 (by rfl) ⟨272624, by rfl⟩ : syracuseStep 363499 = 545249) B545249
theorem B363511 : Blo 362758 363511 := bstep (se 1 (by rfl) ⟨272633, by rfl⟩ : syracuseStep 363511 = 545267) B545267
theorem B363531 : Blo 362758 363531 := bstep (se 1 (by rfl) ⟨272648, by rfl⟩ : syracuseStep 363531 = 545297) B545297
theorem B363543 : Blo 362758 363543 := bstep (se 1 (by rfl) ⟨272657, by rfl⟩ : syracuseStep 363543 = 545315) B545315
theorem B2755619 : Blo 362758 2755619 := bstep (se 1 (by rfl) ⟨2066714, by rfl⟩ : syracuseStep 2755619 = 4133429) B4133429
theorem B363563 : Blo 362758 363563 := bstep (se 1 (by rfl) ⟨272672, by rfl⟩ : syracuseStep 363563 = 545345) B545345
theorem B363575 : Blo 362758 363575 := bstep (se 1 (by rfl) ⟨272681, by rfl⟩ : syracuseStep 363575 = 545363) B545363
theorem B363595 : Blo 362758 363595 := bstep (se 1 (by rfl) ⟨272696, by rfl⟩ : syracuseStep 363595 = 545393) B545393
theorem B822347 : Blo 362758 822347 := bstep (se 1 (by rfl) ⟨616760, by rfl⟩ : syracuseStep 822347 = 1233521) B1233521
theorem B363607 : Blo 362758 363607 := bstep (se 1 (by rfl) ⟨272705, by rfl⟩ : syracuseStep 363607 = 545411) B545411
theorem B363627 : Blo 362758 363627 := bstep (se 1 (by rfl) ⟨272720, by rfl⟩ : syracuseStep 363627 = 545441) B545441
theorem B363639 : Blo 362758 363639 := bstep (se 1 (by rfl) ⟨272729, by rfl⟩ : syracuseStep 363639 = 545459) B545459
theorem B822401 : Blo 362758 822401 := bstep (se 2 (by rfl) ⟨308400, by rfl⟩ : syracuseStep 822401 = 616801) B616801
theorem B363659 : Blo 362758 363659 := bstep (se 1 (by rfl) ⟨272744, by rfl⟩ : syracuseStep 363659 = 545489) B545489
theorem B461963 : Blo 362758 461963 := bstep (se 1 (by rfl) ⟨346472, by rfl⟩ : syracuseStep 461963 = 692945) B692945
theorem B363671 : Blo 362758 363671 := bstep (se 1 (by rfl) ⟨272753, by rfl⟩ : syracuseStep 363671 = 545507) B545507
theorem B363691 : Blo 362758 363691 := bstep (se 1 (by rfl) ⟨272768, by rfl⟩ : syracuseStep 363691 = 545537) B545537
theorem B363703 : Blo 362758 363703 := bstep (se 1 (by rfl) ⟨272777, by rfl⟩ : syracuseStep 363703 = 545555) B545555
theorem B363723 : Blo 362758 363723 := bstep (se 1 (by rfl) ⟨272792, by rfl⟩ : syracuseStep 363723 = 545585) B545585
theorem B363735 : Blo 362758 363735 := bstep (se 1 (by rfl) ⟨272801, by rfl⟩ : syracuseStep 363735 = 545603) B545603
theorem B363755 : Blo 362758 363755 := bstep (se 1 (by rfl) ⟨272816, by rfl⟩ : syracuseStep 363755 = 545633) B545633
theorem B363767 : Blo 362758 363767 := bstep (se 1 (by rfl) ⟨272825, by rfl⟩ : syracuseStep 363767 = 545651) B545651
theorem B363787 : Blo 362758 363787 := bstep (se 1 (by rfl) ⟨272840, by rfl⟩ : syracuseStep 363787 = 545681) B545681
theorem B363799 : Blo 362758 363799 := bstep (se 1 (by rfl) ⟨272849, by rfl⟩ : syracuseStep 363799 = 545699) B545699
theorem B363819 : Blo 362758 363819 := bstep (se 1 (by rfl) ⟨272864, by rfl⟩ : syracuseStep 363819 = 545729) B545729
theorem B363831 : Blo 362758 363831 := bstep (se 1 (by rfl) ⟨272873, by rfl⟩ : syracuseStep 363831 = 545747) B545747
theorem B363851 : Blo 362758 363851 := bstep (se 1 (by rfl) ⟨272888, by rfl⟩ : syracuseStep 363851 = 545777) B545777
theorem B363863 : Blo 362758 363863 := bstep (se 1 (by rfl) ⟨272897, by rfl⟩ : syracuseStep 363863 = 545795) B545795
theorem B822617 : Blo 362758 822617 := bstep (se 2 (by rfl) ⟨308481, by rfl⟩ : syracuseStep 822617 = 616963) B616963
theorem B363883 : Blo 362758 363883 := bstep (se 1 (by rfl) ⟨272912, by rfl⟩ : syracuseStep 363883 = 545825) B545825
theorem B691571 : Blo 362758 691571 := bstep (se 1 (by rfl) ⟨518678, by rfl⟩ : syracuseStep 691571 = 1037357) B1037357
theorem B363895 : Blo 362758 363895 := bstep (se 1 (by rfl) ⟨272921, by rfl⟩ : syracuseStep 363895 = 545843) B545843
theorem B363915 : Blo 362758 363915 := bstep (se 1 (by rfl) ⟨272936, by rfl⟩ : syracuseStep 363915 = 545873) B545873
theorem B363927 : Blo 362758 363927 := bstep (se 1 (by rfl) ⟨272945, by rfl⟩ : syracuseStep 363927 = 545891) B545891
theorem B363947 : Blo 362758 363947 := bstep (se 1 (by rfl) ⟨272960, by rfl⟩ : syracuseStep 363947 = 545921) B545921
theorem B822707 : Blo 362758 822707 := bstep (se 1 (by rfl) ⟨617030, by rfl⟩ : syracuseStep 822707 = 1234061) B1234061
theorem B363959 : Blo 362758 363959 := bstep (se 1 (by rfl) ⟨272969, by rfl⟩ : syracuseStep 363959 = 545939) B545939
theorem B363979 : Blo 362758 363979 := bstep (se 1 (by rfl) ⟨272984, by rfl⟩ : syracuseStep 363979 = 545969) B545969
theorem B757207 : Blo 362758 757207 := bstep (se 1 (by rfl) ⟨567905, by rfl⟩ : syracuseStep 757207 = 1135811) B1135811
theorem B363991 : Blo 362758 363991 := bstep (se 1 (by rfl) ⟨272993, by rfl⟩ : syracuseStep 363991 = 545987) B545987
theorem B822743 : Blo 362758 822743 := bstep (se 1 (by rfl) ⟨617057, by rfl⟩ : syracuseStep 822743 = 1234115) B1234115
theorem B364011 : Blo 362758 364011 := bstep (se 1 (by rfl) ⟨273008, by rfl⟩ : syracuseStep 364011 = 546017) B546017
theorem B364023 : Blo 362758 364023 := bstep (se 1 (by rfl) ⟨273017, by rfl⟩ : syracuseStep 364023 = 546035) B546035
theorem B364043 : Blo 362758 364043 := bstep (se 1 (by rfl) ⟨273032, by rfl⟩ : syracuseStep 364043 = 546065) B546065
theorem B364055 : Blo 362758 364055 := bstep (se 1 (by rfl) ⟨273041, by rfl⟩ : syracuseStep 364055 = 546083) B546083
theorem B364075 : Blo 362758 364075 := bstep (se 1 (by rfl) ⟨273056, by rfl⟩ : syracuseStep 364075 = 546113) B546113
theorem B364087 : Blo 362758 364087 := bstep (se 1 (by rfl) ⟨273065, by rfl⟩ : syracuseStep 364087 = 546131) B546131
theorem B364107 : Blo 362758 364107 := bstep (se 1 (by rfl) ⟨273080, by rfl⟩ : syracuseStep 364107 = 546161) B546161
theorem B364119 : Blo 362758 364119 := bstep (se 1 (by rfl) ⟨273089, by rfl⟩ : syracuseStep 364119 = 546179) B546179
theorem B364139 : Blo 362758 364139 := bstep (se 1 (by rfl) ⟨273104, by rfl⟩ : syracuseStep 364139 = 546209) B546209
theorem B364151 : Blo 362758 364151 := bstep (se 1 (by rfl) ⟨273113, by rfl⟩ : syracuseStep 364151 = 546227) B546227
theorem B364171 : Blo 362758 364171 := bstep (se 1 (by rfl) ⟨273128, by rfl⟩ : syracuseStep 364171 = 546257) B546257
theorem B822923 : Blo 362758 822923 := bstep (se 1 (by rfl) ⟨617192, by rfl⟩ : syracuseStep 822923 = 1234385) B1234385
theorem B364183 : Blo 362758 364183 := bstep (se 1 (by rfl) ⟨273137, by rfl⟩ : syracuseStep 364183 = 546275) B546275
theorem B364203 : Blo 362758 364203 := bstep (se 1 (by rfl) ⟨273152, by rfl⟩ : syracuseStep 364203 = 546305) B546305
theorem B364215 : Blo 362758 364215 := bstep (se 1 (by rfl) ⟨273161, by rfl⟩ : syracuseStep 364215 = 546323) B546323
theorem B822977 : Blo 362758 822977 := bstep (se 2 (by rfl) ⟨308616, by rfl⟩ : syracuseStep 822977 = 617233) B617233
theorem B15699653 : Blo 362758 15699653 := bstep (se 4 (by rfl) ⟨1471842, by rfl⟩ : syracuseStep 15699653 = 2943685) B2943685
theorem B364235 : Blo 362758 364235 := bstep (se 1 (by rfl) ⟨273176, by rfl⟩ : syracuseStep 364235 = 546353) B546353
theorem B364247 : Blo 362758 364247 := bstep (se 1 (by rfl) ⟨273185, by rfl⟩ : syracuseStep 364247 = 546371) B546371
theorem B364267 : Blo 362758 364267 := bstep (se 1 (by rfl) ⟨273200, by rfl⟩ : syracuseStep 364267 = 546401) B546401
theorem B364279 : Blo 362758 364279 := bstep (se 1 (by rfl) ⟨273209, by rfl⟩ : syracuseStep 364279 = 546419) B546419
theorem B364299 : Blo 362758 364299 := bstep (se 1 (by rfl) ⟨273224, by rfl⟩ : syracuseStep 364299 = 546449) B546449
theorem B364311 : Blo 362758 364311 := bstep (se 1 (by rfl) ⟨273233, by rfl⟩ : syracuseStep 364311 = 546467) B546467
theorem B364331 : Blo 362758 364331 := bstep (se 1 (by rfl) ⟨273248, by rfl⟩ : syracuseStep 364331 = 546497) B546497
theorem B921395 : Blo 362758 921395 := bstep (se 1 (by rfl) ⟨691046, by rfl⟩ : syracuseStep 921395 = 1382093) B1382093
theorem B364343 : Blo 362758 364343 := bstep (se 1 (by rfl) ⟨273257, by rfl⟩ : syracuseStep 364343 = 546515) B546515
theorem B364363 : Blo 362758 364363 := bstep (se 1 (by rfl) ⟨273272, by rfl⟩ : syracuseStep 364363 = 546545) B546545
theorem B462667 : Blo 362758 462667 := bstep (se 1 (by rfl) ⟨347000, by rfl⟩ : syracuseStep 462667 = 694001) B694001
theorem B364375 : Blo 362758 364375 := bstep (se 1 (by rfl) ⟨273281, by rfl⟩ : syracuseStep 364375 = 546563) B546563
theorem B692057 : Blo 362758 692057 := bstep (se 2 (by rfl) ⟨259521, by rfl⟩ : syracuseStep 692057 = 519043) B519043
theorem B364395 : Blo 362758 364395 := bstep (se 1 (by rfl) ⟨273296, by rfl⟩ : syracuseStep 364395 = 546593) B546593
theorem B659315 : Blo 362758 659315 := bstep (se 1 (by rfl) ⟨494486, by rfl⟩ : syracuseStep 659315 = 988973) B988973
theorem B364407 : Blo 362758 364407 := bstep (se 1 (by rfl) ⟨273305, by rfl⟩ : syracuseStep 364407 = 546611) B546611
theorem B2068355 : Blo 362758 2068355 := bstep (se 1 (by rfl) ⟨1551266, by rfl⟩ : syracuseStep 2068355 = 3102533) B3102533
theorem B364427 : Blo 362758 364427 := bstep (se 1 (by rfl) ⟨273320, by rfl⟩ : syracuseStep 364427 = 546641) B546641
theorem B364439 : Blo 362758 364439 := bstep (se 1 (by rfl) ⟨273329, by rfl⟩ : syracuseStep 364439 = 546659) B546659
theorem B823193 : Blo 362758 823193 := bstep (se 2 (by rfl) ⟨308697, by rfl⟩ : syracuseStep 823193 = 617395) B617395
theorem B364459 : Blo 362758 364459 := bstep (se 1 (by rfl) ⟨273344, by rfl⟩ : syracuseStep 364459 = 546689) B546689
theorem B364471 : Blo 362758 364471 := bstep (se 1 (by rfl) ⟨273353, by rfl⟩ : syracuseStep 364471 = 546707) B546707
theorem B364491 : Blo 362758 364491 := bstep (se 1 (by rfl) ⟨273368, by rfl⟩ : syracuseStep 364491 = 546737) B546737
theorem B364503 : Blo 362758 364503 := bstep (se 1 (by rfl) ⟨273377, by rfl⟩ : syracuseStep 364503 = 546755) B546755
theorem B364523 : Blo 362758 364523 := bstep (se 1 (by rfl) ⟨273392, by rfl⟩ : syracuseStep 364523 = 546785) B546785
theorem B823283 : Blo 362758 823283 := bstep (se 1 (by rfl) ⟨617462, by rfl⟩ : syracuseStep 823283 = 1234925) B1234925
theorem B364535 : Blo 362758 364535 := bstep (se 1 (by rfl) ⟨273401, by rfl⟩ : syracuseStep 364535 = 546803) B546803
theorem B364555 : Blo 362758 364555 := bstep (se 1 (by rfl) ⟨273416, by rfl⟩ : syracuseStep 364555 = 546833) B546833
theorem B364567 : Blo 362758 364567 := bstep (se 1 (by rfl) ⟨273425, by rfl⟩ : syracuseStep 364567 = 546851) B546851
theorem B823319 : Blo 362758 823319 := bstep (se 1 (by rfl) ⟨617489, by rfl⟩ : syracuseStep 823319 = 1234979) B1234979
theorem B364587 : Blo 362758 364587 := bstep (se 1 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 364587 = 546881) B546881
theorem B364599 : Blo 362758 364599 := bstep (se 1 (by rfl) ⟨273449, by rfl⟩ : syracuseStep 364599 = 546899) B546899
theorem B5279813 : Blo 362758 5279813 := bstep (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) B989965
theorem B364619 : Blo 362758 364619 := bstep (se 1 (by rfl) ⟨273464, by rfl⟩ : syracuseStep 364619 = 546929) B546929
theorem B1052747 : Blo 362758 1052747 := bstep (se 1 (by rfl) ⟨789560, by rfl⟩ : syracuseStep 1052747 = 1579121) B1579121
theorem B364631 : Blo 362758 364631 := bstep (se 1 (by rfl) ⟨273473, by rfl⟩ : syracuseStep 364631 = 546947) B546947
theorem B462935 : Blo 362758 462935 := bstep (se 1 (by rfl) ⟨347201, by rfl⟩ : syracuseStep 462935 = 694403) B694403
theorem B921689 : Blo 362758 921689 := bstep (se 2 (by rfl) ⟨345633, by rfl⟩ : syracuseStep 921689 = 691267) B691267
theorem B364651 : Blo 362758 364651 := bstep (se 1 (by rfl) ⟨273488, by rfl⟩ : syracuseStep 364651 = 546977) B546977
theorem B364663 : Blo 362758 364663 := bstep (se 1 (by rfl) ⟨273497, by rfl⟩ : syracuseStep 364663 = 546995) B546995
theorem B364683 : Blo 362758 364683 := bstep (se 1 (by rfl) ⟨273512, by rfl⟩ : syracuseStep 364683 = 547025) B547025
theorem B364695 : Blo 362758 364695 := bstep (se 1 (by rfl) ⟨273521, by rfl⟩ : syracuseStep 364695 = 547043) B547043
theorem B364715 : Blo 362758 364715 := bstep (se 1 (by rfl) ⟨273536, by rfl⟩ : syracuseStep 364715 = 547073) B547073
theorem B364727 : Blo 362758 364727 := bstep (se 1 (by rfl) ⟨273545, by rfl⟩ : syracuseStep 364727 = 547091) B547091
theorem B987329 : Blo 362758 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B364747 : Blo 362758 364747 := bstep (se 1 (by rfl) ⟨273560, by rfl⟩ : syracuseStep 364747 = 547121) B547121
theorem B823499 : Blo 362758 823499 := bstep (se 1 (by rfl) ⟨617624, by rfl⟩ : syracuseStep 823499 = 1235249) B1235249
theorem B364759 : Blo 362758 364759 := bstep (se 1 (by rfl) ⟨273569, by rfl⟩ : syracuseStep 364759 = 547139) B547139
theorem B364779 : Blo 362758 364779 := bstep (se 1 (by rfl) ⟨273584, by rfl⟩ : syracuseStep 364779 = 547169) B547169
theorem B364791 : Blo 362758 364791 := bstep (se 1 (by rfl) ⟨273593, by rfl⟩ : syracuseStep 364791 = 547187) B547187
theorem B823553 : Blo 362758 823553 := bstep (se 2 (by rfl) ⟨308832, by rfl⟩ : syracuseStep 823553 = 617665) B617665
theorem B364811 : Blo 362758 364811 := bstep (se 1 (by rfl) ⟨273608, by rfl⟩ : syracuseStep 364811 = 547217) B547217
theorem B364823 : Blo 362758 364823 := bstep (se 1 (by rfl) ⟨273617, by rfl⟩ : syracuseStep 364823 = 547235) B547235
theorem B364843 : Blo 362758 364843 := bstep (se 1 (by rfl) ⟨273632, by rfl⟩ : syracuseStep 364843 = 547265) B547265
theorem B364855 : Blo 362758 364855 := bstep (se 1 (by rfl) ⟨273641, by rfl⟩ : syracuseStep 364855 = 547283) B547283
theorem B2068811 : Blo 362758 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B364875 : Blo 362758 364875 := bstep (se 1 (by rfl) ⟨273656, by rfl⟩ : syracuseStep 364875 = 547313) B547313
theorem B790859 : Blo 362758 790859 := bstep (se 1 (by rfl) ⟨593144, by rfl⟩ : syracuseStep 790859 = 1186289) B1186289
theorem B364887 : Blo 362758 364887 := bstep (se 1 (by rfl) ⟨273665, by rfl⟩ : syracuseStep 364887 = 547331) B547331
theorem B364907 : Blo 362758 364907 := bstep (se 1 (by rfl) ⟨273680, by rfl⟩ : syracuseStep 364907 = 547361) B547361
theorem B364919 : Blo 362758 364919 := bstep (se 1 (by rfl) ⟨273689, by rfl⟩ : syracuseStep 364919 = 547379) B547379
theorem B364939 : Blo 362758 364939 := bstep (se 1 (by rfl) ⟨273704, by rfl⟩ : syracuseStep 364939 = 547409) B547409
theorem B364951 : Blo 362758 364951 := bstep (se 1 (by rfl) ⟨273713, by rfl⟩ : syracuseStep 364951 = 547427) B547427
theorem B364971 : Blo 362758 364971 := bstep (se 1 (by rfl) ⟨273728, by rfl⟩ : syracuseStep 364971 = 547457) B547457
theorem B364983 : Blo 362758 364983 := bstep (se 1 (by rfl) ⟨273737, by rfl⟩ : syracuseStep 364983 = 547475) B547475
theorem B365003 : Blo 362758 365003 := bstep (se 1 (by rfl) ⟨273752, by rfl⟩ : syracuseStep 365003 = 547505) B547505
theorem B365015 : Blo 362758 365015 := bstep (se 1 (by rfl) ⟨273761, by rfl⟩ : syracuseStep 365015 = 547523) B547523
theorem B823769 : Blo 362758 823769 := bstep (se 2 (by rfl) ⟨308913, by rfl⟩ : syracuseStep 823769 = 617827) B617827
theorem B365035 : Blo 362758 365035 := bstep (se 1 (by rfl) ⟨273776, by rfl⟩ : syracuseStep 365035 = 547553) B547553
theorem B365047 : Blo 362758 365047 := bstep (se 1 (by rfl) ⟨273785, by rfl⟩ : syracuseStep 365047 = 547571) B547571
theorem B365067 : Blo 362758 365067 := bstep (se 1 (by rfl) ⟨273800, by rfl⟩ : syracuseStep 365067 = 547601) B547601
theorem B365079 : Blo 362758 365079 := bstep (se 1 (by rfl) ⟨273809, by rfl⟩ : syracuseStep 365079 = 547619) B547619
theorem B365099 : Blo 362758 365099 := bstep (se 1 (by rfl) ⟨273824, by rfl⟩ : syracuseStep 365099 = 547649) B547649
theorem B823859 : Blo 362758 823859 := bstep (se 1 (by rfl) ⟨617894, by rfl⟩ : syracuseStep 823859 = 1235789) B1235789
theorem B365111 : Blo 362758 365111 := bstep (se 1 (by rfl) ⟨273833, by rfl⟩ : syracuseStep 365111 = 547667) B547667
theorem B365131 : Blo 362758 365131 := bstep (se 1 (by rfl) ⟨273848, by rfl⟩ : syracuseStep 365131 = 547697) B547697
theorem B365143 : Blo 362758 365143 := bstep (se 1 (by rfl) ⟨273857, by rfl⟩ : syracuseStep 365143 = 547715) B547715
theorem B823895 : Blo 362758 823895 := bstep (se 1 (by rfl) ⟨617921, by rfl⟩ : syracuseStep 823895 = 1235843) B1235843
theorem B365163 : Blo 362758 365163 := bstep (se 1 (by rfl) ⟨273872, by rfl⟩ : syracuseStep 365163 = 547745) B547745
theorem B365175 : Blo 362758 365175 := bstep (se 1 (by rfl) ⟨273881, by rfl⟩ : syracuseStep 365175 = 547763) B547763
theorem B365195 : Blo 362758 365195 := bstep (se 1 (by rfl) ⟨273896, by rfl⟩ : syracuseStep 365195 = 547793) B547793
theorem B660107 : Blo 362758 660107 := bstep (se 1 (by rfl) ⟨495080, by rfl⟩ : syracuseStep 660107 = 990161) B990161
theorem B365207 : Blo 362758 365207 := bstep (se 1 (by rfl) ⟨273905, by rfl⟩ : syracuseStep 365207 = 547811) B547811
theorem B365227 : Blo 362758 365227 := bstep (se 1 (by rfl) ⟨273920, by rfl⟩ : syracuseStep 365227 = 547841) B547841
theorem B365239 : Blo 362758 365239 := bstep (se 1 (by rfl) ⟨273929, by rfl⟩ : syracuseStep 365239 = 547859) B547859
theorem B365259 : Blo 362758 365259 := bstep (se 1 (by rfl) ⟨273944, by rfl⟩ : syracuseStep 365259 = 547889) B547889
theorem B365271 : Blo 362758 365271 := bstep (se 1 (by rfl) ⟨273953, by rfl⟩ : syracuseStep 365271 = 547907) B547907
theorem B1839833 : Blo 362758 1839833 := bstep (se 2 (by rfl) ⟨689937, by rfl⟩ : syracuseStep 1839833 = 1379875) B1379875
theorem B365291 : Blo 362758 365291 := bstep (se 1 (by rfl) ⟨273968, by rfl⟩ : syracuseStep 365291 = 547937) B547937
theorem B365303 : Blo 362758 365303 := bstep (se 1 (by rfl) ⟨273977, by rfl⟩ : syracuseStep 365303 = 547955) B547955
theorem B365323 : Blo 362758 365323 := bstep (se 1 (by rfl) ⟨273992, by rfl⟩ : syracuseStep 365323 = 547985) B547985
theorem B824075 : Blo 362758 824075 := bstep (se 1 (by rfl) ⟨618056, by rfl⟩ : syracuseStep 824075 = 1236113) B1236113
theorem B365335 : Blo 362758 365335 := bstep (se 1 (by rfl) ⟨274001, by rfl⟩ : syracuseStep 365335 = 548003) B548003
theorem B463639 : Blo 362758 463639 := bstep (se 1 (by rfl) ⟨347729, by rfl⟩ : syracuseStep 463639 = 695459) B695459
theorem B365355 : Blo 362758 365355 := bstep (se 1 (by rfl) ⟨274016, by rfl⟩ : syracuseStep 365355 = 548033) B548033
theorem B365367 : Blo 362758 365367 := bstep (se 1 (by rfl) ⟨274025, by rfl⟩ : syracuseStep 365367 = 548051) B548051
theorem B4002625 : Blo 362758 4002625 := bstep (se 2 (by rfl) ⟨1500984, by rfl⟩ : syracuseStep 4002625 = 3001969) B3001969
theorem B824129 : Blo 362758 824129 := bstep (se 2 (by rfl) ⟨309048, by rfl⟩ : syracuseStep 824129 = 618097) B618097
theorem B365387 : Blo 362758 365387 := bstep (se 1 (by rfl) ⟨274040, by rfl⟩ : syracuseStep 365387 = 548081) B548081
theorem B365399 : Blo 362758 365399 := bstep (se 1 (by rfl) ⟨274049, by rfl⟩ : syracuseStep 365399 = 548099) B548099
theorem B365419 : Blo 362758 365419 := bstep (se 1 (by rfl) ⟨274064, by rfl⟩ : syracuseStep 365419 = 548129) B548129
theorem B365431 : Blo 362758 365431 := bstep (se 1 (by rfl) ⟨274073, by rfl⟩ : syracuseStep 365431 = 548147) B548147
theorem B365451 : Blo 362758 365451 := bstep (se 1 (by rfl) ⟨274088, by rfl⟩ : syracuseStep 365451 = 548177) B548177
theorem B365463 : Blo 362758 365463 := bstep (se 1 (by rfl) ⟨274097, by rfl⟩ : syracuseStep 365463 = 548195) B548195
theorem B365483 : Blo 362758 365483 := bstep (se 1 (by rfl) ⟨274112, by rfl⟩ : syracuseStep 365483 = 548225) B548225
theorem B365495 : Blo 362758 365495 := bstep (se 1 (by rfl) ⟨274121, by rfl⟩ : syracuseStep 365495 = 548243) B548243
theorem B365515 : Blo 362758 365515 := bstep (se 1 (by rfl) ⟨274136, by rfl⟩ : syracuseStep 365515 = 548273) B548273
theorem B365527 : Blo 362758 365527 := bstep (se 1 (by rfl) ⟨274145, by rfl⟩ : syracuseStep 365527 = 548291) B548291
theorem B365547 : Blo 362758 365547 := bstep (se 1 (by rfl) ⟨274160, by rfl⟩ : syracuseStep 365547 = 548321) B548321
theorem B365559 : Blo 362758 365559 := bstep (se 1 (by rfl) ⟨274169, by rfl⟩ : syracuseStep 365559 = 548339) B548339
theorem B365579 : Blo 362758 365579 := bstep (se 1 (by rfl) ⟨274184, by rfl⟩ : syracuseStep 365579 = 548369) B548369
theorem B365591 : Blo 362758 365591 := bstep (se 1 (by rfl) ⟨274193, by rfl⟩ : syracuseStep 365591 = 548387) B548387
theorem B824345 : Blo 362758 824345 := bstep (se 2 (by rfl) ⟨309129, by rfl⟩ : syracuseStep 824345 = 618259) B618259
theorem B3118115 : Blo 362758 3118115 := bstep (se 1 (by rfl) ⟨2338586, by rfl⟩ : syracuseStep 3118115 = 4677173) B4677173
theorem B365611 : Blo 362758 365611 := bstep (se 1 (by rfl) ⟨274208, by rfl⟩ : syracuseStep 365611 = 548417) B548417
theorem B365623 : Blo 362758 365623 := bstep (se 1 (by rfl) ⟨274217, by rfl⟩ : syracuseStep 365623 = 548435) B548435
theorem B365643 : Blo 362758 365643 := bstep (se 1 (by rfl) ⟨274232, by rfl⟩ : syracuseStep 365643 = 548465) B548465
theorem B365655 : Blo 362758 365655 := bstep (se 1 (by rfl) ⟨274241, by rfl⟩ : syracuseStep 365655 = 548483) B548483
theorem B365675 : Blo 362758 365675 := bstep (se 1 (by rfl) ⟨274256, by rfl⟩ : syracuseStep 365675 = 548513) B548513
theorem B824435 : Blo 362758 824435 := bstep (se 1 (by rfl) ⟨618326, by rfl⟩ : syracuseStep 824435 = 1236653) B1236653
theorem B365687 : Blo 362758 365687 := bstep (se 1 (by rfl) ⟨274265, by rfl⟩ : syracuseStep 365687 = 548531) B548531
theorem B365707 : Blo 362758 365707 := bstep (se 1 (by rfl) ⟨274280, by rfl⟩ : syracuseStep 365707 = 548561) B548561
theorem B365719 : Blo 362758 365719 := bstep (se 1 (by rfl) ⟨274289, by rfl⟩ : syracuseStep 365719 = 548579) B548579
theorem B824471 : Blo 362758 824471 := bstep (se 1 (by rfl) ⟨618353, by rfl⟩ : syracuseStep 824471 = 1236707) B1236707
theorem B365739 : Blo 362758 365739 := bstep (se 1 (by rfl) ⟨274304, by rfl⟩ : syracuseStep 365739 = 548609) B548609
theorem B365751 : Blo 362758 365751 := bstep (se 1 (by rfl) ⟨274313, by rfl⟩ : syracuseStep 365751 = 548627) B548627
theorem B365771 : Blo 362758 365771 := bstep (se 1 (by rfl) ⟨274328, by rfl⟩ : syracuseStep 365771 = 548657) B548657
theorem B365783 : Blo 362758 365783 := bstep (se 1 (by rfl) ⟨274337, by rfl⟩ : syracuseStep 365783 = 548675) B548675
theorem B365803 : Blo 362758 365803 := bstep (se 1 (by rfl) ⟨274352, by rfl⟩ : syracuseStep 365803 = 548705) B548705
theorem B365815 : Blo 362758 365815 := bstep (se 1 (by rfl) ⟨274361, by rfl⟩ : syracuseStep 365815 = 548723) B548723
theorem B693515 : Blo 362758 693515 := bstep (se 1 (by rfl) ⟨520136, by rfl⟩ : syracuseStep 693515 = 1040273) B1040273
theorem B365835 : Blo 362758 365835 := bstep (se 1 (by rfl) ⟨274376, by rfl⟩ : syracuseStep 365835 = 548753) B548753
theorem B365847 : Blo 362758 365847 := bstep (se 1 (by rfl) ⟨274385, by rfl⟩ : syracuseStep 365847 = 548771) B548771
theorem B365867 : Blo 362758 365867 := bstep (se 1 (by rfl) ⟨274400, by rfl⟩ : syracuseStep 365867 = 548801) B548801
theorem B1316147 : Blo 362758 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B365879 : Blo 362758 365879 := bstep (se 1 (by rfl) ⟨274409, by rfl⟩ : syracuseStep 365879 = 548819) B548819
theorem B365899 : Blo 362758 365899 := bstep (se 1 (by rfl) ⟨274424, by rfl⟩ : syracuseStep 365899 = 548849) B548849
theorem B824651 : Blo 362758 824651 := bstep (se 1 (by rfl) ⟨618488, by rfl⟩ : syracuseStep 824651 = 1236977) B1236977
theorem B365911 : Blo 362758 365911 := bstep (se 1 (by rfl) ⟨274433, by rfl⟩ : syracuseStep 365911 = 548867) B548867
theorem B365931 : Blo 362758 365931 := bstep (se 1 (by rfl) ⟨274448, by rfl⟩ : syracuseStep 365931 = 548897) B548897
theorem B365943 : Blo 362758 365943 := bstep (se 1 (by rfl) ⟨274457, by rfl⟩ : syracuseStep 365943 = 548915) B548915
theorem B824705 : Blo 362758 824705 := bstep (se 2 (by rfl) ⟨309264, by rfl⟩ : syracuseStep 824705 = 618529) B618529
theorem B365963 : Blo 362758 365963 := bstep (se 1 (by rfl) ⟨274472, by rfl⟩ : syracuseStep 365963 = 548945) B548945
theorem B365975 : Blo 362758 365975 := bstep (se 1 (by rfl) ⟨274481, by rfl⟩ : syracuseStep 365975 = 548963) B548963
theorem B365995 : Blo 362758 365995 := bstep (se 1 (by rfl) ⟨274496, by rfl⟩ : syracuseStep 365995 = 548993) B548993
theorem B1381805 : Blo 362758 1381805 := bstep (se 3 (by rfl) ⟨259088, by rfl⟩ : syracuseStep 1381805 = 518177) B518177
theorem B366007 : Blo 362758 366007 := bstep (se 1 (by rfl) ⟨274505, by rfl⟩ : syracuseStep 366007 = 549011) B549011
theorem B693697 : Blo 362758 693697 := bstep (se 2 (by rfl) ⟨260136, by rfl⟩ : syracuseStep 693697 = 520273) B520273
theorem B366027 : Blo 362758 366027 := bstep (se 1 (by rfl) ⟨274520, by rfl⟩ : syracuseStep 366027 = 549041) B549041
theorem B366039 : Blo 362758 366039 := bstep (se 1 (by rfl) ⟨274529, by rfl⟩ : syracuseStep 366039 = 549059) B549059
theorem B366059 : Blo 362758 366059 := bstep (se 1 (by rfl) ⟨274544, by rfl⟩ : syracuseStep 366059 = 549089) B549089
theorem B366071 : Blo 362758 366071 := bstep (se 1 (by rfl) ⟨274553, by rfl⟩ : syracuseStep 366071 = 549107) B549107
theorem B366091 : Blo 362758 366091 := bstep (se 1 (by rfl) ⟨274568, by rfl⟩ : syracuseStep 366091 = 549137) B549137
theorem B366103 : Blo 362758 366103 := bstep (se 1 (by rfl) ⟨274577, by rfl⟩ : syracuseStep 366103 = 549155) B549155
theorem B366123 : Blo 362758 366123 := bstep (se 1 (by rfl) ⟨274592, by rfl⟩ : syracuseStep 366123 = 549185) B549185
theorem B366135 : Blo 362758 366135 := bstep (se 1 (by rfl) ⟨274601, by rfl⟩ : syracuseStep 366135 = 549203) B549203
theorem B366155 : Blo 362758 366155 := bstep (se 1 (by rfl) ⟨274616, by rfl⟩ : syracuseStep 366155 = 549233) B549233
theorem B366167 : Blo 362758 366167 := bstep (se 1 (by rfl) ⟨274625, by rfl⟩ : syracuseStep 366167 = 549251) B549251
theorem B824921 : Blo 362758 824921 := bstep (se 2 (by rfl) ⟨309345, by rfl⟩ : syracuseStep 824921 = 618691) B618691
theorem B366187 : Blo 362758 366187 := bstep (se 1 (by rfl) ⟨274640, by rfl⟩ : syracuseStep 366187 = 549281) B549281
theorem B366199 : Blo 362758 366199 := bstep (se 1 (by rfl) ⟨274649, by rfl⟩ : syracuseStep 366199 = 549299) B549299
theorem B366219 : Blo 362758 366219 := bstep (se 1 (by rfl) ⟨274664, by rfl⟩ : syracuseStep 366219 = 549329) B549329
theorem B366231 : Blo 362758 366231 := bstep (se 1 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 366231 = 549347) B549347
theorem B366251 : Blo 362758 366251 := bstep (se 1 (by rfl) ⟨274688, by rfl⟩ : syracuseStep 366251 = 549377) B549377
theorem B825011 : Blo 362758 825011 := bstep (se 1 (by rfl) ⟨618758, by rfl⟩ : syracuseStep 825011 = 1237517) B1237517
theorem B366263 : Blo 362758 366263 := bstep (se 1 (by rfl) ⟨274697, by rfl⟩ : syracuseStep 366263 = 549395) B549395
theorem B923339 : Blo 362758 923339 := bstep (se 1 (by rfl) ⟨692504, by rfl⟩ : syracuseStep 923339 = 1385009) B1385009
theorem B366283 : Blo 362758 366283 := bstep (se 1 (by rfl) ⟨274712, by rfl⟩ : syracuseStep 366283 = 549425) B549425
theorem B366295 : Blo 362758 366295 := bstep (se 1 (by rfl) ⟨274721, by rfl⟩ : syracuseStep 366295 = 549443) B549443
theorem B825047 : Blo 362758 825047 := bstep (se 1 (by rfl) ⟨618785, by rfl⟩ : syracuseStep 825047 = 1237571) B1237571
theorem B366315 : Blo 362758 366315 := bstep (se 1 (by rfl) ⟨274736, by rfl⟩ : syracuseStep 366315 = 549473) B549473
theorem B366327 : Blo 362758 366327 := bstep (se 1 (by rfl) ⟨274745, by rfl⟩ : syracuseStep 366327 = 549491) B549491
theorem B366347 : Blo 362758 366347 := bstep (se 1 (by rfl) ⟨274760, by rfl⟩ : syracuseStep 366347 = 549521) B549521
theorem B366359 : Blo 362758 366359 := bstep (se 1 (by rfl) ⟨274769, by rfl⟩ : syracuseStep 366359 = 549539) B549539
theorem B366379 : Blo 362758 366379 := bstep (se 1 (by rfl) ⟨274784, by rfl⟩ : syracuseStep 366379 = 549569) B549569
theorem B366391 : Blo 362758 366391 := bstep (se 1 (by rfl) ⟨274793, by rfl⟩ : syracuseStep 366391 = 549587) B549587
theorem B366411 : Blo 362758 366411 := bstep (se 1 (by rfl) ⟨274808, by rfl⟩ : syracuseStep 366411 = 549617) B549617
theorem B366423 : Blo 362758 366423 := bstep (se 1 (by rfl) ⟨274817, by rfl⟩ : syracuseStep 366423 = 549635) B549635
theorem B366443 : Blo 362758 366443 := bstep (se 1 (by rfl) ⟨274832, by rfl⟩ : syracuseStep 366443 = 549665) B549665
theorem B366455 : Blo 362758 366455 := bstep (se 1 (by rfl) ⟨274841, by rfl⟩ : syracuseStep 366455 = 549683) B549683
theorem B694145 : Blo 362758 694145 := bstep (se 2 (by rfl) ⟨260304, by rfl⟩ : syracuseStep 694145 = 520609) B520609
theorem B366475 : Blo 362758 366475 := bstep (se 1 (by rfl) ⟨274856, by rfl⟩ : syracuseStep 366475 = 549713) B549713
theorem B366487 : Blo 362758 366487 := bstep (se 1 (by rfl) ⟨274865, by rfl⟩ : syracuseStep 366487 = 549731) B549731
theorem B366507 : Blo 362758 366507 := bstep (se 1 (by rfl) ⟨274880, by rfl⟩ : syracuseStep 366507 = 549761) B549761
theorem B366519 : Blo 362758 366519 := bstep (se 1 (by rfl) ⟨274889, by rfl⟩ : syracuseStep 366519 = 549779) B549779
theorem B366539 : Blo 362758 366539 := bstep (se 1 (by rfl) ⟨274904, by rfl⟩ : syracuseStep 366539 = 549809) B549809
theorem B366551 : Blo 362758 366551 := bstep (se 1 (by rfl) ⟨274913, by rfl⟩ : syracuseStep 366551 = 549827) B549827
theorem B366571 : Blo 362758 366571 := bstep (se 1 (by rfl) ⟨274928, by rfl⟩ : syracuseStep 366571 = 549857) B549857
theorem B366583 : Blo 362758 366583 := bstep (se 1 (by rfl) ⟨274937, by rfl⟩ : syracuseStep 366583 = 549875) B549875
theorem B366603 : Blo 362758 366603 := bstep (se 1 (by rfl) ⟨274952, by rfl⟩ : syracuseStep 366603 = 549905) B549905
theorem B366615 : Blo 362758 366615 := bstep (se 1 (by rfl) ⟨274961, by rfl⟩ : syracuseStep 366615 = 549923) B549923
theorem B366635 : Blo 362758 366635 := bstep (se 1 (by rfl) ⟨274976, by rfl⟩ : syracuseStep 366635 = 549953) B549953
theorem B366647 : Blo 362758 366647 := bstep (se 1 (by rfl) ⟨274985, by rfl⟩ : syracuseStep 366647 = 549971) B549971
theorem B366667 : Blo 362758 366667 := bstep (se 1 (by rfl) ⟨275000, by rfl⟩ : syracuseStep 366667 = 550001) B550001
theorem B366679 : Blo 362758 366679 := bstep (se 1 (by rfl) ⟨275009, by rfl⟩ : syracuseStep 366679 = 550019) B550019
theorem B366699 : Blo 362758 366699 := bstep (se 1 (by rfl) ⟨275024, by rfl⟩ : syracuseStep 366699 = 550049) B550049
theorem B366711 : Blo 362758 366711 := bstep (se 1 (by rfl) ⟨275033, by rfl⟩ : syracuseStep 366711 = 550067) B550067
theorem B366731 : Blo 362758 366731 := bstep (se 1 (by rfl) ⟨275048, by rfl⟩ : syracuseStep 366731 = 550097) B550097
theorem B366743 : Blo 362758 366743 := bstep (se 1 (by rfl) ⟨275057, by rfl⟩ : syracuseStep 366743 = 550115) B550115
theorem B1382579 : Blo 362758 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B694487 : Blo 362758 694487 := bstep (se 1 (by rfl) ⟨520865, by rfl⟩ : syracuseStep 694487 = 1041731) B1041731
theorem B989405 : Blo 362758 989405 := bstep (se 3 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 989405 = 371027) B371027
theorem B1841453 : Blo 362758 1841453 := bstep (se 3 (by rfl) ⟨345272, by rfl⟩ : syracuseStep 1841453 = 690545) B690545
theorem B924311 : Blo 362758 924311 := bstep (se 1 (by rfl) ⟨693233, by rfl⟩ : syracuseStep 924311 = 1386467) B1386467
theorem B3054401 : Blo 362758 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B1317707 : Blo 362758 1317707 := bstep (se 1 (by rfl) ⟨988280, by rfl⟩ : syracuseStep 1317707 = 1976561) B1976561
theorem B695155 : Blo 362758 695155 := bstep (se 1 (by rfl) ⟨521366, by rfl⟩ : syracuseStep 695155 = 1042733) B1042733
theorem B6232949 : Blo 362758 6232949 := bstep (se 5 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 6232949 = 584339) B584339
theorem B2333771 : Blo 362758 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B3054685 : Blo 362758 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B924979 : Blo 362758 924979 := bstep (se 1 (by rfl) ⟨693734, by rfl⟩ : syracuseStep 924979 = 1387469) B1387469
theorem B695603 : Blo 362758 695603 := bstep (se 1 (by rfl) ⟨521702, by rfl⟩ : syracuseStep 695603 = 1043405) B1043405
theorem B695641 : Blo 362758 695641 := bstep (se 2 (by rfl) ⟨260865, by rfl⟩ : syracuseStep 695641 = 521731) B521731
theorem B925121 : Blo 362758 925121 := bstep (se 2 (by rfl) ⟨346920, by rfl⟩ : syracuseStep 925121 = 693841) B693841
theorem B368075 : Blo 362758 368075 := bstep (se 1 (by rfl) ⟨276056, by rfl⟩ : syracuseStep 368075 = 552113) B552113
theorem B1580609 : Blo 362758 1580609 := bstep (se 2 (by rfl) ⟨592728, by rfl⟩ : syracuseStep 1580609 = 1185457) B1185457
theorem B1384067 : Blo 362758 1384067 := bstep (se 1 (by rfl) ⟨1038050, by rfl⟩ : syracuseStep 1384067 = 2076101) B2076101
theorem B696089 : Blo 362758 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B368651 : Blo 362758 368651 := bstep (se 1 (by rfl) ⟨276488, by rfl⟩ : syracuseStep 368651 = 552977) B552977
theorem B1384523 : Blo 362758 1384523 := bstep (se 1 (by rfl) ⟨1038392, by rfl⟩ : syracuseStep 1384523 = 2076785) B2076785
theorem B4169879 : Blo 362758 4169879 := bstep (se 1 (by rfl) ⟨3127409, by rfl⟩ : syracuseStep 4169879 = 6254819) B6254819
theorem B2760965 : Blo 362758 2760965 := bstep (se 4 (by rfl) ⟨258840, by rfl⟩ : syracuseStep 2760965 = 517681) B517681
theorem B1384721 : Blo 362758 1384721 := bstep (se 2 (by rfl) ⟨519270, by rfl⟩ : syracuseStep 1384721 = 1038541) B1038541
theorem B368983 : Blo 362758 368983 := bstep (se 1 (by rfl) ⟨276737, by rfl⟩ : syracuseStep 368983 = 553475) B553475
theorem B4432229 : Blo 362758 4432229 := bstep (se 4 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 4432229 = 831043) B831043
theorem B3121739 : Blo 362758 3121739 := bstep (se 1 (by rfl) ⟨2341304, by rfl⟩ : syracuseStep 3121739 = 4682609) B4682609
theorem B3711581 : Blo 362758 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B926387 : Blo 362758 926387 := bstep (se 1 (by rfl) ⟨694790, by rfl⟩ : syracuseStep 926387 = 1389581) B1389581
theorem B467671 : Blo 362758 467671 := bstep (se 1 (by rfl) ⟨350753, by rfl⟩ : syracuseStep 467671 = 701507) B701507
theorem B2073437 : Blo 362758 2073437 := bstep (se 3 (by rfl) ⟨388769, by rfl⟩ : syracuseStep 2073437 = 777539) B777539
theorem B1385495 : Blo 362758 1385495 := bstep (se 1 (by rfl) ⟨1039121, by rfl⟩ : syracuseStep 1385495 = 2078243) B2078243
theorem B926923 : Blo 362758 926923 := bstep (se 1 (by rfl) ⟨695192, by rfl⟩ : syracuseStep 926923 = 1390385) B1390385
theorem B1746137 : Blo 362758 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B1385693 : Blo 362758 1385693 := bstep (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) B519635
theorem B927065 : Blo 362758 927065 := bstep (se 2 (by rfl) ⟨347649, by rfl⟩ : syracuseStep 927065 = 695299) B695299
theorem B2631203 : Blo 362758 2631203 := bstep (se 1 (by rfl) ⟨1973402, by rfl⟩ : syracuseStep 2631203 = 3946805) B3946805
theorem B2074187 : Blo 362758 2074187 := bstep (se 1 (by rfl) ⟨1555640, by rfl⟩ : syracuseStep 2074187 = 3111281) B3111281
theorem B2336435 : Blo 362758 2336435 := bstep (se 1 (by rfl) ⟨1752326, by rfl⟩ : syracuseStep 2336435 = 3504653) B3504653
theorem B829145 : Blo 362758 829145 := bstep (se 2 (by rfl) ⟨310929, by rfl⟩ : syracuseStep 829145 = 621859) B621859
theorem B1550173 : Blo 362758 1550173 := bstep (se 3 (by rfl) ⟨290657, by rfl⟩ : syracuseStep 1550173 = 581315) B581315
theorem B1484723 : Blo 362758 1484723 := bstep (se 1 (by rfl) ⟨1113542, by rfl⟩ : syracuseStep 1484723 = 2227085) B2227085
theorem B1320907 : Blo 362758 1320907 := bstep (se 1 (by rfl) ⟨990680, by rfl⟩ : syracuseStep 1320907 = 1981361) B1981361
theorem B1845341 : Blo 362758 1845341 := bstep (se 3 (by rfl) ⟨346001, by rfl⟩ : syracuseStep 1845341 = 692003) B692003
theorem B1976471 : Blo 362758 1976471 := bstep (se 1 (by rfl) ⟨1482353, by rfl⟩ : syracuseStep 1976471 = 2964707) B2964707
theorem B927895 : Blo 362758 927895 := bstep (se 1 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 927895 = 1391843) B1391843
theorem B1550515 : Blo 362758 1550515 := bstep (se 1 (by rfl) ⟨1162886, by rfl⟩ : syracuseStep 1550515 = 2325773) B2325773
theorem B928331 : Blo 362758 928331 := bstep (se 1 (by rfl) ⟨696248, by rfl⟩ : syracuseStep 928331 = 1392497) B1392497
theorem B2763395 : Blo 362758 2763395 := bstep (se 1 (by rfl) ⟨2072546, by rfl⟩ : syracuseStep 2763395 = 4145093) B4145093
theorem B1583833 : Blo 362758 1583833 := bstep (se 2 (by rfl) ⟨593937, by rfl⟩ : syracuseStep 1583833 = 1187875) B1187875
theorem B1190963 : Blo 362758 1190963 := bstep (se 1 (by rfl) ⟨893222, by rfl⟩ : syracuseStep 1190963 = 1786445) B1786445
theorem B830539 : Blo 362758 830539 := bstep (se 1 (by rfl) ⟨622904, by rfl⟩ : syracuseStep 830539 = 1245809) B1245809
theorem B535627 : Blo 362758 535627 := bstep (se 1 (by rfl) ⟨401720, by rfl⟩ : syracuseStep 535627 = 803441) B803441
theorem B1387651 : Blo 362758 1387651 := bstep (se 1 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 1387651 = 2081477) B2081477
theorem B2075827 : Blo 362758 2075827 := bstep (se 1 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 2075827 = 3113741) B3113741
theorem B3124403 : Blo 362758 3124403 := bstep (se 1 (by rfl) ⟨2343302, by rfl⟩ : syracuseStep 3124403 = 4686605) B4686605
theorem B1387955 : Blo 362758 1387955 := bstep (se 1 (by rfl) ⟨1040966, by rfl⟩ : syracuseStep 1387955 = 2081933) B2081933
theorem B1224395 : Blo 362758 1224395 := bstep (se 1 (by rfl) ⟨918296, by rfl⟩ : syracuseStep 1224395 = 1836593) B1836593
theorem B1486637 : Blo 362758 1486637 := bstep (se 3 (by rfl) ⟨278744, by rfl⟩ : syracuseStep 1486637 = 557489) B557489
theorem B1224665 : Blo 362758 1224665 := bstep (se 2 (by rfl) ⟨459249, by rfl⟩ : syracuseStep 1224665 = 918499) B918499
theorem B1388609 : Blo 362758 1388609 := bstep (se 2 (by rfl) ⟨520728, by rfl⟩ : syracuseStep 1388609 = 1041457) B1041457
theorem B1847447 : Blo 362758 1847447 := bstep (se 1 (by rfl) ⟨1385585, by rfl⟩ : syracuseStep 1847447 = 2771171) B2771171
theorem B3125465 : Blo 362758 3125465 := bstep (se 2 (by rfl) ⟨1172049, by rfl⟩ : syracuseStep 3125465 = 2344099) B2344099
theorem B700823 : Blo 362758 700823 := bstep (se 1 (by rfl) ⟨525617, by rfl⟩ : syracuseStep 700823 = 1051235) B1051235
theorem B2240947 : Blo 362758 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B2667043 : Blo 362758 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B2077285 : Blo 362758 2077285 := bstep (se 4 (by rfl) ⟨194745, by rfl⟩ : syracuseStep 2077285 = 389491) B389491
theorem B1225367 : Blo 362758 1225367 := bstep (se 1 (by rfl) ⟨919025, by rfl⟩ : syracuseStep 1225367 = 1838051) B1838051
theorem B2962241 : Blo 362758 2962241 := bstep (se 2 (by rfl) ⟨1110840, by rfl⟩ : syracuseStep 2962241 = 2221681) B2221681
theorem B439447 : Blo 362758 439447 := bstep (se 1 (by rfl) ⟨329585, by rfl⟩ : syracuseStep 439447 = 659171) B659171
theorem B1225907 : Blo 362758 1225907 := bstep (se 1 (by rfl) ⟨919430, by rfl⟩ : syracuseStep 1225907 = 1838861) B1838861
theorem B6206705 : Blo 362758 6206705 := bstep (se 2 (by rfl) ⟨2327514, by rfl⟩ : syracuseStep 6206705 = 4655029) B4655029
theorem B1389869 : Blo 362758 1389869 := bstep (se 3 (by rfl) ⟨260600, by rfl⟩ : syracuseStep 1389869 = 521201) B521201
theorem B1389899 : Blo 362758 1389899 := bstep (se 1 (by rfl) ⟨1042424, by rfl⟩ : syracuseStep 1389899 = 2084849) B2084849
theorem B2340227 : Blo 362758 2340227 := bstep (se 1 (by rfl) ⟨1755170, by rfl⟩ : syracuseStep 2340227 = 3510341) B3510341
theorem B1226177 : Blo 362758 1226177 := bstep (se 2 (by rfl) ⟨459816, by rfl⟩ : syracuseStep 1226177 = 919633) B919633
theorem B439831 : Blo 362758 439831 := bstep (se 1 (by rfl) ⟨329873, by rfl⟩ : syracuseStep 439831 = 659747) B659747
theorem B11417219 : Blo 362758 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B1881731 : Blo 362758 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B440023 : Blo 362758 440023 := bstep (se 1 (by rfl) ⟨330017, by rfl⟩ : syracuseStep 440023 = 660035) B660035
theorem B1554137 : Blo 362758 1554137 := bstep (se 2 (by rfl) ⟨582801, by rfl⟩ : syracuseStep 1554137 = 1165603) B1165603
theorem B374635 : Blo 362758 374635 := bstep (se 1 (by rfl) ⟨280976, by rfl⟩ : syracuseStep 374635 = 561953) B561953
theorem B2766797 : Blo 362758 2766797 := bstep (se 3 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 2766797 = 1037549) B1037549
theorem B1390553 : Blo 362758 1390553 := bstep (se 2 (by rfl) ⟨521457, by rfl⟩ : syracuseStep 1390553 = 1042915) B1042915
theorem B1226717 : Blo 362758 1226717 := bstep (se 3 (by rfl) ⟨230009, by rfl⟩ : syracuseStep 1226717 = 460019) B460019
theorem B1390871 : Blo 362758 1390871 := bstep (se 1 (by rfl) ⟨1043153, by rfl⟩ : syracuseStep 1390871 = 2086307) B2086307
theorem B2767283 : Blo 362758 2767283 := bstep (se 1 (by rfl) ⟨2075462, by rfl⟩ : syracuseStep 2767283 = 4150925) B4150925
theorem B408235 : Blo 362758 408235 := bstep (se 1 (by rfl) ⟨306176, by rfl⟩ : syracuseStep 408235 = 612353) B612353
theorem B408343 : Blo 362758 408343 := bstep (se 1 (by rfl) ⟨306257, by rfl⟩ : syracuseStep 408343 = 612515) B612515
theorem B1391539 : Blo 362758 1391539 := bstep (se 1 (by rfl) ⟨1043654, by rfl⟩ : syracuseStep 1391539 = 2087309) B2087309
theorem B408523 : Blo 362758 408523 := bstep (se 1 (by rfl) ⟨306392, by rfl⟩ : syracuseStep 408523 = 612785) B612785
theorem B408631 : Blo 362758 408631 := bstep (se 1 (by rfl) ⟨306473, by rfl⟩ : syracuseStep 408631 = 612947) B612947
theorem B1227851 : Blo 362758 1227851 := bstep (se 1 (by rfl) ⟨920888, by rfl⟩ : syracuseStep 1227851 = 1841777) B1841777
theorem B408811 : Blo 362758 408811 := bstep (se 1 (by rfl) ⟨306608, by rfl⟩ : syracuseStep 408811 = 613217) B613217
theorem B1555777 : Blo 362758 1555777 := bstep (se 2 (by rfl) ⟨583416, by rfl⟩ : syracuseStep 1555777 = 1166833) B1166833
theorem B408919 : Blo 362758 408919 := bstep (se 1 (by rfl) ⟨306689, by rfl⟩ : syracuseStep 408919 = 613379) B613379
theorem B933209 : Blo 362758 933209 := bstep (se 2 (by rfl) ⟨349953, by rfl⟩ : syracuseStep 933209 = 699907) B699907
theorem B1228121 : Blo 362758 1228121 := bstep (se 2 (by rfl) ⟨460545, by rfl⟩ : syracuseStep 1228121 = 921091) B921091
theorem B409099 : Blo 362758 409099 := bstep (se 1 (by rfl) ⟨306824, by rfl⟩ : syracuseStep 409099 = 613649) B613649
theorem B409207 : Blo 362758 409207 := bstep (se 1 (by rfl) ⟨306905, by rfl⟩ : syracuseStep 409207 = 613811) B613811
theorem B1851011 : Blo 362758 1851011 := bstep (se 1 (by rfl) ⟨1388258, by rfl⟩ : syracuseStep 1851011 = 2776517) B2776517
theorem B409387 : Blo 362758 409387 := bstep (se 1 (by rfl) ⟨307040, by rfl⟩ : syracuseStep 409387 = 614081) B614081
theorem B2768741 : Blo 362758 2768741 := bstep (se 4 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 2768741 = 519139) B519139
theorem B409495 : Blo 362758 409495 := bstep (se 1 (by rfl) ⟨307121, by rfl⟩ : syracuseStep 409495 = 614243) B614243
theorem B1228823 : Blo 362758 1228823 := bstep (se 1 (by rfl) ⟨921617, by rfl⟩ : syracuseStep 1228823 = 1843235) B1843235
theorem B2801729 : Blo 362758 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B409675 : Blo 362758 409675 := bstep (se 1 (by rfl) ⟨307256, by rfl⟩ : syracuseStep 409675 = 614513) B614513
theorem B409783 : Blo 362758 409783 := bstep (se 1 (by rfl) ⟨307337, by rfl⟩ : syracuseStep 409783 = 614675) B614675
theorem B1654987 : Blo 362758 1654987 := bstep (se 1 (by rfl) ⟨1241240, by rfl⟩ : syracuseStep 1654987 = 2482481) B2482481
theorem B2769227 : Blo 362758 2769227 := bstep (se 1 (by rfl) ⟨2076920, by rfl⟩ : syracuseStep 2769227 = 4153841) B4153841
theorem B409963 : Blo 362758 409963 := bstep (se 1 (by rfl) ⟨307472, by rfl⟩ : syracuseStep 409963 = 614945) B614945
theorem B410071 : Blo 362758 410071 := bstep (se 1 (by rfl) ⟨307553, by rfl⟩ : syracuseStep 410071 = 615107) B615107
theorem B1229363 : Blo 362758 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B410251 : Blo 362758 410251 := bstep (se 1 (by rfl) ⟨307688, by rfl⟩ : syracuseStep 410251 = 615377) B615377
theorem B705203 : Blo 362758 705203 := bstep (se 1 (by rfl) ⟨528902, by rfl⟩ : syracuseStep 705203 = 1057805) B1057805
theorem B410359 : Blo 362758 410359 := bstep (se 1 (by rfl) ⟨307769, by rfl⟩ : syracuseStep 410359 = 615539) B615539
theorem B1557265 : Blo 362758 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B1229633 : Blo 362758 1229633 := bstep (se 2 (by rfl) ⟨461112, by rfl⟩ : syracuseStep 1229633 = 922225) B922225
theorem B410539 : Blo 362758 410539 := bstep (se 1 (by rfl) ⟨307904, by rfl⟩ : syracuseStep 410539 = 615809) B615809
theorem B738227 : Blo 362758 738227 := bstep (se 1 (by rfl) ⟨553670, by rfl⟩ : syracuseStep 738227 = 1107341) B1107341
theorem B410647 : Blo 362758 410647 := bstep (se 1 (by rfl) ⟨307985, by rfl⟩ : syracuseStep 410647 = 615971) B615971
theorem B410827 : Blo 362758 410827 := bstep (se 1 (by rfl) ⟨308120, by rfl⟩ : syracuseStep 410827 = 616241) B616241
theorem B1000669 : Blo 362758 1000669 := bstep (se 3 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 1000669 = 375251) B375251
theorem B410935 : Blo 362758 410935 := bstep (se 1 (by rfl) ⟨308201, by rfl⟩ : syracuseStep 410935 = 616403) B616403
theorem B1230173 : Blo 362758 1230173 := bstep (se 3 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 1230173 = 461315) B461315
theorem B411115 : Blo 362758 411115 := bstep (se 1 (by rfl) ⟨308336, by rfl⟩ : syracuseStep 411115 = 616673) B616673
theorem B411223 : Blo 362758 411223 := bstep (se 1 (by rfl) ⟨308417, by rfl⟩ : syracuseStep 411223 = 616835) B616835
theorem B1656409 : Blo 362758 1656409 := bstep (se 2 (by rfl) ⟨621153, by rfl⟩ : syracuseStep 1656409 = 1242307) B1242307
theorem B1328791 : Blo 362758 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B411403 : Blo 362758 411403 := bstep (se 1 (by rfl) ⟨308552, by rfl⟩ : syracuseStep 411403 = 617105) B617105
theorem B1165079 : Blo 362758 1165079 := bstep (se 1 (by rfl) ⟨873809, by rfl⟩ : syracuseStep 1165079 = 1747619) B1747619
theorem B3131237 : Blo 362758 3131237 := bstep (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) B587107
theorem B411511 : Blo 362758 411511 := bstep (se 1 (by rfl) ⟨308633, by rfl⟩ : syracuseStep 411511 = 617267) B617267
theorem B1034201 : Blo 362758 1034201 := bstep (se 2 (by rfl) ⟨387825, by rfl⟩ : syracuseStep 1034201 = 775651) B775651
theorem B411691 : Blo 362758 411691 := bstep (se 1 (by rfl) ⟨308768, by rfl⟩ : syracuseStep 411691 = 617537) B617537
theorem B1034315 : Blo 362758 1034315 := bstep (se 1 (by rfl) ⟨775736, by rfl⟩ : syracuseStep 1034315 = 1551473) B1551473
theorem B1165387 : Blo 362758 1165387 := bstep (se 1 (by rfl) ⟨874040, by rfl⟩ : syracuseStep 1165387 = 1748081) B1748081
theorem B2508893 : Blo 362758 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B411799 : Blo 362758 411799 := bstep (se 1 (by rfl) ⟨308849, by rfl⟩ : syracuseStep 411799 = 617699) B617699
theorem B13355189 : Blo 362758 13355189 := bstep (se 5 (by rfl) ⟨626024, by rfl⟩ : syracuseStep 13355189 = 1252049) B1252049
theorem B2869465 : Blo 362758 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B2083117 : Blo 362758 2083117 := bstep (se 3 (by rfl) ⟨390584, by rfl⟩ : syracuseStep 2083117 = 781169) B781169
theorem B411979 : Blo 362758 411979 := bstep (se 1 (by rfl) ⟨308984, by rfl⟩ : syracuseStep 411979 = 617969) B617969
theorem B412087 : Blo 362758 412087 := bstep (se 1 (by rfl) ⟨309065, by rfl⟩ : syracuseStep 412087 = 618131) B618131
theorem B1231307 : Blo 362758 1231307 := bstep (se 1 (by rfl) ⟨923480, by rfl⟩ : syracuseStep 1231307 = 1846961) B1846961
theorem B412267 : Blo 362758 412267 := bstep (se 1 (by rfl) ⟨309200, by rfl⟩ : syracuseStep 412267 = 618401) B618401
theorem B3492503 : Blo 362758 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B1755827 : Blo 362758 1755827 := bstep (se 1 (by rfl) ⟨1316870, by rfl⟩ : syracuseStep 1755827 = 2633741) B2633741
theorem B412375 : Blo 362758 412375 := bstep (se 1 (by rfl) ⟨309281, by rfl⟩ : syracuseStep 412375 = 618563) B618563
theorem B1231577 : Blo 362758 1231577 := bstep (se 2 (by rfl) ⟨461841, by rfl⟩ : syracuseStep 1231577 = 923683) B923683
theorem B412555 : Blo 362758 412555 := bstep (se 1 (by rfl) ⟨309416, by rfl⟩ : syracuseStep 412555 = 618833) B618833
theorem B1035443 : Blo 362758 1035443 := bstep (se 1 (by rfl) ⟨776582, by rfl⟩ : syracuseStep 1035443 = 1553165) B1553165
theorem B904385 : Blo 362758 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B1854737 : Blo 362758 1854737 := bstep (se 2 (by rfl) ⟨695526, by rfl⟩ : syracuseStep 1854737 = 1391053) B1391053
theorem B740659 : Blo 362758 740659 := bstep (se 1 (by rfl) ⟨555494, by rfl⟩ : syracuseStep 740659 = 1110989) B1110989
theorem B544139 : Blo 362758 544139 := bstep (se 1 (by rfl) ⟨408104, by rfl⟩ : syracuseStep 544139 = 816209) B816209
theorem B544151 : Blo 362758 544151 := bstep (se 1 (by rfl) ⟨408113, by rfl⟩ : syracuseStep 544151 = 816227) B816227
theorem B1232279 : Blo 362758 1232279 := bstep (se 1 (by rfl) ⟨924209, by rfl⟩ : syracuseStep 1232279 = 1848419) B1848419
theorem B1854899 : Blo 362758 1854899 := bstep (se 1 (by rfl) ⟨1391174, by rfl⟩ : syracuseStep 1854899 = 2782349) B2782349
theorem B3132877 : Blo 362758 3132877 := bstep (se 3 (by rfl) ⟨587414, by rfl⟩ : syracuseStep 3132877 = 1174829) B1174829
theorem B544217 : Blo 362758 544217 := bstep (se 2 (by rfl) ⟨204081, by rfl⟩ : syracuseStep 544217 = 408163) B408163
theorem B1035841 : Blo 362758 1035841 := bstep (se 2 (by rfl) ⟨388440, by rfl⟩ : syracuseStep 1035841 = 776881) B776881
theorem B544331 : Blo 362758 544331 := bstep (se 1 (by rfl) ⟨408248, by rfl⟩ : syracuseStep 544331 = 816497) B816497
theorem B544343 : Blo 362758 544343 := bstep (se 1 (by rfl) ⟨408257, by rfl⟩ : syracuseStep 544343 = 816515) B816515
theorem B544409 : Blo 362758 544409 := bstep (se 2 (by rfl) ⟨204153, by rfl⟩ : syracuseStep 544409 = 408307) B408307
theorem B1560323 : Blo 362758 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B544523 : Blo 362758 544523 := bstep (se 1 (by rfl) ⟨408392, by rfl⟩ : syracuseStep 544523 = 816785) B816785
theorem B544535 : Blo 362758 544535 := bstep (se 1 (by rfl) ⟨408401, by rfl⟩ : syracuseStep 544535 = 816803) B816803
theorem B544601 : Blo 362758 544601 := bstep (se 2 (by rfl) ⟨204225, by rfl⟩ : syracuseStep 544601 = 408451) B408451
theorem B1232819 : Blo 362758 1232819 := bstep (se 1 (by rfl) ⟨924614, by rfl⟩ : syracuseStep 1232819 = 1849229) B1849229
theorem B544715 : Blo 362758 544715 := bstep (se 1 (by rfl) ⟨408536, by rfl⟩ : syracuseStep 544715 = 817073) B817073
theorem B741323 : Blo 362758 741323 := bstep (se 1 (by rfl) ⟨555992, by rfl⟩ : syracuseStep 741323 = 1111985) B1111985
theorem B544727 : Blo 362758 544727 := bstep (se 1 (by rfl) ⟨408545, by rfl⟩ : syracuseStep 544727 = 817091) B817091
theorem B544793 : Blo 362758 544793 := bstep (se 2 (by rfl) ⟨204297, by rfl⟩ : syracuseStep 544793 = 408595) B408595
theorem B2969635 : Blo 362758 2969635 := bstep (se 1 (by rfl) ⟨2227226, by rfl⟩ : syracuseStep 2969635 = 4454453) B4454453
theorem B544907 : Blo 362758 544907 := bstep (se 1 (by rfl) ⟨408680, by rfl⟩ : syracuseStep 544907 = 817361) B817361
theorem B544919 : Blo 362758 544919 := bstep (se 1 (by rfl) ⟨408689, by rfl⟩ : syracuseStep 544919 = 817379) B817379
theorem B1233089 : Blo 362758 1233089 := bstep (se 2 (by rfl) ⟨462408, by rfl⟩ : syracuseStep 1233089 = 924817) B924817
theorem B544985 : Blo 362758 544985 := bstep (se 2 (by rfl) ⟨204369, by rfl⟩ : syracuseStep 544985 = 408739) B408739
theorem B3952901 : Blo 362758 3952901 := bstep (se 4 (by rfl) ⟨370584, by rfl⟩ : syracuseStep 3952901 = 741169) B741169
theorem B545099 : Blo 362758 545099 := bstep (se 1 (by rfl) ⟨408824, by rfl⟩ : syracuseStep 545099 = 817649) B817649
theorem B545111 : Blo 362758 545111 := bstep (se 1 (by rfl) ⟨408833, by rfl⟩ : syracuseStep 545111 = 817667) B817667
theorem B1495385 : Blo 362758 1495385 := bstep (se 2 (by rfl) ⟨560769, by rfl⟩ : syracuseStep 1495385 = 1121539) B1121539
theorem B545177 : Blo 362758 545177 := bstep (se 2 (by rfl) ⟨204441, by rfl⟩ : syracuseStep 545177 = 408883) B408883
theorem B545291 : Blo 362758 545291 := bstep (se 1 (by rfl) ⟨408968, by rfl⟩ : syracuseStep 545291 = 817937) B817937
theorem B545303 : Blo 362758 545303 := bstep (se 1 (by rfl) ⟨408977, by rfl⟩ : syracuseStep 545303 = 817955) B817955
theorem B1659457 : Blo 362758 1659457 := bstep (se 2 (by rfl) ⟨622296, by rfl⟩ : syracuseStep 1659457 = 1244593) B1244593
theorem B545369 : Blo 362758 545369 := bstep (se 2 (by rfl) ⟨204513, by rfl⟩ : syracuseStep 545369 = 409027) B409027
theorem B1167961 : Blo 362758 1167961 := bstep (se 2 (by rfl) ⟨437985, by rfl⟩ : syracuseStep 1167961 = 875971) B875971
theorem B2708147 : Blo 362758 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B545483 : Blo 362758 545483 := bstep (se 1 (by rfl) ⟨409112, by rfl⟩ : syracuseStep 545483 = 818225) B818225
theorem B545495 : Blo 362758 545495 := bstep (se 1 (by rfl) ⟨409121, by rfl⟩ : syracuseStep 545495 = 818243) B818243
theorem B1233629 : Blo 362758 1233629 := bstep (se 3 (by rfl) ⟨231305, by rfl⟩ : syracuseStep 1233629 = 462611) B462611
theorem B545561 : Blo 362758 545561 := bstep (se 2 (by rfl) ⟨204585, by rfl⟩ : syracuseStep 545561 = 409171) B409171
theorem B545675 : Blo 362758 545675 := bstep (se 1 (by rfl) ⟨409256, by rfl⟩ : syracuseStep 545675 = 818513) B818513
theorem B545687 : Blo 362758 545687 := bstep (se 1 (by rfl) ⟨409265, by rfl⟩ : syracuseStep 545687 = 818531) B818531
theorem B545753 : Blo 362758 545753 := bstep (se 2 (by rfl) ⟨204657, by rfl⟩ : syracuseStep 545753 = 409315) B409315
theorem B545867 : Blo 362758 545867 := bstep (se 1 (by rfl) ⟨409400, by rfl⟩ : syracuseStep 545867 = 818801) B818801
theorem B545879 : Blo 362758 545879 := bstep (se 1 (by rfl) ⟨409409, by rfl⟩ : syracuseStep 545879 = 818819) B818819
theorem B545945 : Blo 362758 545945 := bstep (se 2 (by rfl) ⟨204729, by rfl⟩ : syracuseStep 545945 = 409459) B409459
theorem B1168577 : Blo 362758 1168577 := bstep (se 2 (by rfl) ⟨438216, by rfl⟩ : syracuseStep 1168577 = 876433) B876433
theorem B5002501 : Blo 362758 5002501 := bstep (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) B937969
theorem B546059 : Blo 362758 546059 := bstep (se 1 (by rfl) ⟨409544, by rfl⟩ : syracuseStep 546059 = 819089) B819089
theorem B546071 : Blo 362758 546071 := bstep (se 1 (by rfl) ⟨409553, by rfl⟩ : syracuseStep 546071 = 819107) B819107
theorem B775489 : Blo 362758 775489 := bstep (se 2 (by rfl) ⟨290808, by rfl⟩ : syracuseStep 775489 = 581617) B581617
theorem B546137 : Blo 362758 546137 := bstep (se 2 (by rfl) ⟨204801, by rfl⟩ : syracuseStep 546137 = 409603) B409603
theorem B546251 : Blo 362758 546251 := bstep (se 1 (by rfl) ⟨409688, by rfl⟩ : syracuseStep 546251 = 819377) B819377
theorem B546263 : Blo 362758 546263 := bstep (se 1 (by rfl) ⟨409697, by rfl⟩ : syracuseStep 546263 = 819395) B819395
theorem B546329 : Blo 362758 546329 := bstep (se 2 (by rfl) ⟨204873, by rfl⟩ : syracuseStep 546329 = 409747) B409747
theorem B2774573 : Blo 362758 2774573 := bstep (se 3 (by rfl) ⟨520232, by rfl⟩ : syracuseStep 2774573 = 1040465) B1040465
theorem B546443 : Blo 362758 546443 := bstep (se 1 (by rfl) ⟨409832, by rfl⟩ : syracuseStep 546443 = 819665) B819665
theorem B775831 : Blo 362758 775831 := bstep (se 1 (by rfl) ⟨581873, by rfl⟩ : syracuseStep 775831 = 1163747) B1163747
theorem B546455 : Blo 362758 546455 := bstep (se 1 (by rfl) ⟨409841, by rfl⟩ : syracuseStep 546455 = 819683) B819683
theorem B546521 : Blo 362758 546521 := bstep (se 2 (by rfl) ⟨204945, by rfl⟩ : syracuseStep 546521 = 409891) B409891
theorem B1103581 : Blo 362758 1103581 := bstep (se 3 (by rfl) ⟨206921, by rfl⟩ : syracuseStep 1103581 = 413843) B413843
theorem B546635 : Blo 362758 546635 := bstep (se 1 (by rfl) ⟨409976, by rfl⟩ : syracuseStep 546635 = 819953) B819953
theorem B1234763 : Blo 362758 1234763 := bstep (se 1 (by rfl) ⟨926072, by rfl⟩ : syracuseStep 1234763 = 1852145) B1852145
theorem B546647 : Blo 362758 546647 := bstep (se 1 (by rfl) ⟨409985, by rfl⟩ : syracuseStep 546647 = 819971) B819971
theorem B546713 : Blo 362758 546713 := bstep (se 2 (by rfl) ⟨205017, by rfl⟩ : syracuseStep 546713 = 410035) B410035
theorem B874433 : Blo 362758 874433 := bstep (se 2 (by rfl) ⟨327912, by rfl⟩ : syracuseStep 874433 = 655825) B655825
theorem B612299 : Blo 362758 612299 := bstep (se 1 (by rfl) ⟨459224, by rfl⟩ : syracuseStep 612299 = 918449) B918449
theorem B546827 : Blo 362758 546827 := bstep (se 1 (by rfl) ⟨410120, by rfl⟩ : syracuseStep 546827 = 820241) B820241
theorem B546839 : Blo 362758 546839 := bstep (se 1 (by rfl) ⟨410129, by rfl⟩ : syracuseStep 546839 = 820259) B820259
theorem B1038359 : Blo 362758 1038359 := bstep (se 1 (by rfl) ⟨778769, by rfl⟩ : syracuseStep 1038359 = 1557539) B1557539
theorem B612427 : Blo 362758 612427 := bstep (se 1 (by rfl) ⟨459320, by rfl⟩ : syracuseStep 612427 = 918641) B918641
theorem B546905 : Blo 362758 546905 := bstep (se 2 (by rfl) ⟨205089, by rfl⟩ : syracuseStep 546905 = 410179) B410179
theorem B1235033 : Blo 362758 1235033 := bstep (se 2 (by rfl) ⟨463137, by rfl⟩ : syracuseStep 1235033 = 926275) B926275
theorem B12572813 : Blo 362758 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B547019 : Blo 362758 547019 := bstep (se 1 (by rfl) ⟨410264, by rfl⟩ : syracuseStep 547019 = 820529) B820529
theorem B547031 : Blo 362758 547031 := bstep (se 1 (by rfl) ⟨410273, by rfl⟩ : syracuseStep 547031 = 820547) B820547
theorem B612569 : Blo 362758 612569 := bstep (se 2 (by rfl) ⟨229713, by rfl⟩ : syracuseStep 612569 = 459427) B459427
theorem B547097 : Blo 362758 547097 := bstep (se 2 (by rfl) ⟨205161, by rfl⟩ : syracuseStep 547097 = 410323) B410323
theorem B612697 : Blo 362758 612697 := bstep (se 2 (by rfl) ⟨229761, by rfl⟩ : syracuseStep 612697 = 459523) B459523
theorem B547211 : Blo 362758 547211 := bstep (se 1 (by rfl) ⟨410408, by rfl⟩ : syracuseStep 547211 = 820817) B820817
theorem B547223 : Blo 362758 547223 := bstep (se 1 (by rfl) ⟨410417, by rfl⟩ : syracuseStep 547223 = 820835) B820835
theorem B547289 : Blo 362758 547289 := bstep (se 2 (by rfl) ⟨205233, by rfl⟩ : syracuseStep 547289 = 410467) B410467
theorem B547403 : Blo 362758 547403 := bstep (se 1 (by rfl) ⟨410552, by rfl⟩ : syracuseStep 547403 = 821105) B821105
theorem B547415 : Blo 362758 547415 := bstep (se 1 (by rfl) ⟨410561, by rfl⟩ : syracuseStep 547415 = 821123) B821123
theorem B547481 : Blo 362758 547481 := bstep (se 2 (by rfl) ⟨205305, by rfl⟩ : syracuseStep 547481 = 410611) B410611
theorem B547595 : Blo 362758 547595 := bstep (se 1 (by rfl) ⟨410696, by rfl⟩ : syracuseStep 547595 = 821393) B821393
theorem B547607 : Blo 362758 547607 := bstep (se 1 (by rfl) ⟨410705, by rfl⟩ : syracuseStep 547607 = 821411) B821411
theorem B1235735 : Blo 362758 1235735 := bstep (se 1 (by rfl) ⟨926801, by rfl⟩ : syracuseStep 1235735 = 1853603) B1853603
theorem B777035 : Blo 362758 777035 := bstep (se 1 (by rfl) ⟨582776, by rfl⟩ : syracuseStep 777035 = 1165553) B1165553
theorem B547673 : Blo 362758 547673 := bstep (se 2 (by rfl) ⟨205377, by rfl⟩ : syracuseStep 547673 = 410755) B410755
theorem B613271 : Blo 362758 613271 := bstep (se 1 (by rfl) ⟨459953, by rfl⟩ : syracuseStep 613271 = 919907) B919907
theorem B547787 : Blo 362758 547787 := bstep (se 1 (by rfl) ⟨410840, by rfl⟩ : syracuseStep 547787 = 821681) B821681
theorem B547799 : Blo 362758 547799 := bstep (se 1 (by rfl) ⟨410849, by rfl⟩ : syracuseStep 547799 = 821699) B821699
theorem B1104857 : Blo 362758 1104857 := bstep (se 2 (by rfl) ⟨414321, by rfl⟩ : syracuseStep 1104857 = 828643) B828643
theorem B613399 : Blo 362758 613399 := bstep (se 1 (by rfl) ⟨460049, by rfl⟩ : syracuseStep 613399 = 920099) B920099
theorem B547865 : Blo 362758 547865 := bstep (se 2 (by rfl) ⟨205449, by rfl⟩ : syracuseStep 547865 = 410899) B410899
theorem B547979 : Blo 362758 547979 := bstep (se 1 (by rfl) ⟨410984, by rfl⟩ : syracuseStep 547979 = 821969) B821969
theorem B547991 : Blo 362758 547991 := bstep (se 1 (by rfl) ⟨410993, by rfl⟩ : syracuseStep 547991 = 821987) B821987
theorem B9395351 : Blo 362758 9395351 := bstep (se 1 (by rfl) ⟨7046513, by rfl⟩ : syracuseStep 9395351 = 14093027) B14093027
theorem B548057 : Blo 362758 548057 := bstep (se 2 (by rfl) ⟨205521, by rfl⟩ : syracuseStep 548057 = 411043) B411043
theorem B1236275 : Blo 362758 1236275 := bstep (se 1 (by rfl) ⟨927206, by rfl⟩ : syracuseStep 1236275 = 1854413) B1854413
theorem B777547 : Blo 362758 777547 := bstep (se 1 (by rfl) ⟨583160, by rfl⟩ : syracuseStep 777547 = 1166321) B1166321
theorem B1039691 : Blo 362758 1039691 := bstep (se 1 (by rfl) ⟨779768, by rfl⟩ : syracuseStep 1039691 = 1559537) B1559537
theorem B548171 : Blo 362758 548171 := bstep (se 1 (by rfl) ⟨411128, by rfl⟩ : syracuseStep 548171 = 822257) B822257
theorem B548183 : Blo 362758 548183 := bstep (se 1 (by rfl) ⟨411137, by rfl⟩ : syracuseStep 548183 = 822275) B822275
theorem B548249 : Blo 362758 548249 := bstep (se 2 (by rfl) ⟨205593, by rfl⟩ : syracuseStep 548249 = 411187) B411187
theorem B3956147 : Blo 362758 3956147 := bstep (se 1 (by rfl) ⟨2967110, by rfl⟩ : syracuseStep 3956147 = 5934221) B5934221
theorem B548363 : Blo 362758 548363 := bstep (se 1 (by rfl) ⟨411272, by rfl⟩ : syracuseStep 548363 = 822545) B822545
theorem B548375 : Blo 362758 548375 := bstep (se 1 (by rfl) ⟨411281, by rfl⟩ : syracuseStep 548375 = 822563) B822563
theorem B1236545 : Blo 362758 1236545 := bstep (se 2 (by rfl) ⟨463704, by rfl⟩ : syracuseStep 1236545 = 927409) B927409
theorem B548441 : Blo 362758 548441 := bstep (se 2 (by rfl) ⟨205665, by rfl⟩ : syracuseStep 548441 = 411331) B411331
theorem B1171037 : Blo 362758 1171037 := bstep (se 3 (by rfl) ⟨219569, by rfl⟩ : syracuseStep 1171037 = 439139) B439139
theorem B614027 : Blo 362758 614027 := bstep (se 1 (by rfl) ⟨460520, by rfl⟩ : syracuseStep 614027 = 921041) B921041
theorem B548555 : Blo 362758 548555 := bstep (se 1 (by rfl) ⟨411416, by rfl⟩ : syracuseStep 548555 = 822833) B822833
theorem B548567 : Blo 362758 548567 := bstep (se 1 (by rfl) ⟨411425, by rfl⟩ : syracuseStep 548567 = 822851) B822851
theorem B614155 : Blo 362758 614155 := bstep (se 1 (by rfl) ⟨460616, by rfl⟩ : syracuseStep 614155 = 921233) B921233
theorem B548633 : Blo 362758 548633 := bstep (se 2 (by rfl) ⟨205737, by rfl⟩ : syracuseStep 548633 = 411475) B411475
theorem B548747 : Blo 362758 548747 := bstep (se 1 (by rfl) ⟨411560, by rfl⟩ : syracuseStep 548747 = 823121) B823121
theorem B548759 : Blo 362758 548759 := bstep (se 1 (by rfl) ⟨411569, by rfl⟩ : syracuseStep 548759 = 823139) B823139
theorem B614297 : Blo 362758 614297 := bstep (se 2 (by rfl) ⟨230361, by rfl⟩ : syracuseStep 614297 = 460723) B460723
theorem B1564595 : Blo 362758 1564595 := bstep (se 1 (by rfl) ⟨1173446, by rfl⟩ : syracuseStep 1564595 = 2346893) B2346893
theorem B548825 : Blo 362758 548825 := bstep (se 2 (by rfl) ⟨205809, by rfl⟩ : syracuseStep 548825 = 411619) B411619
theorem B614425 : Blo 362758 614425 := bstep (se 2 (by rfl) ⟨230409, by rfl⟩ : syracuseStep 614425 = 460819) B460819
theorem B778265 : Blo 362758 778265 := bstep (se 2 (by rfl) ⟨291849, by rfl⟩ : syracuseStep 778265 = 583699) B583699
theorem B548939 : Blo 362758 548939 := bstep (se 1 (by rfl) ⟨411704, by rfl⟩ : syracuseStep 548939 = 823409) B823409
theorem B548951 : Blo 362758 548951 := bstep (se 1 (by rfl) ⟨411713, by rfl⟩ : syracuseStep 548951 = 823427) B823427
theorem B1237085 : Blo 362758 1237085 := bstep (se 3 (by rfl) ⟨231953, by rfl⟩ : syracuseStep 1237085 = 463907) B463907
theorem B549017 : Blo 362758 549017 := bstep (se 2 (by rfl) ⟨205881, by rfl⟩ : syracuseStep 549017 = 411763) B411763
theorem B909515 : Blo 362758 909515 := bstep (se 1 (by rfl) ⟨682136, by rfl⟩ : syracuseStep 909515 = 1364273) B1364273
theorem B549131 : Blo 362758 549131 := bstep (se 1 (by rfl) ⟨411848, by rfl⟩ : syracuseStep 549131 = 823697) B823697
theorem B93184277 : Blo 362758 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B549143 : Blo 362758 549143 := bstep (se 1 (by rfl) ⟨411857, by rfl⟩ : syracuseStep 549143 = 823715) B823715
theorem B549209 : Blo 362758 549209 := bstep (se 2 (by rfl) ⟨205953, by rfl⟩ : syracuseStep 549209 = 411907) B411907
theorem B778675 : Blo 362758 778675 := bstep (se 1 (by rfl) ⟨584006, by rfl⟩ : syracuseStep 778675 = 1168013) B1168013
theorem B549323 : Blo 362758 549323 := bstep (se 1 (by rfl) ⟨411992, by rfl⟩ : syracuseStep 549323 = 823985) B823985
theorem B549335 : Blo 362758 549335 := bstep (se 1 (by rfl) ⟨412001, by rfl⟩ : syracuseStep 549335 = 824003) B824003
theorem B549401 : Blo 362758 549401 := bstep (se 2 (by rfl) ⟨206025, by rfl⟩ : syracuseStep 549401 = 412051) B412051
theorem B614999 : Blo 362758 614999 := bstep (se 1 (by rfl) ⟨461249, by rfl⟩ : syracuseStep 614999 = 922499) B922499
theorem B549515 : Blo 362758 549515 := bstep (se 1 (by rfl) ⟨412136, by rfl⟩ : syracuseStep 549515 = 824273) B824273
theorem B549527 : Blo 362758 549527 := bstep (se 1 (by rfl) ⟨412145, by rfl⟩ : syracuseStep 549527 = 824291) B824291
theorem B615127 : Blo 362758 615127 := bstep (se 1 (by rfl) ⟨461345, by rfl⟩ : syracuseStep 615127 = 922691) B922691
theorem B549593 : Blo 362758 549593 := bstep (se 2 (by rfl) ⟨206097, by rfl⟩ : syracuseStep 549593 = 412195) B412195
theorem B549707 : Blo 362758 549707 := bstep (se 1 (by rfl) ⟨412280, by rfl⟩ : syracuseStep 549707 = 824561) B824561
theorem B549719 : Blo 362758 549719 := bstep (se 1 (by rfl) ⟨412289, by rfl⟩ : syracuseStep 549719 = 824579) B824579
theorem B549785 : Blo 362758 549785 := bstep (se 2 (by rfl) ⟨206169, by rfl⟩ : syracuseStep 549785 = 412339) B412339
theorem B1041331 : Blo 362758 1041331 := bstep (se 1 (by rfl) ⟨780998, by rfl⟩ : syracuseStep 1041331 = 1561997) B1561997
theorem B22438853 : Blo 362758 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B877529 : Blo 362758 877529 := bstep (se 2 (by rfl) ⟨329073, by rfl⟩ : syracuseStep 877529 = 658147) B658147
theorem B549899 : Blo 362758 549899 := bstep (se 1 (by rfl) ⟨412424, by rfl⟩ : syracuseStep 549899 = 824849) B824849
theorem B549911 : Blo 362758 549911 := bstep (se 1 (by rfl) ⟨412433, by rfl⟩ : syracuseStep 549911 = 824867) B824867
theorem B8479819 : Blo 362758 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B549977 : Blo 362758 549977 := bstep (se 2 (by rfl) ⟨206241, by rfl⟩ : syracuseStep 549977 = 412483) B412483
theorem B517271 : Blo 362758 517271 := bstep (se 1 (by rfl) ⟨387953, by rfl⟩ : syracuseStep 517271 = 775907) B775907
theorem B550091 : Blo 362758 550091 := bstep (se 1 (by rfl) ⟨412568, by rfl⟩ : syracuseStep 550091 = 825137) B825137
theorem B550103 : Blo 362758 550103 := bstep (se 1 (by rfl) ⟨412577, by rfl⟩ : syracuseStep 550103 = 825155) B825155
theorem B615755 : Blo 362758 615755 := bstep (se 1 (by rfl) ⟨461816, by rfl⟩ : syracuseStep 615755 = 923633) B923633
theorem B517465 : Blo 362758 517465 := bstep (se 2 (by rfl) ⟨194049, by rfl⟩ : syracuseStep 517465 = 388099) B388099
theorem B2778461 : Blo 362758 2778461 := bstep (se 3 (by rfl) ⟨520961, by rfl⟩ : syracuseStep 2778461 = 1041923) B1041923
theorem B615883 : Blo 362758 615883 := bstep (se 1 (by rfl) ⟨461912, by rfl⟩ : syracuseStep 615883 = 923825) B923825
theorem B1009217 : Blo 362758 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B1795649 : Blo 362758 1795649 := bstep (se 2 (by rfl) ⟨673368, by rfl⟩ : syracuseStep 1795649 = 1346737) B1346737
theorem B779863 : Blo 362758 779863 := bstep (se 1 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 779863 = 1169795) B1169795
theorem B616025 : Blo 362758 616025 := bstep (se 2 (by rfl) ⟨231009, by rfl⟩ : syracuseStep 616025 = 462019) B462019
theorem B779905 : Blo 362758 779905 := bstep (se 2 (by rfl) ⟨292464, by rfl⟩ : syracuseStep 779905 = 584929) B584929
theorem B1664729 : Blo 362758 1664729 := bstep (se 2 (by rfl) ⟨624273, by rfl⟩ : syracuseStep 1664729 = 1248547) B1248547
theorem B616153 : Blo 362758 616153 := bstep (se 2 (by rfl) ⟨231057, by rfl⟩ : syracuseStep 616153 = 462115) B462115
theorem B1042379 : Blo 362758 1042379 := bstep (se 1 (by rfl) ⟨781784, by rfl⟩ : syracuseStep 1042379 = 1563569) B1563569
theorem B7596101 : Blo 362758 7596101 := bstep (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) B1424269
theorem B616727 : Blo 362758 616727 := bstep (se 1 (by rfl) ⟨462545, by rfl⟩ : syracuseStep 616727 = 925091) B925091
theorem B616855 : Blo 362758 616855 := bstep (se 1 (by rfl) ⟨462641, by rfl⟩ : syracuseStep 616855 = 925283) B925283
theorem B387595 : Blo 362758 387595 := bstep (se 1 (by rfl) ⟨290696, by rfl⟩ : syracuseStep 387595 = 581393) B581393
theorem B518923 : Blo 362758 518923 := bstep (se 1 (by rfl) ⟨389192, by rfl⟩ : syracuseStep 518923 = 778385) B778385
theorem B617483 : Blo 362758 617483 := bstep (se 1 (by rfl) ⟨463112, by rfl⟩ : syracuseStep 617483 = 926225) B926225
theorem B748595 : Blo 362758 748595 := bstep (se 1 (by rfl) ⟨561446, by rfl⟩ : syracuseStep 748595 = 1122893) B1122893
theorem B617611 : Blo 362758 617611 := bstep (se 1 (by rfl) ⟨463208, by rfl⟩ : syracuseStep 617611 = 926417) B926417
theorem B781579 : Blo 362758 781579 := bstep (se 1 (by rfl) ⟨586184, by rfl⟩ : syracuseStep 781579 = 1172369) B1172369
theorem B617753 : Blo 362758 617753 := bstep (se 2 (by rfl) ⟨231657, by rfl⟩ : syracuseStep 617753 = 463315) B463315
theorem B617881 : Blo 362758 617881 := bstep (se 2 (by rfl) ⟨231705, by rfl⟩ : syracuseStep 617881 = 463411) B463411
theorem B1044019 : Blo 362758 1044019 := bstep (se 1 (by rfl) ⟨783014, by rfl⟩ : syracuseStep 1044019 = 1566029) B1566029
theorem B781913 : Blo 362758 781913 := bstep (se 2 (by rfl) ⟨293217, by rfl⟩ : syracuseStep 781913 = 586435) B586435
theorem B6942449 : Blo 362758 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B1044247 : Blo 362758 1044247 := bstep (se 1 (by rfl) ⟨783185, by rfl⟩ : syracuseStep 1044247 = 1566371) B1566371
theorem B388919 : Blo 362758 388919 := bstep (se 1 (by rfl) ⟨291689, by rfl⟩ : syracuseStep 388919 = 583379) B583379
theorem B389047 : Blo 362758 389047 := bstep (se 1 (by rfl) ⟨291785, by rfl⟩ : syracuseStep 389047 = 583571) B583571
theorem B618455 : Blo 362758 618455 := bstep (se 1 (by rfl) ⟨463841, by rfl⟩ : syracuseStep 618455 = 927683) B927683
theorem B618583 : Blo 362758 618583 := bstep (se 1 (by rfl) ⟨463937, by rfl⟩ : syracuseStep 618583 = 927875) B927875
theorem B8876213 : Blo 362758 8876213 := bstep (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) B832145
theorem B389611 : Blo 362758 389611 := bstep (se 1 (by rfl) ⟨292208, by rfl⟩ : syracuseStep 389611 = 584417) B584417
theorem B389867 : Blo 362758 389867 := bstep (se 1 (by rfl) ⟨292400, by rfl⟩ : syracuseStep 389867 = 584801) B584801
theorem B783361 : Blo 362758 783361 := bstep (se 2 (by rfl) ⟨293760, by rfl⟩ : syracuseStep 783361 = 587521) B587521
theorem B816281 : Blo 362758 816281 := bstep (se 2 (by rfl) ⟨306105, by rfl⟩ : syracuseStep 816281 = 612211) B612211
theorem B816371 : Blo 362758 816371 := bstep (se 1 (by rfl) ⟨612278, by rfl⟩ : syracuseStep 816371 = 1224557) B1224557
theorem B816407 : Blo 362758 816407 := bstep (se 1 (by rfl) ⟨612305, by rfl⟩ : syracuseStep 816407 = 1224611) B1224611
theorem B2618659 : Blo 362758 2618659 := bstep (se 1 (by rfl) ⟨1963994, by rfl⟩ : syracuseStep 2618659 = 3927989) B3927989
theorem B587159 : Blo 362758 587159 := bstep (se 1 (by rfl) ⟨440369, by rfl⟩ : syracuseStep 587159 = 880739) B880739
theorem B816587 : Blo 362758 816587 := bstep (se 1 (by rfl) ⟨612440, by rfl⟩ : syracuseStep 816587 = 1224881) B1224881
theorem B816641 : Blo 362758 816641 := bstep (se 2 (by rfl) ⟨306240, by rfl⟩ : syracuseStep 816641 = 612481) B612481
theorem B587287 : Blo 362758 587287 := bstep (se 1 (by rfl) ⟨440465, by rfl⟩ : syracuseStep 587287 = 880931) B880931
theorem B816857 : Blo 362758 816857 := bstep (se 2 (by rfl) ⟨306321, by rfl⟩ : syracuseStep 816857 = 612643) B612643
theorem B554777 : Blo 362758 554777 := bstep (se 2 (by rfl) ⟨208041, by rfl⟩ : syracuseStep 554777 = 416083) B416083
theorem B816947 : Blo 362758 816947 := bstep (se 1 (by rfl) ⟨612710, by rfl⟩ : syracuseStep 816947 = 1225421) B1225421
theorem B816983 : Blo 362758 816983 := bstep (se 1 (by rfl) ⟨612737, by rfl⟩ : syracuseStep 816983 = 1225475) B1225475
theorem B4650929 : Blo 362758 4650929 := bstep (se 2 (by rfl) ⟨1744098, by rfl⟩ : syracuseStep 4650929 = 3488197) B3488197
theorem B7010225 : Blo 362758 7010225 := bstep (se 2 (by rfl) ⟨2628834, by rfl⟩ : syracuseStep 7010225 = 5257669) B5257669
theorem B817163 : Blo 362758 817163 := bstep (se 1 (by rfl) ⟨612872, by rfl⟩ : syracuseStep 817163 = 1225745) B1225745
theorem B555031 : Blo 362758 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B817217 : Blo 362758 817217 := bstep (se 2 (by rfl) ⟨306456, by rfl⟩ : syracuseStep 817217 = 612913) B612913
theorem B817433 : Blo 362758 817433 := bstep (se 2 (by rfl) ⟨306537, by rfl⟩ : syracuseStep 817433 = 613075) B613075
theorem B11794733 : Blo 362758 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B817523 : Blo 362758 817523 := bstep (se 1 (by rfl) ⟨613142, by rfl⟩ : syracuseStep 817523 = 1226285) B1226285
theorem B817559 : Blo 362758 817559 := bstep (se 1 (by rfl) ⟨613169, by rfl⟩ : syracuseStep 817559 = 1226339) B1226339
theorem B1407449 : Blo 362758 1407449 := bstep (se 2 (by rfl) ⟨527793, by rfl⟩ : syracuseStep 1407449 = 1055587) B1055587
theorem B7043597 : Blo 362758 7043597 := bstep (se 3 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 7043597 = 2641349) B2641349
theorem B1604141 : Blo 362758 1604141 := bstep (se 3 (by rfl) ⟨300776, by rfl⟩ : syracuseStep 1604141 = 601553) B601553
theorem B817739 : Blo 362758 817739 := bstep (se 1 (by rfl) ⟨613304, by rfl⟩ : syracuseStep 817739 = 1226609) B1226609
theorem B817793 : Blo 362758 817793 := bstep (se 2 (by rfl) ⟨306672, by rfl⟩ : syracuseStep 817793 = 613345) B613345
theorem B5569175 : Blo 362758 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B1178315 : Blo 362758 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B818009 : Blo 362758 818009 := bstep (se 2 (by rfl) ⟨306753, by rfl⟩ : syracuseStep 818009 = 613507) B613507
theorem B818099 : Blo 362758 818099 := bstep (se 1 (by rfl) ⟨613574, by rfl⟩ : syracuseStep 818099 = 1227149) B1227149
theorem B818135 : Blo 362758 818135 := bstep (se 1 (by rfl) ⟨613601, by rfl⟩ : syracuseStep 818135 = 1227203) B1227203
theorem B490583 : Blo 362758 490583 := bstep (se 1 (by rfl) ⟨367937, by rfl⟩ : syracuseStep 490583 = 735875) B735875
theorem B818315 : Blo 362758 818315 := bstep (se 1 (by rfl) ⟨613736, by rfl⟩ : syracuseStep 818315 = 1227473) B1227473
theorem B818369 : Blo 362758 818369 := bstep (se 2 (by rfl) ⟨306888, by rfl⟩ : syracuseStep 818369 = 613777) B613777
theorem B3112343 : Blo 362758 3112343 := bstep (se 1 (by rfl) ⟨2334257, by rfl⟩ : syracuseStep 3112343 = 4668515) B4668515
theorem B654745 : Blo 362758 654745 := bstep (se 2 (by rfl) ⟨245529, by rfl⟩ : syracuseStep 654745 = 491059) B491059
theorem B818585 : Blo 362758 818585 := bstep (se 2 (by rfl) ⟨306969, by rfl⟩ : syracuseStep 818585 = 613939) B613939
theorem B818675 : Blo 362758 818675 := bstep (se 1 (by rfl) ⟨614006, by rfl⟩ : syracuseStep 818675 = 1228013) B1228013
theorem B818711 : Blo 362758 818711 := bstep (se 1 (by rfl) ⟨614033, by rfl⟩ : syracuseStep 818711 = 1228067) B1228067
theorem B818891 : Blo 362758 818891 := bstep (se 1 (by rfl) ⟨614168, by rfl⟩ : syracuseStep 818891 = 1228337) B1228337
theorem B818945 : Blo 362758 818945 := bstep (se 2 (by rfl) ⟨307104, by rfl⟩ : syracuseStep 818945 = 614209) B614209
theorem B7470913 : Blo 362758 7470913 := bstep (se 2 (by rfl) ⟨2801592, by rfl⟩ : syracuseStep 7470913 = 5603185) B5603185
theorem B1965917 : Blo 362758 1965917 := bstep (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) B737219
theorem B819161 : Blo 362758 819161 := bstep (se 2 (by rfl) ⟨307185, by rfl⟩ : syracuseStep 819161 = 614371) B614371
theorem B1015769 : Blo 362758 1015769 := bstep (se 2 (by rfl) ⟨380913, by rfl⟩ : syracuseStep 1015769 = 761827) B761827
theorem B819215 : Blo 362758 819215 := bstep (se 1 (by rfl) ⟨614411, by rfl⟩ : syracuseStep 819215 = 1228823) B1228823
theorem B983069 : Blo 362758 983069 := bstep (se 3 (by rfl) ⟨184325, by rfl⟩ : syracuseStep 983069 = 368651) B368651
theorem B819233 : Blo 362758 819233 := bstep (se 2 (by rfl) ⟨307212, by rfl⟩ : syracuseStep 819233 = 614425) B614425
theorem B1867819 : Blo 362758 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B819575 : Blo 362758 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B491977 : Blo 362758 491977 := bstep (se 2 (by rfl) ⟨184491, by rfl⟩ : syracuseStep 491977 = 368983) B368983
theorem B2425373 : Blo 362758 2425373 := bstep (se 3 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 2425373 = 909515) B909515
theorem B819755 : Blo 362758 819755 := bstep (se 1 (by rfl) ⟨614816, by rfl⟩ : syracuseStep 819755 = 1229633) B1229633
theorem B492151 : Blo 362758 492151 := bstep (se 1 (by rfl) ⟨369113, by rfl⟩ : syracuseStep 492151 = 738227) B738227
theorem B2622145 : Blo 362758 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B918287 : Blo 362758 918287 := bstep (se 1 (by rfl) ⟨688715, by rfl⟩ : syracuseStep 918287 = 1377431) B1377431
theorem B820115 : Blo 362758 820115 := bstep (se 1 (by rfl) ⟨615086, by rfl⟩ : syracuseStep 820115 = 1230173) B1230173
theorem B820169 : Blo 362758 820169 := bstep (se 2 (by rfl) ⟨307563, by rfl⟩ : syracuseStep 820169 = 615127) B615127
theorem B623561 : Blo 362758 623561 := bstep (se 2 (by rfl) ⟨233835, by rfl⟩ : syracuseStep 623561 = 467671) B467671
theorem B656417 : Blo 362758 656417 := bstep (se 2 (by rfl) ⟨246156, by rfl⟩ : syracuseStep 656417 = 492313) B492313
theorem B787499 : Blo 362758 787499 := bstep (se 1 (by rfl) ⟨590624, by rfl⟩ : syracuseStep 787499 = 1181249) B1181249
theorem B460075 : Blo 362758 460075 := bstep (se 1 (by rfl) ⟨345056, by rfl⟩ : syracuseStep 460075 = 690113) B690113
theorem B689467 : Blo 362758 689467 := bstep (se 1 (by rfl) ⟨517100, by rfl⟩ : syracuseStep 689467 = 1034201) B1034201
theorem B4982147 : Blo 362758 4982147 := bstep (se 1 (by rfl) ⟨3736610, by rfl⟩ : syracuseStep 4982147 = 7473221) B7473221
theorem B689543 : Blo 362758 689543 := bstep (se 1 (by rfl) ⟨517157, by rfl⟩ : syracuseStep 689543 = 1034315) B1034315
theorem B1672595 : Blo 362758 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B11306425 : Blo 362758 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B918985 : Blo 362758 918985 := bstep (se 2 (by rfl) ⟨344619, by rfl⟩ : syracuseStep 918985 = 689239) B689239
theorem B36537925 : Blo 362758 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B919127 : Blo 362758 919127 := bstep (se 1 (by rfl) ⟨689345, by rfl⟩ : syracuseStep 919127 = 1378691) B1378691
theorem B788087 : Blo 362758 788087 := bstep (se 1 (by rfl) ⟨591065, by rfl⟩ : syracuseStep 788087 = 1182131) B1182131
theorem B820871 : Blo 362758 820871 := bstep (se 1 (by rfl) ⟨615653, by rfl⟩ : syracuseStep 820871 = 1231307) B1231307
theorem B2328335 : Blo 362758 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B689953 : Blo 362758 689953 := bstep (se 2 (by rfl) ⟨258732, by rfl⟩ : syracuseStep 689953 = 517465) B517465
theorem B821051 : Blo 362758 821051 := bstep (se 1 (by rfl) ⟨615788, by rfl⟩ : syracuseStep 821051 = 1231577) B1231577
theorem B821177 : Blo 362758 821177 := bstep (se 2 (by rfl) ⟨307941, by rfl⟩ : syracuseStep 821177 = 615883) B615883
theorem B657353 : Blo 362758 657353 := bstep (se 2 (by rfl) ⟨246507, by rfl⟩ : syracuseStep 657353 = 493015) B493015
theorem B1837079 : Blo 362758 1837079 := bstep (se 1 (by rfl) ⟨1377809, by rfl⟩ : syracuseStep 1837079 = 2755619) B2755619
theorem B690295 : Blo 362758 690295 := bstep (se 1 (by rfl) ⟨517721, by rfl⟩ : syracuseStep 690295 = 1035443) B1035443
theorem B1771721 : Blo 362758 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B461047 : Blo 362758 461047 := bstep (se 1 (by rfl) ⟨345785, by rfl⟩ : syracuseStep 461047 = 691571) B691571
theorem B362759 : Blo 362758 362759 := bstep (se 1 (by rfl) ⟨272069, by rfl⟩ : syracuseStep 362759 = 544139) B544139
theorem B362767 : Blo 362758 362767 := bstep (se 1 (by rfl) ⟨272075, by rfl⟩ : syracuseStep 362767 = 544151) B544151
theorem B821519 : Blo 362758 821519 := bstep (se 1 (by rfl) ⟨616139, by rfl⟩ : syracuseStep 821519 = 1232279) B1232279
theorem B821537 : Blo 362758 821537 := bstep (se 2 (by rfl) ⟨308076, by rfl⟩ : syracuseStep 821537 = 616153) B616153
theorem B362811 : Blo 362758 362811 := bstep (se 1 (by rfl) ⟨272108, by rfl⟩ : syracuseStep 362811 = 544217) B544217
theorem B362887 : Blo 362758 362887 := bstep (se 1 (by rfl) ⟨272165, by rfl⟩ : syracuseStep 362887 = 544331) B544331
theorem B362895 : Blo 362758 362895 := bstep (se 1 (by rfl) ⟨272171, by rfl⟩ : syracuseStep 362895 = 544343) B544343
theorem B362939 : Blo 362758 362939 := bstep (se 1 (by rfl) ⟨272204, by rfl⟩ : syracuseStep 362939 = 544409) B544409
theorem B2066897 : Blo 362758 2066897 := bstep (se 2 (by rfl) ⟨775086, by rfl⟩ : syracuseStep 2066897 = 1550173) B1550173
theorem B363015 : Blo 362758 363015 := bstep (se 1 (by rfl) ⟨272261, by rfl⟩ : syracuseStep 363015 = 544523) B544523
theorem B363023 : Blo 362758 363023 := bstep (se 1 (by rfl) ⟨272267, by rfl⟩ : syracuseStep 363023 = 544535) B544535
theorem B363067 : Blo 362758 363067 := bstep (se 1 (by rfl) ⟨272300, by rfl⟩ : syracuseStep 363067 = 544601) B544601
theorem B461371 : Blo 362758 461371 := bstep (se 1 (by rfl) ⟨346028, by rfl⟩ : syracuseStep 461371 = 692057) B692057
theorem B1378903 : Blo 362758 1378903 := bstep (se 1 (by rfl) ⟨1034177, by rfl⟩ : syracuseStep 1378903 = 2068355) B2068355
theorem B821879 : Blo 362758 821879 := bstep (se 1 (by rfl) ⟨616409, by rfl⟩ : syracuseStep 821879 = 1232819) B1232819
theorem B363143 : Blo 362758 363143 := bstep (se 1 (by rfl) ⟨272357, by rfl⟩ : syracuseStep 363143 = 544715) B544715
theorem B363151 : Blo 362758 363151 := bstep (se 1 (by rfl) ⟨272363, by rfl⟩ : syracuseStep 363151 = 544727) B544727
theorem B363195 : Blo 362758 363195 := bstep (se 1 (by rfl) ⟨272396, by rfl⟩ : syracuseStep 363195 = 544793) B544793
theorem B363271 : Blo 362758 363271 := bstep (se 1 (by rfl) ⟨272453, by rfl⟩ : syracuseStep 363271 = 544907) B544907
theorem B363279 : Blo 362758 363279 := bstep (se 1 (by rfl) ⟨272459, by rfl⟩ : syracuseStep 363279 = 544919) B544919
theorem B658219 : Blo 362758 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B822059 : Blo 362758 822059 := bstep (se 1 (by rfl) ⟨616544, by rfl⟩ : syracuseStep 822059 = 1233089) B1233089
theorem B363323 : Blo 362758 363323 := bstep (se 1 (by rfl) ⟨272492, by rfl⟩ : syracuseStep 363323 = 544985) B544985
theorem B1379207 : Blo 362758 1379207 := bstep (se 1 (by rfl) ⟨1034405, by rfl⟩ : syracuseStep 1379207 = 2068811) B2068811
theorem B363399 : Blo 362758 363399 := bstep (se 1 (by rfl) ⟨272549, by rfl⟩ : syracuseStep 363399 = 545099) B545099
theorem B527239 : Blo 362758 527239 := bstep (se 1 (by rfl) ⟨395429, by rfl⟩ : syracuseStep 527239 = 790859) B790859
theorem B363407 : Blo 362758 363407 := bstep (se 1 (by rfl) ⟨272555, by rfl⟩ : syracuseStep 363407 = 545111) B545111
theorem B2067353 : Blo 362758 2067353 := bstep (se 2 (by rfl) ⟨775257, by rfl⟩ : syracuseStep 2067353 = 1550515) B1550515
theorem B363451 : Blo 362758 363451 := bstep (se 1 (by rfl) ⟨272588, by rfl⟩ : syracuseStep 363451 = 545177) B545177
theorem B363527 : Blo 362758 363527 := bstep (se 1 (by rfl) ⟨272645, by rfl⟩ : syracuseStep 363527 = 545291) B545291
theorem B363535 : Blo 362758 363535 := bstep (se 1 (by rfl) ⟨272651, by rfl⟩ : syracuseStep 363535 = 545303) B545303
theorem B363579 : Blo 362758 363579 := bstep (se 1 (by rfl) ⟨272684, by rfl⟩ : syracuseStep 363579 = 545369) B545369
theorem B1379389 : Blo 362758 1379389 := bstep (se 3 (by rfl) ⟨258635, by rfl⟩ : syracuseStep 1379389 = 517271) B517271
theorem B1805431 : Blo 362758 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B363655 : Blo 362758 363655 := bstep (se 1 (by rfl) ⟨272741, by rfl⟩ : syracuseStep 363655 = 545483) B545483
theorem B363663 : Blo 362758 363663 := bstep (se 1 (by rfl) ⟨272747, by rfl⟩ : syracuseStep 363663 = 545495) B545495
theorem B822419 : Blo 362758 822419 := bstep (se 1 (by rfl) ⟨616814, by rfl⟩ : syracuseStep 822419 = 1233629) B1233629
theorem B363707 : Blo 362758 363707 := bstep (se 1 (by rfl) ⟨272780, by rfl⟩ : syracuseStep 363707 = 545561) B545561
theorem B822473 : Blo 362758 822473 := bstep (se 2 (by rfl) ⟨308427, by rfl⟩ : syracuseStep 822473 = 616855) B616855
theorem B4656365 : Blo 362758 4656365 := bstep (se 3 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 4656365 = 1746137) B1746137
theorem B363783 : Blo 362758 363783 := bstep (se 1 (by rfl) ⟨272837, by rfl⟩ : syracuseStep 363783 = 545675) B545675
theorem B363791 : Blo 362758 363791 := bstep (se 1 (by rfl) ⟨272843, by rfl⟩ : syracuseStep 363791 = 545687) B545687
theorem B363835 : Blo 362758 363835 := bstep (se 1 (by rfl) ⟨272876, by rfl⟩ : syracuseStep 363835 = 545753) B545753
theorem B363911 : Blo 362758 363911 := bstep (se 1 (by rfl) ⟨272933, by rfl⟩ : syracuseStep 363911 = 545867) B545867
theorem B363919 : Blo 362758 363919 := bstep (se 1 (by rfl) ⟨272939, by rfl⟩ : syracuseStep 363919 = 545879) B545879
theorem B363963 : Blo 362758 363963 := bstep (se 1 (by rfl) ⟨272972, by rfl⟩ : syracuseStep 363963 = 545945) B545945
theorem B3509725 : Blo 362758 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B364039 : Blo 362758 364039 := bstep (se 1 (by rfl) ⟨273029, by rfl⟩ : syracuseStep 364039 = 546059) B546059
theorem B462343 : Blo 362758 462343 := bstep (se 1 (by rfl) ⟨346757, by rfl⟩ : syracuseStep 462343 = 693515) B693515
theorem B364047 : Blo 362758 364047 := bstep (se 1 (by rfl) ⟨273035, by rfl⟩ : syracuseStep 364047 = 546071) B546071
theorem B364091 : Blo 362758 364091 := bstep (se 1 (by rfl) ⟨273068, by rfl⟩ : syracuseStep 364091 = 546137) B546137
theorem B921203 : Blo 362758 921203 := bstep (se 1 (by rfl) ⟨690902, by rfl⟩ : syracuseStep 921203 = 1381805) B1381805
theorem B364167 : Blo 362758 364167 := bstep (se 1 (by rfl) ⟨273125, by rfl⟩ : syracuseStep 364167 = 546251) B546251
theorem B364175 : Blo 362758 364175 := bstep (se 1 (by rfl) ⟨273131, by rfl⟩ : syracuseStep 364175 = 546263) B546263
theorem B691897 : Blo 362758 691897 := bstep (se 2 (by rfl) ⟨259461, by rfl⟩ : syracuseStep 691897 = 518923) B518923
theorem B364219 : Blo 362758 364219 := bstep (se 1 (by rfl) ⟨273164, by rfl⟩ : syracuseStep 364219 = 546329) B546329
theorem B364295 : Blo 362758 364295 := bstep (se 1 (by rfl) ⟨273221, by rfl⟩ : syracuseStep 364295 = 546443) B546443
theorem B364303 : Blo 362758 364303 := bstep (se 1 (by rfl) ⟨273227, by rfl⟩ : syracuseStep 364303 = 546455) B546455
theorem B1314593 : Blo 362758 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B364347 : Blo 362758 364347 := bstep (se 1 (by rfl) ⟨273260, by rfl⟩ : syracuseStep 364347 = 546521) B546521
theorem B364423 : Blo 362758 364423 := bstep (se 1 (by rfl) ⟨273317, by rfl⟩ : syracuseStep 364423 = 546635) B546635
theorem B823175 : Blo 362758 823175 := bstep (se 1 (by rfl) ⟨617381, by rfl⟩ : syracuseStep 823175 = 1234763) B1234763
theorem B364431 : Blo 362758 364431 := bstep (se 1 (by rfl) ⟨273323, by rfl⟩ : syracuseStep 364431 = 546647) B546647
theorem B462763 : Blo 362758 462763 := bstep (se 1 (by rfl) ⟨347072, by rfl⟩ : syracuseStep 462763 = 694145) B694145
theorem B364475 : Blo 362758 364475 := bstep (se 1 (by rfl) ⟨273356, by rfl⟩ : syracuseStep 364475 = 546713) B546713
theorem B364551 : Blo 362758 364551 := bstep (se 1 (by rfl) ⟨273413, by rfl⟩ : syracuseStep 364551 = 546827) B546827
theorem B364559 : Blo 362758 364559 := bstep (se 1 (by rfl) ⟨273419, by rfl⟩ : syracuseStep 364559 = 546839) B546839
theorem B692239 : Blo 362758 692239 := bstep (se 1 (by rfl) ⟨519179, by rfl⟩ : syracuseStep 692239 = 1038359) B1038359
theorem B364603 : Blo 362758 364603 := bstep (se 1 (by rfl) ⟨273452, by rfl⟩ : syracuseStep 364603 = 546905) B546905
theorem B823355 : Blo 362758 823355 := bstep (se 1 (by rfl) ⟨617516, by rfl⟩ : syracuseStep 823355 = 1235033) B1235033
theorem B4198517 : Blo 362758 4198517 := bstep (se 5 (by rfl) ⟨196805, by rfl⟩ : syracuseStep 4198517 = 393611) B393611
theorem B921719 : Blo 362758 921719 := bstep (se 1 (by rfl) ⟨691289, by rfl⟩ : syracuseStep 921719 = 1382579) B1382579
theorem B364679 : Blo 362758 364679 := bstep (se 1 (by rfl) ⟨273509, by rfl⟩ : syracuseStep 364679 = 547019) B547019
theorem B364687 : Blo 362758 364687 := bstep (se 1 (by rfl) ⟨273515, by rfl⟩ : syracuseStep 364687 = 547031) B547031
theorem B462991 : Blo 362758 462991 := bstep (se 1 (by rfl) ⟨347243, by rfl⟩ : syracuseStep 462991 = 694487) B694487
theorem B659603 : Blo 362758 659603 := bstep (se 1 (by rfl) ⟨494702, by rfl⟩ : syracuseStep 659603 = 989405) B989405
theorem B2691245 : Blo 362758 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B4788397 : Blo 362758 4788397 := bstep (se 3 (by rfl) ⟨897824, by rfl⟩ : syracuseStep 4788397 = 1795649) B1795649
theorem B823481 : Blo 362758 823481 := bstep (se 2 (by rfl) ⟨308805, by rfl⟩ : syracuseStep 823481 = 617611) B617611
theorem B364731 : Blo 362758 364731 := bstep (se 1 (by rfl) ⟨273548, by rfl⟩ : syracuseStep 364731 = 547097) B547097
theorem B364807 : Blo 362758 364807 := bstep (se 1 (by rfl) ⟨273605, by rfl⟩ : syracuseStep 364807 = 547211) B547211
theorem B364815 : Blo 362758 364815 := bstep (se 1 (by rfl) ⟨273611, by rfl⟩ : syracuseStep 364815 = 547223) B547223
theorem B364859 : Blo 362758 364859 := bstep (se 1 (by rfl) ⟨273644, by rfl⟩ : syracuseStep 364859 = 547289) B547289
theorem B5017949 : Blo 362758 5017949 := bstep (se 3 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 5017949 = 1881731) B1881731
theorem B364935 : Blo 362758 364935 := bstep (se 1 (by rfl) ⟨273701, by rfl⟩ : syracuseStep 364935 = 547403) B547403
theorem B364943 : Blo 362758 364943 := bstep (se 1 (by rfl) ⟨273707, by rfl⟩ : syracuseStep 364943 = 547415) B547415
theorem B987545 : Blo 362758 987545 := bstep (se 2 (by rfl) ⟨370329, by rfl⟩ : syracuseStep 987545 = 740659) B740659
theorem B364987 : Blo 362758 364987 := bstep (se 1 (by rfl) ⟨273740, by rfl⟩ : syracuseStep 364987 = 547481) B547481
theorem B365063 : Blo 362758 365063 := bstep (se 1 (by rfl) ⟨273797, by rfl⟩ : syracuseStep 365063 = 547595) B547595
theorem B365071 : Blo 362758 365071 := bstep (se 1 (by rfl) ⟨273803, by rfl⟩ : syracuseStep 365071 = 547607) B547607
theorem B823823 : Blo 362758 823823 := bstep (se 1 (by rfl) ⟨617867, by rfl⟩ : syracuseStep 823823 = 1235735) B1235735
theorem B823841 : Blo 362758 823841 := bstep (se 2 (by rfl) ⟨308940, by rfl⟩ : syracuseStep 823841 = 617881) B617881
theorem B2036267 : Blo 362758 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B365115 : Blo 362758 365115 := bstep (se 1 (by rfl) ⟨273836, by rfl⟩ : syracuseStep 365115 = 547673) B547673
theorem B365191 : Blo 362758 365191 := bstep (se 1 (by rfl) ⟨273893, by rfl⟩ : syracuseStep 365191 = 547787) B547787
theorem B365199 : Blo 362758 365199 := bstep (se 1 (by rfl) ⟨273899, by rfl⟩ : syracuseStep 365199 = 547799) B547799
theorem B365243 : Blo 362758 365243 := bstep (se 1 (by rfl) ⟨273932, by rfl⟩ : syracuseStep 365243 = 547865) B547865
theorem B1381121 : Blo 362758 1381121 := bstep (se 2 (by rfl) ⟨517920, by rfl⟩ : syracuseStep 1381121 = 1035841) B1035841
theorem B365319 : Blo 362758 365319 := bstep (se 1 (by rfl) ⟨273989, by rfl⟩ : syracuseStep 365319 = 547979) B547979
theorem B365327 : Blo 362758 365327 := bstep (se 1 (by rfl) ⟨273995, by rfl⟩ : syracuseStep 365327 = 547991) B547991
theorem B6263567 : Blo 362758 6263567 := bstep (se 1 (by rfl) ⟨4697675, by rfl⟩ : syracuseStep 6263567 = 9395351) B9395351
theorem B365371 : Blo 362758 365371 := bstep (se 1 (by rfl) ⟨274028, by rfl⟩ : syracuseStep 365371 = 548057) B548057
theorem B824183 : Blo 362758 824183 := bstep (se 1 (by rfl) ⟨618137, by rfl⟩ : syracuseStep 824183 = 1236275) B1236275
theorem B463735 : Blo 362758 463735 := bstep (se 1 (by rfl) ⟨347801, by rfl⟩ : syracuseStep 463735 = 695603) B695603
theorem B693127 : Blo 362758 693127 := bstep (se 1 (by rfl) ⟨519845, by rfl⟩ : syracuseStep 693127 = 1039691) B1039691
theorem B365447 : Blo 362758 365447 := bstep (se 1 (by rfl) ⟨274085, by rfl⟩ : syracuseStep 365447 = 548171) B548171
theorem B365455 : Blo 362758 365455 := bstep (se 1 (by rfl) ⟨274091, by rfl⟩ : syracuseStep 365455 = 548183) B548183
theorem B365499 : Blo 362758 365499 := bstep (se 1 (by rfl) ⟨274124, by rfl⟩ : syracuseStep 365499 = 548249) B548249
theorem B365575 : Blo 362758 365575 := bstep (se 1 (by rfl) ⟨274181, by rfl⟩ : syracuseStep 365575 = 548363) B548363
theorem B365583 : Blo 362758 365583 := bstep (se 1 (by rfl) ⟨274187, by rfl⟩ : syracuseStep 365583 = 548375) B548375
theorem B1840157 : Blo 362758 1840157 := bstep (se 3 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 1840157 = 690059) B690059
theorem B1053739 : Blo 362758 1053739 := bstep (se 1 (by rfl) ⟨790304, by rfl⟩ : syracuseStep 1053739 = 1580609) B1580609
theorem B824363 : Blo 362758 824363 := bstep (se 1 (by rfl) ⟨618272, by rfl⟩ : syracuseStep 824363 = 1236545) B1236545
theorem B365627 : Blo 362758 365627 := bstep (se 1 (by rfl) ⟨274220, by rfl⟩ : syracuseStep 365627 = 548441) B548441
theorem B922711 : Blo 362758 922711 := bstep (se 1 (by rfl) ⟨692033, by rfl⟩ : syracuseStep 922711 = 1384067) B1384067
theorem B365703 : Blo 362758 365703 := bstep (se 1 (by rfl) ⟨274277, by rfl⟩ : syracuseStep 365703 = 548555) B548555
theorem B365711 : Blo 362758 365711 := bstep (se 1 (by rfl) ⟨274283, by rfl⟩ : syracuseStep 365711 = 548567) B548567
theorem B2331821 : Blo 362758 2331821 := bstep (se 3 (by rfl) ⟨437216, by rfl⟩ : syracuseStep 2331821 = 874433) B874433
theorem B365755 : Blo 362758 365755 := bstep (se 1 (by rfl) ⟨274316, by rfl⟩ : syracuseStep 365755 = 548633) B548633
theorem B464059 : Blo 362758 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B365831 : Blo 362758 365831 := bstep (se 1 (by rfl) ⟨274373, by rfl⟩ : syracuseStep 365831 = 548747) B548747
theorem B365839 : Blo 362758 365839 := bstep (se 1 (by rfl) ⟨274379, by rfl⟩ : syracuseStep 365839 = 548759) B548759
theorem B365883 : Blo 362758 365883 := bstep (se 1 (by rfl) ⟨274412, by rfl⟩ : syracuseStep 365883 = 548825) B548825
theorem B923015 : Blo 362758 923015 := bstep (se 1 (by rfl) ⟨692261, by rfl⟩ : syracuseStep 923015 = 1384523) B1384523
theorem B365959 : Blo 362758 365959 := bstep (se 1 (by rfl) ⟨274469, by rfl⟩ : syracuseStep 365959 = 548939) B548939
theorem B365967 : Blo 362758 365967 := bstep (se 1 (by rfl) ⟨274475, by rfl⟩ : syracuseStep 365967 = 548951) B548951
theorem B824723 : Blo 362758 824723 := bstep (se 1 (by rfl) ⟨618542, by rfl⟩ : syracuseStep 824723 = 1237085) B1237085
theorem B366011 : Blo 362758 366011 := bstep (se 1 (by rfl) ⟨274508, by rfl⟩ : syracuseStep 366011 = 549017) B549017
theorem B824777 : Blo 362758 824777 := bstep (se 2 (by rfl) ⟨309291, by rfl⟩ : syracuseStep 824777 = 618583) B618583
theorem B1840643 : Blo 362758 1840643 := bstep (se 1 (by rfl) ⟨1380482, by rfl⟩ : syracuseStep 1840643 = 2760965) B2760965
theorem B366087 : Blo 362758 366087 := bstep (se 1 (by rfl) ⟨274565, by rfl⟩ : syracuseStep 366087 = 549131) B549131
theorem B923147 : Blo 362758 923147 := bstep (se 1 (by rfl) ⟨692360, by rfl⟩ : syracuseStep 923147 = 1384721) B1384721
theorem B366095 : Blo 362758 366095 := bstep (se 1 (by rfl) ⟨274571, by rfl⟩ : syracuseStep 366095 = 549143) B549143
theorem B366139 : Blo 362758 366139 := bstep (se 1 (by rfl) ⟨274604, by rfl⟩ : syracuseStep 366139 = 549209) B549209
theorem B2954819 : Blo 362758 2954819 := bstep (se 1 (by rfl) ⟨2216114, by rfl⟩ : syracuseStep 2954819 = 4432229) B4432229
theorem B366215 : Blo 362758 366215 := bstep (se 1 (by rfl) ⟨274661, by rfl⟩ : syracuseStep 366215 = 549323) B549323
theorem B366223 : Blo 362758 366223 := bstep (se 1 (by rfl) ⟨274667, by rfl⟩ : syracuseStep 366223 = 549335) B549335
theorem B366267 : Blo 362758 366267 := bstep (se 1 (by rfl) ⟨274700, by rfl⟩ : syracuseStep 366267 = 549401) B549401
theorem B4429541 : Blo 362758 4429541 := bstep (se 4 (by rfl) ⟨415269, by rfl⟩ : syracuseStep 4429541 = 830539) B830539
theorem B366343 : Blo 362758 366343 := bstep (se 1 (by rfl) ⟨274757, by rfl⟩ : syracuseStep 366343 = 549515) B549515
theorem B366351 : Blo 362758 366351 := bstep (se 1 (by rfl) ⟨274763, by rfl⟩ : syracuseStep 366351 = 549527) B549527
theorem B366395 : Blo 362758 366395 := bstep (se 1 (by rfl) ⟨274796, by rfl⟩ : syracuseStep 366395 = 549593) B549593
theorem B366471 : Blo 362758 366471 := bstep (se 1 (by rfl) ⟨274853, by rfl⟩ : syracuseStep 366471 = 549707) B549707
theorem B366479 : Blo 362758 366479 := bstep (se 1 (by rfl) ⟨274859, by rfl⟩ : syracuseStep 366479 = 549719) B549719
theorem B1382291 : Blo 362758 1382291 := bstep (se 1 (by rfl) ⟨1036718, by rfl⟩ : syracuseStep 1382291 = 2073437) B2073437
theorem B2987929 : Blo 362758 2987929 := bstep (se 2 (by rfl) ⟨1120473, by rfl⟩ : syracuseStep 2987929 = 2240947) B2240947
theorem B366523 : Blo 362758 366523 := bstep (se 1 (by rfl) ⟨274892, by rfl⟩ : syracuseStep 366523 = 549785) B549785
theorem B366599 : Blo 362758 366599 := bstep (se 1 (by rfl) ⟨274949, by rfl⟩ : syracuseStep 366599 = 549899) B549899
theorem B923663 : Blo 362758 923663 := bstep (se 1 (by rfl) ⟨692747, by rfl⟩ : syracuseStep 923663 = 1385495) B1385495
theorem B366607 : Blo 362758 366607 := bstep (se 1 (by rfl) ⟨274955, by rfl⟩ : syracuseStep 366607 = 549911) B549911
theorem B366651 : Blo 362758 366651 := bstep (se 1 (by rfl) ⟨274988, by rfl⟩ : syracuseStep 366651 = 549977) B549977
theorem B366727 : Blo 362758 366727 := bstep (se 1 (by rfl) ⟨275045, by rfl⟩ : syracuseStep 366727 = 550091) B550091
theorem B366735 : Blo 362758 366735 := bstep (se 1 (by rfl) ⟨275051, by rfl⟩ : syracuseStep 366735 = 550103) B550103
theorem B923795 : Blo 362758 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B1382791 : Blo 362758 1382791 := bstep (se 1 (by rfl) ⟨1037093, by rfl⟩ : syracuseStep 1382791 = 2074187) B2074187
theorem B989815 : Blo 362758 989815 := bstep (se 1 (by rfl) ⟨742361, by rfl⟩ : syracuseStep 989815 = 1484723) B1484723
theorem B694919 : Blo 362758 694919 := bstep (se 1 (by rfl) ⟨521189, by rfl⟩ : syracuseStep 694919 = 1042379) B1042379
theorem B4168421 : Blo 362758 4168421 := bstep (se 4 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 4168421 = 781579) B781579
theorem B1317647 : Blo 362758 1317647 := bstep (se 1 (by rfl) ⟨988235, by rfl⟩ : syracuseStep 1317647 = 1976471) B1976471
theorem B14851133 : Blo 362758 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B1842263 : Blo 362758 1842263 := bstep (se 1 (by rfl) ⟨1381697, by rfl⟩ : syracuseStep 1842263 = 2763395) B2763395
theorem B924929 : Blo 362758 924929 := bstep (se 2 (by rfl) ⟨346848, by rfl⟩ : syracuseStep 924929 = 693697) B693697
theorem B499063 : Blo 362758 499063 := bstep (se 1 (by rfl) ⟨374297, by rfl⟩ : syracuseStep 499063 = 748595) B748595
theorem B1842749 : Blo 362758 1842749 := bstep (se 3 (by rfl) ⟨345515, by rfl⟩ : syracuseStep 1842749 = 691031) B691031
theorem B925303 : Blo 362758 925303 := bstep (se 1 (by rfl) ⟨693977, by rfl⟩ : syracuseStep 925303 = 1387955) B1387955
theorem B4038437 : Blo 362758 4038437 := bstep (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) B757207
theorem B991091 : Blo 362758 991091 := bstep (se 1 (by rfl) ⟨743318, by rfl⟩ : syracuseStep 991091 = 1486637) B1486637
theorem B925739 : Blo 362758 925739 := bstep (se 1 (by rfl) ⟨694304, by rfl⟩ : syracuseStep 925739 = 1388609) B1388609
theorem B467215 : Blo 362758 467215 := bstep (se 1 (by rfl) ⟨350411, by rfl⟩ : syracuseStep 467215 = 700823) B700823
theorem B1974827 : Blo 362758 1974827 := bstep (se 1 (by rfl) ⟨1481120, by rfl⟩ : syracuseStep 1974827 = 2962241) B2962241
theorem B4137803 : Blo 362758 4137803 := bstep (se 1 (by rfl) ⟨3103352, by rfl⟩ : syracuseStep 4137803 = 6206705) B6206705
theorem B926579 : Blo 362758 926579 := bstep (se 1 (by rfl) ⟨694934, by rfl⟩ : syracuseStep 926579 = 1389869) B1389869
theorem B926599 : Blo 362758 926599 := bstep (se 1 (by rfl) ⟨694949, by rfl⟩ : syracuseStep 926599 = 1389899) B1389899
theorem B7611479 : Blo 362758 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B926873 : Blo 362758 926873 := bstep (se 2 (by rfl) ⟨347577, by rfl⟩ : syracuseStep 926873 = 695155) B695155
theorem B369851 : Blo 362758 369851 := bstep (se 1 (by rfl) ⟨277388, by rfl⟩ : syracuseStep 369851 = 554777) B554777
theorem B1844531 : Blo 362758 1844531 := bstep (se 1 (by rfl) ⟨1383398, by rfl⟩ : syracuseStep 1844531 = 2766797) B2766797
theorem B927035 : Blo 362758 927035 := bstep (se 1 (by rfl) ⟨695276, by rfl⟩ : syracuseStep 927035 = 1390553) B1390553
theorem B4072913 : Blo 362758 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B927247 : Blo 362758 927247 := bstep (se 1 (by rfl) ⟨695435, by rfl⟩ : syracuseStep 927247 = 1390871) B1390871
theorem B1844855 : Blo 362758 1844855 := bstep (se 1 (by rfl) ⟨1383641, by rfl⟩ : syracuseStep 1844855 = 2767283) B2767283
theorem B4695731 : Blo 362758 4695731 := bstep (se 1 (by rfl) ⟨3521798, by rfl⟩ : syracuseStep 4695731 = 7043597) B7043597
theorem B2074369 : Blo 362758 2074369 := bstep (se 2 (by rfl) ⟨777888, by rfl⟩ : syracuseStep 2074369 = 1555777) B1555777
theorem B927521 : Blo 362758 927521 := bstep (se 2 (by rfl) ⟨347820, by rfl⟩ : syracuseStep 927521 = 695641) B695641
theorem B2074895 : Blo 362758 2074895 := bstep (se 1 (by rfl) ⟨1556171, by rfl⟩ : syracuseStep 2074895 = 3112343) B3112343
theorem B1976861 : Blo 362758 1976861 := bstep (se 3 (by rfl) ⟨370661, by rfl⟩ : syracuseStep 1976861 = 741323) B741323
theorem B1845827 : Blo 362758 1845827 := bstep (se 1 (by rfl) ⟨1384370, by rfl⟩ : syracuseStep 1845827 = 2768741) B2768741
theorem B2960165 : Blo 362758 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B1846151 : Blo 362758 1846151 := bstep (se 1 (by rfl) ⟨1384613, by rfl⟩ : syracuseStep 1846151 = 2769227) B2769227
theorem B1551251 : Blo 362758 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B2206649 : Blo 362758 2206649 := bstep (se 2 (by rfl) ⟨827493, by rfl⟩ : syracuseStep 2206649 = 1654987) B1654987
theorem B1551403 : Blo 362758 1551403 := bstep (se 1 (by rfl) ⟨1163552, by rfl⟩ : syracuseStep 1551403 = 2327105) B2327105
theorem B470135 : Blo 362758 470135 := bstep (se 1 (by rfl) ⟨352601, by rfl⟩ : syracuseStep 470135 = 705203) B705203
theorem B248491405 : Blo 362758 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B2076353 : Blo 362758 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B1224449 : Blo 362758 1224449 := bstep (se 2 (by rfl) ⟨459168, by rfl⟩ : syracuseStep 1224449 = 918337) B918337
theorem B1388441 : Blo 362758 1388441 := bstep (se 2 (by rfl) ⟨520665, by rfl⟩ : syracuseStep 1388441 = 1041331) B1041331
theorem B1552907 : Blo 362758 1552907 := bstep (se 1 (by rfl) ⟨1164680, by rfl⟩ : syracuseStep 1552907 = 2329361) B2329361
theorem B1225259 : Blo 362758 1225259 := bstep (se 1 (by rfl) ⟨918944, by rfl⟩ : syracuseStep 1225259 = 1837889) B1837889
theorem B2208545 : Blo 362758 2208545 := bstep (se 2 (by rfl) ⟨828204, by rfl⟩ : syracuseStep 2208545 = 1656409) B1656409
theorem B10466435 : Blo 362758 10466435 := bstep (se 1 (by rfl) ⟨7849826, by rfl⟩ : syracuseStep 10466435 = 15699653) B15699653
theorem B439543 : Blo 362758 439543 := bstep (se 1 (by rfl) ⟨329657, by rfl⟩ : syracuseStep 439543 = 659315) B659315
theorem B3519875 : Blo 362758 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B701831 : Blo 362758 701831 := bstep (se 1 (by rfl) ⟨526373, by rfl⟩ : syracuseStep 701831 = 1052747) B1052747
theorem B1553849 : Blo 362758 1553849 := bstep (se 2 (by rfl) ⟨582693, by rfl⟩ : syracuseStep 1553849 = 1165387) B1165387
theorem B1750481 : Blo 362758 1750481 := bstep (se 2 (by rfl) ⟨656430, by rfl⟩ : syracuseStep 1750481 = 1312861) B1312861
theorem B2635267 : Blo 362758 2635267 := bstep (se 1 (by rfl) ⟨1976450, by rfl⟩ : syracuseStep 2635267 = 3952901) B3952901
theorem B996923 : Blo 362758 996923 := bstep (se 1 (by rfl) ⟨747692, by rfl⟩ : syracuseStep 996923 = 1495385) B1495385
theorem B1226555 : Blo 362758 1226555 := bstep (se 1 (by rfl) ⟨919916, by rfl⟩ : syracuseStep 1226555 = 1839833) B1839833
theorem B2078743 : Blo 362758 2078743 := bstep (se 1 (by rfl) ⟨1559057, by rfl⟩ : syracuseStep 2078743 = 3118115) B3118115
theorem B1227041 : Blo 362758 1227041 := bstep (se 2 (by rfl) ⟨460140, by rfl⟩ : syracuseStep 1227041 = 920281) B920281
theorem B2111777 : Blo 362758 2111777 := bstep (se 2 (by rfl) ⟨791916, by rfl⟩ : syracuseStep 2111777 = 1583833) B1583833
theorem B1849715 : Blo 362758 1849715 := bstep (se 1 (by rfl) ⟨1387286, by rfl⟩ : syracuseStep 1849715 = 2774573) B2774573
theorem B408199 : Blo 362758 408199 := bstep (se 1 (by rfl) ⟨306149, by rfl⟩ : syracuseStep 408199 = 612299) B612299
theorem B408379 : Blo 362758 408379 := bstep (se 1 (by rfl) ⟨306284, by rfl⟩ : syracuseStep 408379 = 612569) B612569
theorem B1850201 : Blo 362758 1850201 := bstep (se 2 (by rfl) ⟨693825, by rfl⟩ : syracuseStep 1850201 = 1387651) B1387651
theorem B1227635 : Blo 362758 1227635 := bstep (se 1 (by rfl) ⟨920726, by rfl⟩ : syracuseStep 1227635 = 1841453) B1841453
theorem B2767769 : Blo 362758 2767769 := bstep (se 2 (by rfl) ⟨1037913, by rfl⟩ : syracuseStep 2767769 = 2075827) B2075827
theorem B408847 : Blo 362758 408847 := bstep (se 1 (by rfl) ⟨306635, by rfl⟩ : syracuseStep 408847 = 613271) B613271
theorem B4177169 : Blo 362758 4177169 := bstep (se 2 (by rfl) ⟨1566438, by rfl⟩ : syracuseStep 4177169 = 3132877) B3132877
theorem B736571 : Blo 362758 736571 := bstep (se 1 (by rfl) ⟨552428, by rfl⟩ : syracuseStep 736571 = 1104857) B1104857
theorem B1555847 : Blo 362758 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B1392025 : Blo 362758 1392025 := bstep (se 2 (by rfl) ⟨522009, by rfl⟩ : syracuseStep 1392025 = 1044019) B1044019
theorem B2637431 : Blo 362758 2637431 := bstep (se 1 (by rfl) ⟨1978073, by rfl⟩ : syracuseStep 2637431 = 3956147) B3956147
theorem B1392329 : Blo 362758 1392329 := bstep (se 2 (by rfl) ⟨522123, by rfl⟩ : syracuseStep 1392329 = 1044247) B1044247
theorem B409351 : Blo 362758 409351 := bstep (se 1 (by rfl) ⟨307013, by rfl⟩ : syracuseStep 409351 = 614027) B614027
theorem B409531 : Blo 362758 409531 := bstep (se 1 (by rfl) ⟨307148, by rfl⟩ : syracuseStep 409531 = 614297) B614297
theorem B2081159 : Blo 362758 2081159 := bstep (se 1 (by rfl) ⟨1560869, by rfl⟩ : syracuseStep 2081159 = 3121739) B3121739
theorem B409999 : Blo 362758 409999 := bstep (se 1 (by rfl) ⟨307499, by rfl⟩ : syracuseStep 409999 = 614999) B614999
theorem B2474387 : Blo 362758 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B14959235 : Blo 362758 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B3556057 : Blo 362758 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B2212609 : Blo 362758 2212609 := bstep (se 2 (by rfl) ⟨829728, by rfl⟩ : syracuseStep 2212609 = 1659457) B1659457
theorem B1557281 : Blo 362758 1557281 := bstep (se 2 (by rfl) ⟨583980, by rfl⟩ : syracuseStep 1557281 = 1167961) B1167961
theorem B2769713 : Blo 362758 2769713 := bstep (se 2 (by rfl) ⟨1038642, by rfl⟩ : syracuseStep 2769713 = 2077285) B2077285
theorem B410503 : Blo 362758 410503 := bstep (se 1 (by rfl) ⟨307877, by rfl⟩ : syracuseStep 410503 = 615755) B615755
theorem B1852307 : Blo 362758 1852307 := bstep (se 1 (by rfl) ⟨1389230, by rfl⟩ : syracuseStep 1852307 = 2778461) B2778461
theorem B1754135 : Blo 362758 1754135 := bstep (se 1 (by rfl) ⟨1315601, by rfl⟩ : syracuseStep 1754135 = 2631203) B2631203
theorem B410683 : Blo 362758 410683 := bstep (se 1 (by rfl) ⟨308012, by rfl⟩ : syracuseStep 410683 = 616025) B616025
theorem B1557623 : Blo 362758 1557623 := bstep (se 1 (by rfl) ⟨1168217, by rfl⟩ : syracuseStep 1557623 = 2336435) B2336435
theorem B4211957 : Blo 362758 4211957 := bstep (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) B394871
theorem B5064067 : Blo 362758 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B1230227 : Blo 362758 1230227 := bstep (se 1 (by rfl) ⟨922670, by rfl⟩ : syracuseStep 1230227 = 1845341) B1845341
theorem B411151 : Blo 362758 411151 := bstep (se 1 (by rfl) ⟨308363, by rfl⟩ : syracuseStep 411151 = 616727) B616727
theorem B6670001 : Blo 362758 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B3491545 : Blo 362758 3491545 := bstep (se 2 (by rfl) ⟨1309329, by rfl⟩ : syracuseStep 3491545 = 2618659) B2618659
theorem B1033985 : Blo 362758 1033985 := bstep (se 2 (by rfl) ⟨387744, by rfl⟩ : syracuseStep 1033985 = 775489) B775489
theorem B411655 : Blo 362758 411655 := bstep (se 1 (by rfl) ⟨308741, by rfl⟩ : syracuseStep 411655 = 617483) B617483
theorem B2082935 : Blo 362758 2082935 := bstep (se 1 (by rfl) ⟨1562201, by rfl⟩ : syracuseStep 2082935 = 3124403) B3124403
theorem B411835 : Blo 362758 411835 := bstep (se 1 (by rfl) ⟨308876, by rfl⟩ : syracuseStep 411835 = 617753) B617753
theorem B1034441 : Blo 362758 1034441 := bstep (se 2 (by rfl) ⟨387915, by rfl⟩ : syracuseStep 1034441 = 775831) B775831
theorem B412303 : Blo 362758 412303 := bstep (se 1 (by rfl) ⟨309227, by rfl⟩ : syracuseStep 412303 = 618455) B618455
theorem B1231631 : Blo 362758 1231631 := bstep (se 1 (by rfl) ⟨923723, by rfl⟩ : syracuseStep 1231631 = 1847447) B1847447
theorem B5917475 : Blo 362758 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B2083643 : Blo 362758 2083643 := bstep (se 1 (by rfl) ⟨1562732, by rfl⟩ : syracuseStep 2083643 = 3125465) B3125465
theorem B1231901 : Blo 362758 1231901 := bstep (se 3 (by rfl) ⟨230981, by rfl⟩ : syracuseStep 1231901 = 461963) B461963
theorem B2411693 : Blo 362758 2411693 := bstep (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) B904385
theorem B544187 : Blo 362758 544187 := bstep (se 1 (by rfl) ⟨408140, by rfl⟩ : syracuseStep 544187 = 816281) B816281
theorem B544247 : Blo 362758 544247 := bstep (se 1 (by rfl) ⟨408185, by rfl⟩ : syracuseStep 544247 = 816371) B816371
theorem B544271 : Blo 362758 544271 := bstep (se 1 (by rfl) ⟨408203, by rfl⟩ : syracuseStep 544271 = 816407) B816407
theorem B544313 : Blo 362758 544313 := bstep (se 2 (by rfl) ⟨204117, by rfl⟩ : syracuseStep 544313 = 408235) B408235
theorem B1560151 : Blo 362758 1560151 := bstep (se 1 (by rfl) ⟨1170113, by rfl⟩ : syracuseStep 1560151 = 2340227) B2340227
theorem B544391 : Blo 362758 544391 := bstep (se 1 (by rfl) ⟨408293, by rfl⟩ : syracuseStep 544391 = 816587) B816587
theorem B544427 : Blo 362758 544427 := bstep (se 1 (by rfl) ⟨408320, by rfl⟩ : syracuseStep 544427 = 816641) B816641
theorem B544457 : Blo 362758 544457 := bstep (se 2 (by rfl) ⟨204171, by rfl⟩ : syracuseStep 544457 = 408343) B408343
theorem B544571 : Blo 362758 544571 := bstep (se 1 (by rfl) ⟨408428, by rfl⟩ : syracuseStep 544571 = 816857) B816857
theorem B1036091 : Blo 362758 1036091 := bstep (se 1 (by rfl) ⟨777068, by rfl⟩ : syracuseStep 1036091 = 1554137) B1554137
theorem B544631 : Blo 362758 544631 := bstep (se 1 (by rfl) ⟨408473, by rfl⟩ : syracuseStep 544631 = 816947) B816947
theorem B544655 : Blo 362758 544655 := bstep (se 1 (by rfl) ⟨408491, by rfl⟩ : syracuseStep 544655 = 816983) B816983
theorem B1855385 : Blo 362758 1855385 := bstep (se 2 (by rfl) ⟨695769, by rfl⟩ : syracuseStep 1855385 = 1391539) B1391539
theorem B544697 : Blo 362758 544697 := bstep (se 2 (by rfl) ⟨204261, by rfl⟩ : syracuseStep 544697 = 408523) B408523
theorem B3100619 : Blo 362758 3100619 := bstep (se 1 (by rfl) ⟨2325464, by rfl⟩ : syracuseStep 3100619 = 4650929) B4650929
theorem B4673483 : Blo 362758 4673483 := bstep (se 1 (by rfl) ⟨3505112, by rfl⟩ : syracuseStep 4673483 = 7010225) B7010225
theorem B544775 : Blo 362758 544775 := bstep (se 1 (by rfl) ⟨408581, by rfl⟩ : syracuseStep 544775 = 817163) B817163
theorem B544811 : Blo 362758 544811 := bstep (se 1 (by rfl) ⟨408608, by rfl⟩ : syracuseStep 544811 = 817217) B817217
theorem B544841 : Blo 362758 544841 := bstep (se 2 (by rfl) ⟨204315, by rfl⟩ : syracuseStep 544841 = 408631) B408631
theorem B544955 : Blo 362758 544955 := bstep (se 1 (by rfl) ⟨408716, by rfl⟩ : syracuseStep 544955 = 817433) B817433
theorem B2085101 : Blo 362758 2085101 := bstep (se 3 (by rfl) ⟨390956, by rfl⟩ : syracuseStep 2085101 = 781913) B781913
theorem B545015 : Blo 362758 545015 := bstep (se 1 (by rfl) ⟨408761, by rfl⟩ : syracuseStep 545015 = 817523) B817523
theorem B545039 : Blo 362758 545039 := bstep (se 1 (by rfl) ⟨408779, by rfl⟩ : syracuseStep 545039 = 817559) B817559
theorem B545081 : Blo 362758 545081 := bstep (se 2 (by rfl) ⟨204405, by rfl⟩ : syracuseStep 545081 = 408811) B408811
theorem B938299 : Blo 362758 938299 := bstep (se 1 (by rfl) ⟨703724, by rfl⟩ : syracuseStep 938299 = 1407449) B1407449
theorem B1069427 : Blo 362758 1069427 := bstep (se 1 (by rfl) ⟨802070, by rfl⟩ : syracuseStep 1069427 = 1604141) B1604141
theorem B545159 : Blo 362758 545159 := bstep (se 1 (by rfl) ⟨408869, by rfl⟩ : syracuseStep 545159 = 817739) B817739
theorem B1233305 : Blo 362758 1233305 := bstep (se 2 (by rfl) ⟨462489, by rfl⟩ : syracuseStep 1233305 = 924979) B924979
theorem B545195 : Blo 362758 545195 := bstep (se 1 (by rfl) ⟨408896, by rfl⟩ : syracuseStep 545195 = 817793) B817793
theorem B1036729 : Blo 362758 1036729 := bstep (se 2 (by rfl) ⟨388773, by rfl⟩ : syracuseStep 1036729 = 777547) B777547
theorem B545225 : Blo 362758 545225 := bstep (se 2 (by rfl) ⟨204459, by rfl⟩ : syracuseStep 545225 = 408919) B408919
theorem B872993 : Blo 362758 872993 := bstep (se 2 (by rfl) ⟨327372, by rfl⟩ : syracuseStep 872993 = 654745) B654745
theorem B545339 : Blo 362758 545339 := bstep (se 1 (by rfl) ⟨409004, by rfl⟩ : syracuseStep 545339 = 818009) B818009
theorem B545399 : Blo 362758 545399 := bstep (se 1 (by rfl) ⟨409049, by rfl⟩ : syracuseStep 545399 = 818099) B818099
theorem B545423 : Blo 362758 545423 := bstep (se 1 (by rfl) ⟨409067, by rfl⟩ : syracuseStep 545423 = 818135) B818135
theorem B545465 : Blo 362758 545465 := bstep (se 2 (by rfl) ⟨204549, by rfl⟩ : syracuseStep 545465 = 409099) B409099
theorem B545543 : Blo 362758 545543 := bstep (se 1 (by rfl) ⟨409157, by rfl⟩ : syracuseStep 545543 = 818315) B818315
theorem B545579 : Blo 362758 545579 := bstep (se 1 (by rfl) ⟨409184, by rfl⟩ : syracuseStep 545579 = 818369) B818369
theorem B1037117 : Blo 362758 1037117 := bstep (se 3 (by rfl) ⟨194459, by rfl⟩ : syracuseStep 1037117 = 388919) B388919
theorem B545609 : Blo 362758 545609 := bstep (se 2 (by rfl) ⟨204603, by rfl⟩ : syracuseStep 545609 = 409207) B409207
theorem B545723 : Blo 362758 545723 := bstep (se 1 (by rfl) ⟨409292, by rfl⟩ : syracuseStep 545723 = 818585) B818585
theorem B545783 : Blo 362758 545783 := bstep (se 1 (by rfl) ⟨409337, by rfl⟩ : syracuseStep 545783 = 818675) B818675
theorem B545807 : Blo 362758 545807 := bstep (se 1 (by rfl) ⟨409355, by rfl⟩ : syracuseStep 545807 = 818711) B818711
theorem B545849 : Blo 362758 545849 := bstep (se 2 (by rfl) ⟨204693, by rfl⟩ : syracuseStep 545849 = 409387) B409387
theorem B1234007 : Blo 362758 1234007 := bstep (se 1 (by rfl) ⟨925505, by rfl⟩ : syracuseStep 1234007 = 1851011) B1851011
theorem B545927 : Blo 362758 545927 := bstep (se 1 (by rfl) ⟨409445, by rfl⟩ : syracuseStep 545927 = 818891) B818891
theorem B545963 : Blo 362758 545963 := bstep (se 1 (by rfl) ⟨409472, by rfl⟩ : syracuseStep 545963 = 818945) B818945
theorem B545993 : Blo 362758 545993 := bstep (se 2 (by rfl) ⟨204747, by rfl⟩ : syracuseStep 545993 = 409495) B409495
theorem B546107 : Blo 362758 546107 := bstep (se 1 (by rfl) ⟨409580, by rfl⟩ : syracuseStep 546107 = 819161) B819161
theorem B677179 : Blo 362758 677179 := bstep (se 1 (by rfl) ⟨507884, by rfl⟩ : syracuseStep 677179 = 1015769) B1015769
theorem B546167 : Blo 362758 546167 := bstep (se 1 (by rfl) ⟨409625, by rfl⟩ : syracuseStep 546167 = 819251) B819251
theorem B546191 : Blo 362758 546191 := bstep (se 1 (by rfl) ⟨409643, by rfl⟩ : syracuseStep 546191 = 819287) B819287
theorem B546233 : Blo 362758 546233 := bstep (se 2 (by rfl) ⟨204837, by rfl⟩ : syracuseStep 546233 = 409675) B409675
theorem B546311 : Blo 362758 546311 := bstep (se 1 (by rfl) ⟨409733, by rfl⟩ : syracuseStep 546311 = 819467) B819467
theorem B546347 : Blo 362758 546347 := bstep (se 1 (by rfl) ⟨409760, by rfl⟩ : syracuseStep 546347 = 819521) B819521
theorem B1234493 : Blo 362758 1234493 := bstep (se 3 (by rfl) ⟨231467, by rfl⟩ : syracuseStep 1234493 = 462935) B462935
theorem B546377 : Blo 362758 546377 := bstep (se 2 (by rfl) ⟨204891, by rfl⟩ : syracuseStep 546377 = 409783) B409783
theorem B546491 : Blo 362758 546491 := bstep (se 1 (by rfl) ⟨409868, by rfl⟩ : syracuseStep 546491 = 819737) B819737
theorem B546551 : Blo 362758 546551 := bstep (se 1 (by rfl) ⟨409913, by rfl⟩ : syracuseStep 546551 = 819827) B819827
theorem B546575 : Blo 362758 546575 := bstep (se 1 (by rfl) ⟨409931, by rfl⟩ : syracuseStep 546575 = 819863) B819863
theorem B546617 : Blo 362758 546617 := bstep (se 2 (by rfl) ⟨204981, by rfl⟩ : syracuseStep 546617 = 409963) B409963
theorem B546695 : Blo 362758 546695 := bstep (se 1 (by rfl) ⟨410021, by rfl⟩ : syracuseStep 546695 = 820043) B820043
theorem B1038233 : Blo 362758 1038233 := bstep (se 2 (by rfl) ⟨389337, by rfl⟩ : syracuseStep 1038233 = 778675) B778675
theorem B546731 : Blo 362758 546731 := bstep (se 1 (by rfl) ⟨410048, by rfl⟩ : syracuseStep 546731 = 820097) B820097
theorem B546761 : Blo 362758 546761 := bstep (se 2 (by rfl) ⟨205035, by rfl⟩ : syracuseStep 546761 = 410071) B410071
theorem B546875 : Blo 362758 546875 := bstep (se 1 (by rfl) ⟨410156, by rfl⟩ : syracuseStep 546875 = 820313) B820313
theorem B546935 : Blo 362758 546935 := bstep (se 1 (by rfl) ⟨410201, by rfl⟩ : syracuseStep 546935 = 820403) B820403
theorem B546959 : Blo 362758 546959 := bstep (se 1 (by rfl) ⟨410219, by rfl⟩ : syracuseStep 546959 = 820439) B820439
theorem B547001 : Blo 362758 547001 := bstep (se 2 (by rfl) ⟨205125, by rfl⟩ : syracuseStep 547001 = 410251) B410251
theorem B547079 : Blo 362758 547079 := bstep (se 1 (by rfl) ⟨410309, by rfl⟩ : syracuseStep 547079 = 820619) B820619
theorem B612623 : Blo 362758 612623 := bstep (se 1 (by rfl) ⟨459467, by rfl⟩ : syracuseStep 612623 = 918935) B918935
theorem B547115 : Blo 362758 547115 := bstep (se 1 (by rfl) ⟨410336, by rfl⟩ : syracuseStep 547115 = 820673) B820673
theorem B547145 : Blo 362758 547145 := bstep (se 2 (by rfl) ⟨205179, by rfl⟩ : syracuseStep 547145 = 410359) B410359
theorem B547259 : Blo 362758 547259 := bstep (se 1 (by rfl) ⟨410444, by rfl⟩ : syracuseStep 547259 = 820889) B820889
theorem B547319 : Blo 362758 547319 := bstep (se 1 (by rfl) ⟨410489, by rfl⟩ : syracuseStep 547319 = 820979) B820979
theorem B776719 : Blo 362758 776719 := bstep (se 1 (by rfl) ⟨582539, by rfl⟩ : syracuseStep 776719 = 1165079) B1165079
theorem B547343 : Blo 362758 547343 := bstep (se 1 (by rfl) ⟨410507, by rfl⟩ : syracuseStep 547343 = 821015) B821015
theorem B547385 : Blo 362758 547385 := bstep (se 2 (by rfl) ⟨205269, by rfl⟩ : syracuseStep 547385 = 410539) B410539
theorem B2087491 : Blo 362758 2087491 := bstep (se 1 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 2087491 = 3131237) B3131237
theorem B547463 : Blo 362758 547463 := bstep (se 1 (by rfl) ⟨410597, by rfl⟩ : syracuseStep 547463 = 821195) B821195
theorem B547499 : Blo 362758 547499 := bstep (se 1 (by rfl) ⟨410624, by rfl⟩ : syracuseStep 547499 = 821249) B821249
theorem B547529 : Blo 362758 547529 := bstep (se 2 (by rfl) ⟨205323, by rfl⟩ : syracuseStep 547529 = 410647) B410647
theorem B8903459 : Blo 362758 8903459 := bstep (se 1 (by rfl) ⟨6677594, by rfl⟩ : syracuseStep 8903459 = 13355189) B13355189
theorem B613163 : Blo 362758 613163 := bstep (se 1 (by rfl) ⟨459872, by rfl⟩ : syracuseStep 613163 = 919745) B919745
theorem B547643 : Blo 362758 547643 := bstep (se 1 (by rfl) ⟨410732, by rfl⟩ : syracuseStep 547643 = 821465) B821465
theorem B547703 : Blo 362758 547703 := bstep (se 1 (by rfl) ⟨410777, by rfl⟩ : syracuseStep 547703 = 821555) B821555
theorem B547727 : Blo 362758 547727 := bstep (se 1 (by rfl) ⟨410795, by rfl⟩ : syracuseStep 547727 = 821591) B821591
theorem B547769 : Blo 362758 547769 := bstep (se 2 (by rfl) ⟨205413, by rfl⟩ : syracuseStep 547769 = 410827) B410827
theorem B1235897 : Blo 362758 1235897 := bstep (se 2 (by rfl) ⟨463461, by rfl⟩ : syracuseStep 1235897 = 926923) B926923
theorem B1334225 : Blo 362758 1334225 := bstep (se 2 (by rfl) ⟨500334, by rfl⟩ : syracuseStep 1334225 = 1000669) B1000669
theorem B547847 : Blo 362758 547847 := bstep (se 1 (by rfl) ⟨410885, by rfl⟩ : syracuseStep 547847 = 821771) B821771
theorem B1760285 : Blo 362758 1760285 := bstep (se 3 (by rfl) ⟨330053, by rfl⟩ : syracuseStep 1760285 = 660107) B660107
theorem B547883 : Blo 362758 547883 := bstep (se 1 (by rfl) ⟨410912, by rfl⟩ : syracuseStep 547883 = 821825) B821825
theorem B547913 : Blo 362758 547913 := bstep (se 2 (by rfl) ⟨205467, by rfl⟩ : syracuseStep 547913 = 410935) B410935
theorem B1170551 : Blo 362758 1170551 := bstep (se 1 (by rfl) ⟨877913, by rfl⟩ : syracuseStep 1170551 = 1755827) B1755827
theorem B613561 : Blo 362758 613561 := bstep (se 2 (by rfl) ⟨230085, by rfl⟩ : syracuseStep 613561 = 460171) B460171
theorem B548027 : Blo 362758 548027 := bstep (se 1 (by rfl) ⟨411020, by rfl⟩ : syracuseStep 548027 = 822041) B822041
theorem B548087 : Blo 362758 548087 := bstep (se 1 (by rfl) ⟨411065, by rfl⟩ : syracuseStep 548087 = 822131) B822131
theorem B548111 : Blo 362758 548111 := bstep (se 1 (by rfl) ⟨411083, by rfl⟩ : syracuseStep 548111 = 822167) B822167
theorem B1039645 : Blo 362758 1039645 := bstep (se 3 (by rfl) ⟨194933, by rfl⟩ : syracuseStep 1039645 = 389867) B389867
theorem B548153 : Blo 362758 548153 := bstep (se 2 (by rfl) ⟨205557, by rfl⟩ : syracuseStep 548153 = 411115) B411115
theorem B14179643 : Blo 362758 14179643 := bstep (se 1 (by rfl) ⟨10634732, by rfl⟩ : syracuseStep 14179643 = 21269465) B21269465
theorem B33840443 : Blo 362758 33840443 := bstep (se 1 (by rfl) ⟨25380332, by rfl⟩ : syracuseStep 33840443 = 50760665) B50760665
theorem B548231 : Blo 362758 548231 := bstep (se 1 (by rfl) ⟨411173, by rfl⟩ : syracuseStep 548231 = 822347) B822347
theorem B548267 : Blo 362758 548267 := bstep (se 1 (by rfl) ⟨411200, by rfl⟩ : syracuseStep 548267 = 822401) B822401
theorem B1039817 : Blo 362758 1039817 := bstep (se 2 (by rfl) ⟨389931, by rfl⟩ : syracuseStep 1039817 = 779863) B779863
theorem B548297 : Blo 362758 548297 := bstep (se 2 (by rfl) ⟨205611, by rfl⟩ : syracuseStep 548297 = 411223) B411223
theorem B1039873 : Blo 362758 1039873 := bstep (se 2 (by rfl) ⟨389952, by rfl⟩ : syracuseStep 1039873 = 779905) B779905
theorem B1236491 : Blo 362758 1236491 := bstep (se 1 (by rfl) ⟨927368, by rfl⟩ : syracuseStep 1236491 = 1854737) B1854737
theorem B548411 : Blo 362758 548411 := bstep (se 1 (by rfl) ⟨411308, by rfl⟩ : syracuseStep 548411 = 822617) B822617
theorem B548471 : Blo 362758 548471 := bstep (se 1 (by rfl) ⟨411353, by rfl⟩ : syracuseStep 548471 = 822707) B822707
theorem B1236599 : Blo 362758 1236599 := bstep (se 1 (by rfl) ⟨927449, by rfl⟩ : syracuseStep 1236599 = 1854899) B1854899
theorem B548495 : Blo 362758 548495 := bstep (se 1 (by rfl) ⟨411371, by rfl⟩ : syracuseStep 548495 = 822743) B822743
theorem B548537 : Blo 362758 548537 := bstep (se 2 (by rfl) ⟨205701, by rfl⟩ : syracuseStep 548537 = 411403) B411403
theorem B548615 : Blo 362758 548615 := bstep (se 1 (by rfl) ⟨411461, by rfl⟩ : syracuseStep 548615 = 822923) B822923
theorem B548651 : Blo 362758 548651 := bstep (se 1 (by rfl) ⟨411488, by rfl⟩ : syracuseStep 548651 = 822977) B822977
theorem B548681 : Blo 362758 548681 := bstep (se 2 (by rfl) ⟨205755, by rfl⟩ : syracuseStep 548681 = 411511) B411511
theorem B1040215 : Blo 362758 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B614263 : Blo 362758 614263 := bstep (se 1 (by rfl) ⟨460697, by rfl⟩ : syracuseStep 614263 = 921395) B921395
theorem B1761209 : Blo 362758 1761209 := bstep (se 2 (by rfl) ⟨660453, by rfl⟩ : syracuseStep 1761209 = 1320907) B1320907
theorem B548795 : Blo 362758 548795 := bstep (se 1 (by rfl) ⟨411596, by rfl⟩ : syracuseStep 548795 = 823193) B823193
theorem B548855 : Blo 362758 548855 := bstep (se 1 (by rfl) ⟨411641, by rfl⟩ : syracuseStep 548855 = 823283) B823283
theorem B548879 : Blo 362758 548879 := bstep (se 1 (by rfl) ⟨411659, by rfl⟩ : syracuseStep 548879 = 823319) B823319
theorem B876577 : Blo 362758 876577 := bstep (se 2 (by rfl) ⟨328716, by rfl⟩ : syracuseStep 876577 = 657433) B657433
theorem B548921 : Blo 362758 548921 := bstep (se 2 (by rfl) ⟨205845, by rfl⟩ : syracuseStep 548921 = 411691) B411691
theorem B614459 : Blo 362758 614459 := bstep (se 1 (by rfl) ⟨460844, by rfl⟩ : syracuseStep 614459 = 921689) B921689
theorem B548999 : Blo 362758 548999 := bstep (se 1 (by rfl) ⟨411749, by rfl⟩ : syracuseStep 548999 = 823499) B823499
theorem B549035 : Blo 362758 549035 := bstep (se 1 (by rfl) ⟨411776, by rfl⟩ : syracuseStep 549035 = 823553) B823553
theorem B549065 : Blo 362758 549065 := bstep (se 2 (by rfl) ⟨205899, by rfl⟩ : syracuseStep 549065 = 411799) B411799
theorem B1237193 : Blo 362758 1237193 := bstep (se 2 (by rfl) ⟨463947, by rfl⟩ : syracuseStep 1237193 = 927895) B927895
theorem B3825953 : Blo 362758 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B549179 : Blo 362758 549179 := bstep (se 1 (by rfl) ⟨411884, by rfl⟩ : syracuseStep 549179 = 823769) B823769
theorem B549239 : Blo 362758 549239 := bstep (se 1 (by rfl) ⟨411929, by rfl⟩ : syracuseStep 549239 = 823859) B823859
theorem B549263 : Blo 362758 549263 := bstep (se 1 (by rfl) ⟨411947, by rfl⟩ : syracuseStep 549263 = 823895) B823895
theorem B2777489 : Blo 362758 2777489 := bstep (se 2 (by rfl) ⟨1041558, by rfl⟩ : syracuseStep 2777489 = 2083117) B2083117
theorem B549305 : Blo 362758 549305 := bstep (se 2 (by rfl) ⟨205989, by rfl⟩ : syracuseStep 549305 = 411979) B411979
theorem B614857 : Blo 362758 614857 := bstep (se 2 (by rfl) ⟨230571, by rfl⟩ : syracuseStep 614857 = 461143) B461143
theorem B549383 : Blo 362758 549383 := bstep (se 1 (by rfl) ⟨412037, by rfl⟩ : syracuseStep 549383 = 824075) B824075
theorem B549419 : Blo 362758 549419 := bstep (se 1 (by rfl) ⟨412064, by rfl⟩ : syracuseStep 549419 = 824129) B824129
theorem B549449 : Blo 362758 549449 := bstep (se 2 (by rfl) ⟨206043, by rfl⟩ : syracuseStep 549449 = 412087) B412087
theorem B516793 : Blo 362758 516793 := bstep (se 2 (by rfl) ⟨193797, by rfl⟩ : syracuseStep 516793 = 387595) B387595
theorem B549563 : Blo 362758 549563 := bstep (se 1 (by rfl) ⟨412172, by rfl⟩ : syracuseStep 549563 = 824345) B824345
theorem B549623 : Blo 362758 549623 := bstep (se 1 (by rfl) ⟨412217, by rfl⟩ : syracuseStep 549623 = 824435) B824435
theorem B549647 : Blo 362758 549647 := bstep (se 1 (by rfl) ⟨412235, by rfl⟩ : syracuseStep 549647 = 824471) B824471
theorem B779051 : Blo 362758 779051 := bstep (se 1 (by rfl) ⟨584288, by rfl⟩ : syracuseStep 779051 = 1168577) B1168577
theorem B549689 : Blo 362758 549689 := bstep (se 2 (by rfl) ⟨206133, by rfl⟩ : syracuseStep 549689 = 412267) B412267
theorem B549767 : Blo 362758 549767 := bstep (se 1 (by rfl) ⟨412325, by rfl⟩ : syracuseStep 549767 = 824651) B824651
theorem B549803 : Blo 362758 549803 := bstep (se 1 (by rfl) ⟨412352, by rfl⟩ : syracuseStep 549803 = 824705) B824705
theorem B549833 : Blo 362758 549833 := bstep (se 2 (by rfl) ⟨206187, by rfl⟩ : syracuseStep 549833 = 412375) B412375
theorem B549947 : Blo 362758 549947 := bstep (se 1 (by rfl) ⟨412460, by rfl⟩ : syracuseStep 549947 = 824921) B824921
theorem B550007 : Blo 362758 550007 := bstep (se 1 (by rfl) ⟨412505, by rfl⟩ : syracuseStep 550007 = 825011) B825011
theorem B615559 : Blo 362758 615559 := bstep (se 1 (by rfl) ⟨461669, by rfl⟩ : syracuseStep 615559 = 923339) B923339
theorem B550031 : Blo 362758 550031 := bstep (se 1 (by rfl) ⟨412523, by rfl⟩ : syracuseStep 550031 = 825047) B825047
theorem B550073 : Blo 362758 550073 := bstep (se 2 (by rfl) ⟨206277, by rfl⟩ : syracuseStep 550073 = 412555) B412555
theorem B8381875 : Blo 362758 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B714169 : Blo 362758 714169 := bstep (se 2 (by rfl) ⟨267813, by rfl⟩ : syracuseStep 714169 = 535627) B535627
theorem B616207 : Blo 362758 616207 := bstep (se 1 (by rfl) ⟨462155, by rfl⟩ : syracuseStep 616207 = 924311) B924311
theorem B518023 : Blo 362758 518023 := bstep (se 1 (by rfl) ⟨388517, by rfl⟩ : syracuseStep 518023 = 777035) B777035
theorem B878471 : Blo 362758 878471 := bstep (se 1 (by rfl) ⟨658853, by rfl⟩ : syracuseStep 878471 = 1317707) B1317707
theorem B4155299 : Blo 362758 4155299 := bstep (se 1 (by rfl) ⟨3116474, by rfl⟩ : syracuseStep 4155299 = 6232949) B6232949
theorem B616747 : Blo 362758 616747 := bstep (se 1 (by rfl) ⟨462560, by rfl⟩ : syracuseStep 616747 = 925121) B925121
theorem B780691 : Blo 362758 780691 := bstep (se 1 (by rfl) ⟨585518, by rfl⟩ : syracuseStep 780691 = 1171037) B1171037
theorem B616889 : Blo 362758 616889 := bstep (se 2 (by rfl) ⟨231333, by rfl⟩ : syracuseStep 616889 = 462667) B462667
theorem B518729 : Blo 362758 518729 := bstep (se 2 (by rfl) ⟨194523, by rfl⟩ : syracuseStep 518729 = 389047) B389047
theorem B1043063 : Blo 362758 1043063 := bstep (se 1 (by rfl) ⟨782297, by rfl⟩ : syracuseStep 1043063 = 1564595) B1564595
theorem B518843 : Blo 362758 518843 := bstep (se 1 (by rfl) ⟨389132, by rfl⟩ : syracuseStep 518843 = 778265) B778265
theorem B3959513 : Blo 362758 3959513 := bstep (se 2 (by rfl) ⟨1484817, by rfl⟩ : syracuseStep 3959513 = 2969635) B2969635
theorem B2779919 : Blo 362758 2779919 := bstep (se 1 (by rfl) ⟨2084939, by rfl⟩ : syracuseStep 2779919 = 4169879) B4169879
theorem B617591 : Blo 362758 617591 := bstep (se 1 (by rfl) ⟨463193, by rfl⟩ : syracuseStep 617591 = 926387) B926387
theorem B519481 : Blo 362758 519481 := bstep (se 2 (by rfl) ⟨194805, by rfl⟩ : syracuseStep 519481 = 389611) B389611
theorem B585019 : Blo 362758 585019 := bstep (se 1 (by rfl) ⟨438764, by rfl⟩ : syracuseStep 585019 = 877529) B877529
theorem B618043 : Blo 362758 618043 := bstep (se 1 (by rfl) ⟨463532, by rfl⟩ : syracuseStep 618043 = 927065) B927065
theorem B618185 : Blo 362758 618185 := bstep (se 2 (by rfl) ⟨231819, by rfl⟩ : syracuseStep 618185 = 463639) B463639
theorem B5336833 : Blo 362758 5336833 := bstep (se 2 (by rfl) ⟨2001312, by rfl⟩ : syracuseStep 5336833 = 4002625) B4002625
theorem B552763 : Blo 362758 552763 := bstep (se 1 (by rfl) ⟨414572, by rfl⟩ : syracuseStep 552763 = 829145) B829145
theorem B1109819 : Blo 362758 1109819 := bstep (se 1 (by rfl) ⟨832364, by rfl⟩ : syracuseStep 1109819 = 1664729) B1664729
theorem B1044481 : Blo 362758 1044481 := bstep (se 2 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 1044481 = 783361) B783361
theorem B585929 : Blo 362758 585929 := bstep (se 2 (by rfl) ⟨219723, by rfl⟩ : syracuseStep 585929 = 439447) B439447
theorem B618887 : Blo 362758 618887 := bstep (se 1 (by rfl) ⟨464165, by rfl⟩ : syracuseStep 618887 = 928331) B928331
theorem B586441 : Blo 362758 586441 := bstep (se 2 (by rfl) ⟨219915, by rfl⟩ : syracuseStep 586441 = 439831) B439831
theorem B783049 : Blo 362758 783049 := bstep (se 2 (by rfl) ⟨293643, by rfl⟩ : syracuseStep 783049 = 587287) B587287
theorem B586697 : Blo 362758 586697 := bstep (se 2 (by rfl) ⟨220011, by rfl⟩ : syracuseStep 586697 = 440023) B440023
theorem B1471441 : Blo 362758 1471441 := bstep (se 2 (by rfl) ⟨551790, by rfl⟩ : syracuseStep 1471441 = 1103581) B1103581
theorem B816263 : Blo 362758 816263 := bstep (se 1 (by rfl) ⟨612197, by rfl⟩ : syracuseStep 816263 = 1224395) B1224395
theorem B816443 : Blo 362758 816443 := bstep (se 1 (by rfl) ⟨612332, by rfl⟩ : syracuseStep 816443 = 1224665) B1224665
theorem B816569 : Blo 362758 816569 := bstep (se 2 (by rfl) ⟨306213, by rfl⟩ : syracuseStep 816569 = 612427) B612427
theorem B3175901 : Blo 362758 3175901 := bstep (se 3 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 3175901 = 1190963) B1190963
theorem B1308221 : Blo 362758 1308221 := bstep (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) B490583
theorem B6649573 : Blo 362758 6649573 := bstep (se 4 (by rfl) ⟨623397, by rfl⟩ : syracuseStep 6649573 = 1246795) B1246795
theorem B816911 : Blo 362758 816911 := bstep (se 1 (by rfl) ⟨612683, by rfl⟩ : syracuseStep 816911 = 1225367) B1225367
theorem B816929 : Blo 362758 816929 := bstep (se 2 (by rfl) ⟨306348, by rfl⟩ : syracuseStep 816929 = 612697) B612697
theorem B817271 : Blo 362758 817271 := bstep (se 1 (by rfl) ⟨612953, by rfl⟩ : syracuseStep 817271 = 1225907) B1225907
theorem B391439 : Blo 362758 391439 := bstep (se 1 (by rfl) ⟨293579, by rfl⟩ : syracuseStep 391439 = 587159) B587159
theorem B817451 : Blo 362758 817451 := bstep (se 1 (by rfl) ⟨613088, by rfl⟩ : syracuseStep 817451 = 1226177) B1226177
theorem B981533 : Blo 362758 981533 := bstep (se 3 (by rfl) ⟨184037, by rfl⟩ : syracuseStep 981533 = 368075) B368075
theorem B817811 : Blo 362758 817811 := bstep (se 1 (by rfl) ⟨613358, by rfl⟩ : syracuseStep 817811 = 1226717) B1226717
theorem B817865 : Blo 362758 817865 := bstep (se 2 (by rfl) ⟨306699, by rfl⟩ : syracuseStep 817865 = 613399) B613399
theorem B7863155 : Blo 362758 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B785543 : Blo 362758 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B1998053 : Blo 362758 1998053 := bstep (se 4 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 1998053 = 374635) B374635
theorem B18513197 : Blo 362758 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B818567 : Blo 362758 818567 := bstep (se 1 (by rfl) ⟨613925, by rfl⟩ : syracuseStep 818567 = 1227851) B1227851
theorem B622139 : Blo 362758 622139 := bstep (se 1 (by rfl) ⟨466604, by rfl⟩ : syracuseStep 622139 = 933209) B933209
theorem B818747 : Blo 362758 818747 := bstep (se 1 (by rfl) ⟨614060, by rfl⟩ : syracuseStep 818747 = 1228121) B1228121
theorem B5242445 : Blo 362758 5242445 := bstep (se 3 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 5242445 = 1965917) B1965917
theorem B818873 : Blo 362758 818873 := bstep (se 2 (by rfl) ⟨307077, by rfl⟩ : syracuseStep 818873 = 614155) B614155
theorem B9961217 : Blo 362758 9961217 := bstep (se 2 (by rfl) ⟨3735456, by rfl⟩ : syracuseStep 9961217 = 7470913) B7470913
theorem B655379 : Blo 362758 655379 := bstep (se 1 (by rfl) ⟨491534, by rfl⟩ : syracuseStep 655379 = 983069) B983069
theorem B2490425 : Blo 362758 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B819809 : Blo 362758 819809 := bstep (se 2 (by rfl) ⟨307428, by rfl⟩ : syracuseStep 819809 = 614857) B614857
theorem B524999 : Blo 362758 524999 := bstep (se 1 (by rfl) ⟨393749, by rfl⟩ : syracuseStep 524999 = 787499) B787499
theorem B656201 : Blo 362758 656201 := bstep (se 2 (by rfl) ⟨246075, by rfl⟩ : syracuseStep 656201 = 492151) B492151
theorem B689057 : Blo 362758 689057 := bstep (se 2 (by rfl) ⟨258396, by rfl⟩ : syracuseStep 689057 = 516793) B516793
theorem B459695 : Blo 362758 459695 := bstep (se 1 (by rfl) ⟨344771, by rfl⟩ : syracuseStep 459695 = 689543) B689543
theorem B820151 : Blo 362758 820151 := bstep (se 1 (by rfl) ⟨615113, by rfl⟩ : syracuseStep 820151 = 1230227) B1230227
theorem B1115063 : Blo 362758 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B2950145 : Blo 362758 2950145 := bstep (se 2 (by rfl) ⟨1106304, by rfl⟩ : syracuseStep 2950145 = 2212609) B2212609
theorem B689323 : Blo 362758 689323 := bstep (se 1 (by rfl) ⟨516992, by rfl⟩ : syracuseStep 689323 = 1033985) B1033985
theorem B2491813 : Blo 362758 2491813 := bstep (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) B467215
theorem B689627 : Blo 362758 689627 := bstep (se 1 (by rfl) ⟨517220, by rfl⟩ : syracuseStep 689627 = 1034441) B1034441
theorem B1181147 : Blo 362758 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B820745 : Blo 362758 820745 := bstep (se 2 (by rfl) ⟨307779, by rfl⟩ : syracuseStep 820745 = 615559) B615559
theorem B1377931 : Blo 362758 1377931 := bstep (se 1 (by rfl) ⟨1033448, by rfl⟩ : syracuseStep 1377931 = 2066897) B2066897
theorem B919289 : Blo 362758 919289 := bstep (se 2 (by rfl) ⟨344733, by rfl⟩ : syracuseStep 919289 = 689467) B689467
theorem B6752089 : Blo 362758 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B821087 : Blo 362758 821087 := bstep (se 1 (by rfl) ⟨615815, by rfl⟩ : syracuseStep 821087 = 1231631) B1231631
theorem B11175833 : Blo 362758 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B952225 : Blo 362758 952225 := bstep (se 2 (by rfl) ⟨357084, by rfl⟩ : syracuseStep 952225 = 714169) B714169
theorem B15075233 : Blo 362758 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B919471 : Blo 362758 919471 := bstep (se 1 (by rfl) ⟨689603, by rfl⟩ : syracuseStep 919471 = 1379207) B1379207
theorem B1378235 : Blo 362758 1378235 := bstep (se 1 (by rfl) ⟨1033676, by rfl⟩ : syracuseStep 1378235 = 2067353) B2067353
theorem B821267 : Blo 362758 821267 := bstep (se 1 (by rfl) ⟨615950, by rfl⟩ : syracuseStep 821267 = 1231901) B1231901
theorem B1607795 : Blo 362758 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B4655393 : Blo 362758 4655393 := bstep (se 2 (by rfl) ⟨1745772, by rfl⟩ : syracuseStep 4655393 = 3491545) B3491545
theorem B362791 : Blo 362758 362791 := bstep (se 1 (by rfl) ⟨272093, by rfl⟩ : syracuseStep 362791 = 544187) B544187
theorem B362831 : Blo 362758 362831 := bstep (se 1 (by rfl) ⟨272123, by rfl⟩ : syracuseStep 362831 = 544247) B544247
theorem B362847 : Blo 362758 362847 := bstep (se 1 (by rfl) ⟨272135, by rfl⟩ : syracuseStep 362847 = 544271) B544271
theorem B821609 : Blo 362758 821609 := bstep (se 2 (by rfl) ⟨308103, by rfl⟩ : syracuseStep 821609 = 616207) B616207
theorem B362875 : Blo 362758 362875 := bstep (se 1 (by rfl) ⟨272156, by rfl⟩ : syracuseStep 362875 = 544313) B544313
theorem B919937 : Blo 362758 919937 := bstep (se 2 (by rfl) ⟨344976, by rfl⟩ : syracuseStep 919937 = 689953) B689953
theorem B2623877 : Blo 362758 2623877 := bstep (se 4 (by rfl) ⟨245988, by rfl⟩ : syracuseStep 2623877 = 491977) B491977
theorem B362927 : Blo 362758 362927 := bstep (se 1 (by rfl) ⟨272195, by rfl⟩ : syracuseStep 362927 = 544391) B544391
theorem B362951 : Blo 362758 362951 := bstep (se 1 (by rfl) ⟨272213, by rfl⟩ : syracuseStep 362951 = 544427) B544427
theorem B362971 : Blo 362758 362971 := bstep (se 1 (by rfl) ⟨272228, by rfl⟩ : syracuseStep 362971 = 544457) B544457
theorem B690697 : Blo 362758 690697 := bstep (se 2 (by rfl) ⟨259011, by rfl⟩ : syracuseStep 690697 = 518023) B518023
theorem B363047 : Blo 362758 363047 := bstep (se 1 (by rfl) ⟨272285, by rfl⟩ : syracuseStep 363047 = 544571) B544571
theorem B363087 : Blo 362758 363087 := bstep (se 1 (by rfl) ⟨272315, by rfl⟩ : syracuseStep 363087 = 544631) B544631
theorem B363103 : Blo 362758 363103 := bstep (se 1 (by rfl) ⟨272327, by rfl⟩ : syracuseStep 363103 = 544655) B544655
theorem B363131 : Blo 362758 363131 := bstep (se 1 (by rfl) ⟨272348, by rfl⟩ : syracuseStep 363131 = 544697) B544697
theorem B2067079 : Blo 362758 2067079 := bstep (se 1 (by rfl) ⟨1550309, by rfl⟩ : syracuseStep 2067079 = 3100619) B3100619
theorem B3115655 : Blo 362758 3115655 := bstep (se 1 (by rfl) ⟨2336741, by rfl⟩ : syracuseStep 3115655 = 4673483) B4673483
theorem B363183 : Blo 362758 363183 := bstep (se 1 (by rfl) ⟨272387, by rfl⟩ : syracuseStep 363183 = 544775) B544775
theorem B363207 : Blo 362758 363207 := bstep (se 1 (by rfl) ⟨272405, by rfl⟩ : syracuseStep 363207 = 544811) B544811
theorem B363227 : Blo 362758 363227 := bstep (se 1 (by rfl) ⟨272420, by rfl⟩ : syracuseStep 363227 = 544841) B544841
theorem B363303 : Blo 362758 363303 := bstep (se 1 (by rfl) ⟨272477, by rfl⟩ : syracuseStep 363303 = 544955) B544955
theorem B920393 : Blo 362758 920393 := bstep (se 2 (by rfl) ⟨345147, by rfl⟩ : syracuseStep 920393 = 690295) B690295
theorem B363343 : Blo 362758 363343 := bstep (se 1 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 363343 = 545015) B545015
theorem B363359 : Blo 362758 363359 := bstep (se 1 (by rfl) ⟨272519, by rfl⟩ : syracuseStep 363359 = 545039) B545039
theorem B363387 : Blo 362758 363387 := bstep (se 1 (by rfl) ⟨272540, by rfl⟩ : syracuseStep 363387 = 545081) B545081
theorem B3345299 : Blo 362758 3345299 := bstep (se 1 (by rfl) ⟨2508974, by rfl⟩ : syracuseStep 3345299 = 5017949) B5017949
theorem B363439 : Blo 362758 363439 := bstep (se 1 (by rfl) ⟨272579, by rfl⟩ : syracuseStep 363439 = 545159) B545159
theorem B658363 : Blo 362758 658363 := bstep (se 1 (by rfl) ⟨493772, by rfl⟩ : syracuseStep 658363 = 987545) B987545
theorem B822203 : Blo 362758 822203 := bstep (se 1 (by rfl) ⟨616652, by rfl⟩ : syracuseStep 822203 = 1233305) B1233305
theorem B363463 : Blo 362758 363463 := bstep (se 1 (by rfl) ⟨272597, by rfl⟩ : syracuseStep 363463 = 545195) B545195
theorem B363483 : Blo 362758 363483 := bstep (se 1 (by rfl) ⟨272612, by rfl⟩ : syracuseStep 363483 = 545225) B545225
theorem B363559 : Blo 362758 363559 := bstep (se 1 (by rfl) ⟨272669, by rfl⟩ : syracuseStep 363559 = 545339) B545339
theorem B822329 : Blo 362758 822329 := bstep (se 2 (by rfl) ⟨308373, by rfl⟩ : syracuseStep 822329 = 616747) B616747
theorem B363599 : Blo 362758 363599 := bstep (se 1 (by rfl) ⟨272699, by rfl⟩ : syracuseStep 363599 = 545399) B545399
theorem B363615 : Blo 362758 363615 := bstep (se 1 (by rfl) ⟨272711, by rfl⟩ : syracuseStep 363615 = 545423) B545423
theorem B363643 : Blo 362758 363643 := bstep (se 1 (by rfl) ⟨272732, by rfl⟩ : syracuseStep 363643 = 545465) B545465
theorem B986269 : Blo 362758 986269 := bstep (se 3 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 986269 = 369851) B369851
theorem B920747 : Blo 362758 920747 := bstep (se 1 (by rfl) ⟨690560, by rfl⟩ : syracuseStep 920747 = 1381121) B1381121
theorem B363695 : Blo 362758 363695 := bstep (se 1 (by rfl) ⟨272771, by rfl⟩ : syracuseStep 363695 = 545543) B545543
theorem B363719 : Blo 362758 363719 := bstep (se 1 (by rfl) ⟨272789, by rfl⟩ : syracuseStep 363719 = 545579) B545579
theorem B691411 : Blo 362758 691411 := bstep (se 1 (by rfl) ⟨518558, by rfl⟩ : syracuseStep 691411 = 1037117) B1037117
theorem B363739 : Blo 362758 363739 := bstep (se 1 (by rfl) ⟨272804, by rfl⟩ : syracuseStep 363739 = 545609) B545609
theorem B363815 : Blo 362758 363815 := bstep (se 1 (by rfl) ⟨272861, by rfl⟩ : syracuseStep 363815 = 545723) B545723
theorem B363855 : Blo 362758 363855 := bstep (se 1 (by rfl) ⟨272891, by rfl⟩ : syracuseStep 363855 = 545783) B545783
theorem B363871 : Blo 362758 363871 := bstep (se 1 (by rfl) ⟨272903, by rfl⟩ : syracuseStep 363871 = 545807) B545807
theorem B363899 : Blo 362758 363899 := bstep (se 1 (by rfl) ⟨272924, by rfl⟩ : syracuseStep 363899 = 545849) B545849
theorem B822671 : Blo 362758 822671 := bstep (se 1 (by rfl) ⟨617003, by rfl⟩ : syracuseStep 822671 = 1234007) B1234007
theorem B363951 : Blo 362758 363951 := bstep (se 1 (by rfl) ⟨272963, by rfl⟩ : syracuseStep 363951 = 545927) B545927
theorem B363975 : Blo 362758 363975 := bstep (se 1 (by rfl) ⟨272981, by rfl⟩ : syracuseStep 363975 = 545963) B545963
theorem B1838537 : Blo 362758 1838537 := bstep (se 2 (by rfl) ⟨689451, by rfl⟩ : syracuseStep 1838537 = 1378903) B1378903
theorem B363995 : Blo 362758 363995 := bstep (se 1 (by rfl) ⟨272996, by rfl⟩ : syracuseStep 363995 = 545993) B545993
theorem B364071 : Blo 362758 364071 := bstep (se 1 (by rfl) ⟨273053, by rfl⟩ : syracuseStep 364071 = 546107) B546107
theorem B364111 : Blo 362758 364111 := bstep (se 1 (by rfl) ⟨273083, by rfl⟩ : syracuseStep 364111 = 546167) B546167
theorem B364127 : Blo 362758 364127 := bstep (se 1 (by rfl) ⟨273095, by rfl⟩ : syracuseStep 364127 = 546191) B546191
theorem B364155 : Blo 362758 364155 := bstep (se 1 (by rfl) ⟨273116, by rfl⟩ : syracuseStep 364155 = 546233) B546233
theorem B364207 : Blo 362758 364207 := bstep (se 1 (by rfl) ⟨273155, by rfl⟩ : syracuseStep 364207 = 546311) B546311
theorem B364231 : Blo 362758 364231 := bstep (se 1 (by rfl) ⟨273173, by rfl⟩ : syracuseStep 364231 = 546347) B546347
theorem B822995 : Blo 362758 822995 := bstep (se 1 (by rfl) ⟨617246, by rfl⟩ : syracuseStep 822995 = 1234493) B1234493
theorem B1969879 : Blo 362758 1969879 := bstep (se 1 (by rfl) ⟨1477409, by rfl⟩ : syracuseStep 1969879 = 2954819) B2954819
theorem B364251 : Blo 362758 364251 := bstep (se 1 (by rfl) ⟨273188, by rfl⟩ : syracuseStep 364251 = 546377) B546377
theorem B364327 : Blo 362758 364327 := bstep (se 1 (by rfl) ⟨273245, by rfl⟩ : syracuseStep 364327 = 546491) B546491
theorem B2953027 : Blo 362758 2953027 := bstep (se 1 (by rfl) ⟨2214770, by rfl⟩ : syracuseStep 2953027 = 4429541) B4429541
theorem B364367 : Blo 362758 364367 := bstep (se 1 (by rfl) ⟨273275, by rfl⟩ : syracuseStep 364367 = 546551) B546551
theorem B364383 : Blo 362758 364383 := bstep (se 1 (by rfl) ⟨273287, by rfl⟩ : syracuseStep 364383 = 546575) B546575
theorem B364411 : Blo 362758 364411 := bstep (se 1 (by rfl) ⟨273308, by rfl⟩ : syracuseStep 364411 = 546617) B546617
theorem B364463 : Blo 362758 364463 := bstep (se 1 (by rfl) ⟨273347, by rfl⟩ : syracuseStep 364463 = 546695) B546695
theorem B921527 : Blo 362758 921527 := bstep (se 1 (by rfl) ⟨691145, by rfl⟩ : syracuseStep 921527 = 1382291) B1382291
theorem B692155 : Blo 362758 692155 := bstep (se 1 (by rfl) ⟨519116, by rfl⟩ : syracuseStep 692155 = 1038233) B1038233
theorem B364487 : Blo 362758 364487 := bstep (se 1 (by rfl) ⟨273365, by rfl⟩ : syracuseStep 364487 = 546731) B546731
theorem B364507 : Blo 362758 364507 := bstep (se 1 (by rfl) ⟨273380, by rfl⟩ : syracuseStep 364507 = 546761) B546761
theorem B364583 : Blo 362758 364583 := bstep (se 1 (by rfl) ⟨273437, by rfl⟩ : syracuseStep 364583 = 546875) B546875
theorem B2068537 : Blo 362758 2068537 := bstep (se 2 (by rfl) ⟨775701, by rfl⟩ : syracuseStep 2068537 = 1551403) B1551403
theorem B364623 : Blo 362758 364623 := bstep (se 1 (by rfl) ⟨273467, by rfl⟩ : syracuseStep 364623 = 546935) B546935
theorem B1839185 : Blo 362758 1839185 := bstep (se 2 (by rfl) ⟨689694, by rfl⟩ : syracuseStep 1839185 = 1379389) B1379389
theorem B364639 : Blo 362758 364639 := bstep (se 1 (by rfl) ⟨273479, by rfl⟩ : syracuseStep 364639 = 546959) B546959
theorem B364667 : Blo 362758 364667 := bstep (se 1 (by rfl) ⟨273500, by rfl⟩ : syracuseStep 364667 = 547001) B547001
theorem B364719 : Blo 362758 364719 := bstep (se 1 (by rfl) ⟨273539, by rfl⟩ : syracuseStep 364719 = 547079) B547079
theorem B364743 : Blo 362758 364743 := bstep (se 1 (by rfl) ⟨273557, by rfl⟩ : syracuseStep 364743 = 547115) B547115
theorem B364763 : Blo 362758 364763 := bstep (se 1 (by rfl) ⟨273572, by rfl⟩ : syracuseStep 364763 = 547145) B547145
theorem B364839 : Blo 362758 364839 := bstep (se 1 (by rfl) ⟨273629, by rfl⟩ : syracuseStep 364839 = 547259) B547259
theorem B2101565 : Blo 362758 2101565 := bstep (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) B788087
theorem B364879 : Blo 362758 364879 := bstep (se 1 (by rfl) ⟨273659, by rfl⟩ : syracuseStep 364879 = 547319) B547319
theorem B364895 : Blo 362758 364895 := bstep (se 1 (by rfl) ⟨273671, by rfl⟩ : syracuseStep 364895 = 547343) B547343
theorem B364923 : Blo 362758 364923 := bstep (se 1 (by rfl) ⟨273692, by rfl⟩ : syracuseStep 364923 = 547385) B547385
theorem B692641 : Blo 362758 692641 := bstep (se 2 (by rfl) ⟨259740, by rfl⟩ : syracuseStep 692641 = 519481) B519481
theorem B364975 : Blo 362758 364975 := bstep (se 1 (by rfl) ⟨273731, by rfl⟩ : syracuseStep 364975 = 547463) B547463
theorem B364999 : Blo 362758 364999 := bstep (se 1 (by rfl) ⟨273749, by rfl⟩ : syracuseStep 364999 = 547499) B547499
theorem B365019 : Blo 362758 365019 := bstep (se 1 (by rfl) ⟨273764, by rfl⟩ : syracuseStep 365019 = 547529) B547529
theorem B331321873 : Blo 362758 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B5935639 : Blo 362758 5935639 := bstep (se 1 (by rfl) ⟨4451729, by rfl⟩ : syracuseStep 5935639 = 8903459) B8903459
theorem B365095 : Blo 362758 365095 := bstep (se 1 (by rfl) ⟨273821, by rfl⟩ : syracuseStep 365095 = 547643) B547643
theorem B365135 : Blo 362758 365135 := bstep (se 1 (by rfl) ⟨273851, by rfl⟩ : syracuseStep 365135 = 547703) B547703
theorem B365151 : Blo 362758 365151 := bstep (se 1 (by rfl) ⟨273863, by rfl⟩ : syracuseStep 365151 = 547727) B547727
theorem B365179 : Blo 362758 365179 := bstep (se 1 (by rfl) ⟨273884, by rfl⟩ : syracuseStep 365179 = 547769) B547769
theorem B823931 : Blo 362758 823931 := bstep (se 1 (by rfl) ⟨617948, by rfl⟩ : syracuseStep 823931 = 1235897) B1235897
theorem B889483 : Blo 362758 889483 := bstep (se 1 (by rfl) ⟨667112, by rfl⟩ : syracuseStep 889483 = 1334225) B1334225
theorem B365231 : Blo 362758 365231 := bstep (se 1 (by rfl) ⟨273923, by rfl⟩ : syracuseStep 365231 = 547847) B547847
theorem B365255 : Blo 362758 365255 := bstep (se 1 (by rfl) ⟨273941, by rfl⟩ : syracuseStep 365255 = 547883) B547883
theorem B9900755 : Blo 362758 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B365275 : Blo 362758 365275 := bstep (se 1 (by rfl) ⟨273956, by rfl⟩ : syracuseStep 365275 = 547913) B547913
theorem B824057 : Blo 362758 824057 := bstep (se 2 (by rfl) ⟨309021, by rfl⟩ : syracuseStep 824057 = 618043) B618043
theorem B365351 : Blo 362758 365351 := bstep (se 1 (by rfl) ⟨274013, by rfl⟩ : syracuseStep 365351 = 548027) B548027
theorem B365391 : Blo 362758 365391 := bstep (se 1 (by rfl) ⟨274043, by rfl⟩ : syracuseStep 365391 = 548087) B548087
theorem B365407 : Blo 362758 365407 := bstep (se 1 (by rfl) ⟨274055, by rfl⟩ : syracuseStep 365407 = 548111) B548111
theorem B365435 : Blo 362758 365435 := bstep (se 1 (by rfl) ⟨274076, by rfl⟩ : syracuseStep 365435 = 548153) B548153
theorem B922529 : Blo 362758 922529 := bstep (se 2 (by rfl) ⟨345948, by rfl⟩ : syracuseStep 922529 = 691897) B691897
theorem B365487 : Blo 362758 365487 := bstep (se 1 (by rfl) ⟨274115, by rfl⟩ : syracuseStep 365487 = 548231) B548231
theorem B365511 : Blo 362758 365511 := bstep (se 1 (by rfl) ⟨274133, by rfl⟩ : syracuseStep 365511 = 548267) B548267
theorem B693211 : Blo 362758 693211 := bstep (se 1 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 693211 = 1039817) B1039817
theorem B365531 : Blo 362758 365531 := bstep (se 1 (by rfl) ⟨274148, by rfl⟩ : syracuseStep 365531 = 548297) B548297
theorem B7115777 : Blo 362758 7115777 := bstep (se 2 (by rfl) ⟨2668416, by rfl⟩ : syracuseStep 7115777 = 5336833) B5336833
theorem B824327 : Blo 362758 824327 := bstep (se 1 (by rfl) ⟨618245, by rfl⟩ : syracuseStep 824327 = 1236491) B1236491
theorem B365607 : Blo 362758 365607 := bstep (se 1 (by rfl) ⟨274205, by rfl⟩ : syracuseStep 365607 = 548411) B548411
theorem B365647 : Blo 362758 365647 := bstep (se 1 (by rfl) ⟨274235, by rfl⟩ : syracuseStep 365647 = 548471) B548471
theorem B824399 : Blo 362758 824399 := bstep (se 1 (by rfl) ⟨618299, by rfl⟩ : syracuseStep 824399 = 1236599) B1236599
theorem B365663 : Blo 362758 365663 := bstep (se 1 (by rfl) ⟨274247, by rfl⟩ : syracuseStep 365663 = 548495) B548495
theorem B365691 : Blo 362758 365691 := bstep (se 1 (by rfl) ⟨274268, by rfl⟩ : syracuseStep 365691 = 548537) B548537
theorem B365743 : Blo 362758 365743 := bstep (se 1 (by rfl) ⟨274307, by rfl⟩ : syracuseStep 365743 = 548615) B548615
theorem B365767 : Blo 362758 365767 := bstep (se 1 (by rfl) ⟨274325, by rfl⟩ : syracuseStep 365767 = 548651) B548651
theorem B365787 : Blo 362758 365787 := bstep (se 1 (by rfl) ⟨274340, by rfl⟩ : syracuseStep 365787 = 548681) B548681
theorem B660727 : Blo 362758 660727 := bstep (se 1 (by rfl) ⟨495545, by rfl⟩ : syracuseStep 660727 = 991091) B991091
theorem B365863 : Blo 362758 365863 := bstep (se 1 (by rfl) ⟨274397, by rfl⟩ : syracuseStep 365863 = 548795) B548795
theorem B365903 : Blo 362758 365903 := bstep (se 1 (by rfl) ⟨274427, by rfl⟩ : syracuseStep 365903 = 548855) B548855
theorem B365919 : Blo 362758 365919 := bstep (se 1 (by rfl) ⟨274439, by rfl⟩ : syracuseStep 365919 = 548879) B548879
theorem B922985 : Blo 362758 922985 := bstep (se 2 (by rfl) ⟨346119, by rfl⟩ : syracuseStep 922985 = 692239) B692239
theorem B365947 : Blo 362758 365947 := bstep (se 1 (by rfl) ⟨274460, by rfl⟩ : syracuseStep 365947 = 548921) B548921
theorem B365999 : Blo 362758 365999 := bstep (se 1 (by rfl) ⟨274499, by rfl⟩ : syracuseStep 365999 = 548999) B548999
theorem B366023 : Blo 362758 366023 := bstep (se 1 (by rfl) ⟨274517, by rfl⟩ : syracuseStep 366023 = 549035) B549035
theorem B366043 : Blo 362758 366043 := bstep (se 1 (by rfl) ⟨274532, by rfl⟩ : syracuseStep 366043 = 549065) B549065
theorem B824795 : Blo 362758 824795 := bstep (se 1 (by rfl) ⟨618596, by rfl⟩ : syracuseStep 824795 = 1237193) B1237193
theorem B366119 : Blo 362758 366119 := bstep (se 1 (by rfl) ⟨274589, by rfl⟩ : syracuseStep 366119 = 549179) B549179
theorem B366159 : Blo 362758 366159 := bstep (se 1 (by rfl) ⟨274619, by rfl⟩ : syracuseStep 366159 = 549239) B549239
theorem B366175 : Blo 362758 366175 := bstep (se 1 (by rfl) ⟨274631, by rfl⟩ : syracuseStep 366175 = 549263) B549263
theorem B366203 : Blo 362758 366203 := bstep (se 1 (by rfl) ⟨274652, by rfl⟩ : syracuseStep 366203 = 549305) B549305
theorem B366255 : Blo 362758 366255 := bstep (se 1 (by rfl) ⟨274691, by rfl⟩ : syracuseStep 366255 = 549383) B549383
theorem B366279 : Blo 362758 366279 := bstep (se 1 (by rfl) ⟨274709, by rfl⟩ : syracuseStep 366279 = 549419) B549419
theorem B366299 : Blo 362758 366299 := bstep (se 1 (by rfl) ⟨274724, by rfl⟩ : syracuseStep 366299 = 549449) B549449
theorem B1251065 : Blo 362758 1251065 := bstep (se 2 (by rfl) ⟨469149, by rfl⟩ : syracuseStep 1251065 = 938299) B938299
theorem B366375 : Blo 362758 366375 := bstep (se 1 (by rfl) ⟨274781, by rfl⟩ : syracuseStep 366375 = 549563) B549563
theorem B366415 : Blo 362758 366415 := bstep (se 1 (by rfl) ⟨274811, by rfl⟩ : syracuseStep 366415 = 549623) B549623
theorem B366431 : Blo 362758 366431 := bstep (se 1 (by rfl) ⟨274823, by rfl⟩ : syracuseStep 366431 = 549647) B549647
theorem B366459 : Blo 362758 366459 := bstep (se 1 (by rfl) ⟨274844, by rfl⟩ : syracuseStep 366459 = 549689) B549689
theorem B2758535 : Blo 362758 2758535 := bstep (se 1 (by rfl) ⟨2068901, by rfl⟩ : syracuseStep 2758535 = 4137803) B4137803
theorem B1382305 : Blo 362758 1382305 := bstep (se 2 (by rfl) ⟨518364, by rfl⟩ : syracuseStep 1382305 = 1036729) B1036729
theorem B366511 : Blo 362758 366511 := bstep (se 1 (by rfl) ⟨274883, by rfl⟩ : syracuseStep 366511 = 549767) B549767
theorem B366535 : Blo 362758 366535 := bstep (se 1 (by rfl) ⟨274901, by rfl⟩ : syracuseStep 366535 = 549803) B549803
theorem B366555 : Blo 362758 366555 := bstep (se 1 (by rfl) ⟨274916, by rfl⟩ : syracuseStep 366555 = 549833) B549833
theorem B366631 : Blo 362758 366631 := bstep (se 1 (by rfl) ⟨274973, by rfl⟩ : syracuseStep 366631 = 549947) B549947
theorem B366671 : Blo 362758 366671 := bstep (se 1 (by rfl) ⟨275003, by rfl⟩ : syracuseStep 366671 = 550007) B550007
theorem B366687 : Blo 362758 366687 := bstep (se 1 (by rfl) ⟨275015, by rfl⟩ : syracuseStep 366687 = 550031) B550031
theorem B366715 : Blo 362758 366715 := bstep (se 1 (by rfl) ⟨275036, by rfl⟩ : syracuseStep 366715 = 550073) B550073
theorem B924169 : Blo 362758 924169 := bstep (se 2 (by rfl) ⟨346563, by rfl⟩ : syracuseStep 924169 = 693127) B693127
theorem B1383263 : Blo 362758 1383263 := bstep (se 1 (by rfl) ⟨1037447, by rfl⟩ : syracuseStep 1383263 = 2074895) B2074895
theorem B1383277 : Blo 362758 1383277 := bstep (se 3 (by rfl) ⟨259364, by rfl⟩ : syracuseStep 1383277 = 518729) B518729
theorem B3611621 : Blo 362758 3611621 := bstep (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) B677179
theorem B1317907 : Blo 362758 1317907 := bstep (se 1 (by rfl) ⟨988430, by rfl⟩ : syracuseStep 1317907 = 1976861) B1976861
theorem B695375 : Blo 362758 695375 := bstep (se 1 (by rfl) ⟨521531, by rfl⟩ : syracuseStep 695375 = 1043063) B1043063
theorem B1383581 : Blo 362758 1383581 := bstep (se 3 (by rfl) ⟨259421, by rfl⟩ : syracuseStep 1383581 = 518843) B518843
theorem B3513689 : Blo 362758 3513689 := bstep (se 2 (by rfl) ⟨1317633, by rfl⟩ : syracuseStep 3513689 = 2635267) B2635267
theorem B3513725 : Blo 362758 3513725 := bstep (se 3 (by rfl) ⟨658823, by rfl⟩ : syracuseStep 3513725 = 1317647) B1317647
theorem B1384235 : Blo 362758 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B925627 : Blo 362758 925627 := bstep (se 1 (by rfl) ⟨694220, by rfl⟩ : syracuseStep 925627 = 1388441) B1388441
theorem B1253693 : Blo 362758 1253693 := bstep (se 3 (by rfl) ⟨235067, by rfl⟩ : syracuseStep 1253693 = 470135) B470135
theorem B1843721 : Blo 362758 1843721 := bstep (se 2 (by rfl) ⟨691395, by rfl⟩ : syracuseStep 1843721 = 1382791) B1382791
theorem B1319753 : Blo 362758 1319753 := bstep (se 2 (by rfl) ⟨494907, by rfl⟩ : syracuseStep 1319753 = 989815) B989815
theorem B467887 : Blo 362758 467887 := bstep (se 1 (by rfl) ⟨350915, by rfl⟩ : syracuseStep 467887 = 701831) B701831
theorem B664615 : Blo 362758 664615 := bstep (se 1 (by rfl) ⟨498461, by rfl⟩ : syracuseStep 664615 = 996923) B996923
theorem B1386193 : Blo 362758 1386193 := bstep (se 2 (by rfl) ⟨519822, by rfl⟩ : syracuseStep 1386193 = 1039645) B1039645
theorem B665417 : Blo 362758 665417 := bstep (se 2 (by rfl) ⟨249531, by rfl⟩ : syracuseStep 665417 = 499063) B499063
theorem B1845179 : Blo 362758 1845179 := bstep (se 1 (by rfl) ⟨1383884, by rfl⟩ : syracuseStep 1845179 = 2767769) B2767769
theorem B1386497 : Blo 362758 1386497 := bstep (se 2 (by rfl) ⟨519936, by rfl⟩ : syracuseStep 1386497 = 1039873) B1039873
theorem B2762909 : Blo 362758 2762909 := bstep (se 3 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 2762909 = 1036091) B1036091
theorem B2959517 : Blo 362758 2959517 := bstep (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) B1109819
theorem B1386953 : Blo 362758 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B928219 : Blo 362758 928219 := bstep (se 1 (by rfl) ⟨696164, by rfl⟩ : syracuseStep 928219 = 1392329) B1392329
theorem B1387439 : Blo 362758 1387439 := bstep (se 1 (by rfl) ⟨1040579, by rfl⟩ : syracuseStep 1387439 = 2081159) B2081159
theorem B1649591 : Blo 362758 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B1616915 : Blo 362758 1616915 := bstep (se 1 (by rfl) ⟨1212686, by rfl⟩ : syracuseStep 1616915 = 2425373) B2425373
theorem B9972823 : Blo 362758 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B1846475 : Blo 362758 1846475 := bstep (se 1 (by rfl) ⟨1384856, by rfl⟩ : syracuseStep 1846475 = 2769713) B2769713
theorem B437611 : Blo 362758 437611 := bstep (se 1 (by rfl) ⟨328208, by rfl⟩ : syracuseStep 437611 = 656417) B656417
theorem B3321431 : Blo 362758 3321431 := bstep (se 1 (by rfl) ⟨2491073, by rfl⟩ : syracuseStep 3321431 = 4982147) B4982147
theorem B1552223 : Blo 362758 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B1224719 : Blo 362758 1224719 := bstep (se 1 (by rfl) ⟨918539, by rfl⟩ : syracuseStep 1224719 = 1837079) B1837079
theorem B1388623 : Blo 362758 1388623 := bstep (se 1 (by rfl) ⟨1041467, by rfl⟩ : syracuseStep 1388623 = 2082935) B2082935
theorem B3944983 : Blo 362758 3944983 := bstep (se 1 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 3944983 = 5917475) B5917475
theorem B1389095 : Blo 362758 1389095 := bstep (se 1 (by rfl) ⟨1041821, by rfl⟩ : syracuseStep 1389095 = 2083643) B2083643
theorem B1225313 : Blo 362758 1225313 := bstep (se 2 (by rfl) ⟨459492, by rfl⟩ : syracuseStep 1225313 = 918985) B918985
theorem B2765825 : Blo 362758 2765825 := bstep (se 2 (by rfl) ⟨1037184, by rfl⟩ : syracuseStep 2765825 = 2074369) B2074369
theorem B2799011 : Blo 362758 2799011 := bstep (se 1 (by rfl) ⟨2099258, by rfl⟩ : syracuseStep 2799011 = 4198517) B4198517
theorem B1390067 : Blo 362758 1390067 := bstep (se 1 (by rfl) ⟨1042550, by rfl⟩ : syracuseStep 1390067 = 2085101) B2085101
theorem B1357511 : Blo 362758 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B4175711 : Blo 362758 4175711 := bstep (se 1 (by rfl) ⟨3131783, by rfl⟩ : syracuseStep 4175711 = 6263567) B6263567
theorem B1226771 : Blo 362758 1226771 := bstep (se 1 (by rfl) ⟨920078, by rfl⟩ : syracuseStep 1226771 = 1840157) B1840157
theorem B1554547 : Blo 362758 1554547 := bstep (se 1 (by rfl) ⟨1165910, by rfl⟩ : syracuseStep 1554547 = 2331821) B2331821
theorem B1227095 : Blo 362758 1227095 := bstep (se 1 (by rfl) ⟨920321, by rfl⟩ : syracuseStep 1227095 = 1840643) B1840643
theorem B702985 : Blo 362758 702985 := bstep (se 2 (by rfl) ⟨263619, by rfl⟩ : syracuseStep 702985 = 527239) B527239
theorem B2407241 : Blo 362758 2407241 := bstep (se 2 (by rfl) ⟨902715, by rfl⟩ : syracuseStep 2407241 = 1805431) B1805431
theorem B408415 : Blo 362758 408415 := bstep (se 1 (by rfl) ⟨306311, by rfl⟩ : syracuseStep 408415 = 612623) B612623
theorem B408775 : Blo 362758 408775 := bstep (se 1 (by rfl) ⟨306581, by rfl⟩ : syracuseStep 408775 = 613163) B613163
theorem B1228175 : Blo 362758 1228175 := bstep (se 1 (by rfl) ⟨921131, by rfl⟩ : syracuseStep 1228175 = 1842263) B1842263
theorem B2080201 : Blo 362758 2080201 := bstep (se 2 (by rfl) ⟨780075, by rfl⟩ : syracuseStep 2080201 = 1560151) B1560151
theorem B9453095 : Blo 362758 9453095 := bstep (se 1 (by rfl) ⟨7089821, by rfl⟩ : syracuseStep 9453095 = 14179643) B14179643
theorem B22560295 : Blo 362758 22560295 := bstep (se 1 (by rfl) ⟨16920221, by rfl⟩ : syracuseStep 22560295 = 33840443) B33840443
theorem B1228499 : Blo 362758 1228499 := bstep (se 1 (by rfl) ⟨921374, by rfl⟩ : syracuseStep 1228499 = 1842749) B1842749
theorem B1752941 : Blo 362758 1752941 := bstep (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) B657353
theorem B1392641 : Blo 362758 1392641 := bstep (se 2 (by rfl) ⟨522240, by rfl⟩ : syracuseStep 1392641 = 1044481) B1044481
theorem B409639 : Blo 362758 409639 := bstep (se 1 (by rfl) ⟨307229, by rfl⟩ : syracuseStep 409639 = 614459) B614459
theorem B1851659 : Blo 362758 1851659 := bstep (se 1 (by rfl) ⟨1388744, by rfl⟩ : syracuseStep 1851659 = 2777489) B2777489
theorem B1229687 : Blo 362758 1229687 := bstep (se 1 (by rfl) ⟨922265, by rfl⟩ : syracuseStep 1229687 = 1844531) B1844531
theorem B1229903 : Blo 362758 1229903 := bstep (se 1 (by rfl) ⟨922427, by rfl⟩ : syracuseStep 1229903 = 1844855) B1844855
theorem B3130487 : Blo 362758 3130487 := bstep (se 1 (by rfl) ⟨2347865, by rfl⟩ : syracuseStep 3130487 = 4695731) B4695731
theorem B2770199 : Blo 362758 2770199 := bstep (se 1 (by rfl) ⟨2077649, by rfl⟩ : syracuseStep 2770199 = 4155299) B4155299
theorem B1230281 : Blo 362758 1230281 := bstep (se 2 (by rfl) ⟨461355, by rfl⟩ : syracuseStep 1230281 = 922711) B922711
theorem B411259 : Blo 362758 411259 := bstep (se 1 (by rfl) ⟨308444, by rfl⟩ : syracuseStep 411259 = 616889) B616889
theorem B1853117 : Blo 362758 1853117 := bstep (se 3 (by rfl) ⟨347459, by rfl⟩ : syracuseStep 1853117 = 694919) B694919
theorem B1230551 : Blo 362758 1230551 := bstep (se 1 (by rfl) ⟨922913, by rfl⟩ : syracuseStep 1230551 = 1845827) B1845827
theorem B2639675 : Blo 362758 2639675 := bstep (se 1 (by rfl) ⟨1979756, by rfl⟩ : syracuseStep 2639675 = 3959513) B3959513
theorem B1853279 : Blo 362758 1853279 := bstep (se 1 (by rfl) ⟨1389959, by rfl⟩ : syracuseStep 1853279 = 2779919) B2779919
theorem B1230767 : Blo 362758 1230767 := bstep (se 1 (by rfl) ⟨923075, by rfl⟩ : syracuseStep 1230767 = 1846151) B1846151
theorem B1034167 : Blo 362758 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B411727 : Blo 362758 411727 := bstep (se 1 (by rfl) ⟨308795, by rfl⟩ : syracuseStep 411727 = 617591) B617591
theorem B8866097 : Blo 362758 8866097 := bstep (se 2 (by rfl) ⟨3324786, by rfl⟩ : syracuseStep 8866097 = 6649573) B6649573
theorem B412123 : Blo 362758 412123 := bstep (se 1 (by rfl) ⟨309092, by rfl⟩ : syracuseStep 412123 = 618185) B618185
theorem B5884397 : Blo 362758 5884397 := bstep (se 3 (by rfl) ⟨1103324, by rfl⟩ : syracuseStep 5884397 = 2206649) B2206649
theorem B3983905 : Blo 362758 3983905 := bstep (se 2 (by rfl) ⟨1493964, by rfl⟩ : syracuseStep 3983905 = 2987929) B2987929
theorem B2771657 : Blo 362758 2771657 := bstep (se 2 (by rfl) ⟨1039371, by rfl⟩ : syracuseStep 2771657 = 2078743) B2078743
theorem B412591 : Blo 362758 412591 := bstep (se 1 (by rfl) ⟨309443, by rfl⟩ : syracuseStep 412591 = 618887) B618887
theorem B1035271 : Blo 362758 1035271 := bstep (se 1 (by rfl) ⟨776453, by rfl⟩ : syracuseStep 1035271 = 1552907) B1552907
theorem B1035625 : Blo 362758 1035625 := bstep (se 2 (by rfl) ⟨388359, by rfl⟩ : syracuseStep 1035625 = 776719) B776719
theorem B544175 : Blo 362758 544175 := bstep (se 1 (by rfl) ⟨408131, by rfl⟩ : syracuseStep 544175 = 816263) B816263
theorem B544265 : Blo 362758 544265 := bstep (se 2 (by rfl) ⟨204099, by rfl⟩ : syracuseStep 544265 = 408199) B408199
theorem B544295 : Blo 362758 544295 := bstep (se 1 (by rfl) ⟨408221, by rfl⟩ : syracuseStep 544295 = 816443) B816443
theorem B2346583 : Blo 362758 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B544379 : Blo 362758 544379 := bstep (se 1 (by rfl) ⟨408284, by rfl⟩ : syracuseStep 544379 = 816569) B816569
theorem B1035899 : Blo 362758 1035899 := bstep (se 1 (by rfl) ⟨776924, by rfl⟩ : syracuseStep 1035899 = 1553849) B1553849
theorem B1166987 : Blo 362758 1166987 := bstep (se 1 (by rfl) ⟨875240, by rfl⟩ : syracuseStep 1166987 = 1750481) B1750481
theorem B2117267 : Blo 362758 2117267 := bstep (se 1 (by rfl) ⟨1587950, by rfl⟩ : syracuseStep 2117267 = 3175901) B3175901
theorem B872147 : Blo 362758 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B544505 : Blo 362758 544505 := bstep (se 2 (by rfl) ⟨204189, by rfl⟩ : syracuseStep 544505 = 408379) B408379
theorem B544607 : Blo 362758 544607 := bstep (se 1 (by rfl) ⟨408455, by rfl⟩ : syracuseStep 544607 = 816911) B816911
theorem B544619 : Blo 362758 544619 := bstep (se 1 (by rfl) ⟨408464, by rfl⟩ : syracuseStep 544619 = 816929) B816929
theorem B544847 : Blo 362758 544847 := bstep (se 1 (by rfl) ⟨408635, by rfl⟩ : syracuseStep 544847 = 817271) B817271
theorem B1659037 : Blo 362758 1659037 := bstep (se 3 (by rfl) ⟨311069, by rfl⟩ : syracuseStep 1659037 = 622139) B622139
theorem B544967 : Blo 362758 544967 := bstep (se 1 (by rfl) ⟨408725, by rfl⟩ : syracuseStep 544967 = 817451) B817451
theorem B1233143 : Blo 362758 1233143 := bstep (se 1 (by rfl) ⟨924857, by rfl⟩ : syracuseStep 1233143 = 1849715) B1849715
theorem B545129 : Blo 362758 545129 := bstep (se 2 (by rfl) ⟨204423, by rfl⟩ : syracuseStep 545129 = 408847) B408847
theorem B545207 : Blo 362758 545207 := bstep (se 1 (by rfl) ⟨408905, by rfl⟩ : syracuseStep 545207 = 817811) B817811
theorem B545243 : Blo 362758 545243 := bstep (se 1 (by rfl) ⟨408932, by rfl⟩ : syracuseStep 545243 = 817865) B817865
theorem B1856033 : Blo 362758 1856033 := bstep (se 2 (by rfl) ⟨696012, by rfl⟩ : syracuseStep 1856033 = 1392025) B1392025
theorem B1233467 : Blo 362758 1233467 := bstep (se 1 (by rfl) ⟨925100, by rfl⟩ : syracuseStep 1233467 = 1850201) B1850201
theorem B10769165 : Blo 362758 10769165 := bstep (se 3 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 10769165 = 4038437) B4038437
theorem B1332035 : Blo 362758 1332035 := bstep (se 1 (by rfl) ⟨999026, by rfl⟩ : syracuseStep 1332035 = 1998053) B1998053
theorem B1233737 : Blo 362758 1233737 := bstep (se 2 (by rfl) ⟨462651, by rfl⟩ : syracuseStep 1233737 = 925303) B925303
theorem B12342131 : Blo 362758 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B545711 : Blo 362758 545711 := bstep (se 1 (by rfl) ⟨409283, by rfl⟩ : syracuseStep 545711 = 818567) B818567
theorem B1037231 : Blo 362758 1037231 := bstep (se 1 (by rfl) ⟨777923, by rfl⟩ : syracuseStep 1037231 = 1555847) B1555847
theorem B545801 : Blo 362758 545801 := bstep (se 2 (by rfl) ⟨204675, by rfl⟩ : syracuseStep 545801 = 409351) B409351
theorem B545831 : Blo 362758 545831 := bstep (se 1 (by rfl) ⟨409373, by rfl⟩ : syracuseStep 545831 = 818747) B818747
theorem B3494963 : Blo 362758 3494963 := bstep (se 1 (by rfl) ⟨2621222, by rfl⟩ : syracuseStep 3494963 = 5242445) B5242445
theorem B1758287 : Blo 362758 1758287 := bstep (se 1 (by rfl) ⟨1318715, by rfl⟩ : syracuseStep 1758287 = 2637431) B2637431
theorem B545915 : Blo 362758 545915 := bstep (se 1 (by rfl) ⟨409436, by rfl⟩ : syracuseStep 545915 = 818873) B818873
theorem B6640811 : Blo 362758 6640811 := bstep (se 1 (by rfl) ⟨4980608, by rfl⟩ : syracuseStep 6640811 = 9961217) B9961217
theorem B546041 : Blo 362758 546041 := bstep (se 2 (by rfl) ⟨204765, by rfl⟩ : syracuseStep 546041 = 409531) B409531
theorem B546143 : Blo 362758 546143 := bstep (se 1 (by rfl) ⟨409607, by rfl⟩ : syracuseStep 546143 = 819215) B819215
theorem B546155 : Blo 362758 546155 := bstep (se 1 (by rfl) ⟨409616, by rfl⟩ : syracuseStep 546155 = 819233) B819233
theorem B1168769 : Blo 362758 1168769 := bstep (se 2 (by rfl) ⟨438288, by rfl⟩ : syracuseStep 1168769 = 876577) B876577
theorem B546383 : Blo 362758 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B546503 : Blo 362758 546503 := bstep (se 1 (by rfl) ⟨409877, by rfl⟩ : syracuseStep 546503 = 819755) B819755
theorem B1758941 : Blo 362758 1758941 := bstep (se 3 (by rfl) ⟨329801, by rfl⟩ : syracuseStep 1758941 = 659603) B659603
theorem B612191 : Blo 362758 612191 := bstep (se 1 (by rfl) ⟨459143, by rfl⟩ : syracuseStep 612191 = 918287) B918287
theorem B546665 : Blo 362758 546665 := bstep (se 2 (by rfl) ⟨204999, by rfl⟩ : syracuseStep 546665 = 409999) B409999
theorem B1038187 : Blo 362758 1038187 := bstep (se 1 (by rfl) ⟨778640, by rfl⟩ : syracuseStep 1038187 = 1557281) B1557281
theorem B546743 : Blo 362758 546743 := bstep (se 1 (by rfl) ⟨410057, by rfl⟩ : syracuseStep 546743 = 820115) B820115
theorem B1234871 : Blo 362758 1234871 := bstep (se 1 (by rfl) ⟨926153, by rfl⟩ : syracuseStep 1234871 = 1852307) B1852307
theorem B546779 : Blo 362758 546779 := bstep (se 1 (by rfl) ⟨410084, by rfl⟩ : syracuseStep 546779 = 820169) B820169
theorem B1169423 : Blo 362758 1169423 := bstep (se 1 (by rfl) ⟨877067, by rfl⟩ : syracuseStep 1169423 = 1754135) B1754135
theorem B1038415 : Blo 362758 1038415 := bstep (se 1 (by rfl) ⟨778811, by rfl⟩ : syracuseStep 1038415 = 1557623) B1557623
theorem B3496193 : Blo 362758 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B4741409 : Blo 362758 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B612751 : Blo 362758 612751 := bstep (se 1 (by rfl) ⟨459563, by rfl⟩ : syracuseStep 612751 = 919127) B919127
theorem B547247 : Blo 362758 547247 := bstep (se 1 (by rfl) ⟨410435, by rfl⟩ : syracuseStep 547247 = 820871) B820871
theorem B4446667 : Blo 362758 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B547337 : Blo 362758 547337 := bstep (se 2 (by rfl) ⟨205251, by rfl⟩ : syracuseStep 547337 = 410503) B410503
theorem B1235465 : Blo 362758 1235465 := bstep (se 2 (by rfl) ⟨463299, by rfl⟩ : syracuseStep 1235465 = 926599) B926599
theorem B547367 : Blo 362758 547367 := bstep (se 1 (by rfl) ⟨410525, by rfl⟩ : syracuseStep 547367 = 821051) B821051
theorem B547451 : Blo 362758 547451 := bstep (se 1 (by rfl) ⟨410588, by rfl⟩ : syracuseStep 547451 = 821177) B821177
theorem B547577 : Blo 362758 547577 := bstep (se 2 (by rfl) ⟨205341, by rfl⟩ : syracuseStep 547577 = 410683) B410683
theorem B5266205 : Blo 362758 5266205 := bstep (se 3 (by rfl) ⟨987413, by rfl⟩ : syracuseStep 5266205 = 1974827) B1974827
theorem B547679 : Blo 362758 547679 := bstep (se 1 (by rfl) ⟨410759, by rfl⟩ : syracuseStep 547679 = 821519) B821519
theorem B547691 : Blo 362758 547691 := bstep (se 1 (by rfl) ⟨410768, by rfl⟩ : syracuseStep 547691 = 821537) B821537
theorem B613433 : Blo 362758 613433 := bstep (se 2 (by rfl) ⟨230037, by rfl⟩ : syracuseStep 613433 = 460075) B460075
theorem B547919 : Blo 362758 547919 := bstep (se 1 (by rfl) ⟨410939, by rfl⟩ : syracuseStep 547919 = 821879) B821879
theorem B548039 : Blo 362758 548039 := bstep (se 1 (by rfl) ⟨411029, by rfl⟩ : syracuseStep 548039 = 822059) B822059
theorem B548201 : Blo 362758 548201 := bstep (se 2 (by rfl) ⟨205575, by rfl⟩ : syracuseStep 548201 = 411151) B411151
theorem B1236329 : Blo 362758 1236329 := bstep (se 2 (by rfl) ⟨463623, by rfl⟩ : syracuseStep 1236329 = 927247) B927247
theorem B48717233 : Blo 362758 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B548279 : Blo 362758 548279 := bstep (se 1 (by rfl) ⟨411209, by rfl⟩ : syracuseStep 548279 = 822419) B822419
theorem B548315 : Blo 362758 548315 := bstep (se 1 (by rfl) ⟨411236, by rfl⟩ : syracuseStep 548315 = 822473) B822473
theorem B3104243 : Blo 362758 3104243 := bstep (se 1 (by rfl) ⟨2328182, by rfl⟩ : syracuseStep 3104243 = 4656365) B4656365
theorem B614135 : Blo 362758 614135 := bstep (se 1 (by rfl) ⟨460601, by rfl⟩ : syracuseStep 614135 = 921203) B921203
theorem B876395 : Blo 362758 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B1564525 : Blo 362758 1564525 := bstep (se 3 (by rfl) ⟨293348, by rfl⟩ : syracuseStep 1564525 = 586697) B586697
theorem B548783 : Blo 362758 548783 := bstep (se 1 (by rfl) ⟨411587, by rfl⟩ : syracuseStep 548783 = 823175) B823175
theorem B1236923 : Blo 362758 1236923 := bstep (se 1 (by rfl) ⟨927692, by rfl⟩ : syracuseStep 1236923 = 1855385) B1855385
theorem B548873 : Blo 362758 548873 := bstep (se 2 (by rfl) ⟨205827, by rfl⟩ : syracuseStep 548873 = 411655) B411655
theorem B548903 : Blo 362758 548903 := bstep (se 1 (by rfl) ⟨411677, by rfl⟩ : syracuseStep 548903 = 823355) B823355
theorem B614479 : Blo 362758 614479 := bstep (se 1 (by rfl) ⟨460859, by rfl⟩ : syracuseStep 614479 = 921719) B921719
theorem B1794163 : Blo 362758 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B548987 : Blo 362758 548987 := bstep (se 1 (by rfl) ⟨411740, by rfl⟩ : syracuseStep 548987 = 823481) B823481
theorem B712951 : Blo 362758 712951 := bstep (se 1 (by rfl) ⟨534713, by rfl⟩ : syracuseStep 712951 = 1069427) B1069427
theorem B549113 : Blo 362758 549113 := bstep (se 2 (by rfl) ⟨205917, by rfl⟩ : syracuseStep 549113 = 411835) B411835
theorem B614729 : Blo 362758 614729 := bstep (se 2 (by rfl) ⟨230523, by rfl⟩ : syracuseStep 614729 = 461047) B461047
theorem B549215 : Blo 362758 549215 := bstep (se 1 (by rfl) ⟨411911, by rfl⟩ : syracuseStep 549215 = 823823) B823823
theorem B581995 : Blo 362758 581995 := bstep (se 1 (by rfl) ⟨436496, by rfl⟩ : syracuseStep 581995 = 872993) B872993
theorem B549227 : Blo 362758 549227 := bstep (se 1 (by rfl) ⟨411920, by rfl⟩ : syracuseStep 549227 = 823841) B823841
theorem B1040921 : Blo 362758 1040921 := bstep (se 2 (by rfl) ⟨390345, by rfl⟩ : syracuseStep 1040921 = 780691) B780691
theorem B549455 : Blo 362758 549455 := bstep (se 1 (by rfl) ⟨412091, by rfl⟩ : syracuseStep 549455 = 824183) B824183
theorem B11231885 : Blo 362758 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B549575 : Blo 362758 549575 := bstep (se 1 (by rfl) ⟨412181, by rfl⟩ : syracuseStep 549575 = 824363) B824363
theorem B615161 : Blo 362758 615161 := bstep (se 2 (by rfl) ⟨230685, by rfl⟩ : syracuseStep 615161 = 461371) B461371
theorem B549737 : Blo 362758 549737 := bstep (se 2 (by rfl) ⟨206151, by rfl⟩ : syracuseStep 549737 = 412303) B412303
theorem B615343 : Blo 362758 615343 := bstep (se 1 (by rfl) ⟨461507, by rfl⟩ : syracuseStep 615343 = 923015) B923015
theorem B549815 : Blo 362758 549815 := bstep (se 1 (by rfl) ⟨412361, by rfl⟩ : syracuseStep 549815 = 824723) B824723
theorem B549851 : Blo 362758 549851 := bstep (se 1 (by rfl) ⟨412388, by rfl⟩ : syracuseStep 549851 = 824777) B824777
theorem B615431 : Blo 362758 615431 := bstep (se 1 (by rfl) ⟨461573, by rfl⟩ : syracuseStep 615431 = 923147) B923147
theorem B877625 : Blo 362758 877625 := bstep (se 2 (by rfl) ⟨329109, by rfl⟩ : syracuseStep 877625 = 658219) B658219
theorem B615775 : Blo 362758 615775 := bstep (se 1 (by rfl) ⟨461831, by rfl⟩ : syracuseStep 615775 = 923663) B923663
theorem B615863 : Blo 362758 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B780025 : Blo 362758 780025 := bstep (se 2 (by rfl) ⟨292509, by rfl⟩ : syracuseStep 780025 = 585019) B585019
theorem B2778947 : Blo 362758 2778947 := bstep (se 1 (by rfl) ⟨2084210, by rfl⟩ : syracuseStep 2778947 = 4168421) B4168421
theorem B4679633 : Blo 362758 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B616457 : Blo 362758 616457 := bstep (se 2 (by rfl) ⟨231171, by rfl⟩ : syracuseStep 616457 = 462343) B462343
theorem B1173523 : Blo 362758 1173523 := bstep (se 1 (by rfl) ⟨880142, by rfl⟩ : syracuseStep 1173523 = 1760285) B1760285
theorem B780367 : Blo 362758 780367 := bstep (se 1 (by rfl) ⟨585275, by rfl⟩ : syracuseStep 780367 = 1170551) B1170551
theorem B616619 : Blo 362758 616619 := bstep (se 1 (by rfl) ⟨462464, by rfl⟩ : syracuseStep 616619 = 924929) B924929
theorem B617017 : Blo 362758 617017 := bstep (se 2 (by rfl) ⟨231381, by rfl⟩ : syracuseStep 617017 = 462763) B462763
theorem B1174139 : Blo 362758 1174139 := bstep (se 1 (by rfl) ⟨880604, by rfl⟩ : syracuseStep 1174139 = 1761209) B1761209
theorem B617159 : Blo 362758 617159 := bstep (se 1 (by rfl) ⟨462869, by rfl⟩ : syracuseStep 617159 = 925739) B925739
theorem B617321 : Blo 362758 617321 := bstep (se 2 (by rfl) ⟨231495, by rfl⟩ : syracuseStep 617321 = 462991) B462991
theorem B2550635 : Blo 362758 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B6384529 : Blo 362758 6384529 := bstep (se 2 (by rfl) ⟨2394198, by rfl⟩ : syracuseStep 6384529 = 4788397) B4788397
theorem B519367 : Blo 362758 519367 := bstep (se 1 (by rfl) ⟨389525, by rfl⟩ : syracuseStep 519367 = 779051) B779051
theorem B617719 : Blo 362758 617719 := bstep (se 1 (by rfl) ⟨463289, by rfl⟩ : syracuseStep 617719 = 926579) B926579
theorem B1043837 : Blo 362758 1043837 := bstep (se 3 (by rfl) ⟨195719, by rfl⟩ : syracuseStep 1043837 = 391439) B391439
theorem B5074319 : Blo 362758 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B617915 : Blo 362758 617915 := bstep (se 1 (by rfl) ⟨463436, by rfl⟩ : syracuseStep 617915 = 926873) B926873
theorem B618023 : Blo 362758 618023 := bstep (se 1 (by rfl) ⟨463517, by rfl⟩ : syracuseStep 618023 = 927035) B927035
theorem B781921 : Blo 362758 781921 := bstep (se 2 (by rfl) ⟨293220, by rfl⟩ : syracuseStep 781921 = 586441) B586441
theorem B1044065 : Blo 362758 1044065 := bstep (se 2 (by rfl) ⟨391524, by rfl⟩ : syracuseStep 1044065 = 783049) B783049
theorem B2715275 : Blo 362758 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B618313 : Blo 362758 618313 := bstep (se 2 (by rfl) ⟨231867, by rfl⟩ : syracuseStep 618313 = 463735) B463735
theorem B618347 : Blo 362758 618347 := bstep (se 1 (by rfl) ⟨463760, by rfl⟩ : syracuseStep 618347 = 927521) B927521
theorem B585647 : Blo 362758 585647 := bstep (se 1 (by rfl) ⟨439235, by rfl⟩ : syracuseStep 585647 = 878471) B878471
theorem B1961921 : Blo 362758 1961921 := bstep (se 2 (by rfl) ⟨735720, by rfl⟩ : syracuseStep 1961921 = 1471441) B1471441
theorem B1404985 : Blo 362758 1404985 := bstep (se 2 (by rfl) ⟨526869, by rfl⟩ : syracuseStep 1404985 = 1053739) B1053739
theorem B618745 : Blo 362758 618745 := bstep (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) B464059
theorem B586057 : Blo 362758 586057 := bstep (se 2 (by rfl) ⟨219771, by rfl⟩ : syracuseStep 586057 = 439543) B439543
theorem B7893773 : Blo 362758 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B816299 : Blo 362758 816299 := bstep (se 1 (by rfl) ⟨612224, by rfl⟩ : syracuseStep 816299 = 1224449) B1224449
theorem B390619 : Blo 362758 390619 := bstep (se 1 (by rfl) ⟨292964, by rfl⟩ : syracuseStep 390619 = 585929) B585929
theorem B2094781 : Blo 362758 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B816839 : Blo 362758 816839 := bstep (se 1 (by rfl) ⟨612629, by rfl⟩ : syracuseStep 816839 = 1225259) B1225259
theorem B1472363 : Blo 362758 1472363 := bstep (se 1 (by rfl) ⟨1104272, by rfl⟩ : syracuseStep 1472363 = 2208545) B2208545
theorem B6977623 : Blo 362758 6977623 := bstep (se 1 (by rfl) ⟨5233217, by rfl⟩ : syracuseStep 6977623 = 10466435) B10466435
theorem B2783321 : Blo 362758 2783321 := bstep (se 2 (by rfl) ⟨1043745, by rfl⟩ : syracuseStep 2783321 = 2087491) B2087491
theorem B1964189 : Blo 362758 1964189 := bstep (se 3 (by rfl) ⟨368285, by rfl⟩ : syracuseStep 1964189 = 736571) B736571
theorem B817703 : Blo 362758 817703 := bstep (se 1 (by rfl) ⟨613277, by rfl⟩ : syracuseStep 817703 = 1226555) B1226555
theorem B1407851 : Blo 362758 1407851 := bstep (se 1 (by rfl) ⟨1055888, by rfl⟩ : syracuseStep 1407851 = 2111777) B2111777
theorem B818027 : Blo 362758 818027 := bstep (se 1 (by rfl) ⟨613520, by rfl⟩ : syracuseStep 818027 = 1227041) B1227041
theorem B818081 : Blo 362758 818081 := bstep (se 2 (by rfl) ⟨306780, by rfl⟩ : syracuseStep 818081 = 613561) B613561
theorem B2948069 : Blo 362758 2948069 := bstep (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) B552763
theorem B654355 : Blo 362758 654355 := bstep (se 1 (by rfl) ⟨490766, by rfl⟩ : syracuseStep 654355 = 981533) B981533
theorem B5242103 : Blo 362758 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B818423 : Blo 362758 818423 := bstep (se 1 (by rfl) ⟨613817, by rfl⟩ : syracuseStep 818423 = 1227635) B1227635
theorem B6651317 : Blo 362758 6651317 := bstep (se 5 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 6651317 = 623561) B623561
theorem B2784779 : Blo 362758 2784779 := bstep (se 1 (by rfl) ⟨2088584, by rfl⟩ : syracuseStep 2784779 = 4177169) B4177169
theorem B819017 : Blo 362758 819017 := bstep (se 2 (by rfl) ⟨307131, by rfl⟩ : syracuseStep 819017 = 614263) B614263
theorem B819305 : Blo 362758 819305 := bstep (se 2 (by rfl) ⟨307239, by rfl⟩ : syracuseStep 819305 = 614479) B614479
theorem B2392217 : Blo 362758 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B819791 : Blo 362758 819791 := bstep (se 1 (by rfl) ⟨614843, by rfl⟩ : syracuseStep 819791 = 1229687) B1229687
theorem B459371 : Blo 362758 459371 := bstep (se 1 (by rfl) ⟨344528, by rfl⟩ : syracuseStep 459371 = 689057) B689057
theorem B1966763 : Blo 362758 1966763 := bstep (se 1 (by rfl) ⟨1475072, by rfl⟩ : syracuseStep 1966763 = 2950145) B2950145
theorem B819935 : Blo 362758 819935 := bstep (se 1 (by rfl) ⟨614951, by rfl⟩ : syracuseStep 819935 = 1229903) B1229903
theorem B5604173 : Blo 362758 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B820187 : Blo 362758 820187 := bstep (se 1 (by rfl) ⟨615140, by rfl⟩ : syracuseStep 820187 = 1230281) B1230281
theorem B459751 : Blo 362758 459751 := bstep (se 1 (by rfl) ⟨344813, by rfl⟩ : syracuseStep 459751 = 689627) B689627
theorem B820367 : Blo 362758 820367 := bstep (se 1 (by rfl) ⟨615275, by rfl⟩ : syracuseStep 820367 = 1230551) B1230551
theorem B820457 : Blo 362758 820457 := bstep (se 2 (by rfl) ⟨307671, by rfl⟩ : syracuseStep 820457 = 615343) B615343
theorem B820511 : Blo 362758 820511 := bstep (se 1 (by rfl) ⟨615383, by rfl⟩ : syracuseStep 820511 = 1230767) B1230767
theorem B3802405 : Blo 362758 3802405 := bstep (se 4 (by rfl) ⟨356475, by rfl⟩ : syracuseStep 3802405 = 712951) B712951
theorem B918823 : Blo 362758 918823 := bstep (se 1 (by rfl) ⟨689117, by rfl⟩ : syracuseStep 918823 = 1378235) B1378235
theorem B886153 : Blo 362758 886153 := bstep (se 2 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 886153 = 664615) B664615
theorem B919097 : Blo 362758 919097 := bstep (se 2 (by rfl) ⟨344661, by rfl⟩ : syracuseStep 919097 = 689323) B689323
theorem B821033 : Blo 362758 821033 := bstep (se 2 (by rfl) ⟨307887, by rfl⟩ : syracuseStep 821033 = 615775) B615775
theorem B2230199 : Blo 362758 2230199 := bstep (se 1 (by rfl) ⟨1672649, by rfl⟩ : syracuseStep 2230199 = 3345299) B3345299
theorem B1837241 : Blo 362758 1837241 := bstep (se 2 (by rfl) ⟨688965, by rfl⟩ : syracuseStep 1837241 = 1377931) B1377931
theorem B362783 : Blo 362758 362783 := bstep (se 1 (by rfl) ⟨272087, by rfl⟩ : syracuseStep 362783 = 544175) B544175
theorem B362843 : Blo 362758 362843 := bstep (se 1 (by rfl) ⟨272132, by rfl⟩ : syracuseStep 362843 = 544265) B544265
theorem B362863 : Blo 362758 362863 := bstep (se 1 (by rfl) ⟨272147, by rfl⟩ : syracuseStep 362863 = 544295) B544295
theorem B362919 : Blo 362758 362919 := bstep (se 1 (by rfl) ⟨272189, by rfl⟩ : syracuseStep 362919 = 544379) B544379
theorem B690599 : Blo 362758 690599 := bstep (se 1 (by rfl) ⟨517949, by rfl⟩ : syracuseStep 690599 = 1035899) B1035899
theorem B1411511 : Blo 362758 1411511 := bstep (se 1 (by rfl) ⟨1058633, by rfl⟩ : syracuseStep 1411511 = 2117267) B2117267
theorem B363003 : Blo 362758 363003 := bstep (se 1 (by rfl) ⟨272252, by rfl⟩ : syracuseStep 363003 = 544505) B544505
theorem B363071 : Blo 362758 363071 := bstep (se 1 (by rfl) ⟨272303, by rfl⟩ : syracuseStep 363071 = 544607) B544607
theorem B363079 : Blo 362758 363079 := bstep (se 1 (by rfl) ⟨272309, by rfl⟩ : syracuseStep 363079 = 544619) B544619
theorem B1378889 : Blo 362758 1378889 := bstep (se 2 (by rfl) ⟨517083, by rfl⟩ : syracuseStep 1378889 = 1034167) B1034167
theorem B363231 : Blo 362758 363231 := bstep (se 1 (by rfl) ⟨272423, by rfl⟩ : syracuseStep 363231 = 544847) B544847
theorem B363311 : Blo 362758 363311 := bstep (se 1 (by rfl) ⟨272483, by rfl⟩ : syracuseStep 363311 = 544967) B544967
theorem B822095 : Blo 362758 822095 := bstep (se 1 (by rfl) ⟨616571, by rfl⟩ : syracuseStep 822095 = 1233143) B1233143
theorem B363419 : Blo 362758 363419 := bstep (se 1 (by rfl) ⟨272564, by rfl⟩ : syracuseStep 363419 = 545129) B545129
theorem B363471 : Blo 362758 363471 := bstep (se 1 (by rfl) ⟨272603, by rfl⟩ : syracuseStep 363471 = 545207) B545207
theorem B363495 : Blo 362758 363495 := bstep (se 1 (by rfl) ⟨272621, by rfl⟩ : syracuseStep 363495 = 545243) B545243
theorem B822311 : Blo 362758 822311 := bstep (se 1 (by rfl) ⟨616733, by rfl⟩ : syracuseStep 822311 = 1233467) B1233467
theorem B7179443 : Blo 362758 7179443 := bstep (se 1 (by rfl) ⟨5384582, by rfl⟩ : syracuseStep 7179443 = 10769165) B10769165
theorem B888023 : Blo 362758 888023 := bstep (se 1 (by rfl) ⟨666017, by rfl⟩ : syracuseStep 888023 = 1332035) B1332035
theorem B822491 : Blo 362758 822491 := bstep (se 1 (by rfl) ⟨616868, by rfl⟩ : syracuseStep 822491 = 1233737) B1233737
theorem B8228087 : Blo 362758 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B363807 : Blo 362758 363807 := bstep (se 1 (by rfl) ⟨272855, by rfl⟩ : syracuseStep 363807 = 545711) B545711
theorem B691487 : Blo 362758 691487 := bstep (se 1 (by rfl) ⟨518615, by rfl⟩ : syracuseStep 691487 = 1037231) B1037231
theorem B363867 : Blo 362758 363867 := bstep (se 1 (by rfl) ⟨272900, by rfl⟩ : syracuseStep 363867 = 545801) B545801
theorem B920929 : Blo 362758 920929 := bstep (se 2 (by rfl) ⟨345348, by rfl⟩ : syracuseStep 920929 = 690697) B690697
theorem B363887 : Blo 362758 363887 := bstep (se 1 (by rfl) ⟨272915, by rfl⟩ : syracuseStep 363887 = 545831) B545831
theorem B2329975 : Blo 362758 2329975 := bstep (se 1 (by rfl) ⟨1747481, by rfl⟩ : syracuseStep 2329975 = 3494963) B3494963
theorem B5311873 : Blo 362758 5311873 := bstep (se 2 (by rfl) ⟨1991952, by rfl⟩ : syracuseStep 5311873 = 3983905) B3983905
theorem B822689 : Blo 362758 822689 := bstep (se 2 (by rfl) ⟨308508, by rfl⟩ : syracuseStep 822689 = 617017) B617017
theorem B363943 : Blo 362758 363943 := bstep (se 1 (by rfl) ⟨272957, by rfl⟩ : syracuseStep 363943 = 545915) B545915
theorem B4427207 : Blo 362758 4427207 := bstep (se 1 (by rfl) ⟨3320405, by rfl⟩ : syracuseStep 4427207 = 6640811) B6640811
theorem B364027 : Blo 362758 364027 := bstep (se 1 (by rfl) ⟨273020, by rfl⟩ : syracuseStep 364027 = 546041) B546041
theorem B2756105 : Blo 362758 2756105 := bstep (se 2 (by rfl) ⟨1033539, by rfl⟩ : syracuseStep 2756105 = 2067079) B2067079
theorem B364095 : Blo 362758 364095 := bstep (se 1 (by rfl) ⟨273071, by rfl⟩ : syracuseStep 364095 = 546143) B546143
theorem B364103 : Blo 362758 364103 := bstep (se 1 (by rfl) ⟨273077, by rfl⟩ : syracuseStep 364103 = 546155) B546155
theorem B3116717 : Blo 362758 3116717 := bstep (se 3 (by rfl) ⟨584384, by rfl⟩ : syracuseStep 3116717 = 1168769) B1168769
theorem B364255 : Blo 362758 364255 := bstep (se 1 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 364255 = 546383) B546383
theorem B364335 : Blo 362758 364335 := bstep (se 1 (by rfl) ⟨273251, by rfl⟩ : syracuseStep 364335 = 546503) B546503
theorem B364443 : Blo 362758 364443 := bstep (se 1 (by rfl) ⟨273332, by rfl⟩ : syracuseStep 364443 = 546665) B546665
theorem B3149725 : Blo 362758 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B1839023 : Blo 362758 1839023 := bstep (se 1 (by rfl) ⟨1379267, by rfl⟩ : syracuseStep 1839023 = 2758535) B2758535
theorem B364495 : Blo 362758 364495 := bstep (se 1 (by rfl) ⟨273371, by rfl⟩ : syracuseStep 364495 = 546743) B546743
theorem B823247 : Blo 362758 823247 := bstep (se 1 (by rfl) ⟨617435, by rfl⟩ : syracuseStep 823247 = 1234871) B1234871
theorem B364519 : Blo 362758 364519 := bstep (se 1 (by rfl) ⟨273389, by rfl⟩ : syracuseStep 364519 = 546779) B546779
theorem B1380361 : Blo 362758 1380361 := bstep (se 2 (by rfl) ⟨517635, by rfl⟩ : syracuseStep 1380361 = 1035271) B1035271
theorem B2330795 : Blo 362758 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B1315025 : Blo 362758 1315025 := bstep (se 2 (by rfl) ⟨493134, by rfl⟩ : syracuseStep 1315025 = 986269) B986269
theorem B692489 : Blo 362758 692489 := bstep (se 2 (by rfl) ⟨259683, by rfl⟩ : syracuseStep 692489 = 519367) B519367
theorem B921881 : Blo 362758 921881 := bstep (se 2 (by rfl) ⟨345705, by rfl⟩ : syracuseStep 921881 = 691411) B691411
theorem B364831 : Blo 362758 364831 := bstep (se 1 (by rfl) ⟨273623, by rfl⟩ : syracuseStep 364831 = 547247) B547247
theorem B823625 : Blo 362758 823625 := bstep (se 2 (by rfl) ⟨308859, by rfl⟩ : syracuseStep 823625 = 617719) B617719
theorem B364891 : Blo 362758 364891 := bstep (se 1 (by rfl) ⟨273668, by rfl⟩ : syracuseStep 364891 = 547337) B547337
theorem B823643 : Blo 362758 823643 := bstep (se 1 (by rfl) ⟨617732, by rfl⟩ : syracuseStep 823643 = 1235465) B1235465
theorem B364911 : Blo 362758 364911 := bstep (se 1 (by rfl) ⟨273683, by rfl⟩ : syracuseStep 364911 = 547367) B547367
theorem B364967 : Blo 362758 364967 := bstep (se 1 (by rfl) ⟨273725, by rfl⟩ : syracuseStep 364967 = 547451) B547451
theorem B1380833 : Blo 362758 1380833 := bstep (se 2 (by rfl) ⟨517812, by rfl⟩ : syracuseStep 1380833 = 1035625) B1035625
theorem B365051 : Blo 362758 365051 := bstep (se 1 (by rfl) ⟨273788, by rfl⟩ : syracuseStep 365051 = 547577) B547577
theorem B3510803 : Blo 362758 3510803 := bstep (se 1 (by rfl) ⟨2633102, by rfl⟩ : syracuseStep 3510803 = 5266205) B5266205
theorem B922175 : Blo 362758 922175 := bstep (se 1 (by rfl) ⟨691631, by rfl⟩ : syracuseStep 922175 = 1383263) B1383263
theorem B365119 : Blo 362758 365119 := bstep (se 1 (by rfl) ⟨273839, by rfl⟩ : syracuseStep 365119 = 547679) B547679
theorem B365127 : Blo 362758 365127 := bstep (se 1 (by rfl) ⟨273845, by rfl⟩ : syracuseStep 365127 = 547691) B547691
theorem B365279 : Blo 362758 365279 := bstep (se 1 (by rfl) ⟨273959, by rfl⟩ : syracuseStep 365279 = 547919) B547919
theorem B463583 : Blo 362758 463583 := bstep (se 1 (by rfl) ⟨347687, by rfl⟩ : syracuseStep 463583 = 695375) B695375
theorem B922387 : Blo 362758 922387 := bstep (se 1 (by rfl) ⟨691790, by rfl⟩ : syracuseStep 922387 = 1383581) B1383581
theorem B365359 : Blo 362758 365359 := bstep (se 1 (by rfl) ⟨274019, by rfl⟩ : syracuseStep 365359 = 548039) B548039
theorem B365467 : Blo 362758 365467 := bstep (se 1 (by rfl) ⟨274100, by rfl⟩ : syracuseStep 365467 = 548201) B548201
theorem B824219 : Blo 362758 824219 := bstep (se 1 (by rfl) ⟨618164, by rfl⟩ : syracuseStep 824219 = 1236329) B1236329
theorem B2626505 : Blo 362758 2626505 := bstep (se 2 (by rfl) ⟨984939, by rfl⟩ : syracuseStep 2626505 = 1969879) B1969879
theorem B32478155 : Blo 362758 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B365519 : Blo 362758 365519 := bstep (se 1 (by rfl) ⟨274139, by rfl⟩ : syracuseStep 365519 = 548279) B548279
theorem B365543 : Blo 362758 365543 := bstep (se 1 (by rfl) ⟨274157, by rfl⟩ : syracuseStep 365543 = 548315) B548315
theorem B2069495 : Blo 362758 2069495 := bstep (se 1 (by rfl) ⟨1552121, by rfl⟩ : syracuseStep 2069495 = 3104243) B3104243
theorem B824417 : Blo 362758 824417 := bstep (se 2 (by rfl) ⟨309156, by rfl⟩ : syracuseStep 824417 = 618313) B618313
theorem B922823 : Blo 362758 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B922873 : Blo 362758 922873 := bstep (se 2 (by rfl) ⟨346077, by rfl⟩ : syracuseStep 922873 = 692155) B692155
theorem B365855 : Blo 362758 365855 := bstep (se 1 (by rfl) ⟨274391, by rfl⟩ : syracuseStep 365855 = 548783) B548783
theorem B824615 : Blo 362758 824615 := bstep (se 1 (by rfl) ⟨618461, by rfl⟩ : syracuseStep 824615 = 1236923) B1236923
theorem B365915 : Blo 362758 365915 := bstep (se 1 (by rfl) ⟨274436, by rfl⟩ : syracuseStep 365915 = 548873) B548873
theorem B365935 : Blo 362758 365935 := bstep (se 1 (by rfl) ⟨274451, by rfl⟩ : syracuseStep 365935 = 548903) B548903
theorem B2758049 : Blo 362758 2758049 := bstep (se 2 (by rfl) ⟨1034268, by rfl⟩ : syracuseStep 2758049 = 2068537) B2068537
theorem B1873313 : Blo 362758 1873313 := bstep (se 2 (by rfl) ⟨702492, by rfl⟩ : syracuseStep 1873313 = 1404985) B1404985
theorem B365991 : Blo 362758 365991 := bstep (se 1 (by rfl) ⟨274493, by rfl⟩ : syracuseStep 365991 = 548987) B548987
theorem B366075 : Blo 362758 366075 := bstep (se 1 (by rfl) ⟨274556, by rfl⟩ : syracuseStep 366075 = 549113) B549113
theorem B366143 : Blo 362758 366143 := bstep (se 1 (by rfl) ⟨274607, by rfl⟩ : syracuseStep 366143 = 549215) B549215
theorem B366151 : Blo 362758 366151 := bstep (se 1 (by rfl) ⟨274613, by rfl⟩ : syracuseStep 366151 = 549227) B549227
theorem B824993 : Blo 362758 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B693947 : Blo 362758 693947 := bstep (se 1 (by rfl) ⟨520460, by rfl⟩ : syracuseStep 693947 = 1040921) B1040921
theorem B366303 : Blo 362758 366303 := bstep (se 1 (by rfl) ⟨274727, by rfl⟩ : syracuseStep 366303 = 549455) B549455
theorem B366383 : Blo 362758 366383 := bstep (se 1 (by rfl) ⟨274787, by rfl⟩ : syracuseStep 366383 = 549575) B549575
theorem B923521 : Blo 362758 923521 := bstep (se 2 (by rfl) ⟨346320, by rfl⟩ : syracuseStep 923521 = 692641) B692641
theorem B366491 : Blo 362758 366491 := bstep (se 1 (by rfl) ⟨274868, by rfl⟩ : syracuseStep 366491 = 549737) B549737
theorem B366543 : Blo 362758 366543 := bstep (se 1 (by rfl) ⟨274907, by rfl⟩ : syracuseStep 366543 = 549815) B549815
theorem B366567 : Blo 362758 366567 := bstep (se 1 (by rfl) ⟨274925, by rfl⟩ : syracuseStep 366567 = 549851) B549851
theorem B1185977 : Blo 362758 1185977 := bstep (se 2 (by rfl) ⟨444741, by rfl⟩ : syracuseStep 1185977 = 889483) B889483
theorem B924281 : Blo 362758 924281 := bstep (se 2 (by rfl) ⟨346605, by rfl⟩ : syracuseStep 924281 = 693211) B693211
theorem B3119755 : Blo 362758 3119755 := bstep (se 1 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 3119755 = 4679633) B4679633
theorem B924331 : Blo 362758 924331 := bstep (se 1 (by rfl) ⟨693248, by rfl⟩ : syracuseStep 924331 = 1386497) B1386497
theorem B1841939 : Blo 362758 1841939 := bstep (se 1 (by rfl) ⟨1381454, by rfl⟩ : syracuseStep 1841939 = 2762909) B2762909
theorem B1973011 : Blo 362758 1973011 := bstep (se 1 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 1973011 = 2959517) B2959517
theorem B924635 : Blo 362758 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B924959 : Blo 362758 924959 := bstep (se 1 (by rfl) ⟨693719, by rfl⟩ : syracuseStep 924959 = 1387439) B1387439
theorem B2793041 : Blo 362758 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B695891 : Blo 362758 695891 := bstep (se 1 (by rfl) ⟨521918, by rfl⟩ : syracuseStep 695891 = 1043837) B1043837
theorem B3382879 : Blo 362758 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B696043 : Blo 362758 696043 := bstep (se 1 (by rfl) ⟨522032, by rfl⟩ : syracuseStep 696043 = 1044065) B1044065
theorem B1810183 : Blo 362758 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B1384249 : Blo 362758 1384249 := bstep (se 2 (by rfl) ⟨519093, by rfl⟩ : syracuseStep 1384249 = 1038187) B1038187
theorem B1843073 : Blo 362758 1843073 := bstep (se 2 (by rfl) ⟨691152, by rfl⟩ : syracuseStep 1843073 = 1382305) B1382305
theorem B1384553 : Blo 362758 1384553 := bstep (se 2 (by rfl) ⟨519207, by rfl⟩ : syracuseStep 1384553 = 1038415) B1038415
theorem B2072729 : Blo 362758 2072729 := bstep (se 2 (by rfl) ⟨777273, by rfl⟩ : syracuseStep 2072729 = 1554547) B1554547
theorem B926063 : Blo 362758 926063 := bstep (se 1 (by rfl) ⟨694547, by rfl⟩ : syracuseStep 926063 = 1389095) B1389095
theorem B1843883 : Blo 362758 1843883 := bstep (se 1 (by rfl) ⟨1382912, by rfl⟩ : syracuseStep 1843883 = 2765825) B2765825
theorem B926711 : Blo 362758 926711 := bstep (se 1 (by rfl) ⟨695033, by rfl⟩ : syracuseStep 926711 = 1390067) B1390067
theorem B1844369 : Blo 362758 1844369 := bstep (se 2 (by rfl) ⟨691638, by rfl⟩ : syracuseStep 1844369 = 1383277) B1383277
theorem B4139261 : Blo 362758 4139261 := bstep (se 3 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 4139261 = 1552223) B1552223
theorem B4434211 : Blo 362758 4434211 := bstep (se 1 (by rfl) ⟨3325658, by rfl⟩ : syracuseStep 4434211 = 6651317) B6651317
theorem B6302063 : Blo 362758 6302063 := bstep (se 1 (by rfl) ⟨4726547, by rfl⟩ : syracuseStep 6302063 = 9453095) B9453095
theorem B928427 : Blo 362758 928427 := bstep (se 1 (by rfl) ⟨696320, by rfl⟩ : syracuseStep 928427 = 1392641) B1392641
theorem B436919 : Blo 362758 436919 := bstep (se 1 (by rfl) ⟨327689, by rfl⟩ : syracuseStep 436919 = 655379) B655379
theorem B437467 : Blo 362758 437467 := bstep (se 1 (by rfl) ⟨328100, by rfl⟩ : syracuseStep 437467 = 656201) B656201
theorem B1846799 : Blo 362758 1846799 := bstep (se 1 (by rfl) ⟨1385099, by rfl⟩ : syracuseStep 1846799 = 2770199) B2770199
theorem B7450555 : Blo 362758 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B5910731 : Blo 362758 5910731 := bstep (se 1 (by rfl) ⟨4433048, by rfl⟩ : syracuseStep 5910731 = 8866097) B8866097
theorem B1749251 : Blo 362758 1749251 := bstep (se 1 (by rfl) ⟨1311938, by rfl⟩ : syracuseStep 1749251 = 2623877) B2623877
theorem B2077103 : Blo 362758 2077103 := bstep (se 1 (by rfl) ⟨1557827, by rfl⟩ : syracuseStep 2077103 = 3115655) B3115655
theorem B1847771 : Blo 362758 1847771 := bstep (se 1 (by rfl) ⟨1385828, by rfl⟩ : syracuseStep 1847771 = 2771657) B2771657
theorem B1848257 : Blo 362758 1848257 := bstep (se 2 (by rfl) ⟨693096, by rfl⟩ : syracuseStep 1848257 = 1386193) B1386193
theorem B1225691 : Blo 362758 1225691 := bstep (se 1 (by rfl) ⟨919268, by rfl⟩ : syracuseStep 1225691 = 1838537) B1838537
theorem B1225853 : Blo 362758 1225853 := bstep (se 3 (by rfl) ⟨229847, by rfl⟩ : syracuseStep 1225853 = 459695) B459695
theorem B1225961 : Blo 362758 1225961 := bstep (se 2 (by rfl) ⟨459735, by rfl⟩ : syracuseStep 1225961 = 919471) B919471
theorem B1226123 : Blo 362758 1226123 := bstep (se 1 (by rfl) ⟨919592, by rfl⟩ : syracuseStep 1226123 = 1839185) B1839185
theorem B6600503 : Blo 362758 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B834043 : Blo 362758 834043 := bstep (se 1 (by rfl) ⟨625532, by rfl⟩ : syracuseStep 834043 = 1251065) B1251065
theorem B408127 : Blo 362758 408127 := bstep (se 1 (by rfl) ⟨306095, by rfl⟩ : syracuseStep 408127 = 612191) B612191
theorem B3160939 : Blo 362758 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B2407747 : Blo 362758 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B408955 : Blo 362758 408955 := bstep (se 1 (by rfl) ⟨306716, by rfl⟩ : syracuseStep 408955 = 613433) B613433
theorem B3128777 : Blo 362758 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B2342459 : Blo 362758 2342459 := bstep (se 1 (by rfl) ⟨1756844, by rfl⟩ : syracuseStep 2342459 = 3513689) B3513689
theorem B2342483 : Blo 362758 2342483 := bstep (se 1 (by rfl) ⟨1756862, by rfl⟩ : syracuseStep 2342483 = 3513725) B3513725
theorem B409423 : Blo 362758 409423 := bstep (se 1 (by rfl) ⟨307067, by rfl⟩ : syracuseStep 409423 = 614135) B614135
theorem B1851497 : Blo 362758 1851497 := bstep (se 2 (by rfl) ⟨694311, by rfl⟩ : syracuseStep 1851497 = 1388623) B1388623
theorem B2212049 : Blo 362758 2212049 := bstep (se 2 (by rfl) ⟨829518, by rfl⟩ : syracuseStep 2212049 = 1659037) B1659037
theorem B835795 : Blo 362758 835795 := bstep (se 1 (by rfl) ⟨626846, by rfl⟩ : syracuseStep 835795 = 1253693) B1253693
theorem B409819 : Blo 362758 409819 := bstep (se 1 (by rfl) ⟨307364, by rfl⟩ : syracuseStep 409819 = 614729) B614729
theorem B1229147 : Blo 362758 1229147 := bstep (se 1 (by rfl) ⟨921860, by rfl⟩ : syracuseStep 1229147 = 1843721) B1843721
theorem B7487923 : Blo 362758 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B410107 : Blo 362758 410107 := bstep (se 1 (by rfl) ⟨307580, by rfl⟩ : syracuseStep 410107 = 615161) B615161
theorem B410287 : Blo 362758 410287 := bstep (se 1 (by rfl) ⟨307715, by rfl⟩ : syracuseStep 410287 = 615431) B615431
theorem B441762497 : Blo 362758 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B5259977 : Blo 362758 5259977 := bstep (se 2 (by rfl) ⟨1972491, by rfl⟩ : syracuseStep 5259977 = 3944983) B3944983
theorem B7914185 : Blo 362758 7914185 := bstep (se 2 (by rfl) ⟨2967819, by rfl⟩ : syracuseStep 7914185 = 5935639) B5935639
theorem B410575 : Blo 362758 410575 := bstep (se 1 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 410575 = 615863) B615863
theorem B1852631 : Blo 362758 1852631 := bstep (se 1 (by rfl) ⟨1389473, by rfl⟩ : syracuseStep 1852631 = 2778947) B2778947
theorem B443611 : Blo 362758 443611 := bstep (se 1 (by rfl) ⟨332708, by rfl⟩ : syracuseStep 443611 = 665417) B665417
theorem B1230119 : Blo 362758 1230119 := bstep (se 1 (by rfl) ⟨922589, by rfl⟩ : syracuseStep 1230119 = 1845179) B1845179
theorem B410971 : Blo 362758 410971 := bstep (se 1 (by rfl) ⟨308228, by rfl⟩ : syracuseStep 410971 = 616457) B616457
theorem B411079 : Blo 362758 411079 := bstep (se 1 (by rfl) ⟨308309, by rfl⟩ : syracuseStep 411079 = 616619) B616619
theorem B411439 : Blo 362758 411439 := bstep (se 1 (by rfl) ⟨308579, by rfl⟩ : syracuseStep 411439 = 617159) B617159
theorem B411547 : Blo 362758 411547 := bstep (se 1 (by rfl) ⟨308660, by rfl⟩ : syracuseStep 411547 = 617321) B617321
theorem B1099727 : Blo 362758 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B1230983 : Blo 362758 1230983 := bstep (se 1 (by rfl) ⟨923237, by rfl⟩ : syracuseStep 1230983 = 1846475) B1846475
theorem B13289669 : Blo 362758 13289669 := bstep (se 4 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 13289669 = 2491813) B2491813
theorem B411943 : Blo 362758 411943 := bstep (se 1 (by rfl) ⟨308957, by rfl⟩ : syracuseStep 411943 = 617915) B617915
theorem B412015 : Blo 362758 412015 := bstep (se 1 (by rfl) ⟨309011, by rfl⟩ : syracuseStep 412015 = 618023) B618023
theorem B2214287 : Blo 362758 2214287 := bstep (se 1 (by rfl) ⟨1660715, by rfl⟩ : syracuseStep 2214287 = 3321431) B3321431
theorem B412231 : Blo 362758 412231 := bstep (se 1 (by rfl) ⟨309173, by rfl⟩ : syracuseStep 412231 = 618347) B618347
theorem B5262515 : Blo 362758 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B1232225 : Blo 362758 1232225 := bstep (se 2 (by rfl) ⟨462084, by rfl⟩ : syracuseStep 1232225 = 924169) B924169
theorem B937313 : Blo 362758 937313 := bstep (se 2 (by rfl) ⟨351492, by rfl⟩ : syracuseStep 937313 = 702985) B702985
theorem B544199 : Blo 362758 544199 := bstep (se 1 (by rfl) ⟨408149, by rfl⟩ : syracuseStep 544199 = 816299) B816299
theorem B9981589 : Blo 362758 9981589 := bstep (se 6 (by rfl) ⟨233943, by rfl⟩ : syracuseStep 9981589 = 467887) B467887
theorem B544553 : Blo 362758 544553 := bstep (se 2 (by rfl) ⟨204207, by rfl⟩ : syracuseStep 544553 = 408415) B408415
theorem B544559 : Blo 362758 544559 := bstep (se 1 (by rfl) ⟨408419, by rfl⟩ : syracuseStep 544559 = 816839) B816839
theorem B872473 : Blo 362758 872473 := bstep (se 2 (by rfl) ⟨327177, by rfl⟩ : syracuseStep 872473 = 654355) B654355
theorem B1757209 : Blo 362758 1757209 := bstep (se 2 (by rfl) ⟨658953, by rfl⟩ : syracuseStep 1757209 = 1317907) B1317907
theorem B1855547 : Blo 362758 1855547 := bstep (se 1 (by rfl) ⟨1391660, by rfl⟩ : syracuseStep 1855547 = 2783321) B2783321
theorem B545033 : Blo 362758 545033 := bstep (se 2 (by rfl) ⟨204387, by rfl⟩ : syracuseStep 545033 = 408775) B408775
theorem B15749477 : Blo 362758 15749477 := bstep (se 4 (by rfl) ⟨1476513, by rfl⟩ : syracuseStep 15749477 = 2953027) B2953027
theorem B545135 : Blo 362758 545135 := bstep (se 1 (by rfl) ⟨408851, by rfl⟩ : syracuseStep 545135 = 817703) B817703
theorem B545351 : Blo 362758 545351 := bstep (se 1 (by rfl) ⟨409013, by rfl⟩ : syracuseStep 545351 = 818027) B818027
theorem B938567 : Blo 362758 938567 := bstep (se 1 (by rfl) ⟨703925, by rfl⟩ : syracuseStep 938567 = 1407851) B1407851
theorem B2773601 : Blo 362758 2773601 := bstep (se 2 (by rfl) ⟨1040100, by rfl⟩ : syracuseStep 2773601 = 2080201) B2080201
theorem B545387 : Blo 362758 545387 := bstep (se 1 (by rfl) ⟨409040, by rfl⟩ : syracuseStep 545387 = 818081) B818081
theorem B3494735 : Blo 362758 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B545615 : Blo 362758 545615 := bstep (se 1 (by rfl) ⟨409211, by rfl⟩ : syracuseStep 545615 = 818423) B818423
theorem B4674509 : Blo 362758 4674509 := bstep (se 3 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 4674509 = 1752941) B1752941
theorem B1856519 : Blo 362758 1856519 := bstep (se 1 (by rfl) ⟨1392389, by rfl⟩ : syracuseStep 1856519 = 2784779) B2784779
theorem B2086033 : Blo 362758 2086033 := bstep (se 2 (by rfl) ⟨782262, by rfl⟩ : syracuseStep 2086033 = 1564525) B1564525
theorem B546011 : Blo 362758 546011 := bstep (se 1 (by rfl) ⟨409508, by rfl⟩ : syracuseStep 546011 = 819017) B819017
theorem B1234169 : Blo 362758 1234169 := bstep (se 2 (by rfl) ⟨462813, by rfl⟩ : syracuseStep 1234169 = 925627) B925627
theorem B1660283 : Blo 362758 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B546185 : Blo 362758 546185 := bstep (se 2 (by rfl) ⟨204819, by rfl⟩ : syracuseStep 546185 = 409639) B409639
theorem B1234439 : Blo 362758 1234439 := bstep (se 1 (by rfl) ⟨925829, by rfl⟩ : syracuseStep 1234439 = 1851659) B1851659
theorem B546539 : Blo 362758 546539 := bstep (se 1 (by rfl) ⟨409904, by rfl⟩ : syracuseStep 546539 = 819809) B819809
theorem B775993 : Blo 362758 775993 := bstep (se 2 (by rfl) ⟨290997, by rfl⟩ : syracuseStep 775993 = 581995) B581995
theorem B546767 : Blo 362758 546767 := bstep (se 1 (by rfl) ⟨410075, by rfl⟩ : syracuseStep 546767 = 820151) B820151
theorem B743375 : Blo 362758 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B2086991 : Blo 362758 2086991 := bstep (se 1 (by rfl) ⟨1565243, by rfl⟩ : syracuseStep 2086991 = 3130487) B3130487
theorem B547163 : Blo 362758 547163 := bstep (se 1 (by rfl) ⟨410372, by rfl⟩ : syracuseStep 547163 = 820745) B820745
theorem B1235411 : Blo 362758 1235411 := bstep (se 1 (by rfl) ⟨926558, by rfl⟩ : syracuseStep 1235411 = 1853117) B1853117
theorem B612859 : Blo 362758 612859 := bstep (se 1 (by rfl) ⟨459644, by rfl⟩ : syracuseStep 612859 = 919289) B919289
theorem B547391 : Blo 362758 547391 := bstep (se 1 (by rfl) ⟨410543, by rfl⟩ : syracuseStep 547391 = 821087) B821087
theorem B1235519 : Blo 362758 1235519 := bstep (se 1 (by rfl) ⟨926639, by rfl⟩ : syracuseStep 1235519 = 1853279) B1853279
theorem B10050155 : Blo 362758 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B547511 : Blo 362758 547511 := bstep (se 1 (by rfl) ⟨410633, by rfl⟩ : syracuseStep 547511 = 821267) B821267
theorem B1071863 : Blo 362758 1071863 := bstep (se 1 (by rfl) ⟨803897, by rfl⟩ : syracuseStep 1071863 = 1607795) B1607795
theorem B3103595 : Blo 362758 3103595 := bstep (se 1 (by rfl) ⟨2327696, by rfl⟩ : syracuseStep 3103595 = 4655393) B4655393
theorem B547739 : Blo 362758 547739 := bstep (se 1 (by rfl) ⟨410804, by rfl⟩ : syracuseStep 547739 = 821609) B821609
theorem B613291 : Blo 362758 613291 := bstep (se 1 (by rfl) ⟨459968, by rfl⟩ : syracuseStep 613291 = 919937) B919937
theorem B3922931 : Blo 362758 3922931 := bstep (se 1 (by rfl) ⟨2942198, by rfl⟩ : syracuseStep 3922931 = 5884397) B5884397
theorem B1399997 : Blo 362758 1399997 := bstep (se 3 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 1399997 = 524999) B524999
theorem B613595 : Blo 362758 613595 := bstep (se 1 (by rfl) ⟨460196, by rfl⟩ : syracuseStep 613595 = 920393) B920393
theorem B548135 : Blo 362758 548135 := bstep (se 1 (by rfl) ⟨411101, by rfl⟩ : syracuseStep 548135 = 822203) B822203
theorem B548219 : Blo 362758 548219 := bstep (se 1 (by rfl) ⟨411164, by rfl⟩ : syracuseStep 548219 = 822329) B822329
theorem B613831 : Blo 362758 613831 := bstep (se 1 (by rfl) ⟨460373, by rfl⟩ : syracuseStep 613831 = 920747) B920747
theorem B548345 : Blo 362758 548345 := bstep (se 2 (by rfl) ⟨205629, by rfl⟩ : syracuseStep 548345 = 411259) B411259
theorem B548447 : Blo 362758 548447 := bstep (se 1 (by rfl) ⟨411335, by rfl⟩ : syracuseStep 548447 = 822671) B822671
theorem B1040033 : Blo 362758 1040033 := bstep (se 2 (by rfl) ⟨390012, by rfl⟩ : syracuseStep 1040033 = 780025) B780025
theorem B9002785 : Blo 362758 9002785 := bstep (se 2 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 9002785 = 6752089) B6752089
theorem B581431 : Blo 362758 581431 := bstep (se 1 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 581431 = 872147) B872147
theorem B548663 : Blo 362758 548663 := bstep (se 1 (by rfl) ⟨411497, by rfl⟩ : syracuseStep 548663 = 822995) B822995
theorem B614351 : Blo 362758 614351 := bstep (se 1 (by rfl) ⟨460763, by rfl⟩ : syracuseStep 614351 = 921527) B921527
theorem B1564697 : Blo 362758 1564697 := bstep (se 2 (by rfl) ⟨586761, by rfl⟩ : syracuseStep 1564697 = 1173523) B1173523
theorem B1040489 : Blo 362758 1040489 := bstep (se 2 (by rfl) ⟨390183, by rfl⟩ : syracuseStep 1040489 = 780367) B780367
theorem B548969 : Blo 362758 548969 := bstep (se 2 (by rfl) ⟨205863, by rfl⟩ : syracuseStep 548969 = 411727) B411727
theorem B1237355 : Blo 362758 1237355 := bstep (se 1 (by rfl) ⟨928016, by rfl⟩ : syracuseStep 1237355 = 1856033) B1856033
theorem B549287 : Blo 362758 549287 := bstep (se 1 (by rfl) ⟨411965, by rfl⟩ : syracuseStep 549287 = 823931) B823931
theorem B549371 : Blo 362758 549371 := bstep (se 1 (by rfl) ⟨412028, by rfl⟩ : syracuseStep 549371 = 824057) B824057
theorem B615019 : Blo 362758 615019 := bstep (se 1 (by rfl) ⟨461264, by rfl⟩ : syracuseStep 615019 = 922529) B922529
theorem B549497 : Blo 362758 549497 := bstep (se 2 (by rfl) ⟨206061, by rfl⟩ : syracuseStep 549497 = 412123) B412123
theorem B1237625 : Blo 362758 1237625 := bstep (se 2 (by rfl) ⟨464109, by rfl⟩ : syracuseStep 1237625 = 928219) B928219
theorem B4743851 : Blo 362758 4743851 := bstep (se 1 (by rfl) ⟨3557888, by rfl⟩ : syracuseStep 4743851 = 7115777) B7115777
theorem B549551 : Blo 362758 549551 := bstep (se 1 (by rfl) ⟨412163, by rfl⟩ : syracuseStep 549551 = 824327) B824327
theorem B1172191 : Blo 362758 1172191 := bstep (se 1 (by rfl) ⟨879143, by rfl⟩ : syracuseStep 1172191 = 1758287) B1758287
theorem B549599 : Blo 362758 549599 := bstep (se 1 (by rfl) ⟨412199, by rfl⟩ : syracuseStep 549599 = 824399) B824399
theorem B615323 : Blo 362758 615323 := bstep (se 1 (by rfl) ⟨461492, by rfl⟩ : syracuseStep 615323 = 922985) B922985
theorem B549863 : Blo 362758 549863 := bstep (se 1 (by rfl) ⟨412397, by rfl⟩ : syracuseStep 549863 = 824795) B824795
theorem B1172627 : Blo 362758 1172627 := bstep (se 1 (by rfl) ⟨879470, by rfl⟩ : syracuseStep 1172627 = 1758941) B1758941
theorem B8512705 : Blo 362758 8512705 := bstep (se 2 (by rfl) ⟨3192264, by rfl⟩ : syracuseStep 8512705 = 6384529) B6384529
theorem B550121 : Blo 362758 550121 := bstep (se 2 (by rfl) ⟨206295, by rfl⟩ : syracuseStep 550121 = 412591) B412591
theorem B877817 : Blo 362758 877817 := bstep (se 2 (by rfl) ⟨329181, by rfl⟩ : syracuseStep 877817 = 658363) B658363
theorem B779615 : Blo 362758 779615 := bstep (se 1 (by rfl) ⟨584711, by rfl⟩ : syracuseStep 779615 = 1169423) B1169423
theorem B13297097 : Blo 362758 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B583481 : Blo 362758 583481 := bstep (se 2 (by rfl) ⟨218805, by rfl⟩ : syracuseStep 583481 = 437611) B437611
theorem B1042561 : Blo 362758 1042561 := bstep (se 2 (by rfl) ⟨390960, by rfl⟩ : syracuseStep 1042561 = 781921) B781921
theorem B7039133 : Blo 362758 7039133 := bstep (se 3 (by rfl) ⟨1319837, by rfl⟩ : syracuseStep 7039133 = 2639675) B2639675
theorem B584263 : Blo 362758 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B781409 : Blo 362758 781409 := bstep (se 2 (by rfl) ⟨293028, by rfl⟩ : syracuseStep 781409 = 586057) B586057
theorem B879835 : Blo 362758 879835 := bstep (se 1 (by rfl) ⟨659876, by rfl⟩ : syracuseStep 879835 = 1319753) B1319753
theorem B585083 : Blo 362758 585083 := bstep (se 1 (by rfl) ⟨438812, by rfl⟩ : syracuseStep 585083 = 877625) B877625
theorem B880969 : Blo 362758 880969 := bstep (se 2 (by rfl) ⟨330363, by rfl⟩ : syracuseStep 880969 = 660727) B660727
theorem B782759 : Blo 362758 782759 := bstep (se 1 (by rfl) ⟨587069, by rfl⟩ : syracuseStep 782759 = 1174139) B1174139
theorem B1700423 : Blo 362758 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B520825 : Blo 362758 520825 := bstep (se 2 (by rfl) ⟨195309, by rfl⟩ : syracuseStep 520825 = 390619) B390619
theorem B1077943 : Blo 362758 1077943 := bstep (se 1 (by rfl) ⟨808457, by rfl⟩ : syracuseStep 1077943 = 1616915) B1616915
theorem B14480117 : Blo 362758 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B390431 : Blo 362758 390431 := bstep (se 1 (by rfl) ⟨292823, by rfl⟩ : syracuseStep 390431 = 585647) B585647
theorem B1307947 : Blo 362758 1307947 := bstep (se 1 (by rfl) ⟨980960, by rfl⟩ : syracuseStep 1307947 = 1961921) B1961921
theorem B816479 : Blo 362758 816479 := bstep (se 1 (by rfl) ⟨612359, by rfl⟩ : syracuseStep 816479 = 1224719) B1224719
theorem B9303497 : Blo 362758 9303497 := bstep (se 2 (by rfl) ⟨3488811, by rfl⟩ : syracuseStep 9303497 = 6977623) B6977623
theorem B816875 : Blo 362758 816875 := bstep (se 1 (by rfl) ⟨612656, by rfl⟩ : syracuseStep 816875 = 1225313) B1225313
theorem B817001 : Blo 362758 817001 := bstep (se 2 (by rfl) ⟨306375, by rfl⟩ : syracuseStep 817001 = 612751) B612751
theorem B5928889 : Blo 362758 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B1866007 : Blo 362758 1866007 := bstep (se 1 (by rfl) ⟨1399505, by rfl⟩ : syracuseStep 1866007 = 2799011) B2799011
theorem B2783807 : Blo 362758 2783807 := bstep (se 1 (by rfl) ⟨2087855, by rfl⟩ : syracuseStep 2783807 = 4175711) B4175711
theorem B981575 : Blo 362758 981575 := bstep (se 1 (by rfl) ⟨736181, by rfl⟩ : syracuseStep 981575 = 1472363) B1472363
theorem B817847 : Blo 362758 817847 := bstep (se 1 (by rfl) ⟨613385, by rfl⟩ : syracuseStep 817847 = 1226771) B1226771
theorem B1309459 : Blo 362758 1309459 := bstep (se 1 (by rfl) ⟨982094, by rfl⟩ : syracuseStep 1309459 = 1964189) B1964189
theorem B818063 : Blo 362758 818063 := bstep (se 1 (by rfl) ⟨613547, by rfl⟩ : syracuseStep 818063 = 1227095) B1227095
theorem B3111965 : Blo 362758 3111965 := bstep (se 3 (by rfl) ⟨583493, by rfl⟩ : syracuseStep 3111965 = 1166987) B1166987
theorem B1604827 : Blo 362758 1604827 := bstep (se 1 (by rfl) ⟨1203620, by rfl⟩ : syracuseStep 1604827 = 2407241) B2407241
theorem B1965379 : Blo 362758 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B30080393 : Blo 362758 30080393 := bstep (se 2 (by rfl) ⟨11280147, by rfl⟩ : syracuseStep 30080393 = 22560295) B22560295
theorem B5078533 : Blo 362758 5078533 := bstep (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) B952225
theorem B818783 : Blo 362758 818783 := bstep (se 1 (by rfl) ⟨614087, by rfl⟩ : syracuseStep 818783 = 1228175) B1228175
theorem B818999 : Blo 362758 818999 := bstep (se 1 (by rfl) ⟨614249, by rfl⟩ : syracuseStep 818999 = 1228499) B1228499
theorem B1474699 : Blo 362758 1474699 := bstep (se 1 (by rfl) ⟨1106024, by rfl⟩ : syracuseStep 1474699 = 2212049) B2212049
theorem B819431 : Blo 362758 819431 := bstep (se 1 (by rfl) ⟨614573, by rfl⟩ : syracuseStep 819431 = 1229147) B1229147
theorem B1114393 : Blo 362758 1114393 := bstep (se 2 (by rfl) ⟨417897, by rfl⟩ : syracuseStep 1114393 = 835795) B835795
theorem B1311175 : Blo 362758 1311175 := bstep (se 1 (by rfl) ⟨983381, by rfl⟩ : syracuseStep 1311175 = 1966763) B1966763
theorem B3506651 : Blo 362758 3506651 := bstep (se 1 (by rfl) ⟨2629988, by rfl⟩ : syracuseStep 3506651 = 5259977) B5259977
theorem B5276123 : Blo 362758 5276123 := bstep (se 1 (by rfl) ⟨3957092, by rfl⟩ : syracuseStep 5276123 = 7914185) B7914185
theorem B3736115 : Blo 362758 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B820025 : Blo 362758 820025 := bstep (se 2 (by rfl) ⟨307509, by rfl⟩ : syracuseStep 820025 = 615019) B615019
theorem B820079 : Blo 362758 820079 := bstep (se 1 (by rfl) ⟨615059, by rfl⟩ : syracuseStep 820079 = 1230119) B1230119
theorem B820655 : Blo 362758 820655 := bstep (se 1 (by rfl) ⟨615491, by rfl⟩ : syracuseStep 820655 = 1230983) B1230983
theorem B1476191 : Blo 362758 1476191 := bstep (se 1 (by rfl) ⟨1107143, by rfl⟩ : syracuseStep 1476191 = 2214287) B2214287
theorem B460399 : Blo 362758 460399 := bstep (se 1 (by rfl) ⟨345299, by rfl⟩ : syracuseStep 460399 = 690599) B690599
theorem B591481 : Blo 362758 591481 := bstep (se 2 (by rfl) ⟨221805, by rfl⟩ : syracuseStep 591481 = 443611) B443611
theorem B919259 : Blo 362758 919259 := bstep (se 1 (by rfl) ⟨689444, by rfl⟩ : syracuseStep 919259 = 1378889) B1378889
theorem B12650269 : Blo 362758 12650269 := bstep (se 3 (by rfl) ⟨2371925, by rfl⟩ : syracuseStep 12650269 = 4743851) B4743851
theorem B1181537 : Blo 362758 1181537 := bstep (se 2 (by rfl) ⟨443076, by rfl⟩ : syracuseStep 1181537 = 886153) B886153
theorem B4786295 : Blo 362758 4786295 := bstep (se 1 (by rfl) ⟨3589721, by rfl⟩ : syracuseStep 4786295 = 7179443) B7179443
theorem B3508343 : Blo 362758 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B460991 : Blo 362758 460991 := bstep (se 1 (by rfl) ⟨345743, by rfl⟩ : syracuseStep 460991 = 691487) B691487
theorem B821483 : Blo 362758 821483 := bstep (se 1 (by rfl) ⟨616112, by rfl⟩ : syracuseStep 821483 = 1232225) B1232225
theorem B624875 : Blo 362758 624875 := bstep (se 1 (by rfl) ⟨468656, by rfl⟩ : syracuseStep 624875 = 937313) B937313
theorem B362799 : Blo 362758 362799 := bstep (se 1 (by rfl) ⟨272099, by rfl⟩ : syracuseStep 362799 = 544199) B544199
theorem B2951471 : Blo 362758 2951471 := bstep (se 1 (by rfl) ⟨2213603, by rfl⟩ : syracuseStep 2951471 = 4427207) B4427207
theorem B1837403 : Blo 362758 1837403 := bstep (se 1 (by rfl) ⟨1378052, by rfl⟩ : syracuseStep 1837403 = 2756105) B2756105
theorem B363035 : Blo 362758 363035 := bstep (se 1 (by rfl) ⟨272276, by rfl⟩ : syracuseStep 363035 = 544553) B544553
theorem B363039 : Blo 362758 363039 := bstep (se 1 (by rfl) ⟨272279, by rfl⟩ : syracuseStep 363039 = 544559) B544559
theorem B363355 : Blo 362758 363355 := bstep (se 1 (by rfl) ⟨272516, by rfl⟩ : syracuseStep 363355 = 545033) B545033
theorem B363423 : Blo 362758 363423 := bstep (se 1 (by rfl) ⟨272567, by rfl⟩ : syracuseStep 363423 = 545135) B545135
theorem B920555 : Blo 362758 920555 := bstep (se 1 (by rfl) ⟨690416, by rfl⟩ : syracuseStep 920555 = 1380833) B1380833
theorem B363567 : Blo 362758 363567 := bstep (se 1 (by rfl) ⟨272675, by rfl⟩ : syracuseStep 363567 = 545351) B545351
theorem B363591 : Blo 362758 363591 := bstep (se 1 (by rfl) ⟨272693, by rfl⟩ : syracuseStep 363591 = 545387) B545387
theorem B2329823 : Blo 362758 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B363743 : Blo 362758 363743 := bstep (se 1 (by rfl) ⟨272807, by rfl⟩ : syracuseStep 363743 = 545615) B545615
theorem B3116339 : Blo 362758 3116339 := bstep (se 1 (by rfl) ⟨2337254, by rfl⟩ : syracuseStep 3116339 = 4674509) B4674509
theorem B1379663 : Blo 362758 1379663 := bstep (se 1 (by rfl) ⟨1034747, by rfl⟩ : syracuseStep 1379663 = 2069495) B2069495
theorem B364007 : Blo 362758 364007 := bstep (se 1 (by rfl) ⟨273005, by rfl⟩ : syracuseStep 364007 = 546011) B546011
theorem B822779 : Blo 362758 822779 := bstep (se 1 (by rfl) ⟨617084, by rfl⟩ : syracuseStep 822779 = 1234169) B1234169
theorem B364123 : Blo 362758 364123 := bstep (se 1 (by rfl) ⟨273092, by rfl⟩ : syracuseStep 364123 = 546185) B546185
theorem B1838699 : Blo 362758 1838699 := bstep (se 1 (by rfl) ⟨1379024, by rfl⟩ : syracuseStep 1838699 = 2758049) B2758049
theorem B1248875 : Blo 362758 1248875 := bstep (se 1 (by rfl) ⟨936656, by rfl⟩ : syracuseStep 1248875 = 1873313) B1873313
theorem B822959 : Blo 362758 822959 := bstep (se 1 (by rfl) ⟨617219, by rfl⟩ : syracuseStep 822959 = 1234439) B1234439
theorem B364359 : Blo 362758 364359 := bstep (se 1 (by rfl) ⟨273269, by rfl⟩ : syracuseStep 364359 = 546539) B546539
theorem B364511 : Blo 362758 364511 := bstep (se 1 (by rfl) ⟨273383, by rfl⟩ : syracuseStep 364511 = 546767) B546767
theorem B790651 : Blo 362758 790651 := bstep (se 1 (by rfl) ⟨592988, by rfl⟩ : syracuseStep 790651 = 1185977) B1185977
theorem B364775 : Blo 362758 364775 := bstep (se 1 (by rfl) ⟨273581, by rfl⟩ : syracuseStep 364775 = 547163) B547163
theorem B823607 : Blo 362758 823607 := bstep (se 1 (by rfl) ⟨617705, by rfl⟩ : syracuseStep 823607 = 1235411) B1235411
theorem B364927 : Blo 362758 364927 := bstep (se 1 (by rfl) ⟨273695, by rfl⟩ : syracuseStep 364927 = 547391) B547391
theorem B823679 : Blo 362758 823679 := bstep (se 1 (by rfl) ⟨617759, by rfl⟩ : syracuseStep 823679 = 1235519) B1235519
theorem B365007 : Blo 362758 365007 := bstep (se 1 (by rfl) ⟨273755, by rfl⟩ : syracuseStep 365007 = 547511) B547511
theorem B7082497 : Blo 362758 7082497 := bstep (se 2 (by rfl) ⟨2655936, by rfl⟩ : syracuseStep 7082497 = 5311873) B5311873
theorem B2069063 : Blo 362758 2069063 := bstep (se 1 (by rfl) ⟨1551797, by rfl⟩ : syracuseStep 2069063 = 3103595) B3103595
theorem B365159 : Blo 362758 365159 := bstep (se 1 (by rfl) ⟨273869, by rfl⟩ : syracuseStep 365159 = 547739) B547739
theorem B365423 : Blo 362758 365423 := bstep (se 1 (by rfl) ⟨274067, by rfl⟩ : syracuseStep 365423 = 548135) B548135
theorem B13308785 : Blo 362758 13308785 := bstep (se 2 (by rfl) ⟨4990794, by rfl⟩ : syracuseStep 13308785 = 9981589) B9981589
theorem B365479 : Blo 362758 365479 := bstep (se 1 (by rfl) ⟨274109, by rfl⟩ : syracuseStep 365479 = 548219) B548219
theorem B365563 : Blo 362758 365563 := bstep (se 1 (by rfl) ⟨274172, by rfl⟩ : syracuseStep 365563 = 548345) B548345
theorem B365631 : Blo 362758 365631 := bstep (se 1 (by rfl) ⟨274223, by rfl⟩ : syracuseStep 365631 = 548447) B548447
theorem B693355 : Blo 362758 693355 := bstep (se 1 (by rfl) ⟨520016, by rfl⟩ : syracuseStep 693355 = 1040033) B1040033
theorem B365775 : Blo 362758 365775 := bstep (se 1 (by rfl) ⟨274331, by rfl⟩ : syracuseStep 365775 = 548663) B548663
theorem B4199633 : Blo 362758 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B9934073 : Blo 362758 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B1840481 : Blo 362758 1840481 := bstep (se 2 (by rfl) ⟨690180, by rfl⟩ : syracuseStep 1840481 = 1380361) B1380361
theorem B923035 : Blo 362758 923035 := bstep (se 1 (by rfl) ⟨692276, by rfl⟩ : syracuseStep 923035 = 1384553) B1384553
theorem B693659 : Blo 362758 693659 := bstep (se 1 (by rfl) ⟨520244, by rfl⟩ : syracuseStep 693659 = 1040489) B1040489
theorem B365979 : Blo 362758 365979 := bstep (se 1 (by rfl) ⟨274484, by rfl⟩ : syracuseStep 365979 = 548969) B548969
theorem B1381819 : Blo 362758 1381819 := bstep (se 1 (by rfl) ⟨1036364, by rfl⟩ : syracuseStep 1381819 = 2072729) B2072729
theorem B824903 : Blo 362758 824903 := bstep (se 1 (by rfl) ⟨618677, by rfl⟩ : syracuseStep 824903 = 1237355) B1237355
theorem B366191 : Blo 362758 366191 := bstep (se 1 (by rfl) ⟨274643, by rfl⟩ : syracuseStep 366191 = 549287) B549287
theorem B366247 : Blo 362758 366247 := bstep (se 1 (by rfl) ⟨274685, by rfl⟩ : syracuseStep 366247 = 549371) B549371
theorem B366331 : Blo 362758 366331 := bstep (se 1 (by rfl) ⟨274748, by rfl⟩ : syracuseStep 366331 = 549497) B549497
theorem B825083 : Blo 362758 825083 := bstep (se 1 (by rfl) ⟨618812, by rfl⟩ : syracuseStep 825083 = 1237625) B1237625
theorem B366367 : Blo 362758 366367 := bstep (se 1 (by rfl) ⟨274775, by rfl⟩ : syracuseStep 366367 = 549551) B549551
theorem B366399 : Blo 362758 366399 := bstep (se 1 (by rfl) ⟨274799, by rfl⟩ : syracuseStep 366399 = 549599) B549599
theorem B366575 : Blo 362758 366575 := bstep (se 1 (by rfl) ⟨274931, by rfl⟩ : syracuseStep 366575 = 549863) B549863
theorem B366747 : Blo 362758 366747 := bstep (se 1 (by rfl) ⟨275060, by rfl⟩ : syracuseStep 366747 = 550121) B550121
theorem B694433 : Blo 362758 694433 := bstep (se 2 (by rfl) ⟨260412, by rfl⟩ : syracuseStep 694433 = 520825) B520825
theorem B4692755 : Blo 362758 4692755 := bstep (se 1 (by rfl) ⟨3519566, by rfl⟩ : syracuseStep 4692755 = 7039133) B7039133
theorem B2759507 : Blo 362758 2759507 := bstep (se 1 (by rfl) ⟨2069630, by rfl⟩ : syracuseStep 2759507 = 4139261) B4139261
theorem B1743929 : Blo 362758 1743929 := bstep (se 2 (by rfl) ⟨653973, by rfl⟩ : syracuseStep 1743929 = 1307947) B1307947
theorem B7905185 : Blo 362758 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B3940487 : Blo 362758 3940487 := bstep (se 1 (by rfl) ⟨2955365, by rfl⟩ : syracuseStep 3940487 = 5910731) B5910731
theorem B1384735 : Blo 362758 1384735 := bstep (se 1 (by rfl) ⟨1038551, by rfl⟩ : syracuseStep 1384735 = 2077103) B2077103
theorem B2368061 : Blo 362758 2368061 := bstep (se 3 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 2368061 = 888023) B888023
theorem B6202331 : Blo 362758 6202331 := bstep (se 1 (by rfl) ⟨4651748, by rfl⟩ : syracuseStep 6202331 = 9303497) B9303497
theorem B1745945 : Blo 362758 1745945 := bstep (se 2 (by rfl) ⟨654729, by rfl⟩ : syracuseStep 1745945 = 1309459) B1309459
theorem B2630681 : Blo 362758 2630681 := bstep (se 2 (by rfl) ⟨986505, by rfl⟩ : syracuseStep 2630681 = 1973011) B1973011
theorem B4400335 : Blo 362758 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B2139769 : Blo 362758 2139769 := bstep (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) B1604827
theorem B2074643 : Blo 362758 2074643 := bstep (se 1 (by rfl) ⟨1555982, by rfl⟩ : syracuseStep 2074643 = 3111965) B3111965
theorem B928057 : Blo 362758 928057 := bstep (se 2 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 928057 = 696043) B696043
theorem B12003713 : Blo 362758 12003713 := bstep (se 2 (by rfl) ⟨4501392, by rfl⟩ : syracuseStep 12003713 = 9002785) B9002785
theorem B1845665 : Blo 362758 1845665 := bstep (se 2 (by rfl) ⟨692124, by rfl⟩ : syracuseStep 1845665 = 1384249) B1384249
theorem B1846637 : Blo 362758 1846637 := bstep (se 3 (by rfl) ⟨346244, by rfl⟩ : syracuseStep 1846637 = 692489) B692489
theorem B1486799 : Blo 362758 1486799 := bstep (se 1 (by rfl) ⟨1115099, by rfl⟩ : syracuseStep 1486799 = 2230199) B2230199
theorem B733151 : Blo 362758 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B1224827 : Blo 362758 1224827 := bstep (se 1 (by rfl) ⟨918620, by rfl⟩ : syracuseStep 1224827 = 1837241) B1837241
theorem B8859779 : Blo 362758 8859779 := bstep (se 1 (by rfl) ⟨6644834, by rfl⟩ : syracuseStep 8859779 = 13289669) B13289669
theorem B2502845 : Blo 362758 2502845 := bstep (se 3 (by rfl) ⟨469283, by rfl⟩ : syracuseStep 2502845 = 938567) B938567
theorem B11350273 : Blo 362758 11350273 := bstep (se 2 (by rfl) ⟨4256352, by rfl⟩ : syracuseStep 11350273 = 8512705) B8512705
theorem B1224989 : Blo 362758 1224989 := bstep (se 3 (by rfl) ⟨229685, by rfl⟩ : syracuseStep 1224989 = 459371) B459371
theorem B1225097 : Blo 362758 1225097 := bstep (se 2 (by rfl) ⟨459411, by rfl⟩ : syracuseStep 1225097 = 918823) B918823
theorem B5485391 : Blo 362758 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B2077811 : Blo 362758 2077811 := bstep (se 1 (by rfl) ⟨1558358, by rfl⟩ : syracuseStep 2077811 = 3116717) B3116717
theorem B1226015 : Blo 362758 1226015 := bstep (se 1 (by rfl) ⟨919511, by rfl⟩ : syracuseStep 1226015 = 1839023) B1839023
theorem B1390081 : Blo 362758 1390081 := bstep (se 2 (by rfl) ⟨521280, by rfl⟩ : syracuseStep 1390081 = 1042561) B1042561
theorem B10499651 : Blo 362758 10499651 := bstep (se 1 (by rfl) ⟨7874738, by rfl⟩ : syracuseStep 10499651 = 15749477) B15749477
theorem B2340535 : Blo 362758 2340535 := bstep (se 1 (by rfl) ⟨1755401, by rfl⟩ : syracuseStep 2340535 = 3510803) B3510803
theorem B5912281 : Blo 362758 5912281 := bstep (se 2 (by rfl) ⟨2217105, by rfl⟩ : syracuseStep 5912281 = 4434211) B4434211
theorem B1849067 : Blo 362758 1849067 := bstep (se 1 (by rfl) ⟨1386800, by rfl⟩ : syracuseStep 1849067 = 2773601) B2773601
theorem B1751003 : Blo 362758 1751003 := bstep (se 1 (by rfl) ⟨1313252, by rfl⟩ : syracuseStep 1751003 = 2626505) B2626505
theorem B1391327 : Blo 362758 1391327 := bstep (se 1 (by rfl) ⟨1043495, by rfl⟩ : syracuseStep 1391327 = 2086991) B2086991
theorem B6700103 : Blo 362758 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B1227905 : Blo 362758 1227905 := bstep (se 2 (by rfl) ⟨460464, by rfl⟩ : syracuseStep 1227905 = 920929) B920929
theorem B1850525 : Blo 362758 1850525 := bstep (se 3 (by rfl) ⟨346973, by rfl⟩ : syracuseStep 1850525 = 693947) B693947
theorem B1227959 : Blo 362758 1227959 := bstep (se 1 (by rfl) ⟨920969, by rfl⟩ : syracuseStep 1227959 = 1841939) B1841939
theorem B933331 : Blo 362758 933331 := bstep (se 1 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 933331 = 1399997) B1399997
theorem B409063 : Blo 362758 409063 := bstep (se 1 (by rfl) ⟨306797, by rfl⟩ : syracuseStep 409063 = 613595) B613595
theorem B1555949 : Blo 362758 1555949 := bstep (se 3 (by rfl) ⟨291740, by rfl⟩ : syracuseStep 1555949 = 583481) B583481
theorem B1982333 : Blo 362758 1982333 := bstep (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) B743375
theorem B1228715 : Blo 362758 1228715 := bstep (se 1 (by rfl) ⟨921536, by rfl⟩ : syracuseStep 1228715 = 1843073) B1843073
theorem B409567 : Blo 362758 409567 := bstep (se 1 (by rfl) ⟨307175, by rfl⟩ : syracuseStep 409567 = 614351) B614351
theorem B1163297 : Blo 362758 1163297 := bstep (se 2 (by rfl) ⟨436236, by rfl⟩ : syracuseStep 1163297 = 872473) B872473
theorem B2342945 : Blo 362758 2342945 := bstep (se 2 (by rfl) ⟨878604, by rfl⟩ : syracuseStep 2342945 = 1757209) B1757209
theorem B1229255 : Blo 362758 1229255 := bstep (se 1 (by rfl) ⟨921941, by rfl⟩ : syracuseStep 1229255 = 1843883) B1843883
theorem B410215 : Blo 362758 410215 := bstep (se 1 (by rfl) ⟨307661, by rfl⟩ : syracuseStep 410215 = 615323) B615323
theorem B1229579 : Blo 362758 1229579 := bstep (se 1 (by rfl) ⟨922184, by rfl⟩ : syracuseStep 1229579 = 1844369) B1844369
theorem B8864731 : Blo 362758 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B1229849 : Blo 362758 1229849 := bstep (se 2 (by rfl) ⟨461193, by rfl⟩ : syracuseStep 1229849 = 922387) B922387
theorem B1230497 : Blo 362758 1230497 := bstep (se 2 (by rfl) ⟨461436, by rfl⟩ : syracuseStep 1230497 = 922873) B922873
theorem B2475805 : Blo 362758 2475805 := bstep (se 3 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 2475805 = 928427) B928427
theorem B1165117 : Blo 362758 1165117 := bstep (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) B436919
theorem B1231199 : Blo 362758 1231199 := bstep (se 1 (by rfl) ⟨923399, by rfl⟩ : syracuseStep 1231199 = 1846799) B1846799
theorem B1034657 : Blo 362758 1034657 := bstep (se 2 (by rfl) ⟨387996, by rfl⟩ : syracuseStep 1034657 = 775993) B775993
theorem B1231361 : Blo 362758 1231361 := bstep (se 2 (by rfl) ⟨461760, by rfl⟩ : syracuseStep 1231361 = 923521) B923521
theorem B1166167 : Blo 362758 1166167 := bstep (se 1 (by rfl) ⟨874625, by rfl⟩ : syracuseStep 1166167 = 1749251) B1749251
theorem B1231847 : Blo 362758 1231847 := bstep (se 1 (by rfl) ⟨923885, by rfl⟩ : syracuseStep 1231847 = 1847771) B1847771
theorem B1133615 : Blo 362758 1133615 := bstep (se 1 (by rfl) ⟨850211, by rfl⟩ : syracuseStep 1133615 = 1700423) B1700423
theorem B9653411 : Blo 362758 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B1232171 : Blo 362758 1232171 := bstep (se 1 (by rfl) ⟨924128, by rfl⟩ : syracuseStep 1232171 = 1848257) B1848257
theorem B544169 : Blo 362758 544169 := bstep (se 2 (by rfl) ⟨204063, by rfl⟩ : syracuseStep 544169 = 408127) B408127
theorem B1232441 : Blo 362758 1232441 := bstep (se 2 (by rfl) ⟨462165, by rfl⟩ : syracuseStep 1232441 = 924331) B924331
theorem B544319 : Blo 362758 544319 := bstep (se 1 (by rfl) ⟨408239, by rfl⟩ : syracuseStep 544319 = 816479) B816479
theorem B1560221 : Blo 362758 1560221 := bstep (se 3 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 1560221 = 585083) B585083
theorem B4214585 : Blo 362758 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B544583 : Blo 362758 544583 := bstep (se 1 (by rfl) ⟨408437, by rfl⟩ : syracuseStep 544583 = 816875) B816875
theorem B544667 : Blo 362758 544667 := bstep (se 1 (by rfl) ⟨408500, by rfl⟩ : syracuseStep 544667 = 817001) B817001
theorem B1855709 : Blo 362758 1855709 := bstep (se 3 (by rfl) ⟨347945, by rfl⟩ : syracuseStep 1855709 = 695891) B695891
theorem B1855871 : Blo 362758 1855871 := bstep (se 1 (by rfl) ⟨1391903, by rfl⟩ : syracuseStep 1855871 = 2783807) B2783807
theorem B545231 : Blo 362758 545231 := bstep (se 1 (by rfl) ⟨408923, by rfl⟩ : syracuseStep 545231 = 817847) B817847
theorem B545273 : Blo 362758 545273 := bstep (se 2 (by rfl) ⟨204477, by rfl⟩ : syracuseStep 545273 = 408955) B408955
theorem B545375 : Blo 362758 545375 := bstep (se 1 (by rfl) ⟨409031, by rfl⟩ : syracuseStep 545375 = 818063) B818063
theorem B6771377 : Blo 362758 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B4510505 : Blo 362758 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B2085851 : Blo 362758 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B2413577 : Blo 362758 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B1561639 : Blo 362758 1561639 := bstep (se 1 (by rfl) ⟨1171229, by rfl⟩ : syracuseStep 1561639 = 2342459) B2342459
theorem B1561655 : Blo 362758 1561655 := bstep (se 1 (by rfl) ⟨1171241, by rfl⟩ : syracuseStep 1561655 = 2342483) B2342483
theorem B545855 : Blo 362758 545855 := bstep (se 1 (by rfl) ⟨409391, by rfl⟩ : syracuseStep 545855 = 818783) B818783
theorem B775241 : Blo 362758 775241 := bstep (se 2 (by rfl) ⟨290715, by rfl⟩ : syracuseStep 775241 = 581431) B581431
theorem B545897 : Blo 362758 545897 := bstep (se 2 (by rfl) ⟨204711, by rfl⟩ : syracuseStep 545897 = 409423) B409423
theorem B545999 : Blo 362758 545999 := bstep (se 1 (by rfl) ⟨409499, by rfl⟩ : syracuseStep 545999 = 818999) B818999
theorem B546203 : Blo 362758 546203 := bstep (se 1 (by rfl) ⟨409652, by rfl⟩ : syracuseStep 546203 = 819305) B819305
theorem B1234331 : Blo 362758 1234331 := bstep (se 1 (by rfl) ⟨925748, by rfl⟩ : syracuseStep 1234331 = 1851497) B1851497
theorem B1594811 : Blo 362758 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B546425 : Blo 362758 546425 := bstep (se 2 (by rfl) ⟨204909, by rfl⟩ : syracuseStep 546425 = 409819) B409819
theorem B546527 : Blo 362758 546527 := bstep (se 1 (by rfl) ⟨409895, by rfl⟩ : syracuseStep 546527 = 819791) B819791
theorem B6215453 : Blo 362758 6215453 := bstep (se 3 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 6215453 = 2330795) B2330795
theorem B294508331 : Blo 362758 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B546623 : Blo 362758 546623 := bstep (se 1 (by rfl) ⟨409967, by rfl⟩ : syracuseStep 546623 = 819935) B819935
theorem B9983897 : Blo 362758 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B546791 : Blo 362758 546791 := bstep (se 1 (by rfl) ⟨410093, by rfl⟩ : syracuseStep 546791 = 820187) B820187
theorem B546809 : Blo 362758 546809 := bstep (se 2 (by rfl) ⟨205053, by rfl⟩ : syracuseStep 546809 = 410107) B410107
theorem B546911 : Blo 362758 546911 := bstep (se 1 (by rfl) ⟨410183, by rfl⟩ : syracuseStep 546911 = 820367) B820367
theorem B1235087 : Blo 362758 1235087 := bstep (se 1 (by rfl) ⟨926315, by rfl⟩ : syracuseStep 1235087 = 1852631) B1852631
theorem B546971 : Blo 362758 546971 := bstep (se 1 (by rfl) ⟨410228, by rfl⟩ : syracuseStep 546971 = 820457) B820457
theorem B547007 : Blo 362758 547007 := bstep (se 1 (by rfl) ⟨410255, by rfl⟩ : syracuseStep 547007 = 820511) B820511
theorem B547049 : Blo 362758 547049 := bstep (se 2 (by rfl) ⟨205143, by rfl⟩ : syracuseStep 547049 = 410287) B410287
theorem B1562921 : Blo 362758 1562921 := bstep (se 2 (by rfl) ⟨586095, by rfl⟩ : syracuseStep 1562921 = 1172191) B1172191
theorem B612731 : Blo 362758 612731 := bstep (se 1 (by rfl) ⟨459548, by rfl⟩ : syracuseStep 612731 = 919097) B919097
theorem B547355 : Blo 362758 547355 := bstep (se 1 (by rfl) ⟨410516, by rfl⟩ : syracuseStep 547355 = 821033) B821033
theorem B547433 : Blo 362758 547433 := bstep (se 2 (by rfl) ⟨205287, by rfl⟩ : syracuseStep 547433 = 410575) B410575
theorem B613001 : Blo 362758 613001 := bstep (se 2 (by rfl) ⟨229875, by rfl⟩ : syracuseStep 613001 = 459751) B459751
theorem B5069873 : Blo 362758 5069873 := bstep (se 2 (by rfl) ⟨1901202, by rfl⟩ : syracuseStep 5069873 = 3802405) B3802405
theorem B547961 : Blo 362758 547961 := bstep (se 2 (by rfl) ⟨205485, by rfl⟩ : syracuseStep 547961 = 410971) B410971
theorem B548063 : Blo 362758 548063 := bstep (se 1 (by rfl) ⟨411047, by rfl⟩ : syracuseStep 548063 = 822095) B822095
theorem B1236221 : Blo 362758 1236221 := bstep (se 3 (by rfl) ⟨231791, by rfl⟩ : syracuseStep 1236221 = 463583) B463583
theorem B548105 : Blo 362758 548105 := bstep (se 2 (by rfl) ⟨205539, by rfl⟩ : syracuseStep 548105 = 411079) B411079
theorem B548207 : Blo 362758 548207 := bstep (se 1 (by rfl) ⟨411155, by rfl⟩ : syracuseStep 548207 = 822311) B822311
theorem B548327 : Blo 362758 548327 := bstep (se 1 (by rfl) ⟨411245, by rfl⟩ : syracuseStep 548327 = 822491) B822491
theorem B548459 : Blo 362758 548459 := bstep (se 1 (by rfl) ⟨411344, by rfl⟩ : syracuseStep 548459 = 822689) B822689
theorem B548585 : Blo 362758 548585 := bstep (se 2 (by rfl) ⟨205719, by rfl⟩ : syracuseStep 548585 = 411439) B411439
theorem B548729 : Blo 362758 548729 := bstep (se 2 (by rfl) ⟨205773, by rfl⟩ : syracuseStep 548729 = 411547) B411547
theorem B548831 : Blo 362758 548831 := bstep (se 1 (by rfl) ⟨411623, by rfl⟩ : syracuseStep 548831 = 823247) B823247
theorem B1237031 : Blo 362758 1237031 := bstep (se 1 (by rfl) ⟨927773, by rfl⟩ : syracuseStep 1237031 = 1855547) B1855547
theorem B876683 : Blo 362758 876683 := bstep (se 1 (by rfl) ⟨657512, by rfl⟩ : syracuseStep 876683 = 1315025) B1315025
theorem B614587 : Blo 362758 614587 := bstep (se 1 (by rfl) ⟨460940, by rfl⟩ : syracuseStep 614587 = 921881) B921881
theorem B549083 : Blo 362758 549083 := bstep (se 1 (by rfl) ⟨411812, by rfl⟩ : syracuseStep 549083 = 823625) B823625
theorem B549095 : Blo 362758 549095 := bstep (se 1 (by rfl) ⟨411821, by rfl⟩ : syracuseStep 549095 = 823643) B823643
theorem B614783 : Blo 362758 614783 := bstep (se 1 (by rfl) ⟨461087, by rfl⟩ : syracuseStep 614783 = 922175) B922175
theorem B549257 : Blo 362758 549257 := bstep (se 2 (by rfl) ⟨205971, by rfl⟩ : syracuseStep 549257 = 411943) B411943
theorem B549353 : Blo 362758 549353 := bstep (se 2 (by rfl) ⟨206007, by rfl⟩ : syracuseStep 549353 = 412015) B412015
theorem B549479 : Blo 362758 549479 := bstep (se 1 (by rfl) ⟨412109, by rfl⟩ : syracuseStep 549479 = 824219) B824219
theorem B21652103 : Blo 362758 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B1237679 : Blo 362758 1237679 := bstep (se 1 (by rfl) ⟨928259, by rfl⟩ : syracuseStep 1237679 = 1856519) B1856519
theorem B549611 : Blo 362758 549611 := bstep (se 1 (by rfl) ⟨412208, by rfl⟩ : syracuseStep 549611 = 824417) B824417
theorem B1041149 : Blo 362758 1041149 := bstep (se 3 (by rfl) ⟨195215, by rfl⟩ : syracuseStep 1041149 = 390431) B390431
theorem B779017 : Blo 362758 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B549641 : Blo 362758 549641 := bstep (se 2 (by rfl) ⟨206115, by rfl⟩ : syracuseStep 549641 = 412231) B412231
theorem B615215 : Blo 362758 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B549743 : Blo 362758 549743 := bstep (se 1 (by rfl) ⟨412307, by rfl⟩ : syracuseStep 549743 = 824615) B824615
theorem B1106855 : Blo 362758 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B549995 : Blo 362758 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B583289 : Blo 362758 583289 := bstep (se 2 (by rfl) ⟨218733, by rfl⟩ : syracuseStep 583289 = 437467) B437467
theorem B1173113 : Blo 362758 1173113 := bstep (se 2 (by rfl) ⟨439917, by rfl⟩ : syracuseStep 1173113 = 879835) B879835
theorem B616187 : Blo 362758 616187 := bstep (se 1 (by rfl) ⟨462140, by rfl⟩ : syracuseStep 616187 = 924281) B924281
theorem B3106633 : Blo 362758 3106633 := bstep (se 2 (by rfl) ⟨1164987, by rfl⟩ : syracuseStep 3106633 = 2329975) B2329975
theorem B714575 : Blo 362758 714575 := bstep (se 1 (by rfl) ⟨535931, by rfl⟩ : syracuseStep 714575 = 1071863) B1071863
theorem B616423 : Blo 362758 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B2615287 : Blo 362758 2615287 := bstep (se 1 (by rfl) ⟨1961465, by rfl⟩ : syracuseStep 2615287 = 3922931) B3922931
theorem B616639 : Blo 362758 616639 := bstep (se 1 (by rfl) ⟨462479, by rfl⟩ : syracuseStep 616639 = 924959) B924959
theorem B1862027 : Blo 362758 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B1043131 : Blo 362758 1043131 := bstep (se 1 (by rfl) ⟨782348, by rfl⟩ : syracuseStep 1043131 = 1564697) B1564697
theorem B617375 : Blo 362758 617375 := bstep (se 1 (by rfl) ⟨463031, by rfl⟩ : syracuseStep 617375 = 926063) B926063
theorem B1174625 : Blo 362758 1174625 := bstep (se 2 (by rfl) ⟨440484, by rfl⟩ : syracuseStep 1174625 = 880969) B880969
theorem B617807 : Blo 362758 617807 := bstep (se 1 (by rfl) ⟨463355, by rfl⟩ : syracuseStep 617807 = 926711) B926711
theorem B781751 : Blo 362758 781751 := bstep (se 1 (by rfl) ⟨586313, by rfl⟩ : syracuseStep 781751 = 1172627) B1172627
theorem B585211 : Blo 362758 585211 := bstep (se 1 (by rfl) ⟨438908, by rfl⟩ : syracuseStep 585211 = 877817) B877817
theorem B519743 : Blo 362758 519743 := bstep (se 1 (by rfl) ⟨389807, by rfl⟩ : syracuseStep 519743 = 779615) B779615
theorem B1437257 : Blo 362758 1437257 := bstep (se 2 (by rfl) ⟨538971, by rfl⟩ : syracuseStep 1437257 = 1077943) B1077943
theorem B16805501 : Blo 362758 16805501 := bstep (se 3 (by rfl) ⟨3151031, by rfl⟩ : syracuseStep 16805501 = 6302063) B6302063
theorem B3764029 : Blo 362758 3764029 := bstep (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) B1411511
theorem B2781377 : Blo 362758 2781377 := bstep (se 2 (by rfl) ⟨1043016, by rfl⟩ : syracuseStep 2781377 = 2086033) B2086033
theorem B520939 : Blo 362758 520939 := bstep (se 1 (by rfl) ⟨390704, by rfl⟩ : syracuseStep 520939 = 781409) B781409
theorem B521839 : Blo 362758 521839 := bstep (se 1 (by rfl) ⟨391379, by rfl⟩ : syracuseStep 521839 = 782759) B782759
theorem B2488009 : Blo 362758 2488009 := bstep (se 2 (by rfl) ⟨933003, by rfl⟩ : syracuseStep 2488009 = 1866007) B1866007
theorem B817127 : Blo 362758 817127 := bstep (se 1 (by rfl) ⟨612845, by rfl⟩ : syracuseStep 817127 = 1225691) B1225691
theorem B817145 : Blo 362758 817145 := bstep (se 2 (by rfl) ⟨306429, by rfl⟩ : syracuseStep 817145 = 612859) B612859
theorem B1112057 : Blo 362758 1112057 := bstep (se 2 (by rfl) ⟨417021, by rfl⟩ : syracuseStep 1112057 = 834043) B834043
theorem B817235 : Blo 362758 817235 := bstep (se 1 (by rfl) ⟨612926, by rfl⟩ : syracuseStep 817235 = 1225853) B1225853
theorem B817307 : Blo 362758 817307 := bstep (se 1 (by rfl) ⟨612980, by rfl⟩ : syracuseStep 817307 = 1225961) B1225961
theorem B4159673 : Blo 362758 4159673 := bstep (se 2 (by rfl) ⟨1559877, by rfl⟩ : syracuseStep 4159673 = 3119755) B3119755
theorem B817415 : Blo 362758 817415 := bstep (se 1 (by rfl) ⟨613061, by rfl⟩ : syracuseStep 817415 = 1226123) B1226123
theorem B817721 : Blo 362758 817721 := bstep (se 2 (by rfl) ⟨306645, by rfl⟩ : syracuseStep 817721 = 613291) B613291
theorem B654383 : Blo 362758 654383 := bstep (se 1 (by rfl) ⟨490787, by rfl⟩ : syracuseStep 654383 = 981575) B981575
theorem B2620505 : Blo 362758 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B3210329 : Blo 362758 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B818441 : Blo 362758 818441 := bstep (se 2 (by rfl) ⟨306915, by rfl⟩ : syracuseStep 818441 = 613831) B613831
theorem B20053595 : Blo 362758 20053595 := bstep (se 1 (by rfl) ⟨15040196, by rfl⟩ : syracuseStep 20053595 = 30080393) B30080393
theorem B1966265 : Blo 362758 1966265 := bstep (se 2 (by rfl) ⟨737349, by rfl⟩ : syracuseStep 1966265 = 1474699) B1474699
theorem B819449 : Blo 362758 819449 := bstep (se 2 (by rfl) ⟨307293, by rfl⟩ : syracuseStep 819449 = 614587) B614587
theorem B819503 : Blo 362758 819503 := bstep (se 1 (by rfl) ⟨614627, by rfl⟩ : syracuseStep 819503 = 1229255) B1229255
theorem B2490743 : Blo 362758 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B819719 : Blo 362758 819719 := bstep (se 1 (by rfl) ⟨614789, by rfl⟩ : syracuseStep 819719 = 1229579) B1229579
theorem B819899 : Blo 362758 819899 := bstep (se 1 (by rfl) ⟨614924, by rfl⟩ : syracuseStep 819899 = 1229849) B1229849
theorem B820331 : Blo 362758 820331 := bstep (se 1 (by rfl) ⟨615248, by rfl⟩ : syracuseStep 820331 = 1230497) B1230497
theorem B787691 : Blo 362758 787691 := bstep (se 1 (by rfl) ⟨590768, by rfl⟩ : syracuseStep 787691 = 1181537) B1181537
theorem B1967647 : Blo 362758 1967647 := bstep (se 1 (by rfl) ⟨1475735, by rfl⟩ : syracuseStep 1967647 = 2951471) B2951471
theorem B820799 : Blo 362758 820799 := bstep (se 1 (by rfl) ⟨615599, by rfl⟩ : syracuseStep 820799 = 1231199) B1231199
theorem B5867113 : Blo 362758 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B689771 : Blo 362758 689771 := bstep (se 1 (by rfl) ⟨517328, by rfl⟩ : syracuseStep 689771 = 1034657) B1034657
theorem B820907 : Blo 362758 820907 := bstep (se 1 (by rfl) ⟨615680, by rfl⟩ : syracuseStep 820907 = 1231361) B1231361
theorem B821231 : Blo 362758 821231 := bstep (se 1 (by rfl) ⟨615923, by rfl⟩ : syracuseStep 821231 = 1231847) B1231847
theorem B755743 : Blo 362758 755743 := bstep (se 1 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 755743 = 1133615) B1133615
theorem B2853025 : Blo 362758 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B821447 : Blo 362758 821447 := bstep (se 1 (by rfl) ⟨616085, by rfl⟩ : syracuseStep 821447 = 1232171) B1232171
theorem B919775 : Blo 362758 919775 := bstep (se 1 (by rfl) ⟨689831, by rfl⟩ : syracuseStep 919775 = 1379663) B1379663
theorem B362779 : Blo 362758 362779 := bstep (se 1 (by rfl) ⟨272084, by rfl⟩ : syracuseStep 362779 = 544169) B544169
theorem B821627 : Blo 362758 821627 := bstep (se 1 (by rfl) ⟨616220, by rfl⟩ : syracuseStep 821627 = 1232441) B1232441
theorem B362879 : Blo 362758 362879 := bstep (se 1 (by rfl) ⟨272159, by rfl⟩ : syracuseStep 362879 = 544319) B544319
theorem B363055 : Blo 362758 363055 := bstep (se 1 (by rfl) ⟨272291, by rfl⟩ : syracuseStep 363055 = 544583) B544583
theorem B363111 : Blo 362758 363111 := bstep (se 1 (by rfl) ⟨272333, by rfl⟩ : syracuseStep 363111 = 544667) B544667
theorem B821897 : Blo 362758 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B822185 : Blo 362758 822185 := bstep (se 2 (by rfl) ⟨308319, by rfl⟩ : syracuseStep 822185 = 616639) B616639
theorem B363487 : Blo 362758 363487 := bstep (se 1 (by rfl) ⟨272615, by rfl⟩ : syracuseStep 363487 = 545231) B545231
theorem B363515 : Blo 362758 363515 := bstep (se 1 (by rfl) ⟨272636, by rfl⟩ : syracuseStep 363515 = 545273) B545273
theorem B1379375 : Blo 362758 1379375 := bstep (se 1 (by rfl) ⟨1034531, by rfl⟩ : syracuseStep 1379375 = 2069063) B2069063
theorem B363583 : Blo 362758 363583 := bstep (se 1 (by rfl) ⟨272687, by rfl⟩ : syracuseStep 363583 = 545375) B545375
theorem B363903 : Blo 362758 363903 := bstep (se 1 (by rfl) ⟨272927, by rfl⟩ : syracuseStep 363903 = 545855) B545855
theorem B363931 : Blo 362758 363931 := bstep (se 1 (by rfl) ⟨272948, by rfl⟩ : syracuseStep 363931 = 545897) B545897
theorem B363999 : Blo 362758 363999 := bstep (se 1 (by rfl) ⟨272999, by rfl⟩ : syracuseStep 363999 = 545999) B545999
theorem B6622715 : Blo 362758 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B822887 : Blo 362758 822887 := bstep (se 1 (by rfl) ⟨617165, by rfl⟩ : syracuseStep 822887 = 1234331) B1234331
theorem B364135 : Blo 362758 364135 := bstep (se 1 (by rfl) ⟨273101, by rfl⟩ : syracuseStep 364135 = 546203) B546203
theorem B462439 : Blo 362758 462439 := bstep (se 1 (by rfl) ⟨346829, by rfl⟩ : syracuseStep 462439 = 693659) B693659
theorem B364283 : Blo 362758 364283 := bstep (se 1 (by rfl) ⟨273212, by rfl⟩ : syracuseStep 364283 = 546425) B546425
theorem B364351 : Blo 362758 364351 := bstep (se 1 (by rfl) ⟨273263, by rfl⟩ : syracuseStep 364351 = 546527) B546527
theorem B364415 : Blo 362758 364415 := bstep (se 1 (by rfl) ⟨273311, by rfl⟩ : syracuseStep 364415 = 546623) B546623
theorem B6655931 : Blo 362758 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B364527 : Blo 362758 364527 := bstep (se 1 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 364527 = 546791) B546791
theorem B364539 : Blo 362758 364539 := bstep (se 1 (by rfl) ⟨273404, by rfl⟩ : syracuseStep 364539 = 546809) B546809
theorem B364607 : Blo 362758 364607 := bstep (se 1 (by rfl) ⟨273455, by rfl⟩ : syracuseStep 364607 = 546911) B546911
theorem B823391 : Blo 362758 823391 := bstep (se 1 (by rfl) ⟨617543, by rfl⟩ : syracuseStep 823391 = 1235087) B1235087
theorem B364647 : Blo 362758 364647 := bstep (se 1 (by rfl) ⟨273485, by rfl⟩ : syracuseStep 364647 = 546971) B546971
theorem B364671 : Blo 362758 364671 := bstep (se 1 (by rfl) ⟨273503, by rfl⟩ : syracuseStep 364671 = 547007) B547007
theorem B364699 : Blo 362758 364699 := bstep (se 1 (by rfl) ⟨273524, by rfl⟩ : syracuseStep 364699 = 547049) B547049
theorem B3936509 : Blo 362758 3936509 := bstep (se 3 (by rfl) ⟨738095, by rfl⟩ : syracuseStep 3936509 = 1476191) B1476191
theorem B364903 : Blo 362758 364903 := bstep (se 1 (by rfl) ⟨273677, by rfl⟩ : syracuseStep 364903 = 547355) B547355
theorem B364955 : Blo 362758 364955 := bstep (se 1 (by rfl) ⟨273716, by rfl⟩ : syracuseStep 364955 = 547433) B547433
theorem B1839671 : Blo 362758 1839671 := bstep (se 1 (by rfl) ⟨1379753, by rfl⟩ : syracuseStep 1839671 = 2759507) B2759507
theorem B3379915 : Blo 362758 3379915 := bstep (se 1 (by rfl) ⟨2534936, by rfl⟩ : syracuseStep 3379915 = 5069873) B5069873
theorem B365307 : Blo 362758 365307 := bstep (se 1 (by rfl) ⟨273980, by rfl⟩ : syracuseStep 365307 = 547961) B547961
theorem B365375 : Blo 362758 365375 := bstep (se 1 (by rfl) ⟨274031, by rfl⟩ : syracuseStep 365375 = 548063) B548063
theorem B824147 : Blo 362758 824147 := bstep (se 1 (by rfl) ⟨618110, by rfl⟩ : syracuseStep 824147 = 1236221) B1236221
theorem B365403 : Blo 362758 365403 := bstep (se 1 (by rfl) ⟨274052, by rfl⟩ : syracuseStep 365403 = 548105) B548105
theorem B365471 : Blo 362758 365471 := bstep (se 1 (by rfl) ⟨274103, by rfl⟩ : syracuseStep 365471 = 548207) B548207
theorem B365551 : Blo 362758 365551 := bstep (se 1 (by rfl) ⟨274163, by rfl⟩ : syracuseStep 365551 = 548327) B548327
theorem B365639 : Blo 362758 365639 := bstep (se 1 (by rfl) ⟨274229, by rfl⟩ : syracuseStep 365639 = 548459) B548459
theorem B5018705 : Blo 362758 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B365723 : Blo 362758 365723 := bstep (se 1 (by rfl) ⟨274292, by rfl⟩ : syracuseStep 365723 = 548585) B548585
theorem B365819 : Blo 362758 365819 := bstep (se 1 (by rfl) ⟨274364, by rfl⟩ : syracuseStep 365819 = 548729) B548729
theorem B365887 : Blo 362758 365887 := bstep (se 1 (by rfl) ⟨274415, by rfl⟩ : syracuseStep 365887 = 548831) B548831
theorem B824687 : Blo 362758 824687 := bstep (se 1 (by rfl) ⟨618515, by rfl⟩ : syracuseStep 824687 = 1237031) B1237031
theorem B2626991 : Blo 362758 2626991 := bstep (se 1 (by rfl) ⟨1970243, by rfl⟩ : syracuseStep 2626991 = 3940487) B3940487
theorem B366055 : Blo 362758 366055 := bstep (se 1 (by rfl) ⟨274541, by rfl⟩ : syracuseStep 366055 = 549083) B549083
theorem B366063 : Blo 362758 366063 := bstep (se 1 (by rfl) ⟨274547, by rfl⟩ : syracuseStep 366063 = 549095) B549095
theorem B1054201 : Blo 362758 1054201 := bstep (se 2 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 1054201 = 790651) B790651
theorem B366171 : Blo 362758 366171 := bstep (se 1 (by rfl) ⟨274628, by rfl⟩ : syracuseStep 366171 = 549257) B549257
theorem B366235 : Blo 362758 366235 := bstep (se 1 (by rfl) ⟨274676, by rfl⟩ : syracuseStep 366235 = 549353) B549353
theorem B1578707 : Blo 362758 1578707 := bstep (se 1 (by rfl) ⟨1184030, by rfl⟩ : syracuseStep 1578707 = 2368061) B2368061
theorem B366319 : Blo 362758 366319 := bstep (se 1 (by rfl) ⟨274739, by rfl⟩ : syracuseStep 366319 = 549479) B549479
theorem B825119 : Blo 362758 825119 := bstep (se 1 (by rfl) ⟨618839, by rfl⟩ : syracuseStep 825119 = 1237679) B1237679
theorem B366407 : Blo 362758 366407 := bstep (se 1 (by rfl) ⟨274805, by rfl⟩ : syracuseStep 366407 = 549611) B549611
theorem B694099 : Blo 362758 694099 := bstep (se 1 (by rfl) ⟨520574, by rfl⟩ : syracuseStep 694099 = 1041149) B1041149
theorem B366427 : Blo 362758 366427 := bstep (se 1 (by rfl) ⟨274820, by rfl⟩ : syracuseStep 366427 = 549641) B549641
theorem B366495 : Blo 362758 366495 := bstep (se 1 (by rfl) ⟨274871, by rfl⟩ : syracuseStep 366495 = 549743) B549743
theorem B4134887 : Blo 362758 4134887 := bstep (se 1 (by rfl) ⟨3101165, by rfl⟩ : syracuseStep 4134887 = 6202331) B6202331
theorem B366663 : Blo 362758 366663 := bstep (se 1 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 366663 = 549995) B549995
theorem B694585 : Blo 362758 694585 := bstep (se 2 (by rfl) ⟨260469, by rfl⟩ : syracuseStep 694585 = 520939) B520939
theorem B1383095 : Blo 362758 1383095 := bstep (se 1 (by rfl) ⟨1037321, by rfl⟩ : syracuseStep 1383095 = 2074643) B2074643
theorem B924473 : Blo 362758 924473 := bstep (se 2 (by rfl) ⟨346677, by rfl⟩ : syracuseStep 924473 = 693355) B693355
theorem B8002475 : Blo 362758 8002475 := bstep (se 1 (by rfl) ⟨6001856, by rfl⟩ : syracuseStep 8002475 = 12003713) B12003713
theorem B1842425 : Blo 362758 1842425 := bstep (se 2 (by rfl) ⟨690909, by rfl⟩ : syracuseStep 1842425 = 1381819) B1381819
theorem B695785 : Blo 362758 695785 := bstep (se 2 (by rfl) ⟨260919, by rfl⟩ : syracuseStep 695785 = 521839) B521839
theorem B3120713 : Blo 362758 3120713 := bstep (se 2 (by rfl) ⟨1170267, by rfl⟩ : syracuseStep 3120713 = 2340535) B2340535
theorem B3317345 : Blo 362758 3317345 := bstep (se 2 (by rfl) ⟨1244004, by rfl⟩ : syracuseStep 3317345 = 2488009) B2488009
theorem B958171 : Blo 362758 958171 := bstep (se 1 (by rfl) ⟨718628, by rfl⟩ : syracuseStep 958171 = 1437257) B1437257
theorem B991199 : Blo 362758 991199 := bstep (se 1 (by rfl) ⟨743399, by rfl⟩ : syracuseStep 991199 = 1486799) B1486799
theorem B5906519 : Blo 362758 5906519 := bstep (se 1 (by rfl) ⟨4429889, by rfl⟩ : syracuseStep 5906519 = 8859779) B8859779
theorem B1745021 : Blo 362758 1745021 := bstep (se 3 (by rfl) ⟨327191, by rfl⟩ : syracuseStep 1745021 = 654383) B654383
theorem B3154565 : Blo 362758 3154565 := bstep (se 4 (by rfl) ⟨295740, by rfl⟩ : syracuseStep 3154565 = 591481) B591481
theorem B1385207 : Blo 362758 1385207 := bstep (se 1 (by rfl) ⟨1038905, by rfl⟩ : syracuseStep 1385207 = 2077811) B2077811
theorem B31532165 : Blo 362758 31532165 := bstep (se 4 (by rfl) ⟨2956140, by rfl⟩ : syracuseStep 31532165 = 5912281) B5912281
theorem B1385981 : Blo 362758 1385981 := bstep (se 3 (by rfl) ⟨259871, by rfl⟩ : syracuseStep 1385981 = 519743) B519743
theorem B927551 : Blo 362758 927551 := bstep (se 1 (by rfl) ⟨695663, by rfl⟩ : syracuseStep 927551 = 1391327) B1391327
theorem B4466735 : Blo 362758 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B1747003 : Blo 362758 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B2140219 : Blo 362758 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B5286221 : Blo 362758 5286221 := bstep (se 3 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 5286221 = 1982333) B1982333
theorem B3517415 : Blo 362758 3517415 := bstep (se 1 (by rfl) ⟨2638061, by rfl⟩ : syracuseStep 3517415 = 5276123) B5276123
theorem B2337767 : Blo 362758 2337767 := bstep (se 1 (by rfl) ⟨1753325, by rfl⟩ : syracuseStep 2337767 = 3506651) B3506651
theorem B2337821 : Blo 362758 2337821 := bstep (se 3 (by rfl) ⟨438341, by rfl⟩ : syracuseStep 2337821 = 876683) B876683
theorem B1485857 : Blo 362758 1485857 := bstep (se 2 (by rfl) ⟨557196, by rfl⟩ : syracuseStep 1485857 = 1114393) B1114393
theorem B1846313 : Blo 362758 1846313 := bstep (se 2 (by rfl) ⟨692367, by rfl⟩ : syracuseStep 1846313 = 1384735) B1384735
theorem B1748233 : Blo 362758 1748233 := bstep (se 2 (by rfl) ⟨655587, by rfl⟩ : syracuseStep 1748233 = 1311175) B1311175
theorem B2338895 : Blo 362758 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B1224935 : Blo 362758 1224935 := bstep (se 1 (by rfl) ⟨918701, by rfl⟩ : syracuseStep 1224935 = 1837403) B1837403
theorem B6435607 : Blo 362758 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B1553215 : Blo 362758 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B2077559 : Blo 362758 2077559 := bstep (se 1 (by rfl) ⟨1558169, by rfl⟩ : syracuseStep 2077559 = 3116339) B3116339
theorem B1225799 : Blo 362758 1225799 := bstep (se 1 (by rfl) ⟨919349, by rfl⟩ : syracuseStep 1225799 = 1838699) B1838699
theorem B832583 : Blo 362758 832583 := bstep (se 1 (by rfl) ⟨624437, by rfl⟩ : syracuseStep 832583 = 1248875) B1248875
theorem B1553489 : Blo 362758 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B4142177 : Blo 362758 4142177 := bstep (se 2 (by rfl) ⟨1553316, by rfl⟩ : syracuseStep 4142177 = 3106633) B3106633
theorem B3487049 : Blo 362758 3487049 := bstep (se 2 (by rfl) ⟨1307643, by rfl⟩ : syracuseStep 3487049 = 2615287) B2615287
theorem B6436205 : Blo 362758 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B1390567 : Blo 362758 1390567 := bstep (se 1 (by rfl) ⟨1042925, by rfl⟩ : syracuseStep 1390567 = 2085851) B2085851
theorem B2799755 : Blo 362758 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B1226987 : Blo 362758 1226987 := bstep (se 1 (by rfl) ⟨920240, by rfl⟩ : syracuseStep 1226987 = 1840481) B1840481
theorem B1390841 : Blo 362758 1390841 := bstep (se 2 (by rfl) ⟨521565, by rfl⟩ : syracuseStep 1390841 = 1043131) B1043131
theorem B1063207 : Blo 362758 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B1554889 : Blo 362758 1554889 := bstep (se 2 (by rfl) ⟨583083, by rfl⟩ : syracuseStep 1554889 = 1166167) B1166167
theorem B4143635 : Blo 362758 4143635 := bstep (se 1 (by rfl) ⟨3107726, by rfl⟩ : syracuseStep 4143635 = 6215453) B6215453
theorem B408487 : Blo 362758 408487 := bstep (se 1 (by rfl) ⟨306365, by rfl⟩ : syracuseStep 408487 = 612731) B612731
theorem B408667 : Blo 362758 408667 := bstep (se 1 (by rfl) ⟨306500, by rfl⟩ : syracuseStep 408667 = 613001) B613001
theorem B3128503 : Blo 362758 3128503 := bstep (se 1 (by rfl) ⟨2346377, by rfl⟩ : syracuseStep 3128503 = 4692755) B4692755
theorem B1162619 : Blo 362758 1162619 := bstep (se 1 (by rfl) ⟨871964, by rfl⟩ : syracuseStep 1162619 = 1743929) B1743929
theorem B409855 : Blo 362758 409855 := bstep (se 1 (by rfl) ⟨307391, by rfl⟩ : syracuseStep 409855 = 614783) B614783
theorem B12763453 : Blo 362758 12763453 := bstep (se 3 (by rfl) ⟨2393147, by rfl⟩ : syracuseStep 12763453 = 4786295) B4786295
theorem B1851821 : Blo 362758 1851821 := bstep (se 3 (by rfl) ⟨347216, by rfl⟩ : syracuseStep 1851821 = 694433) B694433
theorem B14434735 : Blo 362758 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B1229309 : Blo 362758 1229309 := bstep (se 3 (by rfl) ⟨230495, by rfl⟩ : syracuseStep 1229309 = 460991) B460991
theorem B410143 : Blo 362758 410143 := bstep (se 1 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 410143 = 615215) B615215
theorem B737903 : Blo 362758 737903 := bstep (se 1 (by rfl) ⟨553427, by rfl⟩ : syracuseStep 737903 = 1106855) B1106855
theorem B1163963 : Blo 362758 1163963 := bstep (se 1 (by rfl) ⟨872972, by rfl⟩ : syracuseStep 1163963 = 1745945) B1745945
theorem B1753787 : Blo 362758 1753787 := bstep (se 1 (by rfl) ⟨1315340, by rfl⟩ : syracuseStep 1753787 = 2630681) B2630681
theorem B410791 : Blo 362758 410791 := bstep (se 1 (by rfl) ⟨308093, by rfl⟩ : syracuseStep 410791 = 616187) B616187
theorem B476383 : Blo 362758 476383 := bstep (se 1 (by rfl) ⟨357287, by rfl⟩ : syracuseStep 476383 = 714575) B714575
theorem B2082185 : Blo 362758 2082185 := bstep (se 2 (by rfl) ⟨780819, by rfl⟩ : syracuseStep 2082185 = 1561639) B1561639
theorem B1230443 : Blo 362758 1230443 := bstep (se 1 (by rfl) ⟨922832, by rfl⟩ : syracuseStep 1230443 = 1845665) B1845665
theorem B1230713 : Blo 362758 1230713 := bstep (se 2 (by rfl) ⟨461517, by rfl⟩ : syracuseStep 1230713 = 923035) B923035
theorem B411583 : Blo 362758 411583 := bstep (se 1 (by rfl) ⟨308687, by rfl⟩ : syracuseStep 411583 = 617375) B617375
theorem B1853441 : Blo 362758 1853441 := bstep (se 2 (by rfl) ⟨695040, by rfl⟩ : syracuseStep 1853441 = 1390081) B1390081
theorem B411871 : Blo 362758 411871 := bstep (se 1 (by rfl) ⟨308903, by rfl⟩ : syracuseStep 411871 = 617807) B617807
theorem B1231091 : Blo 362758 1231091 := bstep (se 1 (by rfl) ⟨923318, by rfl⟩ : syracuseStep 1231091 = 1846637) B1846637
theorem B1854251 : Blo 362758 1854251 := bstep (se 1 (by rfl) ⟨1390688, by rfl⟩ : syracuseStep 1854251 = 2781377) B2781377
theorem B3656927 : Blo 362758 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B6999767 : Blo 362758 6999767 := bstep (se 1 (by rfl) ⟨5249825, by rfl⟩ : syracuseStep 6999767 = 10499651) B10499651
theorem B1232711 : Blo 362758 1232711 := bstep (se 1 (by rfl) ⟨924533, by rfl⟩ : syracuseStep 1232711 = 1849067) B1849067
theorem B1167335 : Blo 362758 1167335 := bstep (se 1 (by rfl) ⟨875501, by rfl⟩ : syracuseStep 1167335 = 1751003) B1751003
theorem B544751 : Blo 362758 544751 := bstep (se 1 (by rfl) ⟨408563, by rfl⟩ : syracuseStep 544751 = 817127) B817127
theorem B544763 : Blo 362758 544763 := bstep (se 1 (by rfl) ⟨408572, by rfl⟩ : syracuseStep 544763 = 817145) B817145
theorem B741371 : Blo 362758 741371 := bstep (se 1 (by rfl) ⟨556028, by rfl⟩ : syracuseStep 741371 = 1112057) B1112057
theorem B544823 : Blo 362758 544823 := bstep (se 1 (by rfl) ⟨408617, by rfl⟩ : syracuseStep 544823 = 817235) B817235
theorem B544871 : Blo 362758 544871 := bstep (se 1 (by rfl) ⟨408653, by rfl⟩ : syracuseStep 544871 = 817307) B817307
theorem B2773115 : Blo 362758 2773115 := bstep (se 1 (by rfl) ⟨2079836, by rfl⟩ : syracuseStep 2773115 = 4159673) B4159673
theorem B544943 : Blo 362758 544943 := bstep (se 1 (by rfl) ⟨408707, by rfl⟩ : syracuseStep 544943 = 817415) B817415
theorem B545147 : Blo 362758 545147 := bstep (se 1 (by rfl) ⟨408860, by rfl⟩ : syracuseStep 545147 = 817721) B817721
theorem B545417 : Blo 362758 545417 := bstep (se 2 (by rfl) ⟨204531, by rfl⟩ : syracuseStep 545417 = 409063) B409063
theorem B1233683 : Blo 362758 1233683 := bstep (se 1 (by rfl) ⟨925262, by rfl⟩ : syracuseStep 1233683 = 1850525) B1850525
theorem B545627 : Blo 362758 545627 := bstep (se 1 (by rfl) ⟨409220, by rfl⟩ : syracuseStep 545627 = 818441) B818441
theorem B1037299 : Blo 362758 1037299 := bstep (se 1 (by rfl) ⟨777974, by rfl⟩ : syracuseStep 1037299 = 1555949) B1555949
theorem B546089 : Blo 362758 546089 := bstep (se 2 (by rfl) ⟨204783, by rfl⟩ : syracuseStep 546089 = 409567) B409567
theorem B775531 : Blo 362758 775531 := bstep (se 1 (by rfl) ⟨581648, by rfl⟩ : syracuseStep 775531 = 1163297) B1163297
theorem B1561963 : Blo 362758 1561963 := bstep (se 1 (by rfl) ⟨1171472, by rfl⟩ : syracuseStep 1561963 = 2342945) B2342945
theorem B546287 : Blo 362758 546287 := bstep (se 1 (by rfl) ⟨409715, by rfl⟩ : syracuseStep 546287 = 819431) B819431
theorem B546683 : Blo 362758 546683 := bstep (se 1 (by rfl) ⟨410012, by rfl⟩ : syracuseStep 546683 = 820025) B820025
theorem B546719 : Blo 362758 546719 := bstep (se 1 (by rfl) ⟨410039, by rfl⟩ : syracuseStep 546719 = 820079) B820079
theorem B546953 : Blo 362758 546953 := bstep (se 2 (by rfl) ⟨205107, by rfl⟩ : syracuseStep 546953 = 410215) B410215
theorem B547103 : Blo 362758 547103 := bstep (se 1 (by rfl) ⟨410327, by rfl⟩ : syracuseStep 547103 = 820655) B820655
theorem B1038689 : Blo 362758 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B612839 : Blo 362758 612839 := bstep (se 1 (by rfl) ⟨459629, by rfl⟩ : syracuseStep 612839 = 919259) B919259
theorem B11819641 : Blo 362758 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B547655 : Blo 362758 547655 := bstep (se 1 (by rfl) ⟨410741, by rfl⟩ : syracuseStep 547655 = 821483) B821483
theorem B613703 : Blo 362758 613703 := bstep (se 1 (by rfl) ⟨460277, by rfl⟩ : syracuseStep 613703 = 920555) B920555
theorem B613865 : Blo 362758 613865 := bstep (se 2 (by rfl) ⟨230199, by rfl⟩ : syracuseStep 613865 = 460399) B460399
theorem B548519 : Blo 362758 548519 := bstep (se 1 (by rfl) ⟨411389, by rfl⟩ : syracuseStep 548519 = 822779) B822779
theorem B16867025 : Blo 362758 16867025 := bstep (se 2 (by rfl) ⟨6325134, by rfl⟩ : syracuseStep 16867025 = 12650269) B12650269
theorem B3301073 : Blo 362758 3301073 := bstep (se 2 (by rfl) ⟨1237902, by rfl⟩ : syracuseStep 3301073 = 2475805) B2475805
theorem B1040147 : Blo 362758 1040147 := bstep (se 1 (by rfl) ⟨780110, by rfl⟩ : syracuseStep 1040147 = 1560221) B1560221
theorem B548639 : Blo 362758 548639 := bstep (se 1 (by rfl) ⟨411479, by rfl⟩ : syracuseStep 548639 = 822959) B822959
theorem B2809723 : Blo 362758 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B37773317 : Blo 362758 37773317 := bstep (se 4 (by rfl) ⟨3541248, by rfl⟩ : syracuseStep 37773317 = 7082497) B7082497
theorem B1237139 : Blo 362758 1237139 := bstep (se 1 (by rfl) ⟨927854, by rfl⟩ : syracuseStep 1237139 = 1855709) B1855709
theorem B549071 : Blo 362758 549071 := bstep (se 1 (by rfl) ⟨411803, by rfl⟩ : syracuseStep 549071 = 823607) B823607
theorem B549119 : Blo 362758 549119 := bstep (se 1 (by rfl) ⟨411839, by rfl⟩ : syracuseStep 549119 = 823679) B823679
theorem B1237247 : Blo 362758 1237247 := bstep (se 1 (by rfl) ⟨927935, by rfl⟩ : syracuseStep 1237247 = 1855871) B1855871
theorem B1237409 : Blo 362758 1237409 := bstep (se 2 (by rfl) ⟨464028, by rfl⟩ : syracuseStep 1237409 = 928057) B928057
theorem B4514251 : Blo 362758 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B3007003 : Blo 362758 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B8872523 : Blo 362758 8872523 := bstep (se 1 (by rfl) ⟨6654392, by rfl⟩ : syracuseStep 8872523 = 13308785) B13308785
theorem B1041103 : Blo 362758 1041103 := bstep (se 1 (by rfl) ⟨780827, by rfl⟩ : syracuseStep 1041103 = 1561655) B1561655
theorem B516827 : Blo 362758 516827 := bstep (se 1 (by rfl) ⟨387620, by rfl⟩ : syracuseStep 516827 = 775241) B775241
theorem B549935 : Blo 362758 549935 := bstep (se 1 (by rfl) ⟨412451, by rfl⟩ : syracuseStep 549935 = 824903) B824903
theorem B550055 : Blo 362758 550055 := bstep (se 1 (by rfl) ⟨412541, by rfl⟩ : syracuseStep 550055 = 825083) B825083
theorem B196338887 : Blo 362758 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B1041947 : Blo 362758 1041947 := bstep (se 1 (by rfl) ⟨781460, by rfl⟩ : syracuseStep 1041947 = 1562921) B1562921
theorem B780281 : Blo 362758 780281 := bstep (se 2 (by rfl) ⟨292605, by rfl⟩ : syracuseStep 780281 = 585211) B585211
theorem B5270123 : Blo 362758 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B15133697 : Blo 362758 15133697 := bstep (se 2 (by rfl) ⟨5675136, by rfl⟩ : syracuseStep 15133697 = 11350273) B11350273
theorem B1666333 : Blo 362758 1666333 := bstep (se 3 (by rfl) ⟨312437, by rfl⟩ : syracuseStep 1666333 = 624875) B624875
theorem B388859 : Blo 362758 388859 := bstep (se 1 (by rfl) ⟨291644, by rfl⟩ : syracuseStep 388859 = 583289) B583289
theorem B782075 : Blo 362758 782075 := bstep (se 1 (by rfl) ⟨586556, by rfl⟩ : syracuseStep 782075 = 1173113) B1173113
theorem B1241351 : Blo 362758 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B783083 : Blo 362758 783083 := bstep (se 1 (by rfl) ⟨587312, by rfl⟩ : syracuseStep 783083 = 1174625) B1174625
theorem B521167 : Blo 362758 521167 := bstep (se 1 (by rfl) ⟨390875, by rfl⟩ : syracuseStep 521167 = 781751) B781751
theorem B11203667 : Blo 362758 11203667 := bstep (se 1 (by rfl) ⟨8402750, by rfl⟩ : syracuseStep 11203667 = 16805501) B16805501
theorem B488767 : Blo 362758 488767 := bstep (se 1 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 488767 = 733151) B733151
theorem B816551 : Blo 362758 816551 := bstep (se 1 (by rfl) ⟨612413, by rfl⟩ : syracuseStep 816551 = 1224827) B1224827
theorem B1668563 : Blo 362758 1668563 := bstep (se 1 (by rfl) ⟨1251422, by rfl⟩ : syracuseStep 1668563 = 2502845) B2502845
theorem B816659 : Blo 362758 816659 := bstep (se 1 (by rfl) ⟨612494, by rfl⟩ : syracuseStep 816659 = 1224989) B1224989
theorem B816731 : Blo 362758 816731 := bstep (se 1 (by rfl) ⟨612548, by rfl⟩ : syracuseStep 816731 = 1225097) B1225097
theorem B817343 : Blo 362758 817343 := bstep (se 1 (by rfl) ⟨613007, by rfl⟩ : syracuseStep 817343 = 1226015) B1226015
theorem B1244441 : Blo 362758 1244441 := bstep (se 2 (by rfl) ⟨466665, by rfl⟩ : syracuseStep 1244441 = 933331) B933331
theorem B818603 : Blo 362758 818603 := bstep (se 1 (by rfl) ⟨613952, by rfl⟩ : syracuseStep 818603 = 1227905) B1227905
theorem B818639 : Blo 362758 818639 := bstep (se 1 (by rfl) ⟨613979, by rfl⟩ : syracuseStep 818639 = 1227959) B1227959
theorem B13369063 : Blo 362758 13369063 := bstep (se 1 (by rfl) ⟨10026797, by rfl⟩ : syracuseStep 13369063 = 20053595) B20053595
theorem B819143 : Blo 362758 819143 := bstep (se 1 (by rfl) ⟨614357, by rfl⟩ : syracuseStep 819143 = 1228715) B1228715
theorem B1310843 : Blo 362758 1310843 := bstep (se 1 (by rfl) ⟨983132, by rfl⟩ : syracuseStep 1310843 = 1966265) B1966265
theorem B4653389 : Blo 362758 4653389 := bstep (se 3 (by rfl) ⟨872510, by rfl⟩ : syracuseStep 4653389 = 1745021) B1745021
theorem B819539 : Blo 362758 819539 := bstep (se 1 (by rfl) ⟨614654, by rfl⟩ : syracuseStep 819539 = 1229309) B1229309
theorem B491935 : Blo 362758 491935 := bstep (se 1 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 491935 = 737903) B737903
theorem B525127 : Blo 362758 525127 := bstep (se 1 (by rfl) ⟨393845, by rfl⟩ : syracuseStep 525127 = 787691) B787691
theorem B459847 : Blo 362758 459847 := bstep (se 1 (by rfl) ⟨344885, by rfl⟩ : syracuseStep 459847 = 689771) B689771
theorem B820295 : Blo 362758 820295 := bstep (se 1 (by rfl) ⟨615221, by rfl⟩ : syracuseStep 820295 = 1230443) B1230443
theorem B820475 : Blo 362758 820475 := bstep (se 1 (by rfl) ⟨615356, by rfl⟩ : syracuseStep 820475 = 1230713) B1230713
theorem B820727 : Blo 362758 820727 := bstep (se 1 (by rfl) ⟨615545, by rfl⟩ : syracuseStep 820727 = 1231091) B1231091
theorem B1378205 : Blo 362758 1378205 := bstep (se 3 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 1378205 = 516827) B516827
theorem B919583 : Blo 362758 919583 := bstep (se 1 (by rfl) ⟨689687, by rfl⟩ : syracuseStep 919583 = 1379375) B1379375
theorem B2623529 : Blo 362758 2623529 := bstep (se 2 (by rfl) ⟨983823, by rfl⟩ : syracuseStep 2623529 = 1967647) B1967647
theorem B821807 : Blo 362758 821807 := bstep (se 1 (by rfl) ⟨616355, by rfl⟩ : syracuseStep 821807 = 1232711) B1232711
theorem B363167 : Blo 362758 363167 := bstep (se 1 (by rfl) ⟨272375, by rfl⟩ : syracuseStep 363167 = 544751) B544751
theorem B363175 : Blo 362758 363175 := bstep (se 1 (by rfl) ⟨272381, by rfl⟩ : syracuseStep 363175 = 544763) B544763
theorem B363215 : Blo 362758 363215 := bstep (se 1 (by rfl) ⟨272411, by rfl⟩ : syracuseStep 363215 = 544823) B544823
theorem B363247 : Blo 362758 363247 := bstep (se 1 (by rfl) ⟨272435, by rfl⟩ : syracuseStep 363247 = 544871) B544871
theorem B2329337 : Blo 362758 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B2853625 : Blo 362758 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B363295 : Blo 362758 363295 := bstep (se 1 (by rfl) ⟨272471, by rfl⟩ : syracuseStep 363295 = 544943) B544943
theorem B2624339 : Blo 362758 2624339 := bstep (se 1 (by rfl) ⟨1968254, by rfl⟩ : syracuseStep 2624339 = 3936509) B3936509
theorem B363431 : Blo 362758 363431 := bstep (se 1 (by rfl) ⟨272573, by rfl⟩ : syracuseStep 363431 = 545147) B545147
theorem B363611 : Blo 362758 363611 := bstep (se 1 (by rfl) ⟨272708, by rfl⟩ : syracuseStep 363611 = 545417) B545417
theorem B822455 : Blo 362758 822455 := bstep (se 1 (by rfl) ⟨616841, by rfl⟩ : syracuseStep 822455 = 1233683) B1233683
theorem B363751 : Blo 362758 363751 := bstep (se 1 (by rfl) ⟨272813, by rfl⟩ : syracuseStep 363751 = 545627) B545627
theorem B3345803 : Blo 362758 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B364059 : Blo 362758 364059 := bstep (se 1 (by rfl) ⟨273044, by rfl⟩ : syracuseStep 364059 = 546089) B546089
theorem B364191 : Blo 362758 364191 := bstep (se 1 (by rfl) ⟨273143, by rfl⟩ : syracuseStep 364191 = 546287) B546287
theorem B1052471 : Blo 362758 1052471 := bstep (se 1 (by rfl) ⟨789353, by rfl⟩ : syracuseStep 1052471 = 1578707) B1578707
theorem B364455 : Blo 362758 364455 := bstep (se 1 (by rfl) ⟨273341, by rfl⟩ : syracuseStep 364455 = 546683) B546683
theorem B364479 : Blo 362758 364479 := bstep (se 1 (by rfl) ⟨273359, by rfl⟩ : syracuseStep 364479 = 546719) B546719
theorem B2756591 : Blo 362758 2756591 := bstep (se 1 (by rfl) ⟨2067443, by rfl⟩ : syracuseStep 2756591 = 4134887) B4134887
theorem B364635 : Blo 362758 364635 := bstep (se 1 (by rfl) ⟨273476, by rfl⟩ : syracuseStep 364635 = 546953) B546953
theorem B364735 : Blo 362758 364735 := bstep (se 1 (by rfl) ⟨273551, by rfl⟩ : syracuseStep 364735 = 547103) B547103
theorem B692459 : Blo 362758 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B2330977 : Blo 362758 2330977 := bstep (se 2 (by rfl) ⟨874116, by rfl⟩ : syracuseStep 2330977 = 1748233) B1748233
theorem B922063 : Blo 362758 922063 := bstep (se 1 (by rfl) ⟨691547, by rfl⟩ : syracuseStep 922063 = 1383095) B1383095
theorem B365103 : Blo 362758 365103 := bstep (se 1 (by rfl) ⟨273827, by rfl⟩ : syracuseStep 365103 = 547655) B547655
theorem B365679 : Blo 362758 365679 := bstep (se 1 (by rfl) ⟨274259, by rfl⟩ : syracuseStep 365679 = 548519) B548519
theorem B11244683 : Blo 362758 11244683 := bstep (se 1 (by rfl) ⟨8433512, by rfl⟩ : syracuseStep 11244683 = 16867025) B16867025
theorem B2200715 : Blo 362758 2200715 := bstep (se 1 (by rfl) ⟨1650536, by rfl⟩ : syracuseStep 2200715 = 3301073) B3301073
theorem B693431 : Blo 362758 693431 := bstep (se 1 (by rfl) ⟨520073, by rfl⟩ : syracuseStep 693431 = 1040147) B1040147
theorem B365759 : Blo 362758 365759 := bstep (se 1 (by rfl) ⟨274319, by rfl⟩ : syracuseStep 365759 = 548639) B548639
theorem B660799 : Blo 362758 660799 := bstep (se 1 (by rfl) ⟨495599, by rfl⟩ : syracuseStep 660799 = 991199) B991199
theorem B3937679 : Blo 362758 3937679 := bstep (se 1 (by rfl) ⟨2953259, by rfl⟩ : syracuseStep 3937679 = 5906519) B5906519
theorem B824759 : Blo 362758 824759 := bstep (se 1 (by rfl) ⟨618569, by rfl⟩ : syracuseStep 824759 = 1237139) B1237139
theorem B366047 : Blo 362758 366047 := bstep (se 1 (by rfl) ⟨274535, by rfl⟩ : syracuseStep 366047 = 549071) B549071
theorem B366079 : Blo 362758 366079 := bstep (se 1 (by rfl) ⟨274559, by rfl⟩ : syracuseStep 366079 = 549119) B549119
theorem B824831 : Blo 362758 824831 := bstep (se 1 (by rfl) ⟨618623, by rfl⟩ : syracuseStep 824831 = 1237247) B1237247
theorem B824939 : Blo 362758 824939 := bstep (se 1 (by rfl) ⟨618704, by rfl⟩ : syracuseStep 824939 = 1237409) B1237409
theorem B2103043 : Blo 362758 2103043 := bstep (se 1 (by rfl) ⟨1577282, by rfl⟩ : syracuseStep 2103043 = 3154565) B3154565
theorem B923471 : Blo 362758 923471 := bstep (se 1 (by rfl) ⟨692603, by rfl⟩ : syracuseStep 923471 = 1385207) B1385207
theorem B366623 : Blo 362758 366623 := bstep (se 1 (by rfl) ⟨274967, by rfl⟩ : syracuseStep 366623 = 549935) B549935
theorem B366703 : Blo 362758 366703 := bstep (se 1 (by rfl) ⟨275027, by rfl⟩ : syracuseStep 366703 = 550055) B550055
theorem B923987 : Blo 362758 923987 := bstep (se 1 (by rfl) ⟨692990, by rfl⟩ : syracuseStep 923987 = 1385981) B1385981
theorem B694631 : Blo 362758 694631 := bstep (se 1 (by rfl) ⟨520973, by rfl⟩ : syracuseStep 694631 = 1041947) B1041947
theorem B2070953 : Blo 362758 2070953 := bstep (se 2 (by rfl) ⟨776607, by rfl⟩ : syracuseStep 2070953 = 1553215) B1553215
theorem B694889 : Blo 362758 694889 := bstep (se 2 (by rfl) ⟨260583, by rfl⟩ : syracuseStep 694889 = 521167) B521167
theorem B1383065 : Blo 362758 1383065 := bstep (se 2 (by rfl) ⟨518649, by rfl⟩ : syracuseStep 1383065 = 1037299) B1037299
theorem B990571 : Blo 362758 990571 := bstep (se 1 (by rfl) ⟨742928, by rfl⟩ : syracuseStep 990571 = 1485857) B1485857
theorem B925465 : Blo 362758 925465 := bstep (se 2 (by rfl) ⟨347049, by rfl⟩ : syracuseStep 925465 = 694099) B694099
theorem B827567 : Blo 362758 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B1417609 : Blo 362758 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B926113 : Blo 362758 926113 := bstep (se 2 (by rfl) ⟨347292, by rfl⟩ : syracuseStep 926113 = 694585) B694585
theorem B1385039 : Blo 362758 1385039 := bstep (se 1 (by rfl) ⟨1038779, by rfl⟩ : syracuseStep 1385039 = 2077559) B2077559
theorem B2073185 : Blo 362758 2073185 := bstep (se 2 (by rfl) ⟨777444, by rfl⟩ : syracuseStep 2073185 = 1554889) B1554889
theorem B2761451 : Blo 362758 2761451 := bstep (se 1 (by rfl) ⟨2071088, by rfl⟩ : syracuseStep 2761451 = 4142177) B4142177
theorem B3318509 : Blo 362758 3318509 := bstep (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) B1244441
theorem B927227 : Blo 362758 927227 := bstep (se 1 (by rfl) ⟨695420, by rfl⟩ : syracuseStep 927227 = 1390841) B1390841
theorem B4171337 : Blo 362758 4171337 := bstep (se 2 (by rfl) ⟨1564251, by rfl⟩ : syracuseStep 4171337 = 3128503) B3128503
theorem B2762423 : Blo 362758 2762423 := bstep (se 1 (by rfl) ⟨2071817, by rfl⟩ : syracuseStep 2762423 = 4143635) B4143635
theorem B927713 : Blo 362758 927713 := bstep (se 2 (by rfl) ⟨347892, by rfl⟩ : syracuseStep 927713 = 695785) B695785
theorem B3746297 : Blo 362758 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B1976989 : Blo 362758 1976989 := bstep (se 3 (by rfl) ⟨370685, by rfl⟩ : syracuseStep 1976989 = 741371) B741371
theorem B17017937 : Blo 362758 17017937 := bstep (se 2 (by rfl) ⟨6381726, by rfl⟩ : syracuseStep 17017937 = 12763453) B12763453
theorem B19246313 : Blo 362758 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B4009337 : Blo 362758 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B15216133 : Blo 362758 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B1388123 : Blo 362758 1388123 := bstep (se 1 (by rfl) ⟨1041092, by rfl⟩ : syracuseStep 1388123 = 2082185) B2082185
theorem B1388137 : Blo 362758 1388137 := bstep (se 2 (by rfl) ⟨520551, by rfl⟩ : syracuseStep 1388137 = 1041103) B1041103
theorem B635177 : Blo 362758 635177 := bstep (se 2 (by rfl) ⟨238191, by rfl⟩ : syracuseStep 635177 = 476383) B476383
theorem B2437951 : Blo 362758 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B4666511 : Blo 362758 4666511 := bstep (se 1 (by rfl) ⟨3499883, by rfl⟩ : syracuseStep 4666511 = 6999767) B6999767
theorem B4437287 : Blo 362758 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B1848743 : Blo 362758 1848743 := bstep (se 1 (by rfl) ⟨1386557, by rfl⟩ : syracuseStep 1848743 = 2773115) B2773115
theorem B1226447 : Blo 362758 1226447 := bstep (se 1 (by rfl) ⟨919835, by rfl⟩ : syracuseStep 1226447 = 1839671) B1839671
theorem B1751327 : Blo 362758 1751327 := bstep (se 1 (by rfl) ⟨1313495, by rfl⟩ : syracuseStep 1751327 = 2626991) B2626991
theorem B408559 : Blo 362758 408559 := bstep (se 1 (by rfl) ⟨306419, by rfl⟩ : syracuseStep 408559 = 612839) B612839
theorem B1228283 : Blo 362758 1228283 := bstep (se 1 (by rfl) ⟨921212, by rfl⟩ : syracuseStep 1228283 = 1842425) B1842425
theorem B409135 : Blo 362758 409135 := bstep (se 1 (by rfl) ⟨306851, by rfl⟩ : syracuseStep 409135 = 613703) B613703
theorem B409243 : Blo 362758 409243 := bstep (se 1 (by rfl) ⟨306932, by rfl⟩ : syracuseStep 409243 = 613865) B613865
theorem B2080475 : Blo 362758 2080475 := bstep (se 1 (by rfl) ⟨1560356, by rfl⟩ : syracuseStep 2080475 = 3120713) B3120713
theorem B2211563 : Blo 362758 2211563 := bstep (se 1 (by rfl) ⟨1658672, by rfl⟩ : syracuseStep 2211563 = 3317345) B3317345
theorem B25182211 : Blo 362758 25182211 := bstep (se 1 (by rfl) ⟨18886658, by rfl⟩ : syracuseStep 25182211 = 37773317) B37773317
theorem B5915015 : Blo 362758 5915015 := bstep (se 1 (by rfl) ⟨4436261, by rfl⟩ : syracuseStep 5915015 = 8872523) B8872523
theorem B21021443 : Blo 362758 21021443 := bstep (se 1 (by rfl) ⟨15766082, by rfl⟩ : syracuseStep 21021443 = 31532165) B31532165
theorem B130892591 : Blo 362758 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B4506553 : Blo 362758 4506553 := bstep (se 2 (by rfl) ⟨1689957, by rfl⟩ : syracuseStep 4506553 = 3379915) B3379915
theorem B3524147 : Blo 362758 3524147 := bstep (se 1 (by rfl) ⟨2643110, by rfl⟩ : syracuseStep 3524147 = 5286221) B5286221
theorem B1034041 : Blo 362758 1034041 := bstep (se 2 (by rfl) ⟨387765, by rfl⟩ : syracuseStep 1034041 = 775531) B775531
theorem B2082617 : Blo 362758 2082617 := bstep (se 2 (by rfl) ⟨780981, by rfl⟩ : syracuseStep 2082617 = 1561963) B1561963
theorem B1558511 : Blo 362758 1558511 := bstep (se 1 (by rfl) ⟨1168883, by rfl⟩ : syracuseStep 1558511 = 2337767) B2337767
theorem B2344943 : Blo 362758 2344943 := bstep (se 1 (by rfl) ⟨1758707, by rfl⟩ : syracuseStep 2344943 = 3517415) B3517415
theorem B1558547 : Blo 362758 1558547 := bstep (se 1 (by rfl) ⟨1168910, by rfl⟩ : syracuseStep 1558547 = 2337821) B2337821
theorem B1230875 : Blo 362758 1230875 := bstep (se 1 (by rfl) ⟨923156, by rfl⟩ : syracuseStep 1230875 = 1846313) B1846313
theorem B1854089 : Blo 362758 1854089 := bstep (se 2 (by rfl) ⟨695283, by rfl⟩ : syracuseStep 1854089 = 1390567) B1390567
theorem B1559263 : Blo 362758 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B1035659 : Blo 362758 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B544367 : Blo 362758 544367 := bstep (se 1 (by rfl) ⟨408275, by rfl⟩ : syracuseStep 544367 = 816551) B816551
theorem B544439 : Blo 362758 544439 := bstep (se 1 (by rfl) ⟨408329, by rfl⟩ : syracuseStep 544439 = 816659) B816659
theorem B544487 : Blo 362758 544487 := bstep (se 1 (by rfl) ⟨408365, by rfl⟩ : syracuseStep 544487 = 816731) B816731
theorem B544649 : Blo 362758 544649 := bstep (se 2 (by rfl) ⟨204243, by rfl⟩ : syracuseStep 544649 = 408487) B408487
theorem B544889 : Blo 362758 544889 := bstep (se 2 (by rfl) ⟨204333, by rfl⟩ : syracuseStep 544889 = 408667) B408667
theorem B544895 : Blo 362758 544895 := bstep (se 1 (by rfl) ⟨408671, by rfl⟩ : syracuseStep 544895 = 817343) B817343
theorem B1036957 : Blo 362758 1036957 := bstep (se 3 (by rfl) ⟨194429, by rfl⟩ : syracuseStep 1036957 = 388859) B388859
theorem B2085533 : Blo 362758 2085533 := bstep (se 3 (by rfl) ⟨391037, by rfl⟩ : syracuseStep 2085533 = 782075) B782075
theorem B775079 : Blo 362758 775079 := bstep (se 1 (by rfl) ⟨581309, by rfl⟩ : syracuseStep 775079 = 1162619) B1162619
theorem B545735 : Blo 362758 545735 := bstep (se 1 (by rfl) ⟨409301, by rfl⟩ : syracuseStep 545735 = 818603) B818603
theorem B545759 : Blo 362758 545759 := bstep (se 1 (by rfl) ⟨409319, by rfl⟩ : syracuseStep 545759 = 818639) B818639
theorem B546095 : Blo 362758 546095 := bstep (se 1 (by rfl) ⟨409571, by rfl⟩ : syracuseStep 546095 = 819143) B819143
theorem B546299 : Blo 362758 546299 := bstep (se 1 (by rfl) ⟨409724, by rfl⟩ : syracuseStep 546299 = 819449) B819449
theorem B546335 : Blo 362758 546335 := bstep (se 1 (by rfl) ⟨409751, by rfl⟩ : syracuseStep 546335 = 819503) B819503
theorem B1660495 : Blo 362758 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B1234547 : Blo 362758 1234547 := bstep (se 1 (by rfl) ⟨925910, by rfl⟩ : syracuseStep 1234547 = 1851821) B1851821
theorem B546473 : Blo 362758 546473 := bstep (se 2 (by rfl) ⟨204927, by rfl⟩ : syracuseStep 546473 = 409855) B409855
theorem B546479 : Blo 362758 546479 := bstep (se 1 (by rfl) ⟨409859, by rfl⟩ : syracuseStep 546479 = 819719) B819719
theorem B775975 : Blo 362758 775975 := bstep (se 1 (by rfl) ⟨581981, by rfl⟩ : syracuseStep 775975 = 1163963) B1163963
theorem B546599 : Blo 362758 546599 := bstep (se 1 (by rfl) ⟨409949, by rfl⟩ : syracuseStep 546599 = 819899) B819899
theorem B1169191 : Blo 362758 1169191 := bstep (se 1 (by rfl) ⟨876893, by rfl⟩ : syracuseStep 1169191 = 1753787) B1753787
theorem B6019001 : Blo 362758 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B546857 : Blo 362758 546857 := bstep (se 2 (by rfl) ⟨205071, by rfl⟩ : syracuseStep 546857 = 410143) B410143
theorem B546887 : Blo 362758 546887 := bstep (se 1 (by rfl) ⟨410165, by rfl⟩ : syracuseStep 546887 = 820331) B820331
theorem B547199 : Blo 362758 547199 := bstep (se 1 (by rfl) ⟨410399, by rfl⟩ : syracuseStep 547199 = 820799) B820799
theorem B547271 : Blo 362758 547271 := bstep (se 1 (by rfl) ⟨410453, by rfl⟩ : syracuseStep 547271 = 820907) B820907
theorem B547487 : Blo 362758 547487 := bstep (se 1 (by rfl) ⟨410615, by rfl⟩ : syracuseStep 547487 = 821231) B821231
theorem B1235627 : Blo 362758 1235627 := bstep (se 1 (by rfl) ⟨926720, by rfl⟩ : syracuseStep 1235627 = 1853441) B1853441
theorem B547631 : Blo 362758 547631 := bstep (se 1 (by rfl) ⟨410723, by rfl⟩ : syracuseStep 547631 = 821447) B821447
theorem B613183 : Blo 362758 613183 := bstep (se 1 (by rfl) ⟨459887, by rfl⟩ : syracuseStep 613183 = 919775) B919775
theorem B547721 : Blo 362758 547721 := bstep (se 2 (by rfl) ⟨205395, by rfl⟩ : syracuseStep 547721 = 410791) B410791
theorem B547751 : Blo 362758 547751 := bstep (se 1 (by rfl) ⟨410813, by rfl⟩ : syracuseStep 547751 = 821627) B821627
theorem B547931 : Blo 362758 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B1236167 : Blo 362758 1236167 := bstep (se 1 (by rfl) ⟨927125, by rfl⟩ : syracuseStep 1236167 = 1854251) B1854251
theorem B548123 : Blo 362758 548123 := bstep (se 1 (by rfl) ⟨411092, by rfl⟩ : syracuseStep 548123 = 822185) B822185
theorem B7822817 : Blo 362758 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B4415143 : Blo 362758 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B548591 : Blo 362758 548591 := bstep (se 1 (by rfl) ⟨411443, by rfl⟩ : syracuseStep 548591 = 822887) B822887
theorem B548777 : Blo 362758 548777 := bstep (se 2 (by rfl) ⟨205791, by rfl⟩ : syracuseStep 548777 = 411583) B411583
theorem B778223 : Blo 362758 778223 := bstep (se 1 (by rfl) ⟨583667, by rfl⟩ : syracuseStep 778223 = 1167335) B1167335
theorem B1007657 : Blo 362758 1007657 := bstep (se 2 (by rfl) ⟨377871, by rfl⟩ : syracuseStep 1007657 = 755743) B755743
theorem B548927 : Blo 362758 548927 := bstep (se 1 (by rfl) ⟨411695, by rfl⟩ : syracuseStep 548927 = 823391) B823391
theorem B549161 : Blo 362758 549161 := bstep (se 2 (by rfl) ⟨205935, by rfl⟩ : syracuseStep 549161 = 411871) B411871
theorem B549431 : Blo 362758 549431 := bstep (se 1 (by rfl) ⟨412073, by rfl⟩ : syracuseStep 549431 = 824147) B824147
theorem B549791 : Blo 362758 549791 := bstep (se 1 (by rfl) ⟨412343, by rfl⟩ : syracuseStep 549791 = 824687) B824687
theorem B550079 : Blo 362758 550079 := bstep (se 1 (by rfl) ⟨412559, by rfl⟩ : syracuseStep 550079 = 825119) B825119
theorem B2221777 : Blo 362758 2221777 := bstep (se 2 (by rfl) ⟨833166, by rfl⟩ : syracuseStep 2221777 = 1666333) B1666333
theorem B616315 : Blo 362758 616315 := bstep (se 1 (by rfl) ⟨462236, by rfl⟩ : syracuseStep 616315 = 924473) B924473
theorem B5334983 : Blo 362758 5334983 := bstep (se 1 (by rfl) ⟨4001237, by rfl⟩ : syracuseStep 5334983 = 8002475) B8002475
theorem B616585 : Blo 362758 616585 := bstep (se 2 (by rfl) ⟨231219, by rfl⟩ : syracuseStep 616585 = 462439) B462439
theorem B8580809 : Blo 362758 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B618367 : Blo 362758 618367 := bstep (se 1 (by rfl) ⟨463775, by rfl⟩ : syracuseStep 618367 = 927551) B927551
theorem B520187 : Blo 362758 520187 := bstep (se 1 (by rfl) ⟨390140, by rfl⟩ : syracuseStep 520187 = 780281) B780281
theorem B2977823 : Blo 362758 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B14053661 : Blo 362758 14053661 := bstep (se 3 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 14053661 = 5270123) B5270123
theorem B651689 : Blo 362758 651689 := bstep (se 2 (by rfl) ⟨244383, by rfl⟩ : syracuseStep 651689 = 488767) B488767
theorem B1405601 : Blo 362758 1405601 := bstep (se 2 (by rfl) ⟨527100, by rfl⟩ : syracuseStep 1405601 = 1054201) B1054201
theorem B10089131 : Blo 362758 10089131 := bstep (se 1 (by rfl) ⟨7566848, by rfl⟩ : syracuseStep 10089131 = 15133697) B15133697
theorem B816623 : Blo 362758 816623 := bstep (se 1 (by rfl) ⟨612467, by rfl⟩ : syracuseStep 816623 = 1224935) B1224935
theorem B522055 : Blo 362758 522055 := bstep (se 1 (by rfl) ⟨391541, by rfl⟩ : syracuseStep 522055 = 783083) B783083
theorem B817199 : Blo 362758 817199 := bstep (se 1 (by rfl) ⟨612899, by rfl⟩ : syracuseStep 817199 = 1225799) B1225799
theorem B555055 : Blo 362758 555055 := bstep (se 1 (by rfl) ⟨416291, by rfl⟩ : syracuseStep 555055 = 832583) B832583
theorem B7469111 : Blo 362758 7469111 := bstep (se 1 (by rfl) ⟨5601833, by rfl⟩ : syracuseStep 7469111 = 11203667) B11203667
theorem B15759521 : Blo 362758 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B2324699 : Blo 362758 2324699 := bstep (se 1 (by rfl) ⟨1743524, by rfl⟩ : syracuseStep 2324699 = 3487049) B3487049
theorem B4290803 : Blo 362758 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B1112375 : Blo 362758 1112375 := bstep (se 1 (by rfl) ⟨834281, by rfl⟩ : syracuseStep 1112375 = 1668563) B1668563
theorem B1866503 : Blo 362758 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B817991 : Blo 362758 817991 := bstep (se 1 (by rfl) ⟨613493, by rfl⟩ : syracuseStep 817991 = 1226987) B1226987
theorem B1277561 : Blo 362758 1277561 := bstep (se 2 (by rfl) ⟨479085, by rfl⟩ : syracuseStep 1277561 = 958171) B958171
theorem B17825417 : Blo 362758 17825417 := bstep (se 2 (by rfl) ⟨6684531, by rfl⟩ : syracuseStep 17825417 = 13369063) B13369063
theorem B655913 : Blo 362758 655913 := bstep (se 2 (by rfl) ⟨245967, by rfl⟩ : syracuseStep 655913 = 491935) B491935
theorem B918803 : Blo 362758 918803 := bstep (se 1 (by rfl) ⟨689102, by rfl⟩ : syracuseStep 918803 = 1378205) B1378205
theorem B820583 : Blo 362758 820583 := bstep (se 1 (by rfl) ⟨615437, by rfl⟩ : syracuseStep 820583 = 1230875) B1230875
theorem B26904349 : Blo 362758 26904349 := bstep (se 3 (by rfl) ⟨5044565, by rfl⟩ : syracuseStep 26904349 = 10089131) B10089131
theorem B349046909 : Blo 362758 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B690439 : Blo 362758 690439 := bstep (se 1 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 690439 = 1035659) B1035659
theorem B2230535 : Blo 362758 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B362911 : Blo 362758 362911 := bstep (se 1 (by rfl) ⟨272183, by rfl⟩ : syracuseStep 362911 = 544367) B544367
theorem B1378721 : Blo 362758 1378721 := bstep (se 2 (by rfl) ⟨517020, by rfl⟩ : syracuseStep 1378721 = 1034041) B1034041
theorem B362959 : Blo 362758 362959 := bstep (se 1 (by rfl) ⟨272219, by rfl⟩ : syracuseStep 362959 = 544439) B544439
theorem B362991 : Blo 362758 362991 := bstep (se 1 (by rfl) ⟨272243, by rfl⟩ : syracuseStep 362991 = 544487) B544487
theorem B821753 : Blo 362758 821753 := bstep (se 2 (by rfl) ⟨308157, by rfl⟩ : syracuseStep 821753 = 616315) B616315
theorem B363099 : Blo 362758 363099 := bstep (se 1 (by rfl) ⟨272324, by rfl⟩ : syracuseStep 363099 = 544649) B544649
theorem B1837727 : Blo 362758 1837727 := bstep (se 1 (by rfl) ⟨1378295, by rfl⟩ : syracuseStep 1837727 = 2756591) B2756591
theorem B363259 : Blo 362758 363259 := bstep (se 1 (by rfl) ⟨272444, by rfl⟩ : syracuseStep 363259 = 544889) B544889
theorem B363263 : Blo 362758 363263 := bstep (se 1 (by rfl) ⟨272447, by rfl⟩ : syracuseStep 363263 = 544895) B544895
theorem B461639 : Blo 362758 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B822113 : Blo 362758 822113 := bstep (se 2 (by rfl) ⟨308292, by rfl⟩ : syracuseStep 822113 = 616585) B616585
theorem B29985821 : Blo 362758 29985821 := bstep (se 3 (by rfl) ⟨5622341, by rfl⟩ : syracuseStep 29985821 = 11244683) B11244683
theorem B363823 : Blo 362758 363823 := bstep (se 1 (by rfl) ⟨272867, by rfl⟩ : syracuseStep 363823 = 545735) B545735
theorem B363839 : Blo 362758 363839 := bstep (se 1 (by rfl) ⟨272879, by rfl⟩ : syracuseStep 363839 = 545759) B545759
theorem B462287 : Blo 362758 462287 := bstep (se 1 (by rfl) ⟨346715, by rfl⟩ : syracuseStep 462287 = 693431) B693431
theorem B364063 : Blo 362758 364063 := bstep (se 1 (by rfl) ⟨273047, by rfl⟩ : syracuseStep 364063 = 546095) B546095
theorem B2625119 : Blo 362758 2625119 := bstep (se 1 (by rfl) ⟨1968839, by rfl⟩ : syracuseStep 2625119 = 3937679) B3937679
theorem B3804833 : Blo 362758 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B364199 : Blo 362758 364199 := bstep (se 1 (by rfl) ⟨273149, by rfl⟩ : syracuseStep 364199 = 546299) B546299
theorem B364223 : Blo 362758 364223 := bstep (se 1 (by rfl) ⟨273167, by rfl⟩ : syracuseStep 364223 = 546335) B546335
theorem B823031 : Blo 362758 823031 := bstep (se 1 (by rfl) ⟨617273, by rfl⟩ : syracuseStep 823031 = 1234547) B1234547
theorem B364315 : Blo 362758 364315 := bstep (se 1 (by rfl) ⟨273236, by rfl⟩ : syracuseStep 364315 = 546473) B546473
theorem B364319 : Blo 362758 364319 := bstep (se 1 (by rfl) ⟨273239, by rfl⟩ : syracuseStep 364319 = 546479) B546479
theorem B364399 : Blo 362758 364399 := bstep (se 1 (by rfl) ⟨273299, by rfl⟩ : syracuseStep 364399 = 546599) B546599
theorem B364571 : Blo 362758 364571 := bstep (se 1 (by rfl) ⟨273428, by rfl⟩ : syracuseStep 364571 = 546857) B546857
theorem B364591 : Blo 362758 364591 := bstep (se 1 (by rfl) ⟨273443, by rfl⟩ : syracuseStep 364591 = 546887) B546887
theorem B463087 : Blo 362758 463087 := bstep (se 1 (by rfl) ⟨347315, by rfl⟩ : syracuseStep 463087 = 694631) B694631
theorem B364799 : Blo 362758 364799 := bstep (se 1 (by rfl) ⟨273599, by rfl⟩ : syracuseStep 364799 = 547199) B547199
theorem B1380635 : Blo 362758 1380635 := bstep (se 1 (by rfl) ⟨1035476, by rfl⟩ : syracuseStep 1380635 = 2070953) B2070953
theorem B364847 : Blo 362758 364847 := bstep (se 1 (by rfl) ⟨273635, by rfl⟩ : syracuseStep 364847 = 547271) B547271
theorem B463259 : Blo 362758 463259 := bstep (se 1 (by rfl) ⟨347444, by rfl⟩ : syracuseStep 463259 = 694889) B694889
theorem B6951349 : Blo 362758 6951349 := bstep (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) B651689
theorem B922043 : Blo 362758 922043 := bstep (se 1 (by rfl) ⟨691532, by rfl⟩ : syracuseStep 922043 = 1383065) B1383065
theorem B364991 : Blo 362758 364991 := bstep (se 1 (by rfl) ⟨273743, by rfl⟩ : syracuseStep 364991 = 547487) B547487
theorem B823751 : Blo 362758 823751 := bstep (se 1 (by rfl) ⟨617813, by rfl⟩ : syracuseStep 823751 = 1235627) B1235627
theorem B365087 : Blo 362758 365087 := bstep (se 1 (by rfl) ⟨273815, by rfl⟩ : syracuseStep 365087 = 547631) B547631
theorem B365147 : Blo 362758 365147 := bstep (se 1 (by rfl) ⟨273860, by rfl⟩ : syracuseStep 365147 = 547721) B547721
theorem B365167 : Blo 362758 365167 := bstep (se 1 (by rfl) ⟨273875, by rfl⟩ : syracuseStep 365167 = 547751) B547751
theorem B20288177 : Blo 362758 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B365287 : Blo 362758 365287 := bstep (se 1 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 365287 = 547931) B547931
theorem B824111 : Blo 362758 824111 := bstep (se 1 (by rfl) ⟨618083, by rfl⟩ : syracuseStep 824111 = 1236167) B1236167
theorem B365415 : Blo 362758 365415 := bstep (se 1 (by rfl) ⟨274061, by rfl⟩ : syracuseStep 365415 = 548123) B548123
theorem B5215211 : Blo 362758 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B365727 : Blo 362758 365727 := bstep (se 1 (by rfl) ⟨274295, by rfl⟩ : syracuseStep 365727 = 548591) B548591
theorem B824489 : Blo 362758 824489 := bstep (se 2 (by rfl) ⟨309183, by rfl⟩ : syracuseStep 824489 = 618367) B618367
theorem B365851 : Blo 362758 365851 := bstep (se 1 (by rfl) ⟨274388, by rfl⟩ : syracuseStep 365851 = 548777) B548777
theorem B365951 : Blo 362758 365951 := bstep (se 1 (by rfl) ⟨274463, by rfl⟩ : syracuseStep 365951 = 548927) B548927
theorem B366107 : Blo 362758 366107 := bstep (se 1 (by rfl) ⟨274580, by rfl⟩ : syracuseStep 366107 = 549161) B549161
theorem B366287 : Blo 362758 366287 := bstep (se 1 (by rfl) ⟨274715, by rfl⟩ : syracuseStep 366287 = 549431) B549431
theorem B923359 : Blo 362758 923359 := bstep (se 1 (by rfl) ⟨692519, by rfl⟩ : syracuseStep 923359 = 1385039) B1385039
theorem B1382123 : Blo 362758 1382123 := bstep (se 1 (by rfl) ⟨1036592, by rfl⟩ : syracuseStep 1382123 = 2073185) B2073185
theorem B1840967 : Blo 362758 1840967 := bstep (se 1 (by rfl) ⟨1380725, by rfl⟩ : syracuseStep 1840967 = 2761451) B2761451
theorem B366527 : Blo 362758 366527 := bstep (se 1 (by rfl) ⟨274895, by rfl⟩ : syracuseStep 366527 = 549791) B549791
theorem B366719 : Blo 362758 366719 := bstep (se 1 (by rfl) ⟨275039, by rfl⟩ : syracuseStep 366719 = 550079) B550079
theorem B1382609 : Blo 362758 1382609 := bstep (se 2 (by rfl) ⟨518478, by rfl⟩ : syracuseStep 1382609 = 1036957) B1036957
theorem B3250601 : Blo 362758 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B1841615 : Blo 362758 1841615 := bstep (se 1 (by rfl) ⟨1381211, by rfl⟩ : syracuseStep 1841615 = 2762423) B2762423
theorem B11345291 : Blo 362758 11345291 := bstep (se 1 (by rfl) ⟨8508968, by rfl⟩ : syracuseStep 11345291 = 17017937) B17017937
theorem B925415 : Blo 362758 925415 := bstep (se 1 (by rfl) ⟨694061, by rfl⟩ : syracuseStep 925415 = 1388123) B1388123
theorem B2958191 : Blo 362758 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B1549799 : Blo 362758 1549799 := bstep (se 1 (by rfl) ⟨1162349, by rfl⟩ : syracuseStep 1549799 = 2324699) B2324699
theorem B2860535 : Blo 362758 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B1320761 : Blo 362758 1320761 := bstep (se 2 (by rfl) ⟨495285, by rfl⟩ : syracuseStep 1320761 = 990571) B990571
theorem B1386983 : Blo 362758 1386983 := bstep (se 1 (by rfl) ⟨1040237, by rfl⟩ : syracuseStep 1386983 = 2080475) B2080475
theorem B1387165 : Blo 362758 1387165 := bstep (se 3 (by rfl) ⟨260093, by rfl⟩ : syracuseStep 1387165 = 520187) B520187
theorem B7940861 : Blo 362758 7940861 := bstep (se 3 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 7940861 = 2977823) B2977823
theorem B2960293 : Blo 362758 2960293 := bstep (se 4 (by rfl) ⟨277527, by rfl⟩ : syracuseStep 2960293 = 555055) B555055
theorem B3943343 : Blo 362758 3943343 := bstep (se 1 (by rfl) ⟨2957507, by rfl⟩ : syracuseStep 3943343 = 5915015) B5915015
theorem B700169 : Blo 362758 700169 := bstep (se 2 (by rfl) ⟨262563, by rfl⟩ : syracuseStep 700169 = 525127) B525127
theorem B1388411 : Blo 362758 1388411 := bstep (se 1 (by rfl) ⟨1041308, by rfl⟩ : syracuseStep 1388411 = 2082617) B2082617
theorem B6008737 : Blo 362758 6008737 := bstep (se 2 (by rfl) ⟨2253276, by rfl⟩ : syracuseStep 6008737 = 4506553) B4506553
theorem B1552891 : Blo 362758 1552891 := bstep (se 1 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 1552891 = 2329337) B2329337
theorem B1749559 : Blo 362758 1749559 := bstep (se 1 (by rfl) ⟨1312169, by rfl⟩ : syracuseStep 1749559 = 2624339) B2624339
theorem B2962369 : Blo 362758 2962369 := bstep (se 2 (by rfl) ⟨1110888, by rfl⟩ : syracuseStep 2962369 = 2221777) B2221777
theorem B1390355 : Blo 362758 1390355 := bstep (se 1 (by rfl) ⟨1042766, by rfl⟩ : syracuseStep 1390355 = 2085533) B2085533
theorem B2635985 : Blo 362758 2635985 := bstep (se 2 (by rfl) ⟨988494, by rfl⟩ : syracuseStep 2635985 = 1976989) B1976989
theorem B2079017 : Blo 362758 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B4012667 : Blo 362758 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B1850849 : Blo 362758 1850849 := bstep (se 2 (by rfl) ⟨694068, by rfl⟩ : syracuseStep 1850849 = 1388137) B1388137
theorem B671771 : Blo 362758 671771 := bstep (se 1 (by rfl) ⟨503828, by rfl⟩ : syracuseStep 671771 = 1007657) B1007657
theorem B6996077 : Blo 362758 6996077 := bstep (se 3 (by rfl) ⟨1311764, by rfl⟩ : syracuseStep 6996077 = 2623529) B2623529
theorem B2212339 : Blo 362758 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B1229417 : Blo 362758 1229417 := bstep (se 2 (by rfl) ⟨461031, by rfl⟩ : syracuseStep 1229417 = 922063) B922063
theorem B3556655 : Blo 362758 3556655 := bstep (se 1 (by rfl) ⟨2667491, by rfl⟩ : syracuseStep 3556655 = 5334983) B5334983
theorem B2213993 : Blo 362758 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B12830875 : Blo 362758 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B2672891 : Blo 362758 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B2804057 : Blo 362758 2804057 := bstep (se 2 (by rfl) ⟨1051521, by rfl⟩ : syracuseStep 2804057 = 2103043) B2103043
theorem B1034633 : Blo 362758 1034633 := bstep (se 2 (by rfl) ⟨387987, by rfl⟩ : syracuseStep 1034633 = 775975) B775975
theorem B1558921 : Blo 362758 1558921 := bstep (se 2 (by rfl) ⟨584595, by rfl⟩ : syracuseStep 1558921 = 1169191) B1169191
theorem B5720539 : Blo 362758 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B937067 : Blo 362758 937067 := bstep (se 1 (by rfl) ⟨702800, by rfl⟩ : syracuseStep 937067 = 1405601) B1405601
theorem B1232495 : Blo 362758 1232495 := bstep (se 1 (by rfl) ⟨924371, by rfl⟩ : syracuseStep 1232495 = 1848743) B1848743
theorem B544415 : Blo 362758 544415 := bstep (se 1 (by rfl) ⟨408311, by rfl⟩ : syracuseStep 544415 = 816623) B816623
theorem B544745 : Blo 362758 544745 := bstep (se 2 (by rfl) ⟨204279, by rfl⟩ : syracuseStep 544745 = 408559) B408559
theorem B544799 : Blo 362758 544799 := bstep (se 1 (by rfl) ⟨408599, by rfl⟩ : syracuseStep 544799 = 817199) B817199
theorem B10506347 : Blo 362758 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B1167551 : Blo 362758 1167551 := bstep (se 1 (by rfl) ⟨875663, by rfl⟩ : syracuseStep 1167551 = 1751327) B1751327
theorem B741583 : Blo 362758 741583 := bstep (se 1 (by rfl) ⟨556187, by rfl⟩ : syracuseStep 741583 = 1112375) B1112375
theorem B545327 : Blo 362758 545327 := bstep (se 1 (by rfl) ⟨408995, by rfl⟩ : syracuseStep 545327 = 817991) B817991
theorem B545513 : Blo 362758 545513 := bstep (se 2 (by rfl) ⟨204567, by rfl⟩ : syracuseStep 545513 = 409135) B409135
theorem B2806589 : Blo 362758 2806589 := bstep (se 3 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 2806589 = 1052471) B1052471
theorem B545657 : Blo 362758 545657 := bstep (se 2 (by rfl) ⟨204621, by rfl⟩ : syracuseStep 545657 = 409243) B409243
theorem B5886857 : Blo 362758 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B1233953 : Blo 362758 1233953 := bstep (se 2 (by rfl) ⟨462732, by rfl⟩ : syracuseStep 1233953 = 925465) B925465
theorem B11883611 : Blo 362758 11883611 := bstep (se 1 (by rfl) ⟨8912708, by rfl⟩ : syracuseStep 11883611 = 17825417) B17825417
theorem B33576281 : Blo 362758 33576281 := bstep (se 2 (by rfl) ⟨12591105, by rfl⟩ : syracuseStep 33576281 = 25182211) B25182211
theorem B873895 : Blo 362758 873895 := bstep (se 1 (by rfl) ⟨655421, by rfl⟩ : syracuseStep 873895 = 1310843) B1310843
theorem B3102259 : Blo 362758 3102259 := bstep (se 1 (by rfl) ⟨2326694, by rfl⟩ : syracuseStep 3102259 = 4653389) B4653389
theorem B546359 : Blo 362758 546359 := bstep (se 1 (by rfl) ⟨409769, by rfl⟩ : syracuseStep 546359 = 819539) B819539
theorem B14014295 : Blo 362758 14014295 := bstep (se 1 (by rfl) ⟨10510721, by rfl⟩ : syracuseStep 14014295 = 21021443) B21021443
theorem B1890145 : Blo 362758 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B1234817 : Blo 362758 1234817 := bstep (se 2 (by rfl) ⟨463056, by rfl⟩ : syracuseStep 1234817 = 926113) B926113
theorem B546863 : Blo 362758 546863 := bstep (se 1 (by rfl) ⟨410147, by rfl⟩ : syracuseStep 546863 = 820295) B820295
theorem B546983 : Blo 362758 546983 := bstep (se 1 (by rfl) ⟨410237, by rfl⟩ : syracuseStep 546983 = 820475) B820475
theorem B547151 : Blo 362758 547151 := bstep (se 1 (by rfl) ⟨410363, by rfl⟩ : syracuseStep 547151 = 820727) B820727
theorem B2349431 : Blo 362758 2349431 := bstep (se 1 (by rfl) ⟨1762073, by rfl⟩ : syracuseStep 2349431 = 3524147) B3524147
theorem B1039007 : Blo 362758 1039007 := bstep (se 1 (by rfl) ⟨779255, by rfl⟩ : syracuseStep 1039007 = 1558511) B1558511
theorem B1563295 : Blo 362758 1563295 := bstep (se 1 (by rfl) ⟨1172471, by rfl⟩ : syracuseStep 1563295 = 2344943) B2344943
theorem B1039031 : Blo 362758 1039031 := bstep (se 1 (by rfl) ⟨779273, by rfl⟩ : syracuseStep 1039031 = 1558547) B1558547
theorem B613055 : Blo 362758 613055 := bstep (se 1 (by rfl) ⟨459791, by rfl⟩ : syracuseStep 613055 = 919583) B919583
theorem B613129 : Blo 362758 613129 := bstep (se 2 (by rfl) ⟨229923, by rfl⟩ : syracuseStep 613129 = 459847) B459847
theorem B547871 : Blo 362758 547871 := bstep (se 1 (by rfl) ⟨410903, by rfl⟩ : syracuseStep 547871 = 821807) B821807
theorem B1236059 : Blo 362758 1236059 := bstep (se 1 (by rfl) ⟨927044, by rfl⟩ : syracuseStep 1236059 = 1854089) B1854089
theorem B548303 : Blo 362758 548303 := bstep (se 1 (by rfl) ⟨411227, by rfl⟩ : syracuseStep 548303 = 822455) B822455
theorem B516719 : Blo 362758 516719 := bstep (se 1 (by rfl) ⟨387539, by rfl⟩ : syracuseStep 516719 = 775079) B775079
theorem B1467143 : Blo 362758 1467143 := bstep (se 1 (by rfl) ⟨1100357, by rfl⟩ : syracuseStep 1467143 = 2200715) B2200715
theorem B549839 : Blo 362758 549839 := bstep (se 1 (by rfl) ⟨412379, by rfl⟩ : syracuseStep 549839 = 824759) B824759
theorem B549887 : Blo 362758 549887 := bstep (se 1 (by rfl) ⟨412415, by rfl⟩ : syracuseStep 549887 = 824831) B824831
theorem B549959 : Blo 362758 549959 := bstep (se 1 (by rfl) ⟨412469, by rfl⟩ : syracuseStep 549959 = 824939) B824939
theorem B615647 : Blo 362758 615647 := bstep (se 1 (by rfl) ⟨461735, by rfl⟩ : syracuseStep 615647 = 923471) B923471
theorem B615991 : Blo 362758 615991 := bstep (se 1 (by rfl) ⟨461993, by rfl⟩ : syracuseStep 615991 = 923987) B923987
theorem B518815 : Blo 362758 518815 := bstep (se 1 (by rfl) ⟨389111, by rfl⟩ : syracuseStep 518815 = 778223) B778223
theorem B551711 : Blo 362758 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B3107969 : Blo 362758 3107969 := bstep (se 2 (by rfl) ⟨1165488, by rfl⟩ : syracuseStep 3107969 = 2330977) B2330977
theorem B618151 : Blo 362758 618151 := bstep (se 1 (by rfl) ⟨463613, by rfl⟩ : syracuseStep 618151 = 927227) B927227
theorem B2780891 : Blo 362758 2780891 := bstep (se 1 (by rfl) ⟨2085668, by rfl⟩ : syracuseStep 2780891 = 4171337) B4171337
theorem B618475 : Blo 362758 618475 := bstep (se 1 (by rfl) ⟨463856, by rfl⟩ : syracuseStep 618475 = 927713) B927713
theorem B9990125 : Blo 362758 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B881065 : Blo 362758 881065 := bstep (se 2 (by rfl) ⟨330399, by rfl⟩ : syracuseStep 881065 = 660799) B660799
theorem B9369107 : Blo 362758 9369107 := bstep (se 1 (by rfl) ⟨7026830, by rfl⟩ : syracuseStep 9369107 = 14053661) B14053661
theorem B423451 : Blo 362758 423451 := bstep (se 1 (by rfl) ⟨317588, by rfl⟩ : syracuseStep 423451 = 635177) B635177
theorem B3111007 : Blo 362758 3111007 := bstep (se 1 (by rfl) ⟨2333255, by rfl⟩ : syracuseStep 3111007 = 4666511) B4666511
theorem B817577 : Blo 362758 817577 := bstep (se 2 (by rfl) ⟨306591, by rfl⟩ : syracuseStep 817577 = 613183) B613183
theorem B817631 : Blo 362758 817631 := bstep (se 1 (by rfl) ⟨613223, by rfl⟩ : syracuseStep 817631 = 1226447) B1226447
theorem B4979407 : Blo 362758 4979407 := bstep (se 1 (by rfl) ⟨3734555, by rfl⟩ : syracuseStep 4979407 = 7469111) B7469111
theorem B2784293 : Blo 362758 2784293 := bstep (se 4 (by rfl) ⟨261027, by rfl⟩ : syracuseStep 2784293 = 522055) B522055
theorem B1244335 : Blo 362758 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B818855 : Blo 362758 818855 := bstep (se 1 (by rfl) ⟨614141, by rfl⟩ : syracuseStep 818855 = 1228283) B1228283
theorem B851707 : Blo 362758 851707 := bstep (se 1 (by rfl) ⟨638780, by rfl⟩ : syracuseStep 851707 = 1277561) B1277561
theorem B1474375 : Blo 362758 1474375 := bstep (se 1 (by rfl) ⟨1105781, by rfl⟩ : syracuseStep 1474375 = 2211563) B2211563
theorem B819611 : Blo 362758 819611 := bstep (se 1 (by rfl) ⟨614708, by rfl⟩ : syracuseStep 819611 = 1229417) B1229417
theorem B2949785 : Blo 362758 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B1475995 : Blo 362758 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B1869371 : Blo 362758 1869371 := bstep (se 1 (by rfl) ⟨1402028, by rfl⟩ : syracuseStep 1869371 = 2804057) B2804057
theorem B919147 : Blo 362758 919147 := bstep (se 1 (by rfl) ⟨689360, by rfl⟩ : syracuseStep 919147 = 1378721) B1378721
theorem B1377917 : Blo 362758 1377917 := bstep (se 3 (by rfl) ⟨258359, by rfl⟩ : syracuseStep 1377917 = 516719) B516719
theorem B19990547 : Blo 362758 19990547 := bstep (se 1 (by rfl) ⟨14992910, by rfl⟩ : syracuseStep 19990547 = 29985821) B29985821
theorem B821321 : Blo 362758 821321 := bstep (se 2 (by rfl) ⟨307995, by rfl⟩ : syracuseStep 821321 = 615991) B615991
theorem B821663 : Blo 362758 821663 := bstep (se 1 (by rfl) ⟨616247, by rfl⟩ : syracuseStep 821663 = 1232495) B1232495
theorem B362943 : Blo 362758 362943 := bstep (se 1 (by rfl) ⟨272207, by rfl⟩ : syracuseStep 362943 = 544415) B544415
theorem B363163 : Blo 362758 363163 := bstep (se 1 (by rfl) ⟨272372, by rfl⟩ : syracuseStep 363163 = 544745) B544745
theorem B363199 : Blo 362758 363199 := bstep (se 1 (by rfl) ⟨272399, by rfl⟩ : syracuseStep 363199 = 544799) B544799
theorem B920423 : Blo 362758 920423 := bstep (se 1 (by rfl) ⟨690317, by rfl⟩ : syracuseStep 920423 = 1380635) B1380635
theorem B920585 : Blo 362758 920585 := bstep (se 2 (by rfl) ⟨345219, by rfl⟩ : syracuseStep 920585 = 690439) B690439
theorem B363551 : Blo 362758 363551 := bstep (se 1 (by rfl) ⟨272663, by rfl⟩ : syracuseStep 363551 = 545327) B545327
theorem B363675 : Blo 362758 363675 := bstep (se 1 (by rfl) ⟨272756, by rfl⟩ : syracuseStep 363675 = 545513) B545513
theorem B1871059 : Blo 362758 1871059 := bstep (se 1 (by rfl) ⟨1403294, by rfl⟩ : syracuseStep 1871059 = 2806589) B2806589
theorem B363771 : Blo 362758 363771 := bstep (se 1 (by rfl) ⟨272828, by rfl⟩ : syracuseStep 363771 = 545657) B545657
theorem B3476807 : Blo 362758 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B822635 : Blo 362758 822635 := bstep (se 1 (by rfl) ⟨616976, by rfl⟩ : syracuseStep 822635 = 1233953) B1233953
theorem B691753 : Blo 362758 691753 := bstep (se 2 (by rfl) ⟨259407, by rfl⟩ : syracuseStep 691753 = 518815) B518815
theorem B22384187 : Blo 362758 22384187 := bstep (se 1 (by rfl) ⟨16788140, by rfl⟩ : syracuseStep 22384187 = 33576281) B33576281
theorem B364239 : Blo 362758 364239 := bstep (se 1 (by rfl) ⟨273179, by rfl⟩ : syracuseStep 364239 = 546359) B546359
theorem B921415 : Blo 362758 921415 := bstep (se 1 (by rfl) ⟨691061, by rfl⟩ : syracuseStep 921415 = 1382123) B1382123
theorem B9342863 : Blo 362758 9342863 := bstep (se 1 (by rfl) ⟨7007147, by rfl⟩ : syracuseStep 9342863 = 14014295) B14014295
theorem B823211 : Blo 362758 823211 := bstep (se 1 (by rfl) ⟨617408, by rfl⟩ : syracuseStep 823211 = 1234817) B1234817
theorem B364575 : Blo 362758 364575 := bstep (se 1 (by rfl) ⟨273431, by rfl⟩ : syracuseStep 364575 = 546863) B546863
theorem B364655 : Blo 362758 364655 := bstep (se 1 (by rfl) ⟨273491, by rfl⟩ : syracuseStep 364655 = 546983) B546983
theorem B921739 : Blo 362758 921739 := bstep (se 1 (by rfl) ⟨691304, by rfl⟩ : syracuseStep 921739 = 1382609) B1382609
theorem B364767 : Blo 362758 364767 := bstep (se 1 (by rfl) ⟨273575, by rfl⟩ : syracuseStep 364767 = 547151) B547151
theorem B2167067 : Blo 362758 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B692687 : Blo 362758 692687 := bstep (se 1 (by rfl) ⟨519515, by rfl⟩ : syracuseStep 692687 = 1039031) B1039031
theorem B365247 : Blo 362758 365247 := bstep (se 1 (by rfl) ⟨273935, by rfl⟩ : syracuseStep 365247 = 547871) B547871
theorem B824039 : Blo 362758 824039 := bstep (se 1 (by rfl) ⟨618029, by rfl⟩ : syracuseStep 824039 = 1236059) B1236059
theorem B824201 : Blo 362758 824201 := bstep (se 2 (by rfl) ⟨309075, by rfl⟩ : syracuseStep 824201 = 618151) B618151
theorem B365535 : Blo 362758 365535 := bstep (se 1 (by rfl) ⟨274151, by rfl⟩ : syracuseStep 365535 = 548303) B548303
theorem B824633 : Blo 362758 824633 := bstep (se 2 (by rfl) ⟨309237, by rfl⟩ : syracuseStep 824633 = 618475) B618475
theorem B988777 : Blo 362758 988777 := bstep (se 2 (by rfl) ⟨370791, by rfl⟩ : syracuseStep 988777 = 741583) B741583
theorem B1972127 : Blo 362758 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B366559 : Blo 362758 366559 := bstep (se 1 (by rfl) ⟨274919, by rfl⟩ : syracuseStep 366559 = 549839) B549839
theorem B2070521 : Blo 362758 2070521 := bstep (se 2 (by rfl) ⟨776445, by rfl⟩ : syracuseStep 2070521 = 1552891) B1552891
theorem B366591 : Blo 362758 366591 := bstep (se 1 (by rfl) ⟨274943, by rfl⟩ : syracuseStep 366591 = 549887) B549887
theorem B366639 : Blo 362758 366639 := bstep (se 1 (by rfl) ⟨274979, by rfl⟩ : syracuseStep 366639 = 549959) B549959
theorem B2332745 : Blo 362758 2332745 := bstep (se 2 (by rfl) ⟨874779, by rfl⟩ : syracuseStep 2332745 = 1749559) B1749559
theorem B1907023 : Blo 362758 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B2759021 : Blo 362758 2759021 := bstep (se 3 (by rfl) ⟨517316, by rfl⟩ : syracuseStep 2759021 = 1034633) B1034633
theorem B924655 : Blo 362758 924655 := bstep (se 1 (by rfl) ⟨693491, by rfl⟩ : syracuseStep 924655 = 1386983) B1386983
theorem B2628895 : Blo 362758 2628895 := bstep (se 1 (by rfl) ⟨1971671, by rfl⟩ : syracuseStep 2628895 = 3943343) B3943343
theorem B4136345 : Blo 362758 4136345 := bstep (se 2 (by rfl) ⟨1551129, by rfl⟩ : syracuseStep 4136345 = 3102259) B3102259
theorem B2071979 : Blo 362758 2071979 := bstep (se 1 (by rfl) ⟨1553984, by rfl⟩ : syracuseStep 2071979 = 3107969) B3107969
theorem B925607 : Blo 362758 925607 := bstep (se 1 (by rfl) ⟨694205, by rfl⟩ : syracuseStep 925607 = 1388411) B1388411
theorem B6660083 : Blo 362758 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B2498845 : Blo 362758 2498845 := bstep (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) B937067
theorem B926903 : Blo 362758 926903 := bstep (se 1 (by rfl) ⟨695177, by rfl⟩ : syracuseStep 926903 = 1390355) B1390355
theorem B1386011 : Blo 362758 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B4664051 : Blo 362758 4664051 := bstep (se 1 (by rfl) ⟨3498038, by rfl⟩ : syracuseStep 4664051 = 6996077) B6996077
theorem B437275 : Blo 362758 437275 := bstep (se 1 (by rfl) ⟨327956, by rfl⟩ : syracuseStep 437275 = 655913) B655913
theorem B68431333 : Blo 362758 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B2371103 : Blo 362758 2371103 := bstep (se 1 (by rfl) ⟨1778327, by rfl⟩ : syracuseStep 2371103 = 3556655) B3556655
theorem B232697939 : Blo 362758 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B1781927 : Blo 362758 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B1225151 : Blo 362758 1225151 := bstep (se 1 (by rfl) ⟨918863, by rfl⟩ : syracuseStep 1225151 = 1837727) B1837727
theorem B1750079 : Blo 362758 1750079 := bstep (se 1 (by rfl) ⟨1312559, by rfl⟩ : syracuseStep 1750079 = 2625119) B2625119
theorem B2536555 : Blo 362758 2536555 := bstep (se 1 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 2536555 = 3804833) B3804833
theorem B2078561 : Blo 362758 2078561 := bstep (se 2 (by rfl) ⟨779460, by rfl⟩ : syracuseStep 2078561 = 1558921) B1558921
theorem B1849553 : Blo 362758 1849553 := bstep (se 2 (by rfl) ⟨693582, by rfl⟩ : syracuseStep 1849553 = 1387165) B1387165
theorem B1227311 : Blo 362758 1227311 := bstep (se 1 (by rfl) ⟨920483, by rfl⟩ : syracuseStep 1227311 = 1840967) B1840967
theorem B3947057 : Blo 362758 3947057 := bstep (se 2 (by rfl) ⟨1480146, by rfl⟩ : syracuseStep 3947057 = 2960293) B2960293
theorem B1227743 : Blo 362758 1227743 := bstep (se 1 (by rfl) ⟨920807, by rfl⟩ : syracuseStep 1227743 = 1841615) B1841615
theorem B408703 : Blo 362758 408703 := bstep (se 1 (by rfl) ⟨306527, by rfl⟩ : syracuseStep 408703 = 613055) B613055
theorem B8011649 : Blo 362758 8011649 := bstep (se 2 (by rfl) ⟨3004368, by rfl⟩ : syracuseStep 8011649 = 6008737) B6008737
theorem B5948093 : Blo 362758 5948093 := bstep (se 3 (by rfl) ⟨1115267, by rfl⟩ : syracuseStep 5948093 = 2230535) B2230535
theorem B410431 : Blo 362758 410431 := bstep (se 1 (by rfl) ⟨307823, by rfl⟩ : syracuseStep 410431 = 615647) B615647
theorem B1033199 : Blo 362758 1033199 := bstep (se 1 (by rfl) ⟨774899, by rfl⟩ : syracuseStep 1033199 = 1549799) B1549799
theorem B3949825 : Blo 362758 3949825 := bstep (se 2 (by rfl) ⟨1481184, by rfl⟩ : syracuseStep 3949825 = 2962369) B2962369
theorem B2770685 : Blo 362758 2770685 := bstep (se 3 (by rfl) ⟨519503, by rfl⟩ : syracuseStep 2770685 = 1039007) B1039007
theorem B5293907 : Blo 362758 5293907 := bstep (se 1 (by rfl) ⟨3970430, by rfl⟩ : syracuseStep 5293907 = 7940861) B7940861
theorem B1165193 : Blo 362758 1165193 := bstep (se 2 (by rfl) ⟨436947, by rfl⟩ : syracuseStep 1165193 = 873895) B873895
theorem B1231037 : Blo 362758 1231037 := bstep (se 3 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 1231037 = 461639) B461639
theorem B1231145 : Blo 362758 1231145 := bstep (se 2 (by rfl) ⟨461679, by rfl⟩ : syracuseStep 1231145 = 923359) B923359
theorem B1853927 : Blo 362758 1853927 := bstep (se 1 (by rfl) ⟨1390445, by rfl⟩ : syracuseStep 1853927 = 2780891) B2780891
theorem B4148009 : Blo 362758 4148009 := bstep (se 2 (by rfl) ⟨1555503, by rfl⟩ : syracuseStep 4148009 = 3111007) B3111007
theorem B2084393 : Blo 362758 2084393 := bstep (se 2 (by rfl) ⟨781647, by rfl⟩ : syracuseStep 2084393 = 1563295) B1563295
theorem B6639209 : Blo 362758 6639209 := bstep (se 2 (by rfl) ⟨2489703, by rfl⟩ : syracuseStep 6639209 = 4979407) B4979407
theorem B6246071 : Blo 362758 6246071 := bstep (se 1 (by rfl) ⟨4684553, by rfl⟩ : syracuseStep 6246071 = 9369107) B9369107
theorem B1232765 : Blo 362758 1232765 := bstep (se 3 (by rfl) ⟨231143, by rfl⟩ : syracuseStep 1232765 = 462287) B462287
theorem B4542437 : Blo 362758 4542437 := bstep (se 4 (by rfl) ⟨425853, by rfl⟩ : syracuseStep 4542437 = 851707) B851707
theorem B1757323 : Blo 362758 1757323 := bstep (se 1 (by rfl) ⟨1317992, by rfl⟩ : syracuseStep 1757323 = 2635985) B2635985
theorem B1659113 : Blo 362758 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B545051 : Blo 362758 545051 := bstep (se 1 (by rfl) ⟨408788, by rfl⟩ : syracuseStep 545051 = 817577) B817577
theorem B545087 : Blo 362758 545087 := bstep (se 1 (by rfl) ⟨408815, by rfl⟩ : syracuseStep 545087 = 817631) B817631
theorem B2675111 : Blo 362758 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B10080773 : Blo 362758 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B1856195 : Blo 362758 1856195 := bstep (se 1 (by rfl) ⟨1392146, by rfl⟩ : syracuseStep 1856195 = 2784293) B2784293
theorem B1233899 : Blo 362758 1233899 := bstep (se 1 (by rfl) ⟨925424, by rfl⟩ : syracuseStep 1233899 = 1850849) B1850849
theorem B545903 : Blo 362758 545903 := bstep (se 1 (by rfl) ⟨409427, by rfl⟩ : syracuseStep 545903 = 818855) B818855
theorem B1791389 : Blo 362758 1791389 := bstep (se 3 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 1791389 = 671771) B671771
theorem B612535 : Blo 362758 612535 := bstep (se 1 (by rfl) ⟨459401, by rfl⟩ : syracuseStep 612535 = 918803) B918803
theorem B547055 : Blo 362758 547055 := bstep (se 1 (by rfl) ⟨410291, by rfl⟩ : syracuseStep 547055 = 820583) B820583
theorem B1235357 : Blo 362758 1235357 := bstep (se 3 (by rfl) ⟨231629, by rfl⟩ : syracuseStep 1235357 = 463259) B463259
theorem B547835 : Blo 362758 547835 := bstep (se 1 (by rfl) ⟨410876, by rfl⟩ : syracuseStep 547835 = 821753) B821753
theorem B548075 : Blo 362758 548075 := bstep (se 1 (by rfl) ⟨411056, by rfl⟩ : syracuseStep 548075 = 822113) B822113
theorem B35872465 : Blo 362758 35872465 := bstep (se 2 (by rfl) ⟨13452174, by rfl⟩ : syracuseStep 35872465 = 26904349) B26904349
theorem B548687 : Blo 362758 548687 := bstep (se 1 (by rfl) ⟨411515, by rfl⟩ : syracuseStep 548687 = 823031) B823031
theorem B7004231 : Blo 362758 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B778367 : Blo 362758 778367 := bstep (se 1 (by rfl) ⟨583775, by rfl⟩ : syracuseStep 778367 = 1167551) B1167551
theorem B614695 : Blo 362758 614695 := bstep (se 1 (by rfl) ⟨461021, by rfl⟩ : syracuseStep 614695 = 922043) B922043
theorem B549167 : Blo 362758 549167 := bstep (se 1 (by rfl) ⟨411875, by rfl⟩ : syracuseStep 549167 = 823751) B823751
theorem B13525451 : Blo 362758 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B549407 : Blo 362758 549407 := bstep (se 1 (by rfl) ⟨412055, by rfl⟩ : syracuseStep 549407 = 824111) B824111
theorem B3924571 : Blo 362758 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B7627385 : Blo 362758 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B7922407 : Blo 362758 7922407 := bstep (se 1 (by rfl) ⟨5941805, by rfl⟩ : syracuseStep 7922407 = 11883611) B11883611
theorem B549659 : Blo 362758 549659 := bstep (se 1 (by rfl) ⟨412244, by rfl⟩ : syracuseStep 549659 = 824489) B824489
theorem B1566287 : Blo 362758 1566287 := bstep (se 1 (by rfl) ⟨1174715, by rfl⟩ : syracuseStep 1566287 = 2349431) B2349431
theorem B7563527 : Blo 362758 7563527 := bstep (se 1 (by rfl) ⟨5672645, by rfl⟩ : syracuseStep 7563527 = 11345291) B11345291
theorem B616943 : Blo 362758 616943 := bstep (se 1 (by rfl) ⟨462707, by rfl⟩ : syracuseStep 616943 = 925415) B925415
theorem B617449 : Blo 362758 617449 := bstep (se 2 (by rfl) ⟨231543, by rfl⟩ : syracuseStep 617449 = 463087) B463087
theorem B978095 : Blo 362758 978095 := bstep (se 1 (by rfl) ⟨733571, by rfl⟩ : syracuseStep 978095 = 1467143) B1467143
theorem B1174753 : Blo 362758 1174753 := bstep (se 2 (by rfl) ⟨440532, by rfl⟩ : syracuseStep 1174753 = 881065) B881065
theorem B9268465 : Blo 362758 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B880507 : Blo 362758 880507 := bstep (se 1 (by rfl) ⟨660380, by rfl⟩ : syracuseStep 880507 = 1320761) B1320761
theorem B1471229 : Blo 362758 1471229 := bstep (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) B551711
theorem B7468469 : Blo 362758 7468469 := bstep (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) B700169
theorem B2258405 : Blo 362758 2258405 := bstep (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) B423451
theorem B817505 : Blo 362758 817505 := bstep (se 2 (by rfl) ⟨306564, by rfl⟩ : syracuseStep 817505 = 613129) B613129
theorem B1965833 : Blo 362758 1965833 := bstep (se 2 (by rfl) ⟨737187, by rfl⟩ : syracuseStep 1965833 = 1474375) B1474375
theorem B620527837 : Blo 362758 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B819593 : Blo 362758 819593 := bstep (se 2 (by rfl) ⟨307347, by rfl⟩ : syracuseStep 819593 = 614695) B614695
theorem B1966523 : Blo 362758 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B688799 : Blo 362758 688799 := bstep (se 1 (by rfl) ⟨516599, by rfl⟩ : syracuseStep 688799 = 1033199) B1033199
theorem B1246247 : Blo 362758 1246247 := bstep (se 1 (by rfl) ⟨934685, by rfl⟩ : syracuseStep 1246247 = 1869371) B1869371
theorem B918611 : Blo 362758 918611 := bstep (se 1 (by rfl) ⟨688958, by rfl⟩ : syracuseStep 918611 = 1377917) B1377917
theorem B820691 : Blo 362758 820691 := bstep (se 1 (by rfl) ⟨615518, by rfl⟩ : syracuseStep 820691 = 1231037) B1231037
theorem B820763 : Blo 362758 820763 := bstep (se 1 (by rfl) ⟨615572, by rfl⟩ : syracuseStep 820763 = 1231145) B1231145
theorem B15861581 : Blo 362758 15861581 := bstep (se 3 (by rfl) ⟨2974046, by rfl⟩ : syracuseStep 15861581 = 5948093) B5948093
theorem B1967993 : Blo 362758 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B4426139 : Blo 362758 4426139 := bstep (se 1 (by rfl) ⟨3319604, by rfl⟩ : syracuseStep 4426139 = 6639209) B6639209
theorem B4164047 : Blo 362758 4164047 := bstep (se 1 (by rfl) ⟨3123035, by rfl⟩ : syracuseStep 4164047 = 6246071) B6246071
theorem B821843 : Blo 362758 821843 := bstep (se 1 (by rfl) ⟨616382, by rfl⟩ : syracuseStep 821843 = 1232765) B1232765
theorem B6228575 : Blo 362758 6228575 := bstep (se 1 (by rfl) ⟨4671431, by rfl⟩ : syracuseStep 6228575 = 9342863) B9342863
theorem B363367 : Blo 362758 363367 := bstep (se 1 (by rfl) ⟨272525, by rfl⟩ : syracuseStep 363367 = 545051) B545051
theorem B1444711 : Blo 362758 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B363391 : Blo 362758 363391 := bstep (se 1 (by rfl) ⟨272543, by rfl⟩ : syracuseStep 363391 = 545087) B545087
theorem B461791 : Blo 362758 461791 := bstep (se 1 (by rfl) ⟨346343, by rfl⟩ : syracuseStep 461791 = 692687) B692687
theorem B6720515 : Blo 362758 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B822599 : Blo 362758 822599 := bstep (se 1 (by rfl) ⟨616949, by rfl⟩ : syracuseStep 822599 = 1233899) B1233899
theorem B363935 : Blo 362758 363935 := bstep (se 1 (by rfl) ⟨272951, by rfl⟩ : syracuseStep 363935 = 545903) B545903
theorem B823265 : Blo 362758 823265 := bstep (se 2 (by rfl) ⟨308724, by rfl⟩ : syracuseStep 823265 = 617449) B617449
theorem B1380347 : Blo 362758 1380347 := bstep (se 1 (by rfl) ⟨1035260, by rfl⟩ : syracuseStep 1380347 = 2070521) B2070521
theorem B364703 : Blo 362758 364703 := bstep (se 1 (by rfl) ⟨273527, by rfl⟩ : syracuseStep 364703 = 547055) B547055
theorem B1839347 : Blo 362758 1839347 := bstep (se 1 (by rfl) ⟨1379510, by rfl⟩ : syracuseStep 1839347 = 2759021) B2759021
theorem B823571 : Blo 362758 823571 := bstep (se 1 (by rfl) ⟨617678, by rfl⟩ : syracuseStep 823571 = 1235357) B1235357
theorem B2494745 : Blo 362758 2494745 := bstep (se 2 (by rfl) ⟨935529, by rfl⟩ : syracuseStep 2494745 = 1871059) B1871059
theorem B12357953 : Blo 362758 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B365223 : Blo 362758 365223 := bstep (se 1 (by rfl) ⟨273917, by rfl⟩ : syracuseStep 365223 = 547835) B547835
theorem B922337 : Blo 362758 922337 := bstep (se 2 (by rfl) ⟨345876, by rfl⟩ : syracuseStep 922337 = 691753) B691753
theorem B365383 : Blo 362758 365383 := bstep (se 1 (by rfl) ⟨274037, by rfl⟩ : syracuseStep 365383 = 548075) B548075
theorem B2757563 : Blo 362758 2757563 := bstep (se 1 (by rfl) ⟨2068172, by rfl⟩ : syracuseStep 2757563 = 4136345) B4136345
theorem B1381319 : Blo 362758 1381319 := bstep (se 1 (by rfl) ⟨1035989, by rfl⟩ : syracuseStep 1381319 = 2071979) B2071979
theorem B365791 : Blo 362758 365791 := bstep (se 1 (by rfl) ⟨274343, by rfl⟩ : syracuseStep 365791 = 548687) B548687
theorem B366111 : Blo 362758 366111 := bstep (se 1 (by rfl) ⟨274583, by rfl⟩ : syracuseStep 366111 = 549167) B549167
theorem B9016967 : Blo 362758 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B366271 : Blo 362758 366271 := bstep (se 1 (by rfl) ⟨274703, by rfl⟩ : syracuseStep 366271 = 549407) B549407
theorem B366439 : Blo 362758 366439 := bstep (se 1 (by rfl) ⟨274829, by rfl⟩ : syracuseStep 366439 = 549659) B549659
theorem B924007 : Blo 362758 924007 := bstep (se 1 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 924007 = 1386011) B1386011
theorem B3382073 : Blo 362758 3382073 := bstep (se 2 (by rfl) ⟨1268277, by rfl⟩ : syracuseStep 3382073 = 2536555) B2536555
theorem B1318369 : Blo 362758 1318369 := bstep (se 2 (by rfl) ⟨494388, by rfl⟩ : syracuseStep 1318369 = 988777) B988777
theorem B1580735 : Blo 362758 1580735 := bstep (se 1 (by rfl) ⟨1185551, by rfl⟩ : syracuseStep 1580735 = 2371103) B2371103
theorem B1187951 : Blo 362758 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B1385707 : Blo 362758 1385707 := bstep (se 1 (by rfl) ⟨1039280, by rfl⟩ : syracuseStep 1385707 = 2078561) B2078561
theorem B2631371 : Blo 362758 2631371 := bstep (se 1 (by rfl) ⟨1973528, by rfl⟩ : syracuseStep 2631371 = 3947057) B3947057
theorem B2075645 : Blo 362758 2075645 := bstep (se 3 (by rfl) ⟨389183, by rfl⟩ : syracuseStep 2075645 = 778367) B778367
theorem B10563209 : Blo 362758 10563209 := bstep (se 2 (by rfl) ⟨3961203, by rfl⟩ : syracuseStep 10563209 = 7922407) B7922407
theorem B1847123 : Blo 362758 1847123 := bstep (se 1 (by rfl) ⟨1385342, by rfl⟩ : syracuseStep 1847123 = 2770685) B2770685
theorem B2765339 : Blo 362758 2765339 := bstep (se 1 (by rfl) ⟨2074004, by rfl⟩ : syracuseStep 2765339 = 4148009) B4148009
theorem B1225529 : Blo 362758 1225529 := bstep (se 2 (by rfl) ⟨459573, by rfl⟩ : syracuseStep 1225529 = 919147) B919147
theorem B1389595 : Blo 362758 1389595 := bstep (se 1 (by rfl) ⟨1042196, by rfl⟩ : syracuseStep 1389595 = 2084393) B2084393
theorem B14922791 : Blo 362758 14922791 := bstep (se 1 (by rfl) ⟨11192093, by rfl⟩ : syracuseStep 14922791 = 22384187) B22384187
theorem B3028291 : Blo 362758 3028291 := bstep (se 1 (by rfl) ⟨2271218, by rfl⟩ : syracuseStep 3028291 = 4542437) B4542437
theorem B1194259 : Blo 362758 1194259 := bstep (se 1 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 1194259 = 1791389) B1791389
theorem B1555163 : Blo 362758 1555163 := bstep (se 1 (by rfl) ⟨1166372, by rfl⟩ : syracuseStep 1555163 = 2332745) B2332745
theorem B91241777 : Blo 362758 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B5259005 : Blo 362758 5259005 := bstep (se 3 (by rfl) ⟨986063, by rfl⟩ : syracuseStep 5259005 = 1972127) B1972127
theorem B1228553 : Blo 362758 1228553 := bstep (se 2 (by rfl) ⟨460707, by rfl⟩ : syracuseStep 1228553 = 921415) B921415
theorem B4440055 : Blo 362758 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B4669487 : Blo 362758 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B1228985 : Blo 362758 1228985 := bstep (se 2 (by rfl) ⟨460869, by rfl⟩ : syracuseStep 1228985 = 921739) B921739
theorem B2343097 : Blo 362758 2343097 := bstep (se 2 (by rfl) ⟨878661, by rfl⟩ : syracuseStep 2343097 = 1757323) B1757323
theorem B411295 : Blo 362758 411295 := bstep (se 1 (by rfl) ⟨308471, by rfl⟩ : syracuseStep 411295 = 616943) B616943
theorem B2542697 : Blo 362758 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B1166719 : Blo 362758 1166719 := bstep (se 1 (by rfl) ⟨875039, by rfl⟩ : syracuseStep 1166719 = 1750079) B1750079
theorem B1232873 : Blo 362758 1232873 := bstep (se 2 (by rfl) ⟨462327, by rfl⟩ : syracuseStep 1232873 = 924655) B924655
theorem B1233035 : Blo 362758 1233035 := bstep (se 1 (by rfl) ⟨924776, by rfl⟩ : syracuseStep 1233035 = 1849553) B1849553
theorem B544937 : Blo 362758 544937 := bstep (se 2 (by rfl) ⟨204351, by rfl⟩ : syracuseStep 544937 = 408703) B408703
theorem B545003 : Blo 362758 545003 := bstep (se 1 (by rfl) ⟨408752, by rfl⟩ : syracuseStep 545003 = 817505) B817505
theorem B47829953 : Blo 362758 47829953 := bstep (se 2 (by rfl) ⟨17936232, by rfl⟩ : syracuseStep 47829953 = 35872465) B35872465
theorem B546407 : Blo 362758 546407 := bstep (se 1 (by rfl) ⟨409805, by rfl⟩ : syracuseStep 546407 = 819611) B819611
theorem B3331793 : Blo 362758 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B5232761 : Blo 362758 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B547241 : Blo 362758 547241 := bstep (se 2 (by rfl) ⟨205215, by rfl⟩ : syracuseStep 547241 = 410431) B410431
theorem B7133629 : Blo 362758 7133629 := bstep (se 3 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 7133629 = 2675111) B2675111
theorem B3529271 : Blo 362758 3529271 := bstep (se 1 (by rfl) ⟨2646953, by rfl⟩ : syracuseStep 3529271 = 5293907) B5293907
theorem B776795 : Blo 362758 776795 := bstep (se 1 (by rfl) ⟨582596, by rfl⟩ : syracuseStep 776795 = 1165193) B1165193
theorem B13327031 : Blo 362758 13327031 := bstep (se 1 (by rfl) ⟨9995273, by rfl⟩ : syracuseStep 13327031 = 19990547) B19990547
theorem B547547 : Blo 362758 547547 := bstep (se 1 (by rfl) ⟨410660, by rfl⟩ : syracuseStep 547547 = 821321) B821321
theorem B547775 : Blo 362758 547775 := bstep (se 1 (by rfl) ⟨410831, by rfl⟩ : syracuseStep 547775 = 821663) B821663
theorem B20339693 : Blo 362758 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B1235951 : Blo 362758 1235951 := bstep (se 1 (by rfl) ⟨926963, by rfl⟩ : syracuseStep 1235951 = 1853927) B1853927
theorem B5266433 : Blo 362758 5266433 := bstep (se 2 (by rfl) ⟨1974912, by rfl⟩ : syracuseStep 5266433 = 3949825) B3949825
theorem B613615 : Blo 362758 613615 := bstep (se 1 (by rfl) ⟨460211, by rfl⟩ : syracuseStep 613615 = 920423) B920423
theorem B613723 : Blo 362758 613723 := bstep (se 1 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 613723 = 920585) B920585
theorem B2317871 : Blo 362758 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B548423 : Blo 362758 548423 := bstep (se 1 (by rfl) ⟨411317, by rfl⟩ : syracuseStep 548423 = 822635) B822635
theorem B548807 : Blo 362758 548807 := bstep (se 1 (by rfl) ⟨411605, by rfl⟩ : syracuseStep 548807 = 823211) B823211
theorem B1106075 : Blo 362758 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B1237463 : Blo 362758 1237463 := bstep (se 1 (by rfl) ⟨928097, by rfl⟩ : syracuseStep 1237463 = 1856195) B1856195
theorem B549359 : Blo 362758 549359 := bstep (se 1 (by rfl) ⟨412019, by rfl⟩ : syracuseStep 549359 = 824039) B824039
theorem B549467 : Blo 362758 549467 := bstep (se 1 (by rfl) ⟨412100, by rfl⟩ : syracuseStep 549467 = 824201) B824201
theorem B549755 : Blo 362758 549755 := bstep (se 1 (by rfl) ⟨412316, by rfl⟩ : syracuseStep 549755 = 824633) B824633
theorem B583033 : Blo 362758 583033 := bstep (se 2 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 583033 = 437275) B437275
theorem B1566337 : Blo 362758 1566337 := bstep (se 2 (by rfl) ⟨587376, by rfl⟩ : syracuseStep 1566337 = 1174753) B1174753
theorem B1174009 : Blo 362758 1174009 := bstep (se 2 (by rfl) ⟨440253, by rfl⟩ : syracuseStep 1174009 = 880507) B880507
theorem B617071 : Blo 362758 617071 := bstep (se 1 (by rfl) ⟨462803, by rfl⟩ : syracuseStep 617071 = 925607) B925607
theorem B617935 : Blo 362758 617935 := bstep (se 1 (by rfl) ⟨463451, by rfl⟩ : syracuseStep 617935 = 926903) B926903
theorem B1044191 : Blo 362758 1044191 := bstep (se 1 (by rfl) ⟨783143, by rfl⟩ : syracuseStep 1044191 = 1566287) B1566287
theorem B5042351 : Blo 362758 5042351 := bstep (se 1 (by rfl) ⟨3781763, by rfl⟩ : syracuseStep 5042351 = 7563527) B7563527
theorem B3109367 : Blo 362758 3109367 := bstep (se 1 (by rfl) ⟨2332025, by rfl⟩ : syracuseStep 3109367 = 4664051) B4664051
theorem B652063 : Blo 362758 652063 := bstep (se 1 (by rfl) ⟨489047, by rfl⟩ : syracuseStep 652063 = 978095) B978095
theorem B816713 : Blo 362758 816713 := bstep (se 2 (by rfl) ⟨306267, by rfl⟩ : syracuseStep 816713 = 612535) B612535
theorem B816767 : Blo 362758 816767 := bstep (se 1 (by rfl) ⟨612575, by rfl⟩ : syracuseStep 816767 = 1225151) B1225151
theorem B980819 : Blo 362758 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B4978979 : Blo 362758 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B1505603 : Blo 362758 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B818207 : Blo 362758 818207 := bstep (se 1 (by rfl) ⟨613655, by rfl⟩ : syracuseStep 818207 = 1227311) B1227311
theorem B3505193 : Blo 362758 3505193 := bstep (se 2 (by rfl) ⟨1314447, by rfl⟩ : syracuseStep 3505193 = 2628895) B2628895
theorem B818495 : Blo 362758 818495 := bstep (se 1 (by rfl) ⟨613871, by rfl⟩ : syracuseStep 818495 = 1227743) B1227743
theorem B1310555 : Blo 362758 1310555 := bstep (se 1 (by rfl) ⟨982916, by rfl⟩ : syracuseStep 1310555 = 1965833) B1965833
theorem B5341099 : Blo 362758 5341099 := bstep (se 1 (by rfl) ⟨4005824, by rfl⟩ : syracuseStep 5341099 = 8011649) B8011649
theorem B3112991 : Blo 362758 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B819323 : Blo 362758 819323 := bstep (se 1 (by rfl) ⟨614492, by rfl⟩ : syracuseStep 819323 = 1228985) B1228985
theorem B2949533 : Blo 362758 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B459199 : Blo 362758 459199 := bstep (se 1 (by rfl) ⟨344399, by rfl⟩ : syracuseStep 459199 = 688799) B688799
theorem B5244061 : Blo 362758 5244061 := bstep (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) B1966523
theorem B1311995 : Blo 362758 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B2950759 : Blo 362758 2950759 := bstep (se 1 (by rfl) ⟨2213069, by rfl⟩ : syracuseStep 2950759 = 4426139) B4426139
theorem B821915 : Blo 362758 821915 := bstep (se 1 (by rfl) ⟨616436, by rfl⟩ : syracuseStep 821915 = 1232873) B1232873
theorem B920231 : Blo 362758 920231 := bstep (se 1 (by rfl) ⟨690173, by rfl⟩ : syracuseStep 920231 = 1380347) B1380347
theorem B822023 : Blo 362758 822023 := bstep (se 1 (by rfl) ⟨616517, by rfl⟩ : syracuseStep 822023 = 1233035) B1233035
theorem B363291 : Blo 362758 363291 := bstep (se 1 (by rfl) ⟨272468, by rfl⟩ : syracuseStep 363291 = 544937) B544937
theorem B363335 : Blo 362758 363335 := bstep (se 1 (by rfl) ⟨272501, by rfl⟩ : syracuseStep 363335 = 545003) B545003
theorem B1838375 : Blo 362758 1838375 := bstep (se 1 (by rfl) ⟨1378781, by rfl⟩ : syracuseStep 1838375 = 2757563) B2757563
theorem B31886635 : Blo 362758 31886635 := bstep (se 1 (by rfl) ⟨23914976, by rfl⟩ : syracuseStep 31886635 = 47829953) B47829953
theorem B920879 : Blo 362758 920879 := bstep (se 1 (by rfl) ⟨690659, by rfl⟩ : syracuseStep 920879 = 1381319) B1381319
theorem B822761 : Blo 362758 822761 := bstep (se 2 (by rfl) ⟨308535, by rfl⟩ : syracuseStep 822761 = 617071) B617071
theorem B364271 : Blo 362758 364271 := bstep (se 1 (by rfl) ⟨273203, by rfl⟩ : syracuseStep 364271 = 546407) B546407
theorem B364827 : Blo 362758 364827 := bstep (se 1 (by rfl) ⟨273620, by rfl⟩ : syracuseStep 364827 = 547241) B547241
theorem B8884687 : Blo 362758 8884687 := bstep (se 1 (by rfl) ⟨6663515, by rfl⟩ : syracuseStep 8884687 = 13327031) B13327031
theorem B365031 : Blo 362758 365031 := bstep (se 1 (by rfl) ⟨273773, by rfl⟩ : syracuseStep 365031 = 547547) B547547
theorem B7016989 : Blo 362758 7016989 := bstep (se 3 (by rfl) ⟨1315685, by rfl⟩ : syracuseStep 7016989 = 2631371) B2631371
theorem B823913 : Blo 362758 823913 := bstep (se 2 (by rfl) ⟨308967, by rfl⟩ : syracuseStep 823913 = 617935) B617935
theorem B365183 : Blo 362758 365183 := bstep (se 1 (by rfl) ⟨273887, by rfl⟩ : syracuseStep 365183 = 547775) B547775
theorem B823967 : Blo 362758 823967 := bstep (se 1 (by rfl) ⟨617975, by rfl⟩ : syracuseStep 823967 = 1235951) B1235951
theorem B3510955 : Blo 362758 3510955 := bstep (se 1 (by rfl) ⟨2633216, by rfl⟩ : syracuseStep 3510955 = 5266433) B5266433
theorem B1545247 : Blo 362758 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B365615 : Blo 362758 365615 := bstep (se 1 (by rfl) ⟨274211, by rfl⟩ : syracuseStep 365615 = 548423) B548423
theorem B1053823 : Blo 362758 1053823 := bstep (se 1 (by rfl) ⟨790367, by rfl⟩ : syracuseStep 1053823 = 1580735) B1580735
theorem B365871 : Blo 362758 365871 := bstep (se 1 (by rfl) ⟨274403, by rfl⟩ : syracuseStep 365871 = 548807) B548807
theorem B824975 : Blo 362758 824975 := bstep (se 1 (by rfl) ⟨618731, by rfl⟩ : syracuseStep 824975 = 1237463) B1237463
theorem B366239 : Blo 362758 366239 := bstep (se 1 (by rfl) ⟨274679, by rfl⟩ : syracuseStep 366239 = 549359) B549359
theorem B366311 : Blo 362758 366311 := bstep (se 1 (by rfl) ⟨274733, by rfl⟩ : syracuseStep 366311 = 549467) B549467
theorem B366503 : Blo 362758 366503 := bstep (se 1 (by rfl) ⟨274877, by rfl⟩ : syracuseStep 366503 = 549755) B549755
theorem B2071453 : Blo 362758 2071453 := bstep (se 3 (by rfl) ⟨388397, by rfl⟩ : syracuseStep 2071453 = 776795) B776795
theorem B1383763 : Blo 362758 1383763 := bstep (se 1 (by rfl) ⟨1037822, by rfl⟩ : syracuseStep 1383763 = 2075645) B2075645
theorem B696127 : Blo 362758 696127 := bstep (se 1 (by rfl) ⟨522095, by rfl⟩ : syracuseStep 696127 = 1044191) B1044191
theorem B2072911 : Blo 362758 2072911 := bstep (se 1 (by rfl) ⟨1554683, by rfl⟩ : syracuseStep 2072911 = 3109367) B3109367
theorem B1843559 : Blo 362758 1843559 := bstep (se 1 (by rfl) ⟨1382669, by rfl⟩ : syracuseStep 1843559 = 2765339) B2765339
theorem B9511505 : Blo 362758 9511505 := bstep (se 2 (by rfl) ⟨3566814, by rfl⟩ : syracuseStep 9511505 = 7133629) B7133629
theorem B3319319 : Blo 362758 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B2336795 : Blo 362758 2336795 := bstep (se 1 (by rfl) ⟨1752596, by rfl⟩ : syracuseStep 2336795 = 3505193) B3505193
theorem B60827851 : Blo 362758 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B7121465 : Blo 362758 7121465 := bstep (se 2 (by rfl) ⟨2670549, by rfl⟩ : syracuseStep 7121465 = 5341099) B5341099
theorem B3124129 : Blo 362758 3124129 := bstep (se 2 (by rfl) ⟨1171548, by rfl⟩ : syracuseStep 3124129 = 2343097) B2343097
theorem B827370449 : Blo 362758 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B13446269 : Blo 362758 13446269 := bstep (se 3 (by rfl) ⟨2521175, by rfl⟩ : syracuseStep 13446269 = 5042351) B5042351
theorem B830831 : Blo 362758 830831 := bstep (se 1 (by rfl) ⟨623123, by rfl⟩ : syracuseStep 830831 = 1246247) B1246247
theorem B1847609 : Blo 362758 1847609 := bstep (se 2 (by rfl) ⟨692853, by rfl⟩ : syracuseStep 1847609 = 1385707) B1385707
theorem B1226231 : Blo 362758 1226231 := bstep (se 1 (by rfl) ⟨919673, by rfl⟩ : syracuseStep 1226231 = 1839347) B1839347
theorem B8238635 : Blo 362758 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B3488507 : Blo 362758 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B1555625 : Blo 362758 1555625 := bstep (se 2 (by rfl) ⟨583359, by rfl⟩ : syracuseStep 1555625 = 1166719) B1166719
theorem B869417 : Blo 362758 869417 := bstep (se 2 (by rfl) ⟨326031, by rfl⟩ : syracuseStep 869417 = 652063) B652063
theorem B1852793 : Blo 362758 1852793 := bstep (se 2 (by rfl) ⟨694797, by rfl⟩ : syracuseStep 1852793 = 1389595) B1389595
theorem B64603541 : Blo 362758 64603541 := bstep (se 6 (by rfl) ⟨1514145, by rfl⟩ : syracuseStep 64603541 = 3028291) B3028291
theorem B1231415 : Blo 362758 1231415 := bstep (se 1 (by rfl) ⟨923561, by rfl⟩ : syracuseStep 1231415 = 1847123) B1847123
theorem B1592345 : Blo 362758 1592345 := bstep (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) B1194259
theorem B1232009 : Blo 362758 1232009 := bstep (se 2 (by rfl) ⟨462003, by rfl⟩ : syracuseStep 1232009 = 924007) B924007
theorem B9948527 : Blo 362758 9948527 := bstep (se 1 (by rfl) ⟨7461395, by rfl⟩ : syracuseStep 9948527 = 14922791) B14922791
theorem B544475 : Blo 362758 544475 := bstep (se 1 (by rfl) ⟨408356, by rfl⟩ : syracuseStep 544475 = 816713) B816713
theorem B544511 : Blo 362758 544511 := bstep (se 1 (by rfl) ⟨408383, by rfl⟩ : syracuseStep 544511 = 816767) B816767
theorem B1003735 : Blo 362758 1003735 := bstep (se 1 (by rfl) ⟨752801, by rfl⟩ : syracuseStep 1003735 = 1505603) B1505603
theorem B1036775 : Blo 362758 1036775 := bstep (se 1 (by rfl) ⟨777581, by rfl⟩ : syracuseStep 1036775 = 1555163) B1555163
theorem B1757825 : Blo 362758 1757825 := bstep (se 2 (by rfl) ⟨659184, by rfl⟩ : syracuseStep 1757825 = 1318369) B1318369
theorem B545471 : Blo 362758 545471 := bstep (se 1 (by rfl) ⟨409103, by rfl⟩ : syracuseStep 545471 = 818207) B818207
theorem B545663 : Blo 362758 545663 := bstep (se 1 (by rfl) ⟨409247, by rfl⟩ : syracuseStep 545663 = 818495) B818495
theorem B873703 : Blo 362758 873703 := bstep (se 1 (by rfl) ⟨655277, by rfl⟩ : syracuseStep 873703 = 1310555) B1310555
theorem B5920073 : Blo 362758 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B546395 : Blo 362758 546395 := bstep (se 1 (by rfl) ⟨409796, by rfl⟩ : syracuseStep 546395 = 819593) B819593
theorem B612407 : Blo 362758 612407 := bstep (se 1 (by rfl) ⟨459305, by rfl⟩ : syracuseStep 612407 = 918611) B918611
theorem B547127 : Blo 362758 547127 := bstep (se 1 (by rfl) ⟨410345, by rfl⟩ : syracuseStep 547127 = 820691) B820691
theorem B547175 : Blo 362758 547175 := bstep (se 1 (by rfl) ⟨410381, by rfl⟩ : syracuseStep 547175 = 820763) B820763
theorem B12671477 : Blo 362758 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B10574387 : Blo 362758 10574387 := bstep (se 1 (by rfl) ⟨7930790, by rfl⟩ : syracuseStep 10574387 = 15861581) B15861581
theorem B2776031 : Blo 362758 2776031 := bstep (se 1 (by rfl) ⟨2082023, by rfl⟩ : syracuseStep 2776031 = 4164047) B4164047
theorem B547895 : Blo 362758 547895 := bstep (se 1 (by rfl) ⟨410921, by rfl⟩ : syracuseStep 547895 = 821843) B821843
theorem B4152383 : Blo 362758 4152383 := bstep (se 1 (by rfl) ⟨3114287, by rfl⟩ : syracuseStep 4152383 = 6228575) B6228575
theorem B777377 : Blo 362758 777377 := bstep (se 2 (by rfl) ⟨291516, by rfl⟩ : syracuseStep 777377 = 583033) B583033
theorem B4480343 : Blo 362758 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B1695131 : Blo 362758 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B2088449 : Blo 362758 2088449 := bstep (se 2 (by rfl) ⟨783168, by rfl⟩ : syracuseStep 2088449 = 1566337) B1566337
theorem B548393 : Blo 362758 548393 := bstep (se 2 (by rfl) ⟨205647, by rfl⟩ : syracuseStep 548393 = 411295) B411295
theorem B548399 : Blo 362758 548399 := bstep (se 1 (by rfl) ⟨411299, by rfl⟩ : syracuseStep 548399 = 822599) B822599
theorem B548843 : Blo 362758 548843 := bstep (se 1 (by rfl) ⟨411632, by rfl⟩ : syracuseStep 548843 = 823265) B823265
theorem B549047 : Blo 362758 549047 := bstep (se 1 (by rfl) ⟨411785, by rfl⟩ : syracuseStep 549047 = 823571) B823571
theorem B1663163 : Blo 362758 1663163 := bstep (se 1 (by rfl) ⟨1247372, by rfl⟩ : syracuseStep 1663163 = 2494745) B2494745
theorem B614891 : Blo 362758 614891 := bstep (se 1 (by rfl) ⟨461168, by rfl⟩ : syracuseStep 614891 = 922337) B922337
theorem B1565345 : Blo 362758 1565345 := bstep (se 2 (by rfl) ⟨587004, by rfl⟩ : syracuseStep 1565345 = 1174009) B1174009
theorem B1926281 : Blo 362758 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B2221195 : Blo 362758 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B615721 : Blo 362758 615721 := bstep (se 2 (by rfl) ⟨230895, by rfl⟩ : syracuseStep 615721 = 461791) B461791
theorem B24045245 : Blo 362758 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B2352847 : Blo 362758 2352847 := bstep (se 1 (by rfl) ⟨1764635, by rfl⟩ : syracuseStep 2352847 = 3529271) B3529271
theorem B2254715 : Blo 362758 2254715 := bstep (se 1 (by rfl) ⟨1691036, by rfl⟩ : syracuseStep 2254715 = 3382073) B3382073
theorem B13559795 : Blo 362758 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B7042139 : Blo 362758 7042139 := bstep (se 1 (by rfl) ⟨5281604, by rfl⟩ : syracuseStep 7042139 = 10563209) B10563209
theorem B817019 : Blo 362758 817019 := bstep (se 1 (by rfl) ⟨612764, by rfl⟩ : syracuseStep 817019 = 1225529) B1225529
theorem B653879 : Blo 362758 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B818153 : Blo 362758 818153 := bstep (se 2 (by rfl) ⟨306807, by rfl⟩ : syracuseStep 818153 = 613615) B613615
theorem B818297 : Blo 362758 818297 := bstep (se 2 (by rfl) ⟨306861, by rfl⟩ : syracuseStep 818297 = 613723) B613723
theorem B3506003 : Blo 362758 3506003 := bstep (se 1 (by rfl) ⟨2629502, by rfl⟩ : syracuseStep 3506003 = 5259005) B5259005
theorem B819035 : Blo 362758 819035 := bstep (se 1 (by rfl) ⟨614276, by rfl⟩ : syracuseStep 819035 = 1228553) B1228553
theorem B1966355 : Blo 362758 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B820943 : Blo 362758 820943 := bstep (se 1 (by rfl) ⟨615707, by rfl⟩ : syracuseStep 820943 = 1231415) B1231415
theorem B820961 : Blo 362758 820961 := bstep (se 2 (by rfl) ⟨307860, by rfl⟩ : syracuseStep 820961 = 615721) B615721
theorem B821339 : Blo 362758 821339 := bstep (se 1 (by rfl) ⟨616004, by rfl⟩ : syracuseStep 821339 = 1232009) B1232009
theorem B3934345 : Blo 362758 3934345 := bstep (se 2 (by rfl) ⟨1475379, by rfl⟩ : syracuseStep 3934345 = 2950759) B2950759
theorem B362983 : Blo 362758 362983 := bstep (se 1 (by rfl) ⟨272237, by rfl⟩ : syracuseStep 362983 = 544475) B544475
theorem B363007 : Blo 362758 363007 := bstep (se 1 (by rfl) ⟨272255, by rfl⟩ : syracuseStep 363007 = 544511) B544511
theorem B81103801 : Blo 362758 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B691183 : Blo 362758 691183 := bstep (se 1 (by rfl) ⟨518387, by rfl⟩ : syracuseStep 691183 = 1036775) B1036775
theorem B363647 : Blo 362758 363647 := bstep (se 1 (by rfl) ⟨272735, by rfl⟩ : syracuseStep 363647 = 545471) B545471
theorem B363775 : Blo 362758 363775 := bstep (se 1 (by rfl) ⟨272831, by rfl⟩ : syracuseStep 363775 = 545663) B545663
theorem B364263 : Blo 362758 364263 := bstep (se 1 (by rfl) ⟨273197, by rfl⟩ : syracuseStep 364263 = 546395) B546395
theorem B4165505 : Blo 362758 4165505 := bstep (se 2 (by rfl) ⟨1562064, by rfl⟩ : syracuseStep 4165505 = 3124129) B3124129
theorem B364751 : Blo 362758 364751 := bstep (se 1 (by rfl) ⟨273563, by rfl⟩ : syracuseStep 364751 = 547127) B547127
theorem B364783 : Blo 362758 364783 := bstep (se 1 (by rfl) ⟨273587, by rfl⟩ : syracuseStep 364783 = 547175) B547175
theorem B7049591 : Blo 362758 7049591 := bstep (se 1 (by rfl) ⟨5287193, by rfl⟩ : syracuseStep 7049591 = 10574387) B10574387
theorem B365263 : Blo 362758 365263 := bstep (se 1 (by rfl) ⟨273947, by rfl⟩ : syracuseStep 365263 = 547895) B547895
theorem B2986895 : Blo 362758 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B365595 : Blo 362758 365595 := bstep (se 1 (by rfl) ⟨274196, by rfl⟩ : syracuseStep 365595 = 548393) B548393
theorem B365599 : Blo 362758 365599 := bstep (se 1 (by rfl) ⟨274199, by rfl⟩ : syracuseStep 365599 = 548399) B548399
theorem B365895 : Blo 362758 365895 := bstep (se 1 (by rfl) ⟨274421, by rfl⟩ : syracuseStep 365895 = 548843) B548843
theorem B366031 : Blo 362758 366031 := bstep (se 1 (by rfl) ⟨274523, by rfl⟩ : syracuseStep 366031 = 549047) B549047
theorem B1284187 : Blo 362758 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B16030163 : Blo 362758 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B1743677 : Blo 362758 1743677 := bstep (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) B653879
theorem B4694759 : Blo 362758 4694759 := bstep (se 1 (by rfl) ⟨3521069, by rfl⟩ : syracuseStep 4694759 = 7042139) B7042139
theorem B2761937 : Blo 362758 2761937 := bstep (se 2 (by rfl) ⟨1035726, by rfl⟩ : syracuseStep 2761937 = 2071453) B2071453
theorem B1845017 : Blo 362758 1845017 := bstep (se 2 (by rfl) ⟨691881, by rfl⟩ : syracuseStep 1845017 = 1383763) B1383763
theorem B928169 : Blo 362758 928169 := bstep (se 2 (by rfl) ⟨348063, by rfl⟩ : syracuseStep 928169 = 696127) B696127
theorem B2337335 : Blo 362758 2337335 := bstep (se 1 (by rfl) ⟨1753001, by rfl⟩ : syracuseStep 2337335 = 3506003) B3506003
theorem B2075327 : Blo 362758 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B2763881 : Blo 362758 2763881 := bstep (se 2 (by rfl) ⟨1036455, by rfl⟩ : syracuseStep 2763881 = 2072911) B2072911
theorem B43069027 : Blo 362758 43069027 := bstep (se 1 (by rfl) ⟨32301770, by rfl⟩ : syracuseStep 43069027 = 64603541) B64603541
theorem B5353253 : Blo 362758 5353253 := bstep (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) B1003735
theorem B2961593 : Blo 362758 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B6992081 : Blo 362758 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B4174253 : Blo 362758 4174253 := bstep (se 3 (by rfl) ⟨782672, by rfl⟩ : syracuseStep 4174253 = 1565345) B1565345
theorem B1225583 : Blo 362758 1225583 := bstep (se 1 (by rfl) ⟨919187, by rfl⟩ : syracuseStep 1225583 = 1838375) B1838375
theorem B6632351 : Blo 362758 6632351 := bstep (se 1 (by rfl) ⟨4974263, by rfl⟩ : syracuseStep 6632351 = 9948527) B9948527
theorem B3946715 : Blo 362758 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B408271 : Blo 362758 408271 := bstep (se 1 (by rfl) ⟨306203, by rfl⟩ : syracuseStep 408271 = 612407) B612407
theorem B42515513 : Blo 362758 42515513 := bstep (se 2 (by rfl) ⟨15943317, by rfl⟩ : syracuseStep 42515513 = 31886635) B31886635
theorem B1850687 : Blo 362758 1850687 := bstep (se 1 (by rfl) ⟨1388015, by rfl⟩ : syracuseStep 1850687 = 2776031) B2776031
theorem B2768255 : Blo 362758 2768255 := bstep (se 1 (by rfl) ⟨2076191, by rfl⟩ : syracuseStep 2768255 = 4152383) B4152383
theorem B1130087 : Blo 362758 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B1392299 : Blo 362758 1392299 := bstep (se 1 (by rfl) ⟨1044224, by rfl⟩ : syracuseStep 1392299 = 2088449) B2088449
theorem B1229039 : Blo 362758 1229039 := bstep (se 1 (by rfl) ⟨921779, by rfl⟩ : syracuseStep 1229039 = 1843559) B1843559
theorem B409927 : Blo 362758 409927 := bstep (se 1 (by rfl) ⟨307445, by rfl⟩ : syracuseStep 409927 = 614891) B614891
theorem B6341003 : Blo 362758 6341003 := bstep (se 1 (by rfl) ⟨4755752, by rfl⟩ : syracuseStep 6341003 = 9511505) B9511505
theorem B11846249 : Blo 362758 11846249 := bstep (se 2 (by rfl) ⟨4442343, by rfl⟩ : syracuseStep 11846249 = 8884687) B8884687
theorem B9355985 : Blo 362758 9355985 := bstep (se 2 (by rfl) ⟨3508494, by rfl⟩ : syracuseStep 9355985 = 7016989) B7016989
theorem B2212879 : Blo 362758 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B1557863 : Blo 362758 1557863 := bstep (se 1 (by rfl) ⟨1168397, by rfl⟩ : syracuseStep 1557863 = 2336795) B2336795
theorem B1164937 : Blo 362758 1164937 := bstep (se 2 (by rfl) ⟨436851, by rfl⟩ : syracuseStep 1164937 = 873703) B873703
theorem B8964179 : Blo 362758 8964179 := bstep (se 1 (by rfl) ⟨6723134, by rfl⟩ : syracuseStep 8964179 = 13446269) B13446269
theorem B4246253 : Blo 362758 4246253 := bstep (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) B1592345
theorem B1231739 : Blo 362758 1231739 := bstep (se 1 (by rfl) ⟨923804, by rfl⟩ : syracuseStep 1231739 = 1847609) B1847609
theorem B2215549 : Blo 362758 2215549 := bstep (se 3 (by rfl) ⟨415415, by rfl⟩ : syracuseStep 2215549 = 830831) B830831
theorem B5492423 : Blo 362758 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B544679 : Blo 362758 544679 := bstep (se 1 (by rfl) ⟨408509, by rfl⟩ : syracuseStep 544679 = 817019) B817019
theorem B545435 : Blo 362758 545435 := bstep (se 1 (by rfl) ⟨409076, by rfl⟩ : syracuseStep 545435 = 818153) B818153
theorem B545531 : Blo 362758 545531 := bstep (se 1 (by rfl) ⟨409148, by rfl⟩ : syracuseStep 545531 = 818297) B818297
theorem B1037083 : Blo 362758 1037083 := bstep (se 1 (by rfl) ⟨777812, by rfl⟩ : syracuseStep 1037083 = 1555625) B1555625
theorem B546023 : Blo 362758 546023 := bstep (se 1 (by rfl) ⟨409517, by rfl⟩ : syracuseStep 546023 = 819035) B819035
theorem B546215 : Blo 362758 546215 := bstep (se 1 (by rfl) ⟨409661, by rfl⟩ : syracuseStep 546215 = 819323) B819323
theorem B612265 : Blo 362758 612265 := bstep (se 2 (by rfl) ⟨229599, by rfl⟩ : syracuseStep 612265 = 459199) B459199
theorem B579611 : Blo 362758 579611 := bstep (se 1 (by rfl) ⟨434708, by rfl⟩ : syracuseStep 579611 = 869417) B869417
theorem B1235195 : Blo 362758 1235195 := bstep (se 1 (by rfl) ⟨926396, by rfl⟩ : syracuseStep 1235195 = 1852793) B1852793
theorem B547943 : Blo 362758 547943 := bstep (se 1 (by rfl) ⟨410957, by rfl⟩ : syracuseStep 547943 = 821915) B821915
theorem B613487 : Blo 362758 613487 := bstep (se 1 (by rfl) ⟨460115, by rfl⟩ : syracuseStep 613487 = 920231) B920231
theorem B548015 : Blo 362758 548015 := bstep (se 1 (by rfl) ⟨411011, by rfl⟩ : syracuseStep 548015 = 822023) B822023
theorem B613919 : Blo 362758 613919 := bstep (se 1 (by rfl) ⟨460439, by rfl⟩ : syracuseStep 613919 = 920879) B920879
theorem B3137129 : Blo 362758 3137129 := bstep (se 2 (by rfl) ⟨1176423, by rfl⟩ : syracuseStep 3137129 = 2352847) B2352847
theorem B548507 : Blo 362758 548507 := bstep (se 1 (by rfl) ⟨411380, by rfl⟩ : syracuseStep 548507 = 822761) B822761
theorem B549275 : Blo 362758 549275 := bstep (se 1 (by rfl) ⟨411956, by rfl⟩ : syracuseStep 549275 = 823913) B823913
theorem B1171883 : Blo 362758 1171883 := bstep (se 1 (by rfl) ⟨878912, by rfl⟩ : syracuseStep 1171883 = 1757825) B1757825
theorem B549311 : Blo 362758 549311 := bstep (se 1 (by rfl) ⟨411983, by rfl⟩ : syracuseStep 549311 = 823967) B823967
theorem B3498653 : Blo 362758 3498653 := bstep (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) B1311995
theorem B549983 : Blo 362758 549983 := bstep (se 1 (by rfl) ⟨412487, by rfl⟩ : syracuseStep 549983 = 824975) B824975
theorem B8447651 : Blo 362758 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B518251 : Blo 362758 518251 := bstep (se 1 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 518251 = 777377) B777377
theorem B1108775 : Blo 362758 1108775 := bstep (se 1 (by rfl) ⟨831581, by rfl⟩ : syracuseStep 1108775 = 1663163) B1663163
theorem B4681273 : Blo 362758 4681273 := bstep (se 2 (by rfl) ⟨1755477, by rfl⟩ : syracuseStep 4681273 = 3510955) B3510955
theorem B1503143 : Blo 362758 1503143 := bstep (se 1 (by rfl) ⟨1127357, by rfl⟩ : syracuseStep 1503143 = 2254715) B2254715
theorem B9039863 : Blo 362758 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B2060329 : Blo 362758 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B1405097 : Blo 362758 1405097 := bstep (se 2 (by rfl) ⟨526911, by rfl⟩ : syracuseStep 1405097 = 1053823) B1053823
theorem B4747643 : Blo 362758 4747643 := bstep (se 1 (by rfl) ⟨3560732, by rfl⟩ : syracuseStep 4747643 = 7121465) B7121465
theorem B551580299 : Blo 362758 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B817487 : Blo 362758 817487 := bstep (se 1 (by rfl) ⟨613115, by rfl⟩ : syracuseStep 817487 = 1226231) B1226231
theorem B2325671 : Blo 362758 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B819359 : Blo 362758 819359 := bstep (se 1 (by rfl) ⟨614519, by rfl⟩ : syracuseStep 819359 = 1229039) B1229039
theorem B1310903 : Blo 362758 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B4227335 : Blo 362758 4227335 := bstep (se 1 (by rfl) ⟨3170501, by rfl⟩ : syracuseStep 4227335 = 6341003) B6341003
theorem B7897499 : Blo 362758 7897499 := bstep (se 1 (by rfl) ⟨5923124, by rfl⟩ : syracuseStep 7897499 = 11846249) B11846249
theorem B2950505 : Blo 362758 2950505 := bstep (se 2 (by rfl) ⟨1106439, by rfl⟩ : syracuseStep 2950505 = 2212879) B2212879
theorem B821159 : Blo 362758 821159 := bstep (se 1 (by rfl) ⟨615869, by rfl⟩ : syracuseStep 821159 = 1231739) B1231739
theorem B7965053 : Blo 362758 7965053 := bstep (se 3 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 7965053 = 2986895) B2986895
theorem B363119 : Blo 362758 363119 := bstep (se 1 (by rfl) ⟨272339, by rfl⟩ : syracuseStep 363119 = 544679) B544679
theorem B691001 : Blo 362758 691001 := bstep (se 2 (by rfl) ⟨259125, by rfl⟩ : syracuseStep 691001 = 518251) B518251
theorem B5245793 : Blo 362758 5245793 := bstep (se 2 (by rfl) ⟨1967172, by rfl⟩ : syracuseStep 5245793 = 3934345) B3934345
theorem B363623 : Blo 362758 363623 := bstep (se 1 (by rfl) ⟨272717, by rfl⟩ : syracuseStep 363623 = 545435) B545435
theorem B363687 : Blo 362758 363687 := bstep (se 1 (by rfl) ⟨272765, by rfl⟩ : syracuseStep 363687 = 545531) B545531
theorem B364015 : Blo 362758 364015 := bstep (se 1 (by rfl) ⟨273011, by rfl⟩ : syracuseStep 364015 = 546023) B546023
theorem B364143 : Blo 362758 364143 := bstep (se 1 (by rfl) ⟨273107, by rfl⟩ : syracuseStep 364143 = 546215) B546215
theorem B108138401 : Blo 362758 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B921577 : Blo 362758 921577 := bstep (se 2 (by rfl) ⟨345591, by rfl⟩ : syracuseStep 921577 = 691183) B691183
theorem B823463 : Blo 362758 823463 := bstep (se 1 (by rfl) ⟨617597, by rfl⟩ : syracuseStep 823463 = 1235195) B1235195
theorem B365295 : Blo 362758 365295 := bstep (se 1 (by rfl) ⟨273971, by rfl⟩ : syracuseStep 365295 = 547943) B547943
theorem B365343 : Blo 362758 365343 := bstep (se 1 (by rfl) ⟨274007, by rfl⟩ : syracuseStep 365343 = 548015) B548015
theorem B2954065 : Blo 362758 2954065 := bstep (se 2 (by rfl) ⟨1107774, by rfl⟩ : syracuseStep 2954065 = 2215549) B2215549
theorem B365671 : Blo 362758 365671 := bstep (se 1 (by rfl) ⟨274253, by rfl⟩ : syracuseStep 365671 = 548507) B548507
theorem B366183 : Blo 362758 366183 := bstep (se 1 (by rfl) ⟨274637, by rfl⟩ : syracuseStep 366183 = 549275) B549275
theorem B366207 : Blo 362758 366207 := bstep (se 1 (by rfl) ⟨274655, by rfl⟩ : syracuseStep 366207 = 549311) B549311
theorem B366655 : Blo 362758 366655 := bstep (se 1 (by rfl) ⟨274991, by rfl⟩ : syracuseStep 366655 = 549983) B549983
theorem B1841291 : Blo 362758 1841291 := bstep (se 1 (by rfl) ⟨1380968, by rfl⟩ : syracuseStep 1841291 = 2761937) B2761937
theorem B1382777 : Blo 362758 1382777 := bstep (se 2 (by rfl) ⟨518541, by rfl⟩ : syracuseStep 1382777 = 1037083) B1037083
theorem B1383551 : Blo 362758 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B1842587 : Blo 362758 1842587 := bstep (se 1 (by rfl) ⟨1381940, by rfl⟩ : syracuseStep 1842587 = 2763881) B2763881
theorem B2956733 : Blo 362758 2956733 := bstep (se 3 (by rfl) ⟨554387, by rfl⟩ : syracuseStep 2956733 = 1108775) B1108775
theorem B1712249 : Blo 362758 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B1974395 : Blo 362758 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B4661387 : Blo 362758 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B2631143 : Blo 362758 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B1550447 : Blo 362758 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B1845503 : Blo 362758 1845503 := bstep (se 1 (by rfl) ⟨1384127, by rfl⟩ : syracuseStep 1845503 = 2768255) B2768255
theorem B928199 : Blo 362758 928199 := bstep (se 1 (by rfl) ⟨696149, by rfl⟩ : syracuseStep 928199 = 1392299) B1392299
theorem B6237323 : Blo 362758 6237323 := bstep (se 1 (by rfl) ⟨4677992, by rfl⟩ : syracuseStep 6237323 = 9355985) B9355985
theorem B5976119 : Blo 362758 5976119 := bstep (se 1 (by rfl) ⟨4482089, by rfl⟩ : syracuseStep 5976119 = 8964179) B8964179
theorem B2830835 : Blo 362758 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B1553249 : Blo 362758 1553249 := bstep (se 2 (by rfl) ⟨582468, by rfl⟩ : syracuseStep 1553249 = 1164937) B1164937
theorem B4699727 : Blo 362758 4699727 := bstep (se 1 (by rfl) ⟨3524795, by rfl⟩ : syracuseStep 4699727 = 7049591) B7049591
theorem B1162451 : Blo 362758 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B408991 : Blo 362758 408991 := bstep (se 1 (by rfl) ⟨306743, by rfl⟩ : syracuseStep 408991 = 613487) B613487
theorem B6241697 : Blo 362758 6241697 := bstep (se 2 (by rfl) ⟨2340636, by rfl⟩ : syracuseStep 6241697 = 4681273) B4681273
theorem B57425369 : Blo 362758 57425369 := bstep (se 2 (by rfl) ⟨21534513, by rfl⟩ : syracuseStep 57425369 = 43069027) B43069027
theorem B409279 : Blo 362758 409279 := bstep (se 1 (by rfl) ⟨306959, by rfl⟩ : syracuseStep 409279 = 613919) B613919
theorem B3129839 : Blo 362758 3129839 := bstep (se 1 (by rfl) ⟨2347379, by rfl⟩ : syracuseStep 3129839 = 4694759) B4694759
theorem B1230011 : Blo 362758 1230011 := bstep (se 1 (by rfl) ⟨922508, by rfl⟩ : syracuseStep 1230011 = 1845017) B1845017
theorem B42747101 : Blo 362758 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B1558223 : Blo 362758 1558223 := bstep (se 1 (by rfl) ⟨1168667, by rfl⟩ : syracuseStep 1558223 = 2337335) B2337335
theorem B1002095 : Blo 362758 1002095 := bstep (se 1 (by rfl) ⟨751571, by rfl⟩ : syracuseStep 1002095 = 1503143) B1503143
theorem B936731 : Blo 362758 936731 := bstep (se 1 (by rfl) ⟨702548, by rfl⟩ : syracuseStep 936731 = 1405097) B1405097
theorem B3165095 : Blo 362758 3165095 := bstep (se 1 (by rfl) ⟨2373821, by rfl⟩ : syracuseStep 3165095 = 4747643) B4747643
theorem B544361 : Blo 362758 544361 := bstep (se 2 (by rfl) ⟨204135, by rfl⟩ : syracuseStep 544361 = 408271) B408271
theorem B544991 : Blo 362758 544991 := bstep (se 1 (by rfl) ⟨408743, by rfl⟩ : syracuseStep 544991 = 817487) B817487
theorem B1233791 : Blo 362758 1233791 := bstep (se 1 (by rfl) ⟨925343, by rfl⟩ : syracuseStep 1233791 = 1850687) B1850687
theorem B546569 : Blo 362758 546569 := bstep (se 2 (by rfl) ⟨204963, by rfl⟩ : syracuseStep 546569 = 409927) B409927
theorem B1038575 : Blo 362758 1038575 := bstep (se 1 (by rfl) ⟨778931, by rfl⟩ : syracuseStep 1038575 = 1557863) B1557863
theorem B547295 : Blo 362758 547295 := bstep (se 1 (by rfl) ⟨410471, by rfl⟩ : syracuseStep 547295 = 820943) B820943
theorem B547307 : Blo 362758 547307 := bstep (se 1 (by rfl) ⟨410480, by rfl⟩ : syracuseStep 547307 = 820961) B820961
theorem B547559 : Blo 362758 547559 := bstep (se 1 (by rfl) ⟨410669, by rfl⟩ : syracuseStep 547559 = 821339) B821339
theorem B9329741 : Blo 362758 9329741 := bstep (se 3 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 9329741 = 3498653) B3498653
theorem B3661615 : Blo 362758 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B2777003 : Blo 362758 2777003 := bstep (se 1 (by rfl) ⟨2082752, by rfl⟩ : syracuseStep 2777003 = 4165505) B4165505
theorem B386407 : Blo 362758 386407 := bstep (se 1 (by rfl) ⟨289805, by rfl⟩ : syracuseStep 386407 = 579611) B579611
theorem B2091419 : Blo 362758 2091419 := bstep (se 1 (by rfl) ⟨1568564, by rfl⟩ : syracuseStep 2091419 = 3137129) B3137129
theorem B2747105 : Blo 362758 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B781255 : Blo 362758 781255 := bstep (se 1 (by rfl) ⟨585941, by rfl⟩ : syracuseStep 781255 = 1171883) B1171883
theorem B5631767 : Blo 362758 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B618779 : Blo 362758 618779 := bstep (se 1 (by rfl) ⟨464084, by rfl⟩ : syracuseStep 618779 = 928169) B928169
theorem B3568835 : Blo 362758 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B816353 : Blo 362758 816353 := bstep (se 2 (by rfl) ⟨306132, by rfl⟩ : syracuseStep 816353 = 612265) B612265
theorem B6026575 : Blo 362758 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B2782835 : Blo 362758 2782835 := bstep (se 1 (by rfl) ⟨2087126, by rfl⟩ : syracuseStep 2782835 = 4174253) B4174253
theorem B367720199 : Blo 362758 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B817055 : Blo 362758 817055 := bstep (se 1 (by rfl) ⟨612791, by rfl⟩ : syracuseStep 817055 = 1225583) B1225583
theorem B4421567 : Blo 362758 4421567 := bstep (se 1 (by rfl) ⟨3316175, by rfl⟩ : syracuseStep 4421567 = 6632351) B6632351
theorem B28343675 : Blo 362758 28343675 := bstep (se 1 (by rfl) ⟨21257756, by rfl⟩ : syracuseStep 28343675 = 42515513) B42515513
theorem B753391 : Blo 362758 753391 := bstep (se 1 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 753391 = 1130087) B1130087
theorem B2818223 : Blo 362758 2818223 := bstep (se 1 (by rfl) ⟨2113667, by rfl⟩ : syracuseStep 2818223 = 4227335) B4227335
theorem B820007 : Blo 362758 820007 := bstep (se 1 (by rfl) ⟨615005, by rfl⟩ : syracuseStep 820007 = 1230011) B1230011
theorem B1967003 : Blo 362758 1967003 := bstep (se 1 (by rfl) ⟨1475252, by rfl⟩ : syracuseStep 1967003 = 2950505) B2950505
theorem B5310035 : Blo 362758 5310035 := bstep (se 1 (by rfl) ⟨3982526, by rfl⟩ : syracuseStep 5310035 = 7965053) B7965053
theorem B460667 : Blo 362758 460667 := bstep (se 1 (by rfl) ⟨345500, by rfl⟩ : syracuseStep 460667 = 691001) B691001
theorem B362907 : Blo 362758 362907 := bstep (se 1 (by rfl) ⟨272180, by rfl⟩ : syracuseStep 362907 = 544361) B544361
theorem B72092267 : Blo 362758 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B363327 : Blo 362758 363327 := bstep (se 1 (by rfl) ⟨272495, by rfl⟩ : syracuseStep 363327 = 544991) B544991
theorem B822527 : Blo 362758 822527 := bstep (se 1 (by rfl) ⟨616895, by rfl⟩ : syracuseStep 822527 = 1233791) B1233791
theorem B364379 : Blo 362758 364379 := bstep (se 1 (by rfl) ⟨273284, by rfl⟩ : syracuseStep 364379 = 546569) B546569
theorem B692383 : Blo 362758 692383 := bstep (se 1 (by rfl) ⟨519287, by rfl⟩ : syracuseStep 692383 = 1038575) B1038575
theorem B921851 : Blo 362758 921851 := bstep (se 1 (by rfl) ⟨691388, by rfl⟩ : syracuseStep 921851 = 1382777) B1382777
theorem B364863 : Blo 362758 364863 := bstep (se 1 (by rfl) ⟨273647, by rfl⟩ : syracuseStep 364863 = 547295) B547295
theorem B364871 : Blo 362758 364871 := bstep (se 1 (by rfl) ⟨273653, by rfl⟩ : syracuseStep 364871 = 547307) B547307
theorem B365039 : Blo 362758 365039 := bstep (se 1 (by rfl) ⟨273779, by rfl⟩ : syracuseStep 365039 = 547559) B547559
theorem B922367 : Blo 362758 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B1971155 : Blo 362758 1971155 := bstep (se 1 (by rfl) ⟨1478366, by rfl⟩ : syracuseStep 1971155 = 2956733) B2956733
theorem B1316263 : Blo 362758 1316263 := bstep (se 1 (by rfl) ⟨987197, by rfl⟩ : syracuseStep 1316263 = 1974395) B1974395
theorem B3938753 : Blo 362758 3938753 := bstep (se 2 (by rfl) ⟨1477032, by rfl⟩ : syracuseStep 3938753 = 2954065) B2954065
theorem B8035433 : Blo 362758 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B2497949 : Blo 362758 2497949 := bstep (se 3 (by rfl) ⟨468365, by rfl⟩ : syracuseStep 2497949 = 936731) B936731
theorem B245146799 : Blo 362758 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B153134317 : Blo 362758 153134317 := bstep (se 3 (by rfl) ⟨28712684, by rfl⟩ : syracuseStep 153134317 = 57425369) B57425369
theorem B7548893 : Blo 362758 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B668063 : Blo 362758 668063 := bstep (se 1 (by rfl) ⟨501047, by rfl⟩ : syracuseStep 668063 = 1002095) B1002095
theorem B2110063 : Blo 362758 2110063 := bstep (se 1 (by rfl) ⟨1582547, by rfl⟩ : syracuseStep 2110063 = 3165095) B3165095
theorem B1227527 : Blo 362758 1227527 := bstep (se 1 (by rfl) ⟨920645, by rfl⟩ : syracuseStep 1227527 = 1841291) B1841291
theorem B1228391 : Blo 362758 1228391 := bstep (se 1 (by rfl) ⟨921293, by rfl⟩ : syracuseStep 1228391 = 1842587) B1842587
theorem B1851335 : Blo 362758 1851335 := bstep (se 1 (by rfl) ⟨1388501, by rfl⟩ : syracuseStep 1851335 = 2777003) B2777003
theorem B1228769 : Blo 362758 1228769 := bstep (se 2 (by rfl) ⟨460788, by rfl⟩ : syracuseStep 1228769 = 921577) B921577
theorem B1754095 : Blo 362758 1754095 := bstep (se 1 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 1754095 = 2631143) B2631143
theorem B1033631 : Blo 362758 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B1230335 : Blo 362758 1230335 := bstep (se 1 (by rfl) ⟨922751, by rfl⟩ : syracuseStep 1230335 = 1845503) B1845503
theorem B1394279 : Blo 362758 1394279 := bstep (se 1 (by rfl) ⟨1045709, by rfl⟩ : syracuseStep 1394279 = 2091419) B2091419
theorem B3754511 : Blo 362758 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B3984079 : Blo 362758 3984079 := bstep (se 1 (by rfl) ⟨2988059, by rfl⟩ : syracuseStep 3984079 = 5976119) B5976119
theorem B412519 : Blo 362758 412519 := bstep (se 1 (by rfl) ⟨309389, by rfl⟩ : syracuseStep 412519 = 618779) B618779
theorem B3099869 : Blo 362758 3099869 := bstep (se 3 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 3099869 = 1162451) B1162451
theorem B1035499 : Blo 362758 1035499 := bstep (se 1 (by rfl) ⟨776624, by rfl⟩ : syracuseStep 1035499 = 1553249) B1553249
theorem B2379223 : Blo 362758 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B544235 : Blo 362758 544235 := bstep (se 1 (by rfl) ⟨408176, by rfl⟩ : syracuseStep 544235 = 816353) B816353
theorem B3133151 : Blo 362758 3133151 := bstep (se 1 (by rfl) ⟨2349863, by rfl⟩ : syracuseStep 3133151 = 4699727) B4699727
theorem B1855223 : Blo 362758 1855223 := bstep (se 1 (by rfl) ⟨1391417, by rfl⟩ : syracuseStep 1855223 = 2782835) B2782835
theorem B544703 : Blo 362758 544703 := bstep (se 1 (by rfl) ⟨408527, by rfl⟩ : syracuseStep 544703 = 817055) B817055
theorem B545321 : Blo 362758 545321 := bstep (se 2 (by rfl) ⟨204495, by rfl⟩ : syracuseStep 545321 = 408991) B408991
theorem B18895783 : Blo 362758 18895783 := bstep (se 1 (by rfl) ⟨14171837, by rfl⟩ : syracuseStep 18895783 = 28343675) B28343675
theorem B545705 : Blo 362758 545705 := bstep (se 2 (by rfl) ⟨204639, by rfl⟩ : syracuseStep 545705 = 409279) B409279
theorem B1004521 : Blo 362758 1004521 := bstep (se 2 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 1004521 = 753391) B753391
theorem B546239 : Blo 362758 546239 := bstep (se 1 (by rfl) ⟨409679, by rfl⟩ : syracuseStep 546239 = 819359) B819359
theorem B873935 : Blo 362758 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B5264999 : Blo 362758 5264999 := bstep (se 1 (by rfl) ⟨3948749, by rfl⟩ : syracuseStep 5264999 = 7897499) B7897499
theorem B2086559 : Blo 362758 2086559 := bstep (se 1 (by rfl) ⟨1564919, by rfl⟩ : syracuseStep 2086559 = 3129839) B3129839
theorem B28498067 : Blo 362758 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B1038815 : Blo 362758 1038815 := bstep (se 1 (by rfl) ⟨779111, by rfl⟩ : syracuseStep 1038815 = 1558223) B1558223
theorem B547439 : Blo 362758 547439 := bstep (se 1 (by rfl) ⟨410579, by rfl⟩ : syracuseStep 547439 = 821159) B821159
theorem B515209 : Blo 362758 515209 := bstep (se 2 (by rfl) ⟨193203, by rfl⟩ : syracuseStep 515209 = 386407) B386407
theorem B3497195 : Blo 362758 3497195 := bstep (se 1 (by rfl) ⟨2622896, by rfl⟩ : syracuseStep 3497195 = 5245793) B5245793
theorem B548975 : Blo 362758 548975 := bstep (se 1 (by rfl) ⟨411731, by rfl⟩ : syracuseStep 548975 = 823463) B823463
theorem B1041673 : Blo 362758 1041673 := bstep (se 2 (by rfl) ⟨390627, by rfl⟩ : syracuseStep 1041673 = 781255) B781255
theorem B6219827 : Blo 362758 6219827 := bstep (se 1 (by rfl) ⟨4664870, by rfl⟩ : syracuseStep 6219827 = 9329741) B9329741
theorem B1141499 : Blo 362758 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B3107591 : Blo 362758 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B618799 : Blo 362758 618799 := bstep (se 1 (by rfl) ⟨464099, by rfl⟩ : syracuseStep 618799 = 928199) B928199
theorem B1831403 : Blo 362758 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B4158215 : Blo 362758 4158215 := bstep (se 1 (by rfl) ⟨3118661, by rfl⟩ : syracuseStep 4158215 = 6237323) B6237323
theorem B2947711 : Blo 362758 2947711 := bstep (se 1 (by rfl) ⟨2210783, by rfl⟩ : syracuseStep 2947711 = 4421567) B4421567
theorem B19528613 : Blo 362758 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B4161131 : Blo 362758 4161131 := bstep (se 1 (by rfl) ⟨3120848, by rfl⟩ : syracuseStep 4161131 = 6241697) B6241697
theorem B1311335 : Blo 362758 1311335 := bstep (se 1 (by rfl) ⟨983501, by rfl⟩ : syracuseStep 1311335 = 1967003) B1967003
theorem B689087 : Blo 362758 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B820223 : Blo 362758 820223 := bstep (se 1 (by rfl) ⟨615167, by rfl⟩ : syracuseStep 820223 = 1230335) B1230335
theorem B3540023 : Blo 362758 3540023 := bstep (se 1 (by rfl) ⟨2655017, by rfl⟩ : syracuseStep 3540023 = 5310035) B5310035
theorem B2066579 : Blo 362758 2066579 := bstep (se 1 (by rfl) ⟨1549934, by rfl⟩ : syracuseStep 2066579 = 3099869) B3099869
theorem B362823 : Blo 362758 362823 := bstep (se 1 (by rfl) ⟨272117, by rfl⟩ : syracuseStep 362823 = 544235) B544235
theorem B363135 : Blo 362758 363135 := bstep (se 1 (by rfl) ⟨272351, by rfl⟩ : syracuseStep 363135 = 544703) B544703
theorem B363547 : Blo 362758 363547 := bstep (se 1 (by rfl) ⟨272660, by rfl⟩ : syracuseStep 363547 = 545321) B545321
theorem B363803 : Blo 362758 363803 := bstep (se 1 (by rfl) ⟨272852, by rfl⟩ : syracuseStep 363803 = 545705) B545705
theorem B1314103 : Blo 362758 1314103 := bstep (se 1 (by rfl) ⟨985577, by rfl⟩ : syracuseStep 1314103 = 1971155) B1971155
theorem B5312105 : Blo 362758 5312105 := bstep (se 2 (by rfl) ⟨1992039, by rfl⟩ : syracuseStep 5312105 = 3984079) B3984079
theorem B364159 : Blo 362758 364159 := bstep (se 1 (by rfl) ⟨273119, by rfl⟩ : syracuseStep 364159 = 546239) B546239
theorem B3509999 : Blo 362758 3509999 := bstep (se 1 (by rfl) ⟨2632499, by rfl⟩ : syracuseStep 3509999 = 5264999) B5264999
theorem B1380665 : Blo 362758 1380665 := bstep (se 2 (by rfl) ⟨517749, by rfl⟩ : syracuseStep 1380665 = 1035499) B1035499
theorem B692543 : Blo 362758 692543 := bstep (se 1 (by rfl) ⟨519407, by rfl⟩ : syracuseStep 692543 = 1038815) B1038815
theorem B364959 : Blo 362758 364959 := bstep (se 1 (by rfl) ⟨273719, by rfl⟩ : syracuseStep 364959 = 547439) B547439
theorem B2331463 : Blo 362758 2331463 := bstep (se 1 (by rfl) ⟨1748597, by rfl⟩ : syracuseStep 2331463 = 3497195) B3497195
theorem B365983 : Blo 362758 365983 := bstep (se 1 (by rfl) ⟨274487, by rfl⟩ : syracuseStep 365983 = 548975) B548975
theorem B923177 : Blo 362758 923177 := bstep (se 2 (by rfl) ⟨346191, by rfl⟩ : syracuseStep 923177 = 692383) B692383
theorem B825065 : Blo 362758 825065 := bstep (se 2 (by rfl) ⟨309399, by rfl⟩ : syracuseStep 825065 = 618799) B618799
theorem B816716357 : Blo 362758 816716357 := bstep (se 4 (by rfl) ⟨76567158, by rfl⟩ : syracuseStep 816716357 = 153134317) B153134317
theorem B2071727 : Blo 362758 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B1220935 : Blo 362758 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B13019075 : Blo 362758 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B1878815 : Blo 362758 1878815 := bstep (se 1 (by rfl) ⟨1409111, by rfl⟩ : syracuseStep 1878815 = 2818223) B2818223
theorem B929519 : Blo 362758 929519 := bstep (se 1 (by rfl) ⟨697139, by rfl⟩ : syracuseStep 929519 = 1394279) B1394279
theorem B2338793 : Blo 362758 2338793 := bstep (se 2 (by rfl) ⟨877047, by rfl⟩ : syracuseStep 2338793 = 1754095) B1754095
theorem B2503007 : Blo 362758 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B1388897 : Blo 362758 1388897 := bstep (se 2 (by rfl) ⟨520836, by rfl⟩ : syracuseStep 1388897 = 1041673) B1041673
theorem B1391039 : Blo 362758 1391039 := bstep (se 1 (by rfl) ⟨1043279, by rfl⟩ : syracuseStep 1391039 = 2086559) B2086559
theorem B5356955 : Blo 362758 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B1228445 : Blo 362758 1228445 := bstep (se 3 (by rfl) ⟨230333, by rfl⟩ : syracuseStep 1228445 = 460667) B460667
theorem B163431199 : Blo 362758 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B10503341 : Blo 362758 10503341 := bstep (se 3 (by rfl) ⟨1969376, by rfl⟩ : syracuseStep 10503341 = 3938753) B3938753
theorem B4146551 : Blo 362758 4146551 := bstep (se 1 (by rfl) ⟨3109913, by rfl⟩ : syracuseStep 4146551 = 6219827) B6219827
theorem B1755017 : Blo 362758 1755017 := bstep (se 2 (by rfl) ⟨658131, by rfl⟩ : syracuseStep 1755017 = 1316263) B1316263
theorem B5032595 : Blo 362758 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B445375 : Blo 362758 445375 := bstep (se 1 (by rfl) ⟨334031, by rfl⟩ : syracuseStep 445375 = 668063) B668063
theorem B2772143 : Blo 362758 2772143 := bstep (se 1 (by rfl) ⟨2079107, by rfl⟩ : syracuseStep 2772143 = 4158215) B4158215
theorem B2774087 : Blo 362758 2774087 := bstep (se 1 (by rfl) ⟨2080565, by rfl⟩ : syracuseStep 2774087 = 4161131) B4161131
theorem B1234223 : Blo 362758 1234223 := bstep (se 1 (by rfl) ⟨925667, by rfl⟩ : syracuseStep 1234223 = 1851335) B1851335
theorem B546671 : Blo 362758 546671 := bstep (se 1 (by rfl) ⟨410003, by rfl⟩ : syracuseStep 546671 = 820007) B820007
theorem B48061511 : Blo 362758 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B548351 : Blo 362758 548351 := bstep (se 1 (by rfl) ⟨411263, by rfl⟩ : syracuseStep 548351 = 822527) B822527
theorem B2088767 : Blo 362758 2088767 := bstep (se 1 (by rfl) ⟨1566575, by rfl⟩ : syracuseStep 2088767 = 3133151) B3133151
theorem B1236815 : Blo 362758 1236815 := bstep (se 1 (by rfl) ⟨927611, by rfl⟩ : syracuseStep 1236815 = 1855223) B1855223
theorem B614567 : Blo 362758 614567 := bstep (se 1 (by rfl) ⟨460925, by rfl⟩ : syracuseStep 614567 = 921851) B921851
theorem B614911 : Blo 362758 614911 := bstep (se 1 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 614911 = 922367) B922367
theorem B582623 : Blo 362758 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B550025 : Blo 362758 550025 := bstep (se 2 (by rfl) ⟨206259, by rfl⟩ : syracuseStep 550025 = 412519) B412519
theorem B18998711 : Blo 362758 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B3172297 : Blo 362758 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B1665299 : Blo 362758 1665299 := bstep (se 1 (by rfl) ⟨1248974, by rfl⟩ : syracuseStep 1665299 = 2497949) B2497949
theorem B2813417 : Blo 362758 2813417 := bstep (se 2 (by rfl) ⟨1055031, by rfl⟩ : syracuseStep 2813417 = 2110063) B2110063
theorem B25194377 : Blo 362758 25194377 := bstep (se 2 (by rfl) ⟨9447891, by rfl⟩ : syracuseStep 25194377 = 18895783) B18895783
theorem B1339361 : Blo 362758 1339361 := bstep (se 2 (by rfl) ⟨502260, by rfl⟩ : syracuseStep 1339361 = 1004521) B1004521
theorem B3043997 : Blo 362758 3043997 := bstep (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) B1141499
theorem B3930281 : Blo 362758 3930281 := bstep (se 2 (by rfl) ⟨1473855, by rfl⟩ : syracuseStep 3930281 = 2947711) B2947711
theorem B686945 : Blo 362758 686945 := bstep (se 2 (by rfl) ⟨257604, by rfl⟩ : syracuseStep 686945 = 515209) B515209
theorem B818351 : Blo 362758 818351 := bstep (se 1 (by rfl) ⟨613763, by rfl⟩ : syracuseStep 818351 = 1227527) B1227527
theorem B818927 : Blo 362758 818927 := bstep (se 1 (by rfl) ⟨614195, by rfl⟩ : syracuseStep 818927 = 1228391) B1228391
theorem B819179 : Blo 362758 819179 := bstep (se 1 (by rfl) ⟨614384, by rfl⟩ : syracuseStep 819179 = 1228769) B1228769
theorem B819881 : Blo 362758 819881 := bstep (se 2 (by rfl) ⟨307455, by rfl⟩ : syracuseStep 819881 = 614911) B614911
theorem B2360015 : Blo 362758 2360015 := bstep (se 1 (by rfl) ⟨1770011, by rfl⟩ : syracuseStep 2360015 = 3540023) B3540023
theorem B217908265 : Blo 362758 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B1377719 : Blo 362758 1377719 := bstep (se 1 (by rfl) ⟨1033289, by rfl⟩ : syracuseStep 1377719 = 2066579) B2066579
theorem B3541403 : Blo 362758 3541403 := bstep (se 1 (by rfl) ⟨2656052, by rfl⟩ : syracuseStep 3541403 = 5312105) B5312105
theorem B1837565 : Blo 362758 1837565 := bstep (se 3 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 1837565 = 689087) B689087
theorem B4229729 : Blo 362758 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B920443 : Blo 362758 920443 := bstep (se 1 (by rfl) ⟨690332, by rfl⟩ : syracuseStep 920443 = 1380665) B1380665
theorem B461695 : Blo 362758 461695 := bstep (se 1 (by rfl) ⟨346271, by rfl⟩ : syracuseStep 461695 = 692543) B692543
theorem B822815 : Blo 362758 822815 := bstep (se 1 (by rfl) ⟨617111, by rfl⟩ : syracuseStep 822815 = 1234223) B1234223
theorem B364447 : Blo 362758 364447 := bstep (se 1 (by rfl) ⟨273335, by rfl⟩ : syracuseStep 364447 = 546671) B546671
theorem B544477571 : Blo 362758 544477571 := bstep (se 1 (by rfl) ⟨408358178, by rfl⟩ : syracuseStep 544477571 = 816716357) B816716357
theorem B1381151 : Blo 362758 1381151 := bstep (se 1 (by rfl) ⟨1035863, by rfl⟩ : syracuseStep 1381151 = 2071727) B2071727
theorem B365567 : Blo 362758 365567 := bstep (se 1 (by rfl) ⟨274175, by rfl⟩ : syracuseStep 365567 = 548351) B548351
theorem B824543 : Blo 362758 824543 := bstep (se 1 (by rfl) ⟨618407, by rfl⟩ : syracuseStep 824543 = 1236815) B1236815
theorem B366683 : Blo 362758 366683 := bstep (se 1 (by rfl) ⟨275012, by rfl⟩ : syracuseStep 366683 = 550025) B550025
theorem B1875611 : Blo 362758 1875611 := bstep (se 1 (by rfl) ⟨1406708, by rfl⟩ : syracuseStep 1875611 = 2813417) B2813417
theorem B892907 : Blo 362758 892907 := bstep (se 1 (by rfl) ⟨669680, by rfl⟩ : syracuseStep 892907 = 1339361) B1339361
theorem B925931 : Blo 362758 925931 := bstep (se 1 (by rfl) ⟨694448, by rfl⟩ : syracuseStep 925931 = 1388897) B1388897
theorem B927359 : Blo 362758 927359 := bstep (se 1 (by rfl) ⟨695519, by rfl⟩ : syracuseStep 927359 = 1391039) B1391039
theorem B2764367 : Blo 362758 2764367 := bstep (se 1 (by rfl) ⟨2073275, by rfl⟩ : syracuseStep 2764367 = 4146551) B4146551
theorem B3355063 : Blo 362758 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B1848095 : Blo 362758 1848095 := bstep (se 1 (by rfl) ⟨1386071, by rfl⟩ : syracuseStep 1848095 = 2772143) B2772143
theorem B2339999 : Blo 362758 2339999 := bstep (se 1 (by rfl) ⟨1754999, by rfl⟩ : syracuseStep 2339999 = 3509999) B3509999
theorem B1849391 : Blo 362758 1849391 := bstep (se 1 (by rfl) ⟨1387043, by rfl⟩ : syracuseStep 1849391 = 2774087) B2774087
theorem B1752137 : Blo 362758 1752137 := bstep (se 2 (by rfl) ⟨657051, by rfl⟩ : syracuseStep 1752137 = 1314103) B1314103
theorem B2375333 : Blo 362758 2375333 := bstep (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) B445375
theorem B1392511 : Blo 362758 1392511 := bstep (se 1 (by rfl) ⟨1044383, by rfl⟩ : syracuseStep 1392511 = 2088767) B2088767
theorem B409711 : Blo 362758 409711 := bstep (se 1 (by rfl) ⟨307283, by rfl⟩ : syracuseStep 409711 = 614567) B614567
theorem B12665807 : Blo 362758 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B16796251 : Blo 362758 16796251 := bstep (se 1 (by rfl) ⟨12597188, by rfl⟩ : syracuseStep 16796251 = 25194377) B25194377
theorem B1559195 : Blo 362758 1559195 := bstep (se 1 (by rfl) ⟨1169396, by rfl⟩ : syracuseStep 1559195 = 2338793) B2338793
theorem B545567 : Blo 362758 545567 := bstep (se 1 (by rfl) ⟨409175, by rfl⟩ : syracuseStep 545567 = 818351) B818351
theorem B545951 : Blo 362758 545951 := bstep (se 1 (by rfl) ⟨409463, by rfl⟩ : syracuseStep 545951 = 818927) B818927
theorem B546119 : Blo 362758 546119 := bstep (se 1 (by rfl) ⟨409589, by rfl⟩ : syracuseStep 546119 = 819179) B819179
theorem B874223 : Blo 362758 874223 := bstep (se 1 (by rfl) ⟨655667, by rfl⟩ : syracuseStep 874223 = 1311335) B1311335
theorem B1627913 : Blo 362758 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B546815 : Blo 362758 546815 := bstep (se 1 (by rfl) ⟨410111, by rfl⟩ : syracuseStep 546815 = 820223) B820223
theorem B7002227 : Blo 362758 7002227 := bstep (se 1 (by rfl) ⟨5251670, by rfl⟩ : syracuseStep 7002227 = 10503341) B10503341
theorem B1170011 : Blo 362758 1170011 := bstep (se 1 (by rfl) ⟨877508, by rfl⟩ : syracuseStep 1170011 = 1755017) B1755017
theorem B615451 : Blo 362758 615451 := bstep (se 1 (by rfl) ⟨461588, by rfl⟩ : syracuseStep 615451 = 923177) B923177
theorem B550043 : Blo 362758 550043 := bstep (se 1 (by rfl) ⟨412532, by rfl⟩ : syracuseStep 550043 = 825065) B825065
theorem B32041007 : Blo 362758 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B388415 : Blo 362758 388415 := bstep (se 1 (by rfl) ⟨291311, by rfl⟩ : syracuseStep 388415 = 582623) B582623
theorem B3108617 : Blo 362758 3108617 := bstep (se 2 (by rfl) ⟨1165731, by rfl⟩ : syracuseStep 3108617 = 2331463) B2331463
theorem B8679383 : Blo 362758 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B1110199 : Blo 362758 1110199 := bstep (se 1 (by rfl) ⟨832649, by rfl⟩ : syracuseStep 1110199 = 1665299) B1665299
theorem B5010173 : Blo 362758 5010173 := bstep (se 3 (by rfl) ⟨939407, by rfl⟩ : syracuseStep 5010173 = 1878815) B1878815
theorem B619679 : Blo 362758 619679 := bstep (se 1 (by rfl) ⟨464759, by rfl⟩ : syracuseStep 619679 = 929519) B929519
theorem B1668671 : Blo 362758 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B2029331 : Blo 362758 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B2620187 : Blo 362758 2620187 := bstep (se 1 (by rfl) ⟨1965140, by rfl⟩ : syracuseStep 2620187 = 3930281) B3930281
theorem B457963 : Blo 362758 457963 := bstep (se 1 (by rfl) ⟨343472, by rfl⟩ : syracuseStep 457963 = 686945) B686945
theorem B3571303 : Blo 362758 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B818963 : Blo 362758 818963 := bstep (se 1 (by rfl) ⟨614222, by rfl⟩ : syracuseStep 818963 = 1228445) B1228445
theorem B1573343 : Blo 362758 1573343 := bstep (se 1 (by rfl) ⟨1180007, by rfl⟩ : syracuseStep 1573343 = 2360015) B2360015
theorem B918479 : Blo 362758 918479 := bstep (se 1 (by rfl) ⟨688859, by rfl⟩ : syracuseStep 918479 = 1377719) B1377719
theorem B820601 : Blo 362758 820601 := bstep (se 2 (by rfl) ⟨307725, by rfl⟩ : syracuseStep 820601 = 615451) B615451
theorem B2360935 : Blo 362758 2360935 := bstep (se 1 (by rfl) ⟨1770701, by rfl⟩ : syracuseStep 2360935 = 3541403) B3541403
theorem B2819819 : Blo 362758 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B17893669 : Blo 362758 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B363711 : Blo 362758 363711 := bstep (se 1 (by rfl) ⟨272783, by rfl⟩ : syracuseStep 363711 = 545567) B545567
theorem B920767 : Blo 362758 920767 := bstep (se 1 (by rfl) ⟨690575, by rfl⟩ : syracuseStep 920767 = 1381151) B1381151
theorem B363967 : Blo 362758 363967 := bstep (se 1 (by rfl) ⟨272975, by rfl⟩ : syracuseStep 363967 = 545951) B545951
theorem B364079 : Blo 362758 364079 := bstep (se 1 (by rfl) ⟨273059, by rfl⟩ : syracuseStep 364079 = 546119) B546119
theorem B1085275 : Blo 362758 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B364543 : Blo 362758 364543 := bstep (se 1 (by rfl) ⟨273407, by rfl⟩ : syracuseStep 364543 = 546815) B546815
theorem B5411549 : Blo 362758 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B1250407 : Blo 362758 1250407 := bstep (se 1 (by rfl) ⟨937805, by rfl⟩ : syracuseStep 1250407 = 1875611) B1875611
theorem B595271 : Blo 362758 595271 := bstep (se 1 (by rfl) ⟨446453, by rfl⟩ : syracuseStep 595271 = 892907) B892907
theorem B1480265 : Blo 362758 1480265 := bstep (se 2 (by rfl) ⟨555099, by rfl⟩ : syracuseStep 1480265 = 1110199) B1110199
theorem B366695 : Blo 362758 366695 := bstep (se 1 (by rfl) ⟨275021, by rfl⟩ : syracuseStep 366695 = 550043) B550043
theorem B3120029 : Blo 362758 3120029 := bstep (se 3 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 3120029 = 1170011) B1170011
theorem B1842911 : Blo 362758 1842911 := bstep (se 1 (by rfl) ⟨1382183, by rfl⟩ : syracuseStep 1842911 = 2764367) B2764367
theorem B2072411 : Blo 362758 2072411 := bstep (se 1 (by rfl) ⟨1554308, by rfl⟩ : syracuseStep 2072411 = 3108617) B3108617
theorem B1746791 : Blo 362758 1746791 := bstep (se 1 (by rfl) ⟨1310093, by rfl⟩ : syracuseStep 1746791 = 2620187) B2620187
theorem B4761737 : Blo 362758 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B1583555 : Blo 362758 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B1225043 : Blo 362758 1225043 := bstep (se 1 (by rfl) ⟨918782, by rfl⟩ : syracuseStep 1225043 = 1837565) B1837565
theorem B362985047 : Blo 362758 362985047 := bstep (se 1 (by rfl) ⟨272238785, by rfl⟩ : syracuseStep 362985047 = 544477571) B544477571
theorem B22395001 : Blo 362758 22395001 := bstep (se 2 (by rfl) ⟨8398125, by rfl⟩ : syracuseStep 22395001 = 16796251) B16796251
theorem B1227257 : Blo 362758 1227257 := bstep (se 2 (by rfl) ⟨460221, by rfl⟩ : syracuseStep 1227257 = 920443) B920443
theorem B4668151 : Blo 362758 4668151 := bstep (se 1 (by rfl) ⟨3501113, by rfl⟩ : syracuseStep 4668151 = 7002227) B7002227
theorem B2442469 : Blo 362758 2442469 := bstep (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) B457963
theorem B5786255 : Blo 362758 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B1232063 : Blo 362758 1232063 := bstep (se 1 (by rfl) ⟨924047, by rfl⟩ : syracuseStep 1232063 = 1848095) B1848095
theorem B1559999 : Blo 362758 1559999 := bstep (se 1 (by rfl) ⟨1169999, by rfl⟩ : syracuseStep 1559999 = 2339999) B2339999
theorem B413119 : Blo 362758 413119 := bstep (se 1 (by rfl) ⟨309839, by rfl⟩ : syracuseStep 413119 = 619679) B619679
theorem B1035773 : Blo 362758 1035773 := bstep (se 3 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 1035773 = 388415) B388415
theorem B1232927 : Blo 362758 1232927 := bstep (se 1 (by rfl) ⟨924695, by rfl⟩ : syracuseStep 1232927 = 1849391) B1849391
theorem B1168091 : Blo 362758 1168091 := bstep (se 1 (by rfl) ⟨876068, by rfl⟩ : syracuseStep 1168091 = 1752137) B1752137
theorem B1856681 : Blo 362758 1856681 := bstep (se 2 (by rfl) ⟨696255, by rfl⟩ : syracuseStep 1856681 = 1392511) B1392511
theorem B545975 : Blo 362758 545975 := bstep (se 1 (by rfl) ⟨409481, by rfl⟩ : syracuseStep 545975 = 818963) B818963
theorem B546281 : Blo 362758 546281 := bstep (se 2 (by rfl) ⟨204855, by rfl⟩ : syracuseStep 546281 = 409711) B409711
theorem B546587 : Blo 362758 546587 := bstep (se 1 (by rfl) ⟨409940, by rfl⟩ : syracuseStep 546587 = 819881) B819881
theorem B8443871 : Blo 362758 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B290544353 : Blo 362758 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B1039463 : Blo 362758 1039463 := bstep (se 1 (by rfl) ⟨779597, by rfl⟩ : syracuseStep 1039463 = 1559195) B1559195
theorem B548543 : Blo 362758 548543 := bstep (se 1 (by rfl) ⟨411407, by rfl⟩ : syracuseStep 548543 = 822815) B822815
theorem B549695 : Blo 362758 549695 := bstep (se 1 (by rfl) ⟨412271, by rfl⟩ : syracuseStep 549695 = 824543) B824543
theorem B582815 : Blo 362758 582815 := bstep (se 1 (by rfl) ⟨437111, by rfl⟩ : syracuseStep 582815 = 874223) B874223
theorem B615593 : Blo 362758 615593 := bstep (se 2 (by rfl) ⟨230847, by rfl⟩ : syracuseStep 615593 = 461695) B461695
theorem B617287 : Blo 362758 617287 := bstep (se 1 (by rfl) ⟨462965, by rfl⟩ : syracuseStep 617287 = 925931) B925931
theorem B618239 : Blo 362758 618239 := bstep (se 1 (by rfl) ⟨463679, by rfl⟩ : syracuseStep 618239 = 927359) B927359
theorem B21360671 : Blo 362758 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B3340115 : Blo 362758 3340115 := bstep (se 1 (by rfl) ⟨2505086, by rfl⟩ : syracuseStep 3340115 = 5010173) B5010173
theorem B1112447 : Blo 362758 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B1048895 : Blo 362758 1048895 := bstep (se 1 (by rfl) ⟨786671, by rfl⟩ : syracuseStep 1048895 = 1573343) B1573343
theorem B821375 : Blo 362758 821375 := bstep (se 1 (by rfl) ⟨616031, by rfl⟩ : syracuseStep 821375 = 1232063) B1232063
theorem B3147913 : Blo 362758 3147913 := bstep (se 2 (by rfl) ⟨1180467, by rfl⟩ : syracuseStep 3147913 = 2360935) B2360935
theorem B690515 : Blo 362758 690515 := bstep (se 1 (by rfl) ⟨517886, by rfl⟩ : syracuseStep 690515 = 1035773) B1035773
theorem B821951 : Blo 362758 821951 := bstep (se 1 (by rfl) ⟨616463, by rfl⟩ : syracuseStep 821951 = 1232927) B1232927
theorem B23858225 : Blo 362758 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B363983 : Blo 362758 363983 := bstep (se 1 (by rfl) ⟨272987, by rfl⟩ : syracuseStep 363983 = 545975) B545975
theorem B396847 : Blo 362758 396847 := bstep (se 1 (by rfl) ⟨297635, by rfl⟩ : syracuseStep 396847 = 595271) B595271
theorem B364187 : Blo 362758 364187 := bstep (se 1 (by rfl) ⟨273140, by rfl⟩ : syracuseStep 364187 = 546281) B546281
theorem B986843 : Blo 362758 986843 := bstep (se 1 (by rfl) ⟨740132, by rfl⟩ : syracuseStep 986843 = 1480265) B1480265
theorem B823049 : Blo 362758 823049 := bstep (se 2 (by rfl) ⟨308643, by rfl⟩ : syracuseStep 823049 = 617287) B617287
theorem B364391 : Blo 362758 364391 := bstep (se 1 (by rfl) ⟨273293, by rfl⟩ : syracuseStep 364391 = 546587) B546587
theorem B193696235 : Blo 362758 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B692975 : Blo 362758 692975 := bstep (se 1 (by rfl) ⟨519731, by rfl⟩ : syracuseStep 692975 = 1039463) B1039463
theorem B1447033 : Blo 362758 1447033 := bstep (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) B1085275
theorem B365695 : Blo 362758 365695 := bstep (se 1 (by rfl) ⟨274271, by rfl⟩ : syracuseStep 365695 = 548543) B548543
theorem B1381607 : Blo 362758 1381607 := bstep (se 1 (by rfl) ⟨1036205, by rfl⟩ : syracuseStep 1381607 = 2072411) B2072411
theorem B366463 : Blo 362758 366463 := bstep (se 1 (by rfl) ⟨274847, by rfl⟩ : syracuseStep 366463 = 549695) B549695
theorem B2203301 : Blo 362758 2203301 := bstep (se 4 (by rfl) ⟨206559, by rfl⟩ : syracuseStep 2203301 = 413119) B413119
theorem B29860001 : Blo 362758 29860001 := bstep (se 2 (by rfl) ⟨11197500, by rfl⟩ : syracuseStep 29860001 = 22395001) B22395001
theorem B3256625 : Blo 362758 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B14430797 : Blo 362758 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B1554173 : Blo 362758 1554173 := bstep (se 3 (by rfl) ⟨291407, by rfl⟩ : syracuseStep 1554173 = 582815) B582815
theorem B1227689 : Blo 362758 1227689 := bstep (se 2 (by rfl) ⟨460383, by rfl⟩ : syracuseStep 1227689 = 920767) B920767
theorem B2080019 : Blo 362758 2080019 := bstep (se 1 (by rfl) ⟨1560014, by rfl⟩ : syracuseStep 2080019 = 3120029) B3120029
theorem B7519517 : Blo 362758 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B1228607 : Blo 362758 1228607 := bstep (se 1 (by rfl) ⟨921455, by rfl⟩ : syracuseStep 1228607 = 1842911) B1842911
theorem B6668837 : Blo 362758 6668837 := bstep (se 4 (by rfl) ⟨625203, by rfl⟩ : syracuseStep 6668837 = 1250407) B1250407
theorem B410395 : Blo 362758 410395 := bstep (se 1 (by rfl) ⟨307796, by rfl⟩ : syracuseStep 410395 = 615593) B615593
theorem B1164527 : Blo 362758 1164527 := bstep (se 1 (by rfl) ⟨873395, by rfl⟩ : syracuseStep 1164527 = 1746791) B1746791
theorem B412159 : Blo 362758 412159 := bstep (se 1 (by rfl) ⟨309119, by rfl⟩ : syracuseStep 412159 = 618239) B618239
theorem B14240447 : Blo 362758 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B741631 : Blo 362758 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B612319 : Blo 362758 612319 := bstep (se 1 (by rfl) ⟨459239, by rfl⟩ : syracuseStep 612319 = 918479) B918479
theorem B547067 : Blo 362758 547067 := bstep (se 1 (by rfl) ⟨410300, by rfl⟩ : syracuseStep 547067 = 820601) B820601
theorem B3857503 : Blo 362758 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B1039999 : Blo 362758 1039999 := bstep (se 1 (by rfl) ⟨779999, by rfl⟩ : syracuseStep 1039999 = 1559999) B1559999
theorem B778727 : Blo 362758 778727 := bstep (se 1 (by rfl) ⟨584045, by rfl⟩ : syracuseStep 778727 = 1168091) B1168091
theorem B1237787 : Blo 362758 1237787 := bstep (se 1 (by rfl) ⟨928340, by rfl⟩ : syracuseStep 1237787 = 1856681) B1856681
theorem B5629247 : Blo 362758 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B4222813 : Blo 362758 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B3174491 : Blo 362758 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B816695 : Blo 362758 816695 := bstep (se 1 (by rfl) ⟨612521, by rfl⟩ : syracuseStep 816695 = 1225043) B1225043
theorem B6224201 : Blo 362758 6224201 := bstep (se 2 (by rfl) ⟨2334075, by rfl⟩ : syracuseStep 6224201 = 4668151) B4668151
theorem B241990031 : Blo 362758 241990031 := bstep (se 1 (by rfl) ⟨181492523, by rfl⟩ : syracuseStep 241990031 = 362985047) B362985047
theorem B2226743 : Blo 362758 2226743 := bstep (se 1 (by rfl) ⟨1670057, by rfl⟩ : syracuseStep 2226743 = 3340115) B3340115
theorem B818171 : Blo 362758 818171 := bstep (se 1 (by rfl) ⟨613628, by rfl⟩ : syracuseStep 818171 = 1227257) B1227257
theorem B460343 : Blo 362758 460343 := bstep (se 1 (by rfl) ⟨345257, by rfl⟩ : syracuseStep 460343 = 690515) B690515
theorem B657895 : Blo 362758 657895 := bstep (se 1 (by rfl) ⟨493421, by rfl⟩ : syracuseStep 657895 = 986843) B986843
theorem B4197217 : Blo 362758 4197217 := bstep (se 2 (by rfl) ⟨1573956, by rfl⟩ : syracuseStep 4197217 = 3147913) B3147913
theorem B921071 : Blo 362758 921071 := bstep (se 1 (by rfl) ⟨690803, by rfl⟩ : syracuseStep 921071 = 1381607) B1381607
theorem B364711 : Blo 362758 364711 := bstep (se 1 (by rfl) ⟨273533, by rfl⟩ : syracuseStep 364711 = 547067) B547067
theorem B529129 : Blo 362758 529129 := bstep (se 2 (by rfl) ⟨198423, by rfl⟩ : syracuseStep 529129 = 396847) B396847
theorem B988841 : Blo 362758 988841 := bstep (se 2 (by rfl) ⟨370815, by rfl⟩ : syracuseStep 988841 = 741631) B741631
theorem B825191 : Blo 362758 825191 := bstep (se 1 (by rfl) ⟨618893, by rfl⟩ : syracuseStep 825191 = 1237787) B1237787
theorem B2171083 : Blo 362758 2171083 := bstep (se 1 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 2171083 = 3256625) B3256625
theorem B161326687 : Blo 362758 161326687 := bstep (se 1 (by rfl) ⟨120995015, by rfl⟩ : syracuseStep 161326687 = 241990031) B241990031
theorem B1484495 : Blo 362758 1484495 := bstep (se 1 (by rfl) ⟨1113371, by rfl⟩ : syracuseStep 1484495 = 2226743) B2226743
theorem B1386665 : Blo 362758 1386665 := bstep (se 2 (by rfl) ⟨519999, by rfl⟩ : syracuseStep 1386665 = 1039999) B1039999
theorem B1386679 : Blo 362758 1386679 := bstep (se 1 (by rfl) ⟨1040009, by rfl⟩ : syracuseStep 1386679 = 2080019) B2080019
theorem B699263 : Blo 362758 699263 := bstep (se 1 (by rfl) ⟨524447, by rfl⟩ : syracuseStep 699263 = 1048895) B1048895
theorem B8465309 : Blo 362758 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B1847933 : Blo 362758 1847933 := bstep (se 3 (by rfl) ⟨346487, by rfl⟩ : syracuseStep 1847933 = 692975) B692975
theorem B15905483 : Blo 362758 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B19906667 : Blo 362758 19906667 := bstep (se 1 (by rfl) ⟨14930000, by rfl⟩ : syracuseStep 19906667 = 29860001) B29860001
theorem B3752831 : Blo 362758 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B9620531 : Blo 362758 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B544463 : Blo 362758 544463 := bstep (se 1 (by rfl) ⟨408347, by rfl⟩ : syracuseStep 544463 = 816695) B816695
theorem B1036115 : Blo 362758 1036115 := bstep (se 1 (by rfl) ⟨777086, by rfl⟩ : syracuseStep 1036115 = 1554173) B1554173
theorem B4149467 : Blo 362758 4149467 := bstep (se 1 (by rfl) ⟨3112100, by rfl⟩ : syracuseStep 4149467 = 6224201) B6224201
theorem B545447 : Blo 362758 545447 := bstep (se 1 (by rfl) ⟨409085, by rfl⟩ : syracuseStep 545447 = 818171) B818171
theorem B4445891 : Blo 362758 4445891 := bstep (se 1 (by rfl) ⟨3334418, by rfl⟩ : syracuseStep 4445891 = 6668837) B6668837
theorem B776351 : Blo 362758 776351 := bstep (se 1 (by rfl) ⟨582263, by rfl⟩ : syracuseStep 776351 = 1164527) B1164527
theorem B547193 : Blo 362758 547193 := bstep (se 2 (by rfl) ⟨205197, by rfl⟩ : syracuseStep 547193 = 410395) B410395
theorem B547583 : Blo 362758 547583 := bstep (se 1 (by rfl) ⟨410687, by rfl⟩ : syracuseStep 547583 = 821375) B821375
theorem B547967 : Blo 362758 547967 := bstep (se 1 (by rfl) ⟨410975, by rfl⟩ : syracuseStep 547967 = 821951) B821951
theorem B9493631 : Blo 362758 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B548699 : Blo 362758 548699 := bstep (se 1 (by rfl) ⟨411524, by rfl⟩ : syracuseStep 548699 = 823049) B823049
theorem B129130823 : Blo 362758 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B549545 : Blo 362758 549545 := bstep (se 2 (by rfl) ⟨206079, by rfl⟩ : syracuseStep 549545 = 412159) B412159
theorem B1468867 : Blo 362758 1468867 := bstep (se 1 (by rfl) ⟨1101650, by rfl⟩ : syracuseStep 1468867 = 2203301) B2203301
theorem B5630417 : Blo 362758 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B519151 : Blo 362758 519151 := bstep (se 1 (by rfl) ⟨389363, by rfl⟩ : syracuseStep 519151 = 778727) B778727
theorem B1929377 : Blo 362758 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B816425 : Blo 362758 816425 := bstep (se 2 (by rfl) ⟨306159, by rfl⟩ : syracuseStep 816425 = 612319) B612319
theorem B5143337 : Blo 362758 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B818459 : Blo 362758 818459 := bstep (se 1 (by rfl) ⟨613844, by rfl⟩ : syracuseStep 818459 = 1227689) B1227689
theorem B5013011 : Blo 362758 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B819071 : Blo 362758 819071 := bstep (se 1 (by rfl) ⟨614303, by rfl⟩ : syracuseStep 819071 = 1228607) B1228607
theorem B13271111 : Blo 362758 13271111 := bstep (se 1 (by rfl) ⟨9953333, by rfl⟩ : syracuseStep 13271111 = 19906667) B19906667
theorem B5145005 : Blo 362758 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B362975 : Blo 362758 362975 := bstep (se 1 (by rfl) ⟨272231, by rfl⟩ : syracuseStep 362975 = 544463) B544463
theorem B690743 : Blo 362758 690743 := bstep (se 1 (by rfl) ⟨518057, by rfl⟩ : syracuseStep 690743 = 1036115) B1036115
theorem B363631 : Blo 362758 363631 := bstep (se 1 (by rfl) ⟨272723, by rfl⟩ : syracuseStep 363631 = 545447) B545447
theorem B659227 : Blo 362758 659227 := bstep (se 1 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 659227 = 988841) B988841
theorem B692201 : Blo 362758 692201 := bstep (se 2 (by rfl) ⟨259575, by rfl⟩ : syracuseStep 692201 = 519151) B519151
theorem B364795 : Blo 362758 364795 := bstep (se 1 (by rfl) ⟨273596, by rfl⟩ : syracuseStep 364795 = 547193) B547193
theorem B365055 : Blo 362758 365055 := bstep (se 1 (by rfl) ⟨273791, by rfl⟩ : syracuseStep 365055 = 547583) B547583
theorem B365311 : Blo 362758 365311 := bstep (se 1 (by rfl) ⟨273983, by rfl⟩ : syracuseStep 365311 = 547967) B547967
theorem B6329087 : Blo 362758 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B365799 : Blo 362758 365799 := bstep (se 1 (by rfl) ⟨274349, by rfl⟩ : syracuseStep 365799 = 548699) B548699
theorem B86087215 : Blo 362758 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B2070269 : Blo 362758 2070269 := bstep (se 3 (by rfl) ⟨388175, by rfl⟩ : syracuseStep 2070269 = 776351) B776351
theorem B366363 : Blo 362758 366363 := bstep (se 1 (by rfl) ⟨274772, by rfl⟩ : syracuseStep 366363 = 549545) B549545
theorem B989663 : Blo 362758 989663 := bstep (se 1 (by rfl) ⟨742247, by rfl⟩ : syracuseStep 989663 = 1484495) B1484495
theorem B924443 : Blo 362758 924443 := bstep (se 1 (by rfl) ⟨693332, by rfl⟩ : syracuseStep 924443 = 1386665) B1386665
theorem B466175 : Blo 362758 466175 := bstep (se 1 (by rfl) ⟨349631, by rfl⟩ : syracuseStep 466175 = 699263) B699263
theorem B5643539 : Blo 362758 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B2894777 : Blo 362758 2894777 := bstep (se 2 (by rfl) ⟨1085541, by rfl⟩ : syracuseStep 2894777 = 2171083) B2171083
theorem B2501887 : Blo 362758 2501887 := bstep (se 1 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 2501887 = 3752831) B3752831
theorem B215102249 : Blo 362758 215102249 := bstep (se 2 (by rfl) ⟨80663343, by rfl⟩ : syracuseStep 215102249 = 161326687) B161326687
theorem B2766311 : Blo 362758 2766311 := bstep (se 1 (by rfl) ⟨2074733, by rfl⟩ : syracuseStep 2766311 = 4149467) B4149467
theorem B1848905 : Blo 362758 1848905 := bstep (se 2 (by rfl) ⟨693339, by rfl⟩ : syracuseStep 1848905 = 1386679) B1386679
theorem B2963927 : Blo 362758 2963927 := bstep (se 1 (by rfl) ⟨2222945, by rfl⟩ : syracuseStep 2963927 = 4445891) B4445891
theorem B1227581 : Blo 362758 1227581 := bstep (se 3 (by rfl) ⟨230171, by rfl⟩ : syracuseStep 1227581 = 460343) B460343
theorem B705505 : Blo 362758 705505 := bstep (se 2 (by rfl) ⟨264564, by rfl⟩ : syracuseStep 705505 = 529129) B529129
theorem B3753611 : Blo 362758 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B1231955 : Blo 362758 1231955 := bstep (se 1 (by rfl) ⟨923966, by rfl⟩ : syracuseStep 1231955 = 1847933) B1847933
theorem B10603655 : Blo 362758 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B544283 : Blo 362758 544283 := bstep (se 1 (by rfl) ⟨408212, by rfl⟩ : syracuseStep 544283 = 816425) B816425
theorem B3428891 : Blo 362758 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B545639 : Blo 362758 545639 := bstep (se 1 (by rfl) ⟨409229, by rfl⟩ : syracuseStep 545639 = 818459) B818459
theorem B546047 : Blo 362758 546047 := bstep (se 1 (by rfl) ⟨409535, by rfl⟩ : syracuseStep 546047 = 819071) B819071
theorem B6413687 : Blo 362758 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B614047 : Blo 362758 614047 := bstep (se 1 (by rfl) ⟨460535, by rfl⟩ : syracuseStep 614047 = 921071) B921071
theorem B1958489 : Blo 362758 1958489 := bstep (se 2 (by rfl) ⟨734433, by rfl⟩ : syracuseStep 1958489 = 1468867) B1468867
theorem B877193 : Blo 362758 877193 := bstep (se 2 (by rfl) ⟨328947, by rfl⟩ : syracuseStep 877193 = 657895) B657895
theorem B5596289 : Blo 362758 5596289 := bstep (se 2 (by rfl) ⟨2098608, by rfl⟩ : syracuseStep 5596289 = 4197217) B4197217
theorem B550127 : Blo 362758 550127 := bstep (se 1 (by rfl) ⟨412595, by rfl⟩ : syracuseStep 550127 = 825191) B825191
theorem B3342007 : Blo 362758 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B8847407 : Blo 362758 8847407 := bstep (se 1 (by rfl) ⟨6635555, by rfl⟩ : syracuseStep 8847407 = 13271111) B13271111
theorem B460495 : Blo 362758 460495 := bstep (se 1 (by rfl) ⟨345371, by rfl⟩ : syracuseStep 460495 = 690743) B690743
theorem B821303 : Blo 362758 821303 := bstep (se 1 (by rfl) ⟨615977, by rfl⟩ : syracuseStep 821303 = 1231955) B1231955
theorem B362855 : Blo 362758 362855 := bstep (se 1 (by rfl) ⟨272141, by rfl⟩ : syracuseStep 362855 = 544283) B544283
theorem B461467 : Blo 362758 461467 := bstep (se 1 (by rfl) ⟨346100, by rfl⟩ : syracuseStep 461467 = 692201) B692201
theorem B363759 : Blo 362758 363759 := bstep (se 1 (by rfl) ⟨272819, by rfl⟩ : syracuseStep 363759 = 545639) B545639
theorem B364031 : Blo 362758 364031 := bstep (se 1 (by rfl) ⟨273023, by rfl⟩ : syracuseStep 364031 = 546047) B546047
theorem B1380179 : Blo 362758 1380179 := bstep (se 1 (by rfl) ⟨1035134, by rfl⟩ : syracuseStep 1380179 = 2070269) B2070269
theorem B366751 : Blo 362758 366751 := bstep (se 1 (by rfl) ⟨275063, by rfl⟩ : syracuseStep 366751 = 550127) B550127
theorem B143401499 : Blo 362758 143401499 := bstep (se 1 (by rfl) ⟨107551124, by rfl⟩ : syracuseStep 143401499 = 215102249) B215102249
theorem B1844207 : Blo 362758 1844207 := bstep (se 1 (by rfl) ⟨1383155, by rfl⟩ : syracuseStep 1844207 = 2766311) B2766311
theorem B1975951 : Blo 362758 1975951 := bstep (se 1 (by rfl) ⟨1481963, by rfl⟩ : syracuseStep 1975951 = 2963927) B2963927
theorem B2502407 : Blo 362758 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B4275791 : Blo 362758 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B2639101 : Blo 362758 2639101 := bstep (se 3 (by rfl) ⟨494831, by rfl⟩ : syracuseStep 2639101 = 989663) B989663
theorem B1232603 : Blo 362758 1232603 := bstep (se 1 (by rfl) ⟨924452, by rfl⟩ : syracuseStep 1232603 = 1848905) B1848905
theorem B13720013 : Blo 362758 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B940673 : Blo 362758 940673 := bstep (se 2 (by rfl) ⟨352752, by rfl⟩ : syracuseStep 940673 = 705505) B705505
theorem B7069103 : Blo 362758 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B2285927 : Blo 362758 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B4219391 : Blo 362758 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B3335849 : Blo 362758 3335849 := bstep (se 2 (by rfl) ⟨1250943, by rfl⟩ : syracuseStep 3335849 = 2501887) B2501887
theorem B616295 : Blo 362758 616295 := bstep (se 1 (by rfl) ⟨462221, by rfl⟩ : syracuseStep 616295 = 924443) B924443
theorem B3762359 : Blo 362758 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B878969 : Blo 362758 878969 := bstep (se 2 (by rfl) ⟨329613, by rfl⟩ : syracuseStep 878969 = 659227) B659227
theorem B1305659 : Blo 362758 1305659 := bstep (se 1 (by rfl) ⟨979244, by rfl⟩ : syracuseStep 1305659 = 1958489) B1958489
theorem B584795 : Blo 362758 584795 := bstep (se 1 (by rfl) ⟨438596, by rfl⟩ : syracuseStep 584795 = 877193) B877193
theorem B3730859 : Blo 362758 3730859 := bstep (se 1 (by rfl) ⟨2798144, by rfl⟩ : syracuseStep 3730859 = 5596289) B5596289
theorem B1929851 : Blo 362758 1929851 := bstep (se 1 (by rfl) ⟨1447388, by rfl⟩ : syracuseStep 1929851 = 2894777) B2894777
theorem B114782953 : Blo 362758 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B1243133 : Blo 362758 1243133 := bstep (se 3 (by rfl) ⟨233087, by rfl⟩ : syracuseStep 1243133 = 466175) B466175
theorem B818387 : Blo 362758 818387 := bstep (se 1 (by rfl) ⟨613790, by rfl⟩ : syracuseStep 818387 = 1227581) B1227581
theorem B818729 : Blo 362758 818729 := bstep (se 2 (by rfl) ⟨307023, by rfl⟩ : syracuseStep 818729 = 614047) B614047
theorem B4456009 : Blo 362758 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B5898271 : Blo 362758 5898271 := bstep (se 1 (by rfl) ⟨4423703, by rfl⟩ : syracuseStep 5898271 = 8847407) B8847407
theorem B821735 : Blo 362758 821735 := bstep (se 1 (by rfl) ⟨616301, by rfl⟩ : syracuseStep 821735 = 1232603) B1232603
theorem B920119 : Blo 362758 920119 := bstep (se 1 (by rfl) ⟨690089, by rfl⟩ : syracuseStep 920119 = 1380179) B1380179
theorem B9146675 : Blo 362758 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B627115 : Blo 362758 627115 := bstep (se 1 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 627115 = 940673) B940673
theorem B1286567 : Blo 362758 1286567 := bstep (se 1 (by rfl) ⟨964925, by rfl⟩ : syracuseStep 1286567 = 1929851) B1929851
theorem B828755 : Blo 362758 828755 := bstep (se 1 (by rfl) ⟨621566, by rfl⟩ : syracuseStep 828755 = 1243133) B1243133
theorem B5941345 : Blo 362758 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B3518801 : Blo 362758 3518801 := bstep (se 2 (by rfl) ⟨1319550, by rfl⟩ : syracuseStep 3518801 = 2639101) B2639101
theorem B2634601 : Blo 362758 2634601 := bstep (se 2 (by rfl) ⟨987975, by rfl⟩ : syracuseStep 2634601 = 1975951) B1975951
theorem B1523951 : Blo 362758 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B95600999 : Blo 362758 95600999 := bstep (se 1 (by rfl) ⟨71700749, by rfl⟩ : syracuseStep 95600999 = 143401499) B143401499
theorem B1229471 : Blo 362758 1229471 := bstep (se 1 (by rfl) ⟨922103, by rfl⟩ : syracuseStep 1229471 = 1844207) B1844207
theorem B153043937 : Blo 362758 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B2343917 : Blo 362758 2343917 := bstep (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) B878969
theorem B410863 : Blo 362758 410863 := bstep (se 1 (by rfl) ⟨308147, by rfl⟩ : syracuseStep 410863 = 616295) B616295
theorem B2508239 : Blo 362758 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B870439 : Blo 362758 870439 := bstep (se 1 (by rfl) ⟨652829, by rfl⟩ : syracuseStep 870439 = 1305659) B1305659
theorem B545591 : Blo 362758 545591 := bstep (se 1 (by rfl) ⟨409193, by rfl⟩ : syracuseStep 545591 = 818387) B818387
theorem B545819 : Blo 362758 545819 := bstep (se 1 (by rfl) ⟨409364, by rfl⟩ : syracuseStep 545819 = 818729) B818729
theorem B547535 : Blo 362758 547535 := bstep (se 1 (by rfl) ⟨410651, by rfl⟩ : syracuseStep 547535 = 821303) B821303
theorem B613993 : Blo 362758 613993 := bstep (se 2 (by rfl) ⟨230247, by rfl⟩ : syracuseStep 613993 = 460495) B460495
theorem B615289 : Blo 362758 615289 := bstep (se 2 (by rfl) ⟨230733, by rfl⟩ : syracuseStep 615289 = 461467) B461467
theorem B4712735 : Blo 362758 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B2812927 : Blo 362758 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B2223899 : Blo 362758 2223899 := bstep (se 1 (by rfl) ⟨1667924, by rfl⟩ : syracuseStep 2223899 = 3335849) B3335849
theorem B389863 : Blo 362758 389863 := bstep (se 1 (by rfl) ⟨292397, by rfl⟩ : syracuseStep 389863 = 584795) B584795
theorem B2487239 : Blo 362758 2487239 := bstep (se 1 (by rfl) ⟨1865429, by rfl⟩ : syracuseStep 2487239 = 3730859) B3730859
theorem B1668271 : Blo 362758 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B2850527 : Blo 362758 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B7864361 : Blo 362758 7864361 := bstep (se 2 (by rfl) ⟨2949135, by rfl⟩ : syracuseStep 7864361 = 5898271) B5898271
theorem B1015967 : Blo 362758 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B63733999 : Blo 362758 63733999 := bstep (se 1 (by rfl) ⟨47800499, by rfl⟩ : syracuseStep 63733999 = 95600999) B95600999
theorem B819647 : Blo 362758 819647 := bstep (se 1 (by rfl) ⟨614735, by rfl⟩ : syracuseStep 819647 = 1229471) B1229471
theorem B1672159 : Blo 362758 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B820385 : Blo 362758 820385 := bstep (se 2 (by rfl) ⟨307644, by rfl⟩ : syracuseStep 820385 = 615289) B615289
theorem B6097783 : Blo 362758 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B363727 : Blo 362758 363727 := bstep (se 1 (by rfl) ⟨272795, by rfl⟩ : syracuseStep 363727 = 545591) B545591
theorem B363879 : Blo 362758 363879 := bstep (se 1 (by rfl) ⟨272909, by rfl⟩ : syracuseStep 363879 = 545819) B545819
theorem B365023 : Blo 362758 365023 := bstep (se 1 (by rfl) ⟨273767, by rfl⟩ : syracuseStep 365023 = 547535) B547535
theorem B857711 : Blo 362758 857711 := bstep (se 1 (by rfl) ⟨643283, by rfl⟩ : syracuseStep 857711 = 1286567) B1286567
theorem B3512801 : Blo 362758 3512801 := bstep (se 2 (by rfl) ⟨1317300, by rfl⟩ : syracuseStep 3512801 = 2634601) B2634601
theorem B1482599 : Blo 362758 1482599 := bstep (se 1 (by rfl) ⟨1111949, by rfl⟩ : syracuseStep 1482599 = 2223899) B2223899
theorem B1160585 : Blo 362758 1160585 := bstep (se 2 (by rfl) ⟨435219, by rfl⟩ : syracuseStep 1160585 = 870439) B870439
theorem B1226825 : Blo 362758 1226825 := bstep (se 2 (by rfl) ⟨460059, by rfl⟩ : syracuseStep 1226825 = 920119) B920119
theorem B2079269 : Blo 362758 2079269 := bstep (se 4 (by rfl) ⟨194931, by rfl⟩ : syracuseStep 2079269 = 389863) B389863
theorem B3750569 : Blo 362758 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B836153 : Blo 362758 836153 := bstep (se 2 (by rfl) ⟨313557, by rfl⟩ : syracuseStep 836153 = 627115) B627115
theorem B2345867 : Blo 362758 2345867 := bstep (se 1 (by rfl) ⟨1759400, by rfl⟩ : syracuseStep 2345867 = 3518801) B3518801
theorem B1658159 : Blo 362758 1658159 := bstep (se 1 (by rfl) ⟨1243619, by rfl⟩ : syracuseStep 1658159 = 2487239) B2487239
theorem B102029291 : Blo 362758 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B547817 : Blo 362758 547817 := bstep (se 2 (by rfl) ⟨205431, by rfl⟩ : syracuseStep 547817 = 410863) B410863
theorem B547823 : Blo 362758 547823 := bstep (se 1 (by rfl) ⟨410867, by rfl⟩ : syracuseStep 547823 = 821735) B821735
theorem B6250445 : Blo 362758 6250445 := bstep (se 3 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 6250445 = 2343917) B2343917
theorem B7921793 : Blo 362758 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B552503 : Blo 362758 552503 := bstep (se 1 (by rfl) ⟨414377, by rfl⟩ : syracuseStep 552503 = 828755) B828755
theorem B3141823 : Blo 362758 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B2224361 : Blo 362758 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B818657 : Blo 362758 818657 := bstep (se 2 (by rfl) ⟨306996, by rfl⟩ : syracuseStep 818657 = 613993) B613993
theorem B1900351 : Blo 362758 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B5242907 : Blo 362758 5242907 := bstep (se 1 (by rfl) ⟨3932180, by rfl⟩ : syracuseStep 5242907 = 7864361) B7864361
theorem B557435 : Blo 362758 557435 := bstep (se 1 (by rfl) ⟨418076, by rfl⟩ : syracuseStep 557435 = 836153) B836153
theorem B2229545 : Blo 362758 2229545 := bstep (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) B1672159
theorem B8130377 : Blo 362758 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B365211 : Blo 362758 365211 := bstep (se 1 (by rfl) ⟨273908, by rfl⟩ : syracuseStep 365211 = 547817) B547817
theorem B365215 : Blo 362758 365215 := bstep (se 1 (by rfl) ⟨273911, by rfl⟩ : syracuseStep 365215 = 547823) B547823
theorem B988399 : Blo 362758 988399 := bstep (se 1 (by rfl) ⟨741299, by rfl⟩ : syracuseStep 988399 = 1482599) B1482599
theorem B4166963 : Blo 362758 4166963 := bstep (se 1 (by rfl) ⟨3125222, by rfl⟩ : syracuseStep 4166963 = 6250445) B6250445
theorem B5281195 : Blo 362758 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B368335 : Blo 362758 368335 := bstep (se 1 (by rfl) ⟨276251, by rfl⟩ : syracuseStep 368335 = 552503) B552503
theorem B1482907 : Blo 362758 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B10135205 : Blo 362758 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B1386179 : Blo 362758 1386179 := bstep (se 1 (by rfl) ⟨1039634, by rfl⟩ : syracuseStep 1386179 = 2079269) B2079269
theorem B2500379 : Blo 362758 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B84978665 : Blo 362758 84978665 := bstep (se 2 (by rfl) ⟨31866999, by rfl⟩ : syracuseStep 84978665 = 63733999) B63733999
theorem B571807 : Blo 362758 571807 := bstep (se 1 (by rfl) ⟨428855, by rfl⟩ : syracuseStep 571807 = 857711) B857711
theorem B2341867 : Blo 362758 2341867 := bstep (se 1 (by rfl) ⟨1756400, by rfl⟩ : syracuseStep 2341867 = 3512801) B3512801
theorem B773723 : Blo 362758 773723 := bstep (se 1 (by rfl) ⟨580292, by rfl⟩ : syracuseStep 773723 = 1160585) B1160585
theorem B545771 : Blo 362758 545771 := bstep (se 1 (by rfl) ⟨409328, by rfl⟩ : syracuseStep 545771 = 818657) B818657
theorem B546431 : Blo 362758 546431 := bstep (se 1 (by rfl) ⟨409823, by rfl⟩ : syracuseStep 546431 = 819647) B819647
theorem B2709245 : Blo 362758 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B546923 : Blo 362758 546923 := bstep (se 1 (by rfl) ⟨410192, by rfl⟩ : syracuseStep 546923 = 820385) B820385
theorem B1563911 : Blo 362758 1563911 := bstep (se 1 (by rfl) ⟨1172933, by rfl⟩ : syracuseStep 1563911 = 2345867) B2345867
theorem B1105439 : Blo 362758 1105439 := bstep (se 1 (by rfl) ⟨829079, by rfl⟩ : syracuseStep 1105439 = 1658159) B1658159
theorem B68019527 : Blo 362758 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B4189097 : Blo 362758 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B817883 : Blo 362758 817883 := bstep (se 1 (by rfl) ⟨613412, by rfl⟩ : syracuseStep 817883 = 1226825) B1226825
theorem B363847 : Blo 362758 363847 := bstep (se 1 (by rfl) ⟨272885, by rfl⟩ : syracuseStep 363847 = 545771) B545771
theorem B364287 : Blo 362758 364287 := bstep (se 1 (by rfl) ⟨273215, by rfl⟩ : syracuseStep 364287 = 546431) B546431
theorem B364615 : Blo 362758 364615 := bstep (se 1 (by rfl) ⟨273461, by rfl⟩ : syracuseStep 364615 = 546923) B546923
theorem B6756803 : Blo 362758 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B924119 : Blo 362758 924119 := bstep (se 1 (by rfl) ⟨693089, by rfl⟩ : syracuseStep 924119 = 1386179) B1386179
theorem B1317865 : Blo 362758 1317865 := bstep (se 2 (by rfl) ⟨494199, by rfl⟩ : syracuseStep 1317865 = 988399) B988399
theorem B2792731 : Blo 362758 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B762409 : Blo 362758 762409 := bstep (se 2 (by rfl) ⟨285903, by rfl⟩ : syracuseStep 762409 = 571807) B571807
theorem B3122489 : Blo 362758 3122489 := bstep (se 2 (by rfl) ⟨1170933, by rfl⟩ : syracuseStep 3122489 = 2341867) B2341867
theorem B1977209 : Blo 362758 1977209 := bstep (se 2 (by rfl) ⟨741453, by rfl⟩ : syracuseStep 1977209 = 1482907) B1482907
theorem B371623 : Blo 362758 371623 := bstep (se 1 (by rfl) ⟨278717, by rfl⟩ : syracuseStep 371623 = 557435) B557435
theorem B1486363 : Blo 362758 1486363 := bstep (se 1 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 1486363 = 2229545) B2229545
theorem B5420251 : Blo 362758 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B7224653 : Blo 362758 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B545255 : Blo 362758 545255 := bstep (se 1 (by rfl) ⟨408941, by rfl⟩ : syracuseStep 545255 = 817883) B817883
theorem B3495271 : Blo 362758 3495271 := bstep (se 1 (by rfl) ⟨2621453, by rfl⟩ : syracuseStep 3495271 = 5242907) B5242907
theorem B2777975 : Blo 362758 2777975 := bstep (se 1 (by rfl) ⟨2083481, by rfl⟩ : syracuseStep 2777975 = 4166963) B4166963
theorem B1042607 : Blo 362758 1042607 := bstep (se 1 (by rfl) ⟨781955, by rfl⟩ : syracuseStep 1042607 = 1563911) B1563911
theorem B45346351 : Blo 362758 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B1666919 : Blo 362758 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B7041593 : Blo 362758 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B56652443 : Blo 362758 56652443 := bstep (se 1 (by rfl) ⟨42489332, by rfl⟩ : syracuseStep 56652443 = 84978665) B84978665
theorem B2947837 : Blo 362758 2947837 := bstep (se 3 (by rfl) ⟨552719, by rfl⟩ : syracuseStep 2947837 = 1105439) B1105439
theorem B2063261 : Blo 362758 2063261 := bstep (se 3 (by rfl) ⟨386861, by rfl⟩ : syracuseStep 2063261 = 773723) B773723
theorem B491113 : Blo 362758 491113 := bstep (se 2 (by rfl) ⟨184167, by rfl⟩ : syracuseStep 491113 = 368335) B368335
theorem B1016545 : Blo 362758 1016545 := bstep (se 2 (by rfl) ⟨381204, by rfl⟩ : syracuseStep 1016545 = 762409) B762409
theorem B363503 : Blo 362758 363503 := bstep (se 1 (by rfl) ⟨272627, by rfl⟩ : syracuseStep 363503 = 545255) B545255
theorem B495497 : Blo 362758 495497 := bstep (se 2 (by rfl) ⟨185811, by rfl⟩ : syracuseStep 495497 = 371623) B371623
theorem B60461801 : Blo 362758 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B695071 : Blo 362758 695071 := bstep (se 1 (by rfl) ⟨521303, by rfl⟩ : syracuseStep 695071 = 1042607) B1042607
theorem B4660361 : Blo 362758 4660361 := bstep (se 2 (by rfl) ⟨1747635, by rfl⟩ : syracuseStep 4660361 = 3495271) B3495271
theorem B1318139 : Blo 362758 1318139 := bstep (se 1 (by rfl) ⟨988604, by rfl⟩ : syracuseStep 1318139 = 1977209) B1977209
theorem B4694395 : Blo 362758 4694395 := bstep (se 1 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 4694395 = 7041593) B7041593
theorem B4504535 : Blo 362758 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B1981817 : Blo 362758 1981817 := bstep (se 2 (by rfl) ⟨743181, by rfl⟩ : syracuseStep 1981817 = 1486363) B1486363
theorem B1851983 : Blo 362758 1851983 := bstep (se 1 (by rfl) ⟨1388987, by rfl⟩ : syracuseStep 1851983 = 2777975) B2777975
theorem B2081659 : Blo 362758 2081659 := bstep (se 1 (by rfl) ⟨1561244, by rfl⟩ : syracuseStep 2081659 = 3122489) B3122489
theorem B7227001 : Blo 362758 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B37768295 : Blo 362758 37768295 := bstep (se 1 (by rfl) ⟨28326221, by rfl⟩ : syracuseStep 37768295 = 56652443) B56652443
theorem B1757153 : Blo 362758 1757153 := bstep (se 2 (by rfl) ⟨658932, by rfl⟩ : syracuseStep 1757153 = 1317865) B1317865
theorem B3723641 : Blo 362758 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B616079 : Blo 362758 616079 := bstep (se 1 (by rfl) ⟨462059, by rfl⟩ : syracuseStep 616079 = 924119) B924119
theorem B1111279 : Blo 362758 1111279 := bstep (se 1 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 1111279 = 1666919) B1666919
theorem B3930449 : Blo 362758 3930449 := bstep (se 2 (by rfl) ⟨1473918, by rfl⟩ : syracuseStep 3930449 = 2947837) B2947837
theorem B1375507 : Blo 362758 1375507 := bstep (se 1 (by rfl) ⟨1031630, by rfl⟩ : syracuseStep 1375507 = 2063261) B2063261
theorem B654817 : Blo 362758 654817 := bstep (se 2 (by rfl) ⟨245556, by rfl⟩ : syracuseStep 654817 = 491113) B491113
theorem B4816435 : Blo 362758 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B6259193 : Blo 362758 6259193 := bstep (se 2 (by rfl) ⟨2347197, by rfl⟩ : syracuseStep 6259193 = 4694395) B4694395
theorem B40307867 : Blo 362758 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B1481705 : Blo 362758 1481705 := bstep (se 2 (by rfl) ⟨555639, by rfl⟩ : syracuseStep 1481705 = 1111279) B1111279
theorem B38544005 : Blo 362758 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B926761 : Blo 362758 926761 := bstep (se 2 (by rfl) ⟨347535, by rfl⟩ : syracuseStep 926761 = 695071) B695071
theorem B1321211 : Blo 362758 1321211 := bstep (se 1 (by rfl) ⟨990908, by rfl⟩ : syracuseStep 1321211 = 1981817) B1981817
theorem B1321325 : Blo 362758 1321325 := bstep (se 3 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 1321325 = 495497) B495497
theorem B1355393 : Blo 362758 1355393 := bstep (se 2 (by rfl) ⟨508272, by rfl⟩ : syracuseStep 1355393 = 1016545) B1016545
theorem B25178863 : Blo 362758 25178863 := bstep (se 1 (by rfl) ⟨18884147, by rfl⟩ : syracuseStep 25178863 = 37768295) B37768295
theorem B410719 : Blo 362758 410719 := bstep (se 1 (by rfl) ⟨308039, by rfl⟩ : syracuseStep 410719 = 616079) B616079
theorem B873089 : Blo 362758 873089 := bstep (se 2 (by rfl) ⟨327408, by rfl⟩ : syracuseStep 873089 = 654817) B654817
theorem B3003023 : Blo 362758 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B1234655 : Blo 362758 1234655 := bstep (se 1 (by rfl) ⟨925991, by rfl⟩ : syracuseStep 1234655 = 1851983) B1851983
theorem B2775545 : Blo 362758 2775545 := bstep (se 2 (by rfl) ⟨1040829, by rfl⟩ : syracuseStep 2775545 = 2081659) B2081659
theorem B1171435 : Blo 362758 1171435 := bstep (se 1 (by rfl) ⟨878576, by rfl⟩ : syracuseStep 1171435 = 1757153) B1757153
theorem B2482427 : Blo 362758 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B3106907 : Blo 362758 3106907 := bstep (se 1 (by rfl) ⟨2330180, by rfl⟩ : syracuseStep 3106907 = 4660361) B4660361
theorem B878759 : Blo 362758 878759 := bstep (se 1 (by rfl) ⟨659069, by rfl⟩ : syracuseStep 878759 = 1318139) B1318139
theorem B10481197 : Blo 362758 10481197 := bstep (se 3 (by rfl) ⟨1965224, by rfl⟩ : syracuseStep 10481197 = 3930449) B3930449
theorem B7336037 : Blo 362758 7336037 := bstep (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) B1375507
theorem B6421913 : Blo 362758 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B26871911 : Blo 362758 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B2002015 : Blo 362758 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B823103 : Blo 362758 823103 := bstep (se 1 (by rfl) ⟨617327, by rfl⟩ : syracuseStep 823103 = 1234655) B1234655
theorem B987803 : Blo 362758 987803 := bstep (se 1 (by rfl) ⟨740852, by rfl⟩ : syracuseStep 987803 = 1481705) B1481705
theorem B25696003 : Blo 362758 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B2071271 : Blo 362758 2071271 := bstep (se 1 (by rfl) ⟨1553453, by rfl⟩ : syracuseStep 2071271 = 3106907) B3106907
theorem B4890691 : Blo 362758 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B3614381 : Blo 362758 3614381 := bstep (se 3 (by rfl) ⟨677696, by rfl⟩ : syracuseStep 3614381 = 1355393) B1355393
theorem B4172795 : Blo 362758 4172795 := bstep (se 1 (by rfl) ⟨3129596, by rfl⟩ : syracuseStep 4172795 = 6259193) B6259193
theorem B1850363 : Blo 362758 1850363 := bstep (se 1 (by rfl) ⟨1387772, by rfl⟩ : syracuseStep 1850363 = 2775545) B2775545
theorem B13974929 : Blo 362758 13974929 := bstep (se 2 (by rfl) ⟨5240598, by rfl⟩ : syracuseStep 13974929 = 10481197) B10481197
theorem B1654951 : Blo 362758 1654951 := bstep (se 1 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 1654951 = 2482427) B2482427
theorem B33571817 : Blo 362758 33571817 := bstep (se 2 (by rfl) ⟨12589431, by rfl⟩ : syracuseStep 33571817 = 25178863) B25178863
theorem B4281275 : Blo 362758 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B1561913 : Blo 362758 1561913 := bstep (se 2 (by rfl) ⟨585717, by rfl⟩ : syracuseStep 1561913 = 1171435) B1171435
theorem B1235681 : Blo 362758 1235681 := bstep (se 2 (by rfl) ⟨463380, by rfl⟩ : syracuseStep 1235681 = 926761) B926761
theorem B547625 : Blo 362758 547625 := bstep (se 2 (by rfl) ⟨205359, by rfl⟩ : syracuseStep 547625 = 410719) B410719
theorem B582059 : Blo 362758 582059 := bstep (se 1 (by rfl) ⟨436544, by rfl⟩ : syracuseStep 582059 = 873089) B873089
theorem B585839 : Blo 362758 585839 := bstep (se 1 (by rfl) ⟨439379, by rfl⟩ : syracuseStep 585839 = 878759) B878759
theorem B880807 : Blo 362758 880807 := bstep (se 1 (by rfl) ⟨660605, by rfl⟩ : syracuseStep 880807 = 1321211) B1321211
theorem B880883 : Blo 362758 880883 := bstep (se 1 (by rfl) ⟨660662, by rfl⟩ : syracuseStep 880883 = 1321325) B1321325
theorem B26083685 : Blo 362758 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B22381211 : Blo 362758 22381211 := bstep (se 1 (by rfl) ⟨16785908, by rfl⟩ : syracuseStep 22381211 = 33571817) B33571817
theorem B658535 : Blo 362758 658535 := bstep (se 1 (by rfl) ⟨493901, by rfl⟩ : syracuseStep 658535 = 987803) B987803
theorem B823787 : Blo 362758 823787 := bstep (se 1 (by rfl) ⟨617840, by rfl⟩ : syracuseStep 823787 = 1235681) B1235681
theorem B1380847 : Blo 362758 1380847 := bstep (se 1 (by rfl) ⟨1035635, by rfl⟩ : syracuseStep 1380847 = 2071271) B2071271
theorem B365083 : Blo 362758 365083 := bstep (se 1 (by rfl) ⟨273812, by rfl⟩ : syracuseStep 365083 = 547625) B547625
theorem B9316619 : Blo 362758 9316619 := bstep (se 1 (by rfl) ⟨6987464, by rfl⟩ : syracuseStep 9316619 = 13974929) B13974929
theorem B2206601 : Blo 362758 2206601 := bstep (se 2 (by rfl) ⟨827475, by rfl⟩ : syracuseStep 2206601 = 1654951) B1654951
theorem B11416733 : Blo 362758 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B2409587 : Blo 362758 2409587 := bstep (se 1 (by rfl) ⟨1807190, by rfl⟩ : syracuseStep 2409587 = 3614381) B3614381
theorem B34261337 : Blo 362758 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B1233575 : Blo 362758 1233575 := bstep (se 1 (by rfl) ⟨925181, by rfl⟩ : syracuseStep 1233575 = 1850363) B1850363
theorem B1562237 : Blo 362758 1562237 := bstep (se 3 (by rfl) ⟨292919, by rfl⟩ : syracuseStep 1562237 = 585839) B585839
theorem B17914607 : Blo 362758 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B548735 : Blo 362758 548735 := bstep (se 1 (by rfl) ⟨411551, by rfl⟩ : syracuseStep 548735 = 823103) B823103
theorem B1041275 : Blo 362758 1041275 := bstep (se 1 (by rfl) ⟨780956, by rfl⟩ : syracuseStep 1041275 = 1561913) B1561913
theorem B1174409 : Blo 362758 1174409 := bstep (se 2 (by rfl) ⟨440403, by rfl⟩ : syracuseStep 1174409 = 880807) B880807
theorem B388039 : Blo 362758 388039 := bstep (se 1 (by rfl) ⟨291029, by rfl⟩ : syracuseStep 388039 = 582059) B582059
theorem B10677413 : Blo 362758 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B2781863 : Blo 362758 2781863 := bstep (se 1 (by rfl) ⟨2086397, by rfl⟩ : syracuseStep 2781863 = 4172795) B4172795
theorem B587255 : Blo 362758 587255 := bstep (se 1 (by rfl) ⟨440441, by rfl⟩ : syracuseStep 587255 = 880883) B880883
theorem B1606391 : Blo 362758 1606391 := bstep (se 1 (by rfl) ⟨1204793, by rfl⟩ : syracuseStep 1606391 = 2409587) B2409587
theorem B822383 : Blo 362758 822383 := bstep (se 1 (by rfl) ⟨616787, by rfl⟩ : syracuseStep 822383 = 1233575) B1233575
theorem B365823 : Blo 362758 365823 := bstep (se 1 (by rfl) ⟨274367, by rfl⟩ : syracuseStep 365823 = 548735) B548735
theorem B694183 : Blo 362758 694183 := bstep (se 1 (by rfl) ⟨520637, by rfl⟩ : syracuseStep 694183 = 1041275) B1041275
theorem B1841129 : Blo 362758 1841129 := bstep (se 2 (by rfl) ⟨690423, by rfl⟩ : syracuseStep 1841129 = 1380847) B1380847
theorem B91363565 : Blo 362758 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B7118275 : Blo 362758 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B7611155 : Blo 362758 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B14920807 : Blo 362758 14920807 := bstep (se 1 (by rfl) ⟨11190605, by rfl⟩ : syracuseStep 14920807 = 22381211) B22381211
theorem B11943071 : Blo 362758 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B6211079 : Blo 362758 6211079 := bstep (se 1 (by rfl) ⟨4658309, by rfl⟩ : syracuseStep 6211079 = 9316619) B9316619
theorem B1756093 : Blo 362758 1756093 := bstep (se 3 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 1756093 = 658535) B658535
theorem B1854575 : Blo 362758 1854575 := bstep (se 1 (by rfl) ⟨1390931, by rfl⟩ : syracuseStep 1854575 = 2781863) B2781863
theorem B69556493 : Blo 362758 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B549191 : Blo 362758 549191 := bstep (se 1 (by rfl) ⟨411893, by rfl⟩ : syracuseStep 549191 = 823787) B823787
theorem B1041491 : Blo 362758 1041491 := bstep (se 1 (by rfl) ⟨781118, by rfl⟩ : syracuseStep 1041491 = 1562237) B1562237
theorem B517385 : Blo 362758 517385 := bstep (se 2 (by rfl) ⟨194019, by rfl⟩ : syracuseStep 517385 = 388039) B388039
theorem B1566013 : Blo 362758 1566013 := bstep (se 3 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 1566013 = 587255) B587255
theorem B1471067 : Blo 362758 1471067 := bstep (se 1 (by rfl) ⟨1103300, by rfl⟩ : syracuseStep 1471067 = 2206601) B2206601
theorem B782939 : Blo 362758 782939 := bstep (se 1 (by rfl) ⟨587204, by rfl⟩ : syracuseStep 782939 = 1174409) B1174409
theorem B1379693 : Blo 362758 1379693 := bstep (se 3 (by rfl) ⟨258692, by rfl⟩ : syracuseStep 1379693 = 517385) B517385
theorem B19894409 : Blo 362758 19894409 := bstep (se 2 (by rfl) ⟨7460403, by rfl⟩ : syracuseStep 19894409 = 14920807) B14920807
theorem B366127 : Blo 362758 366127 := bstep (se 1 (by rfl) ⟨274595, by rfl⟩ : syracuseStep 366127 = 549191) B549191
theorem B694327 : Blo 362758 694327 := bstep (se 1 (by rfl) ⟨520745, by rfl⟩ : syracuseStep 694327 = 1041491) B1041491
theorem B925577 : Blo 362758 925577 := bstep (se 2 (by rfl) ⟨347091, by rfl⟩ : syracuseStep 925577 = 694183) B694183
theorem B4140719 : Blo 362758 4140719 := bstep (se 1 (by rfl) ⟨3105539, by rfl⟩ : syracuseStep 4140719 = 6211079) B6211079
theorem B2341457 : Blo 362758 2341457 := bstep (se 2 (by rfl) ⟨878046, by rfl⟩ : syracuseStep 2341457 = 1756093) B1756093
theorem B1227419 : Blo 362758 1227419 := bstep (se 1 (by rfl) ⟨920564, by rfl⟩ : syracuseStep 1227419 = 1841129) B1841129
theorem B185483981 : Blo 362758 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B9491033 : Blo 362758 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B1070927 : Blo 362758 1070927 := bstep (se 1 (by rfl) ⟨803195, by rfl⟩ : syracuseStep 1070927 = 1606391) B1606391
theorem B2088017 : Blo 362758 2088017 := bstep (se 2 (by rfl) ⟨783006, by rfl⟩ : syracuseStep 2088017 = 1566013) B1566013
theorem B548255 : Blo 362758 548255 := bstep (se 1 (by rfl) ⟨411191, by rfl⟩ : syracuseStep 548255 = 822383) B822383
theorem B1236383 : Blo 362758 1236383 := bstep (se 1 (by rfl) ⟨927287, by rfl⟩ : syracuseStep 1236383 = 1854575) B1854575
theorem B60909043 : Blo 362758 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B5074103 : Blo 362758 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B980711 : Blo 362758 980711 := bstep (se 1 (by rfl) ⟨735533, by rfl⟩ : syracuseStep 980711 = 1471067) B1471067
theorem B521959 : Blo 362758 521959 := bstep (se 1 (by rfl) ⟨391469, by rfl⟩ : syracuseStep 521959 = 782939) B782939
theorem B7962047 : Blo 362758 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B919795 : Blo 362758 919795 := bstep (se 1 (by rfl) ⟨689846, by rfl⟩ : syracuseStep 919795 = 1379693) B1379693
theorem B365503 : Blo 362758 365503 := bstep (se 1 (by rfl) ⟨274127, by rfl⟩ : syracuseStep 365503 = 548255) B548255
theorem B824255 : Blo 362758 824255 := bstep (se 1 (by rfl) ⟨618191, by rfl⟩ : syracuseStep 824255 = 1236383) B1236383
theorem B3382735 : Blo 362758 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B695945 : Blo 362758 695945 := bstep (se 2 (by rfl) ⟨260979, by rfl⟩ : syracuseStep 695945 = 521959) B521959
theorem B2760479 : Blo 362758 2760479 := bstep (se 1 (by rfl) ⟨2070359, by rfl⟩ : syracuseStep 2760479 = 4140719) B4140719
theorem B925769 : Blo 362758 925769 := bstep (se 2 (by rfl) ⟨347163, by rfl⟩ : syracuseStep 925769 = 694327) B694327
theorem B25309421 : Blo 362758 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B81212057 : Blo 362758 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B1392011 : Blo 362758 1392011 := bstep (se 1 (by rfl) ⟨1044008, by rfl⟩ : syracuseStep 1392011 = 2088017) B2088017
theorem B1560971 : Blo 362758 1560971 := bstep (se 1 (by rfl) ⟨1170728, by rfl⟩ : syracuseStep 1560971 = 2341457) B2341457
theorem B123655987 : Blo 362758 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B13262939 : Blo 362758 13262939 := bstep (se 1 (by rfl) ⟨9947204, by rfl⟩ : syracuseStep 13262939 = 19894409) B19894409
theorem B713951 : Blo 362758 713951 := bstep (se 1 (by rfl) ⟨535463, by rfl⟩ : syracuseStep 713951 = 1070927) B1070927
theorem B617051 : Blo 362758 617051 := bstep (se 1 (by rfl) ⟨462788, by rfl⟩ : syracuseStep 617051 = 925577) B925577
theorem B653807 : Blo 362758 653807 := bstep (se 1 (by rfl) ⟨490355, by rfl⟩ : syracuseStep 653807 = 980711) B980711
theorem B818279 : Blo 362758 818279 := bstep (se 1 (by rfl) ⟨613709, by rfl⟩ : syracuseStep 818279 = 1227419) B1227419
theorem B5308031 : Blo 362758 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B4162589 : Blo 362758 4162589 := bstep (se 3 (by rfl) ⟨780485, by rfl⟩ : syracuseStep 4162589 = 1560971) B1560971
theorem B463963 : Blo 362758 463963 := bstep (se 1 (by rfl) ⟨347972, by rfl⟩ : syracuseStep 463963 = 695945) B695945
theorem B1840319 : Blo 362758 1840319 := bstep (se 1 (by rfl) ⟨1380239, by rfl⟩ : syracuseStep 1840319 = 2760479) B2760479
theorem B54141371 : Blo 362758 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B435871 : Blo 362758 435871 := bstep (se 1 (by rfl) ⟨326903, by rfl⟩ : syracuseStep 435871 = 653807) B653807
theorem B928007 : Blo 362758 928007 := bstep (se 1 (by rfl) ⟨696005, by rfl⟩ : syracuseStep 928007 = 1392011) B1392011
theorem B1226393 : Blo 362758 1226393 := bstep (se 2 (by rfl) ⟨459897, by rfl⟩ : syracuseStep 1226393 = 919795) B919795
theorem B475967 : Blo 362758 475967 := bstep (se 1 (by rfl) ⟨356975, by rfl⟩ : syracuseStep 475967 = 713951) B713951
theorem B411367 : Blo 362758 411367 := bstep (se 1 (by rfl) ⟨308525, by rfl⟩ : syracuseStep 411367 = 617051) B617051
theorem B164874649 : Blo 362758 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B4510313 : Blo 362758 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B545519 : Blo 362758 545519 := bstep (se 1 (by rfl) ⟨409139, by rfl⟩ : syracuseStep 545519 = 818279) B818279
theorem B549503 : Blo 362758 549503 := bstep (se 1 (by rfl) ⟨412127, by rfl⟩ : syracuseStep 549503 = 824255) B824255
theorem B617179 : Blo 362758 617179 := bstep (se 1 (by rfl) ⟨462884, by rfl⟩ : syracuseStep 617179 = 925769) B925769
theorem B8841959 : Blo 362758 8841959 := bstep (se 1 (by rfl) ⟨6631469, by rfl⟩ : syracuseStep 8841959 = 13262939) B13262939
theorem B16872947 : Blo 362758 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B3538687 : Blo 362758 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B363679 : Blo 362758 363679 := bstep (se 1 (by rfl) ⟨272759, by rfl⟩ : syracuseStep 363679 = 545519) B545519
theorem B822905 : Blo 362758 822905 := bstep (se 2 (by rfl) ⟨308589, by rfl⟩ : syracuseStep 822905 = 617179) B617179
theorem B366335 : Blo 362758 366335 := bstep (se 1 (by rfl) ⟨274751, by rfl⟩ : syracuseStep 366335 = 549503) B549503
theorem B11248631 : Blo 362758 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B1226879 : Blo 362758 1226879 := bstep (se 1 (by rfl) ⟨920159, by rfl⟩ : syracuseStep 1226879 = 1840319) B1840319
theorem B36094247 : Blo 362758 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B2775059 : Blo 362758 2775059 := bstep (se 1 (by rfl) ⟨2081294, by rfl⟩ : syracuseStep 2775059 = 4162589) B4162589
theorem B1269245 : Blo 362758 1269245 := bstep (se 3 (by rfl) ⟨237983, by rfl⟩ : syracuseStep 1269245 = 475967) B475967
theorem B548489 : Blo 362758 548489 := bstep (se 2 (by rfl) ⟨205683, by rfl⟩ : syracuseStep 548489 = 411367) B411367
theorem B3006875 : Blo 362758 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B219832865 : Blo 362758 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B618617 : Blo 362758 618617 := bstep (se 2 (by rfl) ⟨231981, by rfl⟩ : syracuseStep 618617 = 463963) B463963
theorem B618671 : Blo 362758 618671 := bstep (se 1 (by rfl) ⟨464003, by rfl⟩ : syracuseStep 618671 = 928007) B928007
theorem B5894639 : Blo 362758 5894639 := bstep (se 1 (by rfl) ⟨4420979, by rfl⟩ : syracuseStep 5894639 = 8841959) B8841959
theorem B2324645 : Blo 362758 2324645 := bstep (se 4 (by rfl) ⟨217935, by rfl⟩ : syracuseStep 2324645 = 435871) B435871
theorem B817595 : Blo 362758 817595 := bstep (se 1 (by rfl) ⟨613196, by rfl⟩ : syracuseStep 817595 = 1226393) B1226393
theorem B4718249 : Blo 362758 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B365659 : Blo 362758 365659 := bstep (se 1 (by rfl) ⟨274244, by rfl⟩ : syracuseStep 365659 = 548489) B548489
theorem B2004583 : Blo 362758 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B1549763 : Blo 362758 1549763 := bstep (se 1 (by rfl) ⟨1162322, by rfl⟩ : syracuseStep 1549763 = 2324645) B2324645
theorem B24062831 : Blo 362758 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B1850039 : Blo 362758 1850039 := bstep (se 1 (by rfl) ⟨1387529, by rfl⟩ : syracuseStep 1850039 = 2775059) B2775059
theorem B146555243 : Blo 362758 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B412411 : Blo 362758 412411 := bstep (se 1 (by rfl) ⟨309308, by rfl⟩ : syracuseStep 412411 = 618617) B618617
theorem B412447 : Blo 362758 412447 := bstep (se 1 (by rfl) ⟨309335, by rfl⟩ : syracuseStep 412447 = 618671) B618671
theorem B545063 : Blo 362758 545063 := bstep (se 1 (by rfl) ⟨408797, by rfl⟩ : syracuseStep 545063 = 817595) B817595
theorem B548603 : Blo 362758 548603 := bstep (se 1 (by rfl) ⟨411452, by rfl⟩ : syracuseStep 548603 = 822905) B822905
theorem B846163 : Blo 362758 846163 := bstep (se 1 (by rfl) ⟨634622, by rfl⟩ : syracuseStep 846163 = 1269245) B1269245
theorem B7499087 : Blo 362758 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B3929759 : Blo 362758 3929759 := bstep (se 1 (by rfl) ⟨2947319, by rfl⟩ : syracuseStep 3929759 = 5894639) B5894639
theorem B817919 : Blo 362758 817919 := bstep (se 1 (by rfl) ⟨613439, by rfl⟩ : syracuseStep 817919 = 1226879) B1226879
theorem B3145499 : Blo 362758 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B363375 : Blo 362758 363375 := bstep (se 1 (by rfl) ⟨272531, by rfl⟩ : syracuseStep 363375 = 545063) B545063
theorem B365735 : Blo 362758 365735 := bstep (se 1 (by rfl) ⟨274301, by rfl⟩ : syracuseStep 365735 = 548603) B548603
theorem B1128217 : Blo 362758 1128217 := bstep (se 2 (by rfl) ⟨423081, by rfl⟩ : syracuseStep 1128217 = 846163) B846163
theorem B1033175 : Blo 362758 1033175 := bstep (se 1 (by rfl) ⟨774881, by rfl⟩ : syracuseStep 1033175 = 1549763) B1549763
theorem B16041887 : Blo 362758 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B2672777 : Blo 362758 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B4999391 : Blo 362758 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B1233359 : Blo 362758 1233359 := bstep (se 1 (by rfl) ⟨925019, by rfl⟩ : syracuseStep 1233359 = 1850039) B1850039
theorem B545279 : Blo 362758 545279 := bstep (se 1 (by rfl) ⟨408959, by rfl⟩ : syracuseStep 545279 = 817919) B817919
theorem B97703495 : Blo 362758 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B549881 : Blo 362758 549881 := bstep (se 2 (by rfl) ⟨206205, by rfl⟩ : syracuseStep 549881 = 412411) B412411
theorem B549929 : Blo 362758 549929 := bstep (se 2 (by rfl) ⟨206223, by rfl⟩ : syracuseStep 549929 = 412447) B412447
theorem B2619839 : Blo 362758 2619839 := bstep (se 1 (by rfl) ⟨1964879, by rfl⟩ : syracuseStep 2619839 = 3929759) B3929759
theorem B2096999 : Blo 362758 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B2755133 : Blo 362758 2755133 := bstep (se 3 (by rfl) ⟨516587, by rfl⟩ : syracuseStep 2755133 = 1033175) B1033175
theorem B822239 : Blo 362758 822239 := bstep (se 1 (by rfl) ⟨616679, by rfl⟩ : syracuseStep 822239 = 1233359) B1233359
theorem B363519 : Blo 362758 363519 := bstep (se 1 (by rfl) ⟨272639, by rfl⟩ : syracuseStep 363519 = 545279) B545279
theorem B366587 : Blo 362758 366587 := bstep (se 1 (by rfl) ⟨274940, by rfl⟩ : syracuseStep 366587 = 549881) B549881
theorem B366619 : Blo 362758 366619 := bstep (se 1 (by rfl) ⟨274964, by rfl⟩ : syracuseStep 366619 = 549929) B549929
theorem B1746559 : Blo 362758 1746559 := bstep (se 1 (by rfl) ⟨1309919, by rfl⟩ : syracuseStep 1746559 = 2619839) B2619839
theorem B10694591 : Blo 362758 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B1781851 : Blo 362758 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B1397999 : Blo 362758 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B3332927 : Blo 362758 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B65135663 : Blo 362758 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B1504289 : Blo 362758 1504289 := bstep (se 2 (by rfl) ⟨564108, by rfl⟩ : syracuseStep 1504289 = 1128217) B1128217
theorem B1836755 : Blo 362758 1836755 := bstep (se 1 (by rfl) ⟨1377566, by rfl⟩ : syracuseStep 1836755 = 2755133) B2755133
theorem B2328745 : Blo 362758 2328745 := bstep (se 2 (by rfl) ⟨873279, by rfl⟩ : syracuseStep 2328745 = 1746559) B1746559
theorem B43423775 : Blo 362758 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B4011437 : Blo 362758 4011437 := bstep (se 3 (by rfl) ⟨752144, by rfl⟩ : syracuseStep 4011437 = 1504289) B1504289
theorem B931999 : Blo 362758 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B2375801 : Blo 362758 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B7129727 : Blo 362758 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B548159 : Blo 362758 548159 := bstep (se 1 (by rfl) ⟨411119, by rfl⟩ : syracuseStep 548159 = 822239) B822239
theorem B2221951 : Blo 362758 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B4753151 : Blo 362758 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B365439 : Blo 362758 365439 := bstep (se 1 (by rfl) ⟨274079, by rfl⟩ : syracuseStep 365439 = 548159) B548159
theorem B1583867 : Blo 362758 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B1224503 : Blo 362758 1224503 := bstep (se 1 (by rfl) ⟨918377, by rfl⟩ : syracuseStep 1224503 = 1836755) B1836755
theorem B2962601 : Blo 362758 2962601 := bstep (se 2 (by rfl) ⟨1110975, by rfl⟩ : syracuseStep 2962601 = 2221951) B2221951
theorem B28949183 : Blo 362758 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B2674291 : Blo 362758 2674291 := bstep (se 1 (by rfl) ⟨2005718, by rfl⟩ : syracuseStep 2674291 = 4011437) B4011437
theorem B3104993 : Blo 362758 3104993 := bstep (se 2 (by rfl) ⟨1164372, by rfl⟩ : syracuseStep 3104993 = 2328745) B2328745
theorem B1242665 : Blo 362758 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B2069995 : Blo 362758 2069995 := bstep (se 1 (by rfl) ⟨1552496, by rfl⟩ : syracuseStep 2069995 = 3104993) B3104993
theorem B1055911 : Blo 362758 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B1975067 : Blo 362758 1975067 := bstep (se 1 (by rfl) ⟨1481300, by rfl⟩ : syracuseStep 1975067 = 2962601) B2962601
theorem B828443 : Blo 362758 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B3168767 : Blo 362758 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B3565721 : Blo 362758 3565721 := bstep (se 2 (by rfl) ⟨1337145, by rfl⟩ : syracuseStep 3565721 = 2674291) B2674291
theorem B816335 : Blo 362758 816335 := bstep (se 1 (by rfl) ⟨612251, by rfl⟩ : syracuseStep 816335 = 1224503) B1224503
theorem B19299455 : Blo 362758 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B1316711 : Blo 362758 1316711 := bstep (se 1 (by rfl) ⟨987533, by rfl⟩ : syracuseStep 1316711 = 1975067) B1975067
theorem B2759993 : Blo 362758 2759993 := bstep (se 2 (by rfl) ⟨1034997, by rfl⟩ : syracuseStep 2759993 = 2069995) B2069995
theorem B2377147 : Blo 362758 2377147 := bstep (se 1 (by rfl) ⟨1782860, by rfl⟩ : syracuseStep 2377147 = 3565721) B3565721
theorem B544223 : Blo 362758 544223 := bstep (se 1 (by rfl) ⟨408167, by rfl⟩ : syracuseStep 544223 = 816335) B816335
theorem B12866303 : Blo 362758 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B552295 : Blo 362758 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B8450045 : Blo 362758 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B1407881 : Blo 362758 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B362815 : Blo 362758 362815 := bstep (se 1 (by rfl) ⟨272111, by rfl⟩ : syracuseStep 362815 = 544223) B544223
theorem B1839995 : Blo 362758 1839995 := bstep (se 1 (by rfl) ⟨1379996, by rfl⟩ : syracuseStep 1839995 = 2759993) B2759993
theorem B736393 : Blo 362758 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B938587 : Blo 362758 938587 := bstep (se 1 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 938587 = 1407881) B1407881
theorem B3169529 : Blo 362758 3169529 := bstep (se 2 (by rfl) ⟨1188573, by rfl⟩ : syracuseStep 3169529 = 2377147) B2377147
theorem B8577535 : Blo 362758 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B877807 : Blo 362758 877807 := bstep (se 1 (by rfl) ⟨658355, by rfl⟩ : syracuseStep 877807 = 1316711) B1316711
theorem B5633363 : Blo 362758 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B11436713 : Blo 362758 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B1251449 : Blo 362758 1251449 := bstep (se 2 (by rfl) ⟨469293, by rfl⟩ : syracuseStep 1251449 = 938587) B938587
theorem B1226663 : Blo 362758 1226663 := bstep (se 1 (by rfl) ⟨919997, by rfl⟩ : syracuseStep 1226663 = 1839995) B1839995
theorem B2113019 : Blo 362758 2113019 := bstep (se 1 (by rfl) ⟨1584764, by rfl⟩ : syracuseStep 2113019 = 3169529) B3169529
theorem B3755575 : Blo 362758 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B4681637 : Blo 362758 4681637 := bstep (se 4 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 4681637 = 877807) B877807
theorem B981857 : Blo 362758 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B3121091 : Blo 362758 3121091 := bstep (se 1 (by rfl) ⟨2340818, by rfl⟩ : syracuseStep 3121091 = 4681637) B4681637
theorem B834299 : Blo 362758 834299 := bstep (se 1 (by rfl) ⟨625724, by rfl⟩ : syracuseStep 834299 = 1251449) B1251449
theorem B7624475 : Blo 362758 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B5007433 : Blo 362758 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B817775 : Blo 362758 817775 := bstep (se 1 (by rfl) ⟨613331, by rfl⟩ : syracuseStep 817775 = 1226663) B1226663
theorem B654571 : Blo 362758 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B1408679 : Blo 362758 1408679 := bstep (se 1 (by rfl) ⟨1056509, by rfl⟩ : syracuseStep 1408679 = 2113019) B2113019
theorem B5082983 : Blo 362758 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B2080727 : Blo 362758 2080727 := bstep (se 1 (by rfl) ⟨1560545, by rfl⟩ : syracuseStep 2080727 = 3121091) B3121091
theorem B3491045 : Blo 362758 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B545183 : Blo 362758 545183 := bstep (se 1 (by rfl) ⟨408887, by rfl⟩ : syracuseStep 545183 = 817775) B817775
theorem B939119 : Blo 362758 939119 := bstep (se 1 (by rfl) ⟨704339, by rfl⟩ : syracuseStep 939119 = 1408679) B1408679
theorem B6676577 : Blo 362758 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B556199 : Blo 362758 556199 := bstep (se 1 (by rfl) ⟨417149, by rfl⟩ : syracuseStep 556199 = 834299) B834299
theorem B2327363 : Blo 362758 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B363455 : Blo 362758 363455 := bstep (se 1 (by rfl) ⟨272591, by rfl⟩ : syracuseStep 363455 = 545183) B545183
theorem B370799 : Blo 362758 370799 := bstep (se 1 (by rfl) ⟨278099, by rfl⟩ : syracuseStep 370799 = 556199) B556199
theorem B1387151 : Blo 362758 1387151 := bstep (se 1 (by rfl) ⟨1040363, by rfl⟩ : syracuseStep 1387151 = 2080727) B2080727
theorem B3388655 : Blo 362758 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B2504317 : Blo 362758 2504317 := bstep (se 3 (by rfl) ⟨469559, by rfl⟩ : syracuseStep 2504317 = 939119) B939119
theorem B4451051 : Blo 362758 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B924767 : Blo 362758 924767 := bstep (se 1 (by rfl) ⟨693575, by rfl⟩ : syracuseStep 924767 = 1387151) B1387151
theorem B1551575 : Blo 362758 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B2967367 : Blo 362758 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B15820757 : Blo 362758 15820757 := bstep (se 7 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 15820757 = 370799) B370799
theorem B3339089 : Blo 362758 3339089 := bstep (se 2 (by rfl) ⟨1252158, by rfl⟩ : syracuseStep 3339089 = 2504317) B2504317
theorem B2259103 : Blo 362758 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B1034383 : Blo 362758 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B3956489 : Blo 362758 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B616511 : Blo 362758 616511 := bstep (se 1 (by rfl) ⟨462383, by rfl⟩ : syracuseStep 616511 = 924767) B924767
theorem B10547171 : Blo 362758 10547171 := bstep (se 1 (by rfl) ⟨7910378, by rfl⟩ : syracuseStep 10547171 = 15820757) B15820757
theorem B3012137 : Blo 362758 3012137 := bstep (se 2 (by rfl) ⟨1129551, by rfl⟩ : syracuseStep 3012137 = 2259103) B2259103
theorem B2226059 : Blo 362758 2226059 := bstep (se 1 (by rfl) ⟨1669544, by rfl⟩ : syracuseStep 2226059 = 3339089) B3339089
theorem B1379177 : Blo 362758 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B2008091 : Blo 362758 2008091 := bstep (se 1 (by rfl) ⟨1506068, by rfl⟩ : syracuseStep 2008091 = 3012137) B3012137
theorem B1484039 : Blo 362758 1484039 := bstep (se 1 (by rfl) ⟨1113029, by rfl⟩ : syracuseStep 1484039 = 2226059) B2226059
theorem B2637659 : Blo 362758 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B411007 : Blo 362758 411007 := bstep (se 1 (by rfl) ⟨308255, by rfl⟩ : syracuseStep 411007 = 616511) B616511
theorem B7031447 : Blo 362758 7031447 := bstep (se 1 (by rfl) ⟨5273585, by rfl⟩ : syracuseStep 7031447 = 10547171) B10547171
theorem B4687631 : Blo 362758 4687631 := bstep (se 1 (by rfl) ⟨3515723, by rfl⟩ : syracuseStep 4687631 = 7031447) B7031447
theorem B919451 : Blo 362758 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B1758439 : Blo 362758 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B548009 : Blo 362758 548009 := bstep (se 2 (by rfl) ⟨205503, by rfl⟩ : syracuseStep 548009 = 411007) B411007
theorem B3957437 : Blo 362758 3957437 := bstep (se 3 (by rfl) ⟨742019, by rfl⟩ : syracuseStep 3957437 = 1484039) B1484039
theorem B1338727 : Blo 362758 1338727 := bstep (se 1 (by rfl) ⟨1004045, by rfl⟩ : syracuseStep 1338727 = 2008091) B2008091
theorem B10553165 : Blo 362758 10553165 := bstep (se 3 (by rfl) ⟨1978718, by rfl⟩ : syracuseStep 10553165 = 3957437) B3957437
theorem B365339 : Blo 362758 365339 := bstep (se 1 (by rfl) ⟨274004, by rfl⟩ : syracuseStep 365339 = 548009) B548009
theorem B3125087 : Blo 362758 3125087 := bstep (se 1 (by rfl) ⟨2343815, by rfl⟩ : syracuseStep 3125087 = 4687631) B4687631
theorem B1784969 : Blo 362758 1784969 := bstep (se 2 (by rfl) ⟨669363, by rfl⟩ : syracuseStep 1784969 = 1338727) B1338727
theorem B2344585 : Blo 362758 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B612967 : Blo 362758 612967 := bstep (se 1 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 612967 = 919451) B919451
theorem B1189979 : Blo 362758 1189979 := bstep (se 1 (by rfl) ⟨892484, by rfl⟩ : syracuseStep 1189979 = 1784969) B1784969
theorem B3126113 : Blo 362758 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B2083391 : Blo 362758 2083391 := bstep (se 1 (by rfl) ⟨1562543, by rfl⟩ : syracuseStep 2083391 = 3125087) B3125087
theorem B7035443 : Blo 362758 7035443 := bstep (se 1 (by rfl) ⟨5276582, by rfl⟩ : syracuseStep 7035443 = 10553165) B10553165
theorem B817289 : Blo 362758 817289 := bstep (se 2 (by rfl) ⟨306483, by rfl⟩ : syracuseStep 817289 = 612967) B612967
theorem B4690295 : Blo 362758 4690295 := bstep (se 1 (by rfl) ⟨3517721, by rfl⟩ : syracuseStep 4690295 = 7035443) B7035443
theorem B793319 : Blo 362758 793319 := bstep (se 1 (by rfl) ⟨594989, by rfl⟩ : syracuseStep 793319 = 1189979) B1189979
theorem B1388927 : Blo 362758 1388927 := bstep (se 1 (by rfl) ⟨1041695, by rfl⟩ : syracuseStep 1388927 = 2083391) B2083391
theorem B2084075 : Blo 362758 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B544859 : Blo 362758 544859 := bstep (se 1 (by rfl) ⟨408644, by rfl⟩ : syracuseStep 544859 = 817289) B817289
theorem B363239 : Blo 362758 363239 := bstep (se 1 (by rfl) ⟨272429, by rfl⟩ : syracuseStep 363239 = 544859) B544859
theorem B925951 : Blo 362758 925951 := bstep (se 1 (by rfl) ⟨694463, by rfl⟩ : syracuseStep 925951 = 1388927) B1388927
theorem B1389383 : Blo 362758 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B3126863 : Blo 362758 3126863 := bstep (se 1 (by rfl) ⟨2345147, by rfl⟩ : syracuseStep 3126863 = 4690295) B4690295
theorem B2115517 : Blo 362758 2115517 := bstep (se 3 (by rfl) ⟨396659, by rfl⟩ : syracuseStep 2115517 = 793319) B793319
theorem B2820689 : Blo 362758 2820689 := bstep (se 2 (by rfl) ⟨1057758, by rfl⟩ : syracuseStep 2820689 = 2115517) B2115517
theorem B926255 : Blo 362758 926255 := bstep (se 1 (by rfl) ⟨694691, by rfl⟩ : syracuseStep 926255 = 1389383) B1389383
theorem B2084575 : Blo 362758 2084575 := bstep (se 1 (by rfl) ⟨1563431, by rfl⟩ : syracuseStep 2084575 = 3126863) B3126863
theorem B1234601 : Blo 362758 1234601 := bstep (se 2 (by rfl) ⟨462975, by rfl⟩ : syracuseStep 1234601 = 925951) B925951
theorem B823067 : Blo 362758 823067 := bstep (se 1 (by rfl) ⟨617300, by rfl⟩ : syracuseStep 823067 = 1234601) B1234601
theorem B1880459 : Blo 362758 1880459 := bstep (se 1 (by rfl) ⟨1410344, by rfl⟩ : syracuseStep 1880459 = 2820689) B2820689
theorem B2779433 : Blo 362758 2779433 := bstep (se 2 (by rfl) ⟨1042287, by rfl⟩ : syracuseStep 2779433 = 2084575) B2084575
theorem B617503 : Blo 362758 617503 := bstep (se 1 (by rfl) ⟨463127, by rfl⟩ : syracuseStep 617503 = 926255) B926255
theorem B823337 : Blo 362758 823337 := bstep (se 2 (by rfl) ⟨308751, by rfl⟩ : syracuseStep 823337 = 617503) B617503
theorem B1253639 : Blo 362758 1253639 := bstep (se 1 (by rfl) ⟨940229, by rfl⟩ : syracuseStep 1253639 = 1880459) B1880459
theorem B1852955 : Blo 362758 1852955 := bstep (se 1 (by rfl) ⟨1389716, by rfl⟩ : syracuseStep 1852955 = 2779433) B2779433
theorem B548711 : Blo 362758 548711 := bstep (se 1 (by rfl) ⟨411533, by rfl⟩ : syracuseStep 548711 = 823067) B823067
theorem B365807 : Blo 362758 365807 := bstep (se 1 (by rfl) ⟨274355, by rfl⟩ : syracuseStep 365807 = 548711) B548711
theorem B835759 : Blo 362758 835759 := bstep (se 1 (by rfl) ⟨626819, by rfl⟩ : syracuseStep 835759 = 1253639) B1253639
theorem B1235303 : Blo 362758 1235303 := bstep (se 1 (by rfl) ⟨926477, by rfl⟩ : syracuseStep 1235303 = 1852955) B1852955
theorem B548891 : Blo 362758 548891 := bstep (se 1 (by rfl) ⟨411668, by rfl⟩ : syracuseStep 548891 = 823337) B823337
theorem B1114345 : Blo 362758 1114345 := bstep (se 2 (by rfl) ⟨417879, by rfl⟩ : syracuseStep 1114345 = 835759) B835759
theorem B823535 : Blo 362758 823535 := bstep (se 1 (by rfl) ⟨617651, by rfl⟩ : syracuseStep 823535 = 1235303) B1235303
theorem B365927 : Blo 362758 365927 := bstep (se 1 (by rfl) ⟨274445, by rfl⟩ : syracuseStep 365927 = 548891) B548891
theorem B1485793 : Blo 362758 1485793 := bstep (se 2 (by rfl) ⟨557172, by rfl⟩ : syracuseStep 1485793 = 1114345) B1114345
theorem B549023 : Blo 362758 549023 := bstep (se 1 (by rfl) ⟨411767, by rfl⟩ : syracuseStep 549023 = 823535) B823535
theorem B366015 : Blo 362758 366015 := bstep (se 1 (by rfl) ⟨274511, by rfl⟩ : syracuseStep 366015 = 549023) B549023
theorem B1981057 : Blo 362758 1981057 := bstep (se 2 (by rfl) ⟨742896, by rfl⟩ : syracuseStep 1981057 = 1485793) B1485793
theorem B2641409 : Blo 362758 2641409 := bstep (se 2 (by rfl) ⟨990528, by rfl⟩ : syracuseStep 2641409 = 1981057) B1981057
theorem B1760939 : Blo 362758 1760939 := bstep (se 1 (by rfl) ⟨1320704, by rfl⟩ : syracuseStep 1760939 = 2641409) B2641409
theorem B1173959 : Blo 362758 1173959 := bstep (se 1 (by rfl) ⟨880469, by rfl⟩ : syracuseStep 1173959 = 1760939) B1760939
theorem B782639 : Blo 362758 782639 := bstep (se 1 (by rfl) ⟨586979, by rfl⟩ : syracuseStep 782639 = 1173959) B1173959
theorem B521759 : Blo 362758 521759 := bstep (se 1 (by rfl) ⟨391319, by rfl⟩ : syracuseStep 521759 = 782639) B782639
theorem B1391357 : Blo 362758 1391357 := bstep (se 3 (by rfl) ⟨260879, by rfl⟩ : syracuseStep 1391357 = 521759) B521759
theorem B927571 : Blo 362758 927571 := bstep (se 1 (by rfl) ⟨695678, by rfl⟩ : syracuseStep 927571 = 1391357) B1391357
theorem B1236761 : Blo 362758 1236761 := bstep (se 2 (by rfl) ⟨463785, by rfl⟩ : syracuseStep 1236761 = 927571) B927571
theorem B824507 : Blo 362758 824507 := bstep (se 1 (by rfl) ⟨618380, by rfl⟩ : syracuseStep 824507 = 1236761) B1236761
theorem B549671 : Blo 362758 549671 := bstep (se 1 (by rfl) ⟨412253, by rfl⟩ : syracuseStep 549671 = 824507) B824507
theorem B366447 : Blo 362758 366447 := bstep (se 1 (by rfl) ⟨274835, by rfl⟩ : syracuseStep 366447 = 549671) B549671

theorem C0 (j : ℕ) (h1 : 90689 ≤ j) (h2 : j ≤ 91388) : Blo 362758 (4 * j + 3) := by
  interval_cases j
  · exact B362759
  · exact B362763
  · exact B362767
  · exact B362771
  · exact B362775
  · exact B362779
  · exact B362783
  · exact B362787
  · exact B362791
  · exact B362795
  · exact B362799
  · exact B362803
  · exact B362807
  · exact B362811
  · exact B362815
  · exact B362819
  · exact B362823
  · exact B362827
  · exact B362831
  · exact B362835
  · exact B362839
  · exact B362843
  · exact B362847
  · exact B362851
  · exact B362855
  · exact B362859
  · exact B362863
  · exact B362867
  · exact B362871
  · exact B362875
  · exact B362879
  · exact B362883
  · exact B362887
  · exact B362891
  · exact B362895
  · exact B362899
  · exact B362903
  · exact B362907
  · exact B362911
  · exact B362915
  · exact B362919
  · exact B362923
  · exact B362927
  · exact B362931
  · exact B362935
  · exact B362939
  · exact B362943
  · exact B362947
  · exact B362951
  · exact B362955
  · exact B362959
  · exact B362963
  · exact B362967
  · exact B362971
  · exact B362975
  · exact B362979
  · exact B362983
  · exact B362987
  · exact B362991
  · exact B362995
  · exact B362999
  · exact B363003
  · exact B363007
  · exact B363011
  · exact B363015
  · exact B363019
  · exact B363023
  · exact B363027
  · exact B363031
  · exact B363035
  · exact B363039
  · exact B363043
  · exact B363047
  · exact B363051
  · exact B363055
  · exact B363059
  · exact B363063
  · exact B363067
  · exact B363071
  · exact B363075
  · exact B363079
  · exact B363083
  · exact B363087
  · exact B363091
  · exact B363095
  · exact B363099
  · exact B363103
  · exact B363107
  · exact B363111
  · exact B363115
  · exact B363119
  · exact B363123
  · exact B363127
  · exact B363131
  · exact B363135
  · exact B363139
  · exact B363143
  · exact B363147
  · exact B363151
  · exact B363155
  · exact B363159
  · exact B363163
  · exact B363167
  · exact B363171
  · exact B363175
  · exact B363179
  · exact B363183
  · exact B363187
  · exact B363191
  · exact B363195
  · exact B363199
  · exact B363203
  · exact B363207
  · exact B363211
  · exact B363215
  · exact B363219
  · exact B363223
  · exact B363227
  · exact B363231
  · exact B363235
  · exact B363239
  · exact B363243
  · exact B363247
  · exact B363251
  · exact B363255
  · exact B363259
  · exact B363263
  · exact B363267
  · exact B363271
  · exact B363275
  · exact B363279
  · exact B363283
  · exact B363287
  · exact B363291
  · exact B363295
  · exact B363299
  · exact B363303
  · exact B363307
  · exact B363311
  · exact B363315
  · exact B363319
  · exact B363323
  · exact B363327
  · exact B363331
  · exact B363335
  · exact B363339
  · exact B363343
  · exact B363347
  · exact B363351
  · exact B363355
  · exact B363359
  · exact B363363
  · exact B363367
  · exact B363371
  · exact B363375
  · exact B363379
  · exact B363383
  · exact B363387
  · exact B363391
  · exact B363395
  · exact B363399
  · exact B363403
  · exact B363407
  · exact B363411
  · exact B363415
  · exact B363419
  · exact B363423
  · exact B363427
  · exact B363431
  · exact B363435
  · exact B363439
  · exact B363443
  · exact B363447
  · exact B363451
  · exact B363455
  · exact B363459
  · exact B363463
  · exact B363467
  · exact B363471
  · exact B363475
  · exact B363479
  · exact B363483
  · exact B363487
  · exact B363491
  · exact B363495
  · exact B363499
  · exact B363503
  · exact B363507
  · exact B363511
  · exact B363515
  · exact B363519
  · exact B363523
  · exact B363527
  · exact B363531
  · exact B363535
  · exact B363539
  · exact B363543
  · exact B363547
  · exact B363551
  · exact B363555
  · exact B363559
  · exact B363563
  · exact B363567
  · exact B363571
  · exact B363575
  · exact B363579
  · exact B363583
  · exact B363587
  · exact B363591
  · exact B363595
  · exact B363599
  · exact B363603
  · exact B363607
  · exact B363611
  · exact B363615
  · exact B363619
  · exact B363623
  · exact B363627
  · exact B363631
  · exact B363635
  · exact B363639
  · exact B363643
  · exact B363647
  · exact B363651
  · exact B363655
  · exact B363659
  · exact B363663
  · exact B363667
  · exact B363671
  · exact B363675
  · exact B363679
  · exact B363683
  · exact B363687
  · exact B363691
  · exact B363695
  · exact B363699
  · exact B363703
  · exact B363707
  · exact B363711
  · exact B363715
  · exact B363719
  · exact B363723
  · exact B363727
  · exact B363731
  · exact B363735
  · exact B363739
  · exact B363743
  · exact B363747
  · exact B363751
  · exact B363755
  · exact B363759
  · exact B363763
  · exact B363767
  · exact B363771
  · exact B363775
  · exact B363779
  · exact B363783
  · exact B363787
  · exact B363791
  · exact B363795
  · exact B363799
  · exact B363803
  · exact B363807
  · exact B363811
  · exact B363815
  · exact B363819
  · exact B363823
  · exact B363827
  · exact B363831
  · exact B363835
  · exact B363839
  · exact B363843
  · exact B363847
  · exact B363851
  · exact B363855
  · exact B363859
  · exact B363863
  · exact B363867
  · exact B363871
  · exact B363875
  · exact B363879
  · exact B363883
  · exact B363887
  · exact B363891
  · exact B363895
  · exact B363899
  · exact B363903
  · exact B363907
  · exact B363911
  · exact B363915
  · exact B363919
  · exact B363923
  · exact B363927
  · exact B363931
  · exact B363935
  · exact B363939
  · exact B363943
  · exact B363947
  · exact B363951
  · exact B363955
  · exact B363959
  · exact B363963
  · exact B363967
  · exact B363971
  · exact B363975
  · exact B363979
  · exact B363983
  · exact B363987
  · exact B363991
  · exact B363995
  · exact B363999
  · exact B364003
  · exact B364007
  · exact B364011
  · exact B364015
  · exact B364019
  · exact B364023
  · exact B364027
  · exact B364031
  · exact B364035
  · exact B364039
  · exact B364043
  · exact B364047
  · exact B364051
  · exact B364055
  · exact B364059
  · exact B364063
  · exact B364067
  · exact B364071
  · exact B364075
  · exact B364079
  · exact B364083
  · exact B364087
  · exact B364091
  · exact B364095
  · exact B364099
  · exact B364103
  · exact B364107
  · exact B364111
  · exact B364115
  · exact B364119
  · exact B364123
  · exact B364127
  · exact B364131
  · exact B364135
  · exact B364139
  · exact B364143
  · exact B364147
  · exact B364151
  · exact B364155
  · exact B364159
  · exact B364163
  · exact B364167
  · exact B364171
  · exact B364175
  · exact B364179
  · exact B364183
  · exact B364187
  · exact B364191
  · exact B364195
  · exact B364199
  · exact B364203
  · exact B364207
  · exact B364211
  · exact B364215
  · exact B364219
  · exact B364223
  · exact B364227
  · exact B364231
  · exact B364235
  · exact B364239
  · exact B364243
  · exact B364247
  · exact B364251
  · exact B364255
  · exact B364259
  · exact B364263
  · exact B364267
  · exact B364271
  · exact B364275
  · exact B364279
  · exact B364283
  · exact B364287
  · exact B364291
  · exact B364295
  · exact B364299
  · exact B364303
  · exact B364307
  · exact B364311
  · exact B364315
  · exact B364319
  · exact B364323
  · exact B364327
  · exact B364331
  · exact B364335
  · exact B364339
  · exact B364343
  · exact B364347
  · exact B364351
  · exact B364355
  · exact B364359
  · exact B364363
  · exact B364367
  · exact B364371
  · exact B364375
  · exact B364379
  · exact B364383
  · exact B364387
  · exact B364391
  · exact B364395
  · exact B364399
  · exact B364403
  · exact B364407
  · exact B364411
  · exact B364415
  · exact B364419
  · exact B364423
  · exact B364427
  · exact B364431
  · exact B364435
  · exact B364439
  · exact B364443
  · exact B364447
  · exact B364451
  · exact B364455
  · exact B364459
  · exact B364463
  · exact B364467
  · exact B364471
  · exact B364475
  · exact B364479
  · exact B364483
  · exact B364487
  · exact B364491
  · exact B364495
  · exact B364499
  · exact B364503
  · exact B364507
  · exact B364511
  · exact B364515
  · exact B364519
  · exact B364523
  · exact B364527
  · exact B364531
  · exact B364535
  · exact B364539
  · exact B364543
  · exact B364547
  · exact B364551
  · exact B364555
  · exact B364559
  · exact B364563
  · exact B364567
  · exact B364571
  · exact B364575
  · exact B364579
  · exact B364583
  · exact B364587
  · exact B364591
  · exact B364595
  · exact B364599
  · exact B364603
  · exact B364607
  · exact B364611
  · exact B364615
  · exact B364619
  · exact B364623
  · exact B364627
  · exact B364631
  · exact B364635
  · exact B364639
  · exact B364643
  · exact B364647
  · exact B364651
  · exact B364655
  · exact B364659
  · exact B364663
  · exact B364667
  · exact B364671
  · exact B364675
  · exact B364679
  · exact B364683
  · exact B364687
  · exact B364691
  · exact B364695
  · exact B364699
  · exact B364703
  · exact B364707
  · exact B364711
  · exact B364715
  · exact B364719
  · exact B364723
  · exact B364727
  · exact B364731
  · exact B364735
  · exact B364739
  · exact B364743
  · exact B364747
  · exact B364751
  · exact B364755
  · exact B364759
  · exact B364763
  · exact B364767
  · exact B364771
  · exact B364775
  · exact B364779
  · exact B364783
  · exact B364787
  · exact B364791
  · exact B364795
  · exact B364799
  · exact B364803
  · exact B364807
  · exact B364811
  · exact B364815
  · exact B364819
  · exact B364823
  · exact B364827
  · exact B364831
  · exact B364835
  · exact B364839
  · exact B364843
  · exact B364847
  · exact B364851
  · exact B364855
  · exact B364859
  · exact B364863
  · exact B364867
  · exact B364871
  · exact B364875
  · exact B364879
  · exact B364883
  · exact B364887
  · exact B364891
  · exact B364895
  · exact B364899
  · exact B364903
  · exact B364907
  · exact B364911
  · exact B364915
  · exact B364919
  · exact B364923
  · exact B364927
  · exact B364931
  · exact B364935
  · exact B364939
  · exact B364943
  · exact B364947
  · exact B364951
  · exact B364955
  · exact B364959
  · exact B364963
  · exact B364967
  · exact B364971
  · exact B364975
  · exact B364979
  · exact B364983
  · exact B364987
  · exact B364991
  · exact B364995
  · exact B364999
  · exact B365003
  · exact B365007
  · exact B365011
  · exact B365015
  · exact B365019
  · exact B365023
  · exact B365027
  · exact B365031
  · exact B365035
  · exact B365039
  · exact B365043
  · exact B365047
  · exact B365051
  · exact B365055
  · exact B365059
  · exact B365063
  · exact B365067
  · exact B365071
  · exact B365075
  · exact B365079
  · exact B365083
  · exact B365087
  · exact B365091
  · exact B365095
  · exact B365099
  · exact B365103
  · exact B365107
  · exact B365111
  · exact B365115
  · exact B365119
  · exact B365123
  · exact B365127
  · exact B365131
  · exact B365135
  · exact B365139
  · exact B365143
  · exact B365147
  · exact B365151
  · exact B365155
  · exact B365159
  · exact B365163
  · exact B365167
  · exact B365171
  · exact B365175
  · exact B365179
  · exact B365183
  · exact B365187
  · exact B365191
  · exact B365195
  · exact B365199
  · exact B365203
  · exact B365207
  · exact B365211
  · exact B365215
  · exact B365219
  · exact B365223
  · exact B365227
  · exact B365231
  · exact B365235
  · exact B365239
  · exact B365243
  · exact B365247
  · exact B365251
  · exact B365255
  · exact B365259
  · exact B365263
  · exact B365267
  · exact B365271
  · exact B365275
  · exact B365279
  · exact B365283
  · exact B365287
  · exact B365291
  · exact B365295
  · exact B365299
  · exact B365303
  · exact B365307
  · exact B365311
  · exact B365315
  · exact B365319
  · exact B365323
  · exact B365327
  · exact B365331
  · exact B365335
  · exact B365339
  · exact B365343
  · exact B365347
  · exact B365351
  · exact B365355
  · exact B365359
  · exact B365363
  · exact B365367
  · exact B365371
  · exact B365375
  · exact B365379
  · exact B365383
  · exact B365387
  · exact B365391
  · exact B365395
  · exact B365399
  · exact B365403
  · exact B365407
  · exact B365411
  · exact B365415
  · exact B365419
  · exact B365423
  · exact B365427
  · exact B365431
  · exact B365435
  · exact B365439
  · exact B365443
  · exact B365447
  · exact B365451
  · exact B365455
  · exact B365459
  · exact B365463
  · exact B365467
  · exact B365471
  · exact B365475
  · exact B365479
  · exact B365483
  · exact B365487
  · exact B365491
  · exact B365495
  · exact B365499
  · exact B365503
  · exact B365507
  · exact B365511
  · exact B365515
  · exact B365519
  · exact B365523
  · exact B365527
  · exact B365531
  · exact B365535
  · exact B365539
  · exact B365543
  · exact B365547
  · exact B365551
  · exact B365555

theorem C1 (j : ℕ) (h1 : 91389 ≤ j) (h2 : j ≤ 91688) : Blo 362758 (4 * j + 3) := by
  interval_cases j
  · exact B365559
  · exact B365563
  · exact B365567
  · exact B365571
  · exact B365575
  · exact B365579
  · exact B365583
  · exact B365587
  · exact B365591
  · exact B365595
  · exact B365599
  · exact B365603
  · exact B365607
  · exact B365611
  · exact B365615
  · exact B365619
  · exact B365623
  · exact B365627
  · exact B365631
  · exact B365635
  · exact B365639
  · exact B365643
  · exact B365647
  · exact B365651
  · exact B365655
  · exact B365659
  · exact B365663
  · exact B365667
  · exact B365671
  · exact B365675
  · exact B365679
  · exact B365683
  · exact B365687
  · exact B365691
  · exact B365695
  · exact B365699
  · exact B365703
  · exact B365707
  · exact B365711
  · exact B365715
  · exact B365719
  · exact B365723
  · exact B365727
  · exact B365731
  · exact B365735
  · exact B365739
  · exact B365743
  · exact B365747
  · exact B365751
  · exact B365755
  · exact B365759
  · exact B365763
  · exact B365767
  · exact B365771
  · exact B365775
  · exact B365779
  · exact B365783
  · exact B365787
  · exact B365791
  · exact B365795
  · exact B365799
  · exact B365803
  · exact B365807
  · exact B365811
  · exact B365815
  · exact B365819
  · exact B365823
  · exact B365827
  · exact B365831
  · exact B365835
  · exact B365839
  · exact B365843
  · exact B365847
  · exact B365851
  · exact B365855
  · exact B365859
  · exact B365863
  · exact B365867
  · exact B365871
  · exact B365875
  · exact B365879
  · exact B365883
  · exact B365887
  · exact B365891
  · exact B365895
  · exact B365899
  · exact B365903
  · exact B365907
  · exact B365911
  · exact B365915
  · exact B365919
  · exact B365923
  · exact B365927
  · exact B365931
  · exact B365935
  · exact B365939
  · exact B365943
  · exact B365947
  · exact B365951
  · exact B365955
  · exact B365959
  · exact B365963
  · exact B365967
  · exact B365971
  · exact B365975
  · exact B365979
  · exact B365983
  · exact B365987
  · exact B365991
  · exact B365995
  · exact B365999
  · exact B366003
  · exact B366007
  · exact B366011
  · exact B366015
  · exact B366019
  · exact B366023
  · exact B366027
  · exact B366031
  · exact B366035
  · exact B366039
  · exact B366043
  · exact B366047
  · exact B366051
  · exact B366055
  · exact B366059
  · exact B366063
  · exact B366067
  · exact B366071
  · exact B366075
  · exact B366079
  · exact B366083
  · exact B366087
  · exact B366091
  · exact B366095
  · exact B366099
  · exact B366103
  · exact B366107
  · exact B366111
  · exact B366115
  · exact B366119
  · exact B366123
  · exact B366127
  · exact B366131
  · exact B366135
  · exact B366139
  · exact B366143
  · exact B366147
  · exact B366151
  · exact B366155
  · exact B366159
  · exact B366163
  · exact B366167
  · exact B366171
  · exact B366175
  · exact B366179
  · exact B366183
  · exact B366187
  · exact B366191
  · exact B366195
  · exact B366199
  · exact B366203
  · exact B366207
  · exact B366211
  · exact B366215
  · exact B366219
  · exact B366223
  · exact B366227
  · exact B366231
  · exact B366235
  · exact B366239
  · exact B366243
  · exact B366247
  · exact B366251
  · exact B366255
  · exact B366259
  · exact B366263
  · exact B366267
  · exact B366271
  · exact B366275
  · exact B366279
  · exact B366283
  · exact B366287
  · exact B366291
  · exact B366295
  · exact B366299
  · exact B366303
  · exact B366307
  · exact B366311
  · exact B366315
  · exact B366319
  · exact B366323
  · exact B366327
  · exact B366331
  · exact B366335
  · exact B366339
  · exact B366343
  · exact B366347
  · exact B366351
  · exact B366355
  · exact B366359
  · exact B366363
  · exact B366367
  · exact B366371
  · exact B366375
  · exact B366379
  · exact B366383
  · exact B366387
  · exact B366391
  · exact B366395
  · exact B366399
  · exact B366403
  · exact B366407
  · exact B366411
  · exact B366415
  · exact B366419
  · exact B366423
  · exact B366427
  · exact B366431
  · exact B366435
  · exact B366439
  · exact B366443
  · exact B366447
  · exact B366451
  · exact B366455
  · exact B366459
  · exact B366463
  · exact B366467
  · exact B366471
  · exact B366475
  · exact B366479
  · exact B366483
  · exact B366487
  · exact B366491
  · exact B366495
  · exact B366499
  · exact B366503
  · exact B366507
  · exact B366511
  · exact B366515
  · exact B366519
  · exact B366523
  · exact B366527
  · exact B366531
  · exact B366535
  · exact B366539
  · exact B366543
  · exact B366547
  · exact B366551
  · exact B366555
  · exact B366559
  · exact B366563
  · exact B366567
  · exact B366571
  · exact B366575
  · exact B366579
  · exact B366583
  · exact B366587
  · exact B366591
  · exact B366595
  · exact B366599
  · exact B366603
  · exact B366607
  · exact B366611
  · exact B366615
  · exact B366619
  · exact B366623
  · exact B366627
  · exact B366631
  · exact B366635
  · exact B366639
  · exact B366643
  · exact B366647
  · exact B366651
  · exact B366655
  · exact B366659
  · exact B366663
  · exact B366667
  · exact B366671
  · exact B366675
  · exact B366679
  · exact B366683
  · exact B366687
  · exact B366691
  · exact B366695
  · exact B366699
  · exact B366703
  · exact B366707
  · exact B366711
  · exact B366715
  · exact B366719
  · exact B366723
  · exact B366727
  · exact B366731
  · exact B366735
  · exact B366739
  · exact B366743
  · exact B366747
  · exact B366751
  · exact B366755

theorem solution (m : ℕ) (hlo : 362758 ≤ m) (hhi : m ≤ 366758) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 90689 ≤ j := by omega
    have hj2 : j ≤ 91688 := by omega
    have hb : Blo 362758 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 91389 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
