-- Prove2me | solution 1 for syracuse_descends_range_271824_275824
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:10.643927+00:00
-- url     : https://prove2.me/submissions/238e073b-1069-40ab-8ae6-17aa64ea912d

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


theorem B458797 : Blo 271824 458797 := bbase (se 3 (by rfl) ⟨86024, by rfl⟩ : syracuseStep 458797 = 172049) (by norm_num)
theorem B917621 : Blo 271824 917621 := bbase (se 5 (by rfl) ⟨43013, by rfl⟩ : syracuseStep 917621 = 86027) (by norm_num)
theorem B458885 : Blo 271824 458885 := bbase (se 4 (by rfl) ⟨43020, by rfl⟩ : syracuseStep 458885 = 86041) (by norm_num)
theorem B327817 : Blo 271824 327817 := bbase (se 2 (by rfl) ⟨122931, by rfl⟩ : syracuseStep 327817 = 245863) (by norm_num)
theorem B688277 : Blo 271824 688277 := bbase (se 6 (by rfl) ⟨16131, by rfl⟩ : syracuseStep 688277 = 32263) (by norm_num)
theorem B295093 : Blo 271824 295093 := bbase (se 5 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 295093 = 27665) (by norm_num)
theorem B524485 : Blo 271824 524485 := bbase (se 4 (by rfl) ⟨49170, by rfl⟩ : syracuseStep 524485 = 98341) (by norm_num)
theorem B459013 : Blo 271824 459013 := bbase (se 4 (by rfl) ⟨43032, by rfl⟩ : syracuseStep 459013 = 86065) (by norm_num)
theorem B459101 : Blo 271824 459101 := bbase (se 3 (by rfl) ⟨86081, by rfl⟩ : syracuseStep 459101 = 172163) (by norm_num)
theorem B328033 : Blo 271824 328033 := bbase (se 2 (by rfl) ⟨123012, by rfl⟩ : syracuseStep 328033 = 246025) (by norm_num)
theorem B459109 : Blo 271824 459109 := bbase (se 4 (by rfl) ⟨43041, by rfl⟩ : syracuseStep 459109 = 86083) (by norm_num)
theorem B1245557 : Blo 271824 1245557 := bbase (se 5 (by rfl) ⟨58385, by rfl⟩ : syracuseStep 1245557 = 116771) (by norm_num)
theorem B459229 : Blo 271824 459229 := bbase (se 3 (by rfl) ⟨86105, by rfl⟩ : syracuseStep 459229 = 172211) (by norm_num)
theorem B688621 : Blo 271824 688621 := bbase (se 3 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 688621 = 258233) (by norm_num)
theorem B918053 : Blo 271824 918053 := bbase (se 4 (by rfl) ⟨86067, by rfl⟩ : syracuseStep 918053 = 172135) (by norm_num)
theorem B459317 : Blo 271824 459317 := bbase (se 5 (by rfl) ⟨21530, by rfl⟩ : syracuseStep 459317 = 43061) (by norm_num)
theorem B1376837 : Blo 271824 1376837 := bbase (se 4 (by rfl) ⟨129078, by rfl⟩ : syracuseStep 1376837 = 258157) (by norm_num)
theorem B688733 : Blo 271824 688733 := bbase (se 3 (by rfl) ⟨129137, by rfl⟩ : syracuseStep 688733 = 258275) (by norm_num)
theorem B2065013 : Blo 271824 2065013 := bbase (se 5 (by rfl) ⟨96797, by rfl⟩ : syracuseStep 2065013 = 193595) (by norm_num)
theorem B459445 : Blo 271824 459445 := bbase (se 5 (by rfl) ⟨21536, by rfl⟩ : syracuseStep 459445 = 43073) (by norm_num)
theorem B492229 : Blo 271824 492229 := bbase (se 4 (by rfl) ⟨46146, by rfl⟩ : syracuseStep 492229 = 92293) (by norm_num)
theorem B459533 : Blo 271824 459533 := bbase (se 3 (by rfl) ⟨86162, by rfl⟩ : syracuseStep 459533 = 172325) (by norm_num)
theorem B688925 : Blo 271824 688925 := bbase (se 3 (by rfl) ⟨129173, by rfl⟩ : syracuseStep 688925 = 258347) (by norm_num)
theorem B459661 : Blo 271824 459661 := bbase (se 3 (by rfl) ⟨86186, by rfl⟩ : syracuseStep 459661 = 172373) (by norm_num)
theorem B590789 : Blo 271824 590789 := bbase (se 4 (by rfl) ⟨55386, by rfl⟩ : syracuseStep 590789 = 110773) (by norm_num)
theorem B918485 : Blo 271824 918485 := bbase (se 7 (by rfl) ⟨10763, by rfl⟩ : syracuseStep 918485 = 21527) (by norm_num)
theorem B459749 : Blo 271824 459749 := bbase (se 4 (by rfl) ⟨43101, by rfl⟩ : syracuseStep 459749 = 86203) (by norm_num)
theorem B459877 : Blo 271824 459877 := bbase (se 4 (by rfl) ⟨43113, by rfl⟩ : syracuseStep 459877 = 86227) (by norm_num)
theorem B689269 : Blo 271824 689269 := bbase (se 5 (by rfl) ⟨32309, by rfl⟩ : syracuseStep 689269 = 64619) (by norm_num)
theorem B459965 : Blo 271824 459965 := bbase (se 3 (by rfl) ⟨86243, by rfl⟩ : syracuseStep 459965 = 172487) (by norm_num)
theorem B689381 : Blo 271824 689381 := bbase (se 4 (by rfl) ⟨64629, by rfl⟩ : syracuseStep 689381 = 129259) (by norm_num)
theorem B460093 : Blo 271824 460093 := bbase (se 3 (by rfl) ⟨86267, by rfl⟩ : syracuseStep 460093 = 172535) (by norm_num)
theorem B492893 : Blo 271824 492893 := bbase (se 3 (by rfl) ⟨92417, by rfl⟩ : syracuseStep 492893 = 184835) (by norm_num)
theorem B755077 : Blo 271824 755077 := bbase (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) (by norm_num)
theorem B918917 : Blo 271824 918917 := bbase (se 4 (by rfl) ⟨86148, by rfl⟩ : syracuseStep 918917 = 172297) (by norm_num)
theorem B460181 : Blo 271824 460181 := bbase (se 6 (by rfl) ⟨10785, by rfl⟩ : syracuseStep 460181 = 21571) (by norm_num)
theorem B689573 : Blo 271824 689573 := bbase (se 4 (by rfl) ⟨64647, by rfl⟩ : syracuseStep 689573 = 129295) (by norm_num)
theorem B394733 : Blo 271824 394733 := bbase (se 3 (by rfl) ⟨74012, by rfl⟩ : syracuseStep 394733 = 148025) (by norm_num)
theorem B493037 : Blo 271824 493037 := bbase (se 3 (by rfl) ⟨92444, by rfl⟩ : syracuseStep 493037 = 184889) (by norm_num)
theorem B624109 : Blo 271824 624109 := bbase (se 3 (by rfl) ⟨117020, by rfl⟩ : syracuseStep 624109 = 234041) (by norm_num)
theorem B460309 : Blo 271824 460309 := bbase (se 6 (by rfl) ⟨10788, by rfl⟩ : syracuseStep 460309 = 21577) (by norm_num)
theorem B460397 : Blo 271824 460397 := bbase (se 3 (by rfl) ⟨86324, by rfl⟩ : syracuseStep 460397 = 172649) (by norm_num)
theorem B624293 : Blo 271824 624293 := bbase (se 4 (by rfl) ⟨58527, by rfl⟩ : syracuseStep 624293 = 117055) (by norm_num)
theorem B296641 : Blo 271824 296641 := bbase (se 2 (by rfl) ⟨111240, by rfl⟩ : syracuseStep 296641 = 222481) (by norm_num)
theorem B460525 : Blo 271824 460525 := bbase (se 3 (by rfl) ⟨86348, by rfl⟩ : syracuseStep 460525 = 172697) (by norm_num)
theorem B689917 : Blo 271824 689917 := bbase (se 3 (by rfl) ⟨129359, by rfl⟩ : syracuseStep 689917 = 258719) (by norm_num)
theorem B919349 : Blo 271824 919349 := bbase (se 5 (by rfl) ⟨43094, by rfl⟩ : syracuseStep 919349 = 86189) (by norm_num)
theorem B460613 : Blo 271824 460613 := bbase (se 4 (by rfl) ⟨43182, by rfl⟩ : syracuseStep 460613 = 86365) (by norm_num)
theorem B1378133 : Blo 271824 1378133 := bbase (se 9 (by rfl) ⟨4037, by rfl⟩ : syracuseStep 1378133 = 8075) (by norm_num)
theorem B591709 : Blo 271824 591709 := bbase (se 3 (by rfl) ⟨110945, by rfl⟩ : syracuseStep 591709 = 221891) (by norm_num)
theorem B690029 : Blo 271824 690029 := bbase (se 3 (by rfl) ⟨129380, by rfl⟩ : syracuseStep 690029 = 258761) (by norm_num)
theorem B657325 : Blo 271824 657325 := bbase (se 3 (by rfl) ⟨123248, by rfl⟩ : syracuseStep 657325 = 246497) (by norm_num)
theorem B460741 : Blo 271824 460741 := bbase (se 4 (by rfl) ⟨43194, by rfl⟩ : syracuseStep 460741 = 86389) (by norm_num)
theorem B329729 : Blo 271824 329729 := bbase (se 2 (by rfl) ⟨123648, by rfl⟩ : syracuseStep 329729 = 247297) (by norm_num)
theorem B3377173 : Blo 271824 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B460829 : Blo 271824 460829 := bbase (se 3 (by rfl) ⟨86405, by rfl⟩ : syracuseStep 460829 = 172811) (by norm_num)
theorem B690221 : Blo 271824 690221 := bbase (se 3 (by rfl) ⟨129416, by rfl⟩ : syracuseStep 690221 = 258833) (by norm_num)
theorem B460957 : Blo 271824 460957 := bbase (se 3 (by rfl) ⟨86429, by rfl⟩ : syracuseStep 460957 = 172859) (by norm_num)
theorem B329941 : Blo 271824 329941 := bbase (se 7 (by rfl) ⟨3866, by rfl⟩ : syracuseStep 329941 = 7733) (by norm_num)
theorem B919781 : Blo 271824 919781 := bbase (se 4 (by rfl) ⟨86229, by rfl⟩ : syracuseStep 919781 = 172459) (by norm_num)
theorem B461045 : Blo 271824 461045 := bbase (se 5 (by rfl) ⟨21611, by rfl⟩ : syracuseStep 461045 = 43223) (by norm_num)
theorem B297317 : Blo 271824 297317 := bbase (se 4 (by rfl) ⟨27873, by rfl⟩ : syracuseStep 297317 = 55747) (by norm_num)
theorem B330085 : Blo 271824 330085 := bbase (se 4 (by rfl) ⟨30945, by rfl⟩ : syracuseStep 330085 = 61891) (by norm_num)
theorem B461173 : Blo 271824 461173 := bbase (se 5 (by rfl) ⟨21617, by rfl⟩ : syracuseStep 461173 = 43235) (by norm_num)
theorem B690565 : Blo 271824 690565 := bbase (se 4 (by rfl) ⟨64740, by rfl⟩ : syracuseStep 690565 = 129481) (by norm_num)
theorem B461261 : Blo 271824 461261 := bbase (se 3 (by rfl) ⟨86486, by rfl⟩ : syracuseStep 461261 = 172973) (by norm_num)
theorem B1051093 : Blo 271824 1051093 := bbase (se 7 (by rfl) ⟨12317, by rfl⟩ : syracuseStep 1051093 = 24635) (by norm_num)
theorem B690677 : Blo 271824 690677 := bbase (se 5 (by rfl) ⟨32375, by rfl⟩ : syracuseStep 690677 = 64751) (by norm_num)
theorem B625205 : Blo 271824 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B461389 : Blo 271824 461389 := bbase (se 3 (by rfl) ⟨86510, by rfl⟩ : syracuseStep 461389 = 173021) (by norm_num)
theorem B658037 : Blo 271824 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B625277 : Blo 271824 625277 := bbase (se 3 (by rfl) ⟨117239, by rfl⟩ : syracuseStep 625277 = 234479) (by norm_num)
theorem B920213 : Blo 271824 920213 := bbase (se 6 (by rfl) ⟨21567, by rfl⟩ : syracuseStep 920213 = 43135) (by norm_num)
theorem B461477 : Blo 271824 461477 := bbase (se 4 (by rfl) ⟨43263, by rfl⟩ : syracuseStep 461477 = 86527) (by norm_num)
theorem B690869 : Blo 271824 690869 := bbase (se 5 (by rfl) ⟨32384, by rfl⟩ : syracuseStep 690869 = 64769) (by norm_num)
theorem B461605 : Blo 271824 461605 := bbase (se 4 (by rfl) ⟨43275, by rfl⟩ : syracuseStep 461605 = 86551) (by norm_num)
theorem B2329397 : Blo 271824 2329397 := bbase (se 5 (by rfl) ⟨109190, by rfl⟩ : syracuseStep 2329397 = 218381) (by norm_num)
theorem B461693 : Blo 271824 461693 := bbase (se 3 (by rfl) ⟨86567, by rfl⟩ : syracuseStep 461693 = 173135) (by norm_num)
theorem B396181 : Blo 271824 396181 := bbase (se 6 (by rfl) ⟨9285, by rfl⟩ : syracuseStep 396181 = 18571) (by norm_num)
theorem B1313765 : Blo 271824 1313765 := bbase (se 4 (by rfl) ⟨123165, by rfl⟩ : syracuseStep 1313765 = 246331) (by norm_num)
theorem B658421 : Blo 271824 658421 := bbase (se 5 (by rfl) ⟨30863, by rfl⟩ : syracuseStep 658421 = 61727) (by norm_num)
theorem B461821 : Blo 271824 461821 := bbase (se 3 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 461821 = 173183) (by norm_num)
theorem B691213 : Blo 271824 691213 := bbase (se 3 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 691213 = 259205) (by norm_num)
theorem B920645 : Blo 271824 920645 := bbase (se 4 (by rfl) ⟨86310, by rfl⟩ : syracuseStep 920645 = 172621) (by norm_num)
theorem B461909 : Blo 271824 461909 := bbase (se 8 (by rfl) ⟨2706, by rfl⟩ : syracuseStep 461909 = 5413) (by norm_num)
theorem B1379429 : Blo 271824 1379429 := bbase (se 4 (by rfl) ⟨129321, by rfl⟩ : syracuseStep 1379429 = 258643) (by norm_num)
theorem B1510517 : Blo 271824 1510517 := bbase (se 5 (by rfl) ⟨70805, by rfl⟩ : syracuseStep 1510517 = 141611) (by norm_num)
theorem B691325 : Blo 271824 691325 := bbase (se 3 (by rfl) ⟨129623, by rfl⟩ : syracuseStep 691325 = 259247) (by norm_num)
theorem B462037 : Blo 271824 462037 := bbase (se 7 (by rfl) ⟨5414, by rfl⟩ : syracuseStep 462037 = 10829) (by norm_num)
theorem B658709 : Blo 271824 658709 := bbase (se 6 (by rfl) ⟨15438, by rfl⟩ : syracuseStep 658709 = 30877) (by norm_num)
theorem B462125 : Blo 271824 462125 := bbase (se 3 (by rfl) ⟨86648, by rfl⟩ : syracuseStep 462125 = 173297) (by norm_num)
theorem B691517 : Blo 271824 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B396677 : Blo 271824 396677 := bbase (se 4 (by rfl) ⟨37188, by rfl⟩ : syracuseStep 396677 = 74377) (by norm_num)
theorem B462253 : Blo 271824 462253 := bbase (se 3 (by rfl) ⟨86672, by rfl⟩ : syracuseStep 462253 = 173345) (by norm_num)
theorem B527789 : Blo 271824 527789 := bbase (se 3 (by rfl) ⟨98960, by rfl⟩ : syracuseStep 527789 = 197921) (by norm_num)
theorem B495085 : Blo 271824 495085 := bbase (se 3 (by rfl) ⟨92828, by rfl⟩ : syracuseStep 495085 = 185657) (by norm_num)
theorem B921077 : Blo 271824 921077 := bbase (se 5 (by rfl) ⟨43175, by rfl⟩ : syracuseStep 921077 = 86351) (by norm_num)
theorem B462341 : Blo 271824 462341 := bbase (se 4 (by rfl) ⟨43344, by rfl⟩ : syracuseStep 462341 = 86689) (by norm_num)
theorem B1052261 : Blo 271824 1052261 := bbase (se 4 (by rfl) ⟨98649, by rfl⟩ : syracuseStep 1052261 = 197299) (by norm_num)
theorem B462469 : Blo 271824 462469 := bbase (se 4 (by rfl) ⟨43356, by rfl⟩ : syracuseStep 462469 = 86713) (by norm_num)
theorem B691861 : Blo 271824 691861 := bbase (se 6 (by rfl) ⟨16215, by rfl⟩ : syracuseStep 691861 = 32431) (by norm_num)
theorem B462557 : Blo 271824 462557 := bbase (se 3 (by rfl) ⟨86729, by rfl⟩ : syracuseStep 462557 = 173459) (by norm_num)
theorem B691973 : Blo 271824 691973 := bbase (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) (by norm_num)
theorem B528157 : Blo 271824 528157 := bbase (se 3 (by rfl) ⟨99029, by rfl⟩ : syracuseStep 528157 = 198059) (by norm_num)
theorem B560981 : Blo 271824 560981 := bbase (se 9 (by rfl) ⟨1643, by rfl⟩ : syracuseStep 560981 = 3287) (by norm_num)
theorem B462685 : Blo 271824 462685 := bbase (se 3 (by rfl) ⟨86753, by rfl⟩ : syracuseStep 462685 = 173507) (by norm_num)
theorem B495517 : Blo 271824 495517 := bbase (se 3 (by rfl) ⟨92909, by rfl⟩ : syracuseStep 495517 = 185819) (by norm_num)
theorem B921509 : Blo 271824 921509 := bbase (se 4 (by rfl) ⟨86391, by rfl⟩ : syracuseStep 921509 = 172783) (by norm_num)
theorem B462773 : Blo 271824 462773 := bbase (se 5 (by rfl) ⟨21692, by rfl⟩ : syracuseStep 462773 = 43385) (by norm_num)
theorem B528317 : Blo 271824 528317 := bbase (se 3 (by rfl) ⟨99059, by rfl⟩ : syracuseStep 528317 = 198119) (by norm_num)
theorem B692165 : Blo 271824 692165 := bbase (se 4 (by rfl) ⟨64890, by rfl⟩ : syracuseStep 692165 = 129781) (by norm_num)
theorem B2625493 : Blo 271824 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B495661 : Blo 271824 495661 := bbase (se 3 (by rfl) ⟨92936, by rfl⟩ : syracuseStep 495661 = 185873) (by norm_num)
theorem B462901 : Blo 271824 462901 := bbase (se 5 (by rfl) ⟨21698, by rfl⟩ : syracuseStep 462901 = 43397) (by norm_num)
theorem B462989 : Blo 271824 462989 := bbase (se 3 (by rfl) ⟨86810, by rfl⟩ : syracuseStep 462989 = 173621) (by norm_num)
theorem B495877 : Blo 271824 495877 := bbase (se 4 (by rfl) ⟨46488, by rfl⟩ : syracuseStep 495877 = 92977) (by norm_num)
theorem B463117 : Blo 271824 463117 := bbase (se 3 (by rfl) ⟨86834, by rfl⟩ : syracuseStep 463117 = 173669) (by norm_num)
theorem B692509 : Blo 271824 692509 := bbase (se 3 (by rfl) ⟨129845, by rfl⟩ : syracuseStep 692509 = 259691) (by norm_num)
theorem B921941 : Blo 271824 921941 := bbase (se 10 (by rfl) ⟨1350, by rfl⟩ : syracuseStep 921941 = 2701) (by norm_num)
theorem B627029 : Blo 271824 627029 := bbase (se 10 (by rfl) ⟨918, by rfl⟩ : syracuseStep 627029 = 1837) (by norm_num)
theorem B463205 : Blo 271824 463205 := bbase (se 4 (by rfl) ⟨43425, by rfl⟩ : syracuseStep 463205 = 86851) (by norm_num)
theorem B1380725 : Blo 271824 1380725 := bbase (se 5 (by rfl) ⟨64721, by rfl⟩ : syracuseStep 1380725 = 129443) (by norm_num)
theorem B692621 : Blo 271824 692621 := bbase (se 3 (by rfl) ⟨129866, by rfl⟩ : syracuseStep 692621 = 259733) (by norm_num)
theorem B1053157 : Blo 271824 1053157 := bbase (se 4 (by rfl) ⟨98733, by rfl⟩ : syracuseStep 1053157 = 197467) (by norm_num)
theorem B463333 : Blo 271824 463333 := bbase (se 4 (by rfl) ⟨43437, by rfl⟩ : syracuseStep 463333 = 86875) (by norm_num)
theorem B561709 : Blo 271824 561709 := bbase (se 3 (by rfl) ⟨105320, by rfl⟩ : syracuseStep 561709 = 210641) (by norm_num)
theorem B463421 : Blo 271824 463421 := bbase (se 3 (by rfl) ⟨86891, by rfl⟩ : syracuseStep 463421 = 173783) (by norm_num)
theorem B692813 : Blo 271824 692813 := bbase (se 3 (by rfl) ⟨129902, by rfl⟩ : syracuseStep 692813 = 259805) (by norm_num)
theorem B627277 : Blo 271824 627277 := bbase (se 3 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 627277 = 235229) (by norm_num)
theorem B463549 : Blo 271824 463549 := bbase (se 3 (by rfl) ⟨86915, by rfl⟩ : syracuseStep 463549 = 173831) (by norm_num)
theorem B922373 : Blo 271824 922373 := bbase (se 4 (by rfl) ⟨86472, by rfl⟩ : syracuseStep 922373 = 172945) (by norm_num)
theorem B463637 : Blo 271824 463637 := bbase (se 6 (by rfl) ⟨10866, by rfl⟩ : syracuseStep 463637 = 21733) (by norm_num)
theorem B2954069 : Blo 271824 2954069 := bbase (se 9 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 2954069 = 17309) (by norm_num)
theorem B496469 : Blo 271824 496469 := bbase (se 9 (by rfl) ⟨1454, by rfl⟩ : syracuseStep 496469 = 2909) (by norm_num)
theorem B463765 : Blo 271824 463765 := bbase (se 6 (by rfl) ⟨10869, by rfl⟩ : syracuseStep 463765 = 21739) (by norm_num)
theorem B693157 : Blo 271824 693157 := bbase (se 4 (by rfl) ⟨64983, by rfl⟩ : syracuseStep 693157 = 129967) (by norm_num)
theorem B463853 : Blo 271824 463853 := bbase (se 3 (by rfl) ⟨86972, by rfl⟩ : syracuseStep 463853 = 173945) (by norm_num)
theorem B693269 : Blo 271824 693269 := bbase (se 6 (by rfl) ⟨16248, by rfl⟩ : syracuseStep 693269 = 32497) (by norm_num)
theorem B1414181 : Blo 271824 1414181 := bbase (se 4 (by rfl) ⟨132579, by rfl⟩ : syracuseStep 1414181 = 265159) (by norm_num)
theorem B496685 : Blo 271824 496685 := bbase (se 3 (by rfl) ⟨93128, by rfl⟩ : syracuseStep 496685 = 186257) (by norm_num)
theorem B463981 : Blo 271824 463981 := bbase (se 3 (by rfl) ⟨86996, by rfl⟩ : syracuseStep 463981 = 173993) (by norm_num)
theorem B922805 : Blo 271824 922805 := bbase (se 5 (by rfl) ⟨43256, by rfl⟩ : syracuseStep 922805 = 86513) (by norm_num)
theorem B464069 : Blo 271824 464069 := bbase (se 4 (by rfl) ⟨43506, by rfl⟩ : syracuseStep 464069 = 87013) (by norm_num)
theorem B693461 : Blo 271824 693461 := bbase (se 7 (by rfl) ⟨8126, by rfl⟩ : syracuseStep 693461 = 16253) (by norm_num)
theorem B627941 : Blo 271824 627941 := bbase (se 4 (by rfl) ⟨58869, by rfl⟩ : syracuseStep 627941 = 117739) (by norm_num)
theorem B464197 : Blo 271824 464197 := bbase (se 4 (by rfl) ⟨43518, by rfl⟩ : syracuseStep 464197 = 87037) (by norm_num)
theorem B496973 : Blo 271824 496973 := bbase (se 3 (by rfl) ⟨93182, by rfl⟩ : syracuseStep 496973 = 186365) (by norm_num)
theorem B464285 : Blo 271824 464285 := bbase (se 3 (by rfl) ⟨87053, by rfl⟩ : syracuseStep 464285 = 174107) (by norm_num)
theorem B2004437 : Blo 271824 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B464413 : Blo 271824 464413 := bbase (se 3 (by rfl) ⟨87077, by rfl⟩ : syracuseStep 464413 = 174155) (by norm_num)
theorem B529949 : Blo 271824 529949 := bbase (se 3 (by rfl) ⟨99365, by rfl⟩ : syracuseStep 529949 = 198731) (by norm_num)
theorem B693805 : Blo 271824 693805 := bbase (se 3 (by rfl) ⟨130088, by rfl⟩ : syracuseStep 693805 = 260177) (by norm_num)
theorem B988757 : Blo 271824 988757 := bbase (se 8 (by rfl) ⟨5793, by rfl⟩ : syracuseStep 988757 = 11587) (by norm_num)
theorem B923237 : Blo 271824 923237 := bbase (se 4 (by rfl) ⟨86553, by rfl⟩ : syracuseStep 923237 = 173107) (by norm_num)
theorem B464501 : Blo 271824 464501 := bbase (se 5 (by rfl) ⟨21773, by rfl⟩ : syracuseStep 464501 = 43547) (by norm_num)
theorem B1382021 : Blo 271824 1382021 := bbase (se 4 (by rfl) ⟨129564, by rfl⟩ : syracuseStep 1382021 = 259129) (by norm_num)
theorem B693917 : Blo 271824 693917 := bbase (se 3 (by rfl) ⟨130109, by rfl⟩ : syracuseStep 693917 = 260219) (by norm_num)
theorem B1316533 : Blo 271824 1316533 := bbase (se 5 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 1316533 = 123425) (by norm_num)
theorem B464629 : Blo 271824 464629 := bbase (se 5 (by rfl) ⟨21779, by rfl⟩ : syracuseStep 464629 = 43559) (by norm_num)
theorem B890677 : Blo 271824 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B464717 : Blo 271824 464717 := bbase (se 3 (by rfl) ⟨87134, by rfl⟩ : syracuseStep 464717 = 174269) (by norm_num)
theorem B694109 : Blo 271824 694109 := bbase (se 3 (by rfl) ⟨130145, by rfl⟩ : syracuseStep 694109 = 260291) (by norm_num)
theorem B464845 : Blo 271824 464845 := bbase (se 3 (by rfl) ⟨87158, by rfl⟩ : syracuseStep 464845 = 174317) (by norm_num)
theorem B923669 : Blo 271824 923669 := bbase (se 6 (by rfl) ⟨21648, by rfl⟩ : syracuseStep 923669 = 43297) (by norm_num)
theorem B464933 : Blo 271824 464933 := bbase (se 4 (by rfl) ⟨43587, by rfl⟩ : syracuseStep 464933 = 87175) (by norm_num)
theorem B530533 : Blo 271824 530533 := bbase (se 4 (by rfl) ⟨49737, by rfl⟩ : syracuseStep 530533 = 99475) (by norm_num)
theorem B727157 : Blo 271824 727157 := bbase (se 5 (by rfl) ⟨34085, by rfl⟩ : syracuseStep 727157 = 68171) (by norm_num)
theorem B465061 : Blo 271824 465061 := bbase (se 4 (by rfl) ⟨43599, by rfl⟩ : syracuseStep 465061 = 87199) (by norm_num)
theorem B694453 : Blo 271824 694453 := bbase (se 5 (by rfl) ⟨32552, by rfl⟩ : syracuseStep 694453 = 65105) (by norm_num)
theorem B465149 : Blo 271824 465149 := bbase (se 3 (by rfl) ⟨87215, by rfl⟩ : syracuseStep 465149 = 174431) (by norm_num)
theorem B661765 : Blo 271824 661765 := bbase (se 4 (by rfl) ⟨62040, by rfl⟩ : syracuseStep 661765 = 124081) (by norm_num)
theorem B694565 : Blo 271824 694565 := bbase (se 4 (by rfl) ⟨65115, by rfl⟩ : syracuseStep 694565 = 130231) (by norm_num)
theorem B465277 : Blo 271824 465277 := bbase (se 3 (by rfl) ⟨87239, by rfl⟩ : syracuseStep 465277 = 174479) (by norm_num)
theorem B924101 : Blo 271824 924101 := bbase (se 4 (by rfl) ⟨86634, by rfl⟩ : syracuseStep 924101 = 173269) (by norm_num)
theorem B465365 : Blo 271824 465365 := bbase (se 7 (by rfl) ⟨5453, by rfl⟩ : syracuseStep 465365 = 10907) (by norm_num)
theorem B694757 : Blo 271824 694757 := bbase (se 4 (by rfl) ⟨65133, by rfl⟩ : syracuseStep 694757 = 130267) (by norm_num)
theorem B662069 : Blo 271824 662069 := bbase (se 5 (by rfl) ⟨31034, by rfl⟩ : syracuseStep 662069 = 62069) (by norm_num)
theorem B989765 : Blo 271824 989765 := bbase (se 4 (by rfl) ⟨92790, by rfl⟩ : syracuseStep 989765 = 185581) (by norm_num)
theorem B695101 : Blo 271824 695101 := bbase (se 3 (by rfl) ⟨130331, by rfl⟩ : syracuseStep 695101 = 260663) (by norm_num)
theorem B662381 : Blo 271824 662381 := bbase (se 3 (by rfl) ⟨124196, by rfl⟩ : syracuseStep 662381 = 248393) (by norm_num)
theorem B924533 : Blo 271824 924533 := bbase (se 5 (by rfl) ⟨43337, by rfl⟩ : syracuseStep 924533 = 86675) (by norm_num)
theorem B1383317 : Blo 271824 1383317 := bbase (se 6 (by rfl) ⟨32421, by rfl⟩ : syracuseStep 1383317 = 64843) (by norm_num)
theorem B695213 : Blo 271824 695213 := bbase (se 3 (by rfl) ⟨130352, by rfl⟩ : syracuseStep 695213 = 260705) (by norm_num)
theorem B662573 : Blo 271824 662573 := bbase (se 3 (by rfl) ⟨124232, by rfl⟩ : syracuseStep 662573 = 248465) (by norm_num)
theorem B695405 : Blo 271824 695405 := bbase (se 3 (by rfl) ⟨130388, by rfl⟩ : syracuseStep 695405 = 260777) (by norm_num)
theorem B924965 : Blo 271824 924965 := bbase (se 4 (by rfl) ⟨86715, by rfl⟩ : syracuseStep 924965 = 173431) (by norm_num)
theorem B368005 : Blo 271824 368005 := bbase (se 4 (by rfl) ⟨34500, by rfl⟩ : syracuseStep 368005 = 69001) (by norm_num)
theorem B695749 : Blo 271824 695749 := bbase (se 4 (by rfl) ⟨65226, by rfl⟩ : syracuseStep 695749 = 130453) (by norm_num)
theorem B695861 : Blo 271824 695861 := bbase (se 5 (by rfl) ⟨32618, by rfl⟩ : syracuseStep 695861 = 65237) (by norm_num)
theorem B368221 : Blo 271824 368221 := bbase (se 3 (by rfl) ⟨69041, by rfl⟩ : syracuseStep 368221 = 138083) (by norm_num)
theorem B335549 : Blo 271824 335549 := bbase (se 3 (by rfl) ⟨62915, by rfl⟩ : syracuseStep 335549 = 125831) (by norm_num)
theorem B2989781 : Blo 271824 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B925397 : Blo 271824 925397 := bbase (se 7 (by rfl) ⟨10844, by rfl⟩ : syracuseStep 925397 = 21689) (by norm_num)
theorem B696053 : Blo 271824 696053 := bbase (se 5 (by rfl) ⟨32627, by rfl⟩ : syracuseStep 696053 = 65255) (by norm_num)
theorem B466741 : Blo 271824 466741 := bbase (se 5 (by rfl) ⟨21878, by rfl⟩ : syracuseStep 466741 = 43757) (by norm_num)
theorem B2957269 : Blo 271824 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B696397 : Blo 271824 696397 := bbase (se 3 (by rfl) ⟨130574, by rfl⟩ : syracuseStep 696397 = 261149) (by norm_num)
theorem B925829 : Blo 271824 925829 := bbase (se 4 (by rfl) ⟨86796, by rfl⟩ : syracuseStep 925829 = 173593) (by norm_num)
theorem B1384613 : Blo 271824 1384613 := bbase (se 4 (by rfl) ⟨129807, by rfl⟩ : syracuseStep 1384613 = 259615) (by norm_num)
theorem B696509 : Blo 271824 696509 := bbase (se 3 (by rfl) ⟨130595, by rfl⟩ : syracuseStep 696509 = 261191) (by norm_num)
theorem B532685 : Blo 271824 532685 := bbase (se 3 (by rfl) ⟨99878, by rfl⟩ : syracuseStep 532685 = 199757) (by norm_num)
theorem B2072789 : Blo 271824 2072789 := bbase (se 7 (by rfl) ⟨24290, by rfl⟩ : syracuseStep 2072789 = 48581) (by norm_num)
theorem B696701 : Blo 271824 696701 := bbase (se 3 (by rfl) ⟨130631, by rfl⟩ : syracuseStep 696701 = 261263) (by norm_num)
theorem B467453 : Blo 271824 467453 := bbase (se 3 (by rfl) ⟨87647, by rfl⟩ : syracuseStep 467453 = 175295) (by norm_num)
theorem B926261 : Blo 271824 926261 := bbase (se 5 (by rfl) ⟨43418, by rfl⟩ : syracuseStep 926261 = 86837) (by norm_num)
theorem B697045 : Blo 271824 697045 := bbase (se 7 (by rfl) ⟨8168, by rfl⟩ : syracuseStep 697045 = 16337) (by norm_num)
theorem B697157 : Blo 271824 697157 := bbase (se 4 (by rfl) ⟨65358, by rfl⟩ : syracuseStep 697157 = 130717) (by norm_num)
theorem B992101 : Blo 271824 992101 := bbase (se 4 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 992101 = 186019) (by norm_num)
theorem B926693 : Blo 271824 926693 := bbase (se 4 (by rfl) ⟨86877, by rfl⟩ : syracuseStep 926693 = 173755) (by norm_num)
theorem B697349 : Blo 271824 697349 := bbase (se 4 (by rfl) ⟨65376, by rfl⟩ : syracuseStep 697349 = 130753) (by norm_num)
theorem B5284885 : Blo 271824 5284885 := bbase (se 6 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 5284885 = 247729) (by norm_num)
theorem B894005 : Blo 271824 894005 := bbase (se 5 (by rfl) ⟨41906, by rfl⟩ : syracuseStep 894005 = 83813) (by norm_num)
theorem B2368693 : Blo 271824 2368693 := bbase (se 5 (by rfl) ⟨111032, by rfl⟩ : syracuseStep 2368693 = 222065) (by norm_num)
theorem B435461 : Blo 271824 435461 := bbase (se 4 (by rfl) ⟨40824, by rfl⟩ : syracuseStep 435461 = 81649) (by norm_num)
theorem B599381 : Blo 271824 599381 := bbase (se 12 (by rfl) ⟨219, by rfl⟩ : syracuseStep 599381 = 439) (by norm_num)
theorem B697693 : Blo 271824 697693 := bbase (se 3 (by rfl) ⟨130817, by rfl⟩ : syracuseStep 697693 = 261635) (by norm_num)
theorem B664949 : Blo 271824 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B927125 : Blo 271824 927125 := bbase (se 6 (by rfl) ⟨21729, by rfl⟩ : syracuseStep 927125 = 43459) (by norm_num)
theorem B1385909 : Blo 271824 1385909 := bbase (se 5 (by rfl) ⟨64964, by rfl⟩ : syracuseStep 1385909 = 129929) (by norm_num)
theorem B697805 : Blo 271824 697805 := bbase (se 3 (by rfl) ⟨130838, by rfl⟩ : syracuseStep 697805 = 261677) (by norm_num)
theorem B501373 : Blo 271824 501373 := bbase (se 3 (by rfl) ⟨94007, by rfl⟩ : syracuseStep 501373 = 188015) (by norm_num)
theorem B697997 : Blo 271824 697997 := bbase (se 3 (by rfl) ⟨130874, by rfl⟩ : syracuseStep 697997 = 261749) (by norm_num)
theorem B436013 : Blo 271824 436013 := bbase (se 3 (by rfl) ⟨81752, by rfl⟩ : syracuseStep 436013 = 163505) (by norm_num)
theorem B927557 : Blo 271824 927557 := bbase (se 4 (by rfl) ⟨86958, by rfl⟩ : syracuseStep 927557 = 173917) (by norm_num)
theorem B436045 : Blo 271824 436045 := bbase (se 3 (by rfl) ⟨81758, by rfl⟩ : syracuseStep 436045 = 163517) (by norm_num)
theorem B829397 : Blo 271824 829397 := bbase (se 7 (by rfl) ⟨9719, by rfl⟩ : syracuseStep 829397 = 19439) (by norm_num)
theorem B1321109 : Blo 271824 1321109 := bbase (se 6 (by rfl) ⟨30963, by rfl⟩ : syracuseStep 1321109 = 61927) (by norm_num)
theorem B1976501 : Blo 271824 1976501 := bbase (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) (by norm_num)
theorem B927989 : Blo 271824 927989 := bbase (se 5 (by rfl) ⟨43499, by rfl⟩ : syracuseStep 927989 = 86999) (by norm_num)
theorem B928421 : Blo 271824 928421 := bbase (se 4 (by rfl) ⟨87039, by rfl⟩ : syracuseStep 928421 = 174079) (by norm_num)
theorem B305833 : Blo 271824 305833 := bbase (se 2 (by rfl) ⟨114687, by rfl⟩ : syracuseStep 305833 = 229375) (by norm_num)
theorem B1387205 : Blo 271824 1387205 := bbase (se 4 (by rfl) ⟨130050, by rfl⟩ : syracuseStep 1387205 = 260101) (by norm_num)
theorem B305869 : Blo 271824 305869 := bbase (se 3 (by rfl) ⟨57350, by rfl⟩ : syracuseStep 305869 = 114701) (by norm_num)
theorem B436973 : Blo 271824 436973 := bbase (se 3 (by rfl) ⟨81932, by rfl⟩ : syracuseStep 436973 = 163865) (by norm_num)
theorem B305905 : Blo 271824 305905 := bbase (se 2 (by rfl) ⟨114714, by rfl⟩ : syracuseStep 305905 = 229429) (by norm_num)
theorem B305941 : Blo 271824 305941 := bbase (se 6 (by rfl) ⟨7170, by rfl⟩ : syracuseStep 305941 = 14341) (by norm_num)
theorem B305977 : Blo 271824 305977 := bbase (se 2 (by rfl) ⟨114741, by rfl⟩ : syracuseStep 305977 = 229483) (by norm_num)
theorem B306013 : Blo 271824 306013 := bbase (se 3 (by rfl) ⟨57377, by rfl⟩ : syracuseStep 306013 = 114755) (by norm_num)
theorem B1551221 : Blo 271824 1551221 := bbase (se 5 (by rfl) ⟨72713, by rfl⟩ : syracuseStep 1551221 = 145427) (by norm_num)
theorem B306049 : Blo 271824 306049 := bbase (se 2 (by rfl) ⟨114768, by rfl⟩ : syracuseStep 306049 = 229537) (by norm_num)
theorem B306085 : Blo 271824 306085 := bbase (se 4 (by rfl) ⟨28695, by rfl⟩ : syracuseStep 306085 = 57391) (by norm_num)
theorem B306121 : Blo 271824 306121 := bbase (se 2 (by rfl) ⟨114795, by rfl⟩ : syracuseStep 306121 = 229591) (by norm_num)
theorem B306157 : Blo 271824 306157 := bbase (se 3 (by rfl) ⟨57404, by rfl⟩ : syracuseStep 306157 = 114809) (by norm_num)
theorem B306193 : Blo 271824 306193 := bbase (se 2 (by rfl) ⟨114822, by rfl⟩ : syracuseStep 306193 = 229645) (by norm_num)
theorem B306229 : Blo 271824 306229 := bbase (se 5 (by rfl) ⟨14354, by rfl⟩ : syracuseStep 306229 = 28709) (by norm_num)
theorem B928853 : Blo 271824 928853 := bbase (se 8 (by rfl) ⟨5442, by rfl⟩ : syracuseStep 928853 = 10885) (by norm_num)
theorem B306265 : Blo 271824 306265 := bbase (se 2 (by rfl) ⟨114849, by rfl⟩ : syracuseStep 306265 = 229699) (by norm_num)
theorem B306301 : Blo 271824 306301 := bbase (se 3 (by rfl) ⟨57431, by rfl⟩ : syracuseStep 306301 = 114863) (by norm_num)
theorem B306337 : Blo 271824 306337 := bbase (se 2 (by rfl) ⟨114876, by rfl⟩ : syracuseStep 306337 = 229753) (by norm_num)
theorem B306373 : Blo 271824 306373 := bbase (se 4 (by rfl) ⟨28722, by rfl⟩ : syracuseStep 306373 = 57445) (by norm_num)
theorem B306409 : Blo 271824 306409 := bbase (se 2 (by rfl) ⟨114903, by rfl⟩ : syracuseStep 306409 = 229807) (by norm_num)
theorem B306445 : Blo 271824 306445 := bbase (se 3 (by rfl) ⟨57458, by rfl⟩ : syracuseStep 306445 = 114917) (by norm_num)
theorem B306481 : Blo 271824 306481 := bbase (se 2 (by rfl) ⟨114930, by rfl⟩ : syracuseStep 306481 = 229861) (by norm_num)
theorem B306517 : Blo 271824 306517 := bbase (se 11 (by rfl) ⟨224, by rfl⟩ : syracuseStep 306517 = 449) (by norm_num)
theorem B306553 : Blo 271824 306553 := bbase (se 2 (by rfl) ⟨114957, by rfl⟩ : syracuseStep 306553 = 229915) (by norm_num)
theorem B437653 : Blo 271824 437653 := bbase (se 6 (by rfl) ⟨10257, by rfl⟩ : syracuseStep 437653 = 20515) (by norm_num)
theorem B3943829 : Blo 271824 3943829 := bbase (se 6 (by rfl) ⟨92433, by rfl⟩ : syracuseStep 3943829 = 184867) (by norm_num)
theorem B306589 : Blo 271824 306589 := bbase (se 3 (by rfl) ⟨57485, by rfl⟩ : syracuseStep 306589 = 114971) (by norm_num)
theorem B1748405 : Blo 271824 1748405 := bbase (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) (by norm_num)
theorem B306625 : Blo 271824 306625 := bbase (se 2 (by rfl) ⟨114984, by rfl⟩ : syracuseStep 306625 = 229969) (by norm_num)
theorem B437717 : Blo 271824 437717 := bbase (se 7 (by rfl) ⟨5129, by rfl⟩ : syracuseStep 437717 = 10259) (by norm_num)
theorem B306661 : Blo 271824 306661 := bbase (se 4 (by rfl) ⟨28749, by rfl⟩ : syracuseStep 306661 = 57499) (by norm_num)
theorem B929285 : Blo 271824 929285 := bbase (se 4 (by rfl) ⟨87120, by rfl⟩ : syracuseStep 929285 = 174241) (by norm_num)
theorem B306697 : Blo 271824 306697 := bbase (se 2 (by rfl) ⟨115011, by rfl⟩ : syracuseStep 306697 = 230023) (by norm_num)
theorem B306733 : Blo 271824 306733 := bbase (se 3 (by rfl) ⟨57512, by rfl⟩ : syracuseStep 306733 = 115025) (by norm_num)
theorem B470573 : Blo 271824 470573 := bbase (se 3 (by rfl) ⟨88232, by rfl⟩ : syracuseStep 470573 = 176465) (by norm_num)
theorem B306769 : Blo 271824 306769 := bbase (se 2 (by rfl) ⟨115038, by rfl⟩ : syracuseStep 306769 = 230077) (by norm_num)
theorem B306805 : Blo 271824 306805 := bbase (se 5 (by rfl) ⟨14381, by rfl⟩ : syracuseStep 306805 = 28763) (by norm_num)
theorem B306841 : Blo 271824 306841 := bbase (se 2 (by rfl) ⟨115065, by rfl⟩ : syracuseStep 306841 = 230131) (by norm_num)
theorem B306877 : Blo 271824 306877 := bbase (se 3 (by rfl) ⟨57539, by rfl⟩ : syracuseStep 306877 = 115079) (by norm_num)
theorem B306913 : Blo 271824 306913 := bbase (se 2 (by rfl) ⟨115092, by rfl⟩ : syracuseStep 306913 = 230185) (by norm_num)
theorem B306949 : Blo 271824 306949 := bbase (se 4 (by rfl) ⟨28776, by rfl⟩ : syracuseStep 306949 = 57553) (by norm_num)
theorem B306985 : Blo 271824 306985 := bbase (se 2 (by rfl) ⟨115119, by rfl⟩ : syracuseStep 306985 = 230239) (by norm_num)
theorem B307021 : Blo 271824 307021 := bbase (se 3 (by rfl) ⟨57566, by rfl⟩ : syracuseStep 307021 = 115133) (by norm_num)
theorem B307057 : Blo 271824 307057 := bbase (se 2 (by rfl) ⟨115146, by rfl⟩ : syracuseStep 307057 = 230293) (by norm_num)
theorem B307093 : Blo 271824 307093 := bbase (se 6 (by rfl) ⟨7197, by rfl⟩ : syracuseStep 307093 = 14395) (by norm_num)
theorem B929717 : Blo 271824 929717 := bbase (se 5 (by rfl) ⟨43580, by rfl⟩ : syracuseStep 929717 = 87161) (by norm_num)
theorem B307129 : Blo 271824 307129 := bbase (se 2 (by rfl) ⟨115173, by rfl⟩ : syracuseStep 307129 = 230347) (by norm_num)
theorem B1388501 : Blo 271824 1388501 := bbase (se 7 (by rfl) ⟨16271, by rfl⟩ : syracuseStep 1388501 = 32543) (by norm_num)
theorem B307165 : Blo 271824 307165 := bbase (se 3 (by rfl) ⟨57593, by rfl⟩ : syracuseStep 307165 = 115187) (by norm_num)
theorem B307201 : Blo 271824 307201 := bbase (se 2 (by rfl) ⟨115200, by rfl⟩ : syracuseStep 307201 = 230401) (by norm_num)
theorem B1552405 : Blo 271824 1552405 := bbase (se 6 (by rfl) ⟨36384, by rfl⟩ : syracuseStep 1552405 = 72769) (by norm_num)
theorem B307237 : Blo 271824 307237 := bbase (se 4 (by rfl) ⟨28803, by rfl⟩ : syracuseStep 307237 = 57607) (by norm_num)
theorem B307273 : Blo 271824 307273 := bbase (se 2 (by rfl) ⟨115227, by rfl⟩ : syracuseStep 307273 = 230455) (by norm_num)
theorem B307309 : Blo 271824 307309 := bbase (se 3 (by rfl) ⟨57620, by rfl⟩ : syracuseStep 307309 = 115241) (by norm_num)
theorem B307345 : Blo 271824 307345 := bbase (se 2 (by rfl) ⟨115254, by rfl⟩ : syracuseStep 307345 = 230509) (by norm_num)
theorem B307381 : Blo 271824 307381 := bbase (se 5 (by rfl) ⟨14408, by rfl⟩ : syracuseStep 307381 = 28817) (by norm_num)
theorem B307417 : Blo 271824 307417 := bbase (se 2 (by rfl) ⟨115281, by rfl⟩ : syracuseStep 307417 = 230563) (by norm_num)
theorem B307453 : Blo 271824 307453 := bbase (se 3 (by rfl) ⟨57647, by rfl⟩ : syracuseStep 307453 = 115295) (by norm_num)
theorem B307489 : Blo 271824 307489 := bbase (se 2 (by rfl) ⟨115308, by rfl⟩ : syracuseStep 307489 = 230617) (by norm_num)
theorem B307525 : Blo 271824 307525 := bbase (se 4 (by rfl) ⟨28830, by rfl⟩ : syracuseStep 307525 = 57661) (by norm_num)
theorem B930149 : Blo 271824 930149 := bbase (se 4 (by rfl) ⟨87201, by rfl⟩ : syracuseStep 930149 = 174403) (by norm_num)
theorem B307561 : Blo 271824 307561 := bbase (se 2 (by rfl) ⟨115335, by rfl⟩ : syracuseStep 307561 = 230671) (by norm_num)
theorem B307597 : Blo 271824 307597 := bbase (se 3 (by rfl) ⟨57674, by rfl⟩ : syracuseStep 307597 = 115349) (by norm_num)
theorem B307633 : Blo 271824 307633 := bbase (se 2 (by rfl) ⟨115362, by rfl⟩ : syracuseStep 307633 = 230725) (by norm_num)
theorem B307669 : Blo 271824 307669 := bbase (se 7 (by rfl) ⟨3605, by rfl⟩ : syracuseStep 307669 = 7211) (by norm_num)
theorem B307705 : Blo 271824 307705 := bbase (se 2 (by rfl) ⟨115389, by rfl⟩ : syracuseStep 307705 = 230779) (by norm_num)
theorem B307741 : Blo 271824 307741 := bbase (se 3 (by rfl) ⟨57701, by rfl⟩ : syracuseStep 307741 = 115403) (by norm_num)
theorem B1487413 : Blo 271824 1487413 := bbase (se 5 (by rfl) ⟨69722, by rfl⟩ : syracuseStep 1487413 = 139445) (by norm_num)
theorem B307777 : Blo 271824 307777 := bbase (se 2 (by rfl) ⟨115416, by rfl⟩ : syracuseStep 307777 = 230833) (by norm_num)
theorem B307813 : Blo 271824 307813 := bbase (se 4 (by rfl) ⟨28857, by rfl⟩ : syracuseStep 307813 = 57715) (by norm_num)
theorem B307849 : Blo 271824 307849 := bbase (se 2 (by rfl) ⟨115443, by rfl⟩ : syracuseStep 307849 = 230887) (by norm_num)
theorem B307885 : Blo 271824 307885 := bbase (se 3 (by rfl) ⟨57728, by rfl⟩ : syracuseStep 307885 = 115457) (by norm_num)
theorem B307921 : Blo 271824 307921 := bbase (se 2 (by rfl) ⟨115470, by rfl⟩ : syracuseStep 307921 = 230941) (by norm_num)
theorem B307957 : Blo 271824 307957 := bbase (se 5 (by rfl) ⟨14435, by rfl⟩ : syracuseStep 307957 = 28871) (by norm_num)
theorem B439037 : Blo 271824 439037 := bbase (se 3 (by rfl) ⟨82319, by rfl⟩ : syracuseStep 439037 = 164639) (by norm_num)
theorem B930581 : Blo 271824 930581 := bbase (se 6 (by rfl) ⟨21810, by rfl⟩ : syracuseStep 930581 = 43621) (by norm_num)
theorem B307993 : Blo 271824 307993 := bbase (se 2 (by rfl) ⟨115497, by rfl⟩ : syracuseStep 307993 = 230995) (by norm_num)
theorem B308029 : Blo 271824 308029 := bbase (se 3 (by rfl) ⟨57755, by rfl⟩ : syracuseStep 308029 = 115511) (by norm_num)
theorem B8926037 : Blo 271824 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B308065 : Blo 271824 308065 := bbase (se 2 (by rfl) ⟨115524, by rfl⟩ : syracuseStep 308065 = 231049) (by norm_num)
theorem B308101 : Blo 271824 308101 := bbase (se 4 (by rfl) ⟨28884, by rfl⟩ : syracuseStep 308101 = 57769) (by norm_num)
theorem B1880981 : Blo 271824 1880981 := bbase (se 6 (by rfl) ⟨44085, by rfl⟩ : syracuseStep 1880981 = 88171) (by norm_num)
theorem B308137 : Blo 271824 308137 := bbase (se 2 (by rfl) ⟨115551, by rfl⟩ : syracuseStep 308137 = 231103) (by norm_num)
theorem B439229 : Blo 271824 439229 := bbase (se 3 (by rfl) ⟨82355, by rfl⟩ : syracuseStep 439229 = 164711) (by norm_num)
theorem B308173 : Blo 271824 308173 := bbase (se 3 (by rfl) ⟨57782, by rfl⟩ : syracuseStep 308173 = 115565) (by norm_num)
theorem B308209 : Blo 271824 308209 := bbase (se 2 (by rfl) ⟨115578, by rfl⟩ : syracuseStep 308209 = 231157) (by norm_num)
theorem B308245 : Blo 271824 308245 := bbase (se 6 (by rfl) ⟨7224, by rfl⟩ : syracuseStep 308245 = 14449) (by norm_num)
theorem B308281 : Blo 271824 308281 := bbase (se 2 (by rfl) ⟨115605, by rfl⟩ : syracuseStep 308281 = 231211) (by norm_num)
theorem B439357 : Blo 271824 439357 := bbase (se 3 (by rfl) ⟨82379, by rfl⟩ : syracuseStep 439357 = 164759) (by norm_num)
theorem B308317 : Blo 271824 308317 := bbase (se 3 (by rfl) ⟨57809, by rfl⟩ : syracuseStep 308317 = 115619) (by norm_num)
theorem B308353 : Blo 271824 308353 := bbase (se 2 (by rfl) ⟨115632, by rfl⟩ : syracuseStep 308353 = 231265) (by norm_num)
theorem B701581 : Blo 271824 701581 := bbase (se 3 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 701581 = 263093) (by norm_num)
theorem B308389 : Blo 271824 308389 := bbase (se 4 (by rfl) ⟨28911, by rfl⟩ : syracuseStep 308389 = 57823) (by norm_num)
theorem B308425 : Blo 271824 308425 := bbase (se 2 (by rfl) ⟨115659, by rfl⟩ : syracuseStep 308425 = 231319) (by norm_num)
theorem B1389797 : Blo 271824 1389797 := bbase (se 4 (by rfl) ⟨130293, by rfl⟩ : syracuseStep 1389797 = 260587) (by norm_num)
theorem B308461 : Blo 271824 308461 := bbase (se 3 (by rfl) ⟨57836, by rfl⟩ : syracuseStep 308461 = 115673) (by norm_num)
theorem B308497 : Blo 271824 308497 := bbase (se 2 (by rfl) ⟨115686, by rfl⟩ : syracuseStep 308497 = 231373) (by norm_num)
theorem B308533 : Blo 271824 308533 := bbase (se 5 (by rfl) ⟨14462, by rfl⟩ : syracuseStep 308533 = 28925) (by norm_num)
theorem B308569 : Blo 271824 308569 := bbase (se 2 (by rfl) ⟨115713, by rfl⟩ : syracuseStep 308569 = 231427) (by norm_num)
theorem B308605 : Blo 271824 308605 := bbase (se 3 (by rfl) ⟨57863, by rfl⟩ : syracuseStep 308605 = 115727) (by norm_num)
theorem B308641 : Blo 271824 308641 := bbase (se 2 (by rfl) ⟨115740, by rfl⟩ : syracuseStep 308641 = 231481) (by norm_num)
theorem B308677 : Blo 271824 308677 := bbase (se 4 (by rfl) ⟨28938, by rfl⟩ : syracuseStep 308677 = 57877) (by norm_num)
theorem B308713 : Blo 271824 308713 := bbase (se 2 (by rfl) ⟨115767, by rfl⟩ : syracuseStep 308713 = 231535) (by norm_num)
theorem B308749 : Blo 271824 308749 := bbase (se 3 (by rfl) ⟨57890, by rfl⟩ : syracuseStep 308749 = 115781) (by norm_num)
theorem B308785 : Blo 271824 308785 := bbase (se 2 (by rfl) ⟨115794, by rfl⟩ : syracuseStep 308785 = 231589) (by norm_num)
theorem B308821 : Blo 271824 308821 := bbase (se 8 (by rfl) ⟨1809, by rfl⟩ : syracuseStep 308821 = 3619) (by norm_num)
theorem B308857 : Blo 271824 308857 := bbase (se 2 (by rfl) ⟨115821, by rfl⟩ : syracuseStep 308857 = 231643) (by norm_num)
theorem B472717 : Blo 271824 472717 := bbase (se 3 (by rfl) ⟨88634, by rfl⟩ : syracuseStep 472717 = 177269) (by norm_num)
theorem B308893 : Blo 271824 308893 := bbase (se 3 (by rfl) ⟨57917, by rfl⟩ : syracuseStep 308893 = 115835) (by norm_num)
theorem B439997 : Blo 271824 439997 := bbase (se 3 (by rfl) ⟨82499, by rfl⟩ : syracuseStep 439997 = 164999) (by norm_num)
theorem B308929 : Blo 271824 308929 := bbase (se 2 (by rfl) ⟨115848, by rfl⟩ : syracuseStep 308929 = 231697) (by norm_num)
theorem B308965 : Blo 271824 308965 := bbase (se 4 (by rfl) ⟨28965, by rfl⟩ : syracuseStep 308965 = 57931) (by norm_num)
theorem B309001 : Blo 271824 309001 := bbase (se 2 (by rfl) ⟨115875, by rfl⟩ : syracuseStep 309001 = 231751) (by norm_num)
theorem B309037 : Blo 271824 309037 := bbase (se 3 (by rfl) ⟨57944, by rfl⟩ : syracuseStep 309037 = 115889) (by norm_num)
theorem B309073 : Blo 271824 309073 := bbase (se 2 (by rfl) ⟨115902, by rfl⟩ : syracuseStep 309073 = 231805) (by norm_num)
theorem B309109 : Blo 271824 309109 := bbase (se 5 (by rfl) ⟨14489, by rfl⟩ : syracuseStep 309109 = 28979) (by norm_num)
theorem B309145 : Blo 271824 309145 := bbase (se 2 (by rfl) ⟨115929, by rfl⟩ : syracuseStep 309145 = 231859) (by norm_num)
theorem B309181 : Blo 271824 309181 := bbase (se 3 (by rfl) ⟨57971, by rfl⟩ : syracuseStep 309181 = 115943) (by norm_num)
theorem B1554389 : Blo 271824 1554389 := bbase (se 7 (by rfl) ⟨18215, by rfl⟩ : syracuseStep 1554389 = 36431) (by norm_num)
theorem B309217 : Blo 271824 309217 := bbase (se 2 (by rfl) ⟨115956, by rfl⟩ : syracuseStep 309217 = 231913) (by norm_num)
theorem B931829 : Blo 271824 931829 := bbase (se 5 (by rfl) ⟨43679, by rfl⟩ : syracuseStep 931829 = 87359) (by norm_num)
theorem B309253 : Blo 271824 309253 := bbase (se 4 (by rfl) ⟨28992, by rfl⟩ : syracuseStep 309253 = 57985) (by norm_num)
theorem B309289 : Blo 271824 309289 := bbase (se 2 (by rfl) ⟨115983, by rfl⟩ : syracuseStep 309289 = 231967) (by norm_num)
theorem B309325 : Blo 271824 309325 := bbase (se 3 (by rfl) ⟨57998, by rfl⟩ : syracuseStep 309325 = 115997) (by norm_num)
theorem B309361 : Blo 271824 309361 := bbase (se 2 (by rfl) ⟨116010, by rfl⟩ : syracuseStep 309361 = 232021) (by norm_num)
theorem B1423493 : Blo 271824 1423493 := bbase (se 4 (by rfl) ⟨133452, by rfl⟩ : syracuseStep 1423493 = 266905) (by norm_num)
theorem B440453 : Blo 271824 440453 := bbase (se 4 (by rfl) ⟨41292, by rfl⟩ : syracuseStep 440453 = 82585) (by norm_num)
theorem B309397 : Blo 271824 309397 := bbase (se 6 (by rfl) ⟨7251, by rfl⟩ : syracuseStep 309397 = 14503) (by norm_num)
theorem B309433 : Blo 271824 309433 := bbase (se 2 (by rfl) ⟨116037, by rfl⟩ : syracuseStep 309433 = 232075) (by norm_num)
theorem B407741 : Blo 271824 407741 := bbase (se 3 (by rfl) ⟨76451, by rfl⟩ : syracuseStep 407741 = 152903) (by norm_num)
theorem B407765 : Blo 271824 407765 := bbase (se 7 (by rfl) ⟨4778, by rfl⟩ : syracuseStep 407765 = 9557) (by norm_num)
theorem B309469 : Blo 271824 309469 := bbase (se 3 (by rfl) ⟨58025, by rfl⟩ : syracuseStep 309469 = 116051) (by norm_num)
theorem B407789 : Blo 271824 407789 := bbase (se 3 (by rfl) ⟨76460, by rfl⟩ : syracuseStep 407789 = 152921) (by norm_num)
theorem B309505 : Blo 271824 309505 := bbase (se 2 (by rfl) ⟨116064, by rfl⟩ : syracuseStep 309505 = 232129) (by norm_num)
theorem B407813 : Blo 271824 407813 := bbase (se 4 (by rfl) ⟨38232, by rfl⟩ : syracuseStep 407813 = 76465) (by norm_num)
theorem B375053 : Blo 271824 375053 := bbase (se 3 (by rfl) ⟨70322, by rfl⟩ : syracuseStep 375053 = 140645) (by norm_num)
theorem B407837 : Blo 271824 407837 := bbase (se 3 (by rfl) ⟨76469, by rfl⟩ : syracuseStep 407837 = 152939) (by norm_num)
theorem B309541 : Blo 271824 309541 := bbase (se 4 (by rfl) ⟨29019, by rfl⟩ : syracuseStep 309541 = 58039) (by norm_num)
theorem B407861 : Blo 271824 407861 := bbase (se 5 (by rfl) ⟨19118, by rfl⟩ : syracuseStep 407861 = 38237) (by norm_num)
theorem B309577 : Blo 271824 309577 := bbase (se 2 (by rfl) ⟨116091, by rfl⟩ : syracuseStep 309577 = 232183) (by norm_num)
theorem B407885 : Blo 271824 407885 := bbase (se 3 (by rfl) ⟨76478, by rfl⟩ : syracuseStep 407885 = 152957) (by norm_num)
theorem B407909 : Blo 271824 407909 := bbase (se 4 (by rfl) ⟨38241, by rfl⟩ : syracuseStep 407909 = 76483) (by norm_num)
theorem B440677 : Blo 271824 440677 := bbase (se 4 (by rfl) ⟨41313, by rfl⟩ : syracuseStep 440677 = 82627) (by norm_num)
theorem B1325413 : Blo 271824 1325413 := bbase (se 4 (by rfl) ⟨124257, by rfl⟩ : syracuseStep 1325413 = 248515) (by norm_num)
theorem B309613 : Blo 271824 309613 := bbase (se 3 (by rfl) ⟨58052, by rfl⟩ : syracuseStep 309613 = 116105) (by norm_num)
theorem B407933 : Blo 271824 407933 := bbase (se 3 (by rfl) ⟨76487, by rfl⟩ : syracuseStep 407933 = 152975) (by norm_num)
theorem B309649 : Blo 271824 309649 := bbase (se 2 (by rfl) ⟨116118, by rfl⟩ : syracuseStep 309649 = 232237) (by norm_num)
theorem B407957 : Blo 271824 407957 := bbase (se 6 (by rfl) ⟨9561, by rfl⟩ : syracuseStep 407957 = 19123) (by norm_num)
theorem B440741 : Blo 271824 440741 := bbase (se 4 (by rfl) ⟨41319, by rfl⟩ : syracuseStep 440741 = 82639) (by norm_num)
theorem B407981 : Blo 271824 407981 := bbase (se 3 (by rfl) ⟨76496, by rfl⟩ : syracuseStep 407981 = 152993) (by norm_num)
theorem B309685 : Blo 271824 309685 := bbase (se 5 (by rfl) ⟨14516, by rfl⟩ : syracuseStep 309685 = 29033) (by norm_num)
theorem B408005 : Blo 271824 408005 := bbase (se 4 (by rfl) ⟨38250, by rfl⟩ : syracuseStep 408005 = 76501) (by norm_num)
theorem B309721 : Blo 271824 309721 := bbase (se 2 (by rfl) ⟨116145, by rfl⟩ : syracuseStep 309721 = 232291) (by norm_num)
theorem B408029 : Blo 271824 408029 := bbase (se 3 (by rfl) ⟨76505, by rfl⟩ : syracuseStep 408029 = 153011) (by norm_num)
theorem B408053 : Blo 271824 408053 := bbase (se 5 (by rfl) ⟨19127, by rfl⟩ : syracuseStep 408053 = 38255) (by norm_num)
theorem B1391093 : Blo 271824 1391093 := bbase (se 5 (by rfl) ⟨65207, by rfl⟩ : syracuseStep 1391093 = 130415) (by norm_num)
theorem B309757 : Blo 271824 309757 := bbase (se 3 (by rfl) ⟨58079, by rfl⟩ : syracuseStep 309757 = 116159) (by norm_num)
theorem B408077 : Blo 271824 408077 := bbase (se 3 (by rfl) ⟨76514, by rfl⟩ : syracuseStep 408077 = 153029) (by norm_num)
theorem B309793 : Blo 271824 309793 := bbase (se 2 (by rfl) ⟨116172, by rfl⟩ : syracuseStep 309793 = 232345) (by norm_num)
theorem B408101 : Blo 271824 408101 := bbase (se 4 (by rfl) ⟨38259, by rfl⟩ : syracuseStep 408101 = 76519) (by norm_num)
theorem B440869 : Blo 271824 440869 := bbase (se 4 (by rfl) ⟨41331, by rfl⟩ : syracuseStep 440869 = 82663) (by norm_num)
theorem B408125 : Blo 271824 408125 := bbase (se 3 (by rfl) ⟨76523, by rfl⟩ : syracuseStep 408125 = 153047) (by norm_num)
theorem B309829 : Blo 271824 309829 := bbase (se 4 (by rfl) ⟨29046, by rfl⟩ : syracuseStep 309829 = 58093) (by norm_num)
theorem B408149 : Blo 271824 408149 := bbase (se 8 (by rfl) ⟨2391, by rfl⟩ : syracuseStep 408149 = 4783) (by norm_num)
theorem B309865 : Blo 271824 309865 := bbase (se 2 (by rfl) ⟨116199, by rfl⟩ : syracuseStep 309865 = 232399) (by norm_num)
theorem B408173 : Blo 271824 408173 := bbase (se 3 (by rfl) ⟨76532, by rfl⟩ : syracuseStep 408173 = 153065) (by norm_num)
theorem B408197 : Blo 271824 408197 := bbase (se 4 (by rfl) ⟨38268, by rfl⟩ : syracuseStep 408197 = 76537) (by norm_num)
theorem B309901 : Blo 271824 309901 := bbase (se 3 (by rfl) ⟨58106, by rfl⟩ : syracuseStep 309901 = 116213) (by norm_num)
theorem B408221 : Blo 271824 408221 := bbase (se 3 (by rfl) ⟨76541, by rfl⟩ : syracuseStep 408221 = 153083) (by norm_num)
theorem B309937 : Blo 271824 309937 := bbase (se 2 (by rfl) ⟨116226, by rfl⟩ : syracuseStep 309937 = 232453) (by norm_num)
theorem B408245 : Blo 271824 408245 := bbase (se 5 (by rfl) ⟨19136, by rfl⟩ : syracuseStep 408245 = 38273) (by norm_num)
theorem B408269 : Blo 271824 408269 := bbase (se 3 (by rfl) ⟨76550, by rfl⟩ : syracuseStep 408269 = 153101) (by norm_num)
theorem B309973 : Blo 271824 309973 := bbase (se 7 (by rfl) ⟨3632, by rfl⟩ : syracuseStep 309973 = 7265) (by norm_num)
theorem B408293 : Blo 271824 408293 := bbase (se 4 (by rfl) ⟨38277, by rfl⟩ : syracuseStep 408293 = 76555) (by norm_num)
theorem B310009 : Blo 271824 310009 := bbase (se 2 (by rfl) ⟨116253, by rfl⟩ : syracuseStep 310009 = 232507) (by norm_num)
theorem B408317 : Blo 271824 408317 := bbase (se 3 (by rfl) ⟨76559, by rfl⟩ : syracuseStep 408317 = 153119) (by norm_num)
theorem B408341 : Blo 271824 408341 := bbase (se 6 (by rfl) ⟨9570, by rfl⟩ : syracuseStep 408341 = 19141) (by norm_num)
theorem B310045 : Blo 271824 310045 := bbase (se 3 (by rfl) ⟨58133, by rfl⟩ : syracuseStep 310045 = 116267) (by norm_num)
theorem B408365 : Blo 271824 408365 := bbase (se 3 (by rfl) ⟨76568, by rfl⟩ : syracuseStep 408365 = 153137) (by norm_num)
theorem B310081 : Blo 271824 310081 := bbase (se 2 (by rfl) ⟨116280, by rfl⟩ : syracuseStep 310081 = 232561) (by norm_num)
theorem B408389 : Blo 271824 408389 := bbase (se 4 (by rfl) ⟨38286, by rfl⟩ : syracuseStep 408389 = 76573) (by norm_num)
theorem B408413 : Blo 271824 408413 := bbase (se 3 (by rfl) ⟨76577, by rfl⟩ : syracuseStep 408413 = 153155) (by norm_num)
theorem B310117 : Blo 271824 310117 := bbase (se 4 (by rfl) ⟨29073, by rfl⟩ : syracuseStep 310117 = 58147) (by norm_num)
theorem B408437 : Blo 271824 408437 := bbase (se 5 (by rfl) ⟨19145, by rfl⟩ : syracuseStep 408437 = 38291) (by norm_num)
theorem B1162117 : Blo 271824 1162117 := bbase (se 4 (by rfl) ⟨108948, by rfl⟩ : syracuseStep 1162117 = 217897) (by norm_num)
theorem B310153 : Blo 271824 310153 := bbase (se 2 (by rfl) ⟨116307, by rfl⟩ : syracuseStep 310153 = 232615) (by norm_num)
theorem B408461 : Blo 271824 408461 := bbase (se 3 (by rfl) ⟨76586, by rfl⟩ : syracuseStep 408461 = 153173) (by norm_num)
theorem B408485 : Blo 271824 408485 := bbase (se 4 (by rfl) ⟨38295, by rfl⟩ : syracuseStep 408485 = 76591) (by norm_num)
theorem B310189 : Blo 271824 310189 := bbase (se 3 (by rfl) ⟨58160, by rfl⟩ : syracuseStep 310189 = 116321) (by norm_num)
theorem B408509 : Blo 271824 408509 := bbase (se 3 (by rfl) ⟨76595, by rfl⟩ : syracuseStep 408509 = 153191) (by norm_num)
theorem B310225 : Blo 271824 310225 := bbase (se 2 (by rfl) ⟨116334, by rfl⟩ : syracuseStep 310225 = 232669) (by norm_num)
theorem B408533 : Blo 271824 408533 := bbase (se 7 (by rfl) ⟨4787, by rfl⟩ : syracuseStep 408533 = 9575) (by norm_num)
theorem B408557 : Blo 271824 408557 := bbase (se 3 (by rfl) ⟨76604, by rfl⟩ : syracuseStep 408557 = 153209) (by norm_num)
theorem B703477 : Blo 271824 703477 := bbase (se 5 (by rfl) ⟨32975, by rfl⟩ : syracuseStep 703477 = 65951) (by norm_num)
theorem B310261 : Blo 271824 310261 := bbase (se 5 (by rfl) ⟨14543, by rfl⟩ : syracuseStep 310261 = 29087) (by norm_num)
theorem B408581 : Blo 271824 408581 := bbase (se 4 (by rfl) ⟨38304, by rfl⟩ : syracuseStep 408581 = 76609) (by norm_num)
theorem B310297 : Blo 271824 310297 := bbase (se 2 (by rfl) ⟨116361, by rfl⟩ : syracuseStep 310297 = 232723) (by norm_num)
theorem B408605 : Blo 271824 408605 := bbase (se 3 (by rfl) ⟨76613, by rfl⟩ : syracuseStep 408605 = 153227) (by norm_num)
theorem B408629 : Blo 271824 408629 := bbase (se 5 (by rfl) ⟨19154, by rfl⟩ : syracuseStep 408629 = 38309) (by norm_num)
theorem B408653 : Blo 271824 408653 := bbase (se 3 (by rfl) ⟨76622, by rfl⟩ : syracuseStep 408653 = 153245) (by norm_num)
theorem B408677 : Blo 271824 408677 := bbase (se 4 (by rfl) ⟨38313, by rfl⟩ : syracuseStep 408677 = 76627) (by norm_num)
theorem B408701 : Blo 271824 408701 := bbase (se 3 (by rfl) ⟨76631, by rfl⟩ : syracuseStep 408701 = 153263) (by norm_num)
theorem B408725 : Blo 271824 408725 := bbase (se 6 (by rfl) ⟨9579, by rfl⟩ : syracuseStep 408725 = 19159) (by norm_num)
theorem B408749 : Blo 271824 408749 := bbase (se 3 (by rfl) ⟨76640, by rfl⟩ : syracuseStep 408749 = 153281) (by norm_num)
theorem B408773 : Blo 271824 408773 := bbase (se 4 (by rfl) ⟨38322, by rfl⟩ : syracuseStep 408773 = 76645) (by norm_num)
theorem B408797 : Blo 271824 408797 := bbase (se 3 (by rfl) ⟨76649, by rfl⟩ : syracuseStep 408797 = 153299) (by norm_num)
theorem B408821 : Blo 271824 408821 := bbase (se 5 (by rfl) ⟨19163, by rfl⟩ : syracuseStep 408821 = 38327) (by norm_num)
theorem B1129733 : Blo 271824 1129733 := bbase (se 4 (by rfl) ⟨105912, by rfl⟩ : syracuseStep 1129733 = 211825) (by norm_num)
theorem B408845 : Blo 271824 408845 := bbase (se 3 (by rfl) ⟨76658, by rfl⟩ : syracuseStep 408845 = 153317) (by norm_num)
theorem B408869 : Blo 271824 408869 := bbase (se 4 (by rfl) ⟨38331, by rfl⟩ : syracuseStep 408869 = 76663) (by norm_num)
theorem B408893 : Blo 271824 408893 := bbase (se 3 (by rfl) ⟨76667, by rfl⟩ : syracuseStep 408893 = 153335) (by norm_num)
theorem B408917 : Blo 271824 408917 := bbase (se 11 (by rfl) ⟨299, by rfl⟩ : syracuseStep 408917 = 599) (by norm_num)
theorem B408941 : Blo 271824 408941 := bbase (se 3 (by rfl) ⟨76676, by rfl⟩ : syracuseStep 408941 = 153353) (by norm_num)
theorem B408965 : Blo 271824 408965 := bbase (se 4 (by rfl) ⟨38340, by rfl⟩ : syracuseStep 408965 = 76681) (by norm_num)
theorem B408989 : Blo 271824 408989 := bbase (se 3 (by rfl) ⟨76685, by rfl⟩ : syracuseStep 408989 = 153371) (by norm_num)
theorem B409013 : Blo 271824 409013 := bbase (se 5 (by rfl) ⟨19172, by rfl⟩ : syracuseStep 409013 = 38345) (by norm_num)
theorem B409037 : Blo 271824 409037 := bbase (se 3 (by rfl) ⟨76694, by rfl⟩ : syracuseStep 409037 = 153389) (by norm_num)
theorem B409061 : Blo 271824 409061 := bbase (se 4 (by rfl) ⟨38349, by rfl⟩ : syracuseStep 409061 = 76699) (by norm_num)
theorem B441845 : Blo 271824 441845 := bbase (se 5 (by rfl) ⟨20711, by rfl⟩ : syracuseStep 441845 = 41423) (by norm_num)
theorem B409085 : Blo 271824 409085 := bbase (se 3 (by rfl) ⟨76703, by rfl⟩ : syracuseStep 409085 = 153407) (by norm_num)
theorem B409109 : Blo 271824 409109 := bbase (se 6 (by rfl) ⟨9588, by rfl⟩ : syracuseStep 409109 = 19177) (by norm_num)
theorem B409133 : Blo 271824 409133 := bbase (se 3 (by rfl) ⟨76712, by rfl⟩ : syracuseStep 409133 = 153425) (by norm_num)
theorem B409157 : Blo 271824 409157 := bbase (se 4 (by rfl) ⟨38358, by rfl⟩ : syracuseStep 409157 = 76717) (by norm_num)
theorem B409181 : Blo 271824 409181 := bbase (se 3 (by rfl) ⟨76721, by rfl⟩ : syracuseStep 409181 = 153443) (by norm_num)
theorem B409205 : Blo 271824 409205 := bbase (se 5 (by rfl) ⟨19181, by rfl⟩ : syracuseStep 409205 = 38363) (by norm_num)
theorem B409229 : Blo 271824 409229 := bbase (se 3 (by rfl) ⟨76730, by rfl⟩ : syracuseStep 409229 = 153461) (by norm_num)
theorem B442013 : Blo 271824 442013 := bbase (se 3 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 442013 = 165755) (by norm_num)
theorem B409253 : Blo 271824 409253 := bbase (se 4 (by rfl) ⟨38367, by rfl⟩ : syracuseStep 409253 = 76735) (by norm_num)
theorem B409277 : Blo 271824 409277 := bbase (se 3 (by rfl) ⟨76739, by rfl⟩ : syracuseStep 409277 = 153479) (by norm_num)
theorem B409301 : Blo 271824 409301 := bbase (se 7 (by rfl) ⟨4796, by rfl⟩ : syracuseStep 409301 = 9593) (by norm_num)
theorem B409325 : Blo 271824 409325 := bbase (se 3 (by rfl) ⟨76748, by rfl⟩ : syracuseStep 409325 = 153497) (by norm_num)
theorem B409349 : Blo 271824 409349 := bbase (se 4 (by rfl) ⟨38376, by rfl⟩ : syracuseStep 409349 = 76753) (by norm_num)
theorem B1392389 : Blo 271824 1392389 := bbase (se 4 (by rfl) ⟨130536, by rfl⟩ : syracuseStep 1392389 = 261073) (by norm_num)
theorem B409373 : Blo 271824 409373 := bbase (se 3 (by rfl) ⟨76757, by rfl⟩ : syracuseStep 409373 = 153515) (by norm_num)
theorem B409397 : Blo 271824 409397 := bbase (se 5 (by rfl) ⟨19190, by rfl⟩ : syracuseStep 409397 = 38381) (by norm_num)
theorem B2080565 : Blo 271824 2080565 := bbase (se 5 (by rfl) ⟨97526, by rfl⟩ : syracuseStep 2080565 = 195053) (by norm_num)
theorem B409421 : Blo 271824 409421 := bbase (se 3 (by rfl) ⟨76766, by rfl⟩ : syracuseStep 409421 = 153533) (by norm_num)
theorem B409445 : Blo 271824 409445 := bbase (se 4 (by rfl) ⟨38385, by rfl⟩ : syracuseStep 409445 = 76771) (by norm_num)
theorem B409469 : Blo 271824 409469 := bbase (se 3 (by rfl) ⟨76775, by rfl⟩ : syracuseStep 409469 = 153551) (by norm_num)
theorem B409493 : Blo 271824 409493 := bbase (se 6 (by rfl) ⟨9597, by rfl⟩ : syracuseStep 409493 = 19195) (by norm_num)
theorem B409517 : Blo 271824 409517 := bbase (se 3 (by rfl) ⟨76784, by rfl⟩ : syracuseStep 409517 = 153569) (by norm_num)
theorem B409541 : Blo 271824 409541 := bbase (se 4 (by rfl) ⟨38394, by rfl⟩ : syracuseStep 409541 = 76789) (by norm_num)
theorem B409565 : Blo 271824 409565 := bbase (se 3 (by rfl) ⟨76793, by rfl⟩ : syracuseStep 409565 = 153587) (by norm_num)
theorem B409589 : Blo 271824 409589 := bbase (se 5 (by rfl) ⟨19199, by rfl⟩ : syracuseStep 409589 = 38399) (by norm_num)
theorem B409613 : Blo 271824 409613 := bbase (se 3 (by rfl) ⟨76802, by rfl⟩ : syracuseStep 409613 = 153605) (by norm_num)
theorem B409637 : Blo 271824 409637 := bbase (se 4 (by rfl) ⟨38403, by rfl⟩ : syracuseStep 409637 = 76807) (by norm_num)
theorem B409661 : Blo 271824 409661 := bbase (se 3 (by rfl) ⟨76811, by rfl⟩ : syracuseStep 409661 = 153623) (by norm_num)
theorem B475213 : Blo 271824 475213 := bbase (se 3 (by rfl) ⟨89102, by rfl⟩ : syracuseStep 475213 = 178205) (by norm_num)
theorem B409685 : Blo 271824 409685 := bbase (se 8 (by rfl) ⟨2400, by rfl⟩ : syracuseStep 409685 = 4801) (by norm_num)
theorem B442469 : Blo 271824 442469 := bbase (se 4 (by rfl) ⟨41481, by rfl⟩ : syracuseStep 442469 = 82963) (by norm_num)
theorem B409709 : Blo 271824 409709 := bbase (se 3 (by rfl) ⟨76820, by rfl⟩ : syracuseStep 409709 = 153641) (by norm_num)
theorem B1556597 : Blo 271824 1556597 := bbase (se 5 (by rfl) ⟨72965, by rfl⟩ : syracuseStep 1556597 = 145931) (by norm_num)
theorem B344189 : Blo 271824 344189 := bbase (se 3 (by rfl) ⟨64535, by rfl⟩ : syracuseStep 344189 = 129071) (by norm_num)
theorem B409733 : Blo 271824 409733 := bbase (se 4 (by rfl) ⟨38412, by rfl⟩ : syracuseStep 409733 = 76825) (by norm_num)
theorem B409757 : Blo 271824 409757 := bbase (se 3 (by rfl) ⟨76829, by rfl⟩ : syracuseStep 409757 = 153659) (by norm_num)
theorem B344245 : Blo 271824 344245 := bbase (se 5 (by rfl) ⟨16136, by rfl⟩ : syracuseStep 344245 = 32273) (by norm_num)
theorem B409781 : Blo 271824 409781 := bbase (se 5 (by rfl) ⟨19208, by rfl⟩ : syracuseStep 409781 = 38417) (by norm_num)
theorem B409805 : Blo 271824 409805 := bbase (se 3 (by rfl) ⟨76838, by rfl⟩ : syracuseStep 409805 = 153677) (by norm_num)
theorem B409829 : Blo 271824 409829 := bbase (se 4 (by rfl) ⟨38421, by rfl⟩ : syracuseStep 409829 = 76843) (by norm_num)
theorem B737525 : Blo 271824 737525 := bbase (se 5 (by rfl) ⟨34571, by rfl⟩ : syracuseStep 737525 = 69143) (by norm_num)
theorem B409853 : Blo 271824 409853 := bbase (se 3 (by rfl) ⟨76847, by rfl⟩ : syracuseStep 409853 = 153695) (by norm_num)
theorem B344341 : Blo 271824 344341 := bbase (se 6 (by rfl) ⟨8070, by rfl⟩ : syracuseStep 344341 = 16141) (by norm_num)
theorem B409877 : Blo 271824 409877 := bbase (se 6 (by rfl) ⟨9606, by rfl⟩ : syracuseStep 409877 = 19213) (by norm_num)
theorem B278825 : Blo 271824 278825 := bbase (se 2 (by rfl) ⟨104559, by rfl⟩ : syracuseStep 278825 = 209119) (by norm_num)
theorem B409901 : Blo 271824 409901 := bbase (se 3 (by rfl) ⟨76856, by rfl⟩ : syracuseStep 409901 = 153713) (by norm_num)
theorem B409925 : Blo 271824 409925 := bbase (se 4 (by rfl) ⟨38430, by rfl⟩ : syracuseStep 409925 = 76861) (by norm_num)
theorem B999749 : Blo 271824 999749 := bbase (se 4 (by rfl) ⟨93726, by rfl⟩ : syracuseStep 999749 = 187453) (by norm_num)
theorem B1163605 : Blo 271824 1163605 := bbase (se 10 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 1163605 = 3409) (by norm_num)
theorem B409949 : Blo 271824 409949 := bbase (se 3 (by rfl) ⟨76865, by rfl⟩ : syracuseStep 409949 = 153731) (by norm_num)
theorem B1163621 : Blo 271824 1163621 := bbase (se 4 (by rfl) ⟨109089, by rfl⟩ : syracuseStep 1163621 = 218179) (by norm_num)
theorem B409973 : Blo 271824 409973 := bbase (se 5 (by rfl) ⟨19217, by rfl⟩ : syracuseStep 409973 = 38435) (by norm_num)
theorem B409997 : Blo 271824 409997 := bbase (se 3 (by rfl) ⟨76874, by rfl⟩ : syracuseStep 409997 = 153749) (by norm_num)
theorem B410021 : Blo 271824 410021 := bbase (se 4 (by rfl) ⟨38439, by rfl⟩ : syracuseStep 410021 = 76879) (by norm_num)
theorem B410045 : Blo 271824 410045 := bbase (se 3 (by rfl) ⟨76883, by rfl⟩ : syracuseStep 410045 = 153767) (by norm_num)
theorem B344513 : Blo 271824 344513 := bbase (se 2 (by rfl) ⟨129192, by rfl⟩ : syracuseStep 344513 = 258385) (by norm_num)
theorem B410069 : Blo 271824 410069 := bbase (se 7 (by rfl) ⟨4805, by rfl⟩ : syracuseStep 410069 = 9611) (by norm_num)
theorem B410093 : Blo 271824 410093 := bbase (se 3 (by rfl) ⟨76892, by rfl⟩ : syracuseStep 410093 = 153785) (by norm_num)
theorem B344569 : Blo 271824 344569 := bbase (se 2 (by rfl) ⟨129213, by rfl⟩ : syracuseStep 344569 = 258427) (by norm_num)
theorem B410117 : Blo 271824 410117 := bbase (se 4 (by rfl) ⟨38448, by rfl⟩ : syracuseStep 410117 = 76897) (by norm_num)
theorem B410141 : Blo 271824 410141 := bbase (se 3 (by rfl) ⟨76901, by rfl⟩ : syracuseStep 410141 = 153803) (by norm_num)
theorem B410165 : Blo 271824 410165 := bbase (se 5 (by rfl) ⟨19226, by rfl⟩ : syracuseStep 410165 = 38453) (by norm_num)
theorem B410189 : Blo 271824 410189 := bbase (se 3 (by rfl) ⟨76910, by rfl⟩ : syracuseStep 410189 = 153821) (by norm_num)
theorem B344665 : Blo 271824 344665 := bbase (se 2 (by rfl) ⟨129249, by rfl⟩ : syracuseStep 344665 = 258499) (by norm_num)
theorem B410213 : Blo 271824 410213 := bbase (se 4 (by rfl) ⟨38457, by rfl⟩ : syracuseStep 410213 = 76915) (by norm_num)
theorem B803429 : Blo 271824 803429 := bbase (se 4 (by rfl) ⟨75321, by rfl⟩ : syracuseStep 803429 = 150643) (by norm_num)
theorem B410237 : Blo 271824 410237 := bbase (se 3 (by rfl) ⟨76919, by rfl⟩ : syracuseStep 410237 = 153839) (by norm_num)
theorem B410261 : Blo 271824 410261 := bbase (se 6 (by rfl) ⟨9615, by rfl⟩ : syracuseStep 410261 = 19231) (by norm_num)
theorem B410285 : Blo 271824 410285 := bbase (se 3 (by rfl) ⟨76928, by rfl⟩ : syracuseStep 410285 = 153857) (by norm_num)
theorem B410309 : Blo 271824 410309 := bbase (se 4 (by rfl) ⟨38466, by rfl⟩ : syracuseStep 410309 = 76933) (by norm_num)
theorem B410333 : Blo 271824 410333 := bbase (se 3 (by rfl) ⟨76937, by rfl⟩ : syracuseStep 410333 = 153875) (by norm_num)
theorem B410357 : Blo 271824 410357 := bbase (se 5 (by rfl) ⟨19235, by rfl⟩ : syracuseStep 410357 = 38471) (by norm_num)
theorem B1884917 : Blo 271824 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B344837 : Blo 271824 344837 := bbase (se 4 (by rfl) ⟨32328, by rfl⟩ : syracuseStep 344837 = 64657) (by norm_num)
theorem B410381 : Blo 271824 410381 := bbase (se 3 (by rfl) ⟨76946, by rfl⟩ : syracuseStep 410381 = 153893) (by norm_num)
theorem B738085 : Blo 271824 738085 := bbase (se 4 (by rfl) ⟨69195, by rfl⟩ : syracuseStep 738085 = 138391) (by norm_num)
theorem B410405 : Blo 271824 410405 := bbase (se 4 (by rfl) ⟨38475, by rfl⟩ : syracuseStep 410405 = 76951) (by norm_num)
theorem B344893 : Blo 271824 344893 := bbase (se 3 (by rfl) ⟨64667, by rfl⟩ : syracuseStep 344893 = 129335) (by norm_num)
theorem B410429 : Blo 271824 410429 := bbase (se 3 (by rfl) ⟨76955, by rfl⟩ : syracuseStep 410429 = 153911) (by norm_num)
theorem B410453 : Blo 271824 410453 := bbase (se 9 (by rfl) ⟨1202, by rfl⟩ : syracuseStep 410453 = 2405) (by norm_num)
theorem B410477 : Blo 271824 410477 := bbase (se 3 (by rfl) ⟨76964, by rfl⟩ : syracuseStep 410477 = 153929) (by norm_num)
theorem B410501 : Blo 271824 410501 := bbase (se 4 (by rfl) ⟨38484, by rfl⟩ : syracuseStep 410501 = 76969) (by norm_num)
theorem B344989 : Blo 271824 344989 := bbase (se 3 (by rfl) ⟨64685, by rfl⟩ : syracuseStep 344989 = 129371) (by norm_num)
theorem B410525 : Blo 271824 410525 := bbase (se 3 (by rfl) ⟨76973, by rfl⟩ : syracuseStep 410525 = 153947) (by norm_num)
theorem B410549 : Blo 271824 410549 := bbase (se 5 (by rfl) ⟨19244, by rfl⟩ : syracuseStep 410549 = 38489) (by norm_num)
theorem B410573 : Blo 271824 410573 := bbase (se 3 (by rfl) ⟨76982, by rfl⟩ : syracuseStep 410573 = 153965) (by norm_num)
theorem B3130325 : Blo 271824 3130325 := bbase (se 7 (by rfl) ⟨36683, by rfl⟩ : syracuseStep 3130325 = 73367) (by norm_num)
theorem B410597 : Blo 271824 410597 := bbase (se 4 (by rfl) ⟨38493, by rfl⟩ : syracuseStep 410597 = 76987) (by norm_num)
theorem B410621 : Blo 271824 410621 := bbase (se 3 (by rfl) ⟨76991, by rfl⟩ : syracuseStep 410621 = 153983) (by norm_num)
theorem B410645 : Blo 271824 410645 := bbase (se 6 (by rfl) ⟨9624, by rfl⟩ : syracuseStep 410645 = 19249) (by norm_num)
theorem B1393685 : Blo 271824 1393685 := bbase (se 6 (by rfl) ⟨32664, by rfl⟩ : syracuseStep 1393685 = 65329) (by norm_num)
theorem B410669 : Blo 271824 410669 := bbase (se 3 (by rfl) ⟨77000, by rfl⟩ : syracuseStep 410669 = 154001) (by norm_num)
theorem B410693 : Blo 271824 410693 := bbase (se 4 (by rfl) ⟨38502, by rfl⟩ : syracuseStep 410693 = 77005) (by norm_num)
theorem B345161 : Blo 271824 345161 := bbase (se 2 (by rfl) ⟨129435, by rfl⟩ : syracuseStep 345161 = 258871) (by norm_num)
theorem B410717 : Blo 271824 410717 := bbase (se 3 (by rfl) ⟨77009, by rfl⟩ : syracuseStep 410717 = 154019) (by norm_num)
theorem B410741 : Blo 271824 410741 := bbase (se 5 (by rfl) ⟨19253, by rfl⟩ : syracuseStep 410741 = 38507) (by norm_num)
theorem B345217 : Blo 271824 345217 := bbase (se 2 (by rfl) ⟨129456, by rfl⟩ : syracuseStep 345217 = 258913) (by norm_num)
theorem B410765 : Blo 271824 410765 := bbase (se 3 (by rfl) ⟨77018, by rfl⟩ : syracuseStep 410765 = 154037) (by norm_num)
theorem B410789 : Blo 271824 410789 := bbase (se 4 (by rfl) ⟨38511, by rfl⟩ : syracuseStep 410789 = 77023) (by norm_num)
theorem B410813 : Blo 271824 410813 := bbase (se 3 (by rfl) ⟨77027, by rfl⟩ : syracuseStep 410813 = 154055) (by norm_num)
theorem B410837 : Blo 271824 410837 := bbase (se 7 (by rfl) ⟨4814, by rfl⟩ : syracuseStep 410837 = 9629) (by norm_num)
theorem B345313 : Blo 271824 345313 := bbase (se 2 (by rfl) ⟨129492, by rfl⟩ : syracuseStep 345313 = 258985) (by norm_num)
theorem B410861 : Blo 271824 410861 := bbase (se 3 (by rfl) ⟨77036, by rfl⟩ : syracuseStep 410861 = 154073) (by norm_num)
theorem B410885 : Blo 271824 410885 := bbase (se 4 (by rfl) ⟨38520, by rfl⟩ : syracuseStep 410885 = 77041) (by norm_num)
theorem B410909 : Blo 271824 410909 := bbase (se 3 (by rfl) ⟨77045, by rfl⟩ : syracuseStep 410909 = 154091) (by norm_num)
theorem B410933 : Blo 271824 410933 := bbase (se 5 (by rfl) ⟨19262, by rfl⟩ : syracuseStep 410933 = 38525) (by norm_num)
theorem B410957 : Blo 271824 410957 := bbase (se 3 (by rfl) ⟨77054, by rfl⟩ : syracuseStep 410957 = 154109) (by norm_num)
theorem B1754453 : Blo 271824 1754453 := bbase (se 12 (by rfl) ⟨642, by rfl⟩ : syracuseStep 1754453 = 1285) (by norm_num)
theorem B410981 : Blo 271824 410981 := bbase (se 4 (by rfl) ⟨38529, by rfl⟩ : syracuseStep 410981 = 77059) (by norm_num)
theorem B411005 : Blo 271824 411005 := bbase (se 3 (by rfl) ⟨77063, by rfl⟩ : syracuseStep 411005 = 154127) (by norm_num)
theorem B345485 : Blo 271824 345485 := bbase (se 3 (by rfl) ⟨64778, by rfl⟩ : syracuseStep 345485 = 129557) (by norm_num)
theorem B411029 : Blo 271824 411029 := bbase (se 6 (by rfl) ⟨9633, by rfl⟩ : syracuseStep 411029 = 19267) (by norm_num)
theorem B411053 : Blo 271824 411053 := bbase (se 3 (by rfl) ⟨77072, by rfl⟩ : syracuseStep 411053 = 154145) (by norm_num)
theorem B345541 : Blo 271824 345541 := bbase (se 4 (by rfl) ⟨32394, by rfl⟩ : syracuseStep 345541 = 64789) (by norm_num)
theorem B411077 : Blo 271824 411077 := bbase (se 4 (by rfl) ⟨38538, by rfl⟩ : syracuseStep 411077 = 77077) (by norm_num)
theorem B2803157 : Blo 271824 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B411101 : Blo 271824 411101 := bbase (se 3 (by rfl) ⟨77081, by rfl⟩ : syracuseStep 411101 = 154163) (by norm_num)
theorem B411125 : Blo 271824 411125 := bbase (se 5 (by rfl) ⟨19271, by rfl⟩ : syracuseStep 411125 = 38543) (by norm_num)
theorem B411149 : Blo 271824 411149 := bbase (se 3 (by rfl) ⟨77090, by rfl⟩ : syracuseStep 411149 = 154181) (by norm_num)
theorem B345637 : Blo 271824 345637 := bbase (se 4 (by rfl) ⟨32403, by rfl⟩ : syracuseStep 345637 = 64807) (by norm_num)
theorem B411173 : Blo 271824 411173 := bbase (se 4 (by rfl) ⟨38547, by rfl⟩ : syracuseStep 411173 = 77095) (by norm_num)
theorem B411197 : Blo 271824 411197 := bbase (se 3 (by rfl) ⟨77099, by rfl⟩ : syracuseStep 411197 = 154199) (by norm_num)
theorem B411221 : Blo 271824 411221 := bbase (se 8 (by rfl) ⟨2409, by rfl⟩ : syracuseStep 411221 = 4819) (by norm_num)
theorem B1033829 : Blo 271824 1033829 := bbase (se 4 (by rfl) ⟨96921, by rfl⟩ : syracuseStep 1033829 = 193843) (by norm_num)
theorem B411245 : Blo 271824 411245 := bbase (se 3 (by rfl) ⟨77108, by rfl⟩ : syracuseStep 411245 = 154217) (by norm_num)
theorem B411269 : Blo 271824 411269 := bbase (se 4 (by rfl) ⟨38556, by rfl⟩ : syracuseStep 411269 = 77113) (by norm_num)
theorem B411293 : Blo 271824 411293 := bbase (se 3 (by rfl) ⟨77117, by rfl⟩ : syracuseStep 411293 = 154235) (by norm_num)
theorem B411317 : Blo 271824 411317 := bbase (se 5 (by rfl) ⟨19280, by rfl⟩ : syracuseStep 411317 = 38561) (by norm_num)
theorem B411341 : Blo 271824 411341 := bbase (se 3 (by rfl) ⟨77126, by rfl⟩ : syracuseStep 411341 = 154253) (by norm_num)
theorem B345809 : Blo 271824 345809 := bbase (se 2 (by rfl) ⟨129678, by rfl⟩ : syracuseStep 345809 = 259357) (by norm_num)
theorem B411365 : Blo 271824 411365 := bbase (se 4 (by rfl) ⟨38565, by rfl⟩ : syracuseStep 411365 = 77131) (by norm_num)
theorem B411389 : Blo 271824 411389 := bbase (se 3 (by rfl) ⟨77135, by rfl⟩ : syracuseStep 411389 = 154271) (by norm_num)
theorem B345865 : Blo 271824 345865 := bbase (se 2 (by rfl) ⟨129699, by rfl⟩ : syracuseStep 345865 = 259399) (by norm_num)
theorem B411413 : Blo 271824 411413 := bbase (se 6 (by rfl) ⟨9642, by rfl⟩ : syracuseStep 411413 = 19285) (by norm_num)
theorem B411437 : Blo 271824 411437 := bbase (se 3 (by rfl) ⟨77144, by rfl⟩ : syracuseStep 411437 = 154289) (by norm_num)
theorem B313141 : Blo 271824 313141 := bbase (se 5 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 313141 = 29357) (by norm_num)
theorem B411461 : Blo 271824 411461 := bbase (se 4 (by rfl) ⟨38574, by rfl⟩ : syracuseStep 411461 = 77149) (by norm_num)
theorem B411485 : Blo 271824 411485 := bbase (se 3 (by rfl) ⟨77153, by rfl⟩ : syracuseStep 411485 = 154307) (by norm_num)
theorem B345961 : Blo 271824 345961 := bbase (se 2 (by rfl) ⟨129735, by rfl⟩ : syracuseStep 345961 = 259471) (by norm_num)
theorem B411509 : Blo 271824 411509 := bbase (se 5 (by rfl) ⟨19289, by rfl⟩ : syracuseStep 411509 = 38579) (by norm_num)
theorem B1034117 : Blo 271824 1034117 := bbase (se 4 (by rfl) ⟨96948, by rfl⟩ : syracuseStep 1034117 = 193897) (by norm_num)
theorem B411533 : Blo 271824 411533 := bbase (se 3 (by rfl) ⟨77162, by rfl⟩ : syracuseStep 411533 = 154325) (by norm_num)
theorem B411557 : Blo 271824 411557 := bbase (se 4 (by rfl) ⟨38583, by rfl⟩ : syracuseStep 411557 = 77167) (by norm_num)
theorem B411581 : Blo 271824 411581 := bbase (se 3 (by rfl) ⟨77171, by rfl⟩ : syracuseStep 411581 = 154343) (by norm_num)
theorem B411605 : Blo 271824 411605 := bbase (se 7 (by rfl) ⟨4823, by rfl⟩ : syracuseStep 411605 = 9647) (by norm_num)
theorem B411629 : Blo 271824 411629 := bbase (se 3 (by rfl) ⟨77180, by rfl⟩ : syracuseStep 411629 = 154361) (by norm_num)
theorem B411653 : Blo 271824 411653 := bbase (se 4 (by rfl) ⟨38592, by rfl⟩ : syracuseStep 411653 = 77185) (by norm_num)
theorem B346133 : Blo 271824 346133 := bbase (se 6 (by rfl) ⟨8112, by rfl⟩ : syracuseStep 346133 = 16225) (by norm_num)
theorem B411677 : Blo 271824 411677 := bbase (se 3 (by rfl) ⟨77189, by rfl⟩ : syracuseStep 411677 = 154379) (by norm_num)
theorem B411701 : Blo 271824 411701 := bbase (se 5 (by rfl) ⟨19298, by rfl⟩ : syracuseStep 411701 = 38597) (by norm_num)
theorem B804917 : Blo 271824 804917 := bbase (se 5 (by rfl) ⟨37730, by rfl⟩ : syracuseStep 804917 = 75461) (by norm_num)
theorem B346189 : Blo 271824 346189 := bbase (se 3 (by rfl) ⟨64910, by rfl⟩ : syracuseStep 346189 = 129821) (by norm_num)
theorem B411725 : Blo 271824 411725 := bbase (se 3 (by rfl) ⟨77198, by rfl⟩ : syracuseStep 411725 = 154397) (by norm_num)
theorem B411749 : Blo 271824 411749 := bbase (se 4 (by rfl) ⟨38601, by rfl⟩ : syracuseStep 411749 = 77203) (by norm_num)
theorem B411773 : Blo 271824 411773 := bbase (se 3 (by rfl) ⟨77207, by rfl⟩ : syracuseStep 411773 = 154415) (by norm_num)
theorem B411797 : Blo 271824 411797 := bbase (se 6 (by rfl) ⟨9651, by rfl⟩ : syracuseStep 411797 = 19303) (by norm_num)
theorem B346285 : Blo 271824 346285 := bbase (se 3 (by rfl) ⟨64928, by rfl⟩ : syracuseStep 346285 = 129857) (by norm_num)
theorem B411821 : Blo 271824 411821 := bbase (se 3 (by rfl) ⟨77216, by rfl⟩ : syracuseStep 411821 = 154433) (by norm_num)
theorem B411845 : Blo 271824 411845 := bbase (se 4 (by rfl) ⟨38610, by rfl⟩ : syracuseStep 411845 = 77221) (by norm_num)
theorem B411869 : Blo 271824 411869 := bbase (se 3 (by rfl) ⟨77225, by rfl⟩ : syracuseStep 411869 = 154451) (by norm_num)
theorem B411893 : Blo 271824 411893 := bbase (se 5 (by rfl) ⟨19307, by rfl⟩ : syracuseStep 411893 = 38615) (by norm_num)
theorem B411917 : Blo 271824 411917 := bbase (se 3 (by rfl) ⟨77234, by rfl⟩ : syracuseStep 411917 = 154469) (by norm_num)
theorem B411941 : Blo 271824 411941 := bbase (se 4 (by rfl) ⟨38619, by rfl⟩ : syracuseStep 411941 = 77239) (by norm_num)
theorem B1394981 : Blo 271824 1394981 := bbase (se 4 (by rfl) ⟨130779, by rfl⟩ : syracuseStep 1394981 = 261559) (by norm_num)
theorem B411965 : Blo 271824 411965 := bbase (se 3 (by rfl) ⟨77243, by rfl⟩ : syracuseStep 411965 = 154487) (by norm_num)
theorem B411989 : Blo 271824 411989 := bbase (se 10 (by rfl) ⟨603, by rfl⟩ : syracuseStep 411989 = 1207) (by norm_num)
theorem B346457 : Blo 271824 346457 := bbase (se 2 (by rfl) ⟨129921, by rfl⟩ : syracuseStep 346457 = 259843) (by norm_num)
theorem B412013 : Blo 271824 412013 := bbase (se 3 (by rfl) ⟨77252, by rfl⟩ : syracuseStep 412013 = 154505) (by norm_num)
theorem B412037 : Blo 271824 412037 := bbase (se 4 (by rfl) ⟨38628, by rfl⟩ : syracuseStep 412037 = 77257) (by norm_num)
theorem B346513 : Blo 271824 346513 := bbase (se 2 (by rfl) ⟨129942, by rfl⟩ : syracuseStep 346513 = 259885) (by norm_num)
theorem B412061 : Blo 271824 412061 := bbase (se 3 (by rfl) ⟨77261, by rfl⟩ : syracuseStep 412061 = 154523) (by norm_num)
theorem B412085 : Blo 271824 412085 := bbase (se 5 (by rfl) ⟨19316, by rfl⟩ : syracuseStep 412085 = 38633) (by norm_num)
theorem B412109 : Blo 271824 412109 := bbase (se 3 (by rfl) ⟨77270, by rfl⟩ : syracuseStep 412109 = 154541) (by norm_num)
theorem B412133 : Blo 271824 412133 := bbase (se 4 (by rfl) ⟨38637, by rfl⟩ : syracuseStep 412133 = 77275) (by norm_num)
theorem B346609 : Blo 271824 346609 := bbase (se 2 (by rfl) ⟨129978, by rfl⟩ : syracuseStep 346609 = 259957) (by norm_num)
theorem B412157 : Blo 271824 412157 := bbase (se 3 (by rfl) ⟨77279, by rfl⟩ : syracuseStep 412157 = 154559) (by norm_num)
theorem B412181 : Blo 271824 412181 := bbase (se 6 (by rfl) ⟨9660, by rfl⟩ : syracuseStep 412181 = 19321) (by norm_num)
theorem B412205 : Blo 271824 412205 := bbase (se 3 (by rfl) ⟨77288, by rfl⟩ : syracuseStep 412205 = 154577) (by norm_num)
theorem B1165877 : Blo 271824 1165877 := bbase (se 5 (by rfl) ⟨54650, by rfl⟩ : syracuseStep 1165877 = 109301) (by norm_num)
theorem B412229 : Blo 271824 412229 := bbase (se 4 (by rfl) ⟨38646, by rfl⟩ : syracuseStep 412229 = 77293) (by norm_num)
theorem B739925 : Blo 271824 739925 := bbase (se 8 (by rfl) ⟨4335, by rfl⟩ : syracuseStep 739925 = 8671) (by norm_num)
theorem B2345557 : Blo 271824 2345557 := bbase (se 8 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 2345557 = 27487) (by norm_num)
theorem B412253 : Blo 271824 412253 := bbase (se 3 (by rfl) ⟨77297, by rfl⟩ : syracuseStep 412253 = 154595) (by norm_num)
theorem B412277 : Blo 271824 412277 := bbase (se 5 (by rfl) ⟨19325, by rfl⟩ : syracuseStep 412277 = 38651) (by norm_num)
theorem B412301 : Blo 271824 412301 := bbase (se 3 (by rfl) ⟨77306, by rfl⟩ : syracuseStep 412301 = 154613) (by norm_num)
theorem B346781 : Blo 271824 346781 := bbase (se 3 (by rfl) ⟨65021, by rfl⟩ : syracuseStep 346781 = 130043) (by norm_num)
theorem B412325 : Blo 271824 412325 := bbase (se 4 (by rfl) ⟨38655, by rfl⟩ : syracuseStep 412325 = 77311) (by norm_num)
theorem B412349 : Blo 271824 412349 := bbase (se 3 (by rfl) ⟨77315, by rfl⟩ : syracuseStep 412349 = 154631) (by norm_num)
theorem B346837 : Blo 271824 346837 := bbase (se 7 (by rfl) ⟨4064, by rfl⟩ : syracuseStep 346837 = 8129) (by norm_num)
theorem B412373 : Blo 271824 412373 := bbase (se 7 (by rfl) ⟨4832, by rfl⟩ : syracuseStep 412373 = 9665) (by norm_num)
theorem B412397 : Blo 271824 412397 := bbase (se 3 (by rfl) ⟨77324, by rfl⟩ : syracuseStep 412397 = 154649) (by norm_num)
theorem B412421 : Blo 271824 412421 := bbase (se 4 (by rfl) ⟨38664, by rfl⟩ : syracuseStep 412421 = 77329) (by norm_num)
theorem B412445 : Blo 271824 412445 := bbase (se 3 (by rfl) ⟨77333, by rfl⟩ : syracuseStep 412445 = 154667) (by norm_num)
theorem B412469 : Blo 271824 412469 := bbase (se 5 (by rfl) ⟨19334, by rfl⟩ : syracuseStep 412469 = 38669) (by norm_num)
theorem B346933 : Blo 271824 346933 := bbase (se 5 (by rfl) ⟨16262, by rfl⟩ : syracuseStep 346933 = 32525) (by norm_num)
theorem B412493 : Blo 271824 412493 := bbase (se 3 (by rfl) ⟨77342, by rfl⟩ : syracuseStep 412493 = 154685) (by norm_num)
theorem B412517 : Blo 271824 412517 := bbase (se 4 (by rfl) ⟨38673, by rfl⟩ : syracuseStep 412517 = 77347) (by norm_num)
theorem B412541 : Blo 271824 412541 := bbase (se 3 (by rfl) ⟨77351, by rfl⟩ : syracuseStep 412541 = 154703) (by norm_num)
theorem B2378645 : Blo 271824 2378645 := bbase (se 6 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 2378645 = 111499) (by norm_num)
theorem B412565 : Blo 271824 412565 := bbase (se 6 (by rfl) ⟨9669, by rfl⟩ : syracuseStep 412565 = 19339) (by norm_num)
theorem B412589 : Blo 271824 412589 := bbase (se 3 (by rfl) ⟨77360, by rfl⟩ : syracuseStep 412589 = 154721) (by norm_num)
theorem B412613 : Blo 271824 412613 := bbase (se 4 (by rfl) ⟨38682, by rfl⟩ : syracuseStep 412613 = 77365) (by norm_num)
theorem B412637 : Blo 271824 412637 := bbase (se 3 (by rfl) ⟨77369, by rfl⟩ : syracuseStep 412637 = 154739) (by norm_num)
theorem B347105 : Blo 271824 347105 := bbase (se 2 (by rfl) ⟨130164, by rfl⟩ : syracuseStep 347105 = 260329) (by norm_num)
theorem B412661 : Blo 271824 412661 := bbase (se 5 (by rfl) ⟨19343, by rfl⟩ : syracuseStep 412661 = 38687) (by norm_num)
theorem B412685 : Blo 271824 412685 := bbase (se 3 (by rfl) ⟨77378, by rfl⟩ : syracuseStep 412685 = 154757) (by norm_num)
theorem B347161 : Blo 271824 347161 := bbase (se 2 (by rfl) ⟨130185, by rfl⟩ : syracuseStep 347161 = 260371) (by norm_num)
theorem B1035301 : Blo 271824 1035301 := bbase (se 4 (by rfl) ⟨97059, by rfl⟩ : syracuseStep 1035301 = 194119) (by norm_num)
theorem B412709 : Blo 271824 412709 := bbase (se 4 (by rfl) ⟨38691, by rfl⟩ : syracuseStep 412709 = 77383) (by norm_num)
theorem B412733 : Blo 271824 412733 := bbase (se 3 (by rfl) ⟨77387, by rfl⟩ : syracuseStep 412733 = 154775) (by norm_num)
theorem B412757 : Blo 271824 412757 := bbase (se 8 (by rfl) ⟨2418, by rfl⟩ : syracuseStep 412757 = 4837) (by norm_num)
theorem B412781 : Blo 271824 412781 := bbase (se 3 (by rfl) ⟨77396, by rfl⟩ : syracuseStep 412781 = 154793) (by norm_num)
theorem B347257 : Blo 271824 347257 := bbase (se 2 (by rfl) ⟨130221, by rfl⟩ : syracuseStep 347257 = 260443) (by norm_num)
theorem B412805 : Blo 271824 412805 := bbase (se 4 (by rfl) ⟨38700, by rfl⟩ : syracuseStep 412805 = 77401) (by norm_num)
theorem B412829 : Blo 271824 412829 := bbase (se 3 (by rfl) ⟨77405, by rfl⟩ : syracuseStep 412829 = 154811) (by norm_num)
theorem B412853 : Blo 271824 412853 := bbase (se 5 (by rfl) ⟨19352, by rfl⟩ : syracuseStep 412853 = 38705) (by norm_num)
theorem B412877 : Blo 271824 412877 := bbase (se 3 (by rfl) ⟨77414, by rfl⟩ : syracuseStep 412877 = 154829) (by norm_num)
theorem B412901 : Blo 271824 412901 := bbase (se 4 (by rfl) ⟨38709, by rfl⟩ : syracuseStep 412901 = 77419) (by norm_num)
theorem B511213 : Blo 271824 511213 := bbase (se 3 (by rfl) ⟨95852, by rfl⟩ : syracuseStep 511213 = 191705) (by norm_num)
theorem B412925 : Blo 271824 412925 := bbase (se 3 (by rfl) ⟨77423, by rfl⟩ : syracuseStep 412925 = 154847) (by norm_num)
theorem B412949 : Blo 271824 412949 := bbase (se 6 (by rfl) ⟨9678, by rfl⟩ : syracuseStep 412949 = 19357) (by norm_num)
theorem B871717 : Blo 271824 871717 := bbase (se 4 (by rfl) ⟨81723, by rfl⟩ : syracuseStep 871717 = 163447) (by norm_num)
theorem B347429 : Blo 271824 347429 := bbase (se 4 (by rfl) ⟨32571, by rfl⟩ : syracuseStep 347429 = 65143) (by norm_num)
theorem B412973 : Blo 271824 412973 := bbase (se 3 (by rfl) ⟨77432, by rfl⟩ : syracuseStep 412973 = 154865) (by norm_num)
theorem B412997 : Blo 271824 412997 := bbase (se 4 (by rfl) ⟨38718, by rfl⟩ : syracuseStep 412997 = 77437) (by norm_num)
theorem B1035605 : Blo 271824 1035605 := bbase (se 11 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1035605 = 1517) (by norm_num)
theorem B347485 : Blo 271824 347485 := bbase (se 3 (by rfl) ⟨65153, by rfl⟩ : syracuseStep 347485 = 130307) (by norm_num)
theorem B413021 : Blo 271824 413021 := bbase (se 3 (by rfl) ⟨77441, by rfl⟩ : syracuseStep 413021 = 154883) (by norm_num)
theorem B413045 : Blo 271824 413045 := bbase (se 5 (by rfl) ⟨19361, by rfl⟩ : syracuseStep 413045 = 38723) (by norm_num)
theorem B413069 : Blo 271824 413069 := bbase (se 3 (by rfl) ⟨77450, by rfl⟩ : syracuseStep 413069 = 154901) (by norm_num)
theorem B413093 : Blo 271824 413093 := bbase (se 4 (by rfl) ⟨38727, by rfl⟩ : syracuseStep 413093 = 77455) (by norm_num)
theorem B347581 : Blo 271824 347581 := bbase (se 3 (by rfl) ⟨65171, by rfl⟩ : syracuseStep 347581 = 130343) (by norm_num)
theorem B413117 : Blo 271824 413117 := bbase (se 3 (by rfl) ⟨77459, by rfl⟩ : syracuseStep 413117 = 154919) (by norm_num)
theorem B413141 : Blo 271824 413141 := bbase (se 7 (by rfl) ⟨4841, by rfl⟩ : syracuseStep 413141 = 9683) (by norm_num)
theorem B413165 : Blo 271824 413165 := bbase (se 3 (by rfl) ⟨77468, by rfl⟩ : syracuseStep 413165 = 154937) (by norm_num)
theorem B413189 : Blo 271824 413189 := bbase (se 4 (by rfl) ⟨38736, by rfl⟩ : syracuseStep 413189 = 77473) (by norm_num)
theorem B413213 : Blo 271824 413213 := bbase (se 3 (by rfl) ⟨77477, by rfl⟩ : syracuseStep 413213 = 154955) (by norm_num)
theorem B413237 : Blo 271824 413237 := bbase (se 5 (by rfl) ⟨19370, by rfl⟩ : syracuseStep 413237 = 38741) (by norm_num)
theorem B1396277 : Blo 271824 1396277 := bbase (se 5 (by rfl) ⟨65450, by rfl⟩ : syracuseStep 1396277 = 130901) (by norm_num)
theorem B413261 : Blo 271824 413261 := bbase (se 3 (by rfl) ⟨77486, by rfl⟩ : syracuseStep 413261 = 154973) (by norm_num)
theorem B413285 : Blo 271824 413285 := bbase (se 4 (by rfl) ⟨38745, by rfl⟩ : syracuseStep 413285 = 77491) (by norm_num)
theorem B347753 : Blo 271824 347753 := bbase (se 2 (by rfl) ⟨130407, by rfl⟩ : syracuseStep 347753 = 260815) (by norm_num)
theorem B413309 : Blo 271824 413309 := bbase (se 3 (by rfl) ⟨77495, by rfl⟩ : syracuseStep 413309 = 154991) (by norm_num)
theorem B413333 : Blo 271824 413333 := bbase (se 6 (by rfl) ⟨9687, by rfl⟩ : syracuseStep 413333 = 19375) (by norm_num)
theorem B347809 : Blo 271824 347809 := bbase (se 2 (by rfl) ⟨130428, by rfl⟩ : syracuseStep 347809 = 260857) (by norm_num)
theorem B413357 : Blo 271824 413357 := bbase (se 3 (by rfl) ⟨77504, by rfl⟩ : syracuseStep 413357 = 155009) (by norm_num)
theorem B413381 : Blo 271824 413381 := bbase (se 4 (by rfl) ⟨38754, by rfl⟩ : syracuseStep 413381 = 77509) (by norm_num)
theorem B413405 : Blo 271824 413405 := bbase (se 3 (by rfl) ⟨77513, by rfl⟩ : syracuseStep 413405 = 155027) (by norm_num)
theorem B413429 : Blo 271824 413429 := bbase (se 5 (by rfl) ⟨19379, by rfl⟩ : syracuseStep 413429 = 38759) (by norm_num)
theorem B347905 : Blo 271824 347905 := bbase (se 2 (by rfl) ⟨130464, by rfl⟩ : syracuseStep 347905 = 260929) (by norm_num)
theorem B413453 : Blo 271824 413453 := bbase (se 3 (by rfl) ⟨77522, by rfl⟩ : syracuseStep 413453 = 155045) (by norm_num)
theorem B413477 : Blo 271824 413477 := bbase (se 4 (by rfl) ⟨38763, by rfl⟩ : syracuseStep 413477 = 77527) (by norm_num)
theorem B413501 : Blo 271824 413501 := bbase (se 3 (by rfl) ⟨77531, by rfl⟩ : syracuseStep 413501 = 155063) (by norm_num)
theorem B413525 : Blo 271824 413525 := bbase (se 9 (by rfl) ⟨1211, by rfl⟩ : syracuseStep 413525 = 2423) (by norm_num)
theorem B413549 : Blo 271824 413549 := bbase (se 3 (by rfl) ⟨77540, by rfl⟩ : syracuseStep 413549 = 155081) (by norm_num)
theorem B413573 : Blo 271824 413573 := bbase (se 4 (by rfl) ⟨38772, by rfl⟩ : syracuseStep 413573 = 77545) (by norm_num)
theorem B413597 : Blo 271824 413597 := bbase (se 3 (by rfl) ⟨77549, by rfl⟩ : syracuseStep 413597 = 155099) (by norm_num)
theorem B348077 : Blo 271824 348077 := bbase (se 3 (by rfl) ⟨65264, by rfl⟩ : syracuseStep 348077 = 130529) (by norm_num)
theorem B413621 : Blo 271824 413621 := bbase (se 5 (by rfl) ⟨19388, by rfl⟩ : syracuseStep 413621 = 38777) (by norm_num)
theorem B413645 : Blo 271824 413645 := bbase (se 3 (by rfl) ⟨77558, by rfl⟩ : syracuseStep 413645 = 155117) (by norm_num)
theorem B348133 : Blo 271824 348133 := bbase (se 4 (by rfl) ⟨32637, by rfl⟩ : syracuseStep 348133 = 65275) (by norm_num)
theorem B413669 : Blo 271824 413669 := bbase (se 4 (by rfl) ⟨38781, by rfl⟩ : syracuseStep 413669 = 77563) (by norm_num)
theorem B413693 : Blo 271824 413693 := bbase (se 3 (by rfl) ⟨77567, by rfl⟩ : syracuseStep 413693 = 155135) (by norm_num)
theorem B413717 : Blo 271824 413717 := bbase (se 6 (by rfl) ⟨9696, by rfl⟩ : syracuseStep 413717 = 19393) (by norm_num)
theorem B348229 : Blo 271824 348229 := bbase (se 4 (by rfl) ⟨32646, by rfl⟩ : syracuseStep 348229 = 65293) (by norm_num)
theorem B1986677 : Blo 271824 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B348401 : Blo 271824 348401 := bbase (se 2 (by rfl) ⟨130650, by rfl⟩ : syracuseStep 348401 = 261301) (by norm_num)
theorem B413957 : Blo 271824 413957 := bbase (se 4 (by rfl) ⟨38808, by rfl⟩ : syracuseStep 413957 = 77617) (by norm_num)
theorem B348457 : Blo 271824 348457 := bbase (se 2 (by rfl) ⟨130671, by rfl⟩ : syracuseStep 348457 = 261343) (by norm_num)
theorem B774517 : Blo 271824 774517 := bbase (se 5 (by rfl) ⟨36305, by rfl⟩ : syracuseStep 774517 = 72611) (by norm_num)
theorem B348553 : Blo 271824 348553 := bbase (se 2 (by rfl) ⟨130707, by rfl⟩ : syracuseStep 348553 = 261415) (by norm_num)
theorem B774677 : Blo 271824 774677 := bbase (se 6 (by rfl) ⟨18156, by rfl⟩ : syracuseStep 774677 = 36313) (by norm_num)
theorem B2347541 : Blo 271824 2347541 := bbase (se 6 (by rfl) ⟨55020, by rfl⟩ : syracuseStep 2347541 = 110041) (by norm_num)
theorem B348725 : Blo 271824 348725 := bbase (se 5 (by rfl) ⟨16346, by rfl⟩ : syracuseStep 348725 = 32693) (by norm_num)
theorem B971365 : Blo 271824 971365 := bbase (se 4 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 971365 = 182131) (by norm_num)
theorem B348781 : Blo 271824 348781 := bbase (se 3 (by rfl) ⟨65396, by rfl⟩ : syracuseStep 348781 = 130793) (by norm_num)
theorem B348845 : Blo 271824 348845 := bbase (se 3 (by rfl) ⟨65408, by rfl⟩ : syracuseStep 348845 = 130817) (by norm_num)
theorem B348877 : Blo 271824 348877 := bbase (se 3 (by rfl) ⟨65414, by rfl⟩ : syracuseStep 348877 = 130829) (by norm_num)
theorem B774917 : Blo 271824 774917 := bbase (se 4 (by rfl) ⟨72648, by rfl⟩ : syracuseStep 774917 = 145297) (by norm_num)
theorem B349049 : Blo 271824 349049 := bbase (se 2 (by rfl) ⟨130893, by rfl⟩ : syracuseStep 349049 = 261787) (by norm_num)
theorem B775109 : Blo 271824 775109 := bbase (se 4 (by rfl) ⟨72666, by rfl⟩ : syracuseStep 775109 = 145333) (by norm_num)
theorem B1987573 : Blo 271824 1987573 := bbase (se 5 (by rfl) ⟨93167, by rfl⟩ : syracuseStep 1987573 = 186335) (by norm_num)
theorem B611621 : Blo 271824 611621 := bbase (se 4 (by rfl) ⟨57339, by rfl⟩ : syracuseStep 611621 = 114679) (by norm_num)
theorem B611693 : Blo 271824 611693 := bbase (se 3 (by rfl) ⟨114692, by rfl⟩ : syracuseStep 611693 = 229385) (by norm_num)
theorem B1037717 : Blo 271824 1037717 := bbase (se 6 (by rfl) ⟨24321, by rfl⟩ : syracuseStep 1037717 = 48643) (by norm_num)
theorem B611765 : Blo 271824 611765 := bbase (se 5 (by rfl) ⟨28676, by rfl⟩ : syracuseStep 611765 = 57353) (by norm_num)
theorem B611837 : Blo 271824 611837 := bbase (se 3 (by rfl) ⟨114719, by rfl⟩ : syracuseStep 611837 = 229439) (by norm_num)
theorem B611909 : Blo 271824 611909 := bbase (se 4 (by rfl) ⟨57366, by rfl⟩ : syracuseStep 611909 = 114733) (by norm_num)
theorem B611981 : Blo 271824 611981 := bbase (se 3 (by rfl) ⟨114746, by rfl⟩ : syracuseStep 611981 = 229493) (by norm_num)
theorem B1038005 : Blo 271824 1038005 := bbase (se 5 (by rfl) ⟨48656, by rfl⟩ : syracuseStep 1038005 = 97313) (by norm_num)
theorem B612053 : Blo 271824 612053 := bbase (se 7 (by rfl) ⟨7172, by rfl⟩ : syracuseStep 612053 = 14345) (by norm_num)
theorem B415477 : Blo 271824 415477 := bbase (se 5 (by rfl) ⟨19475, by rfl⟩ : syracuseStep 415477 = 38951) (by norm_num)
theorem B710405 : Blo 271824 710405 := bbase (se 4 (by rfl) ⟨66600, by rfl⟩ : syracuseStep 710405 = 133201) (by norm_num)
theorem B612125 : Blo 271824 612125 := bbase (se 3 (by rfl) ⟨114773, by rfl⟩ : syracuseStep 612125 = 229547) (by norm_num)
theorem B612197 : Blo 271824 612197 := bbase (se 4 (by rfl) ⟨57393, by rfl⟩ : syracuseStep 612197 = 114787) (by norm_num)
theorem B382837 : Blo 271824 382837 := bbase (se 5 (by rfl) ⟨17945, by rfl⟩ : syracuseStep 382837 = 35891) (by norm_num)
theorem B776101 : Blo 271824 776101 := bbase (se 4 (by rfl) ⟨72759, by rfl⟩ : syracuseStep 776101 = 145519) (by norm_num)
theorem B939941 : Blo 271824 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B612269 : Blo 271824 612269 := bbase (se 3 (by rfl) ⟨114800, by rfl⟩ : syracuseStep 612269 = 229601) (by norm_num)
theorem B612341 : Blo 271824 612341 := bbase (se 5 (by rfl) ⟨28703, by rfl⟩ : syracuseStep 612341 = 57407) (by norm_num)
theorem B415757 : Blo 271824 415757 := bbase (se 3 (by rfl) ⟨77954, by rfl⟩ : syracuseStep 415757 = 155909) (by norm_num)
theorem B612413 : Blo 271824 612413 := bbase (se 3 (by rfl) ⟨114827, by rfl⟩ : syracuseStep 612413 = 229655) (by norm_num)
theorem B874613 : Blo 271824 874613 := bbase (se 5 (by rfl) ⟨40997, by rfl⟩ : syracuseStep 874613 = 81995) (by norm_num)
theorem B612485 : Blo 271824 612485 := bbase (se 4 (by rfl) ⟨57420, by rfl⟩ : syracuseStep 612485 = 114841) (by norm_num)
theorem B612557 : Blo 271824 612557 := bbase (se 3 (by rfl) ⟨114854, by rfl⟩ : syracuseStep 612557 = 229709) (by norm_num)
theorem B612629 : Blo 271824 612629 := bbase (se 6 (by rfl) ⟨14358, by rfl⟩ : syracuseStep 612629 = 28717) (by norm_num)
theorem B612701 : Blo 271824 612701 := bbase (se 3 (by rfl) ⟨114881, by rfl⟩ : syracuseStep 612701 = 229763) (by norm_num)
theorem B612773 : Blo 271824 612773 := bbase (se 4 (by rfl) ⟨57447, by rfl⟩ : syracuseStep 612773 = 114895) (by norm_num)
theorem B612845 : Blo 271824 612845 := bbase (se 3 (by rfl) ⟨114908, by rfl⟩ : syracuseStep 612845 = 229817) (by norm_num)
theorem B1169909 : Blo 271824 1169909 := bbase (se 5 (by rfl) ⟨54839, by rfl⟩ : syracuseStep 1169909 = 109679) (by norm_num)
theorem B743957 : Blo 271824 743957 := bbase (se 6 (by rfl) ⟨17436, by rfl⟩ : syracuseStep 743957 = 34873) (by norm_num)
theorem B612917 : Blo 271824 612917 := bbase (se 5 (by rfl) ⟨28730, by rfl⟩ : syracuseStep 612917 = 57461) (by norm_num)
theorem B612989 : Blo 271824 612989 := bbase (se 3 (by rfl) ⟨114935, by rfl⟩ : syracuseStep 612989 = 229871) (by norm_num)
theorem B416389 : Blo 271824 416389 := bbase (se 4 (by rfl) ⟨39036, by rfl⟩ : syracuseStep 416389 = 78073) (by norm_num)
theorem B613061 : Blo 271824 613061 := bbase (se 4 (by rfl) ⟨57474, by rfl⟩ : syracuseStep 613061 = 114949) (by norm_num)
theorem B613133 : Blo 271824 613133 := bbase (se 3 (by rfl) ⟨114962, by rfl⟩ : syracuseStep 613133 = 229925) (by norm_num)
theorem B613205 : Blo 271824 613205 := bbase (se 9 (by rfl) ⟨1796, by rfl⟩ : syracuseStep 613205 = 3593) (by norm_num)
theorem B1039189 : Blo 271824 1039189 := bbase (se 9 (by rfl) ⟨3044, by rfl⟩ : syracuseStep 1039189 = 6089) (by norm_num)
theorem B613277 : Blo 271824 613277 := bbase (se 3 (by rfl) ⟨114989, by rfl⟩ : syracuseStep 613277 = 229979) (by norm_num)
theorem B613349 : Blo 271824 613349 := bbase (se 4 (by rfl) ⟨57501, by rfl⟩ : syracuseStep 613349 = 115003) (by norm_num)
theorem B777205 : Blo 271824 777205 := bbase (se 5 (by rfl) ⟨36431, by rfl⟩ : syracuseStep 777205 = 72863) (by norm_num)
theorem B613421 : Blo 271824 613421 := bbase (se 3 (by rfl) ⟨115016, by rfl⟩ : syracuseStep 613421 = 230033) (by norm_num)
theorem B580709 : Blo 271824 580709 := bbase (se 4 (by rfl) ⟨54441, by rfl⟩ : syracuseStep 580709 = 108883) (by norm_num)
theorem B580717 : Blo 271824 580717 := bbase (se 3 (by rfl) ⟨108884, by rfl⟩ : syracuseStep 580717 = 217769) (by norm_num)
theorem B613493 : Blo 271824 613493 := bbase (se 5 (by rfl) ⟨28757, by rfl⟩ : syracuseStep 613493 = 57515) (by norm_num)
theorem B1039493 : Blo 271824 1039493 := bbase (se 4 (by rfl) ⟨97452, by rfl⟩ : syracuseStep 1039493 = 194905) (by norm_num)
theorem B613565 : Blo 271824 613565 := bbase (se 3 (by rfl) ⟨115043, by rfl⟩ : syracuseStep 613565 = 230087) (by norm_num)
theorem B318697 : Blo 271824 318697 := bbase (se 2 (by rfl) ⟨119511, by rfl⟩ : syracuseStep 318697 = 239023) (by norm_num)
theorem B613637 : Blo 271824 613637 := bbase (se 4 (by rfl) ⟨57528, by rfl⟩ : syracuseStep 613637 = 115057) (by norm_num)
theorem B613709 : Blo 271824 613709 := bbase (se 3 (by rfl) ⟨115070, by rfl⟩ : syracuseStep 613709 = 230141) (by norm_num)
theorem B613781 : Blo 271824 613781 := bbase (se 6 (by rfl) ⟨14385, by rfl⟩ : syracuseStep 613781 = 28771) (by norm_num)
theorem B2219413 : Blo 271824 2219413 := bbase (se 6 (by rfl) ⟨52017, by rfl⟩ : syracuseStep 2219413 = 104035) (by norm_num)
theorem B2088341 : Blo 271824 2088341 := bbase (se 6 (by rfl) ⟨48945, by rfl⟩ : syracuseStep 2088341 = 97891) (by norm_num)
theorem B613853 : Blo 271824 613853 := bbase (se 3 (by rfl) ⟨115097, by rfl⟩ : syracuseStep 613853 = 230195) (by norm_num)
theorem B613925 : Blo 271824 613925 := bbase (se 4 (by rfl) ⟨57555, by rfl⟩ : syracuseStep 613925 = 115111) (by norm_num)
theorem B613997 : Blo 271824 613997 := bbase (se 3 (by rfl) ⟨115124, by rfl⟩ : syracuseStep 613997 = 230249) (by norm_num)
theorem B614069 : Blo 271824 614069 := bbase (se 5 (by rfl) ⟨28784, by rfl⟩ : syracuseStep 614069 = 57569) (by norm_num)
theorem B614141 : Blo 271824 614141 := bbase (se 3 (by rfl) ⟨115151, by rfl⟩ : syracuseStep 614141 = 230303) (by norm_num)
theorem B614213 : Blo 271824 614213 := bbase (se 4 (by rfl) ⟨57582, by rfl⟩ : syracuseStep 614213 = 115165) (by norm_num)
theorem B614285 : Blo 271824 614285 := bbase (se 3 (by rfl) ⟨115178, by rfl⟩ : syracuseStep 614285 = 230357) (by norm_num)
theorem B614357 : Blo 271824 614357 := bbase (se 7 (by rfl) ⟨7199, by rfl⟩ : syracuseStep 614357 = 14399) (by norm_num)
theorem B516125 : Blo 271824 516125 := bbase (se 3 (by rfl) ⟨96773, by rfl⟩ : syracuseStep 516125 = 193547) (by norm_num)
theorem B614429 : Blo 271824 614429 := bbase (se 3 (by rfl) ⟨115205, by rfl⟩ : syracuseStep 614429 = 230411) (by norm_num)
theorem B614501 : Blo 271824 614501 := bbase (se 4 (by rfl) ⟨57609, by rfl⟩ : syracuseStep 614501 = 115219) (by norm_num)
theorem B516269 : Blo 271824 516269 := bbase (se 3 (by rfl) ⟨96800, by rfl⟩ : syracuseStep 516269 = 193601) (by norm_num)
theorem B614573 : Blo 271824 614573 := bbase (se 3 (by rfl) ⟨115232, by rfl⟩ : syracuseStep 614573 = 230465) (by norm_num)
theorem B581845 : Blo 271824 581845 := bbase (se 7 (by rfl) ⟨6818, by rfl⟩ : syracuseStep 581845 = 13637) (by norm_num)
theorem B1171685 : Blo 271824 1171685 := bbase (se 4 (by rfl) ⟨109845, by rfl⟩ : syracuseStep 1171685 = 219691) (by norm_num)
theorem B614645 : Blo 271824 614645 := bbase (se 5 (by rfl) ⟨28811, by rfl⟩ : syracuseStep 614645 = 57623) (by norm_num)
theorem B614717 : Blo 271824 614717 := bbase (se 3 (by rfl) ⟨115259, by rfl⟩ : syracuseStep 614717 = 230519) (by norm_num)
theorem B876869 : Blo 271824 876869 := bbase (se 4 (by rfl) ⟨82206, by rfl⟩ : syracuseStep 876869 = 164413) (by norm_num)
theorem B418117 : Blo 271824 418117 := bbase (se 4 (by rfl) ⟨39198, by rfl⟩ : syracuseStep 418117 = 78397) (by norm_num)
theorem B614789 : Blo 271824 614789 := bbase (se 4 (by rfl) ⟨57636, by rfl⟩ : syracuseStep 614789 = 115273) (by norm_num)
theorem B516557 : Blo 271824 516557 := bbase (se 3 (by rfl) ⟨96854, by rfl⟩ : syracuseStep 516557 = 193709) (by norm_num)
theorem B614861 : Blo 271824 614861 := bbase (se 3 (by rfl) ⟨115286, by rfl⟩ : syracuseStep 614861 = 230573) (by norm_num)
theorem B778709 : Blo 271824 778709 := bbase (se 7 (by rfl) ⟨9125, by rfl⟩ : syracuseStep 778709 = 18251) (by norm_num)
theorem B614933 : Blo 271824 614933 := bbase (se 6 (by rfl) ⟨14412, by rfl⟩ : syracuseStep 614933 = 28825) (by norm_num)
theorem B582221 : Blo 271824 582221 := bbase (se 3 (by rfl) ⟨109166, by rfl⟩ : syracuseStep 582221 = 218333) (by norm_num)
theorem B615005 : Blo 271824 615005 := bbase (se 3 (by rfl) ⟨115313, by rfl⟩ : syracuseStep 615005 = 230627) (by norm_num)
theorem B516709 : Blo 271824 516709 := bbase (se 4 (by rfl) ⟨48441, by rfl⟩ : syracuseStep 516709 = 96883) (by norm_num)
theorem B615077 : Blo 271824 615077 := bbase (se 4 (by rfl) ⟨57663, by rfl⟩ : syracuseStep 615077 = 115327) (by norm_num)
theorem B615149 : Blo 271824 615149 := bbase (se 3 (by rfl) ⟨115340, by rfl⟩ : syracuseStep 615149 = 230681) (by norm_num)
theorem B615221 : Blo 271824 615221 := bbase (se 5 (by rfl) ⟨28838, by rfl⟩ : syracuseStep 615221 = 57677) (by norm_num)
theorem B615293 : Blo 271824 615293 := bbase (se 3 (by rfl) ⟨115367, by rfl⟩ : syracuseStep 615293 = 230735) (by norm_num)
theorem B517013 : Blo 271824 517013 := bbase (se 6 (by rfl) ⟨12117, by rfl⟩ : syracuseStep 517013 = 24235) (by norm_num)
theorem B615365 : Blo 271824 615365 := bbase (se 4 (by rfl) ⟨57690, by rfl⟩ : syracuseStep 615365 = 115381) (by norm_num)
theorem B615437 : Blo 271824 615437 := bbase (se 3 (by rfl) ⟨115394, by rfl⟩ : syracuseStep 615437 = 230789) (by norm_num)
theorem B877637 : Blo 271824 877637 := bbase (se 4 (by rfl) ⟨82278, by rfl⟩ : syracuseStep 877637 = 164557) (by norm_num)
theorem B615509 : Blo 271824 615509 := bbase (se 8 (by rfl) ⟨3606, by rfl⟩ : syracuseStep 615509 = 7213) (by norm_num)
theorem B353381 : Blo 271824 353381 := bbase (se 4 (by rfl) ⟨33129, by rfl⟩ : syracuseStep 353381 = 66259) (by norm_num)
theorem B615581 : Blo 271824 615581 := bbase (se 3 (by rfl) ⟨115421, by rfl⟩ : syracuseStep 615581 = 230843) (by norm_num)
theorem B1041605 : Blo 271824 1041605 := bbase (se 4 (by rfl) ⟨97650, by rfl⟩ : syracuseStep 1041605 = 195301) (by norm_num)
theorem B1172677 : Blo 271824 1172677 := bbase (se 4 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 1172677 = 219877) (by norm_num)
theorem B615653 : Blo 271824 615653 := bbase (se 4 (by rfl) ⟨57717, by rfl⟩ : syracuseStep 615653 = 115435) (by norm_num)
theorem B615725 : Blo 271824 615725 := bbase (se 3 (by rfl) ⟨115448, by rfl⟩ : syracuseStep 615725 = 230897) (by norm_num)
theorem B615797 : Blo 271824 615797 := bbase (se 5 (by rfl) ⟨28865, by rfl⟩ : syracuseStep 615797 = 57731) (by norm_num)
theorem B615869 : Blo 271824 615869 := bbase (se 3 (by rfl) ⟨115475, by rfl⟩ : syracuseStep 615869 = 230951) (by norm_num)
theorem B1041893 : Blo 271824 1041893 := bbase (se 4 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 1041893 = 195355) (by norm_num)
theorem B615941 : Blo 271824 615941 := bbase (se 4 (by rfl) ⟨57744, by rfl⟩ : syracuseStep 615941 = 115489) (by norm_num)
theorem B878149 : Blo 271824 878149 := bbase (se 4 (by rfl) ⟨82326, by rfl⟩ : syracuseStep 878149 = 164653) (by norm_num)
theorem B616013 : Blo 271824 616013 := bbase (se 3 (by rfl) ⟨115502, by rfl⟩ : syracuseStep 616013 = 231005) (by norm_num)
theorem B2647637 : Blo 271824 2647637 := bbase (se 8 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 2647637 = 31027) (by norm_num)
theorem B517765 : Blo 271824 517765 := bbase (se 4 (by rfl) ⟨48540, by rfl⟩ : syracuseStep 517765 = 97081) (by norm_num)
theorem B616085 : Blo 271824 616085 := bbase (se 6 (by rfl) ⟨14439, by rfl⟩ : syracuseStep 616085 = 28879) (by norm_num)
theorem B1926805 : Blo 271824 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B4187861 : Blo 271824 4187861 := bbase (se 7 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 4187861 = 98153) (by norm_num)
theorem B616157 : Blo 271824 616157 := bbase (se 3 (by rfl) ⟨115529, by rfl⟩ : syracuseStep 616157 = 231059) (by norm_num)
theorem B517909 : Blo 271824 517909 := bbase (se 6 (by rfl) ⟨12138, by rfl⟩ : syracuseStep 517909 = 24277) (by norm_num)
theorem B1566485 : Blo 271824 1566485 := bbase (se 6 (by rfl) ⟨36714, by rfl⟩ : syracuseStep 1566485 = 73429) (by norm_num)
theorem B616229 : Blo 271824 616229 := bbase (se 4 (by rfl) ⟨57771, by rfl⟩ : syracuseStep 616229 = 115543) (by norm_num)
theorem B616301 : Blo 271824 616301 := bbase (se 3 (by rfl) ⟨115556, by rfl⟩ : syracuseStep 616301 = 231113) (by norm_num)
theorem B518069 : Blo 271824 518069 := bbase (se 5 (by rfl) ⟨24284, by rfl⟩ : syracuseStep 518069 = 48569) (by norm_num)
theorem B616373 : Blo 271824 616373 := bbase (se 5 (by rfl) ⟨28892, by rfl⟩ : syracuseStep 616373 = 57785) (by norm_num)
theorem B7858133 : Blo 271824 7858133 := bbase (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) (by norm_num)
theorem B616445 : Blo 271824 616445 := bbase (se 3 (by rfl) ⟨115583, by rfl⟩ : syracuseStep 616445 = 231167) (by norm_num)
theorem B780293 : Blo 271824 780293 := bbase (se 4 (by rfl) ⟨73152, by rfl⟩ : syracuseStep 780293 = 146305) (by norm_num)
theorem B518213 : Blo 271824 518213 := bbase (se 4 (by rfl) ⟨48582, by rfl⟩ : syracuseStep 518213 = 97165) (by norm_num)
theorem B616517 : Blo 271824 616517 := bbase (se 4 (by rfl) ⟨57798, by rfl⟩ : syracuseStep 616517 = 115597) (by norm_num)
theorem B616589 : Blo 271824 616589 := bbase (se 3 (by rfl) ⟨115610, by rfl⟩ : syracuseStep 616589 = 231221) (by norm_num)
theorem B583861 : Blo 271824 583861 := bbase (se 5 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 583861 = 54737) (by norm_num)
theorem B551117 : Blo 271824 551117 := bbase (se 3 (by rfl) ⟨103334, by rfl⟩ : syracuseStep 551117 = 206669) (by norm_num)
theorem B616661 : Blo 271824 616661 := bbase (se 7 (by rfl) ⟨7226, by rfl⟩ : syracuseStep 616661 = 14453) (by norm_num)
theorem B616733 : Blo 271824 616733 := bbase (se 3 (by rfl) ⟨115637, by rfl⟩ : syracuseStep 616733 = 231275) (by norm_num)
theorem B518501 : Blo 271824 518501 := bbase (se 4 (by rfl) ⟨48609, by rfl⟩ : syracuseStep 518501 = 97219) (by norm_num)
theorem B616805 : Blo 271824 616805 := bbase (se 4 (by rfl) ⟨57825, by rfl⟩ : syracuseStep 616805 = 115651) (by norm_num)
theorem B616877 : Blo 271824 616877 := bbase (se 3 (by rfl) ⟨115664, by rfl⟩ : syracuseStep 616877 = 231329) (by norm_num)
theorem B387509 : Blo 271824 387509 := bbase (se 5 (by rfl) ⟨18164, by rfl⟩ : syracuseStep 387509 = 36329) (by norm_num)
theorem B616949 : Blo 271824 616949 := bbase (se 5 (by rfl) ⟨28919, by rfl⟩ : syracuseStep 616949 = 57839) (by norm_num)
theorem B518653 : Blo 271824 518653 := bbase (se 3 (by rfl) ⟨97247, by rfl⟩ : syracuseStep 518653 = 194495) (by norm_num)
theorem B617021 : Blo 271824 617021 := bbase (se 3 (by rfl) ⟨115691, by rfl⟩ : syracuseStep 617021 = 231383) (by norm_num)
theorem B617093 : Blo 271824 617093 := bbase (se 4 (by rfl) ⟨57852, by rfl⟩ : syracuseStep 617093 = 115705) (by norm_num)
theorem B1043077 : Blo 271824 1043077 := bbase (se 4 (by rfl) ⟨97788, by rfl⟩ : syracuseStep 1043077 = 195577) (by norm_num)
theorem B780965 : Blo 271824 780965 := bbase (se 4 (by rfl) ⟨73215, by rfl⟩ : syracuseStep 780965 = 146431) (by norm_num)
theorem B617165 : Blo 271824 617165 := bbase (se 3 (by rfl) ⟨115718, by rfl⟩ : syracuseStep 617165 = 231437) (by norm_num)
theorem B617237 : Blo 271824 617237 := bbase (se 6 (by rfl) ⟨14466, by rfl⟩ : syracuseStep 617237 = 28933) (by norm_num)
theorem B518957 : Blo 271824 518957 := bbase (se 3 (by rfl) ⟨97304, by rfl⟩ : syracuseStep 518957 = 194609) (by norm_num)
theorem B617309 : Blo 271824 617309 := bbase (se 3 (by rfl) ⟨115745, by rfl⟩ : syracuseStep 617309 = 231491) (by norm_num)
theorem B617381 : Blo 271824 617381 := bbase (se 4 (by rfl) ⟨57879, by rfl⟩ : syracuseStep 617381 = 115759) (by norm_num)
theorem B355249 : Blo 271824 355249 := bbase (se 2 (by rfl) ⟨133218, by rfl⟩ : syracuseStep 355249 = 266437) (by norm_num)
theorem B1043381 : Blo 271824 1043381 := bbase (se 5 (by rfl) ⟨48908, by rfl⟩ : syracuseStep 1043381 = 97817) (by norm_num)
theorem B617453 : Blo 271824 617453 := bbase (se 3 (by rfl) ⟨115772, by rfl⟩ : syracuseStep 617453 = 231545) (by norm_num)
theorem B584749 : Blo 271824 584749 := bbase (se 3 (by rfl) ⟨109640, by rfl⟩ : syracuseStep 584749 = 219281) (by norm_num)
theorem B617525 : Blo 271824 617525 := bbase (se 5 (by rfl) ⟨28946, by rfl⟩ : syracuseStep 617525 = 57893) (by norm_num)
theorem B781397 : Blo 271824 781397 := bbase (se 8 (by rfl) ⟨4578, by rfl⟩ : syracuseStep 781397 = 9157) (by norm_num)
theorem B617597 : Blo 271824 617597 := bbase (se 3 (by rfl) ⟨115799, by rfl⟩ : syracuseStep 617597 = 231599) (by norm_num)
theorem B388261 : Blo 271824 388261 := bbase (se 4 (by rfl) ⟨36399, by rfl⟩ : syracuseStep 388261 = 72799) (by norm_num)
theorem B1109189 : Blo 271824 1109189 := bbase (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) (by norm_num)
theorem B617669 : Blo 271824 617669 := bbase (se 4 (by rfl) ⟨57906, by rfl⟩ : syracuseStep 617669 = 115813) (by norm_num)
theorem B617741 : Blo 271824 617741 := bbase (se 3 (by rfl) ⟨115826, by rfl⟩ : syracuseStep 617741 = 231653) (by norm_num)
theorem B879893 : Blo 271824 879893 := bbase (se 6 (by rfl) ⟨20622, by rfl⟩ : syracuseStep 879893 = 41245) (by norm_num)
theorem B617813 : Blo 271824 617813 := bbase (se 11 (by rfl) ⟨452, by rfl⟩ : syracuseStep 617813 = 905) (by norm_num)
theorem B552349 : Blo 271824 552349 := bbase (se 3 (by rfl) ⟨103565, by rfl⟩ : syracuseStep 552349 = 207131) (by norm_num)
theorem B617885 : Blo 271824 617885 := bbase (se 3 (by rfl) ⟨115853, by rfl⟩ : syracuseStep 617885 = 231707) (by norm_num)
theorem B880085 : Blo 271824 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B552413 : Blo 271824 552413 := bbase (se 3 (by rfl) ⟨103577, by rfl⟩ : syracuseStep 552413 = 207155) (by norm_num)
theorem B617957 : Blo 271824 617957 := bbase (se 4 (by rfl) ⟨57933, by rfl⟩ : syracuseStep 617957 = 115867) (by norm_num)
theorem B519709 : Blo 271824 519709 := bbase (se 3 (by rfl) ⟨97445, by rfl⟩ : syracuseStep 519709 = 194891) (by norm_num)
theorem B585245 : Blo 271824 585245 := bbase (se 3 (by rfl) ⟨109733, by rfl⟩ : syracuseStep 585245 = 219467) (by norm_num)
theorem B618029 : Blo 271824 618029 := bbase (se 3 (by rfl) ⟨115880, by rfl⟩ : syracuseStep 618029 = 231761) (by norm_num)
theorem B618101 : Blo 271824 618101 := bbase (se 5 (by rfl) ⟨28973, by rfl⟩ : syracuseStep 618101 = 57947) (by norm_num)
theorem B519853 : Blo 271824 519853 := bbase (se 3 (by rfl) ⟨97472, by rfl⟩ : syracuseStep 519853 = 194945) (by norm_num)
theorem B618173 : Blo 271824 618173 := bbase (se 3 (by rfl) ⟨115907, by rfl⟩ : syracuseStep 618173 = 231815) (by norm_num)
theorem B618245 : Blo 271824 618245 := bbase (se 4 (by rfl) ⟨57960, by rfl⟩ : syracuseStep 618245 = 115921) (by norm_num)
theorem B782149 : Blo 271824 782149 := bbase (se 4 (by rfl) ⟨73326, by rfl⟩ : syracuseStep 782149 = 146653) (by norm_num)
theorem B520013 : Blo 271824 520013 := bbase (se 3 (by rfl) ⟨97502, by rfl⟩ : syracuseStep 520013 = 195005) (by norm_num)
theorem B618317 : Blo 271824 618317 := bbase (se 3 (by rfl) ⟨115934, by rfl⟩ : syracuseStep 618317 = 231869) (by norm_num)
theorem B618389 : Blo 271824 618389 := bbase (se 6 (by rfl) ⟨14493, by rfl⟩ : syracuseStep 618389 = 28987) (by norm_num)
theorem B716701 : Blo 271824 716701 := bbase (se 3 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 716701 = 268763) (by norm_num)
theorem B389053 : Blo 271824 389053 := bbase (se 3 (by rfl) ⟨72947, by rfl⟩ : syracuseStep 389053 = 145895) (by norm_num)
theorem B520157 : Blo 271824 520157 := bbase (se 3 (by rfl) ⟨97529, by rfl⟩ : syracuseStep 520157 = 195059) (by norm_num)
theorem B618461 : Blo 271824 618461 := bbase (se 3 (by rfl) ⟨115961, by rfl⟩ : syracuseStep 618461 = 231923) (by norm_num)
theorem B290837 : Blo 271824 290837 := bbase (se 6 (by rfl) ⟨6816, by rfl⟩ : syracuseStep 290837 = 13633) (by norm_num)
theorem B618533 : Blo 271824 618533 := bbase (se 4 (by rfl) ⟨57987, by rfl⟩ : syracuseStep 618533 = 115975) (by norm_num)
theorem B618605 : Blo 271824 618605 := bbase (se 3 (by rfl) ⟨115988, by rfl⟩ : syracuseStep 618605 = 231977) (by norm_num)
theorem B553109 : Blo 271824 553109 := bbase (se 6 (by rfl) ⟨12963, by rfl⟩ : syracuseStep 553109 = 25927) (by norm_num)
theorem B618677 : Blo 271824 618677 := bbase (se 5 (by rfl) ⟨29000, by rfl⟩ : syracuseStep 618677 = 58001) (by norm_num)
theorem B618749 : Blo 271824 618749 := bbase (se 3 (by rfl) ⟨116015, by rfl⟩ : syracuseStep 618749 = 232031) (by norm_num)
theorem B520445 : Blo 271824 520445 := bbase (se 3 (by rfl) ⟨97583, by rfl⟩ : syracuseStep 520445 = 195167) (by norm_num)
theorem B389389 : Blo 271824 389389 := bbase (se 3 (by rfl) ⟨73010, by rfl⟩ : syracuseStep 389389 = 146021) (by norm_num)
theorem B1241413 : Blo 271824 1241413 := bbase (se 4 (by rfl) ⟨116382, by rfl⟩ : syracuseStep 1241413 = 232765) (by norm_num)
theorem B618821 : Blo 271824 618821 := bbase (se 4 (by rfl) ⟨58014, by rfl⟩ : syracuseStep 618821 = 116029) (by norm_num)
theorem B586109 : Blo 271824 586109 := bbase (se 3 (by rfl) ⟨109895, by rfl⟩ : syracuseStep 586109 = 219791) (by norm_num)
theorem B618893 : Blo 271824 618893 := bbase (se 3 (by rfl) ⟨116042, by rfl⟩ : syracuseStep 618893 = 232085) (by norm_num)
theorem B520597 : Blo 271824 520597 := bbase (se 6 (by rfl) ⟨12201, by rfl⟩ : syracuseStep 520597 = 24403) (by norm_num)
theorem B291281 : Blo 271824 291281 := bbase (se 2 (by rfl) ⟨109230, by rfl⟩ : syracuseStep 291281 = 218461) (by norm_num)
theorem B618965 : Blo 271824 618965 := bbase (se 7 (by rfl) ⟨7253, by rfl⟩ : syracuseStep 618965 = 14507) (by norm_num)
theorem B389605 : Blo 271824 389605 := bbase (se 4 (by rfl) ⟨36525, by rfl⟩ : syracuseStep 389605 = 73051) (by norm_num)
theorem B586253 : Blo 271824 586253 := bbase (se 3 (by rfl) ⟨109922, by rfl⟩ : syracuseStep 586253 = 219845) (by norm_num)
theorem B619037 : Blo 271824 619037 := bbase (se 3 (by rfl) ⟨116069, by rfl⟩ : syracuseStep 619037 = 232139) (by norm_num)
theorem B1110629 : Blo 271824 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B619109 : Blo 271824 619109 := bbase (se 4 (by rfl) ⟨58041, by rfl⟩ : syracuseStep 619109 = 116083) (by norm_num)
theorem B619181 : Blo 271824 619181 := bbase (se 3 (by rfl) ⟨116096, by rfl⟩ : syracuseStep 619181 = 232193) (by norm_num)
theorem B520901 : Blo 271824 520901 := bbase (se 4 (by rfl) ⟨48834, by rfl⟩ : syracuseStep 520901 = 97669) (by norm_num)
theorem B291529 : Blo 271824 291529 := bbase (se 2 (by rfl) ⟨109323, by rfl⟩ : syracuseStep 291529 = 218647) (by norm_num)
theorem B619253 : Blo 271824 619253 := bbase (se 5 (by rfl) ⟨29027, by rfl⟩ : syracuseStep 619253 = 58055) (by norm_num)
theorem B619325 : Blo 271824 619325 := bbase (se 3 (by rfl) ⟨116123, by rfl⟩ : syracuseStep 619325 = 232247) (by norm_num)
theorem B1307461 : Blo 271824 1307461 := bbase (se 4 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 1307461 = 245149) (by norm_num)
theorem B389981 : Blo 271824 389981 := bbase (se 3 (by rfl) ⟨73121, by rfl⟩ : syracuseStep 389981 = 146243) (by norm_num)
theorem B619397 : Blo 271824 619397 := bbase (se 4 (by rfl) ⟨58068, by rfl⟩ : syracuseStep 619397 = 116137) (by norm_num)
theorem B619469 : Blo 271824 619469 := bbase (se 3 (by rfl) ⟨116150, by rfl⟩ : syracuseStep 619469 = 232301) (by norm_num)
theorem B1045493 : Blo 271824 1045493 := bbase (se 5 (by rfl) ⟨49007, by rfl⟩ : syracuseStep 1045493 = 98015) (by norm_num)
theorem B619541 : Blo 271824 619541 := bbase (se 6 (by rfl) ⟨14520, by rfl⟩ : syracuseStep 619541 = 29041) (by norm_num)
theorem B619613 : Blo 271824 619613 := bbase (se 3 (by rfl) ⟨116177, by rfl⟩ : syracuseStep 619613 = 232355) (by norm_num)
theorem B291961 : Blo 271824 291961 := bbase (se 2 (by rfl) ⟨109485, by rfl⟩ : syracuseStep 291961 = 218971) (by norm_num)
theorem B1766549 : Blo 271824 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B619685 : Blo 271824 619685 := bbase (se 4 (by rfl) ⟨58095, by rfl⟩ : syracuseStep 619685 = 116191) (by norm_num)
theorem B292033 : Blo 271824 292033 := bbase (se 2 (by rfl) ⟨109512, by rfl⟩ : syracuseStep 292033 = 219025) (by norm_num)
theorem B619757 : Blo 271824 619757 := bbase (se 3 (by rfl) ⟨116204, by rfl⟩ : syracuseStep 619757 = 232409) (by norm_num)
theorem B586997 : Blo 271824 586997 := bbase (se 5 (by rfl) ⟨27515, by rfl⟩ : syracuseStep 586997 = 55031) (by norm_num)
theorem B1045781 : Blo 271824 1045781 := bbase (se 6 (by rfl) ⟨24510, by rfl⟩ : syracuseStep 1045781 = 49021) (by norm_num)
theorem B619829 : Blo 271824 619829 := bbase (se 5 (by rfl) ⟨29054, by rfl⟩ : syracuseStep 619829 = 58109) (by norm_num)
theorem B619901 : Blo 271824 619901 := bbase (se 3 (by rfl) ⟨116231, by rfl⟩ : syracuseStep 619901 = 232463) (by norm_num)
theorem B521653 : Blo 271824 521653 := bbase (se 5 (by rfl) ⟨24452, by rfl⟩ : syracuseStep 521653 = 48905) (by norm_num)
theorem B619973 : Blo 271824 619973 := bbase (se 4 (by rfl) ⟨58122, by rfl⟩ : syracuseStep 619973 = 116245) (by norm_num)
theorem B620045 : Blo 271824 620045 := bbase (se 3 (by rfl) ⟨116258, by rfl⟩ : syracuseStep 620045 = 232517) (by norm_num)
theorem B292405 : Blo 271824 292405 := bbase (se 5 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 292405 = 27413) (by norm_num)
theorem B521797 : Blo 271824 521797 := bbase (se 4 (by rfl) ⟨48918, by rfl⟩ : syracuseStep 521797 = 97837) (by norm_num)
theorem B2979413 : Blo 271824 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B620117 : Blo 271824 620117 := bbase (se 8 (by rfl) ⟨3633, by rfl⟩ : syracuseStep 620117 = 7267) (by norm_num)
theorem B620189 : Blo 271824 620189 := bbase (se 3 (by rfl) ⟨116285, by rfl⟩ : syracuseStep 620189 = 232571) (by norm_num)
theorem B554701 : Blo 271824 554701 := bbase (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) (by norm_num)
theorem B521957 : Blo 271824 521957 := bbase (se 4 (by rfl) ⟨48933, by rfl⟩ : syracuseStep 521957 = 97867) (by norm_num)
theorem B620261 : Blo 271824 620261 := bbase (se 4 (by rfl) ⟨58149, by rfl⟩ : syracuseStep 620261 = 116299) (by norm_num)
theorem B620333 : Blo 271824 620333 := bbase (se 3 (by rfl) ⟨116312, by rfl⟩ : syracuseStep 620333 = 232625) (by norm_num)
theorem B1242965 : Blo 271824 1242965 := bbase (se 9 (by rfl) ⟨3641, by rfl⟩ : syracuseStep 1242965 = 7283) (by norm_num)
theorem B522101 : Blo 271824 522101 := bbase (se 5 (by rfl) ⟨24473, by rfl⟩ : syracuseStep 522101 = 48947) (by norm_num)
theorem B620405 : Blo 271824 620405 := bbase (se 5 (by rfl) ⟨29081, by rfl⟩ : syracuseStep 620405 = 58163) (by norm_num)
theorem B292781 : Blo 271824 292781 := bbase (se 3 (by rfl) ⟨54896, by rfl⟩ : syracuseStep 292781 = 109793) (by norm_num)
theorem B620477 : Blo 271824 620477 := bbase (se 3 (by rfl) ⟨116339, by rfl⟩ : syracuseStep 620477 = 232679) (by norm_num)
theorem B587749 : Blo 271824 587749 := bbase (se 4 (by rfl) ⟨55101, by rfl⟩ : syracuseStep 587749 = 110203) (by norm_num)
theorem B292853 : Blo 271824 292853 := bbase (se 5 (by rfl) ⟨13727, by rfl⟩ : syracuseStep 292853 = 27455) (by norm_num)
theorem B620549 : Blo 271824 620549 := bbase (se 4 (by rfl) ⟨58176, by rfl⟩ : syracuseStep 620549 = 116353) (by norm_num)
theorem B1177685 : Blo 271824 1177685 := bbase (se 8 (by rfl) ⟨6900, by rfl⟩ : syracuseStep 1177685 = 13801) (by norm_num)
theorem B587893 : Blo 271824 587893 := bbase (se 5 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 587893 = 55115) (by norm_num)
theorem B653453 : Blo 271824 653453 := bbase (se 3 (by rfl) ⟨122522, by rfl⟩ : syracuseStep 653453 = 245045) (by norm_num)
theorem B522389 : Blo 271824 522389 := bbase (se 6 (by rfl) ⟨12243, by rfl⟩ : syracuseStep 522389 = 24487) (by norm_num)
theorem B293041 : Blo 271824 293041 := bbase (se 2 (by rfl) ⟨109890, by rfl⟩ : syracuseStep 293041 = 219781) (by norm_num)
theorem B981173 : Blo 271824 981173 := bbase (se 5 (by rfl) ⟨45992, by rfl⟩ : syracuseStep 981173 = 91985) (by norm_num)
theorem B391405 : Blo 271824 391405 := bbase (se 3 (by rfl) ⟨73388, by rfl⟩ : syracuseStep 391405 = 146777) (by norm_num)
theorem B522541 : Blo 271824 522541 := bbase (se 3 (by rfl) ⟨97976, by rfl⟩ : syracuseStep 522541 = 195953) (by norm_num)
theorem B751925 : Blo 271824 751925 := bbase (se 5 (by rfl) ⟨35246, by rfl⟩ : syracuseStep 751925 = 70493) (by norm_num)
theorem B293225 : Blo 271824 293225 := bbase (se 2 (by rfl) ⟨109959, by rfl⟩ : syracuseStep 293225 = 219919) (by norm_num)
theorem B555373 : Blo 271824 555373 := bbase (se 3 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 555373 = 208265) (by norm_num)
theorem B1177973 : Blo 271824 1177973 := bbase (se 5 (by rfl) ⟨55217, by rfl⟩ : syracuseStep 1177973 = 110435) (by norm_num)
theorem B1046965 : Blo 271824 1046965 := bbase (se 5 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 1046965 = 98153) (by norm_num)
theorem B588269 : Blo 271824 588269 := bbase (se 3 (by rfl) ⟨110300, by rfl⟩ : syracuseStep 588269 = 220601) (by norm_num)
theorem B522845 : Blo 271824 522845 := bbase (se 3 (by rfl) ⟨98033, by rfl⟩ : syracuseStep 522845 = 196067) (by norm_num)
theorem B784997 : Blo 271824 784997 := bbase (se 4 (by rfl) ⟨73593, by rfl⟩ : syracuseStep 784997 = 147187) (by norm_num)
theorem B490205 : Blo 271824 490205 := bbase (se 3 (by rfl) ⟨91913, by rfl⟩ : syracuseStep 490205 = 183827) (by norm_num)
theorem B1047269 : Blo 271824 1047269 := bbase (se 4 (by rfl) ⟨98181, by rfl⟩ : syracuseStep 1047269 = 196363) (by norm_num)
theorem B391997 : Blo 271824 391997 := bbase (se 3 (by rfl) ⟨73499, by rfl⟩ : syracuseStep 391997 = 146999) (by norm_num)
theorem B588637 : Blo 271824 588637 := bbase (se 3 (by rfl) ⟨110369, by rfl⟩ : syracuseStep 588637 = 220739) (by norm_num)
theorem B621437 : Blo 271824 621437 := bbase (se 3 (by rfl) ⟨116519, by rfl⟩ : syracuseStep 621437 = 233039) (by norm_num)
theorem B392077 : Blo 271824 392077 := bbase (se 3 (by rfl) ⟨73514, by rfl⟩ : syracuseStep 392077 = 147029) (by norm_num)
theorem B392197 : Blo 271824 392197 := bbase (se 4 (by rfl) ⟨36768, by rfl⟩ : syracuseStep 392197 = 73537) (by norm_num)
theorem B293977 : Blo 271824 293977 := bbase (se 2 (by rfl) ⟨110241, by rfl⟩ : syracuseStep 293977 = 220483) (by norm_num)
theorem B392293 : Blo 271824 392293 := bbase (se 4 (by rfl) ⟨36777, by rfl⟩ : syracuseStep 392293 = 73555) (by norm_num)
theorem B294049 : Blo 271824 294049 := bbase (se 2 (by rfl) ⟨110268, by rfl⟩ : syracuseStep 294049 = 220537) (by norm_num)
theorem B523597 : Blo 271824 523597 := bbase (se 3 (by rfl) ⟨98174, by rfl⟩ : syracuseStep 523597 = 196349) (by norm_num)
theorem B294229 : Blo 271824 294229 := bbase (se 11 (by rfl) ⟨215, by rfl⟩ : syracuseStep 294229 = 431) (by norm_num)
theorem B327125 : Blo 271824 327125 := bbase (se 7 (by rfl) ⟨3833, by rfl⟩ : syracuseStep 327125 = 7667) (by norm_num)
theorem B556541 : Blo 271824 556541 := bbase (se 3 (by rfl) ⟨104351, by rfl⟩ : syracuseStep 556541 = 208703) (by norm_num)
theorem B982613 : Blo 271824 982613 := bbase (se 8 (by rfl) ⟨5757, by rfl⟩ : syracuseStep 982613 = 11515) (by norm_num)
theorem B491221 : Blo 271824 491221 := bbase (se 7 (by rfl) ⟨5756, by rfl⟩ : syracuseStep 491221 = 11513) (by norm_num)
theorem B3211093 : Blo 271824 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B655229 : Blo 271824 655229 := bbase (se 3 (by rfl) ⟨122855, by rfl⟩ : syracuseStep 655229 = 245711) (by norm_num)
theorem B2326421 : Blo 271824 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B491437 : Blo 271824 491437 := bbase (se 3 (by rfl) ⟨92144, by rfl⟩ : syracuseStep 491437 = 184289) (by norm_num)
theorem B688085 : Blo 271824 688085 := bbase (se 7 (by rfl) ⟨8063, by rfl⟩ : syracuseStep 688085 = 16127) (by norm_num)
theorem B458851 : Blo 271824 458851 := bstep (se 1 (by rfl) ⟨344138, by rfl⟩ : syracuseStep 458851 = 688277) B688277
theorem B491683 : Blo 271824 491683 := bstep (se 1 (by rfl) ⟨368762, by rfl⟩ : syracuseStep 491683 = 737525) B737525
theorem B458993 : Blo 271824 458993 := bstep (se 2 (by rfl) ⟨172122, by rfl⟩ : syracuseStep 458993 = 344245) B344245
theorem B1179917 : Blo 271824 1179917 := bstep (se 3 (by rfl) ⟨221234, by rfl⟩ : syracuseStep 1179917 = 442469) B442469
theorem B917837 : Blo 271824 917837 := bstep (se 3 (by rfl) ⟨172094, by rfl⟩ : syracuseStep 917837 = 344189) B344189
theorem B459121 : Blo 271824 459121 := bstep (se 2 (by rfl) ⟨172170, by rfl⟩ : syracuseStep 459121 = 344341) B344341
theorem B917891 : Blo 271824 917891 := bstep (se 1 (by rfl) ⟨688418, by rfl⟩ : syracuseStep 917891 = 1376837) B1376837
theorem B1474957 : Blo 271824 1474957 := bstep (se 3 (by rfl) ⟨276554, by rfl⟩ : syracuseStep 1474957 = 553109) B553109
theorem B459155 : Blo 271824 459155 := bstep (se 1 (by rfl) ⟨344366, by rfl⟩ : syracuseStep 459155 = 688733) B688733
theorem B1376675 : Blo 271824 1376675 := bstep (se 1 (by rfl) ⟨1032506, by rfl⟩ : syracuseStep 1376675 = 2065013) B2065013
theorem B557489 : Blo 271824 557489 := bstep (se 2 (by rfl) ⟨209058, by rfl⟩ : syracuseStep 557489 = 418117) B418117
theorem B459283 : Blo 271824 459283 := bstep (se 1 (by rfl) ⟨344462, by rfl⟩ : syracuseStep 459283 = 688925) B688925
theorem B393859 : Blo 271824 393859 := bstep (se 1 (by rfl) ⟨295394, by rfl⟩ : syracuseStep 393859 = 590789) B590789
theorem B918161 : Blo 271824 918161 := bstep (se 2 (by rfl) ⟨344310, by rfl⟩ : syracuseStep 918161 = 688621) B688621
theorem B459425 : Blo 271824 459425 := bstep (se 2 (by rfl) ⟨172284, by rfl⟩ : syracuseStep 459425 = 344569) B344569
theorem B459553 : Blo 271824 459553 := bstep (se 2 (by rfl) ⟨172332, by rfl⟩ : syracuseStep 459553 = 344665) B344665
theorem B688945 : Blo 271824 688945 := bstep (se 2 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 688945 = 516709) B516709
theorem B459587 : Blo 271824 459587 := bstep (se 1 (by rfl) ⟨344690, by rfl⟩ : syracuseStep 459587 = 689381) B689381
theorem B328595 : Blo 271824 328595 := bstep (se 1 (by rfl) ⟨246446, by rfl⟩ : syracuseStep 328595 = 492893) B492893
theorem B656305 : Blo 271824 656305 := bstep (se 2 (by rfl) ⟨246114, by rfl⟩ : syracuseStep 656305 = 492229) B492229
theorem B459715 : Blo 271824 459715 := bstep (se 1 (by rfl) ⟨344786, by rfl⟩ : syracuseStep 459715 = 689573) B689573
theorem B1573829 : Blo 271824 1573829 := bstep (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) B295093
theorem B1868771 : Blo 271824 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B328691 : Blo 271824 328691 := bstep (se 1 (by rfl) ⟨246518, by rfl⟩ : syracuseStep 328691 = 493037) B493037
theorem B984113 : Blo 271824 984113 := bstep (se 2 (by rfl) ⟨369042, by rfl⟩ : syracuseStep 984113 = 738085) B738085
theorem B689219 : Blo 271824 689219 := bstep (se 1 (by rfl) ⟨516914, by rfl⟩ : syracuseStep 689219 = 1033829) B1033829
theorem B459857 : Blo 271824 459857 := bstep (se 2 (by rfl) ⟨172446, by rfl⟩ : syracuseStep 459857 = 344893) B344893
theorem B918701 : Blo 271824 918701 := bstep (se 3 (by rfl) ⟨172256, by rfl⟩ : syracuseStep 918701 = 344513) B344513
theorem B1377485 : Blo 271824 1377485 := bstep (se 3 (by rfl) ⟨258278, by rfl⟩ : syracuseStep 1377485 = 516557) B516557
theorem B459985 : Blo 271824 459985 := bstep (se 2 (by rfl) ⟨172494, by rfl⟩ : syracuseStep 459985 = 344989) B344989
theorem B918755 : Blo 271824 918755 := bstep (se 1 (by rfl) ⟨689066, by rfl⟩ : syracuseStep 918755 = 1378133) B1378133
theorem B460019 : Blo 271824 460019 := bstep (se 1 (by rfl) ⟨345014, by rfl⟩ : syracuseStep 460019 = 690029) B690029
theorem B689411 : Blo 271824 689411 := bstep (se 1 (by rfl) ⟨517058, by rfl⟩ : syracuseStep 689411 = 1034117) B1034117
theorem B7046513 : Blo 271824 7046513 := bstep (se 2 (by rfl) ⟨2642442, by rfl⟩ : syracuseStep 7046513 = 5284885) B5284885
theorem B460147 : Blo 271824 460147 := bstep (se 1 (by rfl) ⟨345110, by rfl⟩ : syracuseStep 460147 = 690221) B690221
theorem B919025 : Blo 271824 919025 := bstep (se 2 (by rfl) ⟨344634, by rfl⟩ : syracuseStep 919025 = 689269) B689269
theorem B460289 : Blo 271824 460289 := bstep (se 2 (by rfl) ⟨172608, by rfl⟩ : syracuseStep 460289 = 345217) B345217
theorem B460417 : Blo 271824 460417 := bstep (se 2 (by rfl) ⟨172656, by rfl⟩ : syracuseStep 460417 = 345313) B345313
theorem B460451 : Blo 271824 460451 := bstep (se 1 (by rfl) ⟨345338, by rfl⟩ : syracuseStep 460451 = 690677) B690677
theorem B6620869 : Blo 271824 6620869 := bstep (se 4 (by rfl) ⟨620706, by rfl⟩ : syracuseStep 6620869 = 1241413) B1241413
theorem B493283 : Blo 271824 493283 := bstep (se 1 (by rfl) ⟨369962, by rfl⟩ : syracuseStep 493283 = 739925) B739925
theorem B460579 : Blo 271824 460579 := bstep (se 1 (by rfl) ⟨345434, by rfl⟩ : syracuseStep 460579 = 690869) B690869
theorem B460721 : Blo 271824 460721 := bstep (se 2 (by rfl) ⟨172770, by rfl⟩ : syracuseStep 460721 = 345541) B345541
theorem B919565 : Blo 271824 919565 := bstep (se 3 (by rfl) ⟨172418, by rfl⟩ : syracuseStep 919565 = 344837) B344837
theorem B460849 : Blo 271824 460849 := bstep (se 2 (by rfl) ⟨172818, by rfl⟩ : syracuseStep 460849 = 345637) B345637
theorem B919619 : Blo 271824 919619 := bstep (se 1 (by rfl) ⟨689714, by rfl⟩ : syracuseStep 919619 = 1379429) B1379429
theorem B460883 : Blo 271824 460883 := bstep (se 1 (by rfl) ⟨345662, by rfl⟩ : syracuseStep 460883 = 691325) B691325
theorem B690353 : Blo 271824 690353 := bstep (se 2 (by rfl) ⟨258882, by rfl⟩ : syracuseStep 690353 = 517765) B517765
theorem B461011 : Blo 271824 461011 := bstep (se 1 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 461011 = 691517) B691517
theorem B690403 : Blo 271824 690403 := bstep (se 1 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 690403 = 1035605) B1035605
theorem B395521 : Blo 271824 395521 := bstep (se 2 (by rfl) ⟨148320, by rfl⟩ : syracuseStep 395521 = 296641) B296641
theorem B919889 : Blo 271824 919889 := bstep (se 2 (by rfl) ⟨344958, by rfl⟩ : syracuseStep 919889 = 689917) B689917
theorem B461153 : Blo 271824 461153 := bstep (se 2 (by rfl) ⟨172932, by rfl⟩ : syracuseStep 461153 = 345865) B345865
theorem B690545 : Blo 271824 690545 := bstep (se 2 (by rfl) ⟨258954, by rfl⟩ : syracuseStep 690545 = 517909) B517909
theorem B788945 : Blo 271824 788945 := bstep (se 2 (by rfl) ⟨295854, by rfl⟩ : syracuseStep 788945 = 591709) B591709
theorem B461281 : Blo 271824 461281 := bstep (se 2 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 461281 = 345961) B345961
theorem B461315 : Blo 271824 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B2066957 : Blo 271824 2066957 := bstep (se 3 (by rfl) ⟨387554, by rfl⟩ : syracuseStep 2066957 = 775109) B775109
theorem B461443 : Blo 271824 461443 := bstep (se 1 (by rfl) ⟨346082, by rfl⟩ : syracuseStep 461443 = 692165) B692165
theorem B461585 : Blo 271824 461585 := bstep (se 2 (by rfl) ⟨173094, by rfl⟩ : syracuseStep 461585 = 346189) B346189
theorem B4000565 : Blo 271824 4000565 := bstep (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) B375053
theorem B920429 : Blo 271824 920429 := bstep (se 3 (by rfl) ⟨172580, by rfl⟩ : syracuseStep 920429 = 345161) B345161
theorem B461713 : Blo 271824 461713 := bstep (se 2 (by rfl) ⟨173142, by rfl⟩ : syracuseStep 461713 = 346285) B346285
theorem B920483 : Blo 271824 920483 := bstep (se 1 (by rfl) ⟨690362, by rfl⟩ : syracuseStep 920483 = 1380725) B1380725
theorem B461747 : Blo 271824 461747 := bstep (se 1 (by rfl) ⟨346310, by rfl⟩ : syracuseStep 461747 = 692621) B692621
theorem B461875 : Blo 271824 461875 := bstep (se 1 (by rfl) ⟨346406, by rfl⟩ : syracuseStep 461875 = 692813) B692813
theorem B920753 : Blo 271824 920753 := bstep (se 2 (by rfl) ⟨345282, by rfl⟩ : syracuseStep 920753 = 690565) B690565
theorem B462017 : Blo 271824 462017 := bstep (se 2 (by rfl) ⟨173256, by rfl⟩ : syracuseStep 462017 = 346513) B346513
theorem B1969379 : Blo 271824 1969379 := bstep (se 1 (by rfl) ⟨1477034, by rfl⟩ : syracuseStep 1969379 = 2954069) B2954069
theorem B330979 : Blo 271824 330979 := bstep (se 1 (by rfl) ⟨248234, by rfl⟩ : syracuseStep 330979 = 496469) B496469
theorem B462145 : Blo 271824 462145 := bstep (se 2 (by rfl) ⟨173304, by rfl⟩ : syracuseStep 462145 = 346609) B346609
theorem B691537 : Blo 271824 691537 := bstep (se 2 (by rfl) ⟨259326, by rfl⟩ : syracuseStep 691537 = 518653) B518653
theorem B462179 : Blo 271824 462179 := bstep (se 1 (by rfl) ⟨346634, by rfl⟩ : syracuseStep 462179 = 693269) B693269
theorem B331123 : Blo 271824 331123 := bstep (se 1 (by rfl) ⟨248342, by rfl⟩ : syracuseStep 331123 = 496685) B496685
theorem B462307 : Blo 271824 462307 := bstep (se 1 (by rfl) ⟨346730, by rfl⟩ : syracuseStep 462307 = 693461) B693461
theorem B691811 : Blo 271824 691811 := bstep (se 1 (by rfl) ⟨518858, by rfl⟩ : syracuseStep 691811 = 1037717) B1037717
theorem B462449 : Blo 271824 462449 := bstep (se 2 (by rfl) ⟨173418, by rfl⟩ : syracuseStep 462449 = 346837) B346837
theorem B1773197 : Blo 271824 1773197 := bstep (se 3 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 1773197 = 664949) B664949
theorem B921293 : Blo 271824 921293 := bstep (se 3 (by rfl) ⟨172742, by rfl⟩ : syracuseStep 921293 = 345485) B345485
theorem B659171 : Blo 271824 659171 := bstep (se 1 (by rfl) ⟨494378, by rfl⟩ : syracuseStep 659171 = 988757) B988757
theorem B462577 : Blo 271824 462577 := bstep (se 2 (by rfl) ⟨173466, by rfl⟩ : syracuseStep 462577 = 346933) B346933
theorem B921347 : Blo 271824 921347 := bstep (se 1 (by rfl) ⟨691010, by rfl⟩ : syracuseStep 921347 = 1382021) B1382021
theorem B462611 : Blo 271824 462611 := bstep (se 1 (by rfl) ⟨346958, by rfl⟩ : syracuseStep 462611 = 693917) B693917
theorem B692003 : Blo 271824 692003 := bstep (se 1 (by rfl) ⟨519002, by rfl⟩ : syracuseStep 692003 = 1038005) B1038005
theorem B5345165 : Blo 271824 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B462739 : Blo 271824 462739 := bstep (se 1 (by rfl) ⟨347054, by rfl⟩ : syracuseStep 462739 = 694109) B694109
theorem B626627 : Blo 271824 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B1052621 : Blo 271824 1052621 := bstep (se 3 (by rfl) ⟨197366, by rfl⟩ : syracuseStep 1052621 = 394733) B394733
theorem B921617 : Blo 271824 921617 := bstep (se 2 (by rfl) ⟨345606, by rfl⟩ : syracuseStep 921617 = 691213) B691213
theorem B462881 : Blo 271824 462881 := bstep (se 2 (by rfl) ⟨173580, by rfl⟩ : syracuseStep 462881 = 347161) B347161
theorem B1380401 : Blo 271824 1380401 := bstep (se 2 (by rfl) ⟨517650, by rfl⟩ : syracuseStep 1380401 = 1035301) B1035301
theorem B1413197 : Blo 271824 1413197 := bstep (se 3 (by rfl) ⟨264974, by rfl⟩ : syracuseStep 1413197 = 529949) B529949
theorem B463009 : Blo 271824 463009 := bstep (se 2 (by rfl) ⟨173628, by rfl⟩ : syracuseStep 463009 = 347257) B347257
theorem B463043 : Blo 271824 463043 := bstep (se 1 (by rfl) ⟨347282, by rfl⟩ : syracuseStep 463043 = 694565) B694565
theorem B463171 : Blo 271824 463171 := bstep (se 1 (by rfl) ⟨347378, by rfl⟩ : syracuseStep 463171 = 694757) B694757
theorem B495971 : Blo 271824 495971 := bstep (se 1 (by rfl) ⟨371978, by rfl⟩ : syracuseStep 495971 = 743957) B743957
theorem B659843 : Blo 271824 659843 := bstep (se 1 (by rfl) ⟨494882, by rfl⟩ : syracuseStep 659843 = 989765) B989765
theorem B463313 : Blo 271824 463313 := bstep (se 2 (by rfl) ⟨173742, by rfl⟩ : syracuseStep 463313 = 347485) B347485
theorem B922157 : Blo 271824 922157 := bstep (se 3 (by rfl) ⟨172904, by rfl⟩ : syracuseStep 922157 = 345809) B345809
theorem B463441 : Blo 271824 463441 := bstep (se 2 (by rfl) ⟨173790, by rfl⟩ : syracuseStep 463441 = 347581) B347581
theorem B922211 : Blo 271824 922211 := bstep (se 1 (by rfl) ⟨691658, by rfl⟩ : syracuseStep 922211 = 1383317) B1383317
theorem B463475 : Blo 271824 463475 := bstep (se 1 (by rfl) ⟨347606, by rfl⟩ : syracuseStep 463475 = 695213) B695213
theorem B660113 : Blo 271824 660113 := bstep (se 2 (by rfl) ⟨247542, by rfl⟩ : syracuseStep 660113 = 495085) B495085
theorem B692945 : Blo 271824 692945 := bstep (se 2 (by rfl) ⟨259854, by rfl⟩ : syracuseStep 692945 = 519709) B519709
theorem B463603 : Blo 271824 463603 := bstep (se 1 (by rfl) ⟨347702, by rfl⟩ : syracuseStep 463603 = 695405) B695405
theorem B692995 : Blo 271824 692995 := bstep (se 1 (by rfl) ⟨519746, by rfl⟩ : syracuseStep 692995 = 1039493) B1039493
theorem B922481 : Blo 271824 922481 := bstep (se 2 (by rfl) ⟨345930, by rfl⟩ : syracuseStep 922481 = 691861) B691861
theorem B463745 : Blo 271824 463745 := bstep (se 2 (by rfl) ⟨173904, by rfl⟩ : syracuseStep 463745 = 347809) B347809
theorem B693137 : Blo 271824 693137 := bstep (se 2 (by rfl) ⟨259926, by rfl⟩ : syracuseStep 693137 = 519853) B519853
theorem B463873 : Blo 271824 463873 := bstep (se 2 (by rfl) ⟨173952, by rfl⟩ : syracuseStep 463873 = 347905) B347905
theorem B463907 : Blo 271824 463907 := bstep (se 1 (by rfl) ⟨347930, by rfl⟩ : syracuseStep 463907 = 695861) B695861
theorem B464035 : Blo 271824 464035 := bstep (se 1 (by rfl) ⟨348026, by rfl⟩ : syracuseStep 464035 = 696053) B696053
theorem B660689 : Blo 271824 660689 := bstep (se 2 (by rfl) ⟨247758, by rfl⟩ : syracuseStep 660689 = 495517) B495517
theorem B955601 : Blo 271824 955601 := bstep (se 2 (by rfl) ⟨358350, by rfl⟩ : syracuseStep 955601 = 716701) B716701
theorem B464177 : Blo 271824 464177 := bstep (se 2 (by rfl) ⟨174066, by rfl⟩ : syracuseStep 464177 = 348133) B348133
theorem B2069873 : Blo 271824 2069873 := bstep (se 2 (by rfl) ⟨776202, by rfl⟩ : syracuseStep 2069873 = 1552405) B1552405
theorem B923021 : Blo 271824 923021 := bstep (se 3 (by rfl) ⟨173066, by rfl⟩ : syracuseStep 923021 = 346133) B346133
theorem B660881 : Blo 271824 660881 := bstep (se 2 (by rfl) ⟨247830, by rfl⟩ : syracuseStep 660881 = 495661) B495661
theorem B464305 : Blo 271824 464305 := bstep (se 2 (by rfl) ⟨174114, by rfl⟩ : syracuseStep 464305 = 348229) B348229
theorem B923075 : Blo 271824 923075 := bstep (se 1 (by rfl) ⟨692306, by rfl⟩ : syracuseStep 923075 = 1384613) B1384613
theorem B464339 : Blo 271824 464339 := bstep (se 1 (by rfl) ⟨348254, by rfl⟩ : syracuseStep 464339 = 696509) B696509
theorem B1381859 : Blo 271824 1381859 := bstep (se 1 (by rfl) ⟨1036394, by rfl⟩ : syracuseStep 1381859 = 2072789) B2072789
theorem B3118661 : Blo 271824 3118661 := bstep (se 4 (by rfl) ⟨292374, by rfl⟩ : syracuseStep 3118661 = 584749) B584749
theorem B464467 : Blo 271824 464467 := bstep (se 1 (by rfl) ⟨348350, by rfl⟩ : syracuseStep 464467 = 696701) B696701
theorem B1939085 : Blo 271824 1939085 := bstep (se 3 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 1939085 = 727157) B727157
theorem B661169 : Blo 271824 661169 := bstep (se 2 (by rfl) ⟨247938, by rfl⟩ : syracuseStep 661169 = 495877) B495877
theorem B923345 : Blo 271824 923345 := bstep (se 2 (by rfl) ⟨346254, by rfl⟩ : syracuseStep 923345 = 692509) B692509
theorem B464609 : Blo 271824 464609 := bstep (se 2 (by rfl) ⟨174228, by rfl⟩ : syracuseStep 464609 = 348457) B348457
theorem B464737 : Blo 271824 464737 := bstep (se 2 (by rfl) ⟨174276, by rfl⟩ : syracuseStep 464737 = 348553) B348553
theorem B694129 : Blo 271824 694129 := bstep (se 2 (by rfl) ⟨260298, by rfl⟩ : syracuseStep 694129 = 520597) B520597
theorem B464771 : Blo 271824 464771 := bstep (se 1 (by rfl) ⟨348578, by rfl⟩ : syracuseStep 464771 = 697157) B697157
theorem B464899 : Blo 271824 464899 := bstep (se 1 (by rfl) ⟨348674, by rfl⟩ : syracuseStep 464899 = 697349) B697349
theorem B596003 : Blo 271824 596003 := bstep (se 1 (by rfl) ⟨447002, by rfl⟩ : syracuseStep 596003 = 894005) B894005
theorem B694403 : Blo 271824 694403 := bstep (se 1 (by rfl) ⟨520802, by rfl⟩ : syracuseStep 694403 = 1041605) B1041605
theorem B465041 : Blo 271824 465041 := bstep (se 2 (by rfl) ⟨174390, by rfl⟩ : syracuseStep 465041 = 348781) B348781
theorem B399587 : Blo 271824 399587 := bstep (se 1 (by rfl) ⟨299690, by rfl⟩ : syracuseStep 399587 = 599381) B599381
theorem B923885 : Blo 271824 923885 := bstep (se 3 (by rfl) ⟨173228, by rfl⟩ : syracuseStep 923885 = 346457) B346457
theorem B1382669 : Blo 271824 1382669 := bstep (se 3 (by rfl) ⟨259250, by rfl⟩ : syracuseStep 1382669 = 518501) B518501
theorem B792845 : Blo 271824 792845 := bstep (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) B297317
theorem B465169 : Blo 271824 465169 := bstep (se 2 (by rfl) ⟨174438, by rfl⟩ : syracuseStep 465169 = 348877) B348877
theorem B923939 : Blo 271824 923939 := bstep (se 1 (by rfl) ⟨692954, by rfl⟩ : syracuseStep 923939 = 1385909) B1385909
theorem B465203 : Blo 271824 465203 := bstep (se 1 (by rfl) ⟨348902, by rfl⟩ : syracuseStep 465203 = 697805) B697805
theorem B694595 : Blo 271824 694595 := bstep (se 1 (by rfl) ⟨520946, by rfl⟩ : syracuseStep 694595 = 1041893) B1041893
theorem B1743281 : Blo 271824 1743281 := bstep (se 2 (by rfl) ⟨653730, by rfl⟩ : syracuseStep 1743281 = 1307461) B1307461
theorem B465331 : Blo 271824 465331 := bstep (se 1 (by rfl) ⟨348998, by rfl⟩ : syracuseStep 465331 = 697997) B697997
theorem B2791907 : Blo 271824 2791907 := bstep (se 1 (by rfl) ⟨2093930, by rfl⟩ : syracuseStep 2791907 = 4187861) B4187861
theorem B924209 : Blo 271824 924209 := bstep (se 2 (by rfl) ⟨346578, by rfl⟩ : syracuseStep 924209 = 693157) B693157
theorem B367411 : Blo 271824 367411 := bstep (se 1 (by rfl) ⟨275558, by rfl⟩ : syracuseStep 367411 = 551117) B551117
theorem B924749 : Blo 271824 924749 := bstep (se 3 (by rfl) ⟨173390, by rfl⟩ : syracuseStep 924749 = 346781) B346781
theorem B924803 : Blo 271824 924803 := bstep (se 1 (by rfl) ⟨693602, by rfl⟩ : syracuseStep 924803 = 1387205) B1387205
theorem B695537 : Blo 271824 695537 := bstep (se 2 (by rfl) ⟨260826, by rfl⟩ : syracuseStep 695537 = 521653) B521653
theorem B695587 : Blo 271824 695587 := bstep (se 1 (by rfl) ⟨521690, by rfl⟩ : syracuseStep 695587 = 1043381) B1043381
theorem B4693301 : Blo 271824 4693301 := bstep (se 5 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 4693301 = 439997) B439997
theorem B925073 : Blo 271824 925073 := bstep (se 2 (by rfl) ⟨346902, by rfl⟩ : syracuseStep 925073 = 693805) B693805
theorem B695729 : Blo 271824 695729 := bstep (se 2 (by rfl) ⟨260898, by rfl⟩ : syracuseStep 695729 = 521797) B521797
theorem B630289 : Blo 271824 630289 := bstep (se 2 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 630289 = 472717) B472717
theorem B2629219 : Blo 271824 2629219 := bstep (se 1 (by rfl) ⟨1971914, by rfl⟩ : syracuseStep 2629219 = 3943829) B3943829
theorem B368275 : Blo 271824 368275 := bstep (se 1 (by rfl) ⟨276206, by rfl⟩ : syracuseStep 368275 = 552413) B552413
theorem B1187569 : Blo 271824 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B925613 : Blo 271824 925613 := bstep (se 3 (by rfl) ⟨173552, by rfl⟩ : syracuseStep 925613 = 347105) B347105
theorem B925667 : Blo 271824 925667 := bstep (se 1 (by rfl) ⟨694250, by rfl⟩ : syracuseStep 925667 = 1388501) B1388501
theorem B925937 : Blo 271824 925937 := bstep (se 2 (by rfl) ⟨347226, by rfl⟩ : syracuseStep 925937 = 694453) B694453
theorem B1548557 : Blo 271824 1548557 := bstep (se 3 (by rfl) ⟨290354, by rfl⟩ : syracuseStep 1548557 = 580709) B580709
theorem B696721 : Blo 271824 696721 := bstep (se 2 (by rfl) ⟨261270, by rfl⟩ : syracuseStep 696721 = 522541) B522541
theorem B1253987 : Blo 271824 1253987 := bstep (se 1 (by rfl) ⟨940490, by rfl⟩ : syracuseStep 1253987 = 1880981) B1880981
theorem B696995 : Blo 271824 696995 := bstep (se 1 (by rfl) ⟨522746, by rfl⟩ : syracuseStep 696995 = 1045493) B1045493
theorem B926477 : Blo 271824 926477 := bstep (se 3 (by rfl) ⟨173714, by rfl⟩ : syracuseStep 926477 = 347429) B347429
theorem B926531 : Blo 271824 926531 := bstep (se 1 (by rfl) ⟨694898, by rfl⟩ : syracuseStep 926531 = 1389797) B1389797
theorem B697187 : Blo 271824 697187 := bstep (se 1 (by rfl) ⟨522890, by rfl⟩ : syracuseStep 697187 = 1045781) B1045781
theorem B1057805 : Blo 271824 1057805 := bstep (se 3 (by rfl) ⟨198338, by rfl⟩ : syracuseStep 1057805 = 396677) B396677
theorem B926801 : Blo 271824 926801 := bstep (se 2 (by rfl) ⟨347550, by rfl⟩ : syracuseStep 926801 = 695101) B695101
theorem B1385585 : Blo 271824 1385585 := bstep (se 2 (by rfl) ⟨519594, by rfl⟩ : syracuseStep 1385585 = 1039189) B1039189
theorem B1549489 : Blo 271824 1549489 := bstep (se 2 (by rfl) ⟨581058, by rfl⟩ : syracuseStep 1549489 = 1162117) B1162117
theorem B828643 : Blo 271824 828643 := bstep (se 1 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 828643 = 1242965) B1242965
theorem B6628661 : Blo 271824 6628661 := bstep (se 5 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 6628661 = 621437) B621437
theorem B435635 : Blo 271824 435635 := bstep (se 1 (by rfl) ⟨326726, by rfl⟩ : syracuseStep 435635 = 653453) B653453
theorem B271827 : Blo 271824 271827 := bstep (se 1 (by rfl) ⟨203870, by rfl⟩ : syracuseStep 271827 = 407741) B407741
theorem B271843 : Blo 271824 271843 := bstep (se 1 (by rfl) ⟨203882, by rfl⟩ : syracuseStep 271843 = 407765) B407765
theorem B271859 : Blo 271824 271859 := bstep (se 1 (by rfl) ⟨203894, by rfl⟩ : syracuseStep 271859 = 407789) B407789
theorem B271875 : Blo 271824 271875 := bstep (se 1 (by rfl) ⟨203906, by rfl⟩ : syracuseStep 271875 = 407813) B407813
theorem B271891 : Blo 271824 271891 := bstep (se 1 (by rfl) ⟨203918, by rfl⟩ : syracuseStep 271891 = 407837) B407837
theorem B271907 : Blo 271824 271907 := bstep (se 1 (by rfl) ⟨203930, by rfl⟩ : syracuseStep 271907 = 407861) B407861
theorem B501283 : Blo 271824 501283 := bstep (se 1 (by rfl) ⟨375962, by rfl⟩ : syracuseStep 501283 = 751925) B751925
theorem B271923 : Blo 271824 271923 := bstep (se 1 (by rfl) ⟨203942, by rfl⟩ : syracuseStep 271923 = 407885) B407885
theorem B271939 : Blo 271824 271939 := bstep (se 1 (by rfl) ⟨203954, by rfl⟩ : syracuseStep 271939 = 407909) B407909
theorem B271955 : Blo 271824 271955 := bstep (se 1 (by rfl) ⟨203966, by rfl⟩ : syracuseStep 271955 = 407933) B407933
theorem B271971 : Blo 271824 271971 := bstep (se 1 (by rfl) ⟨203978, by rfl⟩ : syracuseStep 271971 = 407957) B407957
theorem B927341 : Blo 271824 927341 := bstep (se 3 (by rfl) ⟨173876, by rfl⟩ : syracuseStep 927341 = 347753) B347753
theorem B271987 : Blo 271824 271987 := bstep (se 1 (by rfl) ⟨203990, by rfl⟩ : syracuseStep 271987 = 407981) B407981
theorem B272003 : Blo 271824 272003 := bstep (se 1 (by rfl) ⟨204002, by rfl⟩ : syracuseStep 272003 = 408005) B408005
theorem B272019 : Blo 271824 272019 := bstep (se 1 (by rfl) ⟨204014, by rfl⟩ : syracuseStep 272019 = 408029) B408029
theorem B272035 : Blo 271824 272035 := bstep (se 1 (by rfl) ⟨204026, by rfl⟩ : syracuseStep 272035 = 408053) B408053
theorem B927395 : Blo 271824 927395 := bstep (se 1 (by rfl) ⟨695546, by rfl⟩ : syracuseStep 927395 = 1391093) B1391093
theorem B272051 : Blo 271824 272051 := bstep (se 1 (by rfl) ⟨204038, by rfl⟩ : syracuseStep 272051 = 408077) B408077
theorem B272067 : Blo 271824 272067 := bstep (se 1 (by rfl) ⟨204050, by rfl⟩ : syracuseStep 272067 = 408101) B408101
theorem B272083 : Blo 271824 272083 := bstep (se 1 (by rfl) ⟨204062, by rfl⟩ : syracuseStep 272083 = 408125) B408125
theorem B272099 : Blo 271824 272099 := bstep (se 1 (by rfl) ⟨204074, by rfl⟩ : syracuseStep 272099 = 408149) B408149
theorem B272115 : Blo 271824 272115 := bstep (se 1 (by rfl) ⟨204086, by rfl⟩ : syracuseStep 272115 = 408173) B408173
theorem B272131 : Blo 271824 272131 := bstep (se 1 (by rfl) ⟨204098, by rfl⟩ : syracuseStep 272131 = 408197) B408197
theorem B698129 : Blo 271824 698129 := bstep (se 2 (by rfl) ⟨261798, by rfl⟩ : syracuseStep 698129 = 523597) B523597
theorem B272147 : Blo 271824 272147 := bstep (se 1 (by rfl) ⟨204110, by rfl⟩ : syracuseStep 272147 = 408221) B408221
theorem B272163 : Blo 271824 272163 := bstep (se 1 (by rfl) ⟨204122, by rfl⟩ : syracuseStep 272163 = 408245) B408245
theorem B272179 : Blo 271824 272179 := bstep (se 1 (by rfl) ⟨204134, by rfl⟩ : syracuseStep 272179 = 408269) B408269
theorem B272195 : Blo 271824 272195 := bstep (se 1 (by rfl) ⟨204146, by rfl⟩ : syracuseStep 272195 = 408293) B408293
theorem B698179 : Blo 271824 698179 := bstep (se 1 (by rfl) ⟨523634, by rfl⟩ : syracuseStep 698179 = 1047269) B1047269
theorem B894797 : Blo 271824 894797 := bstep (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) B335549
theorem B272211 : Blo 271824 272211 := bstep (se 1 (by rfl) ⟨204158, by rfl⟩ : syracuseStep 272211 = 408317) B408317
theorem B272227 : Blo 271824 272227 := bstep (se 1 (by rfl) ⟨204170, by rfl⟩ : syracuseStep 272227 = 408341) B408341
theorem B2959217 : Blo 271824 2959217 := bstep (se 2 (by rfl) ⟨1109706, by rfl⟩ : syracuseStep 2959217 = 2219413) B2219413
theorem B272243 : Blo 271824 272243 := bstep (se 1 (by rfl) ⟨204182, by rfl⟩ : syracuseStep 272243 = 408365) B408365
theorem B272259 : Blo 271824 272259 := bstep (se 1 (by rfl) ⟨204194, by rfl⟩ : syracuseStep 272259 = 408389) B408389
theorem B272275 : Blo 271824 272275 := bstep (se 1 (by rfl) ⟨204206, by rfl⟩ : syracuseStep 272275 = 408413) B408413
theorem B272291 : Blo 271824 272291 := bstep (se 1 (by rfl) ⟨204218, by rfl⟩ : syracuseStep 272291 = 408437) B408437
theorem B927665 : Blo 271824 927665 := bstep (se 2 (by rfl) ⟨347874, by rfl⟩ : syracuseStep 927665 = 695749) B695749
theorem B272307 : Blo 271824 272307 := bstep (se 1 (by rfl) ⟨204230, by rfl⟩ : syracuseStep 272307 = 408461) B408461
theorem B272323 : Blo 271824 272323 := bstep (se 1 (by rfl) ⟨204242, by rfl⟩ : syracuseStep 272323 = 408485) B408485
theorem B272339 : Blo 271824 272339 := bstep (se 1 (by rfl) ⟨204254, by rfl⟩ : syracuseStep 272339 = 408509) B408509
theorem B272355 : Blo 271824 272355 := bstep (se 1 (by rfl) ⟨204266, by rfl⟩ : syracuseStep 272355 = 408533) B408533
theorem B272371 : Blo 271824 272371 := bstep (se 1 (by rfl) ⟨204278, by rfl⟩ : syracuseStep 272371 = 408557) B408557
theorem B272387 : Blo 271824 272387 := bstep (se 1 (by rfl) ⟨204290, by rfl⟩ : syracuseStep 272387 = 408581) B408581
theorem B272403 : Blo 271824 272403 := bstep (se 1 (by rfl) ⟨204302, by rfl⟩ : syracuseStep 272403 = 408605) B408605
theorem B272419 : Blo 271824 272419 := bstep (se 1 (by rfl) ⟨204314, by rfl⟩ : syracuseStep 272419 = 408629) B408629
theorem B272435 : Blo 271824 272435 := bstep (se 1 (by rfl) ⟨204326, by rfl⟩ : syracuseStep 272435 = 408653) B408653
theorem B272451 : Blo 271824 272451 := bstep (se 1 (by rfl) ⟨204338, by rfl⟩ : syracuseStep 272451 = 408677) B408677
theorem B272467 : Blo 271824 272467 := bstep (se 1 (by rfl) ⟨204350, by rfl⟩ : syracuseStep 272467 = 408701) B408701
theorem B272483 : Blo 271824 272483 := bstep (se 1 (by rfl) ⟨204362, by rfl⟩ : syracuseStep 272483 = 408725) B408725
theorem B272499 : Blo 271824 272499 := bstep (se 1 (by rfl) ⟨204374, by rfl⟩ : syracuseStep 272499 = 408749) B408749
theorem B272515 : Blo 271824 272515 := bstep (se 1 (by rfl) ⟨204386, by rfl⟩ : syracuseStep 272515 = 408773) B408773
theorem B272531 : Blo 271824 272531 := bstep (se 1 (by rfl) ⟨204398, by rfl⟩ : syracuseStep 272531 = 408797) B408797
theorem B272547 : Blo 271824 272547 := bstep (se 1 (by rfl) ⟨204410, by rfl⟩ : syracuseStep 272547 = 408821) B408821
theorem B272563 : Blo 271824 272563 := bstep (se 1 (by rfl) ⟨204422, by rfl⟩ : syracuseStep 272563 = 408845) B408845
theorem B272579 : Blo 271824 272579 := bstep (se 1 (by rfl) ⟨204434, by rfl⟩ : syracuseStep 272579 = 408869) B408869
theorem B272595 : Blo 271824 272595 := bstep (se 1 (by rfl) ⟨204446, by rfl⟩ : syracuseStep 272595 = 408893) B408893
theorem B272611 : Blo 271824 272611 := bstep (se 1 (by rfl) ⟨204458, by rfl⟩ : syracuseStep 272611 = 408917) B408917
theorem B272627 : Blo 271824 272627 := bstep (se 1 (by rfl) ⟨204470, by rfl⟩ : syracuseStep 272627 = 408941) B408941
theorem B272643 : Blo 271824 272643 := bstep (se 1 (by rfl) ⟨204482, by rfl⟩ : syracuseStep 272643 = 408965) B408965
theorem B272659 : Blo 271824 272659 := bstep (se 1 (by rfl) ⟨204494, by rfl⟩ : syracuseStep 272659 = 408989) B408989
theorem B272675 : Blo 271824 272675 := bstep (se 1 (by rfl) ⟨204506, by rfl⟩ : syracuseStep 272675 = 409013) B409013
theorem B272691 : Blo 271824 272691 := bstep (se 1 (by rfl) ⟨204518, by rfl⟩ : syracuseStep 272691 = 409037) B409037
theorem B272707 : Blo 271824 272707 := bstep (se 1 (by rfl) ⟨204530, by rfl⟩ : syracuseStep 272707 = 409061) B409061
theorem B1747277 : Blo 271824 1747277 := bstep (se 3 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 1747277 = 655229) B655229
theorem B272723 : Blo 271824 272723 := bstep (se 1 (by rfl) ⟨204542, by rfl⟩ : syracuseStep 272723 = 409085) B409085
theorem B371027 : Blo 271824 371027 := bstep (se 1 (by rfl) ⟨278270, by rfl⟩ : syracuseStep 371027 = 556541) B556541
theorem B272739 : Blo 271824 272739 := bstep (se 1 (by rfl) ⟨204554, by rfl⟩ : syracuseStep 272739 = 409109) B409109
theorem B272755 : Blo 271824 272755 := bstep (se 1 (by rfl) ⟨204566, by rfl⟩ : syracuseStep 272755 = 409133) B409133
theorem B272771 : Blo 271824 272771 := bstep (se 1 (by rfl) ⟨204578, by rfl⟩ : syracuseStep 272771 = 409157) B409157
theorem B272787 : Blo 271824 272787 := bstep (se 1 (by rfl) ⟨204590, by rfl⟩ : syracuseStep 272787 = 409181) B409181
theorem B272803 : Blo 271824 272803 := bstep (se 1 (by rfl) ⟨204602, by rfl⟩ : syracuseStep 272803 = 409205) B409205
theorem B272819 : Blo 271824 272819 := bstep (se 1 (by rfl) ⟨204614, by rfl⟩ : syracuseStep 272819 = 409229) B409229
theorem B272835 : Blo 271824 272835 := bstep (se 1 (by rfl) ⟨204626, by rfl⟩ : syracuseStep 272835 = 409253) B409253
theorem B928205 : Blo 271824 928205 := bstep (se 3 (by rfl) ⟨174038, by rfl⟩ : syracuseStep 928205 = 348077) B348077
theorem B272851 : Blo 271824 272851 := bstep (se 1 (by rfl) ⟨204638, by rfl⟩ : syracuseStep 272851 = 409277) B409277
theorem B272867 : Blo 271824 272867 := bstep (se 1 (by rfl) ⟨204650, by rfl⟩ : syracuseStep 272867 = 409301) B409301
theorem B272883 : Blo 271824 272883 := bstep (se 1 (by rfl) ⟨204662, by rfl⟩ : syracuseStep 272883 = 409325) B409325
theorem B272899 : Blo 271824 272899 := bstep (se 1 (by rfl) ⟨204674, by rfl⟩ : syracuseStep 272899 = 409349) B409349
theorem B928259 : Blo 271824 928259 := bstep (se 1 (by rfl) ⟨696194, by rfl⟩ : syracuseStep 928259 = 1392389) B1392389
theorem B272915 : Blo 271824 272915 := bstep (se 1 (by rfl) ⟨204686, by rfl⟩ : syracuseStep 272915 = 409373) B409373
theorem B272931 : Blo 271824 272931 := bstep (se 1 (by rfl) ⟨204698, by rfl⟩ : syracuseStep 272931 = 409397) B409397
theorem B1387043 : Blo 271824 1387043 := bstep (se 1 (by rfl) ⟨1040282, by rfl⟩ : syracuseStep 1387043 = 2080565) B2080565
theorem B272947 : Blo 271824 272947 := bstep (se 1 (by rfl) ⟨204710, by rfl⟩ : syracuseStep 272947 = 409421) B409421
theorem B272963 : Blo 271824 272963 := bstep (se 1 (by rfl) ⟨204722, by rfl⟩ : syracuseStep 272963 = 409445) B409445
theorem B272979 : Blo 271824 272979 := bstep (se 1 (by rfl) ⟨204734, by rfl⟩ : syracuseStep 272979 = 409469) B409469
theorem B1550947 : Blo 271824 1550947 := bstep (se 1 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 1550947 = 2326421) B2326421
theorem B272995 : Blo 271824 272995 := bstep (se 1 (by rfl) ⟨204746, by rfl⟩ : syracuseStep 272995 = 409493) B409493
theorem B3943025 : Blo 271824 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B273011 : Blo 271824 273011 := bstep (se 1 (by rfl) ⟨204758, by rfl⟩ : syracuseStep 273011 = 409517) B409517
theorem B273027 : Blo 271824 273027 := bstep (se 1 (by rfl) ⟨204770, by rfl⟩ : syracuseStep 273027 = 409541) B409541
theorem B273043 : Blo 271824 273043 := bstep (se 1 (by rfl) ⟨204782, by rfl⟩ : syracuseStep 273043 = 409565) B409565
theorem B273059 : Blo 271824 273059 := bstep (se 1 (by rfl) ⟨204794, by rfl⟩ : syracuseStep 273059 = 409589) B409589
theorem B273075 : Blo 271824 273075 := bstep (se 1 (by rfl) ⟨204806, by rfl⟩ : syracuseStep 273075 = 409613) B409613
theorem B273091 : Blo 271824 273091 := bstep (se 1 (by rfl) ⟨204818, by rfl⟩ : syracuseStep 273091 = 409637) B409637
theorem B273107 : Blo 271824 273107 := bstep (se 1 (by rfl) ⟨204830, by rfl⟩ : syracuseStep 273107 = 409661) B409661
theorem B273123 : Blo 271824 273123 := bstep (se 1 (by rfl) ⟨204842, by rfl⟩ : syracuseStep 273123 = 409685) B409685
theorem B273139 : Blo 271824 273139 := bstep (se 1 (by rfl) ⟨204854, by rfl⟩ : syracuseStep 273139 = 409709) B409709
theorem B305923 : Blo 271824 305923 := bstep (se 1 (by rfl) ⟨229442, by rfl⟩ : syracuseStep 305923 = 458885) B458885
theorem B273155 : Blo 271824 273155 := bstep (se 1 (by rfl) ⟨204866, by rfl⟩ : syracuseStep 273155 = 409733) B409733
theorem B633617 : Blo 271824 633617 := bstep (se 2 (by rfl) ⟨237606, by rfl⟩ : syracuseStep 633617 = 475213) B475213
theorem B928529 : Blo 271824 928529 := bstep (se 2 (by rfl) ⟨348198, by rfl⟩ : syracuseStep 928529 = 696397) B696397
theorem B273171 : Blo 271824 273171 := bstep (se 1 (by rfl) ⟨204878, by rfl⟩ : syracuseStep 273171 = 409757) B409757
theorem B273187 : Blo 271824 273187 := bstep (se 1 (by rfl) ⟨204890, by rfl⟩ : syracuseStep 273187 = 409781) B409781
theorem B273203 : Blo 271824 273203 := bstep (se 1 (by rfl) ⟨204902, by rfl⟩ : syracuseStep 273203 = 409805) B409805
theorem B273219 : Blo 271824 273219 := bstep (se 1 (by rfl) ⟨204914, by rfl⟩ : syracuseStep 273219 = 409829) B409829
theorem B273235 : Blo 271824 273235 := bstep (se 1 (by rfl) ⟨204926, by rfl⟩ : syracuseStep 273235 = 409853) B409853
theorem B437089 : Blo 271824 437089 := bstep (se 2 (by rfl) ⟨163908, by rfl⟩ : syracuseStep 437089 = 327817) B327817
theorem B273251 : Blo 271824 273251 := bstep (se 1 (by rfl) ⟨204938, by rfl⟩ : syracuseStep 273251 = 409877) B409877
theorem B273267 : Blo 271824 273267 := bstep (se 1 (by rfl) ⟨204950, by rfl⟩ : syracuseStep 273267 = 409901) B409901
theorem B273283 : Blo 271824 273283 := bstep (se 1 (by rfl) ⟨204962, by rfl⟩ : syracuseStep 273283 = 409925) B409925
theorem B306067 : Blo 271824 306067 := bstep (se 1 (by rfl) ⟨229550, by rfl⟩ : syracuseStep 306067 = 459101) B459101
theorem B273299 : Blo 271824 273299 := bstep (se 1 (by rfl) ⟨204974, by rfl⟩ : syracuseStep 273299 = 409949) B409949
theorem B273315 : Blo 271824 273315 := bstep (se 1 (by rfl) ⟨204986, by rfl⟩ : syracuseStep 273315 = 409973) B409973
theorem B699313 : Blo 271824 699313 := bstep (se 2 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 699313 = 524485) B524485
theorem B273331 : Blo 271824 273331 := bstep (se 1 (by rfl) ⟨204998, by rfl⟩ : syracuseStep 273331 = 409997) B409997
theorem B273347 : Blo 271824 273347 := bstep (se 1 (by rfl) ⟨205010, by rfl⟩ : syracuseStep 273347 = 410021) B410021
theorem B273363 : Blo 271824 273363 := bstep (se 1 (by rfl) ⟨205022, by rfl⟩ : syracuseStep 273363 = 410045) B410045
theorem B273379 : Blo 271824 273379 := bstep (se 1 (by rfl) ⟨205034, by rfl⟩ : syracuseStep 273379 = 410069) B410069
theorem B273395 : Blo 271824 273395 := bstep (se 1 (by rfl) ⟨205046, by rfl⟩ : syracuseStep 273395 = 410093) B410093
theorem B273411 : Blo 271824 273411 := bstep (se 1 (by rfl) ⟨205058, by rfl⟩ : syracuseStep 273411 = 410117) B410117
theorem B273427 : Blo 271824 273427 := bstep (se 1 (by rfl) ⟨205070, by rfl⟩ : syracuseStep 273427 = 410141) B410141
theorem B306211 : Blo 271824 306211 := bstep (se 1 (by rfl) ⟨229658, by rfl⟩ : syracuseStep 306211 = 459317) B459317
theorem B273443 : Blo 271824 273443 := bstep (se 1 (by rfl) ⟨205082, by rfl⟩ : syracuseStep 273443 = 410165) B410165
theorem B273459 : Blo 271824 273459 := bstep (se 1 (by rfl) ⟨205094, by rfl⟩ : syracuseStep 273459 = 410189) B410189
theorem B273475 : Blo 271824 273475 := bstep (se 1 (by rfl) ⟨205106, by rfl⟩ : syracuseStep 273475 = 410213) B410213
theorem B535619 : Blo 271824 535619 := bstep (se 1 (by rfl) ⟨401714, by rfl⟩ : syracuseStep 535619 = 803429) B803429
theorem B273491 : Blo 271824 273491 := bstep (se 1 (by rfl) ⟨205118, by rfl⟩ : syracuseStep 273491 = 410237) B410237
theorem B273507 : Blo 271824 273507 := bstep (se 1 (by rfl) ⟨205130, by rfl⟩ : syracuseStep 273507 = 410261) B410261
theorem B1551473 : Blo 271824 1551473 := bstep (se 2 (by rfl) ⟨581802, by rfl⟩ : syracuseStep 1551473 = 1163605) B1163605
theorem B273523 : Blo 271824 273523 := bstep (se 1 (by rfl) ⟨205142, by rfl⟩ : syracuseStep 273523 = 410285) B410285
theorem B273539 : Blo 271824 273539 := bstep (se 1 (by rfl) ⟨205154, by rfl⟩ : syracuseStep 273539 = 410309) B410309
theorem B273555 : Blo 271824 273555 := bstep (se 1 (by rfl) ⟨205166, by rfl⟩ : syracuseStep 273555 = 410333) B410333
theorem B273571 : Blo 271824 273571 := bstep (se 1 (by rfl) ⟨205178, by rfl⟩ : syracuseStep 273571 = 410357) B410357
theorem B306355 : Blo 271824 306355 := bstep (se 1 (by rfl) ⟨229766, by rfl⟩ : syracuseStep 306355 = 459533) B459533
theorem B273587 : Blo 271824 273587 := bstep (se 1 (by rfl) ⟨205190, by rfl⟩ : syracuseStep 273587 = 410381) B410381
theorem B273603 : Blo 271824 273603 := bstep (se 1 (by rfl) ⟨205202, by rfl⟩ : syracuseStep 273603 = 410405) B410405
theorem B2829509 : Blo 271824 2829509 := bstep (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) B530533
theorem B273619 : Blo 271824 273619 := bstep (se 1 (by rfl) ⟨205214, by rfl⟩ : syracuseStep 273619 = 410429) B410429
theorem B273635 : Blo 271824 273635 := bstep (se 1 (by rfl) ⟨205226, by rfl⟩ : syracuseStep 273635 = 410453) B410453
theorem B273651 : Blo 271824 273651 := bstep (se 1 (by rfl) ⟨205238, by rfl⟩ : syracuseStep 273651 = 410477) B410477
theorem B273667 : Blo 271824 273667 := bstep (se 1 (by rfl) ⟨205250, by rfl⟩ : syracuseStep 273667 = 410501) B410501
theorem B3124493 : Blo 271824 3124493 := bstep (se 3 (by rfl) ⟨585842, by rfl⟩ : syracuseStep 3124493 = 1171685) B1171685
theorem B273683 : Blo 271824 273683 := bstep (se 1 (by rfl) ⟨205262, by rfl⟩ : syracuseStep 273683 = 410525) B410525
theorem B273699 : Blo 271824 273699 := bstep (se 1 (by rfl) ⟨205274, by rfl⟩ : syracuseStep 273699 = 410549) B410549
theorem B929069 : Blo 271824 929069 := bstep (se 3 (by rfl) ⟨174200, by rfl⟩ : syracuseStep 929069 = 348401) B348401
theorem B273715 : Blo 271824 273715 := bstep (se 1 (by rfl) ⟨205286, by rfl⟩ : syracuseStep 273715 = 410573) B410573
theorem B306499 : Blo 271824 306499 := bstep (se 1 (by rfl) ⟨229874, by rfl⟩ : syracuseStep 306499 = 459749) B459749
theorem B273731 : Blo 271824 273731 := bstep (se 1 (by rfl) ⟨205298, by rfl⟩ : syracuseStep 273731 = 410597) B410597
theorem B1387853 : Blo 271824 1387853 := bstep (se 3 (by rfl) ⟨260222, by rfl⟩ : syracuseStep 1387853 = 520445) B520445
theorem B273747 : Blo 271824 273747 := bstep (se 1 (by rfl) ⟨205310, by rfl⟩ : syracuseStep 273747 = 410621) B410621
theorem B273763 : Blo 271824 273763 := bstep (se 1 (by rfl) ⟨205322, by rfl⟩ : syracuseStep 273763 = 410645) B410645
theorem B929123 : Blo 271824 929123 := bstep (se 1 (by rfl) ⟨696842, by rfl⟩ : syracuseStep 929123 = 1393685) B1393685
theorem B273779 : Blo 271824 273779 := bstep (se 1 (by rfl) ⟨205334, by rfl⟩ : syracuseStep 273779 = 410669) B410669
theorem B273795 : Blo 271824 273795 := bstep (se 1 (by rfl) ⟨205346, by rfl⟩ : syracuseStep 273795 = 410693) B410693
theorem B273811 : Blo 271824 273811 := bstep (se 1 (by rfl) ⟨205358, by rfl⟩ : syracuseStep 273811 = 410717) B410717
theorem B273827 : Blo 271824 273827 := bstep (se 1 (by rfl) ⟨205370, by rfl⟩ : syracuseStep 273827 = 410741) B410741
theorem B273843 : Blo 271824 273843 := bstep (se 1 (by rfl) ⟨205382, by rfl⟩ : syracuseStep 273843 = 410765) B410765
theorem B273859 : Blo 271824 273859 := bstep (se 1 (by rfl) ⟨205394, by rfl⟩ : syracuseStep 273859 = 410789) B410789
theorem B306643 : Blo 271824 306643 := bstep (se 1 (by rfl) ⟨229982, by rfl⟩ : syracuseStep 306643 = 459965) B459965
theorem B273875 : Blo 271824 273875 := bstep (se 1 (by rfl) ⟨205406, by rfl⟩ : syracuseStep 273875 = 410813) B410813
theorem B273891 : Blo 271824 273891 := bstep (se 1 (by rfl) ⟨205418, by rfl⟩ : syracuseStep 273891 = 410837) B410837
theorem B273907 : Blo 271824 273907 := bstep (se 1 (by rfl) ⟨205430, by rfl⟩ : syracuseStep 273907 = 410861) B410861
theorem B273923 : Blo 271824 273923 := bstep (se 1 (by rfl) ⟨205442, by rfl⟩ : syracuseStep 273923 = 410885) B410885
theorem B2665997 : Blo 271824 2665997 := bstep (se 3 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 2665997 = 999749) B999749
theorem B273939 : Blo 271824 273939 := bstep (se 1 (by rfl) ⟨205454, by rfl⟩ : syracuseStep 273939 = 410909) B410909
theorem B273955 : Blo 271824 273955 := bstep (se 1 (by rfl) ⟨205466, by rfl⟩ : syracuseStep 273955 = 410933) B410933
theorem B273971 : Blo 271824 273971 := bstep (se 1 (by rfl) ⟨205478, by rfl⟩ : syracuseStep 273971 = 410957) B410957
theorem B273987 : Blo 271824 273987 := bstep (se 1 (by rfl) ⟨205490, by rfl⟩ : syracuseStep 273987 = 410981) B410981
theorem B274003 : Blo 271824 274003 := bstep (se 1 (by rfl) ⟨205502, by rfl⟩ : syracuseStep 274003 = 411005) B411005
theorem B306787 : Blo 271824 306787 := bstep (se 1 (by rfl) ⟨230090, by rfl⟩ : syracuseStep 306787 = 460181) B460181
theorem B274019 : Blo 271824 274019 := bstep (se 1 (by rfl) ⟨205514, by rfl⟩ : syracuseStep 274019 = 411029) B411029
theorem B929393 : Blo 271824 929393 := bstep (se 2 (by rfl) ⟨348522, by rfl⟩ : syracuseStep 929393 = 697045) B697045
theorem B274035 : Blo 271824 274035 := bstep (se 1 (by rfl) ⟨205526, by rfl⟩ : syracuseStep 274035 = 411053) B411053
theorem B274051 : Blo 271824 274051 := bstep (se 1 (by rfl) ⟨205538, by rfl⟩ : syracuseStep 274051 = 411077) B411077
theorem B3321485 : Blo 271824 3321485 := bstep (se 3 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 3321485 = 1245557) B1245557
theorem B274067 : Blo 271824 274067 := bstep (se 1 (by rfl) ⟨205550, by rfl⟩ : syracuseStep 274067 = 411101) B411101
theorem B274083 : Blo 271824 274083 := bstep (se 1 (by rfl) ⟨205562, by rfl⟩ : syracuseStep 274083 = 411125) B411125
theorem B274099 : Blo 271824 274099 := bstep (se 1 (by rfl) ⟨205574, by rfl⟩ : syracuseStep 274099 = 411149) B411149
theorem B274115 : Blo 271824 274115 := bstep (se 1 (by rfl) ⟨205586, by rfl⟩ : syracuseStep 274115 = 411173) B411173
theorem B274131 : Blo 271824 274131 := bstep (se 1 (by rfl) ⟨205598, by rfl⟩ : syracuseStep 274131 = 411197) B411197
theorem B274147 : Blo 271824 274147 := bstep (se 1 (by rfl) ⟨205610, by rfl⟩ : syracuseStep 274147 = 411221) B411221
theorem B306931 : Blo 271824 306931 := bstep (se 1 (by rfl) ⟨230198, by rfl⟩ : syracuseStep 306931 = 460397) B460397
theorem B274163 : Blo 271824 274163 := bstep (se 1 (by rfl) ⟨205622, by rfl⟩ : syracuseStep 274163 = 411245) B411245
theorem B274179 : Blo 271824 274179 := bstep (se 1 (by rfl) ⟨205634, by rfl⟩ : syracuseStep 274179 = 411269) B411269
theorem B274195 : Blo 271824 274195 := bstep (se 1 (by rfl) ⟨205646, by rfl⟩ : syracuseStep 274195 = 411293) B411293
theorem B274211 : Blo 271824 274211 := bstep (se 1 (by rfl) ⟨205658, by rfl⟩ : syracuseStep 274211 = 411317) B411317
theorem B1322801 : Blo 271824 1322801 := bstep (se 2 (by rfl) ⟨496050, by rfl⟩ : syracuseStep 1322801 = 992101) B992101
theorem B274227 : Blo 271824 274227 := bstep (se 1 (by rfl) ⟨205670, by rfl⟩ : syracuseStep 274227 = 411341) B411341
theorem B274243 : Blo 271824 274243 := bstep (se 1 (by rfl) ⟨205682, by rfl⟩ : syracuseStep 274243 = 411365) B411365
theorem B274259 : Blo 271824 274259 := bstep (se 1 (by rfl) ⟨205694, by rfl⟩ : syracuseStep 274259 = 411389) B411389
theorem B274275 : Blo 271824 274275 := bstep (se 1 (by rfl) ⟨205706, by rfl⟩ : syracuseStep 274275 = 411413) B411413
theorem B274291 : Blo 271824 274291 := bstep (se 1 (by rfl) ⟨205718, by rfl⟩ : syracuseStep 274291 = 411437) B411437
theorem B307075 : Blo 271824 307075 := bstep (se 1 (by rfl) ⟨230306, by rfl⟩ : syracuseStep 307075 = 460613) B460613
theorem B274307 : Blo 271824 274307 := bstep (se 1 (by rfl) ⟨205730, by rfl⟩ : syracuseStep 274307 = 411461) B411461
theorem B274323 : Blo 271824 274323 := bstep (se 1 (by rfl) ⟨205742, by rfl⟩ : syracuseStep 274323 = 411485) B411485
theorem B274339 : Blo 271824 274339 := bstep (se 1 (by rfl) ⟨205754, by rfl⟩ : syracuseStep 274339 = 411509) B411509
theorem B274355 : Blo 271824 274355 := bstep (se 1 (by rfl) ⟨205766, by rfl⟩ : syracuseStep 274355 = 411533) B411533
theorem B274371 : Blo 271824 274371 := bstep (se 1 (by rfl) ⟨205778, by rfl⟩ : syracuseStep 274371 = 411557) B411557
theorem B274387 : Blo 271824 274387 := bstep (se 1 (by rfl) ⟨205790, by rfl⟩ : syracuseStep 274387 = 411581) B411581
theorem B274403 : Blo 271824 274403 := bstep (se 1 (by rfl) ⟨205802, by rfl⟩ : syracuseStep 274403 = 411605) B411605
theorem B274419 : Blo 271824 274419 := bstep (se 1 (by rfl) ⟨205814, by rfl⟩ : syracuseStep 274419 = 411629) B411629
theorem B274435 : Blo 271824 274435 := bstep (se 1 (by rfl) ⟨205826, by rfl⟩ : syracuseStep 274435 = 411653) B411653
theorem B307219 : Blo 271824 307219 := bstep (se 1 (by rfl) ⟨230414, by rfl⟩ : syracuseStep 307219 = 460829) B460829
theorem B274451 : Blo 271824 274451 := bstep (se 1 (by rfl) ⟨205838, by rfl⟩ : syracuseStep 274451 = 411677) B411677
theorem B274467 : Blo 271824 274467 := bstep (se 1 (by rfl) ⟨205850, by rfl⟩ : syracuseStep 274467 = 411701) B411701
theorem B536611 : Blo 271824 536611 := bstep (se 1 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 536611 = 804917) B804917
theorem B274483 : Blo 271824 274483 := bstep (se 1 (by rfl) ⟨205862, by rfl⟩ : syracuseStep 274483 = 411725) B411725
theorem B274499 : Blo 271824 274499 := bstep (se 1 (by rfl) ⟨205874, by rfl⟩ : syracuseStep 274499 = 411749) B411749
theorem B274515 : Blo 271824 274515 := bstep (se 1 (by rfl) ⟨205886, by rfl⟩ : syracuseStep 274515 = 411773) B411773
theorem B274531 : Blo 271824 274531 := bstep (se 1 (by rfl) ⟨205898, by rfl⟩ : syracuseStep 274531 = 411797) B411797
theorem B274547 : Blo 271824 274547 := bstep (se 1 (by rfl) ⟨205910, by rfl⟩ : syracuseStep 274547 = 411821) B411821
theorem B274563 : Blo 271824 274563 := bstep (se 1 (by rfl) ⟨205922, by rfl⟩ : syracuseStep 274563 = 411845) B411845
theorem B929933 : Blo 271824 929933 := bstep (se 3 (by rfl) ⟨174362, by rfl⟩ : syracuseStep 929933 = 348725) B348725
theorem B274579 : Blo 271824 274579 := bstep (se 1 (by rfl) ⟨205934, by rfl⟩ : syracuseStep 274579 = 411869) B411869
theorem B307363 : Blo 271824 307363 := bstep (se 1 (by rfl) ⟨230522, by rfl⟩ : syracuseStep 307363 = 461045) B461045
theorem B274595 : Blo 271824 274595 := bstep (se 1 (by rfl) ⟨205946, by rfl⟩ : syracuseStep 274595 = 411893) B411893
theorem B274611 : Blo 271824 274611 := bstep (se 1 (by rfl) ⟨205958, by rfl⟩ : syracuseStep 274611 = 411917) B411917
theorem B274627 : Blo 271824 274627 := bstep (se 1 (by rfl) ⟨205970, by rfl⟩ : syracuseStep 274627 = 411941) B411941
theorem B929987 : Blo 271824 929987 := bstep (se 1 (by rfl) ⟨697490, by rfl⟩ : syracuseStep 929987 = 1394981) B1394981
theorem B274643 : Blo 271824 274643 := bstep (se 1 (by rfl) ⟨205982, by rfl⟩ : syracuseStep 274643 = 411965) B411965
theorem B274659 : Blo 271824 274659 := bstep (se 1 (by rfl) ⟨205994, by rfl⟩ : syracuseStep 274659 = 411989) B411989
theorem B274675 : Blo 271824 274675 := bstep (se 1 (by rfl) ⟨206006, by rfl⟩ : syracuseStep 274675 = 412013) B412013
theorem B274691 : Blo 271824 274691 := bstep (se 1 (by rfl) ⟨206018, by rfl⟩ : syracuseStep 274691 = 412037) B412037
theorem B2961677 : Blo 271824 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B274707 : Blo 271824 274707 := bstep (se 1 (by rfl) ⟨206030, by rfl⟩ : syracuseStep 274707 = 412061) B412061
theorem B274723 : Blo 271824 274723 := bstep (se 1 (by rfl) ⟨206042, by rfl⟩ : syracuseStep 274723 = 412085) B412085
theorem B307507 : Blo 271824 307507 := bstep (se 1 (by rfl) ⟨230630, by rfl⟩ : syracuseStep 307507 = 461261) B461261
theorem B274739 : Blo 271824 274739 := bstep (se 1 (by rfl) ⟨206054, by rfl⟩ : syracuseStep 274739 = 412109) B412109
theorem B274755 : Blo 271824 274755 := bstep (se 1 (by rfl) ⟨206066, by rfl⟩ : syracuseStep 274755 = 412133) B412133
theorem B274771 : Blo 271824 274771 := bstep (se 1 (by rfl) ⟨206078, by rfl⟩ : syracuseStep 274771 = 412157) B412157
theorem B274787 : Blo 271824 274787 := bstep (se 1 (by rfl) ⟨206090, by rfl⟩ : syracuseStep 274787 = 412181) B412181
theorem B274803 : Blo 271824 274803 := bstep (se 1 (by rfl) ⟨206102, by rfl⟩ : syracuseStep 274803 = 412205) B412205
theorem B274819 : Blo 271824 274819 := bstep (se 1 (by rfl) ⟨206114, by rfl⟩ : syracuseStep 274819 = 412229) B412229
theorem B274835 : Blo 271824 274835 := bstep (se 1 (by rfl) ⟨206126, by rfl⟩ : syracuseStep 274835 = 412253) B412253
theorem B438691 : Blo 271824 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B274851 : Blo 271824 274851 := bstep (se 1 (by rfl) ⟨206138, by rfl⟩ : syracuseStep 274851 = 412277) B412277
theorem B274867 : Blo 271824 274867 := bstep (se 1 (by rfl) ⟨206150, by rfl⟩ : syracuseStep 274867 = 412301) B412301
theorem B307651 : Blo 271824 307651 := bstep (se 1 (by rfl) ⟨230738, by rfl⟩ : syracuseStep 307651 = 461477) B461477
theorem B274883 : Blo 271824 274883 := bstep (se 1 (by rfl) ⟨206162, by rfl⟩ : syracuseStep 274883 = 412325) B412325
theorem B930253 : Blo 271824 930253 := bstep (se 3 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 930253 = 348845) B348845
theorem B930257 : Blo 271824 930257 := bstep (se 2 (by rfl) ⟨348846, by rfl⟩ : syracuseStep 930257 = 697693) B697693
theorem B274899 : Blo 271824 274899 := bstep (se 1 (by rfl) ⟨206174, by rfl⟩ : syracuseStep 274899 = 412349) B412349
theorem B274915 : Blo 271824 274915 := bstep (se 1 (by rfl) ⟨206186, by rfl⟩ : syracuseStep 274915 = 412373) B412373
theorem B274931 : Blo 271824 274931 := bstep (se 1 (by rfl) ⟨206198, by rfl⟩ : syracuseStep 274931 = 412397) B412397
theorem B274947 : Blo 271824 274947 := bstep (se 1 (by rfl) ⟨206210, by rfl⟩ : syracuseStep 274947 = 412421) B412421
theorem B1749509 : Blo 271824 1749509 := bstep (se 4 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 1749509 = 328033) B328033
theorem B274963 : Blo 271824 274963 := bstep (se 1 (by rfl) ⟨206222, by rfl⟩ : syracuseStep 274963 = 412445) B412445
theorem B1552931 : Blo 271824 1552931 := bstep (se 1 (by rfl) ⟨1164698, by rfl⟩ : syracuseStep 1552931 = 2329397) B2329397
theorem B274979 : Blo 271824 274979 := bstep (se 1 (by rfl) ⟨206234, by rfl⟩ : syracuseStep 274979 = 412469) B412469
theorem B274995 : Blo 271824 274995 := bstep (se 1 (by rfl) ⟨206246, by rfl⟩ : syracuseStep 274995 = 412493) B412493
theorem B275011 : Blo 271824 275011 := bstep (se 1 (by rfl) ⟨206258, by rfl⟩ : syracuseStep 275011 = 412517) B412517
theorem B307795 : Blo 271824 307795 := bstep (se 1 (by rfl) ⟨230846, by rfl⟩ : syracuseStep 307795 = 461693) B461693
theorem B275027 : Blo 271824 275027 := bstep (se 1 (by rfl) ⟨206270, by rfl⟩ : syracuseStep 275027 = 412541) B412541
theorem B1585763 : Blo 271824 1585763 := bstep (se 1 (by rfl) ⟨1189322, by rfl⟩ : syracuseStep 1585763 = 2378645) B2378645
theorem B275043 : Blo 271824 275043 := bstep (se 1 (by rfl) ⟨206282, by rfl⟩ : syracuseStep 275043 = 412565) B412565
theorem B275059 : Blo 271824 275059 := bstep (se 1 (by rfl) ⟨206294, by rfl⟩ : syracuseStep 275059 = 412589) B412589
theorem B275075 : Blo 271824 275075 := bstep (se 1 (by rfl) ⟨206306, by rfl⟩ : syracuseStep 275075 = 412613) B412613
theorem B5026445 : Blo 271824 5026445 := bstep (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) B1884917
theorem B832145 : Blo 271824 832145 := bstep (se 2 (by rfl) ⟨312054, by rfl⟩ : syracuseStep 832145 = 624109) B624109
theorem B275091 : Blo 271824 275091 := bstep (se 1 (by rfl) ⟨206318, by rfl⟩ : syracuseStep 275091 = 412637) B412637
theorem B438947 : Blo 271824 438947 := bstep (se 1 (by rfl) ⟨329210, by rfl⟩ : syracuseStep 438947 = 658421) B658421
theorem B275107 : Blo 271824 275107 := bstep (se 1 (by rfl) ⟨206330, by rfl⟩ : syracuseStep 275107 = 412661) B412661
theorem B275123 : Blo 271824 275123 := bstep (se 1 (by rfl) ⟨206342, by rfl⟩ : syracuseStep 275123 = 412685) B412685
theorem B275139 : Blo 271824 275139 := bstep (se 1 (by rfl) ⟨206354, by rfl⟩ : syracuseStep 275139 = 412709) B412709
theorem B275155 : Blo 271824 275155 := bstep (se 1 (by rfl) ⟨206366, by rfl⟩ : syracuseStep 275155 = 412733) B412733
theorem B307939 : Blo 271824 307939 := bstep (se 1 (by rfl) ⟨230954, by rfl⟩ : syracuseStep 307939 = 461909) B461909
theorem B275171 : Blo 271824 275171 := bstep (se 1 (by rfl) ⟨206378, by rfl⟩ : syracuseStep 275171 = 412757) B412757
theorem B275187 : Blo 271824 275187 := bstep (se 1 (by rfl) ⟨206390, by rfl⟩ : syracuseStep 275187 = 412781) B412781
theorem B275203 : Blo 271824 275203 := bstep (se 1 (by rfl) ⟨206402, by rfl⟩ : syracuseStep 275203 = 412805) B412805
theorem B275219 : Blo 271824 275219 := bstep (se 1 (by rfl) ⟨206414, by rfl⟩ : syracuseStep 275219 = 412829) B412829
theorem B275235 : Blo 271824 275235 := bstep (se 1 (by rfl) ⟨206426, by rfl⟩ : syracuseStep 275235 = 412853) B412853
theorem B275251 : Blo 271824 275251 := bstep (se 1 (by rfl) ⟨206438, by rfl⟩ : syracuseStep 275251 = 412877) B412877
theorem B275267 : Blo 271824 275267 := bstep (se 1 (by rfl) ⟨206450, by rfl⟩ : syracuseStep 275267 = 412901) B412901
theorem B668497 : Blo 271824 668497 := bstep (se 2 (by rfl) ⟨250686, by rfl⟩ : syracuseStep 668497 = 501373) B501373
theorem B275283 : Blo 271824 275283 := bstep (se 1 (by rfl) ⟨206462, by rfl⟩ : syracuseStep 275283 = 412925) B412925
theorem B439139 : Blo 271824 439139 := bstep (se 1 (by rfl) ⟨329354, by rfl⟩ : syracuseStep 439139 = 658709) B658709
theorem B275299 : Blo 271824 275299 := bstep (se 1 (by rfl) ⟨206474, by rfl⟩ : syracuseStep 275299 = 412949) B412949
theorem B2569073 : Blo 271824 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B308083 : Blo 271824 308083 := bstep (se 1 (by rfl) ⟨231062, by rfl⟩ : syracuseStep 308083 = 462125) B462125
theorem B275315 : Blo 271824 275315 := bstep (se 1 (by rfl) ⟨206486, by rfl⟩ : syracuseStep 275315 = 412973) B412973
theorem B275331 : Blo 271824 275331 := bstep (se 1 (by rfl) ⟨206498, by rfl⟩ : syracuseStep 275331 = 412997) B412997
theorem B275347 : Blo 271824 275347 := bstep (se 1 (by rfl) ⟨206510, by rfl⟩ : syracuseStep 275347 = 413021) B413021
theorem B275363 : Blo 271824 275363 := bstep (se 1 (by rfl) ⟨206522, by rfl⟩ : syracuseStep 275363 = 413045) B413045
theorem B275379 : Blo 271824 275379 := bstep (se 1 (by rfl) ⟨206534, by rfl⟩ : syracuseStep 275379 = 413069) B413069
theorem B275395 : Blo 271824 275395 := bstep (se 1 (by rfl) ⟨206546, by rfl⟩ : syracuseStep 275395 = 413093) B413093
theorem B275411 : Blo 271824 275411 := bstep (se 1 (by rfl) ⟨206558, by rfl⟩ : syracuseStep 275411 = 413117) B413117
theorem B275427 : Blo 271824 275427 := bstep (se 1 (by rfl) ⟨206570, by rfl⟩ : syracuseStep 275427 = 413141) B413141
theorem B930797 : Blo 271824 930797 := bstep (se 3 (by rfl) ⟨174524, by rfl⟩ : syracuseStep 930797 = 349049) B349049
theorem B275443 : Blo 271824 275443 := bstep (se 1 (by rfl) ⟨206582, by rfl⟩ : syracuseStep 275443 = 413165) B413165
theorem B308227 : Blo 271824 308227 := bstep (se 1 (by rfl) ⟨231170, by rfl⟩ : syracuseStep 308227 = 462341) B462341
theorem B275459 : Blo 271824 275459 := bstep (se 1 (by rfl) ⟨206594, by rfl⟩ : syracuseStep 275459 = 413189) B413189
theorem B275475 : Blo 271824 275475 := bstep (se 1 (by rfl) ⟨206606, by rfl⟩ : syracuseStep 275475 = 413213) B413213
theorem B275491 : Blo 271824 275491 := bstep (se 1 (by rfl) ⟨206618, by rfl⟩ : syracuseStep 275491 = 413237) B413237
theorem B930851 : Blo 271824 930851 := bstep (se 1 (by rfl) ⟨698138, by rfl⟩ : syracuseStep 930851 = 1396277) B1396277
theorem B275507 : Blo 271824 275507 := bstep (se 1 (by rfl) ⟨206630, by rfl⟩ : syracuseStep 275507 = 413261) B413261
theorem B701507 : Blo 271824 701507 := bstep (se 1 (by rfl) ⟨526130, by rfl⟩ : syracuseStep 701507 = 1052261) B1052261
theorem B275523 : Blo 271824 275523 := bstep (se 1 (by rfl) ⟨206642, by rfl⟩ : syracuseStep 275523 = 413285) B413285
theorem B275539 : Blo 271824 275539 := bstep (se 1 (by rfl) ⟨206654, by rfl⟩ : syracuseStep 275539 = 413309) B413309
theorem B275555 : Blo 271824 275555 := bstep (se 1 (by rfl) ⟨206666, by rfl⟩ : syracuseStep 275555 = 413333) B413333
theorem B275571 : Blo 271824 275571 := bstep (se 1 (by rfl) ⟨206678, by rfl⟩ : syracuseStep 275571 = 413357) B413357
theorem B275587 : Blo 271824 275587 := bstep (se 1 (by rfl) ⟨206690, by rfl⟩ : syracuseStep 275587 = 413381) B413381
theorem B308371 : Blo 271824 308371 := bstep (se 1 (by rfl) ⟨231278, by rfl⟩ : syracuseStep 308371 = 462557) B462557
theorem B275603 : Blo 271824 275603 := bstep (se 1 (by rfl) ⟨206702, by rfl⟩ : syracuseStep 275603 = 413405) B413405
theorem B275619 : Blo 271824 275619 := bstep (se 1 (by rfl) ⟨206714, by rfl⟩ : syracuseStep 275619 = 413429) B413429
theorem B275635 : Blo 271824 275635 := bstep (se 1 (by rfl) ⟨206726, by rfl⟩ : syracuseStep 275635 = 413453) B413453
theorem B275651 : Blo 271824 275651 := bstep (se 1 (by rfl) ⟨206738, by rfl⟩ : syracuseStep 275651 = 413477) B413477
theorem B275667 : Blo 271824 275667 := bstep (se 1 (by rfl) ⟨206750, by rfl⟩ : syracuseStep 275667 = 413501) B413501
theorem B373987 : Blo 271824 373987 := bstep (se 1 (by rfl) ⟨280490, by rfl⟩ : syracuseStep 373987 = 560981) B560981
theorem B275683 : Blo 271824 275683 := bstep (se 1 (by rfl) ⟨206762, by rfl⟩ : syracuseStep 275683 = 413525) B413525
theorem B275699 : Blo 271824 275699 := bstep (se 1 (by rfl) ⟨206774, by rfl⟩ : syracuseStep 275699 = 413549) B413549
theorem B275715 : Blo 271824 275715 := bstep (se 1 (by rfl) ⟨206786, by rfl⟩ : syracuseStep 275715 = 413573) B413573
theorem B275731 : Blo 271824 275731 := bstep (se 1 (by rfl) ⟨206798, by rfl⟩ : syracuseStep 275731 = 413597) B413597
theorem B308515 : Blo 271824 308515 := bstep (se 1 (by rfl) ⟨231386, by rfl⟩ : syracuseStep 308515 = 462773) B462773
theorem B275747 : Blo 271824 275747 := bstep (se 1 (by rfl) ⟨206810, by rfl⟩ : syracuseStep 275747 = 413621) B413621
theorem B275763 : Blo 271824 275763 := bstep (se 1 (by rfl) ⟨206822, by rfl⟩ : syracuseStep 275763 = 413645) B413645
theorem B275779 : Blo 271824 275779 := bstep (se 1 (by rfl) ⟨206834, by rfl⟩ : syracuseStep 275779 = 413669) B413669
theorem B275795 : Blo 271824 275795 := bstep (se 1 (by rfl) ⟨206846, by rfl⟩ : syracuseStep 275795 = 413693) B413693
theorem B275811 : Blo 271824 275811 := bstep (se 1 (by rfl) ⟨206858, by rfl⟩ : syracuseStep 275811 = 413717) B413717
theorem B4502897 : Blo 271824 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B1324451 : Blo 271824 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B308659 : Blo 271824 308659 := bstep (se 1 (by rfl) ⟨231494, by rfl⟩ : syracuseStep 308659 = 462989) B462989
theorem B275971 : Blo 271824 275971 := bstep (se 1 (by rfl) ⟨206978, by rfl⟩ : syracuseStep 275971 = 413957) B413957
theorem B308803 : Blo 271824 308803 := bstep (se 1 (by rfl) ⟨231602, by rfl⟩ : syracuseStep 308803 = 463205) B463205
theorem B439921 : Blo 271824 439921 := bstep (se 2 (by rfl) ⟨164970, by rfl⟩ : syracuseStep 439921 = 329941) B329941
theorem B308947 : Blo 271824 308947 := bstep (se 1 (by rfl) ⟨231710, by rfl⟩ : syracuseStep 308947 = 463421) B463421
theorem B309091 : Blo 271824 309091 := bstep (se 1 (by rfl) ⟨231818, by rfl⟩ : syracuseStep 309091 = 463637) B463637
theorem B309235 : Blo 271824 309235 := bstep (se 1 (by rfl) ⟨231926, by rfl⟩ : syracuseStep 309235 = 463853) B463853
theorem B1161229 : Blo 271824 1161229 := bstep (se 3 (by rfl) ⟨217730, by rfl⟩ : syracuseStep 1161229 = 435461) B435461
theorem B3127409 : Blo 271824 3127409 := bstep (se 2 (by rfl) ⟨1172778, by rfl⟩ : syracuseStep 3127409 = 2345557) B2345557
theorem B309379 : Blo 271824 309379 := bstep (se 1 (by rfl) ⟨232034, by rfl⟩ : syracuseStep 309379 = 464069) B464069
theorem B1390769 : Blo 271824 1390769 := bstep (se 2 (by rfl) ⟨521538, by rfl⟩ : syracuseStep 1390769 = 1043077) B1043077
theorem B407747 : Blo 271824 407747 := bstep (se 1 (by rfl) ⟨305810, by rfl⟩ : syracuseStep 407747 = 611621) B611621
theorem B1325261 : Blo 271824 1325261 := bstep (se 3 (by rfl) ⟨248486, by rfl⟩ : syracuseStep 1325261 = 496973) B496973
theorem B407777 : Blo 271824 407777 := bstep (se 2 (by rfl) ⟨152916, by rfl⟩ : syracuseStep 407777 = 305833) B305833
theorem B407795 : Blo 271824 407795 := bstep (se 1 (by rfl) ⟨305846, by rfl⟩ : syracuseStep 407795 = 611693) B611693
theorem B407825 : Blo 271824 407825 := bstep (se 2 (by rfl) ⟨152934, by rfl⟩ : syracuseStep 407825 = 305869) B305869
theorem B309523 : Blo 271824 309523 := bstep (se 1 (by rfl) ⟨232142, by rfl⟩ : syracuseStep 309523 = 464285) B464285
theorem B407843 : Blo 271824 407843 := bstep (se 1 (by rfl) ⟨305882, by rfl⟩ : syracuseStep 407843 = 611765) B611765
theorem B407873 : Blo 271824 407873 := bstep (se 2 (by rfl) ⟨152952, by rfl⟩ : syracuseStep 407873 = 305905) B305905
theorem B407891 : Blo 271824 407891 := bstep (se 1 (by rfl) ⟨305918, by rfl⟩ : syracuseStep 407891 = 611837) B611837
theorem B407921 : Blo 271824 407921 := bstep (se 2 (by rfl) ⟨152970, by rfl⟩ : syracuseStep 407921 = 305941) B305941
theorem B407939 : Blo 271824 407939 := bstep (se 1 (by rfl) ⟨305954, by rfl⟩ : syracuseStep 407939 = 611909) B611909
theorem B1554821 : Blo 271824 1554821 := bstep (se 4 (by rfl) ⟨145764, by rfl⟩ : syracuseStep 1554821 = 291529) B291529
theorem B407969 : Blo 271824 407969 := bstep (se 2 (by rfl) ⟨152988, by rfl⟩ : syracuseStep 407969 = 305977) B305977
theorem B309667 : Blo 271824 309667 := bstep (se 1 (by rfl) ⟨232250, by rfl⟩ : syracuseStep 309667 = 464501) B464501
theorem B407987 : Blo 271824 407987 := bstep (se 1 (by rfl) ⟨305990, by rfl⟩ : syracuseStep 407987 = 611981) B611981
theorem B408017 : Blo 271824 408017 := bstep (se 2 (by rfl) ⟨153006, by rfl⟩ : syracuseStep 408017 = 306013) B306013
theorem B408035 : Blo 271824 408035 := bstep (se 1 (by rfl) ⟨306026, by rfl⟩ : syracuseStep 408035 = 612053) B612053
theorem B408065 : Blo 271824 408065 := bstep (se 2 (by rfl) ⟨153024, by rfl⟩ : syracuseStep 408065 = 306049) B306049
theorem B473603 : Blo 271824 473603 := bstep (se 1 (by rfl) ⟨355202, by rfl⟩ : syracuseStep 473603 = 710405) B710405
theorem B408083 : Blo 271824 408083 := bstep (se 1 (by rfl) ⟨306062, by rfl⟩ : syracuseStep 408083 = 612125) B612125
theorem B408113 : Blo 271824 408113 := bstep (se 2 (by rfl) ⟨153042, by rfl⟩ : syracuseStep 408113 = 306085) B306085
theorem B309811 : Blo 271824 309811 := bstep (se 1 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 309811 = 464717) B464717
theorem B408131 : Blo 271824 408131 := bstep (se 1 (by rfl) ⟨306098, by rfl⟩ : syracuseStep 408131 = 612197) B612197
theorem B408161 : Blo 271824 408161 := bstep (se 2 (by rfl) ⟨153060, by rfl⟩ : syracuseStep 408161 = 306121) B306121
theorem B408179 : Blo 271824 408179 := bstep (se 1 (by rfl) ⟨306134, by rfl⟩ : syracuseStep 408179 = 612269) B612269
theorem B408209 : Blo 271824 408209 := bstep (se 2 (by rfl) ⟨153078, by rfl⟩ : syracuseStep 408209 = 306157) B306157
theorem B408227 : Blo 271824 408227 := bstep (se 1 (by rfl) ⟨306170, by rfl⟩ : syracuseStep 408227 = 612341) B612341
theorem B277171 : Blo 271824 277171 := bstep (se 1 (by rfl) ⟨207878, by rfl⟩ : syracuseStep 277171 = 415757) B415757
theorem B408257 : Blo 271824 408257 := bstep (se 2 (by rfl) ⟨153096, by rfl⟩ : syracuseStep 408257 = 306193) B306193
theorem B309955 : Blo 271824 309955 := bstep (se 1 (by rfl) ⟨232466, by rfl⟩ : syracuseStep 309955 = 464933) B464933
theorem B408275 : Blo 271824 408275 := bstep (se 1 (by rfl) ⟨306206, by rfl⟩ : syracuseStep 408275 = 612413) B612413
theorem B408305 : Blo 271824 408305 := bstep (se 2 (by rfl) ⟨153114, by rfl⟩ : syracuseStep 408305 = 306229) B306229
theorem B408323 : Blo 271824 408323 := bstep (se 1 (by rfl) ⟨306242, by rfl⟩ : syracuseStep 408323 = 612485) B612485
theorem B408353 : Blo 271824 408353 := bstep (se 2 (by rfl) ⟨153132, by rfl⟩ : syracuseStep 408353 = 306265) B306265
theorem B408371 : Blo 271824 408371 := bstep (se 1 (by rfl) ⟨306278, by rfl⟩ : syracuseStep 408371 = 612557) B612557
theorem B408401 : Blo 271824 408401 := bstep (se 2 (by rfl) ⟨153150, by rfl⟩ : syracuseStep 408401 = 306301) B306301
theorem B310099 : Blo 271824 310099 := bstep (se 1 (by rfl) ⟨232574, by rfl⟩ : syracuseStep 310099 = 465149) B465149
theorem B408419 : Blo 271824 408419 := bstep (se 1 (by rfl) ⟨306314, by rfl⟩ : syracuseStep 408419 = 612629) B612629
theorem B408449 : Blo 271824 408449 := bstep (se 2 (by rfl) ⟨153168, by rfl⟩ : syracuseStep 408449 = 306337) B306337
theorem B408467 : Blo 271824 408467 := bstep (se 1 (by rfl) ⟨306350, by rfl⟩ : syracuseStep 408467 = 612701) B612701
theorem B408497 : Blo 271824 408497 := bstep (se 2 (by rfl) ⟨153186, by rfl⟩ : syracuseStep 408497 = 306373) B306373
theorem B408515 : Blo 271824 408515 := bstep (se 1 (by rfl) ⟨306386, by rfl⟩ : syracuseStep 408515 = 612773) B612773
theorem B408545 : Blo 271824 408545 := bstep (se 2 (by rfl) ⟨153204, by rfl⟩ : syracuseStep 408545 = 306409) B306409
theorem B310243 : Blo 271824 310243 := bstep (se 1 (by rfl) ⟨232682, by rfl⟩ : syracuseStep 310243 = 465365) B465365
theorem B408563 : Blo 271824 408563 := bstep (se 1 (by rfl) ⟨306422, by rfl⟩ : syracuseStep 408563 = 612845) B612845
theorem B408593 : Blo 271824 408593 := bstep (se 2 (by rfl) ⟨153222, by rfl⟩ : syracuseStep 408593 = 306445) B306445
theorem B441379 : Blo 271824 441379 := bstep (se 1 (by rfl) ⟨331034, by rfl⟩ : syracuseStep 441379 = 662069) B662069
theorem B408611 : Blo 271824 408611 := bstep (se 1 (by rfl) ⟨306458, by rfl⟩ : syracuseStep 408611 = 612917) B612917
theorem B1162289 : Blo 271824 1162289 := bstep (se 2 (by rfl) ⟨435858, by rfl⟩ : syracuseStep 1162289 = 871717) B871717
theorem B408641 : Blo 271824 408641 := bstep (se 2 (by rfl) ⟨153240, by rfl⟩ : syracuseStep 408641 = 306481) B306481
theorem B408659 : Blo 271824 408659 := bstep (se 1 (by rfl) ⟨306494, by rfl⟩ : syracuseStep 408659 = 612989) B612989
theorem B408689 : Blo 271824 408689 := bstep (se 2 (by rfl) ⟨153258, by rfl⟩ : syracuseStep 408689 = 306517) B306517
theorem B408707 : Blo 271824 408707 := bstep (se 1 (by rfl) ⟨306530, by rfl⟩ : syracuseStep 408707 = 613061) B613061
theorem B408737 : Blo 271824 408737 := bstep (se 2 (by rfl) ⟨153276, by rfl⟩ : syracuseStep 408737 = 306553) B306553
theorem B408755 : Blo 271824 408755 := bstep (se 1 (by rfl) ⟨306566, by rfl⟩ : syracuseStep 408755 = 613133) B613133
theorem B736465 : Blo 271824 736465 := bstep (se 2 (by rfl) ⟨276174, by rfl⟩ : syracuseStep 736465 = 552349) B552349
theorem B408785 : Blo 271824 408785 := bstep (se 2 (by rfl) ⟨153294, by rfl⟩ : syracuseStep 408785 = 306589) B306589
theorem B408803 : Blo 271824 408803 := bstep (se 1 (by rfl) ⟨306602, by rfl⟩ : syracuseStep 408803 = 613205) B613205
theorem B441587 : Blo 271824 441587 := bstep (se 1 (by rfl) ⟨331190, by rfl⟩ : syracuseStep 441587 = 662381) B662381
theorem B408833 : Blo 271824 408833 := bstep (se 2 (by rfl) ⟨153312, by rfl⟩ : syracuseStep 408833 = 306625) B306625
theorem B408851 : Blo 271824 408851 := bstep (se 1 (by rfl) ⟨306638, by rfl⟩ : syracuseStep 408851 = 613277) B613277
theorem B408881 : Blo 271824 408881 := bstep (se 2 (by rfl) ⟨153330, by rfl⟩ : syracuseStep 408881 = 306661) B306661
theorem B408899 : Blo 271824 408899 := bstep (se 1 (by rfl) ⟨306674, by rfl⟩ : syracuseStep 408899 = 613349) B613349
theorem B408929 : Blo 271824 408929 := bstep (se 2 (by rfl) ⟨153348, by rfl⟩ : syracuseStep 408929 = 306697) B306697
theorem B408947 : Blo 271824 408947 := bstep (se 1 (by rfl) ⟨306710, by rfl⟩ : syracuseStep 408947 = 613421) B613421
theorem B441715 : Blo 271824 441715 := bstep (se 1 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 441715 = 662573) B662573
theorem B408977 : Blo 271824 408977 := bstep (se 2 (by rfl) ⟨153366, by rfl⟩ : syracuseStep 408977 = 306733) B306733
theorem B408995 : Blo 271824 408995 := bstep (se 1 (by rfl) ⟨306746, by rfl⟩ : syracuseStep 408995 = 613493) B613493
theorem B409025 : Blo 271824 409025 := bstep (se 2 (by rfl) ⟨153384, by rfl⟩ : syracuseStep 409025 = 306769) B306769
theorem B2112965 : Blo 271824 2112965 := bstep (se 4 (by rfl) ⟨198090, by rfl⟩ : syracuseStep 2112965 = 396181) B396181
theorem B409043 : Blo 271824 409043 := bstep (se 1 (by rfl) ⟨306782, by rfl⟩ : syracuseStep 409043 = 613565) B613565
theorem B409073 : Blo 271824 409073 := bstep (se 2 (by rfl) ⟨153402, by rfl⟩ : syracuseStep 409073 = 306805) B306805
theorem B409091 : Blo 271824 409091 := bstep (se 1 (by rfl) ⟨306818, by rfl⟩ : syracuseStep 409091 = 613637) B613637
theorem B409121 : Blo 271824 409121 := bstep (se 2 (by rfl) ⟨153420, by rfl⟩ : syracuseStep 409121 = 306841) B306841
theorem B409139 : Blo 271824 409139 := bstep (se 1 (by rfl) ⟨306854, by rfl⟩ : syracuseStep 409139 = 613709) B613709
theorem B409169 : Blo 271824 409169 := bstep (se 2 (by rfl) ⟨153438, by rfl⟩ : syracuseStep 409169 = 306877) B306877
theorem B409187 : Blo 271824 409187 := bstep (se 1 (by rfl) ⟨306890, by rfl⟩ : syracuseStep 409187 = 613781) B613781
theorem B1392227 : Blo 271824 1392227 := bstep (se 1 (by rfl) ⟨1044170, by rfl⟩ : syracuseStep 1392227 = 2088341) B2088341
theorem B409217 : Blo 271824 409217 := bstep (se 2 (by rfl) ⟨153456, by rfl⟩ : syracuseStep 409217 = 306913) B306913
theorem B409235 : Blo 271824 409235 := bstep (se 1 (by rfl) ⟨306926, by rfl⟩ : syracuseStep 409235 = 613853) B613853
theorem B409265 : Blo 271824 409265 := bstep (se 2 (by rfl) ⟨153474, by rfl⟩ : syracuseStep 409265 = 306949) B306949
theorem B409283 : Blo 271824 409283 := bstep (se 1 (by rfl) ⟨306962, by rfl⟩ : syracuseStep 409283 = 613925) B613925
theorem B704209 : Blo 271824 704209 := bstep (se 2 (by rfl) ⟨264078, by rfl⟩ : syracuseStep 704209 = 528157) B528157
theorem B409313 : Blo 271824 409313 := bstep (se 2 (by rfl) ⟨153492, by rfl⟩ : syracuseStep 409313 = 306985) B306985
theorem B409331 : Blo 271824 409331 := bstep (se 1 (by rfl) ⟨306998, by rfl⟩ : syracuseStep 409331 = 613997) B613997
theorem B409361 : Blo 271824 409361 := bstep (se 2 (by rfl) ⟨153510, by rfl⟩ : syracuseStep 409361 = 307021) B307021
theorem B409379 : Blo 271824 409379 := bstep (se 1 (by rfl) ⟨307034, by rfl⟩ : syracuseStep 409379 = 614069) B614069
theorem B409409 : Blo 271824 409409 := bstep (se 2 (by rfl) ⟨153528, by rfl⟩ : syracuseStep 409409 = 307057) B307057
theorem B409427 : Blo 271824 409427 := bstep (se 1 (by rfl) ⟨307070, by rfl⟩ : syracuseStep 409427 = 614141) B614141
theorem B409457 : Blo 271824 409457 := bstep (se 2 (by rfl) ⟨153546, by rfl⟩ : syracuseStep 409457 = 307093) B307093
theorem B409475 : Blo 271824 409475 := bstep (se 1 (by rfl) ⟨307106, by rfl⟩ : syracuseStep 409475 = 614213) B614213
theorem B2211725 : Blo 271824 2211725 := bstep (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) B829397
theorem B409505 : Blo 271824 409505 := bstep (se 2 (by rfl) ⟨153564, by rfl⟩ : syracuseStep 409505 = 307129) B307129
theorem B409523 : Blo 271824 409523 := bstep (se 1 (by rfl) ⟨307142, by rfl⟩ : syracuseStep 409523 = 614285) B614285
theorem B409553 : Blo 271824 409553 := bstep (se 2 (by rfl) ⟨153582, by rfl⟩ : syracuseStep 409553 = 307165) B307165
theorem B409571 : Blo 271824 409571 := bstep (se 1 (by rfl) ⟨307178, by rfl⟩ : syracuseStep 409571 = 614357) B614357
theorem B409601 : Blo 271824 409601 := bstep (se 2 (by rfl) ⟨153600, by rfl⟩ : syracuseStep 409601 = 307201) B307201
theorem B344083 : Blo 271824 344083 := bstep (se 1 (by rfl) ⟨258062, by rfl⟩ : syracuseStep 344083 = 516125) B516125
theorem B409619 : Blo 271824 409619 := bstep (se 1 (by rfl) ⟨307214, by rfl⟩ : syracuseStep 409619 = 614429) B614429
theorem B409649 : Blo 271824 409649 := bstep (se 2 (by rfl) ⟨153618, by rfl⟩ : syracuseStep 409649 = 307237) B307237
theorem B409667 : Blo 271824 409667 := bstep (se 1 (by rfl) ⟨307250, by rfl⟩ : syracuseStep 409667 = 614501) B614501
theorem B409697 : Blo 271824 409697 := bstep (se 2 (by rfl) ⟨153636, by rfl⟩ : syracuseStep 409697 = 307273) B307273
theorem B344179 : Blo 271824 344179 := bstep (se 1 (by rfl) ⟨258134, by rfl⟩ : syracuseStep 344179 = 516269) B516269
theorem B409715 : Blo 271824 409715 := bstep (se 1 (by rfl) ⟨307286, by rfl⟩ : syracuseStep 409715 = 614573) B614573
theorem B409745 : Blo 271824 409745 := bstep (se 2 (by rfl) ⟨153654, by rfl⟩ : syracuseStep 409745 = 307309) B307309
theorem B409763 : Blo 271824 409763 := bstep (se 1 (by rfl) ⟨307322, by rfl⟩ : syracuseStep 409763 = 614645) B614645
theorem B409793 : Blo 271824 409793 := bstep (se 2 (by rfl) ⟨153672, by rfl⟩ : syracuseStep 409793 = 307345) B307345
theorem B409811 : Blo 271824 409811 := bstep (se 1 (by rfl) ⟨307358, by rfl⟩ : syracuseStep 409811 = 614717) B614717
theorem B409841 : Blo 271824 409841 := bstep (se 2 (by rfl) ⟨153690, by rfl⟩ : syracuseStep 409841 = 307381) B307381
theorem B409859 : Blo 271824 409859 := bstep (se 1 (by rfl) ⟨307394, by rfl⟩ : syracuseStep 409859 = 614789) B614789
theorem B409889 : Blo 271824 409889 := bstep (se 2 (by rfl) ⟨153708, by rfl⟩ : syracuseStep 409889 = 307417) B307417
theorem B409907 : Blo 271824 409907 := bstep (se 1 (by rfl) ⟨307430, by rfl⟩ : syracuseStep 409907 = 614861) B614861
theorem B409937 : Blo 271824 409937 := bstep (se 2 (by rfl) ⟨153726, by rfl⟩ : syracuseStep 409937 = 307453) B307453
theorem B311635 : Blo 271824 311635 := bstep (se 1 (by rfl) ⟨233726, by rfl⟩ : syracuseStep 311635 = 467453) B467453
theorem B409955 : Blo 271824 409955 := bstep (se 1 (by rfl) ⟨307466, by rfl⟩ : syracuseStep 409955 = 614933) B614933
theorem B409985 : Blo 271824 409985 := bstep (se 2 (by rfl) ⟨153744, by rfl⟩ : syracuseStep 409985 = 307489) B307489
theorem B1393037 : Blo 271824 1393037 := bstep (se 3 (by rfl) ⟨261194, by rfl⟩ : syracuseStep 1393037 = 522389) B522389
theorem B410003 : Blo 271824 410003 := bstep (se 1 (by rfl) ⟨307502, by rfl⟩ : syracuseStep 410003 = 615005) B615005
theorem B410033 : Blo 271824 410033 := bstep (se 2 (by rfl) ⟨153762, by rfl⟩ : syracuseStep 410033 = 307525) B307525
theorem B410051 : Blo 271824 410051 := bstep (se 1 (by rfl) ⟨307538, by rfl⟩ : syracuseStep 410051 = 615077) B615077
theorem B410081 : Blo 271824 410081 := bstep (se 2 (by rfl) ⟨153780, by rfl⟩ : syracuseStep 410081 = 307561) B307561
theorem B1032689 : Blo 271824 1032689 := bstep (se 2 (by rfl) ⟨387258, by rfl⟩ : syracuseStep 1032689 = 774517) B774517
theorem B410099 : Blo 271824 410099 := bstep (se 1 (by rfl) ⟨307574, by rfl⟩ : syracuseStep 410099 = 615149) B615149
theorem B410129 : Blo 271824 410129 := bstep (se 2 (by rfl) ⟨153798, by rfl⟩ : syracuseStep 410129 = 307597) B307597
theorem B410147 : Blo 271824 410147 := bstep (se 1 (by rfl) ⟨307610, by rfl⟩ : syracuseStep 410147 = 615221) B615221
theorem B410177 : Blo 271824 410177 := bstep (se 2 (by rfl) ⟨153816, by rfl⟩ : syracuseStep 410177 = 307633) B307633
theorem B410195 : Blo 271824 410195 := bstep (se 1 (by rfl) ⟨307646, by rfl⟩ : syracuseStep 410195 = 615293) B615293
theorem B344675 : Blo 271824 344675 := bstep (se 1 (by rfl) ⟨258506, by rfl⟩ : syracuseStep 344675 = 517013) B517013
theorem B410225 : Blo 271824 410225 := bstep (se 2 (by rfl) ⟨153834, by rfl⟩ : syracuseStep 410225 = 307669) B307669
theorem B410243 : Blo 271824 410243 := bstep (se 1 (by rfl) ⟨307682, by rfl⟩ : syracuseStep 410243 = 615365) B615365
theorem B410273 : Blo 271824 410273 := bstep (se 2 (by rfl) ⟨153852, by rfl⟩ : syracuseStep 410273 = 307705) B307705
theorem B410291 : Blo 271824 410291 := bstep (se 1 (by rfl) ⟨307718, by rfl⟩ : syracuseStep 410291 = 615437) B615437
theorem B410321 : Blo 271824 410321 := bstep (se 2 (by rfl) ⟨153870, by rfl⟩ : syracuseStep 410321 = 307741) B307741
theorem B410339 : Blo 271824 410339 := bstep (se 1 (by rfl) ⟨307754, by rfl⟩ : syracuseStep 410339 = 615509) B615509
theorem B1983217 : Blo 271824 1983217 := bstep (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) B1487413
theorem B410369 : Blo 271824 410369 := bstep (se 2 (by rfl) ⟨153888, by rfl⟩ : syracuseStep 410369 = 307777) B307777
theorem B836369 : Blo 271824 836369 := bstep (se 2 (by rfl) ⟨313638, by rfl⟩ : syracuseStep 836369 = 627277) B627277
theorem B410387 : Blo 271824 410387 := bstep (se 1 (by rfl) ⟨307790, by rfl⟩ : syracuseStep 410387 = 615581) B615581
theorem B1295153 : Blo 271824 1295153 := bstep (se 2 (by rfl) ⟨485682, by rfl⟩ : syracuseStep 1295153 = 971365) B971365
theorem B410417 : Blo 271824 410417 := bstep (se 2 (by rfl) ⟨153906, by rfl⟩ : syracuseStep 410417 = 307813) B307813
theorem B410435 : Blo 271824 410435 := bstep (se 1 (by rfl) ⟨307826, by rfl⟩ : syracuseStep 410435 = 615653) B615653
theorem B410465 : Blo 271824 410465 := bstep (se 2 (by rfl) ⟨153924, by rfl⟩ : syracuseStep 410465 = 307849) B307849
theorem B410483 : Blo 271824 410483 := bstep (se 1 (by rfl) ⟨307862, by rfl⟩ : syracuseStep 410483 = 615725) B615725
theorem B410513 : Blo 271824 410513 := bstep (se 2 (by rfl) ⟨153942, by rfl⟩ : syracuseStep 410513 = 307885) B307885
theorem B410531 : Blo 271824 410531 := bstep (se 1 (by rfl) ⟨307898, by rfl⟩ : syracuseStep 410531 = 615797) B615797
theorem B410561 : Blo 271824 410561 := bstep (se 2 (by rfl) ⟨153960, by rfl⟩ : syracuseStep 410561 = 307921) B307921
theorem B12633029 : Blo 271824 12633029 := bstep (se 4 (by rfl) ⟨1184346, by rfl⟩ : syracuseStep 12633029 = 2368693) B2368693
theorem B410579 : Blo 271824 410579 := bstep (se 1 (by rfl) ⟨307934, by rfl⟩ : syracuseStep 410579 = 615869) B615869
theorem B410609 : Blo 271824 410609 := bstep (se 2 (by rfl) ⟨153978, by rfl⟩ : syracuseStep 410609 = 307957) B307957
theorem B410627 : Blo 271824 410627 := bstep (se 1 (by rfl) ⟨307970, by rfl⟩ : syracuseStep 410627 = 615941) B615941
theorem B410657 : Blo 271824 410657 := bstep (se 2 (by rfl) ⟨153996, by rfl⟩ : syracuseStep 410657 = 307993) B307993
theorem B410675 : Blo 271824 410675 := bstep (se 1 (by rfl) ⟨308006, by rfl⟩ : syracuseStep 410675 = 616013) B616013
theorem B410705 : Blo 271824 410705 := bstep (se 2 (by rfl) ⟨154014, by rfl⟩ : syracuseStep 410705 = 308029) B308029
theorem B410723 : Blo 271824 410723 := bstep (se 1 (by rfl) ⟨308042, by rfl⟩ : syracuseStep 410723 = 616085) B616085
theorem B410753 : Blo 271824 410753 := bstep (se 2 (by rfl) ⟨154032, by rfl⟩ : syracuseStep 410753 = 308065) B308065
theorem B1033357 : Blo 271824 1033357 := bstep (se 3 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 1033357 = 387509) B387509
theorem B410771 : Blo 271824 410771 := bstep (se 1 (by rfl) ⟨308078, by rfl⟩ : syracuseStep 410771 = 616157) B616157
theorem B410801 : Blo 271824 410801 := bstep (se 2 (by rfl) ⟨154050, by rfl⟩ : syracuseStep 410801 = 308101) B308101
theorem B410819 : Blo 271824 410819 := bstep (se 1 (by rfl) ⟨308114, by rfl⟩ : syracuseStep 410819 = 616229) B616229
theorem B410849 : Blo 271824 410849 := bstep (se 2 (by rfl) ⟨154068, by rfl⟩ : syracuseStep 410849 = 308137) B308137
theorem B410867 : Blo 271824 410867 := bstep (se 1 (by rfl) ⟨308150, by rfl⟩ : syracuseStep 410867 = 616301) B616301
theorem B410897 : Blo 271824 410897 := bstep (se 2 (by rfl) ⟨154086, by rfl⟩ : syracuseStep 410897 = 308173) B308173
theorem B345379 : Blo 271824 345379 := bstep (se 1 (by rfl) ⟨259034, by rfl⟩ : syracuseStep 345379 = 518069) B518069
theorem B410915 : Blo 271824 410915 := bstep (se 1 (by rfl) ⟨308186, by rfl⟩ : syracuseStep 410915 = 616373) B616373
theorem B410945 : Blo 271824 410945 := bstep (se 2 (by rfl) ⟨154104, by rfl⟩ : syracuseStep 410945 = 308209) B308209
theorem B410963 : Blo 271824 410963 := bstep (se 1 (by rfl) ⟨308222, by rfl⟩ : syracuseStep 410963 = 616445) B616445
theorem B410993 : Blo 271824 410993 := bstep (se 2 (by rfl) ⟨154122, by rfl⟩ : syracuseStep 410993 = 308245) B308245
theorem B345475 : Blo 271824 345475 := bstep (se 1 (by rfl) ⟨259106, by rfl⟩ : syracuseStep 345475 = 518213) B518213
theorem B411011 : Blo 271824 411011 := bstep (se 1 (by rfl) ⟨308258, by rfl⟩ : syracuseStep 411011 = 616517) B616517
theorem B411041 : Blo 271824 411041 := bstep (se 2 (by rfl) ⟨154140, by rfl⟩ : syracuseStep 411041 = 308281) B308281
theorem B411059 : Blo 271824 411059 := bstep (se 1 (by rfl) ⟨308294, by rfl⟩ : syracuseStep 411059 = 616589) B616589
theorem B411089 : Blo 271824 411089 := bstep (se 2 (by rfl) ⟨154158, by rfl⟩ : syracuseStep 411089 = 308317) B308317
theorem B411107 : Blo 271824 411107 := bstep (se 1 (by rfl) ⟨308330, by rfl⟩ : syracuseStep 411107 = 616661) B616661
theorem B411137 : Blo 271824 411137 := bstep (se 2 (by rfl) ⟨154176, by rfl⟩ : syracuseStep 411137 = 308353) B308353
theorem B935441 : Blo 271824 935441 := bstep (se 2 (by rfl) ⟨350790, by rfl⟩ : syracuseStep 935441 = 701581) B701581
theorem B411155 : Blo 271824 411155 := bstep (se 1 (by rfl) ⟨308366, by rfl⟩ : syracuseStep 411155 = 616733) B616733
theorem B411185 : Blo 271824 411185 := bstep (se 2 (by rfl) ⟨154194, by rfl⟩ : syracuseStep 411185 = 308389) B308389
theorem B411203 : Blo 271824 411203 := bstep (se 1 (by rfl) ⟨308402, by rfl⟩ : syracuseStep 411203 = 616805) B616805
theorem B411233 : Blo 271824 411233 := bstep (se 2 (by rfl) ⟨154212, by rfl⟩ : syracuseStep 411233 = 308425) B308425
theorem B411251 : Blo 271824 411251 := bstep (se 1 (by rfl) ⟨308438, by rfl⟩ : syracuseStep 411251 = 616877) B616877
theorem B411281 : Blo 271824 411281 := bstep (se 2 (by rfl) ⟨154230, by rfl⟩ : syracuseStep 411281 = 308461) B308461
theorem B411299 : Blo 271824 411299 := bstep (se 1 (by rfl) ⟨308474, by rfl⟩ : syracuseStep 411299 = 616949) B616949
theorem B411329 : Blo 271824 411329 := bstep (se 2 (by rfl) ⟨154248, by rfl⟩ : syracuseStep 411329 = 308497) B308497
theorem B411347 : Blo 271824 411347 := bstep (se 1 (by rfl) ⟨308510, by rfl⟩ : syracuseStep 411347 = 617021) B617021
theorem B411377 : Blo 271824 411377 := bstep (se 2 (by rfl) ⟨154266, by rfl⟩ : syracuseStep 411377 = 308533) B308533
theorem B411395 : Blo 271824 411395 := bstep (se 1 (by rfl) ⟨308546, by rfl⟩ : syracuseStep 411395 = 617093) B617093
theorem B411425 : Blo 271824 411425 := bstep (se 2 (by rfl) ⟨154284, by rfl⟩ : syracuseStep 411425 = 308569) B308569
theorem B411443 : Blo 271824 411443 := bstep (se 1 (by rfl) ⟨308582, by rfl⟩ : syracuseStep 411443 = 617165) B617165
theorem B411473 : Blo 271824 411473 := bstep (se 2 (by rfl) ⟨154302, by rfl⟩ : syracuseStep 411473 = 308605) B308605
theorem B411491 : Blo 271824 411491 := bstep (se 1 (by rfl) ⟨308618, by rfl⟩ : syracuseStep 411491 = 617237) B617237
theorem B345971 : Blo 271824 345971 := bstep (se 1 (by rfl) ⟨259478, by rfl⟩ : syracuseStep 345971 = 518957) B518957
theorem B411521 : Blo 271824 411521 := bstep (se 2 (by rfl) ⟨154320, by rfl⟩ : syracuseStep 411521 = 308641) B308641
theorem B411539 : Blo 271824 411539 := bstep (se 1 (by rfl) ⟨308654, by rfl⟩ : syracuseStep 411539 = 617309) B617309
theorem B1034147 : Blo 271824 1034147 := bstep (se 1 (by rfl) ⟨775610, by rfl⟩ : syracuseStep 1034147 = 1551221) B1551221
theorem B411569 : Blo 271824 411569 := bstep (se 2 (by rfl) ⟨154338, by rfl⟩ : syracuseStep 411569 = 308677) B308677
theorem B411587 : Blo 271824 411587 := bstep (se 1 (by rfl) ⟨308690, by rfl⟩ : syracuseStep 411587 = 617381) B617381
theorem B1165261 : Blo 271824 1165261 := bstep (se 3 (by rfl) ⟨218486, by rfl⟩ : syracuseStep 1165261 = 436973) B436973
theorem B411617 : Blo 271824 411617 := bstep (se 2 (by rfl) ⟨154356, by rfl⟩ : syracuseStep 411617 = 308713) B308713
theorem B411635 : Blo 271824 411635 := bstep (se 1 (by rfl) ⟨308726, by rfl⟩ : syracuseStep 411635 = 617453) B617453
theorem B411665 : Blo 271824 411665 := bstep (se 2 (by rfl) ⟨154374, by rfl⟩ : syracuseStep 411665 = 308749) B308749
theorem B411683 : Blo 271824 411683 := bstep (se 1 (by rfl) ⟨308762, by rfl⟩ : syracuseStep 411683 = 617525) B617525
theorem B411713 : Blo 271824 411713 := bstep (se 2 (by rfl) ⟨154392, by rfl⟩ : syracuseStep 411713 = 308785) B308785
theorem B411731 : Blo 271824 411731 := bstep (se 1 (by rfl) ⟨308798, by rfl⟩ : syracuseStep 411731 = 617597) B617597
theorem B411761 : Blo 271824 411761 := bstep (se 2 (by rfl) ⟨154410, by rfl⟩ : syracuseStep 411761 = 308821) B308821
theorem B739459 : Blo 271824 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B411779 : Blo 271824 411779 := bstep (se 1 (by rfl) ⟨308834, by rfl⟩ : syracuseStep 411779 = 617669) B617669
theorem B411809 : Blo 271824 411809 := bstep (se 2 (by rfl) ⟨154428, by rfl⟩ : syracuseStep 411809 = 308857) B308857
theorem B411827 : Blo 271824 411827 := bstep (se 1 (by rfl) ⟨308870, by rfl⟩ : syracuseStep 411827 = 617741) B617741
theorem B411857 : Blo 271824 411857 := bstep (se 2 (by rfl) ⟨154446, by rfl⟩ : syracuseStep 411857 = 308893) B308893
theorem B411875 : Blo 271824 411875 := bstep (se 1 (by rfl) ⟨308906, by rfl⟩ : syracuseStep 411875 = 617813) B617813
theorem B1755377 : Blo 271824 1755377 := bstep (se 2 (by rfl) ⟨658266, by rfl⟩ : syracuseStep 1755377 = 1316533) B1316533
theorem B411905 : Blo 271824 411905 := bstep (se 2 (by rfl) ⟨154464, by rfl⟩ : syracuseStep 411905 = 308929) B308929
theorem B739601 : Blo 271824 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B411923 : Blo 271824 411923 := bstep (se 1 (by rfl) ⟨308942, by rfl⟩ : syracuseStep 411923 = 617885) B617885
theorem B1165603 : Blo 271824 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B411953 : Blo 271824 411953 := bstep (se 2 (by rfl) ⟨154482, by rfl⟩ : syracuseStep 411953 = 308965) B308965
theorem B411971 : Blo 271824 411971 := bstep (se 1 (by rfl) ⟨308978, by rfl⟩ : syracuseStep 411971 = 617957) B617957
theorem B412001 : Blo 271824 412001 := bstep (se 2 (by rfl) ⟨154500, by rfl⟩ : syracuseStep 412001 = 309001) B309001
theorem B412019 : Blo 271824 412019 := bstep (se 1 (by rfl) ⟨309014, by rfl⟩ : syracuseStep 412019 = 618029) B618029
theorem B313715 : Blo 271824 313715 := bstep (se 1 (by rfl) ⟨235286, by rfl⟩ : syracuseStep 313715 = 470573) B470573
theorem B412049 : Blo 271824 412049 := bstep (se 2 (by rfl) ⟨154518, by rfl⟩ : syracuseStep 412049 = 309037) B309037
theorem B412067 : Blo 271824 412067 := bstep (se 1 (by rfl) ⟨309050, by rfl⟩ : syracuseStep 412067 = 618101) B618101
theorem B412097 : Blo 271824 412097 := bstep (se 2 (by rfl) ⟨154536, by rfl⟩ : syracuseStep 412097 = 309073) B309073
theorem B412115 : Blo 271824 412115 := bstep (se 1 (by rfl) ⟨309086, by rfl⟩ : syracuseStep 412115 = 618173) B618173
theorem B510449 : Blo 271824 510449 := bstep (se 2 (by rfl) ⟨191418, by rfl⟩ : syracuseStep 510449 = 382837) B382837
theorem B412145 : Blo 271824 412145 := bstep (se 2 (by rfl) ⟨154554, by rfl⟩ : syracuseStep 412145 = 309109) B309109
theorem B412163 : Blo 271824 412163 := bstep (se 1 (by rfl) ⟨309122, by rfl⟩ : syracuseStep 412163 = 618245) B618245
theorem B412193 : Blo 271824 412193 := bstep (se 2 (by rfl) ⟨154572, by rfl⟩ : syracuseStep 412193 = 309145) B309145
theorem B1034801 : Blo 271824 1034801 := bstep (se 2 (by rfl) ⟨388050, by rfl⟩ : syracuseStep 1034801 = 776101) B776101
theorem B346675 : Blo 271824 346675 := bstep (se 1 (by rfl) ⟨260006, by rfl⟩ : syracuseStep 346675 = 520013) B520013
theorem B412211 : Blo 271824 412211 := bstep (se 1 (by rfl) ⟨309158, by rfl⟩ : syracuseStep 412211 = 618317) B618317
theorem B412241 : Blo 271824 412241 := bstep (se 2 (by rfl) ⟨154590, by rfl⟩ : syracuseStep 412241 = 309181) B309181
theorem B412259 : Blo 271824 412259 := bstep (se 1 (by rfl) ⟨309194, by rfl⟩ : syracuseStep 412259 = 618389) B618389
theorem B412289 : Blo 271824 412289 := bstep (se 2 (by rfl) ⟨154608, by rfl⟩ : syracuseStep 412289 = 309217) B309217
theorem B412307 : Blo 271824 412307 := bstep (se 1 (by rfl) ⟨309230, by rfl⟩ : syracuseStep 412307 = 618461) B618461
theorem B346771 : Blo 271824 346771 := bstep (se 1 (by rfl) ⟨260078, by rfl⟩ : syracuseStep 346771 = 520157) B520157
theorem B412337 : Blo 271824 412337 := bstep (se 2 (by rfl) ⟨154626, by rfl⟩ : syracuseStep 412337 = 309253) B309253
theorem B412355 : Blo 271824 412355 := bstep (se 1 (by rfl) ⟨309266, by rfl⟩ : syracuseStep 412355 = 618533) B618533
theorem B412385 : Blo 271824 412385 := bstep (se 2 (by rfl) ⟨154644, by rfl⟩ : syracuseStep 412385 = 309289) B309289
theorem B412403 : Blo 271824 412403 := bstep (se 1 (by rfl) ⟨309302, by rfl⟩ : syracuseStep 412403 = 618605) B618605
theorem B412433 : Blo 271824 412433 := bstep (se 2 (by rfl) ⟨154662, by rfl⟩ : syracuseStep 412433 = 309325) B309325
theorem B412451 : Blo 271824 412451 := bstep (se 1 (by rfl) ⟨309338, by rfl⟩ : syracuseStep 412451 = 618677) B618677
theorem B412481 : Blo 271824 412481 := bstep (se 2 (by rfl) ⟨154680, by rfl⟩ : syracuseStep 412481 = 309361) B309361
theorem B412499 : Blo 271824 412499 := bstep (se 1 (by rfl) ⟨309374, by rfl⟩ : syracuseStep 412499 = 618749) B618749
theorem B412529 : Blo 271824 412529 := bstep (se 2 (by rfl) ⟨154698, by rfl⟩ : syracuseStep 412529 = 309397) B309397
theorem B412547 : Blo 271824 412547 := bstep (se 1 (by rfl) ⟨309410, by rfl⟩ : syracuseStep 412547 = 618821) B618821
theorem B412577 : Blo 271824 412577 := bstep (se 2 (by rfl) ⟨154716, by rfl⟩ : syracuseStep 412577 = 309433) B309433
theorem B412595 : Blo 271824 412595 := bstep (se 1 (by rfl) ⟨309446, by rfl⟩ : syracuseStep 412595 = 618893) B618893
theorem B412625 : Blo 271824 412625 := bstep (se 2 (by rfl) ⟨154734, by rfl⟩ : syracuseStep 412625 = 309469) B309469
theorem B412643 : Blo 271824 412643 := bstep (se 1 (by rfl) ⟨309482, by rfl⟩ : syracuseStep 412643 = 618965) B618965
theorem B412673 : Blo 271824 412673 := bstep (se 2 (by rfl) ⟨154752, by rfl⟩ : syracuseStep 412673 = 309505) B309505
theorem B412691 : Blo 271824 412691 := bstep (se 1 (by rfl) ⟨309518, by rfl⟩ : syracuseStep 412691 = 619037) B619037
theorem B412721 : Blo 271824 412721 := bstep (se 2 (by rfl) ⟨154770, by rfl⟩ : syracuseStep 412721 = 309541) B309541
theorem B412739 : Blo 271824 412739 := bstep (se 1 (by rfl) ⟨309554, by rfl⟩ : syracuseStep 412739 = 619109) B619109
theorem B412769 : Blo 271824 412769 := bstep (se 2 (by rfl) ⟨154788, by rfl⟩ : syracuseStep 412769 = 309577) B309577
theorem B412787 : Blo 271824 412787 := bstep (se 1 (by rfl) ⟨309590, by rfl⟩ : syracuseStep 412787 = 619181) B619181
theorem B347267 : Blo 271824 347267 := bstep (se 1 (by rfl) ⟨260450, by rfl⟩ : syracuseStep 347267 = 520901) B520901
theorem B740497 : Blo 271824 740497 := bstep (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) B555373
theorem B412817 : Blo 271824 412817 := bstep (se 2 (by rfl) ⟨154806, by rfl⟩ : syracuseStep 412817 = 309613) B309613
theorem B412835 : Blo 271824 412835 := bstep (se 1 (by rfl) ⟨309626, by rfl⟩ : syracuseStep 412835 = 619253) B619253
theorem B412865 : Blo 271824 412865 := bstep (se 2 (by rfl) ⟨154824, by rfl⟩ : syracuseStep 412865 = 309649) B309649
theorem B412883 : Blo 271824 412883 := bstep (se 1 (by rfl) ⟨309662, by rfl⟩ : syracuseStep 412883 = 619325) B619325
theorem B5950691 : Blo 271824 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B412913 : Blo 271824 412913 := bstep (se 2 (by rfl) ⟨154842, by rfl⟩ : syracuseStep 412913 = 309685) B309685
theorem B1395953 : Blo 271824 1395953 := bstep (se 2 (by rfl) ⟨523482, by rfl⟩ : syracuseStep 1395953 = 1046965) B1046965
theorem B412931 : Blo 271824 412931 := bstep (se 1 (by rfl) ⟨309698, by rfl⟩ : syracuseStep 412931 = 619397) B619397
theorem B412961 : Blo 271824 412961 := bstep (se 2 (by rfl) ⟨154860, by rfl⟩ : syracuseStep 412961 = 309721) B309721
theorem B412979 : Blo 271824 412979 := bstep (se 1 (by rfl) ⟨309734, by rfl⟩ : syracuseStep 412979 = 619469) B619469
theorem B413009 : Blo 271824 413009 := bstep (se 2 (by rfl) ⟨154878, by rfl⟩ : syracuseStep 413009 = 309757) B309757
theorem B413027 : Blo 271824 413027 := bstep (se 1 (by rfl) ⟨309770, by rfl⟩ : syracuseStep 413027 = 619541) B619541
theorem B413057 : Blo 271824 413057 := bstep (se 2 (by rfl) ⟨154896, by rfl⟩ : syracuseStep 413057 = 309793) B309793
theorem B413075 : Blo 271824 413075 := bstep (se 1 (by rfl) ⟨309806, by rfl⟩ : syracuseStep 413075 = 619613) B619613
theorem B413105 : Blo 271824 413105 := bstep (se 2 (by rfl) ⟨154914, by rfl⟩ : syracuseStep 413105 = 309829) B309829
theorem B413123 : Blo 271824 413123 := bstep (se 1 (by rfl) ⟨309842, by rfl⟩ : syracuseStep 413123 = 619685) B619685
theorem B413153 : Blo 271824 413153 := bstep (se 2 (by rfl) ⟨154932, by rfl⟩ : syracuseStep 413153 = 309865) B309865
theorem B413171 : Blo 271824 413171 := bstep (se 1 (by rfl) ⟨309878, by rfl⟩ : syracuseStep 413171 = 619757) B619757
theorem B413201 : Blo 271824 413201 := bstep (se 2 (by rfl) ⟨154950, by rfl⟩ : syracuseStep 413201 = 309901) B309901
theorem B413219 : Blo 271824 413219 := bstep (se 1 (by rfl) ⟨309914, by rfl⟩ : syracuseStep 413219 = 619829) B619829
theorem B413249 : Blo 271824 413249 := bstep (se 2 (by rfl) ⟨154968, by rfl⟩ : syracuseStep 413249 = 309937) B309937
theorem B413267 : Blo 271824 413267 := bstep (se 1 (by rfl) ⟨309950, by rfl⟩ : syracuseStep 413267 = 619901) B619901
theorem B413297 : Blo 271824 413297 := bstep (se 2 (by rfl) ⟨154986, by rfl⟩ : syracuseStep 413297 = 309973) B309973
theorem B413315 : Blo 271824 413315 := bstep (se 1 (by rfl) ⟨309986, by rfl⟩ : syracuseStep 413315 = 619973) B619973
theorem B413345 : Blo 271824 413345 := bstep (se 2 (by rfl) ⟨155004, by rfl⟩ : syracuseStep 413345 = 310009) B310009
theorem B413363 : Blo 271824 413363 := bstep (se 1 (by rfl) ⟨310022, by rfl⟩ : syracuseStep 413363 = 620045) B620045
theorem B413393 : Blo 271824 413393 := bstep (se 2 (by rfl) ⟨155022, by rfl⟩ : syracuseStep 413393 = 310045) B310045
theorem B1986275 : Blo 271824 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B413411 : Blo 271824 413411 := bstep (se 1 (by rfl) ⟨310058, by rfl⟩ : syracuseStep 413411 = 620117) B620117
theorem B413441 : Blo 271824 413441 := bstep (se 2 (by rfl) ⟨155040, by rfl⟩ : syracuseStep 413441 = 310081) B310081
theorem B413459 : Blo 271824 413459 := bstep (se 1 (by rfl) ⟨310094, by rfl⟩ : syracuseStep 413459 = 620189) B620189
theorem B413489 : Blo 271824 413489 := bstep (se 2 (by rfl) ⟨155058, by rfl⟩ : syracuseStep 413489 = 310117) B310117
theorem B347971 : Blo 271824 347971 := bstep (se 1 (by rfl) ⟨260978, by rfl⟩ : syracuseStep 347971 = 521957) B521957
theorem B413507 : Blo 271824 413507 := bstep (se 1 (by rfl) ⟨310130, by rfl⟩ : syracuseStep 413507 = 620261) B620261
theorem B413537 : Blo 271824 413537 := bstep (se 2 (by rfl) ⟨155076, by rfl⟩ : syracuseStep 413537 = 310153) B310153
theorem B413555 : Blo 271824 413555 := bstep (se 1 (by rfl) ⟨310166, by rfl⟩ : syracuseStep 413555 = 620333) B620333
theorem B872333 : Blo 271824 872333 := bstep (se 3 (by rfl) ⟨163562, by rfl⟩ : syracuseStep 872333 = 327125) B327125
theorem B2346893 : Blo 271824 2346893 := bstep (se 3 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 2346893 = 880085) B880085
theorem B413585 : Blo 271824 413585 := bstep (se 2 (by rfl) ⟨155094, by rfl⟩ : syracuseStep 413585 = 310189) B310189
theorem B348067 : Blo 271824 348067 := bstep (se 1 (by rfl) ⟨261050, by rfl⟩ : syracuseStep 348067 = 522101) B522101
theorem B413603 : Blo 271824 413603 := bstep (se 1 (by rfl) ⟨310202, by rfl⟩ : syracuseStep 413603 = 620405) B620405
theorem B413633 : Blo 271824 413633 := bstep (se 2 (by rfl) ⟨155112, by rfl⟩ : syracuseStep 413633 = 310225) B310225
theorem B413651 : Blo 271824 413651 := bstep (se 1 (by rfl) ⟨310238, by rfl⟩ : syracuseStep 413651 = 620477) B620477
theorem B1036259 : Blo 271824 1036259 := bstep (se 1 (by rfl) ⟨777194, by rfl⟩ : syracuseStep 1036259 = 1554389) B1554389
theorem B1036273 : Blo 271824 1036273 := bstep (se 2 (by rfl) ⟨388602, by rfl⟩ : syracuseStep 1036273 = 777205) B777205
theorem B937969 : Blo 271824 937969 := bstep (se 2 (by rfl) ⟨351738, by rfl⟩ : syracuseStep 937969 = 703477) B703477
theorem B413681 : Blo 271824 413681 := bstep (se 2 (by rfl) ⟨155130, by rfl⟩ : syracuseStep 413681 = 310261) B310261
theorem B413699 : Blo 271824 413699 := bstep (se 1 (by rfl) ⟨310274, by rfl⟩ : syracuseStep 413699 = 620549) B620549
theorem B413729 : Blo 271824 413729 := bstep (se 2 (by rfl) ⟨155148, by rfl⟩ : syracuseStep 413729 = 310297) B310297
theorem B1560653 : Blo 271824 1560653 := bstep (se 3 (by rfl) ⟨292622, by rfl⟩ : syracuseStep 1560653 = 585245) B585245
theorem B774289 : Blo 271824 774289 := bstep (se 2 (by rfl) ⟨290358, by rfl⟩ : syracuseStep 774289 = 580717) B580717
theorem B348563 : Blo 271824 348563 := bstep (se 1 (by rfl) ⟨261422, by rfl⟩ : syracuseStep 348563 = 522845) B522845
theorem B17125829 : Blo 271824 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B775565 : Blo 271824 775565 := bstep (se 3 (by rfl) ⟨145418, by rfl⟩ : syracuseStep 775565 = 290837) B290837
theorem B611729 : Blo 271824 611729 := bstep (se 2 (by rfl) ⟨229398, by rfl⟩ : syracuseStep 611729 = 458797) B458797
theorem B611747 : Blo 271824 611747 := bstep (se 1 (by rfl) ⟨458810, by rfl⟩ : syracuseStep 611747 = 917621) B917621
theorem B1037731 : Blo 271824 1037731 := bstep (se 1 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 1037731 = 1556597) B1556597
theorem B775747 : Blo 271824 775747 := bstep (se 1 (by rfl) ⟨581810, by rfl⟩ : syracuseStep 775747 = 1163621) B1163621
theorem B775793 : Blo 271824 775793 := bstep (se 2 (by rfl) ⟨290922, by rfl⟩ : syracuseStep 775793 = 581845) B581845
theorem B612017 : Blo 271824 612017 := bstep (se 2 (by rfl) ⟨229506, by rfl⟩ : syracuseStep 612017 = 459013) B459013
theorem B612035 : Blo 271824 612035 := bstep (se 1 (by rfl) ⟨459026, by rfl⟩ : syracuseStep 612035 = 918053) B918053
theorem B612145 : Blo 271824 612145 := bstep (se 2 (by rfl) ⟨229554, by rfl⟩ : syracuseStep 612145 = 459109) B459109
theorem B612305 : Blo 271824 612305 := bstep (se 2 (by rfl) ⟨229614, by rfl⟩ : syracuseStep 612305 = 459229) B459229
theorem B612323 : Blo 271824 612323 := bstep (se 1 (by rfl) ⟨459242, by rfl⟩ : syracuseStep 612323 = 918485) B918485
theorem B2086883 : Blo 271824 2086883 := bstep (se 1 (by rfl) ⟨1565162, by rfl⟩ : syracuseStep 2086883 = 3130325) B3130325
theorem B1169635 : Blo 271824 1169635 := bstep (se 1 (by rfl) ⟨877226, by rfl⟩ : syracuseStep 1169635 = 1754453) B1754453
theorem B612593 : Blo 271824 612593 := bstep (se 2 (by rfl) ⟨229722, by rfl⟩ : syracuseStep 612593 = 459445) B459445
theorem B612611 : Blo 271824 612611 := bstep (se 1 (by rfl) ⟨459458, by rfl⟩ : syracuseStep 612611 = 918917) B918917
theorem B1562885 : Blo 271824 1562885 := bstep (se 4 (by rfl) ⟨146520, by rfl⟩ : syracuseStep 1562885 = 293041) B293041
theorem B416195 : Blo 271824 416195 := bstep (se 1 (by rfl) ⟨312146, by rfl⟩ : syracuseStep 416195 = 624293) B624293
theorem B612881 : Blo 271824 612881 := bstep (se 2 (by rfl) ⟨229830, by rfl⟩ : syracuseStep 612881 = 459661) B459661
theorem B612899 : Blo 271824 612899 := bstep (se 1 (by rfl) ⟨459674, by rfl⟩ : syracuseStep 612899 = 919349) B919349
theorem B613169 : Blo 271824 613169 := bstep (se 2 (by rfl) ⟨229938, by rfl⟩ : syracuseStep 613169 = 459877) B459877
theorem B613187 : Blo 271824 613187 := bstep (se 1 (by rfl) ⟨459890, by rfl⟩ : syracuseStep 613187 = 919781) B919781
theorem B1563569 : Blo 271824 1563569 := bstep (se 2 (by rfl) ⟨586338, by rfl⟩ : syracuseStep 1563569 = 1172677) B1172677
theorem B777251 : Blo 271824 777251 := bstep (se 1 (by rfl) ⟨582938, by rfl⟩ : syracuseStep 777251 = 1165877) B1165877
theorem B613457 : Blo 271824 613457 := bstep (se 2 (by rfl) ⟨230046, by rfl⟩ : syracuseStep 613457 = 460093) B460093
theorem B613475 : Blo 271824 613475 := bstep (se 1 (by rfl) ⟨460106, by rfl⟩ : syracuseStep 613475 = 920213) B920213
theorem B1006769 : Blo 271824 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B1760453 : Blo 271824 1760453 := bstep (se 4 (by rfl) ⟨165042, by rfl⟩ : syracuseStep 1760453 = 330085) B330085
theorem B875843 : Blo 271824 875843 := bstep (se 1 (by rfl) ⟨656882, by rfl⟩ : syracuseStep 875843 = 1313765) B1313765
theorem B613745 : Blo 271824 613745 := bstep (se 2 (by rfl) ⟨230154, by rfl⟩ : syracuseStep 613745 = 460309) B460309
theorem B613763 : Blo 271824 613763 := bstep (se 1 (by rfl) ⟨460322, by rfl⟩ : syracuseStep 613763 = 920645) B920645
theorem B1007011 : Blo 271824 1007011 := bstep (se 1 (by rfl) ⟨755258, by rfl⟩ : syracuseStep 1007011 = 1510517) B1510517
theorem B1170865 : Blo 271824 1170865 := bstep (se 2 (by rfl) ⟨439074, by rfl⟩ : syracuseStep 1170865 = 878149) B878149
theorem B1039949 : Blo 271824 1039949 := bstep (se 3 (by rfl) ⟨194990, by rfl⟩ : syracuseStep 1039949 = 389981) B389981
theorem B351859 : Blo 271824 351859 := bstep (se 1 (by rfl) ⟨263894, by rfl⟩ : syracuseStep 351859 = 527789) B527789
theorem B614033 : Blo 271824 614033 := bstep (se 2 (by rfl) ⟨230262, by rfl⟩ : syracuseStep 614033 = 460525) B460525
theorem B614051 : Blo 271824 614051 := bstep (se 1 (by rfl) ⟨460538, by rfl⟩ : syracuseStep 614051 = 921077) B921077
theorem B417521 : Blo 271824 417521 := bstep (se 2 (by rfl) ⟨156570, by rfl⟩ : syracuseStep 417521 = 313141) B313141
theorem B581393 : Blo 271824 581393 := bstep (se 2 (by rfl) ⟨218022, by rfl⟩ : syracuseStep 581393 = 436045) B436045
theorem B876433 : Blo 271824 876433 := bstep (se 2 (by rfl) ⟨328662, by rfl⟩ : syracuseStep 876433 = 657325) B657325
theorem B614321 : Blo 271824 614321 := bstep (se 2 (by rfl) ⟨230370, by rfl⟩ : syracuseStep 614321 = 460741) B460741
theorem B614339 : Blo 271824 614339 := bstep (se 1 (by rfl) ⟨460754, by rfl⟩ : syracuseStep 614339 = 921509) B921509
theorem B352211 : Blo 271824 352211 := bstep (se 1 (by rfl) ⟨264158, by rfl⟩ : syracuseStep 352211 = 528317) B528317
theorem B614609 : Blo 271824 614609 := bstep (se 2 (by rfl) ⟨230478, by rfl⟩ : syracuseStep 614609 = 460957) B460957
theorem B614627 : Blo 271824 614627 := bstep (se 1 (by rfl) ⟨460970, by rfl⟩ : syracuseStep 614627 = 921941) B921941
theorem B418019 : Blo 271824 418019 := bstep (se 1 (by rfl) ⟨313514, by rfl⟩ : syracuseStep 418019 = 627029) B627029
theorem B778481 : Blo 271824 778481 := bstep (se 2 (by rfl) ⟨291930, by rfl⟩ : syracuseStep 778481 = 583861) B583861
theorem B942349 : Blo 271824 942349 := bstep (se 3 (by rfl) ⟨176690, by rfl⟩ : syracuseStep 942349 = 353381) B353381
theorem B516451 : Blo 271824 516451 := bstep (se 1 (by rfl) ⟨387338, by rfl⟩ : syracuseStep 516451 = 774677) B774677
theorem B1565027 : Blo 271824 1565027 := bstep (se 1 (by rfl) ⟨1173770, by rfl⟩ : syracuseStep 1565027 = 2347541) B2347541
theorem B4710797 : Blo 271824 4710797 := bstep (se 3 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 4710797 = 1766549) B1766549
theorem B2974133 : Blo 271824 2974133 := bstep (se 5 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 2974133 = 278825) B278825
theorem B614897 : Blo 271824 614897 := bstep (se 2 (by rfl) ⟨230586, by rfl⟩ : syracuseStep 614897 = 461173) B461173
theorem B516611 : Blo 271824 516611 := bstep (se 1 (by rfl) ⟨387458, by rfl⟩ : syracuseStep 516611 = 774917) B774917
theorem B614915 : Blo 271824 614915 := bstep (se 1 (by rfl) ⟨461186, by rfl⟩ : syracuseStep 614915 = 922373) B922373
theorem B1401457 : Blo 271824 1401457 := bstep (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) B1051093
theorem B942787 : Blo 271824 942787 := bstep (se 1 (by rfl) ⟨707090, by rfl⟩ : syracuseStep 942787 = 1414181) B1414181
theorem B615185 : Blo 271824 615185 := bstep (se 2 (by rfl) ⟨230694, by rfl⟩ : syracuseStep 615185 = 461389) B461389
theorem B615203 : Blo 271824 615203 := bstep (se 1 (by rfl) ⟨461402, by rfl⟩ : syracuseStep 615203 = 922805) B922805
theorem B418627 : Blo 271824 418627 := bstep (se 1 (by rfl) ⟨313970, by rfl⟩ : syracuseStep 418627 = 627941) B627941
theorem B615473 : Blo 271824 615473 := bstep (se 2 (by rfl) ⟨230802, by rfl⟩ : syracuseStep 615473 = 461605) B461605
theorem B615491 : Blo 271824 615491 := bstep (se 1 (by rfl) ⟨461618, by rfl⟩ : syracuseStep 615491 = 923237) B923237
theorem B615761 : Blo 271824 615761 := bstep (se 2 (by rfl) ⟨230910, by rfl⟩ : syracuseStep 615761 = 461821) B461821
theorem B615779 : Blo 271824 615779 := bstep (se 1 (by rfl) ⟨461834, by rfl⟩ : syracuseStep 615779 = 923669) B923669
theorem B583075 : Blo 271824 583075 := bstep (se 1 (by rfl) ⟨437306, by rfl⟩ : syracuseStep 583075 = 874613) B874613
theorem B517681 : Blo 271824 517681 := bstep (se 2 (by rfl) ⟨194130, by rfl⟩ : syracuseStep 517681 = 388261) B388261
theorem B616049 : Blo 271824 616049 := bstep (se 2 (by rfl) ⟨231018, by rfl⟩ : syracuseStep 616049 = 462037) B462037
theorem B616067 : Blo 271824 616067 := bstep (se 1 (by rfl) ⟨462050, by rfl⟩ : syracuseStep 616067 = 924101) B924101
theorem B681617 : Blo 271824 681617 := bstep (se 2 (by rfl) ⟨255606, by rfl⟩ : syracuseStep 681617 = 511213) B511213
theorem B779939 : Blo 271824 779939 := bstep (se 1 (by rfl) ⟨584954, by rfl⟩ : syracuseStep 779939 = 1169909) B1169909
theorem B583537 : Blo 271824 583537 := bstep (se 2 (by rfl) ⟨218826, by rfl⟩ : syracuseStep 583537 = 437653) B437653
theorem B616337 : Blo 271824 616337 := bstep (se 2 (by rfl) ⟨231126, by rfl⟩ : syracuseStep 616337 = 462253) B462253
theorem B616355 : Blo 271824 616355 := bstep (se 1 (by rfl) ⟨462266, by rfl⟩ : syracuseStep 616355 = 924533) B924533
theorem B616625 : Blo 271824 616625 := bstep (se 2 (by rfl) ⟨231234, by rfl⟩ : syracuseStep 616625 = 462469) B462469
theorem B3106997 : Blo 271824 3106997 := bstep (se 5 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 3106997 = 291281) B291281
theorem B616643 : Blo 271824 616643 := bstep (se 1 (by rfl) ⟨462482, by rfl⟩ : syracuseStep 616643 = 924965) B924965
theorem B1894661 : Blo 271824 1894661 := bstep (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) B355249
theorem B1042865 : Blo 271824 1042865 := bstep (se 2 (by rfl) ⟨391074, by rfl⟩ : syracuseStep 1042865 = 782149) B782149
theorem B780749 : Blo 271824 780749 := bstep (se 3 (by rfl) ⟨146390, by rfl⟩ : syracuseStep 780749 = 292781) B292781
theorem B616913 : Blo 271824 616913 := bstep (se 2 (by rfl) ⟨231342, by rfl⟩ : syracuseStep 616913 = 462685) B462685
theorem B1993187 : Blo 271824 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B616931 : Blo 271824 616931 := bstep (se 1 (by rfl) ⟨462698, by rfl⟩ : syracuseStep 616931 = 925397) B925397
theorem B518737 : Blo 271824 518737 := bstep (se 2 (by rfl) ⟨194526, by rfl⟩ : syracuseStep 518737 = 389053) B389053
theorem B3500657 : Blo 271824 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B2484877 : Blo 271824 2484877 := bstep (se 3 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 2484877 = 931829) B931829
theorem B780941 : Blo 271824 780941 := bstep (se 3 (by rfl) ⟨146426, by rfl⟩ : syracuseStep 780941 = 292853) B292853
theorem B879277 : Blo 271824 879277 := bstep (se 3 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 879277 = 329729) B329729
theorem B617201 : Blo 271824 617201 := bstep (se 2 (by rfl) ⟨231450, by rfl⟩ : syracuseStep 617201 = 462901) B462901
theorem B617219 : Blo 271824 617219 := bstep (se 1 (by rfl) ⟨462914, by rfl⟩ : syracuseStep 617219 = 925829) B925829
theorem B355123 : Blo 271824 355123 := bstep (se 1 (by rfl) ⟨266342, by rfl⟩ : syracuseStep 355123 = 532685) B532685
theorem B584579 : Blo 271824 584579 := bstep (se 1 (by rfl) ⟨438434, by rfl⟩ : syracuseStep 584579 = 876869) B876869
theorem B519139 : Blo 271824 519139 := bstep (se 1 (by rfl) ⟨389354, by rfl⟩ : syracuseStep 519139 = 778709) B778709
theorem B519185 : Blo 271824 519185 := bstep (se 2 (by rfl) ⟨194694, by rfl⟩ : syracuseStep 519185 = 389389) B389389
theorem B617489 : Blo 271824 617489 := bstep (se 2 (by rfl) ⟨231558, by rfl⟩ : syracuseStep 617489 = 463117) B463117
theorem B617507 : Blo 271824 617507 := bstep (se 1 (by rfl) ⟨463130, by rfl⟩ : syracuseStep 617507 = 926261) B926261
theorem B388147 : Blo 271824 388147 := bstep (se 1 (by rfl) ⟨291110, by rfl⟩ : syracuseStep 388147 = 582221) B582221
theorem B5270669 : Blo 271824 5270669 := bstep (se 3 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 5270669 = 1976501) B1976501
theorem B2092229 : Blo 271824 2092229 := bstep (se 4 (by rfl) ⟨196146, by rfl⟩ : syracuseStep 2092229 = 392293) B392293
theorem B519473 : Blo 271824 519473 := bstep (se 2 (by rfl) ⟨194802, by rfl⟩ : syracuseStep 519473 = 389605) B389605
theorem B1404209 : Blo 271824 1404209 := bstep (se 2 (by rfl) ⟨526578, by rfl⟩ : syracuseStep 1404209 = 1053157) B1053157
theorem B617777 : Blo 271824 617777 := bstep (se 2 (by rfl) ⟨231666, by rfl⟩ : syracuseStep 617777 = 463333) B463333
theorem B617795 : Blo 271824 617795 := bstep (se 1 (by rfl) ⟨463346, by rfl⟩ : syracuseStep 617795 = 926693) B926693
theorem B585091 : Blo 271824 585091 := bstep (se 1 (by rfl) ⟨438818, by rfl⟩ : syracuseStep 585091 = 877637) B877637
theorem B748945 : Blo 271824 748945 := bstep (se 2 (by rfl) ⟨280854, by rfl⟩ : syracuseStep 748945 = 561709) B561709
theorem B1568261 : Blo 271824 1568261 := bstep (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) B294049
theorem B618065 : Blo 271824 618065 := bstep (se 2 (by rfl) ⟨231774, by rfl⟩ : syracuseStep 618065 = 463549) B463549
theorem B618083 : Blo 271824 618083 := bstep (se 1 (by rfl) ⟨463562, by rfl⟩ : syracuseStep 618083 = 927125) B927125
theorem B781933 : Blo 271824 781933 := bstep (se 3 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 781933 = 293225) B293225
theorem B1765091 : Blo 271824 1765091 := bstep (se 1 (by rfl) ⟨1323818, by rfl⟩ : syracuseStep 1765091 = 2647637) B2647637
theorem B1175309 : Blo 271824 1175309 := bstep (se 3 (by rfl) ⟨220370, by rfl⟩ : syracuseStep 1175309 = 440741) B440741
theorem B1044323 : Blo 271824 1044323 := bstep (se 1 (by rfl) ⟨783242, by rfl⟩ : syracuseStep 1044323 = 1566485) B1566485
theorem B618353 : Blo 271824 618353 := bstep (se 2 (by rfl) ⟨231882, by rfl⟩ : syracuseStep 618353 = 463765) B463765
theorem B290675 : Blo 271824 290675 := bstep (se 1 (by rfl) ⟨218006, by rfl⟩ : syracuseStep 290675 = 436013) B436013
theorem B618371 : Blo 271824 618371 := bstep (se 1 (by rfl) ⟨463778, by rfl⟩ : syracuseStep 618371 = 927557) B927557
theorem B1699717 : Blo 271824 1699717 := bstep (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) B318697
theorem B1568717 : Blo 271824 1568717 := bstep (se 3 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 1568717 = 588269) B588269
theorem B5238755 : Blo 271824 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B2650097 : Blo 271824 2650097 := bstep (se 2 (by rfl) ⟨993786, by rfl⟩ : syracuseStep 2650097 = 1987573) B1987573
theorem B520195 : Blo 271824 520195 := bstep (se 1 (by rfl) ⟨390146, by rfl⟩ : syracuseStep 520195 = 780293) B780293
theorem B585809 : Blo 271824 585809 := bstep (se 2 (by rfl) ⟨219678, by rfl⟩ : syracuseStep 585809 = 439357) B439357
theorem B880739 : Blo 271824 880739 := bstep (se 1 (by rfl) ⟨660554, by rfl⟩ : syracuseStep 880739 = 1321109) B1321109
theorem B1667213 : Blo 271824 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B618641 : Blo 271824 618641 := bstep (se 2 (by rfl) ⟨231990, by rfl⟩ : syracuseStep 618641 = 463981) B463981
theorem B389281 : Blo 271824 389281 := bstep (se 2 (by rfl) ⟨145980, by rfl⟩ : syracuseStep 389281 = 291961) B291961
theorem B618659 : Blo 271824 618659 := bstep (se 1 (by rfl) ⟨463994, by rfl⟩ : syracuseStep 618659 = 927989) B927989
theorem B389377 : Blo 271824 389377 := bstep (se 2 (by rfl) ⟨146016, by rfl⟩ : syracuseStep 389377 = 292033) B292033
theorem B4714805 : Blo 271824 4714805 := bstep (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) B442013
theorem B1667405 : Blo 271824 1667405 := bstep (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) B625277
theorem B618929 : Blo 271824 618929 := bstep (se 2 (by rfl) ⟨232098, by rfl⟩ : syracuseStep 618929 = 464197) B464197
theorem B520643 : Blo 271824 520643 := bstep (se 1 (by rfl) ⟨390482, by rfl⟩ : syracuseStep 520643 = 780965) B780965
theorem B618947 : Blo 271824 618947 := bstep (se 1 (by rfl) ⟨464210, by rfl⟩ : syracuseStep 618947 = 928421) B928421
theorem B619217 : Blo 271824 619217 := bstep (se 2 (by rfl) ⟨232206, by rfl⟩ : syracuseStep 619217 = 464413) B464413
theorem B520931 : Blo 271824 520931 := bstep (se 1 (by rfl) ⟨390698, by rfl⟩ : syracuseStep 520931 = 781397) B781397
theorem B619235 : Blo 271824 619235 := bstep (se 1 (by rfl) ⟨464426, by rfl⟩ : syracuseStep 619235 = 928853) B928853
theorem B389873 : Blo 271824 389873 := bstep (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) B292405
theorem B1045325 : Blo 271824 1045325 := bstep (se 3 (by rfl) ⟨195998, by rfl⟩ : syracuseStep 1045325 = 391997) B391997
theorem B586595 : Blo 271824 586595 := bstep (se 1 (by rfl) ⟨439946, by rfl⟩ : syracuseStep 586595 = 879893) B879893
theorem B291811 : Blo 271824 291811 := bstep (se 1 (by rfl) ⟨218858, by rfl⟩ : syracuseStep 291811 = 437717) B437717
theorem B553969 : Blo 271824 553969 := bstep (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) B415477
theorem B619505 : Blo 271824 619505 := bstep (se 2 (by rfl) ⟨232314, by rfl⟩ : syracuseStep 619505 = 464629) B464629
theorem B619523 : Blo 271824 619523 := bstep (se 1 (by rfl) ⟨464642, by rfl⟩ : syracuseStep 619523 = 929285) B929285
theorem B619793 : Blo 271824 619793 := bstep (se 2 (by rfl) ⟨232422, by rfl⟩ : syracuseStep 619793 = 464845) B464845
theorem B619811 : Blo 271824 619811 := bstep (se 1 (by rfl) ⟨464858, by rfl⟩ : syracuseStep 619811 = 929717) B929717
theorem B783665 : Blo 271824 783665 := bstep (se 2 (by rfl) ⟨293874, by rfl⟩ : syracuseStep 783665 = 587749) B587749
theorem B783857 : Blo 271824 783857 := bstep (se 2 (by rfl) ⟨293946, by rfl⟩ : syracuseStep 783857 = 587893) B587893
theorem B620081 : Blo 271824 620081 := bstep (se 2 (by rfl) ⟨232530, by rfl⟩ : syracuseStep 620081 = 465061) B465061
theorem B620099 : Blo 271824 620099 := bstep (se 1 (by rfl) ⟨465074, by rfl⟩ : syracuseStep 620099 = 930149) B930149
theorem B390739 : Blo 271824 390739 := bstep (se 1 (by rfl) ⟨293054, by rfl⟩ : syracuseStep 390739 = 586109) B586109
theorem B521873 : Blo 271824 521873 := bstep (se 2 (by rfl) ⟨195702, by rfl⟩ : syracuseStep 521873 = 391405) B391405
theorem B882353 : Blo 271824 882353 := bstep (se 2 (by rfl) ⟨330882, by rfl⟩ : syracuseStep 882353 = 661765) B661765
theorem B390835 : Blo 271824 390835 := bstep (se 1 (by rfl) ⟨293126, by rfl⟩ : syracuseStep 390835 = 586253) B586253
theorem B587569 : Blo 271824 587569 := bstep (se 2 (by rfl) ⟨220338, by rfl⟩ : syracuseStep 587569 = 440677) B440677
theorem B1767217 : Blo 271824 1767217 := bstep (se 2 (by rfl) ⟨662706, by rfl⟩ : syracuseStep 1767217 = 1325413) B1325413
theorem B620369 : Blo 271824 620369 := bstep (se 2 (by rfl) ⟨232638, by rfl⟩ : syracuseStep 620369 = 465277) B465277
theorem B292691 : Blo 271824 292691 := bstep (se 1 (by rfl) ⟨219518, by rfl⟩ : syracuseStep 292691 = 439037) B439037
theorem B620387 : Blo 271824 620387 := bstep (se 1 (by rfl) ⟨465290, by rfl⟩ : syracuseStep 620387 = 930581) B930581
theorem B292819 : Blo 271824 292819 := bstep (se 1 (by rfl) ⟨219614, by rfl⟩ : syracuseStep 292819 = 439229) B439229
theorem B587825 : Blo 271824 587825 := bstep (se 2 (by rfl) ⟨220434, by rfl⟩ : syracuseStep 587825 = 440869) B440869
theorem B391331 : Blo 271824 391331 := bstep (se 1 (by rfl) ⟨293498, by rfl⟩ : syracuseStep 391331 = 586997) B586997
theorem B555185 : Blo 271824 555185 := bstep (se 2 (by rfl) ⟨208194, by rfl⟩ : syracuseStep 555185 = 416389) B416389
theorem B784849 : Blo 271824 784849 := bstep (se 2 (by rfl) ⟨294318, by rfl⟩ : syracuseStep 784849 = 588637) B588637
theorem B522769 : Blo 271824 522769 := bstep (se 2 (by rfl) ⟨196038, by rfl⟩ : syracuseStep 522769 = 392077) B392077
theorem B522929 : Blo 271824 522929 := bstep (se 2 (by rfl) ⟨196098, by rfl⟩ : syracuseStep 522929 = 392197) B392197
theorem B785123 : Blo 271824 785123 := bstep (se 1 (by rfl) ⟨588842, by rfl⟩ : syracuseStep 785123 = 1177685) B1177685
theorem B948995 : Blo 271824 948995 := bstep (se 1 (by rfl) ⟨711746, by rfl⟩ : syracuseStep 948995 = 1423493) B1423493
theorem B293635 : Blo 271824 293635 := bstep (se 1 (by rfl) ⟨220226, by rfl⟩ : syracuseStep 293635 = 440453) B440453
theorem B391969 : Blo 271824 391969 := bstep (se 2 (by rfl) ⟨146988, by rfl⟩ : syracuseStep 391969 = 293977) B293977
theorem B654115 : Blo 271824 654115 := bstep (se 1 (by rfl) ⟨490586, by rfl⟩ : syracuseStep 654115 = 981173) B981173
theorem B785315 : Blo 271824 785315 := bstep (se 1 (by rfl) ⟨588986, by rfl⟩ : syracuseStep 785315 = 1177973) B1177973
theorem B2489285 : Blo 271824 2489285 := bstep (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) B466741
theorem B523331 : Blo 271824 523331 := bstep (se 1 (by rfl) ⟨392498, by rfl⟩ : syracuseStep 523331 = 784997) B784997
theorem B392305 : Blo 271824 392305 := bstep (se 2 (by rfl) ⟨147114, by rfl⟩ : syracuseStep 392305 = 294229) B294229
theorem B326803 : Blo 271824 326803 := bstep (se 1 (by rfl) ⟨245102, by rfl⟩ : syracuseStep 326803 = 490205) B490205
theorem B490673 : Blo 271824 490673 := bstep (se 2 (by rfl) ⟨184002, by rfl⟩ : syracuseStep 490673 = 368005) B368005
theorem B490961 : Blo 271824 490961 := bstep (se 2 (by rfl) ⟨184110, by rfl⟩ : syracuseStep 490961 = 368221) B368221
theorem B753155 : Blo 271824 753155 := bstep (se 1 (by rfl) ⟨564866, by rfl⟩ : syracuseStep 753155 = 1129733) B1129733
theorem B2620997 : Blo 271824 2620997 := bstep (se 4 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 2620997 = 491437) B491437
theorem B654961 : Blo 271824 654961 := bstep (se 2 (by rfl) ⟨245610, by rfl⟩ : syracuseStep 654961 = 491221) B491221
theorem B294563 : Blo 271824 294563 := bstep (se 1 (by rfl) ⟨220922, by rfl⟩ : syracuseStep 294563 = 441845) B441845
theorem B655075 : Blo 271824 655075 := bstep (se 1 (by rfl) ⟨491306, by rfl⟩ : syracuseStep 655075 = 982613) B982613
theorem B458723 : Blo 271824 458723 := bstep (se 1 (by rfl) ⟨344042, by rfl⟩ : syracuseStep 458723 = 688085) B688085
theorem B458777 : Blo 271824 458777 := bstep (se 2 (by rfl) ⟨172041, by rfl⟩ : syracuseStep 458777 = 344083) B344083
theorem B458905 : Blo 271824 458905 := bstep (se 2 (by rfl) ⟨172089, by rfl⟩ : syracuseStep 458905 = 344179) B344179
theorem B786611 : Blo 271824 786611 := bstep (se 1 (by rfl) ⟨589958, by rfl⟩ : syracuseStep 786611 = 1179917) B1179917
theorem B655577 : Blo 271824 655577 := bstep (se 2 (by rfl) ⟨245841, by rfl⟩ : syracuseStep 655577 = 491683) B491683
theorem B917783 : Blo 271824 917783 := bstep (se 1 (by rfl) ⟨688337, by rfl⟩ : syracuseStep 917783 = 1376675) B1376675
theorem B688459 : Blo 271824 688459 := bstep (se 1 (by rfl) ⟨516344, by rfl⟩ : syracuseStep 688459 = 1032689) B1032689
theorem B688601 : Blo 271824 688601 := bstep (se 2 (by rfl) ⟨258225, by rfl⟩ : syracuseStep 688601 = 516451) B516451
theorem B557579 : Blo 271824 557579 := bstep (se 1 (by rfl) ⟨418184, by rfl⟩ : syracuseStep 557579 = 836369) B836369
theorem B1966609 : Blo 271824 1966609 := bstep (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) B1474957
theorem B1114717 : Blo 271824 1114717 := bstep (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) B418019
theorem B1049219 : Blo 271824 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B8422019 : Blo 271824 8422019 := bstep (se 1 (by rfl) ⟨6316514, by rfl⟩ : syracuseStep 8422019 = 12633029) B12633029
theorem B656075 : Blo 271824 656075 := bstep (se 1 (by rfl) ⟨492056, by rfl⟩ : syracuseStep 656075 = 984113) B984113
theorem B459479 : Blo 271824 459479 := bstep (se 1 (by rfl) ⟨344609, by rfl⟩ : syracuseStep 459479 = 689219) B689219
theorem B918323 : Blo 271824 918323 := bstep (se 1 (by rfl) ⟨688742, by rfl⟩ : syracuseStep 918323 = 1377485) B1377485
theorem B1868609 : Blo 271824 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B459607 : Blo 271824 459607 := bstep (se 1 (by rfl) ⟨344705, by rfl⟩ : syracuseStep 459607 = 689411) B689411
theorem B525145 : Blo 271824 525145 := bstep (se 2 (by rfl) ⟨196929, by rfl⟩ : syracuseStep 525145 = 393859) B393859
theorem B623627 : Blo 271824 623627 := bstep (se 1 (by rfl) ⟨467720, by rfl⟩ : syracuseStep 623627 = 935441) B935441
theorem B918593 : Blo 271824 918593 := bstep (se 2 (by rfl) ⟨344472, by rfl⟩ : syracuseStep 918593 = 688945) B688945
theorem B328855 : Blo 271824 328855 := bstep (se 1 (by rfl) ⟨246641, by rfl⟩ : syracuseStep 328855 = 493283) B493283
theorem B689431 : Blo 271824 689431 := bstep (se 1 (by rfl) ⟨517073, by rfl⟩ : syracuseStep 689431 = 1034147) B1034147
theorem B460235 : Blo 271824 460235 := bstep (se 1 (by rfl) ⟨345176, by rfl⟩ : syracuseStep 460235 = 690353) B690353
theorem B493067 : Blo 271824 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B1377809 : Blo 271824 1377809 := bstep (se 2 (by rfl) ⟨516678, by rfl⟩ : syracuseStep 1377809 = 1033357) B1033357
theorem B2065985 : Blo 271824 2065985 := bstep (se 2 (by rfl) ⟨774744, by rfl⟩ : syracuseStep 2065985 = 1549489) B1549489
theorem B460363 : Blo 271824 460363 := bstep (se 1 (by rfl) ⟨345272, by rfl⟩ : syracuseStep 460363 = 690545) B690545
theorem B919133 : Blo 271824 919133 := bstep (se 3 (by rfl) ⟨172337, by rfl⟩ : syracuseStep 919133 = 344675) B344675
theorem B1377971 : Blo 271824 1377971 := bstep (se 1 (by rfl) ⟨1033478, by rfl⟩ : syracuseStep 1377971 = 2066957) B2066957
theorem B689867 : Blo 271824 689867 := bstep (se 1 (by rfl) ⟨517400, by rfl⟩ : syracuseStep 689867 = 1034801) B1034801
theorem B460505 : Blo 271824 460505 := bstep (se 2 (by rfl) ⟨172689, by rfl⟩ : syracuseStep 460505 = 345379) B345379
theorem B460633 : Blo 271824 460633 := bstep (se 2 (by rfl) ⟨172737, by rfl⟩ : syracuseStep 460633 = 345475) B345475
theorem B690241 : Blo 271824 690241 := bstep (se 2 (by rfl) ⟨258840, by rfl⟩ : syracuseStep 690241 = 517681) B517681
theorem B1312919 : Blo 271824 1312919 := bstep (se 1 (by rfl) ⟨984689, by rfl⟩ : syracuseStep 1312919 = 1969379) B1969379
theorem B3967127 : Blo 271824 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B6850861 : Blo 271824 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B461207 : Blo 271824 461207 := bstep (se 1 (by rfl) ⟨345905, by rfl⟩ : syracuseStep 461207 = 691811) B691811
theorem B1182131 : Blo 271824 1182131 := bstep (se 1 (by rfl) ⟨886598, by rfl⟩ : syracuseStep 1182131 = 1773197) B1773197
theorem B461335 : Blo 271824 461335 := bstep (se 1 (by rfl) ⟨346001, by rfl⟩ : syracuseStep 461335 = 692003) B692003
theorem B4983389 : Blo 271824 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B690839 : Blo 271824 690839 := bstep (se 1 (by rfl) ⟨518129, by rfl⟩ : syracuseStep 690839 = 1036259) B1036259
theorem B920267 : Blo 271824 920267 := bstep (se 1 (by rfl) ⟨690200, by rfl⟩ : syracuseStep 920267 = 1380401) B1380401
theorem B985945 : Blo 271824 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B330647 : Blo 271824 330647 := bstep (se 1 (by rfl) ⟨247985, by rfl⟩ : syracuseStep 330647 = 495971) B495971
theorem B920537 : Blo 271824 920537 := bstep (se 2 (by rfl) ⟨345201, by rfl⟩ : syracuseStep 920537 = 690403) B690403
theorem B461963 : Blo 271824 461963 := bstep (se 1 (by rfl) ⟨346472, by rfl⟩ : syracuseStep 461963 = 692945) B692945
theorem B462091 : Blo 271824 462091 := bstep (se 1 (by rfl) ⟨346568, by rfl⟩ : syracuseStep 462091 = 693137) B693137
theorem B462233 : Blo 271824 462233 := bstep (se 2 (by rfl) ⟨173337, by rfl⟩ : syracuseStep 462233 = 346675) B346675
theorem B691649 : Blo 271824 691649 := bstep (se 2 (by rfl) ⟨259368, by rfl⟩ : syracuseStep 691649 = 518737) B518737
theorem B2067929 : Blo 271824 2067929 := bstep (se 2 (by rfl) ⟨775473, by rfl⟩ : syracuseStep 2067929 = 1550947) B1550947
theorem B3313169 : Blo 271824 3313169 := bstep (se 2 (by rfl) ⟨1242438, by rfl⟩ : syracuseStep 3313169 = 2484877) B2484877
theorem B462361 : Blo 271824 462361 := bstep (se 2 (by rfl) ⟨173385, by rfl⟩ : syracuseStep 462361 = 346771) B346771
theorem B1379915 : Blo 271824 1379915 := bstep (se 1 (by rfl) ⟨1034936, by rfl⟩ : syracuseStep 1379915 = 2069873) B2069873
theorem B1478245 : Blo 271824 1478245 := bstep (se 4 (by rfl) ⟨138585, by rfl⟩ : syracuseStep 1478245 = 277171) B277171
theorem B921239 : Blo 271824 921239 := bstep (se 1 (by rfl) ⟨690929, by rfl⟩ : syracuseStep 921239 = 1381859) B1381859
theorem B692185 : Blo 271824 692185 := bstep (se 2 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 692185 = 519139) B519139
theorem B462935 : Blo 271824 462935 := bstep (se 1 (by rfl) ⟨347201, by rfl⟩ : syracuseStep 462935 = 694403) B694403
theorem B921779 : Blo 271824 921779 := bstep (se 1 (by rfl) ⟨691334, by rfl⟩ : syracuseStep 921779 = 1382669) B1382669
theorem B528563 : Blo 271824 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B987329 : Blo 271824 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B463063 : Blo 271824 463063 := bstep (se 1 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 463063 = 694595) B694595
theorem B2232677 : Blo 271824 2232677 := bstep (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) B418627
theorem B922049 : Blo 271824 922049 := bstep (se 2 (by rfl) ⟨345768, by rfl⟩ : syracuseStep 922049 = 691537) B691537
theorem B463691 : Blo 271824 463691 := bstep (se 1 (by rfl) ⟨347768, by rfl⟩ : syracuseStep 463691 = 695537) B695537
theorem B463819 : Blo 271824 463819 := bstep (se 1 (by rfl) ⟨347864, by rfl⟩ : syracuseStep 463819 = 695729) B695729
theorem B922589 : Blo 271824 922589 := bstep (se 3 (by rfl) ⟨172985, by rfl⟩ : syracuseStep 922589 = 345971) B345971
theorem B693299 : Blo 271824 693299 := bstep (se 1 (by rfl) ⟨519974, by rfl⟩ : syracuseStep 693299 = 1039949) B1039949
theorem B463961 : Blo 271824 463961 := bstep (se 2 (by rfl) ⟨173985, by rfl⟩ : syracuseStep 463961 = 347971) B347971
theorem B2266289 : Blo 271824 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B464089 : Blo 271824 464089 := bstep (se 2 (by rfl) ⟨174033, by rfl⟩ : syracuseStep 464089 = 348067) B348067
theorem B2954501 : Blo 271824 2954501 := bstep (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) B553969
theorem B1381697 : Blo 271824 1381697 := bstep (se 2 (by rfl) ⟨518136, by rfl⟩ : syracuseStep 1381697 = 1036273) B1036273
theorem B693593 : Blo 271824 693593 := bstep (se 2 (by rfl) ⟨260097, by rfl⟩ : syracuseStep 693593 = 520195) B520195
theorem B5051765 : Blo 271824 5051765 := bstep (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) B473603
theorem B464663 : Blo 271824 464663 := bstep (se 1 (by rfl) ⟨348497, by rfl⟩ : syracuseStep 464663 = 696995) B696995
theorem B1480493 : Blo 271824 1480493 := bstep (se 3 (by rfl) ⟨277592, by rfl⟩ : syracuseStep 1480493 = 555185) B555185
theorem B464791 : Blo 271824 464791 := bstep (se 1 (by rfl) ⟨348593, by rfl⟩ : syracuseStep 464791 = 697187) B697187
theorem B923723 : Blo 271824 923723 := bstep (se 1 (by rfl) ⟨692792, by rfl⟩ : syracuseStep 923723 = 1385585) B1385585
theorem B989405 : Blo 271824 989405 := bstep (se 3 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 989405 = 371027) B371027
theorem B923993 : Blo 271824 923993 := bstep (se 2 (by rfl) ⟨346497, by rfl⟩ : syracuseStep 923993 = 692995) B692995
theorem B891329 : Blo 271824 891329 := bstep (se 2 (by rfl) ⟨334248, by rfl⟩ : syracuseStep 891329 = 668497) B668497
theorem B465419 : Blo 271824 465419 := bstep (se 1 (by rfl) ⟨349064, by rfl⟩ : syracuseStep 465419 = 698129) B698129
theorem B2103853 : Blo 271824 2103853 := bstep (se 3 (by rfl) ⟨394472, by rfl⟩ : syracuseStep 2103853 = 788945) B788945
theorem B596531 : Blo 271824 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B1972811 : Blo 271824 1972811 := bstep (se 1 (by rfl) ⟨1479608, by rfl⟩ : syracuseStep 1972811 = 2959217) B2959217
theorem B2071331 : Blo 271824 2071331 := bstep (se 1 (by rfl) ⟨1553498, by rfl⟩ : syracuseStep 2071331 = 3106997) B3106997
theorem B695243 : Blo 271824 695243 := bstep (se 1 (by rfl) ⟨521432, by rfl⟩ : syracuseStep 695243 = 1042865) B1042865
theorem B498649 : Blo 271824 498649 := bstep (se 2 (by rfl) ⟨186993, by rfl⟩ : syracuseStep 498649 = 373987) B373987
theorem B924695 : Blo 271824 924695 := bstep (se 1 (by rfl) ⟨693521, by rfl⟩ : syracuseStep 924695 = 1387043) B1387043
theorem B2333771 : Blo 271824 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B2628683 : Blo 271824 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B1383641 : Blo 271824 1383641 := bstep (se 2 (by rfl) ⟨518865, by rfl⟩ : syracuseStep 1383641 = 1037731) B1037731
theorem B367961 : Blo 271824 367961 := bstep (se 2 (by rfl) ⟨137985, by rfl⟩ : syracuseStep 367961 = 275971) B275971
theorem B3513779 : Blo 271824 3513779 := bstep (se 1 (by rfl) ⟨2635334, by rfl⟩ : syracuseStep 3513779 = 5270669) B5270669
theorem B925235 : Blo 271824 925235 := bstep (se 1 (by rfl) ⟨693926, by rfl⟩ : syracuseStep 925235 = 1387853) B1387853
theorem B1777331 : Blo 271824 1777331 := bstep (se 1 (by rfl) ⟨1332998, by rfl⟩ : syracuseStep 1777331 = 2665997) B2665997
theorem B925505 : Blo 271824 925505 := bstep (se 2 (by rfl) ⟨347064, by rfl⟩ : syracuseStep 925505 = 694129) B694129
theorem B696215 : Blo 271824 696215 := bstep (se 1 (by rfl) ⟨522161, by rfl⟩ : syracuseStep 696215 = 1044323) B1044323
theorem B1548305 : Blo 271824 1548305 := bstep (se 2 (by rfl) ⟨580614, by rfl⟩ : syracuseStep 1548305 = 1161229) B1161229
theorem B1974451 : Blo 271824 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B926045 : Blo 271824 926045 := bstep (se 3 (by rfl) ⟨173633, by rfl⟩ : syracuseStep 926045 = 347267) B347267
theorem B1057175 : Blo 271824 1057175 := bstep (se 1 (by rfl) ⟨792881, by rfl⟩ : syracuseStep 1057175 = 1585763) B1585763
theorem B3350963 : Blo 271824 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B696883 : Blo 271824 696883 := bstep (se 1 (by rfl) ⟨522662, by rfl⟩ : syracuseStep 696883 = 1045325) B1045325
theorem B697025 : Blo 271824 697025 := bstep (se 2 (by rfl) ⟨261384, by rfl⟩ : syracuseStep 697025 = 522769) B522769
theorem B467671 : Blo 271824 467671 := bstep (se 1 (by rfl) ⟨350753, by rfl⟩ : syracuseStep 467671 = 701507) B701507
theorem B1385261 : Blo 271824 1385261 := bstep (se 3 (by rfl) ⟨259736, by rfl⟩ : syracuseStep 1385261 = 519473) B519473
theorem B927179 : Blo 271824 927179 := bstep (se 1 (by rfl) ⟨695384, by rfl⟩ : syracuseStep 927179 = 1390769) B1390769
theorem B271831 : Blo 271824 271831 := bstep (se 1 (by rfl) ⟨203873, by rfl⟩ : syracuseStep 271831 = 407747) B407747
theorem B271851 : Blo 271824 271851 := bstep (se 1 (by rfl) ⟨203888, by rfl⟩ : syracuseStep 271851 = 407777) B407777
theorem B271863 : Blo 271824 271863 := bstep (se 1 (by rfl) ⟨203897, by rfl⟩ : syracuseStep 271863 = 407795) B407795
theorem B271883 : Blo 271824 271883 := bstep (se 1 (by rfl) ⟨203912, by rfl⟩ : syracuseStep 271883 = 407825) B407825
theorem B271895 : Blo 271824 271895 := bstep (se 1 (by rfl) ⟨203921, by rfl⟩ : syracuseStep 271895 = 407843) B407843
theorem B435737 : Blo 271824 435737 := bstep (se 2 (by rfl) ⟨163401, by rfl⟩ : syracuseStep 435737 = 326803) B326803
theorem B271915 : Blo 271824 271915 := bstep (se 1 (by rfl) ⟨203936, by rfl⟩ : syracuseStep 271915 = 407873) B407873
theorem B271927 : Blo 271824 271927 := bstep (se 1 (by rfl) ⟨203945, by rfl⟩ : syracuseStep 271927 = 407891) B407891
theorem B271947 : Blo 271824 271947 := bstep (se 1 (by rfl) ⟨203960, by rfl⟩ : syracuseStep 271947 = 407921) B407921
theorem B271959 : Blo 271824 271959 := bstep (se 1 (by rfl) ⟨203969, by rfl⟩ : syracuseStep 271959 = 407939) B407939
theorem B271979 : Blo 271824 271979 := bstep (se 1 (by rfl) ⟨203984, by rfl⟩ : syracuseStep 271979 = 407969) B407969
theorem B271991 : Blo 271824 271991 := bstep (se 1 (by rfl) ⟨203993, by rfl⟩ : syracuseStep 271991 = 407987) B407987
theorem B272011 : Blo 271824 272011 := bstep (se 1 (by rfl) ⟨204008, by rfl⟩ : syracuseStep 272011 = 408017) B408017
theorem B272023 : Blo 271824 272023 := bstep (se 1 (by rfl) ⟨204017, by rfl⟩ : syracuseStep 272023 = 408035) B408035
theorem B272043 : Blo 271824 272043 := bstep (se 1 (by rfl) ⟨204032, by rfl⟩ : syracuseStep 272043 = 408065) B408065
theorem B272055 : Blo 271824 272055 := bstep (se 1 (by rfl) ⟨204041, by rfl⟩ : syracuseStep 272055 = 408083) B408083
theorem B272075 : Blo 271824 272075 := bstep (se 1 (by rfl) ⟨204056, by rfl⟩ : syracuseStep 272075 = 408113) B408113
theorem B272087 : Blo 271824 272087 := bstep (se 1 (by rfl) ⟨204065, by rfl⟩ : syracuseStep 272087 = 408131) B408131
theorem B927449 : Blo 271824 927449 := bstep (se 2 (by rfl) ⟨347793, by rfl⟩ : syracuseStep 927449 = 695587) B695587
theorem B272107 : Blo 271824 272107 := bstep (se 1 (by rfl) ⟨204080, by rfl⟩ : syracuseStep 272107 = 408161) B408161
theorem B272119 : Blo 271824 272119 := bstep (se 1 (by rfl) ⟨204089, by rfl⟩ : syracuseStep 272119 = 408179) B408179
theorem B272139 : Blo 271824 272139 := bstep (se 1 (by rfl) ⟨204104, by rfl⟩ : syracuseStep 272139 = 408209) B408209
theorem B272151 : Blo 271824 272151 := bstep (se 1 (by rfl) ⟨204113, by rfl⟩ : syracuseStep 272151 = 408227) B408227
theorem B272171 : Blo 271824 272171 := bstep (se 1 (by rfl) ⟨204128, by rfl⟩ : syracuseStep 272171 = 408257) B408257
theorem B272183 : Blo 271824 272183 := bstep (se 1 (by rfl) ⟨204137, by rfl⟩ : syracuseStep 272183 = 408275) B408275
theorem B272203 : Blo 271824 272203 := bstep (se 1 (by rfl) ⟨204152, by rfl⟩ : syracuseStep 272203 = 408305) B408305
theorem B272215 : Blo 271824 272215 := bstep (se 1 (by rfl) ⟨204161, by rfl⟩ : syracuseStep 272215 = 408323) B408323
theorem B632663 : Blo 271824 632663 := bstep (se 1 (by rfl) ⟨474497, by rfl⟩ : syracuseStep 632663 = 948995) B948995
theorem B272235 : Blo 271824 272235 := bstep (se 1 (by rfl) ⟨204176, by rfl⟩ : syracuseStep 272235 = 408353) B408353
theorem B272247 : Blo 271824 272247 := bstep (se 1 (by rfl) ⟨204185, by rfl⟩ : syracuseStep 272247 = 408371) B408371
theorem B272267 : Blo 271824 272267 := bstep (se 1 (by rfl) ⟨204200, by rfl⟩ : syracuseStep 272267 = 408401) B408401
theorem B272279 : Blo 271824 272279 := bstep (se 1 (by rfl) ⟨204209, by rfl⟩ : syracuseStep 272279 = 408419) B408419
theorem B272299 : Blo 271824 272299 := bstep (se 1 (by rfl) ⟨204224, by rfl⟩ : syracuseStep 272299 = 408449) B408449
theorem B272311 : Blo 271824 272311 := bstep (se 1 (by rfl) ⟨204233, by rfl⟩ : syracuseStep 272311 = 408467) B408467
theorem B272331 : Blo 271824 272331 := bstep (se 1 (by rfl) ⟨204248, by rfl⟩ : syracuseStep 272331 = 408497) B408497
theorem B272343 : Blo 271824 272343 := bstep (se 1 (by rfl) ⟨204257, by rfl⟩ : syracuseStep 272343 = 408515) B408515
theorem B272363 : Blo 271824 272363 := bstep (se 1 (by rfl) ⟨204272, by rfl⟩ : syracuseStep 272363 = 408545) B408545
theorem B272375 : Blo 271824 272375 := bstep (se 1 (by rfl) ⟨204281, by rfl⟩ : syracuseStep 272375 = 408563) B408563
theorem B272395 : Blo 271824 272395 := bstep (se 1 (by rfl) ⟨204296, by rfl⟩ : syracuseStep 272395 = 408593) B408593
theorem B272407 : Blo 271824 272407 := bstep (se 1 (by rfl) ⟨204305, by rfl⟩ : syracuseStep 272407 = 408611) B408611
theorem B272427 : Blo 271824 272427 := bstep (se 1 (by rfl) ⟨204320, by rfl⟩ : syracuseStep 272427 = 408641) B408641
theorem B272439 : Blo 271824 272439 := bstep (se 1 (by rfl) ⟨204329, by rfl⟩ : syracuseStep 272439 = 408659) B408659
theorem B272459 : Blo 271824 272459 := bstep (se 1 (by rfl) ⟨204344, by rfl⟩ : syracuseStep 272459 = 408689) B408689
theorem B272471 : Blo 271824 272471 := bstep (se 1 (by rfl) ⟨204353, by rfl⟩ : syracuseStep 272471 = 408707) B408707
theorem B272491 : Blo 271824 272491 := bstep (se 1 (by rfl) ⟨204368, by rfl⟩ : syracuseStep 272491 = 408737) B408737
theorem B272503 : Blo 271824 272503 := bstep (se 1 (by rfl) ⟨204377, by rfl⟩ : syracuseStep 272503 = 408755) B408755
theorem B272523 : Blo 271824 272523 := bstep (se 1 (by rfl) ⟨204392, by rfl⟩ : syracuseStep 272523 = 408785) B408785
theorem B272535 : Blo 271824 272535 := bstep (se 1 (by rfl) ⟨204401, by rfl⟩ : syracuseStep 272535 = 408803) B408803
theorem B469145 : Blo 271824 469145 := bstep (se 2 (by rfl) ⟨175929, by rfl⟩ : syracuseStep 469145 = 351859) B351859
theorem B272555 : Blo 271824 272555 := bstep (se 1 (by rfl) ⟨204416, by rfl⟩ : syracuseStep 272555 = 408833) B408833
theorem B272567 : Blo 271824 272567 := bstep (se 1 (by rfl) ⟨204425, by rfl⟩ : syracuseStep 272567 = 408851) B408851
theorem B272587 : Blo 271824 272587 := bstep (se 1 (by rfl) ⟨204440, by rfl⟩ : syracuseStep 272587 = 408881) B408881
theorem B272599 : Blo 271824 272599 := bstep (se 1 (by rfl) ⟨204449, by rfl⟩ : syracuseStep 272599 = 408899) B408899
theorem B272619 : Blo 271824 272619 := bstep (se 1 (by rfl) ⟨204464, by rfl⟩ : syracuseStep 272619 = 408929) B408929
theorem B272631 : Blo 271824 272631 := bstep (se 1 (by rfl) ⟨204473, by rfl⟩ : syracuseStep 272631 = 408947) B408947
theorem B272651 : Blo 271824 272651 := bstep (se 1 (by rfl) ⟨204488, by rfl⟩ : syracuseStep 272651 = 408977) B408977
theorem B272663 : Blo 271824 272663 := bstep (se 1 (by rfl) ⟨204497, by rfl⟩ : syracuseStep 272663 = 408995) B408995
theorem B272683 : Blo 271824 272683 := bstep (se 1 (by rfl) ⟨204512, by rfl⟩ : syracuseStep 272683 = 409025) B409025
theorem B272695 : Blo 271824 272695 := bstep (se 1 (by rfl) ⟨204521, by rfl⟩ : syracuseStep 272695 = 409043) B409043
theorem B1583425 : Blo 271824 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B272715 : Blo 271824 272715 := bstep (se 1 (by rfl) ⟨204536, by rfl⟩ : syracuseStep 272715 = 409073) B409073
theorem B272727 : Blo 271824 272727 := bstep (se 1 (by rfl) ⟨204545, by rfl⟩ : syracuseStep 272727 = 409091) B409091
theorem B502103 : Blo 271824 502103 := bstep (se 1 (by rfl) ⟨376577, by rfl⟩ : syracuseStep 502103 = 753155) B753155
theorem B272747 : Blo 271824 272747 := bstep (se 1 (by rfl) ⟨204560, by rfl⟩ : syracuseStep 272747 = 409121) B409121
theorem B272759 : Blo 271824 272759 := bstep (se 1 (by rfl) ⟨204569, by rfl⟩ : syracuseStep 272759 = 409139) B409139
theorem B1747331 : Blo 271824 1747331 := bstep (se 1 (by rfl) ⟨1310498, by rfl⟩ : syracuseStep 1747331 = 2620997) B2620997
theorem B272779 : Blo 271824 272779 := bstep (se 1 (by rfl) ⟨204584, by rfl⟩ : syracuseStep 272779 = 409169) B409169
theorem B272791 : Blo 271824 272791 := bstep (se 1 (by rfl) ⟨204593, by rfl⟩ : syracuseStep 272791 = 409187) B409187
theorem B928151 : Blo 271824 928151 := bstep (se 1 (by rfl) ⟨696113, by rfl⟩ : syracuseStep 928151 = 1392227) B1392227
theorem B272811 : Blo 271824 272811 := bstep (se 1 (by rfl) ⟨204608, by rfl⟩ : syracuseStep 272811 = 409217) B409217
theorem B272823 : Blo 271824 272823 := bstep (se 1 (by rfl) ⟨204617, by rfl⟩ : syracuseStep 272823 = 409235) B409235
theorem B272843 : Blo 271824 272843 := bstep (se 1 (by rfl) ⟨204632, by rfl⟩ : syracuseStep 272843 = 409265) B409265
theorem B272855 : Blo 271824 272855 := bstep (se 1 (by rfl) ⟨204641, by rfl⟩ : syracuseStep 272855 = 409283) B409283
theorem B272875 : Blo 271824 272875 := bstep (se 1 (by rfl) ⟨204656, by rfl⟩ : syracuseStep 272875 = 409313) B409313
theorem B272887 : Blo 271824 272887 := bstep (se 1 (by rfl) ⟨204665, by rfl⟩ : syracuseStep 272887 = 409331) B409331
theorem B272907 : Blo 271824 272907 := bstep (se 1 (by rfl) ⟨204680, by rfl⟩ : syracuseStep 272907 = 409361) B409361
theorem B272919 : Blo 271824 272919 := bstep (se 1 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 272919 = 409379) B409379
theorem B272939 : Blo 271824 272939 := bstep (se 1 (by rfl) ⟨204704, by rfl⟩ : syracuseStep 272939 = 409409) B409409
theorem B272951 : Blo 271824 272951 := bstep (se 1 (by rfl) ⟨204713, by rfl⟩ : syracuseStep 272951 = 409427) B409427
theorem B272971 : Blo 271824 272971 := bstep (se 1 (by rfl) ⟨204728, by rfl⟩ : syracuseStep 272971 = 409457) B409457
theorem B272983 : Blo 271824 272983 := bstep (se 1 (by rfl) ⟨204737, by rfl⟩ : syracuseStep 272983 = 409475) B409475
theorem B273003 : Blo 271824 273003 := bstep (se 1 (by rfl) ⟨204752, by rfl⟩ : syracuseStep 273003 = 409505) B409505
theorem B273015 : Blo 271824 273015 := bstep (se 1 (by rfl) ⟨204761, by rfl⟩ : syracuseStep 273015 = 409523) B409523
theorem B273035 : Blo 271824 273035 := bstep (se 1 (by rfl) ⟨204776, by rfl⟩ : syracuseStep 273035 = 409553) B409553
theorem B305815 : Blo 271824 305815 := bstep (se 1 (by rfl) ⟨229361, by rfl⟩ : syracuseStep 305815 = 458723) B458723
theorem B273047 : Blo 271824 273047 := bstep (se 1 (by rfl) ⟨204785, by rfl⟩ : syracuseStep 273047 = 409571) B409571
theorem B273067 : Blo 271824 273067 := bstep (se 1 (by rfl) ⟨204800, by rfl⟩ : syracuseStep 273067 = 409601) B409601
theorem B273079 : Blo 271824 273079 := bstep (se 1 (by rfl) ⟨204809, by rfl⟩ : syracuseStep 273079 = 409619) B409619
theorem B273099 : Blo 271824 273099 := bstep (se 1 (by rfl) ⟨204824, by rfl⟩ : syracuseStep 273099 = 409649) B409649
theorem B273111 : Blo 271824 273111 := bstep (se 1 (by rfl) ⟨204833, by rfl⟩ : syracuseStep 273111 = 409667) B409667
theorem B273131 : Blo 271824 273131 := bstep (se 1 (by rfl) ⟨204848, by rfl⟩ : syracuseStep 273131 = 409697) B409697
theorem B273143 : Blo 271824 273143 := bstep (se 1 (by rfl) ⟨204857, by rfl⟩ : syracuseStep 273143 = 409715) B409715
theorem B273163 : Blo 271824 273163 := bstep (se 1 (by rfl) ⟨204872, by rfl⟩ : syracuseStep 273163 = 409745) B409745
theorem B273175 : Blo 271824 273175 := bstep (se 1 (by rfl) ⟨204881, by rfl⟩ : syracuseStep 273175 = 409763) B409763
theorem B273195 : Blo 271824 273195 := bstep (se 1 (by rfl) ⟨204896, by rfl⟩ : syracuseStep 273195 = 409793) B409793
theorem B273207 : Blo 271824 273207 := bstep (se 1 (by rfl) ⟨204905, by rfl⟩ : syracuseStep 273207 = 409811) B409811
theorem B305995 : Blo 271824 305995 := bstep (se 1 (by rfl) ⟨229496, by rfl⟩ : syracuseStep 305995 = 458993) B458993
theorem B273227 : Blo 271824 273227 := bstep (se 1 (by rfl) ⟨204920, by rfl⟩ : syracuseStep 273227 = 409841) B409841
theorem B273239 : Blo 271824 273239 := bstep (se 1 (by rfl) ⟨204929, by rfl⟩ : syracuseStep 273239 = 409859) B409859
theorem B273259 : Blo 271824 273259 := bstep (se 1 (by rfl) ⟨204944, by rfl⟩ : syracuseStep 273259 = 409889) B409889
theorem B273271 : Blo 271824 273271 := bstep (se 1 (by rfl) ⟨204953, by rfl⟩ : syracuseStep 273271 = 409907) B409907
theorem B273291 : Blo 271824 273291 := bstep (se 1 (by rfl) ⟨204968, by rfl⟩ : syracuseStep 273291 = 409937) B409937
theorem B273303 : Blo 271824 273303 := bstep (se 1 (by rfl) ⟨204977, by rfl⟩ : syracuseStep 273303 = 409955) B409955
theorem B273323 : Blo 271824 273323 := bstep (se 1 (by rfl) ⟨204992, by rfl⟩ : syracuseStep 273323 = 409985) B409985
theorem B928691 : Blo 271824 928691 := bstep (se 1 (by rfl) ⟨696518, by rfl⟩ : syracuseStep 928691 = 1393037) B1393037
theorem B306103 : Blo 271824 306103 := bstep (se 1 (by rfl) ⟨229577, by rfl⟩ : syracuseStep 306103 = 459155) B459155
theorem B273335 : Blo 271824 273335 := bstep (se 1 (by rfl) ⟨205001, by rfl⟩ : syracuseStep 273335 = 410003) B410003
theorem B273355 : Blo 271824 273355 := bstep (se 1 (by rfl) ⟨205016, by rfl⟩ : syracuseStep 273355 = 410033) B410033
theorem B273367 : Blo 271824 273367 := bstep (se 1 (by rfl) ⟨205025, by rfl⟩ : syracuseStep 273367 = 410051) B410051
theorem B273387 : Blo 271824 273387 := bstep (se 1 (by rfl) ⟨205040, by rfl⟩ : syracuseStep 273387 = 410081) B410081
theorem B273399 : Blo 271824 273399 := bstep (se 1 (by rfl) ⟨205049, by rfl⟩ : syracuseStep 273399 = 410099) B410099
theorem B273419 : Blo 271824 273419 := bstep (se 1 (by rfl) ⟨205064, by rfl⟩ : syracuseStep 273419 = 410129) B410129
theorem B1256465 : Blo 271824 1256465 := bstep (se 2 (by rfl) ⟨471174, by rfl⟩ : syracuseStep 1256465 = 942349) B942349
theorem B273431 : Blo 271824 273431 := bstep (se 1 (by rfl) ⟨205073, by rfl⟩ : syracuseStep 273431 = 410147) B410147
theorem B273451 : Blo 271824 273451 := bstep (se 1 (by rfl) ⟨205088, by rfl⟩ : syracuseStep 273451 = 410177) B410177
theorem B273463 : Blo 271824 273463 := bstep (se 1 (by rfl) ⟨205097, by rfl⟩ : syracuseStep 273463 = 410195) B410195
theorem B273483 : Blo 271824 273483 := bstep (se 1 (by rfl) ⟨205112, by rfl⟩ : syracuseStep 273483 = 410225) B410225
theorem B273495 : Blo 271824 273495 := bstep (se 1 (by rfl) ⟨205121, by rfl⟩ : syracuseStep 273495 = 410243) B410243
theorem B306283 : Blo 271824 306283 := bstep (se 1 (by rfl) ⟨229712, by rfl⟩ : syracuseStep 306283 = 459425) B459425
theorem B273515 : Blo 271824 273515 := bstep (se 1 (by rfl) ⟨205136, by rfl⟩ : syracuseStep 273515 = 410273) B410273
theorem B273527 : Blo 271824 273527 := bstep (se 1 (by rfl) ⟨205145, by rfl⟩ : syracuseStep 273527 = 410291) B410291
theorem B273547 : Blo 271824 273547 := bstep (se 1 (by rfl) ⟨205160, by rfl⟩ : syracuseStep 273547 = 410321) B410321
theorem B273559 : Blo 271824 273559 := bstep (se 1 (by rfl) ⟨205169, by rfl⟩ : syracuseStep 273559 = 410339) B410339
theorem B273579 : Blo 271824 273579 := bstep (se 1 (by rfl) ⟨205184, by rfl⟩ : syracuseStep 273579 = 410369) B410369
theorem B273591 : Blo 271824 273591 := bstep (se 1 (by rfl) ⟨205193, by rfl⟩ : syracuseStep 273591 = 410387) B410387
theorem B928961 : Blo 271824 928961 := bstep (se 2 (by rfl) ⟨348360, by rfl⟩ : syracuseStep 928961 = 696721) B696721
theorem B863435 : Blo 271824 863435 := bstep (se 1 (by rfl) ⟨647576, by rfl⟩ : syracuseStep 863435 = 1295153) B1295153
theorem B273611 : Blo 271824 273611 := bstep (se 1 (by rfl) ⟨205208, by rfl⟩ : syracuseStep 273611 = 410417) B410417
theorem B306391 : Blo 271824 306391 := bstep (se 1 (by rfl) ⟨229793, by rfl⟩ : syracuseStep 306391 = 459587) B459587
theorem B273623 : Blo 271824 273623 := bstep (se 1 (by rfl) ⟨205217, by rfl⟩ : syracuseStep 273623 = 410435) B410435
theorem B273643 : Blo 271824 273643 := bstep (se 1 (by rfl) ⟨205232, by rfl⟩ : syracuseStep 273643 = 410465) B410465
theorem B273655 : Blo 271824 273655 := bstep (se 1 (by rfl) ⟨205241, by rfl⟩ : syracuseStep 273655 = 410483) B410483
theorem B273675 : Blo 271824 273675 := bstep (se 1 (by rfl) ⟨205256, by rfl⟩ : syracuseStep 273675 = 410513) B410513
theorem B273687 : Blo 271824 273687 := bstep (se 1 (by rfl) ⟨205265, by rfl⟩ : syracuseStep 273687 = 410531) B410531
theorem B273707 : Blo 271824 273707 := bstep (se 1 (by rfl) ⟨205280, by rfl⟩ : syracuseStep 273707 = 410561) B410561
theorem B273719 : Blo 271824 273719 := bstep (se 1 (by rfl) ⟨205289, by rfl⟩ : syracuseStep 273719 = 410579) B410579
theorem B273739 : Blo 271824 273739 := bstep (se 1 (by rfl) ⟨205304, by rfl⟩ : syracuseStep 273739 = 410609) B410609
theorem B273751 : Blo 271824 273751 := bstep (se 1 (by rfl) ⟨205313, by rfl⟩ : syracuseStep 273751 = 410627) B410627
theorem B273771 : Blo 271824 273771 := bstep (se 1 (by rfl) ⟨205328, by rfl⟩ : syracuseStep 273771 = 410657) B410657
theorem B273783 : Blo 271824 273783 := bstep (se 1 (by rfl) ⟨205337, by rfl⟩ : syracuseStep 273783 = 410675) B410675
theorem B306571 : Blo 271824 306571 := bstep (se 1 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 306571 = 459857) B459857
theorem B273803 : Blo 271824 273803 := bstep (se 1 (by rfl) ⟨205352, by rfl⟩ : syracuseStep 273803 = 410705) B410705
theorem B273815 : Blo 271824 273815 := bstep (se 1 (by rfl) ⟨205361, by rfl⟩ : syracuseStep 273815 = 410723) B410723
theorem B273835 : Blo 271824 273835 := bstep (se 1 (by rfl) ⟨205376, by rfl⟩ : syracuseStep 273835 = 410753) B410753
theorem B273847 : Blo 271824 273847 := bstep (se 1 (by rfl) ⟨205385, by rfl⟩ : syracuseStep 273847 = 410771) B410771
theorem B273867 : Blo 271824 273867 := bstep (se 1 (by rfl) ⟨205400, by rfl⟩ : syracuseStep 273867 = 410801) B410801
theorem B273879 : Blo 271824 273879 := bstep (se 1 (by rfl) ⟨205409, by rfl⟩ : syracuseStep 273879 = 410819) B410819
theorem B273899 : Blo 271824 273899 := bstep (se 1 (by rfl) ⟨205424, by rfl⟩ : syracuseStep 273899 = 410849) B410849
theorem B306679 : Blo 271824 306679 := bstep (se 1 (by rfl) ⟨230009, by rfl⟩ : syracuseStep 306679 = 460019) B460019
theorem B273911 : Blo 271824 273911 := bstep (se 1 (by rfl) ⟨205433, by rfl⟩ : syracuseStep 273911 = 410867) B410867
theorem B273931 : Blo 271824 273931 := bstep (se 1 (by rfl) ⟨205448, by rfl⟩ : syracuseStep 273931 = 410897) B410897
theorem B273943 : Blo 271824 273943 := bstep (se 1 (by rfl) ⟨205457, by rfl⟩ : syracuseStep 273943 = 410915) B410915
theorem B273963 : Blo 271824 273963 := bstep (se 1 (by rfl) ⟨205472, by rfl⟩ : syracuseStep 273963 = 410945) B410945
theorem B273975 : Blo 271824 273975 := bstep (se 1 (by rfl) ⟨205481, by rfl⟩ : syracuseStep 273975 = 410963) B410963
theorem B273995 : Blo 271824 273995 := bstep (se 1 (by rfl) ⟨205496, by rfl⟩ : syracuseStep 273995 = 410993) B410993
theorem B4697675 : Blo 271824 4697675 := bstep (se 1 (by rfl) ⟨3523256, by rfl⟩ : syracuseStep 4697675 = 7046513) B7046513
theorem B274007 : Blo 271824 274007 := bstep (se 1 (by rfl) ⟨205505, by rfl⟩ : syracuseStep 274007 = 411011) B411011
theorem B1257049 : Blo 271824 1257049 := bstep (se 2 (by rfl) ⟨471393, by rfl⟩ : syracuseStep 1257049 = 942787) B942787
theorem B274027 : Blo 271824 274027 := bstep (se 1 (by rfl) ⟨205520, by rfl⟩ : syracuseStep 274027 = 411041) B411041
theorem B274039 : Blo 271824 274039 := bstep (se 1 (by rfl) ⟨205529, by rfl⟩ : syracuseStep 274039 = 411059) B411059
theorem B274059 : Blo 271824 274059 := bstep (se 1 (by rfl) ⟨205544, by rfl⟩ : syracuseStep 274059 = 411089) B411089
theorem B274071 : Blo 271824 274071 := bstep (se 1 (by rfl) ⟨205553, by rfl⟩ : syracuseStep 274071 = 411107) B411107
theorem B306859 : Blo 271824 306859 := bstep (se 1 (by rfl) ⟨230144, by rfl⟩ : syracuseStep 306859 = 460289) B460289
theorem B274091 : Blo 271824 274091 := bstep (se 1 (by rfl) ⟨205568, by rfl⟩ : syracuseStep 274091 = 411137) B411137
theorem B274103 : Blo 271824 274103 := bstep (se 1 (by rfl) ⟨205577, by rfl⟩ : syracuseStep 274103 = 411155) B411155
theorem B274123 : Blo 271824 274123 := bstep (se 1 (by rfl) ⟨205592, by rfl⟩ : syracuseStep 274123 = 411185) B411185
theorem B274135 : Blo 271824 274135 := bstep (se 1 (by rfl) ⟨205601, by rfl⟩ : syracuseStep 274135 = 411203) B411203
theorem B929501 : Blo 271824 929501 := bstep (se 3 (by rfl) ⟨174281, by rfl⟩ : syracuseStep 929501 = 348563) B348563
theorem B274155 : Blo 271824 274155 := bstep (se 1 (by rfl) ⟨205616, by rfl⟩ : syracuseStep 274155 = 411233) B411233
theorem B274167 : Blo 271824 274167 := bstep (se 1 (by rfl) ⟨205625, by rfl⟩ : syracuseStep 274167 = 411251) B411251
theorem B274187 : Blo 271824 274187 := bstep (se 1 (by rfl) ⟨205640, by rfl⟩ : syracuseStep 274187 = 411281) B411281
theorem B306967 : Blo 271824 306967 := bstep (se 1 (by rfl) ⟨230225, by rfl⟩ : syracuseStep 306967 = 460451) B460451
theorem B274199 : Blo 271824 274199 := bstep (se 1 (by rfl) ⟨205649, by rfl⟩ : syracuseStep 274199 = 411299) B411299
theorem B274219 : Blo 271824 274219 := bstep (se 1 (by rfl) ⟨205664, by rfl⟩ : syracuseStep 274219 = 411329) B411329
theorem B1486637 : Blo 271824 1486637 := bstep (se 3 (by rfl) ⟨278744, by rfl⟩ : syracuseStep 1486637 = 557489) B557489
theorem B274231 : Blo 271824 274231 := bstep (se 1 (by rfl) ⟨205673, by rfl⟩ : syracuseStep 274231 = 411347) B411347
theorem B274251 : Blo 271824 274251 := bstep (se 1 (by rfl) ⟨205688, by rfl⟩ : syracuseStep 274251 = 411377) B411377
theorem B274263 : Blo 271824 274263 := bstep (se 1 (by rfl) ⟨205697, by rfl⟩ : syracuseStep 274263 = 411395) B411395
theorem B274283 : Blo 271824 274283 := bstep (se 1 (by rfl) ⟨205712, by rfl⟩ : syracuseStep 274283 = 411425) B411425
theorem B274295 : Blo 271824 274295 := bstep (se 1 (by rfl) ⟨205721, by rfl⟩ : syracuseStep 274295 = 411443) B411443
theorem B274315 : Blo 271824 274315 := bstep (se 1 (by rfl) ⟨205736, by rfl⟩ : syracuseStep 274315 = 411473) B411473
theorem B274327 : Blo 271824 274327 := bstep (se 1 (by rfl) ⟨205745, by rfl⟩ : syracuseStep 274327 = 411491) B411491
theorem B274347 : Blo 271824 274347 := bstep (se 1 (by rfl) ⟨205760, by rfl⟩ : syracuseStep 274347 = 411521) B411521
theorem B274359 : Blo 271824 274359 := bstep (se 1 (by rfl) ⟨205769, by rfl⟩ : syracuseStep 274359 = 411539) B411539
theorem B307147 : Blo 271824 307147 := bstep (se 1 (by rfl) ⟨230360, by rfl⟩ : syracuseStep 307147 = 460721) B460721
theorem B274379 : Blo 271824 274379 := bstep (se 1 (by rfl) ⟨205784, by rfl⟩ : syracuseStep 274379 = 411569) B411569
theorem B274391 : Blo 271824 274391 := bstep (se 1 (by rfl) ⟨205793, by rfl⟩ : syracuseStep 274391 = 411587) B411587
theorem B274411 : Blo 271824 274411 := bstep (se 1 (by rfl) ⟨205808, by rfl⟩ : syracuseStep 274411 = 411617) B411617
theorem B274423 : Blo 271824 274423 := bstep (se 1 (by rfl) ⟨205817, by rfl⟩ : syracuseStep 274423 = 411635) B411635
theorem B2076677 : Blo 271824 2076677 := bstep (se 4 (by rfl) ⟨194688, by rfl⟩ : syracuseStep 2076677 = 389377) B389377
theorem B2109445 : Blo 271824 2109445 := bstep (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) B395521
theorem B274443 : Blo 271824 274443 := bstep (se 1 (by rfl) ⟨205832, by rfl⟩ : syracuseStep 274443 = 411665) B411665
theorem B274455 : Blo 271824 274455 := bstep (se 1 (by rfl) ⟨205841, by rfl⟩ : syracuseStep 274455 = 411683) B411683
theorem B274475 : Blo 271824 274475 := bstep (se 1 (by rfl) ⟨205856, by rfl⟩ : syracuseStep 274475 = 411713) B411713
theorem B307255 : Blo 271824 307255 := bstep (se 1 (by rfl) ⟨230441, by rfl⟩ : syracuseStep 307255 = 460883) B460883
theorem B274487 : Blo 271824 274487 := bstep (se 1 (by rfl) ⟨205865, by rfl⟩ : syracuseStep 274487 = 411731) B411731
theorem B274507 : Blo 271824 274507 := bstep (se 1 (by rfl) ⟨205880, by rfl⟩ : syracuseStep 274507 = 411761) B411761
theorem B274519 : Blo 271824 274519 := bstep (se 1 (by rfl) ⟨205889, by rfl⟩ : syracuseStep 274519 = 411779) B411779
theorem B274539 : Blo 271824 274539 := bstep (se 1 (by rfl) ⟨205904, by rfl⟩ : syracuseStep 274539 = 411809) B411809
theorem B274551 : Blo 271824 274551 := bstep (se 1 (by rfl) ⟨205913, by rfl⟩ : syracuseStep 274551 = 411827) B411827
theorem B274571 : Blo 271824 274571 := bstep (se 1 (by rfl) ⟨205928, by rfl⟩ : syracuseStep 274571 = 411857) B411857
theorem B274583 : Blo 271824 274583 := bstep (se 1 (by rfl) ⟨205937, by rfl⟩ : syracuseStep 274583 = 411875) B411875
theorem B274603 : Blo 271824 274603 := bstep (se 1 (by rfl) ⟨205952, by rfl⟩ : syracuseStep 274603 = 411905) B411905
theorem B274615 : Blo 271824 274615 := bstep (se 1 (by rfl) ⟨205961, by rfl⟩ : syracuseStep 274615 = 411923) B411923
theorem B274635 : Blo 271824 274635 := bstep (se 1 (by rfl) ⟨205976, by rfl⟩ : syracuseStep 274635 = 411953) B411953
theorem B274647 : Blo 271824 274647 := bstep (se 1 (by rfl) ⟨205985, by rfl⟩ : syracuseStep 274647 = 411971) B411971
theorem B307435 : Blo 271824 307435 := bstep (se 1 (by rfl) ⟨230576, by rfl⟩ : syracuseStep 307435 = 461153) B461153
theorem B274667 : Blo 271824 274667 := bstep (se 1 (by rfl) ⟨206000, by rfl⟩ : syracuseStep 274667 = 412001) B412001
theorem B274679 : Blo 271824 274679 := bstep (se 1 (by rfl) ⟨206009, by rfl⟩ : syracuseStep 274679 = 412019) B412019
theorem B274699 : Blo 271824 274699 := bstep (se 1 (by rfl) ⟨206024, by rfl⟩ : syracuseStep 274699 = 412049) B412049
theorem B274711 : Blo 271824 274711 := bstep (se 1 (by rfl) ⟨206033, by rfl⟩ : syracuseStep 274711 = 412067) B412067
theorem B274731 : Blo 271824 274731 := bstep (se 1 (by rfl) ⟨206048, by rfl⟩ : syracuseStep 274731 = 412097) B412097
theorem B274743 : Blo 271824 274743 := bstep (se 1 (by rfl) ⟨206057, by rfl⟩ : syracuseStep 274743 = 412115) B412115
theorem B274763 : Blo 271824 274763 := bstep (se 1 (by rfl) ⟨206072, by rfl⟩ : syracuseStep 274763 = 412145) B412145
theorem B307543 : Blo 271824 307543 := bstep (se 1 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 307543 = 461315) B461315
theorem B274775 : Blo 271824 274775 := bstep (se 1 (by rfl) ⟨206081, by rfl⟩ : syracuseStep 274775 = 412163) B412163
theorem B274795 : Blo 271824 274795 := bstep (se 1 (by rfl) ⟨206096, by rfl⟩ : syracuseStep 274795 = 412193) B412193
theorem B274807 : Blo 271824 274807 := bstep (se 1 (by rfl) ⟨206105, by rfl⟩ : syracuseStep 274807 = 412211) B412211
theorem B274827 : Blo 271824 274827 := bstep (se 1 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 274827 = 412241) B412241
theorem B274839 : Blo 271824 274839 := bstep (se 1 (by rfl) ⟨206129, by rfl⟩ : syracuseStep 274839 = 412259) B412259
theorem B274859 : Blo 271824 274859 := bstep (se 1 (by rfl) ⟨206144, by rfl⟩ : syracuseStep 274859 = 412289) B412289
theorem B274871 : Blo 271824 274871 := bstep (se 1 (by rfl) ⟨206153, by rfl⟩ : syracuseStep 274871 = 412307) B412307
theorem B274891 : Blo 271824 274891 := bstep (se 1 (by rfl) ⟨206168, by rfl⟩ : syracuseStep 274891 = 412337) B412337
theorem B274903 : Blo 271824 274903 := bstep (se 1 (by rfl) ⟨206177, by rfl⟩ : syracuseStep 274903 = 412355) B412355
theorem B274923 : Blo 271824 274923 := bstep (se 1 (by rfl) ⟨206192, by rfl⟩ : syracuseStep 274923 = 412385) B412385
theorem B274935 : Blo 271824 274935 := bstep (se 1 (by rfl) ⟨206201, by rfl⟩ : syracuseStep 274935 = 412403) B412403
theorem B307723 : Blo 271824 307723 := bstep (se 1 (by rfl) ⟨230792, by rfl⟩ : syracuseStep 307723 = 461585) B461585
theorem B274955 : Blo 271824 274955 := bstep (se 1 (by rfl) ⟨206216, by rfl⟩ : syracuseStep 274955 = 412433) B412433
theorem B274967 : Blo 271824 274967 := bstep (se 1 (by rfl) ⟨206225, by rfl⟩ : syracuseStep 274967 = 412451) B412451
theorem B2667043 : Blo 271824 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B274987 : Blo 271824 274987 := bstep (se 1 (by rfl) ⟨206240, by rfl⟩ : syracuseStep 274987 = 412481) B412481
theorem B274999 : Blo 271824 274999 := bstep (se 1 (by rfl) ⟨206249, by rfl⟩ : syracuseStep 274999 = 412499) B412499
theorem B275019 : Blo 271824 275019 := bstep (se 1 (by rfl) ⟨206264, by rfl⟩ : syracuseStep 275019 = 412529) B412529
theorem B275031 : Blo 271824 275031 := bstep (se 1 (by rfl) ⟨206273, by rfl⟩ : syracuseStep 275031 = 412547) B412547
theorem B1389149 : Blo 271824 1389149 := bstep (se 3 (by rfl) ⟨260465, by rfl⟩ : syracuseStep 1389149 = 520931) B520931
theorem B275051 : Blo 271824 275051 := bstep (se 1 (by rfl) ⟨206288, by rfl⟩ : syracuseStep 275051 = 412577) B412577
theorem B307831 : Blo 271824 307831 := bstep (se 1 (by rfl) ⟨230873, by rfl⟩ : syracuseStep 307831 = 461747) B461747
theorem B275063 : Blo 271824 275063 := bstep (se 1 (by rfl) ⟨206297, by rfl⟩ : syracuseStep 275063 = 412595) B412595
theorem B275083 : Blo 271824 275083 := bstep (se 1 (by rfl) ⟨206312, by rfl⟩ : syracuseStep 275083 = 412625) B412625
theorem B275095 : Blo 271824 275095 := bstep (se 1 (by rfl) ⟨206321, by rfl⟩ : syracuseStep 275095 = 412643) B412643
theorem B275115 : Blo 271824 275115 := bstep (se 1 (by rfl) ⟨206336, by rfl⟩ : syracuseStep 275115 = 412673) B412673
theorem B275127 : Blo 271824 275127 := bstep (se 1 (by rfl) ⟨206345, by rfl⟩ : syracuseStep 275127 = 412691) B412691
theorem B275147 : Blo 271824 275147 := bstep (se 1 (by rfl) ⟨206360, by rfl⟩ : syracuseStep 275147 = 412721) B412721
theorem B275159 : Blo 271824 275159 := bstep (se 1 (by rfl) ⟨206369, by rfl⟩ : syracuseStep 275159 = 412739) B412739
theorem B668377 : Blo 271824 668377 := bstep (se 2 (by rfl) ⟨250641, by rfl⟩ : syracuseStep 668377 = 501283) B501283
theorem B275179 : Blo 271824 275179 := bstep (se 1 (by rfl) ⟨206384, by rfl⟩ : syracuseStep 275179 = 412769) B412769
theorem B275191 : Blo 271824 275191 := bstep (se 1 (by rfl) ⟨206393, by rfl⟩ : syracuseStep 275191 = 412787) B412787
theorem B275211 : Blo 271824 275211 := bstep (se 1 (by rfl) ⟨206408, by rfl⟩ : syracuseStep 275211 = 412817) B412817
theorem B275223 : Blo 271824 275223 := bstep (se 1 (by rfl) ⟨206417, by rfl⟩ : syracuseStep 275223 = 412835) B412835
theorem B308011 : Blo 271824 308011 := bstep (se 1 (by rfl) ⟨231008, by rfl⟩ : syracuseStep 308011 = 462017) B462017
theorem B275243 : Blo 271824 275243 := bstep (se 1 (by rfl) ⟨206432, by rfl⟩ : syracuseStep 275243 = 412865) B412865
theorem B275255 : Blo 271824 275255 := bstep (se 1 (by rfl) ⟨206441, by rfl⟩ : syracuseStep 275255 = 412883) B412883
theorem B275275 : Blo 271824 275275 := bstep (se 1 (by rfl) ⟨206456, by rfl⟩ : syracuseStep 275275 = 412913) B412913
theorem B930635 : Blo 271824 930635 := bstep (se 1 (by rfl) ⟨697976, by rfl⟩ : syracuseStep 930635 = 1395953) B1395953
theorem B275287 : Blo 271824 275287 := bstep (se 1 (by rfl) ⟨206465, by rfl⟩ : syracuseStep 275287 = 412931) B412931
theorem B275307 : Blo 271824 275307 := bstep (se 1 (by rfl) ⟨206480, by rfl⟩ : syracuseStep 275307 = 412961) B412961
theorem B275319 : Blo 271824 275319 := bstep (se 1 (by rfl) ⟨206489, by rfl⟩ : syracuseStep 275319 = 412979) B412979
theorem B275339 : Blo 271824 275339 := bstep (se 1 (by rfl) ⟨206504, by rfl⟩ : syracuseStep 275339 = 413009) B413009
theorem B308119 : Blo 271824 308119 := bstep (se 1 (by rfl) ⟨231089, by rfl⟩ : syracuseStep 308119 = 462179) B462179
theorem B275351 : Blo 271824 275351 := bstep (se 1 (by rfl) ⟨206513, by rfl⟩ : syracuseStep 275351 = 413027) B413027
theorem B275371 : Blo 271824 275371 := bstep (se 1 (by rfl) ⟨206528, by rfl⟩ : syracuseStep 275371 = 413057) B413057
theorem B8827825 : Blo 271824 8827825 := bstep (se 2 (by rfl) ⟨3310434, by rfl⟩ : syracuseStep 8827825 = 6620869) B6620869
theorem B275383 : Blo 271824 275383 := bstep (se 1 (by rfl) ⟨206537, by rfl⟩ : syracuseStep 275383 = 413075) B413075
theorem B275403 : Blo 271824 275403 := bstep (se 1 (by rfl) ⟨206552, by rfl⟩ : syracuseStep 275403 = 413105) B413105
theorem B275415 : Blo 271824 275415 := bstep (se 1 (by rfl) ⟨206561, by rfl⟩ : syracuseStep 275415 = 413123) B413123
theorem B275435 : Blo 271824 275435 := bstep (se 1 (by rfl) ⟨206576, by rfl⟩ : syracuseStep 275435 = 413153) B413153
theorem B275447 : Blo 271824 275447 := bstep (se 1 (by rfl) ⟨206585, by rfl⟩ : syracuseStep 275447 = 413171) B413171
theorem B275467 : Blo 271824 275467 := bstep (se 1 (by rfl) ⟨206600, by rfl⟩ : syracuseStep 275467 = 413201) B413201
theorem B275479 : Blo 271824 275479 := bstep (se 1 (by rfl) ⟨206609, by rfl⟩ : syracuseStep 275479 = 413219) B413219
theorem B275499 : Blo 271824 275499 := bstep (se 1 (by rfl) ⟨206624, by rfl⟩ : syracuseStep 275499 = 413249) B413249
theorem B275511 : Blo 271824 275511 := bstep (se 1 (by rfl) ⟨206633, by rfl⟩ : syracuseStep 275511 = 413267) B413267
theorem B308299 : Blo 271824 308299 := bstep (se 1 (by rfl) ⟨231224, by rfl⟩ : syracuseStep 308299 = 462449) B462449
theorem B275531 : Blo 271824 275531 := bstep (se 1 (by rfl) ⟨206648, by rfl⟩ : syracuseStep 275531 = 413297) B413297
theorem B275543 : Blo 271824 275543 := bstep (se 1 (by rfl) ⟨206657, by rfl⟩ : syracuseStep 275543 = 413315) B413315
theorem B930905 : Blo 271824 930905 := bstep (se 2 (by rfl) ⟨349089, by rfl⟩ : syracuseStep 930905 = 698179) B698179
theorem B275563 : Blo 271824 275563 := bstep (se 1 (by rfl) ⟨206672, by rfl⟩ : syracuseStep 275563 = 413345) B413345
theorem B275575 : Blo 271824 275575 := bstep (se 1 (by rfl) ⟨206681, by rfl⟩ : syracuseStep 275575 = 413363) B413363
theorem B275595 : Blo 271824 275595 := bstep (se 1 (by rfl) ⟨206696, by rfl⟩ : syracuseStep 275595 = 413393) B413393
theorem B439447 : Blo 271824 439447 := bstep (se 1 (by rfl) ⟨329585, by rfl⟩ : syracuseStep 439447 = 659171) B659171
theorem B1324183 : Blo 271824 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B275607 : Blo 271824 275607 := bstep (se 1 (by rfl) ⟨206705, by rfl⟩ : syracuseStep 275607 = 413411) B413411
theorem B275627 : Blo 271824 275627 := bstep (se 1 (by rfl) ⟨206720, by rfl⟩ : syracuseStep 275627 = 413441) B413441
theorem B308407 : Blo 271824 308407 := bstep (se 1 (by rfl) ⟨231305, by rfl⟩ : syracuseStep 308407 = 462611) B462611
theorem B275639 : Blo 271824 275639 := bstep (se 1 (by rfl) ⟨206729, by rfl⟩ : syracuseStep 275639 = 413459) B413459
theorem B275659 : Blo 271824 275659 := bstep (se 1 (by rfl) ⟨206744, by rfl⟩ : syracuseStep 275659 = 413489) B413489
theorem B275671 : Blo 271824 275671 := bstep (se 1 (by rfl) ⟨206753, by rfl⟩ : syracuseStep 275671 = 413507) B413507
theorem B275691 : Blo 271824 275691 := bstep (se 1 (by rfl) ⟨206768, by rfl⟩ : syracuseStep 275691 = 413537) B413537
theorem B275703 : Blo 271824 275703 := bstep (se 1 (by rfl) ⟨206777, by rfl⟩ : syracuseStep 275703 = 413555) B413555
theorem B275723 : Blo 271824 275723 := bstep (se 1 (by rfl) ⟨206792, by rfl⟩ : syracuseStep 275723 = 413585) B413585
theorem B1553681 : Blo 271824 1553681 := bstep (se 2 (by rfl) ⟨582630, by rfl⟩ : syracuseStep 1553681 = 1165261) B1165261
theorem B275735 : Blo 271824 275735 := bstep (se 1 (by rfl) ⟨206801, by rfl⟩ : syracuseStep 275735 = 413603) B413603
theorem B275755 : Blo 271824 275755 := bstep (se 1 (by rfl) ⟨206816, by rfl⟩ : syracuseStep 275755 = 413633) B413633
theorem B701747 : Blo 271824 701747 := bstep (se 1 (by rfl) ⟨526310, by rfl⟩ : syracuseStep 701747 = 1052621) B1052621
theorem B275767 : Blo 271824 275767 := bstep (se 1 (by rfl) ⟨206825, by rfl⟩ : syracuseStep 275767 = 413651) B413651
theorem B275787 : Blo 271824 275787 := bstep (se 1 (by rfl) ⟨206840, by rfl⟩ : syracuseStep 275787 = 413681) B413681
theorem B275799 : Blo 271824 275799 := bstep (se 1 (by rfl) ⟨206849, by rfl⟩ : syracuseStep 275799 = 413699) B413699
theorem B308587 : Blo 271824 308587 := bstep (se 1 (by rfl) ⟨231440, by rfl⟩ : syracuseStep 308587 = 462881) B462881
theorem B275819 : Blo 271824 275819 := bstep (se 1 (by rfl) ⟨206864, by rfl⟩ : syracuseStep 275819 = 413729) B413729
theorem B308695 : Blo 271824 308695 := bstep (se 1 (by rfl) ⟨231521, by rfl⟩ : syracuseStep 308695 = 463043) B463043
theorem B439895 : Blo 271824 439895 := bstep (se 1 (by rfl) ⟨329921, by rfl⟩ : syracuseStep 439895 = 659843) B659843
theorem B11417219 : Blo 271824 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B308875 : Blo 271824 308875 := bstep (se 1 (by rfl) ⟨231656, by rfl⟩ : syracuseStep 308875 = 463313) B463313
theorem B1554137 : Blo 271824 1554137 := bstep (se 2 (by rfl) ⟨582801, by rfl⟩ : syracuseStep 1554137 = 1165603) B1165603
theorem B308983 : Blo 271824 308983 := bstep (se 1 (by rfl) ⟨231737, by rfl⟩ : syracuseStep 308983 = 463475) B463475
theorem B440075 : Blo 271824 440075 := bstep (se 1 (by rfl) ⟨330056, by rfl⟩ : syracuseStep 440075 = 660113) B660113
theorem B309163 : Blo 271824 309163 := bstep (se 1 (by rfl) ⟨231872, by rfl⟩ : syracuseStep 309163 = 463745) B463745
theorem B309271 : Blo 271824 309271 := bstep (se 1 (by rfl) ⟨231953, by rfl⟩ : syracuseStep 309271 = 463907) B463907
theorem B440459 : Blo 271824 440459 := bstep (se 1 (by rfl) ⟨330344, by rfl⟩ : syracuseStep 440459 = 660689) B660689
theorem B637067 : Blo 271824 637067 := bstep (se 1 (by rfl) ⟨477800, by rfl⟩ : syracuseStep 637067 = 955601) B955601
theorem B309451 : Blo 271824 309451 := bstep (se 1 (by rfl) ⟨232088, by rfl⟩ : syracuseStep 309451 = 464177) B464177
theorem B407819 : Blo 271824 407819 := bstep (se 1 (by rfl) ⟨305864, by rfl⟩ : syracuseStep 407819 = 611729) B611729
theorem B440587 : Blo 271824 440587 := bstep (se 1 (by rfl) ⟨330440, by rfl⟩ : syracuseStep 440587 = 660881) B660881
theorem B407831 : Blo 271824 407831 := bstep (se 1 (by rfl) ⟨305873, by rfl⟩ : syracuseStep 407831 = 611747) B611747
theorem B309559 : Blo 271824 309559 := bstep (se 1 (by rfl) ⟨232169, by rfl⟩ : syracuseStep 309559 = 464339) B464339
theorem B407897 : Blo 271824 407897 := bstep (se 2 (by rfl) ⟨152961, by rfl⟩ : syracuseStep 407897 = 305923) B305923
theorem B2079107 : Blo 271824 2079107 := bstep (se 1 (by rfl) ⟨1559330, by rfl⟩ : syracuseStep 2079107 = 3118661) B3118661
theorem B1292723 : Blo 271824 1292723 := bstep (se 1 (by rfl) ⟨969542, by rfl⟩ : syracuseStep 1292723 = 1939085) B1939085
theorem B408011 : Blo 271824 408011 := bstep (se 1 (by rfl) ⟨306008, by rfl⟩ : syracuseStep 408011 = 612017) B612017
theorem B408023 : Blo 271824 408023 := bstep (se 1 (by rfl) ⟨306017, by rfl⟩ : syracuseStep 408023 = 612035) B612035
theorem B309739 : Blo 271824 309739 := bstep (se 1 (by rfl) ⟨232304, by rfl⟩ : syracuseStep 309739 = 464609) B464609
theorem B408089 : Blo 271824 408089 := bstep (se 2 (by rfl) ⟨153033, by rfl⟩ : syracuseStep 408089 = 306067) B306067
theorem B932417 : Blo 271824 932417 := bstep (se 2 (by rfl) ⟨349656, by rfl⟩ : syracuseStep 932417 = 699313) B699313
theorem B309847 : Blo 271824 309847 := bstep (se 1 (by rfl) ⟨232385, by rfl⟩ : syracuseStep 309847 = 464771) B464771
theorem B408203 : Blo 271824 408203 := bstep (se 1 (by rfl) ⟨306152, by rfl⟩ : syracuseStep 408203 = 612305) B612305
theorem B408215 : Blo 271824 408215 := bstep (se 1 (by rfl) ⟨306161, by rfl⟩ : syracuseStep 408215 = 612323) B612323
theorem B1391255 : Blo 271824 1391255 := bstep (se 1 (by rfl) ⟨1043441, by rfl⟩ : syracuseStep 1391255 = 2086883) B2086883
theorem B408281 : Blo 271824 408281 := bstep (se 2 (by rfl) ⟨153105, by rfl⟩ : syracuseStep 408281 = 306211) B306211
theorem B310027 : Blo 271824 310027 := bstep (se 1 (by rfl) ⟨232520, by rfl⟩ : syracuseStep 310027 = 465041) B465041
theorem B408395 : Blo 271824 408395 := bstep (se 1 (by rfl) ⟨306296, by rfl⟩ : syracuseStep 408395 = 612593) B612593
theorem B408407 : Blo 271824 408407 := bstep (se 1 (by rfl) ⟨306305, by rfl⟩ : syracuseStep 408407 = 612611) B612611
theorem B310135 : Blo 271824 310135 := bstep (se 1 (by rfl) ⟨232601, by rfl⟩ : syracuseStep 310135 = 465203) B465203
theorem B408473 : Blo 271824 408473 := bstep (se 2 (by rfl) ⟨153177, by rfl⟩ : syracuseStep 408473 = 306355) B306355
theorem B1162187 : Blo 271824 1162187 := bstep (se 1 (by rfl) ⟨871640, by rfl⟩ : syracuseStep 1162187 = 1743281) B1743281
theorem B277463 : Blo 271824 277463 := bstep (se 1 (by rfl) ⟨208097, by rfl⟩ : syracuseStep 277463 = 416195) B416195
theorem B441305 : Blo 271824 441305 := bstep (se 2 (by rfl) ⟨165489, by rfl⟩ : syracuseStep 441305 = 330979) B330979
theorem B408587 : Blo 271824 408587 := bstep (se 1 (by rfl) ⟨306440, by rfl⟩ : syracuseStep 408587 = 612881) B612881
theorem B408599 : Blo 271824 408599 := bstep (se 1 (by rfl) ⟨306449, by rfl⟩ : syracuseStep 408599 = 612899) B612899
theorem B408665 : Blo 271824 408665 := bstep (se 2 (by rfl) ⟨153249, by rfl⟩ : syracuseStep 408665 = 306499) B306499
theorem B441497 : Blo 271824 441497 := bstep (se 2 (by rfl) ⟨165561, by rfl⟩ : syracuseStep 441497 = 331123) B331123
theorem B408779 : Blo 271824 408779 := bstep (se 1 (by rfl) ⟨306584, by rfl⟩ : syracuseStep 408779 = 613169) B613169
theorem B408791 : Blo 271824 408791 := bstep (se 1 (by rfl) ⟨306593, by rfl⟩ : syracuseStep 408791 = 613187) B613187
theorem B408857 : Blo 271824 408857 := bstep (se 2 (by rfl) ⟨153321, by rfl⟩ : syracuseStep 408857 = 306643) B306643
theorem B408971 : Blo 271824 408971 := bstep (se 1 (by rfl) ⟨306728, by rfl⟩ : syracuseStep 408971 = 613457) B613457
theorem B408983 : Blo 271824 408983 := bstep (se 1 (by rfl) ⟨306737, by rfl⟩ : syracuseStep 408983 = 613475) B613475
theorem B671179 : Blo 271824 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B409049 : Blo 271824 409049 := bstep (se 2 (by rfl) ⟨153393, by rfl⟩ : syracuseStep 409049 = 306787) B306787
theorem B3128867 : Blo 271824 3128867 := bstep (se 1 (by rfl) ⟨2346650, by rfl⟩ : syracuseStep 3128867 = 4693301) B4693301
theorem B409163 : Blo 271824 409163 := bstep (se 1 (by rfl) ⟨306872, by rfl⟩ : syracuseStep 409163 = 613745) B613745
theorem B409175 : Blo 271824 409175 := bstep (se 1 (by rfl) ⟨306881, by rfl⟩ : syracuseStep 409175 = 613763) B613763
theorem B409241 : Blo 271824 409241 := bstep (se 2 (by rfl) ⟨153465, by rfl⟩ : syracuseStep 409241 = 306931) B306931
theorem B409355 : Blo 271824 409355 := bstep (se 1 (by rfl) ⟨307016, by rfl⟩ : syracuseStep 409355 = 614033) B614033
theorem B409367 : Blo 271824 409367 := bstep (se 1 (by rfl) ⟨307025, by rfl⟩ : syracuseStep 409367 = 614051) B614051
theorem B409433 : Blo 271824 409433 := bstep (se 2 (by rfl) ⟨153537, by rfl⟩ : syracuseStep 409433 = 307075) B307075
theorem B409547 : Blo 271824 409547 := bstep (se 1 (by rfl) ⟨307160, by rfl⟩ : syracuseStep 409547 = 614321) B614321
theorem B409559 : Blo 271824 409559 := bstep (se 1 (by rfl) ⟨307169, by rfl⟩ : syracuseStep 409559 = 614339) B614339
theorem B409625 : Blo 271824 409625 := bstep (se 2 (by rfl) ⟨153609, by rfl⟩ : syracuseStep 409625 = 307219) B307219
theorem B1589341 : Blo 271824 1589341 := bstep (se 3 (by rfl) ⟨298001, by rfl⟩ : syracuseStep 1589341 = 596003) B596003
theorem B409739 : Blo 271824 409739 := bstep (se 1 (by rfl) ⟨307304, by rfl⟩ : syracuseStep 409739 = 614609) B614609
theorem B409751 : Blo 271824 409751 := bstep (se 1 (by rfl) ⟨307313, by rfl⟩ : syracuseStep 409751 = 614627) B614627
theorem B1032371 : Blo 271824 1032371 := bstep (se 1 (by rfl) ⟨774278, by rfl⟩ : syracuseStep 1032371 = 1548557) B1548557
theorem B1032385 : Blo 271824 1032385 := bstep (se 2 (by rfl) ⟨387144, by rfl⟩ : syracuseStep 1032385 = 774289) B774289
theorem B409817 : Blo 271824 409817 := bstep (se 2 (by rfl) ⟨153681, by rfl⟩ : syracuseStep 409817 = 307363) B307363
theorem B1982755 : Blo 271824 1982755 := bstep (se 1 (by rfl) ⟨1487066, by rfl⟩ : syracuseStep 1982755 = 2974133) B2974133
theorem B409931 : Blo 271824 409931 := bstep (se 1 (by rfl) ⟨307448, by rfl⟩ : syracuseStep 409931 = 614897) B614897
theorem B344407 : Blo 271824 344407 := bstep (se 1 (by rfl) ⟨258305, by rfl⟩ : syracuseStep 344407 = 516611) B516611
theorem B409943 : Blo 271824 409943 := bstep (se 1 (by rfl) ⟨307457, by rfl⟩ : syracuseStep 409943 = 614915) B614915
theorem B835991 : Blo 271824 835991 := bstep (se 1 (by rfl) ⟨626993, by rfl⟩ : syracuseStep 835991 = 1253987) B1253987
theorem B410009 : Blo 271824 410009 := bstep (se 2 (by rfl) ⟨153753, by rfl⟩ : syracuseStep 410009 = 307507) B307507
theorem B410123 : Blo 271824 410123 := bstep (se 1 (by rfl) ⟨307592, by rfl⟩ : syracuseStep 410123 = 615185) B615185
theorem B410135 : Blo 271824 410135 := bstep (se 1 (by rfl) ⟨307601, by rfl⟩ : syracuseStep 410135 = 615203) B615203
theorem B410201 : Blo 271824 410201 := bstep (se 2 (by rfl) ⟨153825, by rfl⟩ : syracuseStep 410201 = 307651) B307651
theorem B1065565 : Blo 271824 1065565 := bstep (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) B399587
theorem B705203 : Blo 271824 705203 := bstep (se 1 (by rfl) ⟨528902, by rfl⟩ : syracuseStep 705203 = 1057805) B1057805
theorem B410315 : Blo 271824 410315 := bstep (se 1 (by rfl) ⟨307736, by rfl⟩ : syracuseStep 410315 = 615473) B615473
theorem B410327 : Blo 271824 410327 := bstep (se 1 (by rfl) ⟨307745, by rfl⟩ : syracuseStep 410327 = 615491) B615491
theorem B410393 : Blo 271824 410393 := bstep (se 2 (by rfl) ⟨153897, by rfl⟩ : syracuseStep 410393 = 307795) B307795
theorem B410507 : Blo 271824 410507 := bstep (se 1 (by rfl) ⟨307880, by rfl⟩ : syracuseStep 410507 = 615761) B615761
theorem B410519 : Blo 271824 410519 := bstep (se 1 (by rfl) ⟨307889, by rfl⟩ : syracuseStep 410519 = 615779) B615779
theorem B410585 : Blo 271824 410585 := bstep (se 2 (by rfl) ⟨153969, by rfl⟩ : syracuseStep 410585 = 307939) B307939
theorem B836573 : Blo 271824 836573 := bstep (se 3 (by rfl) ⟨156857, by rfl⟩ : syracuseStep 836573 = 313715) B313715
theorem B410699 : Blo 271824 410699 := bstep (se 1 (by rfl) ⟨308024, by rfl⟩ : syracuseStep 410699 = 616049) B616049
theorem B410711 : Blo 271824 410711 := bstep (se 1 (by rfl) ⟨308033, by rfl⟩ : syracuseStep 410711 = 616067) B616067
theorem B410777 : Blo 271824 410777 := bstep (se 2 (by rfl) ⟨154041, by rfl⟩ : syracuseStep 410777 = 308083) B308083
theorem B410891 : Blo 271824 410891 := bstep (se 1 (by rfl) ⟨308168, by rfl⟩ : syracuseStep 410891 = 616337) B616337
theorem B410903 : Blo 271824 410903 := bstep (se 1 (by rfl) ⟨308177, by rfl⟩ : syracuseStep 410903 = 616355) B616355
theorem B1361197 : Blo 271824 1361197 := bstep (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) B510449
theorem B410969 : Blo 271824 410969 := bstep (se 2 (by rfl) ⟨154113, by rfl⟩ : syracuseStep 410969 = 308227) B308227
theorem B411083 : Blo 271824 411083 := bstep (se 1 (by rfl) ⟨308312, by rfl⟩ : syracuseStep 411083 = 616625) B616625
theorem B411095 : Blo 271824 411095 := bstep (se 1 (by rfl) ⟨308321, by rfl⟩ : syracuseStep 411095 = 616643) B616643
theorem B1263107 : Blo 271824 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B411161 : Blo 271824 411161 := bstep (se 2 (by rfl) ⟨154185, by rfl⟩ : syracuseStep 411161 = 308371) B308371
theorem B1164851 : Blo 271824 1164851 := bstep (se 1 (by rfl) ⟨873638, by rfl⟩ : syracuseStep 1164851 = 1747277) B1747277
theorem B411275 : Blo 271824 411275 := bstep (se 1 (by rfl) ⟨308456, by rfl⟩ : syracuseStep 411275 = 616913) B616913
theorem B1328791 : Blo 271824 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B411287 : Blo 271824 411287 := bstep (se 1 (by rfl) ⟨308465, by rfl⟩ : syracuseStep 411287 = 616931) B616931
theorem B2082509 : Blo 271824 2082509 := bstep (se 3 (by rfl) ⟨390470, by rfl⟩ : syracuseStep 2082509 = 780941) B780941
theorem B411353 : Blo 271824 411353 := bstep (se 2 (by rfl) ⟨154257, by rfl⟩ : syracuseStep 411353 = 308515) B308515
theorem B411467 : Blo 271824 411467 := bstep (se 1 (by rfl) ⟨308600, by rfl⟩ : syracuseStep 411467 = 617201) B617201
theorem B411479 : Blo 271824 411479 := bstep (se 1 (by rfl) ⟨308609, by rfl⟩ : syracuseStep 411479 = 617219) B617219
theorem B411545 : Blo 271824 411545 := bstep (se 2 (by rfl) ⟨154329, by rfl⟩ : syracuseStep 411545 = 308659) B308659
theorem B346123 : Blo 271824 346123 := bstep (se 1 (by rfl) ⟨259592, by rfl⟩ : syracuseStep 346123 = 519185) B519185
theorem B411659 : Blo 271824 411659 := bstep (se 1 (by rfl) ⟨308744, by rfl⟩ : syracuseStep 411659 = 617489) B617489
theorem B411671 : Blo 271824 411671 := bstep (se 1 (by rfl) ⟨308753, by rfl⟩ : syracuseStep 411671 = 617507) B617507
theorem B1034315 : Blo 271824 1034315 := bstep (se 1 (by rfl) ⟨775736, by rfl⟩ : syracuseStep 1034315 = 1551473) B1551473
theorem B1034329 : Blo 271824 1034329 := bstep (se 2 (by rfl) ⟨387873, by rfl⟩ : syracuseStep 1034329 = 775747) B775747
theorem B411737 : Blo 271824 411737 := bstep (se 2 (by rfl) ⟨154401, by rfl⟩ : syracuseStep 411737 = 308803) B308803
theorem B1394819 : Blo 271824 1394819 := bstep (se 1 (by rfl) ⟨1046114, by rfl⟩ : syracuseStep 1394819 = 2092229) B2092229
theorem B1886339 : Blo 271824 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B2082995 : Blo 271824 2082995 := bstep (se 1 (by rfl) ⟨1562246, by rfl⟩ : syracuseStep 2082995 = 3124493) B3124493
theorem B936139 : Blo 271824 936139 := bstep (se 1 (by rfl) ⟨702104, by rfl⟩ : syracuseStep 936139 = 1404209) B1404209
theorem B411851 : Blo 271824 411851 := bstep (se 1 (by rfl) ⟨308888, by rfl⟩ : syracuseStep 411851 = 617777) B617777
theorem B411863 : Blo 271824 411863 := bstep (se 1 (by rfl) ⟨308897, by rfl⟩ : syracuseStep 411863 = 617795) B617795
theorem B411929 : Blo 271824 411929 := bstep (se 2 (by rfl) ⟨154473, by rfl⟩ : syracuseStep 411929 = 308947) B308947
theorem B412043 : Blo 271824 412043 := bstep (se 1 (by rfl) ⟨309032, by rfl⟩ : syracuseStep 412043 = 618065) B618065
theorem B412055 : Blo 271824 412055 := bstep (se 1 (by rfl) ⟨309041, by rfl⟩ : syracuseStep 412055 = 618083) B618083
theorem B2214323 : Blo 271824 2214323 := bstep (se 1 (by rfl) ⟨1660742, by rfl⟩ : syracuseStep 2214323 = 3321485) B3321485
theorem B412121 : Blo 271824 412121 := bstep (se 2 (by rfl) ⟨154545, by rfl⟩ : syracuseStep 412121 = 309091) B309091
theorem B412235 : Blo 271824 412235 := bstep (se 1 (by rfl) ⟨309176, by rfl⟩ : syracuseStep 412235 = 618353) B618353
theorem B412247 : Blo 271824 412247 := bstep (se 1 (by rfl) ⟨309185, by rfl⟩ : syracuseStep 412247 = 618371) B618371
theorem B3492503 : Blo 271824 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B412313 : Blo 271824 412313 := bstep (se 2 (by rfl) ⟨154617, by rfl⟩ : syracuseStep 412313 = 309235) B309235
theorem B412427 : Blo 271824 412427 := bstep (se 1 (by rfl) ⟨309320, by rfl⟩ : syracuseStep 412427 = 618641) B618641
theorem B412439 : Blo 271824 412439 := bstep (se 1 (by rfl) ⟨309329, by rfl⟩ : syracuseStep 412439 = 618659) B618659
theorem B412505 : Blo 271824 412505 := bstep (se 2 (by rfl) ⟨154689, by rfl⟩ : syracuseStep 412505 = 309379) B309379
theorem B1428317 : Blo 271824 1428317 := bstep (se 3 (by rfl) ⟨267809, by rfl⟩ : syracuseStep 1428317 = 535619) B535619
theorem B412619 : Blo 271824 412619 := bstep (se 1 (by rfl) ⟨309464, by rfl⟩ : syracuseStep 412619 = 618929) B618929
theorem B347095 : Blo 271824 347095 := bstep (se 1 (by rfl) ⟨260321, by rfl⟩ : syracuseStep 347095 = 520643) B520643
theorem B412631 : Blo 271824 412631 := bstep (se 1 (by rfl) ⟨309473, by rfl⟩ : syracuseStep 412631 = 618947) B618947
theorem B1559513 : Blo 271824 1559513 := bstep (se 2 (by rfl) ⟨584817, by rfl⟩ : syracuseStep 1559513 = 1169635) B1169635
theorem B1166339 : Blo 271824 1166339 := bstep (se 1 (by rfl) ⟨874754, by rfl⟩ : syracuseStep 1166339 = 1749509) B1749509
theorem B1035287 : Blo 271824 1035287 := bstep (se 1 (by rfl) ⟨776465, by rfl⟩ : syracuseStep 1035287 = 1552931) B1552931
theorem B412697 : Blo 271824 412697 := bstep (se 2 (by rfl) ⟨154761, by rfl⟩ : syracuseStep 412697 = 309523) B309523
theorem B412811 : Blo 271824 412811 := bstep (se 1 (by rfl) ⟨309608, by rfl⟩ : syracuseStep 412811 = 619217) B619217
theorem B412823 : Blo 271824 412823 := bstep (se 1 (by rfl) ⟨309617, by rfl⟩ : syracuseStep 412823 = 619235) B619235
theorem B412889 : Blo 271824 412889 := bstep (se 2 (by rfl) ⟨154833, by rfl⟩ : syracuseStep 412889 = 309667) B309667
theorem B413003 : Blo 271824 413003 := bstep (se 1 (by rfl) ⟨309752, by rfl⟩ : syracuseStep 413003 = 619505) B619505
theorem B413015 : Blo 271824 413015 := bstep (se 1 (by rfl) ⟨309761, by rfl⟩ : syracuseStep 413015 = 619523) B619523
theorem B413081 : Blo 271824 413081 := bstep (se 2 (by rfl) ⟨154905, by rfl⟩ : syracuseStep 413081 = 309811) B309811
theorem B413195 : Blo 271824 413195 := bstep (se 1 (by rfl) ⟨309896, by rfl⟩ : syracuseStep 413195 = 619793) B619793
theorem B413207 : Blo 271824 413207 := bstep (se 1 (by rfl) ⟨309905, by rfl⟩ : syracuseStep 413207 = 619811) B619811
theorem B3001931 : Blo 271824 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B413273 : Blo 271824 413273 := bstep (se 2 (by rfl) ⟨154977, by rfl⟩ : syracuseStep 413273 = 309955) B309955
theorem B2084453 : Blo 271824 2084453 := bstep (se 4 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 2084453 = 390835) B390835
theorem B413387 : Blo 271824 413387 := bstep (se 1 (by rfl) ⟨310040, by rfl⟩ : syracuseStep 413387 = 620081) B620081
theorem B413399 : Blo 271824 413399 := bstep (se 1 (by rfl) ⟨310049, by rfl⟩ : syracuseStep 413399 = 620099) B620099
theorem B872153 : Blo 271824 872153 := bstep (se 2 (by rfl) ⟨327057, by rfl⟩ : syracuseStep 872153 = 654115) B654115
theorem B347915 : Blo 271824 347915 := bstep (se 1 (by rfl) ⟨260936, by rfl⟩ : syracuseStep 347915 = 521873) B521873
theorem B413465 : Blo 271824 413465 := bstep (se 2 (by rfl) ⟨155049, by rfl⟩ : syracuseStep 413465 = 310099) B310099
theorem B413579 : Blo 271824 413579 := bstep (se 1 (by rfl) ⟨310184, by rfl⟩ : syracuseStep 413579 = 620369) B620369
theorem B413591 : Blo 271824 413591 := bstep (se 1 (by rfl) ⟨310193, by rfl⟩ : syracuseStep 413591 = 620387) B620387
theorem B413657 : Blo 271824 413657 := bstep (se 2 (by rfl) ⟨155121, by rfl⟩ : syracuseStep 413657 = 310243) B310243
theorem B2084939 : Blo 271824 2084939 := bstep (se 1 (by rfl) ⟨1563704, by rfl⟩ : syracuseStep 2084939 = 3127409) B3127409
theorem B1036547 : Blo 271824 1036547 := bstep (se 1 (by rfl) ⟨777410, by rfl⟩ : syracuseStep 1036547 = 1554821) B1554821
theorem B348619 : Blo 271824 348619 := bstep (se 1 (by rfl) ⟨261464, by rfl⟩ : syracuseStep 348619 = 522929) B522929
theorem B1561153 : Blo 271824 1561153 := bstep (se 2 (by rfl) ⟨585432, by rfl⟩ : syracuseStep 1561153 = 1170865) B1170865
theorem B1659523 : Blo 271824 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B840385 : Blo 271824 840385 := bstep (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) B630289
theorem B774859 : Blo 271824 774859 := bstep (se 1 (by rfl) ⟨581144, by rfl⟩ : syracuseStep 774859 = 1162289) B1162289
theorem B348887 : Blo 271824 348887 := bstep (se 1 (by rfl) ⟨261665, by rfl⟩ : syracuseStep 348887 = 523331) B523331
theorem B873281 : Blo 271824 873281 := bstep (se 2 (by rfl) ⟨327480, by rfl⟩ : syracuseStep 873281 = 654961) B654961
theorem B3756917 : Blo 271824 3756917 := bstep (se 5 (by rfl) ⟨176105, by rfl⟩ : syracuseStep 3756917 = 352211) B352211
theorem B938945 : Blo 271824 938945 := bstep (se 2 (by rfl) ⟨352104, by rfl⟩ : syracuseStep 938945 = 704209) B704209
theorem B873433 : Blo 271824 873433 := bstep (se 2 (by rfl) ⟨327537, by rfl⟩ : syracuseStep 873433 = 655075) B655075
theorem B775133 : Blo 271824 775133 := bstep (se 3 (by rfl) ⟨145337, by rfl⟩ : syracuseStep 775133 = 290675) B290675
theorem B1168577 : Blo 271824 1168577 := bstep (se 2 (by rfl) ⟨438216, by rfl⟩ : syracuseStep 1168577 = 876433) B876433
theorem B5002501 : Blo 271824 5002501 := bstep (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) B937969
theorem B611801 : Blo 271824 611801 := bstep (se 2 (by rfl) ⟨229425, by rfl⟩ : syracuseStep 611801 = 458851) B458851
theorem B611891 : Blo 271824 611891 := bstep (se 1 (by rfl) ⟨458918, by rfl⟩ : syracuseStep 611891 = 917837) B917837
theorem B611927 : Blo 271824 611927 := bstep (se 1 (by rfl) ⟨458945, by rfl⟩ : syracuseStep 611927 = 917891) B917891
theorem B612107 : Blo 271824 612107 := bstep (se 1 (by rfl) ⟨459080, by rfl⟩ : syracuseStep 612107 = 918161) B918161
theorem B415513 : Blo 271824 415513 := bstep (se 2 (by rfl) ⟨155817, by rfl⟩ : syracuseStep 415513 = 311635) B311635
theorem B612161 : Blo 271824 612161 := bstep (se 2 (by rfl) ⟨229560, by rfl⟩ : syracuseStep 612161 = 459121) B459121
theorem B612377 : Blo 271824 612377 := bstep (se 2 (by rfl) ⟨229641, by rfl⟩ : syracuseStep 612377 = 459283) B459283
theorem B612467 : Blo 271824 612467 := bstep (se 1 (by rfl) ⟨459350, by rfl⟩ : syracuseStep 612467 = 918701) B918701
theorem B12572813 : Blo 271824 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B612503 : Blo 271824 612503 := bstep (se 1 (by rfl) ⟨459377, by rfl⟩ : syracuseStep 612503 = 918755) B918755
theorem B4446413 : Blo 271824 4446413 := bstep (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) B1667405
theorem B2644289 : Blo 271824 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B612683 : Blo 271824 612683 := bstep (se 1 (by rfl) ⟨459512, by rfl⟩ : syracuseStep 612683 = 919025) B919025
theorem B612737 : Blo 271824 612737 := bstep (se 2 (by rfl) ⟨229776, by rfl⟩ : syracuseStep 612737 = 459553) B459553
theorem B612953 : Blo 271824 612953 := bstep (se 2 (by rfl) ⟨229857, by rfl⟩ : syracuseStep 612953 = 459715) B459715
theorem B613043 : Blo 271824 613043 := bstep (se 1 (by rfl) ⟨459782, by rfl⟩ : syracuseStep 613043 = 919565) B919565
theorem B613079 : Blo 271824 613079 := bstep (se 1 (by rfl) ⟨459809, by rfl⟩ : syracuseStep 613079 = 919619) B919619
theorem B1170251 : Blo 271824 1170251 := bstep (se 1 (by rfl) ⟨877688, by rfl⟩ : syracuseStep 1170251 = 1755377) B1755377
theorem B613259 : Blo 271824 613259 := bstep (se 1 (by rfl) ⟨459944, by rfl⟩ : syracuseStep 613259 = 919889) B919889
theorem B613313 : Blo 271824 613313 := bstep (se 2 (by rfl) ⟨229992, by rfl⟩ : syracuseStep 613313 = 459985) B459985
theorem B1104857 : Blo 271824 1104857 := bstep (se 2 (by rfl) ⟨414321, by rfl⟩ : syracuseStep 1104857 = 828643) B828643
theorem B613529 : Blo 271824 613529 := bstep (se 2 (by rfl) ⟨230073, by rfl⟩ : syracuseStep 613529 = 460147) B460147
theorem B777433 : Blo 271824 777433 := bstep (se 2 (by rfl) ⟨291537, by rfl⟩ : syracuseStep 777433 = 583075) B583075
theorem B613619 : Blo 271824 613619 := bstep (se 1 (by rfl) ⟨460214, by rfl⟩ : syracuseStep 613619 = 920429) B920429
theorem B613655 : Blo 271824 613655 := bstep (se 1 (by rfl) ⟨460241, by rfl⟩ : syracuseStep 613655 = 920483) B920483
theorem B1039661 : Blo 271824 1039661 := bstep (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) B389873
theorem B613835 : Blo 271824 613835 := bstep (se 1 (by rfl) ⟨460376, by rfl⟩ : syracuseStep 613835 = 920753) B920753
theorem B613889 : Blo 271824 613889 := bstep (se 2 (by rfl) ⟨230208, by rfl⟩ : syracuseStep 613889 = 460417) B460417
theorem B1171037 : Blo 271824 1171037 := bstep (se 3 (by rfl) ⟨219569, by rfl⟩ : syracuseStep 1171037 = 439139) B439139
theorem B614105 : Blo 271824 614105 := bstep (se 2 (by rfl) ⟨230289, by rfl⟩ : syracuseStep 614105 = 460579) B460579
theorem B876253 : Blo 271824 876253 := bstep (se 3 (by rfl) ⟨164297, by rfl⟩ : syracuseStep 876253 = 328595) B328595
theorem B614195 : Blo 271824 614195 := bstep (se 1 (by rfl) ⟨460646, by rfl⟩ : syracuseStep 614195 = 921293) B921293
theorem B778049 : Blo 271824 778049 := bstep (se 2 (by rfl) ⟨291768, by rfl⟩ : syracuseStep 778049 = 583537) B583537
theorem B614231 : Blo 271824 614231 := bstep (se 1 (by rfl) ⟨460673, by rfl⟩ : syracuseStep 614231 = 921347) B921347
theorem B581555 : Blo 271824 581555 := bstep (se 1 (by rfl) ⟨436166, by rfl⟩ : syracuseStep 581555 = 872333) B872333
theorem B3563443 : Blo 271824 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B1564595 : Blo 271824 1564595 := bstep (se 1 (by rfl) ⟨1173446, by rfl⟩ : syracuseStep 1564595 = 2346893) B2346893
theorem B876509 : Blo 271824 876509 := bstep (se 3 (by rfl) ⟨164345, by rfl⟩ : syracuseStep 876509 = 328691) B328691
theorem B614411 : Blo 271824 614411 := bstep (se 1 (by rfl) ⟨460808, by rfl⟩ : syracuseStep 614411 = 921617) B921617
theorem B1040435 : Blo 271824 1040435 := bstep (se 1 (by rfl) ⟨780326, by rfl⟩ : syracuseStep 1040435 = 1560653) B1560653
theorem B942131 : Blo 271824 942131 := bstep (se 1 (by rfl) ⟨706598, by rfl⟩ : syracuseStep 942131 = 1413197) B1413197
theorem B614465 : Blo 271824 614465 := bstep (se 2 (by rfl) ⟨230424, by rfl⟩ : syracuseStep 614465 = 460849) B460849
theorem B614681 : Blo 271824 614681 := bstep (se 2 (by rfl) ⟨230505, by rfl⟩ : syracuseStep 614681 = 461011) B461011
theorem B614771 : Blo 271824 614771 := bstep (se 1 (by rfl) ⟨461078, by rfl⟩ : syracuseStep 614771 = 922157) B922157
theorem B614807 : Blo 271824 614807 := bstep (se 1 (by rfl) ⟨461105, by rfl⟩ : syracuseStep 614807 = 922211) B922211
theorem B614987 : Blo 271824 614987 := bstep (se 1 (by rfl) ⟨461240, by rfl⟩ : syracuseStep 614987 = 922481) B922481
theorem B615041 : Blo 271824 615041 := bstep (se 2 (by rfl) ⟨230640, by rfl⟩ : syracuseStep 615041 = 461281) B461281
theorem B615257 : Blo 271824 615257 := bstep (se 2 (by rfl) ⟨230721, by rfl⟩ : syracuseStep 615257 = 461443) B461443
theorem B1172369 : Blo 271824 1172369 := bstep (se 2 (by rfl) ⟨439638, by rfl⟩ : syracuseStep 1172369 = 879277) B879277
theorem B517043 : Blo 271824 517043 := bstep (se 1 (by rfl) ⟨387782, by rfl⟩ : syracuseStep 517043 = 775565) B775565
theorem B615347 : Blo 271824 615347 := bstep (se 1 (by rfl) ⟨461510, by rfl⟩ : syracuseStep 615347 = 923021) B923021
theorem B615383 : Blo 271824 615383 := bstep (se 1 (by rfl) ⟨461537, by rfl⟩ : syracuseStep 615383 = 923075) B923075
theorem B517195 : Blo 271824 517195 := bstep (se 1 (by rfl) ⟨387896, by rfl⟩ : syracuseStep 517195 = 775793) B775793
theorem B3531869 : Blo 271824 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B582785 : Blo 271824 582785 := bstep (se 2 (by rfl) ⟨218544, by rfl⟩ : syracuseStep 582785 = 437089) B437089
theorem B615563 : Blo 271824 615563 := bstep (se 1 (by rfl) ⟨461672, by rfl⟩ : syracuseStep 615563 = 923345) B923345
theorem B615617 : Blo 271824 615617 := bstep (se 2 (by rfl) ⟨230856, by rfl⟩ : syracuseStep 615617 = 461713) B461713
theorem B2090285 : Blo 271824 2090285 := bstep (se 3 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 2090285 = 783857) B783857
theorem B1566053 : Blo 271824 1566053 := bstep (se 4 (by rfl) ⟨146817, by rfl⟩ : syracuseStep 1566053 = 293635) B293635
theorem B517529 : Blo 271824 517529 := bstep (se 2 (by rfl) ⟨194073, by rfl⟩ : syracuseStep 517529 = 388147) B388147
theorem B615833 : Blo 271824 615833 := bstep (se 2 (by rfl) ⟨230937, by rfl⟩ : syracuseStep 615833 = 461875) B461875
theorem B615923 : Blo 271824 615923 := bstep (se 1 (by rfl) ⟨461942, by rfl⟩ : syracuseStep 615923 = 923885) B923885
theorem B1041923 : Blo 271824 1041923 := bstep (se 1 (by rfl) ⟨781442, by rfl⟩ : syracuseStep 1041923 = 1562885) B1562885
theorem B615959 : Blo 271824 615959 := bstep (se 1 (by rfl) ⟨461969, by rfl⟩ : syracuseStep 615959 = 923939) B923939
theorem B1893989 : Blo 271824 1893989 := bstep (se 4 (by rfl) ⟨177561, by rfl⟩ : syracuseStep 1893989 = 355123) B355123
theorem B1861271 : Blo 271824 1861271 := bstep (se 1 (by rfl) ⟨1395953, by rfl⟩ : syracuseStep 1861271 = 2791907) B2791907
theorem B616139 : Blo 271824 616139 := bstep (se 1 (by rfl) ⟨462104, by rfl⟩ : syracuseStep 616139 = 924209) B924209
theorem B616193 : Blo 271824 616193 := bstep (se 2 (by rfl) ⟨231072, by rfl⟩ : syracuseStep 616193 = 462145) B462145
theorem B1763117 : Blo 271824 1763117 := bstep (se 3 (by rfl) ⟨330584, by rfl⟩ : syracuseStep 1763117 = 661169) B661169
theorem B780121 : Blo 271824 780121 := bstep (se 2 (by rfl) ⟨292545, by rfl⟩ : syracuseStep 780121 = 585091) B585091
theorem B1042379 : Blo 271824 1042379 := bstep (se 1 (by rfl) ⟨781784, by rfl⟩ : syracuseStep 1042379 = 1563569) B1563569
theorem B616409 : Blo 271824 616409 := bstep (se 2 (by rfl) ⟨231153, by rfl⟩ : syracuseStep 616409 = 462307) B462307
theorem B518167 : Blo 271824 518167 := bstep (se 1 (by rfl) ⟨388625, by rfl⟩ : syracuseStep 518167 = 777251) B777251
theorem B616499 : Blo 271824 616499 := bstep (se 1 (by rfl) ⟨462374, by rfl⟩ : syracuseStep 616499 = 924749) B924749
theorem B616535 : Blo 271824 616535 := bstep (se 1 (by rfl) ⟨462401, by rfl⟩ : syracuseStep 616535 = 924803) B924803
theorem B1173635 : Blo 271824 1173635 := bstep (se 1 (by rfl) ⟨880226, by rfl⟩ : syracuseStep 1173635 = 1760453) B1760453
theorem B1042577 : Blo 271824 1042577 := bstep (se 2 (by rfl) ⟨390966, by rfl⟩ : syracuseStep 1042577 = 781933) B781933
theorem B583895 : Blo 271824 583895 := bstep (se 1 (by rfl) ⟨437921, by rfl⟩ : syracuseStep 583895 = 875843) B875843
theorem B780509 : Blo 271824 780509 := bstep (se 3 (by rfl) ⟨146345, by rfl⟩ : syracuseStep 780509 = 292691) B292691
theorem B3500293 : Blo 271824 3500293 := bstep (se 4 (by rfl) ⟨328152, by rfl⟩ : syracuseStep 3500293 = 656305) B656305
theorem B616715 : Blo 271824 616715 := bstep (se 1 (by rfl) ⟨462536, by rfl⟩ : syracuseStep 616715 = 925073) B925073
theorem B616769 : Blo 271824 616769 := bstep (se 2 (by rfl) ⟨231288, by rfl⟩ : syracuseStep 616769 = 462577) B462577
theorem B387595 : Blo 271824 387595 := bstep (se 1 (by rfl) ⟨290696, by rfl⟩ : syracuseStep 387595 = 581393) B581393
theorem B616985 : Blo 271824 616985 := bstep (se 2 (by rfl) ⟨231369, by rfl⟩ : syracuseStep 616985 = 462739) B462739
theorem B617075 : Blo 271824 617075 := bstep (se 1 (by rfl) ⟨462806, by rfl⟩ : syracuseStep 617075 = 925613) B925613
theorem B617111 : Blo 271824 617111 := bstep (se 1 (by rfl) ⟨462833, by rfl⟩ : syracuseStep 617111 = 925667) B925667
theorem B715481 : Blo 271824 715481 := bstep (se 2 (by rfl) ⟨268305, by rfl⟩ : syracuseStep 715481 = 536611) B536611
theorem B518987 : Blo 271824 518987 := bstep (se 1 (by rfl) ⟨389240, by rfl⟩ : syracuseStep 518987 = 778481) B778481
theorem B617291 : Blo 271824 617291 := bstep (se 1 (by rfl) ⟨462968, by rfl⟩ : syracuseStep 617291 = 925937) B925937
theorem B519041 : Blo 271824 519041 := bstep (se 2 (by rfl) ⟨194640, by rfl⟩ : syracuseStep 519041 = 389281) B389281
theorem B617345 : Blo 271824 617345 := bstep (se 2 (by rfl) ⟨231504, by rfl⟩ : syracuseStep 617345 = 463009) B463009
theorem B1043351 : Blo 271824 1043351 := bstep (se 1 (by rfl) ⟨782513, by rfl⟩ : syracuseStep 1043351 = 1565027) B1565027
theorem B3140531 : Blo 271824 3140531 := bstep (se 1 (by rfl) ⟨2355398, by rfl⟩ : syracuseStep 3140531 = 4710797) B4710797
theorem B617561 : Blo 271824 617561 := bstep (se 2 (by rfl) ⟨231585, by rfl⟩ : syracuseStep 617561 = 463171) B463171
theorem B1043549 : Blo 271824 1043549 := bstep (se 3 (by rfl) ⟨195665, by rfl⟩ : syracuseStep 1043549 = 391331) B391331
theorem B617651 : Blo 271824 617651 := bstep (se 1 (by rfl) ⟨463238, by rfl⟩ : syracuseStep 617651 = 926477) B926477
theorem B617687 : Blo 271824 617687 := bstep (se 1 (by rfl) ⟨463265, by rfl⟩ : syracuseStep 617687 = 926531) B926531
theorem B584921 : Blo 271824 584921 := bstep (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) B438691
theorem B1240337 : Blo 271824 1240337 := bstep (se 2 (by rfl) ⟨465126, by rfl⟩ : syracuseStep 1240337 = 930253) B930253
theorem B617867 : Blo 271824 617867 := bstep (se 1 (by rfl) ⟨463400, by rfl⟩ : syracuseStep 617867 = 926801) B926801
theorem B617921 : Blo 271824 617921 := bstep (se 2 (by rfl) ⟨231720, by rfl⟩ : syracuseStep 617921 = 463441) B463441
theorem B4419107 : Blo 271824 4419107 := bstep (se 1 (by rfl) ⟨3314330, by rfl⟩ : syracuseStep 4419107 = 6628661) B6628661
theorem B290423 : Blo 271824 290423 := bstep (se 1 (by rfl) ⟨217817, by rfl⟩ : syracuseStep 290423 = 435635) B435635
theorem B618137 : Blo 271824 618137 := bstep (se 2 (by rfl) ⟨231801, by rfl⟩ : syracuseStep 618137 = 463603) B463603
theorem B618227 : Blo 271824 618227 := bstep (se 1 (by rfl) ⟨463670, by rfl⟩ : syracuseStep 618227 = 927341) B927341
theorem B454411 : Blo 271824 454411 := bstep (se 1 (by rfl) ⟨340808, by rfl⟩ : syracuseStep 454411 = 681617) B681617
theorem B519959 : Blo 271824 519959 := bstep (se 1 (by rfl) ⟨389969, by rfl⟩ : syracuseStep 519959 = 779939) B779939
theorem B618263 : Blo 271824 618263 := bstep (se 1 (by rfl) ⟨463697, by rfl⟩ : syracuseStep 618263 = 927395) B927395
theorem B618443 : Blo 271824 618443 := bstep (se 1 (by rfl) ⟨463832, by rfl⟩ : syracuseStep 618443 = 927665) B927665
theorem B389081 : Blo 271824 389081 := bstep (se 2 (by rfl) ⟨145905, by rfl⟩ : syracuseStep 389081 = 291811) B291811
theorem B618497 : Blo 271824 618497 := bstep (se 2 (by rfl) ⟨231936, by rfl⟩ : syracuseStep 618497 = 463873) B463873
theorem B8876213 : Blo 271824 8876213 := bstep (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) B832145
theorem B618713 : Blo 271824 618713 := bstep (se 2 (by rfl) ⟨232017, by rfl⟩ : syracuseStep 618713 = 464035) B464035
theorem B520499 : Blo 271824 520499 := bstep (se 1 (by rfl) ⟨390374, by rfl⟩ : syracuseStep 520499 = 780749) B780749
theorem B618803 : Blo 271824 618803 := bstep (se 1 (by rfl) ⟨464102, by rfl⟩ : syracuseStep 618803 = 928205) B928205
theorem B618839 : Blo 271824 618839 := bstep (se 1 (by rfl) ⟨464129, by rfl⟩ : syracuseStep 618839 = 928259) B928259
theorem B422411 : Blo 271824 422411 := bstep (se 1 (by rfl) ⟨316808, by rfl⟩ : syracuseStep 422411 = 633617) B633617
theorem B619019 : Blo 271824 619019 := bstep (se 1 (by rfl) ⟨464264, by rfl⟩ : syracuseStep 619019 = 928529) B928529
theorem B619073 : Blo 271824 619073 := bstep (se 2 (by rfl) ⟨232152, by rfl⟩ : syracuseStep 619073 = 464305) B464305
theorem B389719 : Blo 271824 389719 := bstep (se 1 (by rfl) ⟨292289, by rfl⟩ : syracuseStep 389719 = 584579) B584579
theorem B3994373 : Blo 271824 3994373 := bstep (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) B748945
theorem B520985 : Blo 271824 520985 := bstep (se 2 (by rfl) ⟨195369, by rfl⟩ : syracuseStep 520985 = 390739) B390739
theorem B619289 : Blo 271824 619289 := bstep (se 2 (by rfl) ⟨232233, by rfl⟩ : syracuseStep 619289 = 464467) B464467
theorem B586561 : Blo 271824 586561 := bstep (se 2 (by rfl) ⟨219960, by rfl⟩ : syracuseStep 586561 = 439921) B439921
theorem B5370725 : Blo 271824 5370725 := bstep (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) B1007011
theorem B619379 : Blo 271824 619379 := bstep (se 1 (by rfl) ⟨464534, by rfl⟩ : syracuseStep 619379 = 929069) B929069
theorem B619415 : Blo 271824 619415 := bstep (se 1 (by rfl) ⟨464561, by rfl⟩ : syracuseStep 619415 = 929123) B929123
theorem B1045507 : Blo 271824 1045507 := bstep (se 1 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 1045507 = 1568261) B1568261
theorem B783425 : Blo 271824 783425 := bstep (se 2 (by rfl) ⟨293784, by rfl⟩ : syracuseStep 783425 = 587569) B587569
theorem B816193 : Blo 271824 816193 := bstep (se 2 (by rfl) ⟨306072, by rfl⟩ : syracuseStep 816193 = 612145) B612145
theorem B2356289 : Blo 271824 2356289 := bstep (se 2 (by rfl) ⟨883608, by rfl⟩ : syracuseStep 2356289 = 1767217) B1767217
theorem B619595 : Blo 271824 619595 := bstep (se 1 (by rfl) ⟨464696, by rfl⟩ : syracuseStep 619595 = 929393) B929393
theorem B2094173 : Blo 271824 2094173 := bstep (se 3 (by rfl) ⟨392657, by rfl⟩ : syracuseStep 2094173 = 785315) B785315
theorem B619649 : Blo 271824 619649 := bstep (se 2 (by rfl) ⟨232368, by rfl⟩ : syracuseStep 619649 = 464737) B464737
theorem B1176727 : Blo 271824 1176727 := bstep (se 1 (by rfl) ⟨882545, by rfl⟩ : syracuseStep 1176727 = 1765091) B1765091
theorem B783539 : Blo 271824 783539 := bstep (se 1 (by rfl) ⟨587654, by rfl⟩ : syracuseStep 783539 = 1175309) B1175309
theorem B881867 : Blo 271824 881867 := bstep (se 1 (by rfl) ⟨661400, by rfl⟩ : syracuseStep 881867 = 1322801) B1322801
theorem B390425 : Blo 271824 390425 := bstep (se 2 (by rfl) ⟨146409, by rfl⟩ : syracuseStep 390425 = 292819) B292819
theorem B1045811 : Blo 271824 1045811 := bstep (se 1 (by rfl) ⟨784358, by rfl⟩ : syracuseStep 1045811 = 1568717) B1568717
theorem B1766731 : Blo 271824 1766731 := bstep (se 1 (by rfl) ⟨1325048, by rfl⟩ : syracuseStep 1766731 = 2650097) B2650097
theorem B619865 : Blo 271824 619865 := bstep (se 2 (by rfl) ⟨232449, by rfl⟩ : syracuseStep 619865 = 464899) B464899
theorem B390539 : Blo 271824 390539 := bstep (se 1 (by rfl) ⟨292904, by rfl⟩ : syracuseStep 390539 = 585809) B585809
theorem B587159 : Blo 271824 587159 := bstep (se 1 (by rfl) ⟨440369, by rfl⟩ : syracuseStep 587159 = 880739) B880739
theorem B1111475 : Blo 271824 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B619955 : Blo 271824 619955 := bstep (se 1 (by rfl) ⟨464966, by rfl⟩ : syracuseStep 619955 = 929933) B929933
theorem B619991 : Blo 271824 619991 := bstep (se 1 (by rfl) ⟨464993, by rfl⟩ : syracuseStep 619991 = 929987) B929987
theorem B620171 : Blo 271824 620171 := bstep (se 1 (by rfl) ⟨465128, by rfl⟩ : syracuseStep 620171 = 930257) B930257
theorem B620225 : Blo 271824 620225 := bstep (se 2 (by rfl) ⟨232584, by rfl⟩ : syracuseStep 620225 = 465169) B465169
theorem B292631 : Blo 271824 292631 := bstep (se 1 (by rfl) ⟨219473, by rfl⟩ : syracuseStep 292631 = 438947) B438947
theorem B391063 : Blo 271824 391063 := bstep (se 1 (by rfl) ⟨293297, by rfl⟩ : syracuseStep 391063 = 586595) B586595
theorem B620441 : Blo 271824 620441 := bstep (se 2 (by rfl) ⟨232665, by rfl⟩ : syracuseStep 620441 = 465331) B465331
theorem B1046465 : Blo 271824 1046465 := bstep (se 2 (by rfl) ⟨392424, by rfl⟩ : syracuseStep 1046465 = 784849) B784849
theorem B620531 : Blo 271824 620531 := bstep (se 1 (by rfl) ⟨465398, by rfl⟩ : syracuseStep 620531 = 930797) B930797
theorem B620567 : Blo 271824 620567 := bstep (se 1 (by rfl) ⟨465425, by rfl⟩ : syracuseStep 620567 = 930851) B930851
theorem B522443 : Blo 271824 522443 := bstep (se 1 (by rfl) ⟨391832, by rfl⟩ : syracuseStep 522443 = 783665) B783665
theorem B522625 : Blo 271824 522625 := bstep (se 2 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 522625 = 391969) B391969
theorem B489881 : Blo 271824 489881 := bstep (se 2 (by rfl) ⟨183705, by rfl⟩ : syracuseStep 489881 = 367411) B367411
theorem B588235 : Blo 271824 588235 := bstep (se 1 (by rfl) ⟨441176, by rfl⟩ : syracuseStep 588235 = 882353) B882353
theorem B1309229 : Blo 271824 1309229 := bstep (se 3 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 1309229 = 490961) B490961
theorem B391883 : Blo 271824 391883 := bstep (se 1 (by rfl) ⟨293912, by rfl⟩ : syracuseStep 391883 = 587825) B587825
theorem B588505 : Blo 271824 588505 := bstep (se 2 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 588505 = 441379) B441379
theorem B883507 : Blo 271824 883507 := bstep (se 1 (by rfl) ⟨662630, by rfl⟩ : syracuseStep 883507 = 1325261) B1325261
theorem B523073 : Blo 271824 523073 := bstep (se 2 (by rfl) ⟨196152, by rfl⟩ : syracuseStep 523073 = 392305) B392305
theorem B981953 : Blo 271824 981953 := bstep (se 2 (by rfl) ⟨368232, by rfl⟩ : syracuseStep 981953 = 736465) B736465
theorem B785501 : Blo 271824 785501 := bstep (se 3 (by rfl) ⟨147281, by rfl⟩ : syracuseStep 785501 = 294563) B294563
theorem B523415 : Blo 271824 523415 := bstep (se 1 (by rfl) ⟨392561, by rfl⟩ : syracuseStep 523415 = 785123) B785123
theorem B588953 : Blo 271824 588953 := bstep (se 2 (by rfl) ⟨220857, by rfl⟩ : syracuseStep 588953 = 441715) B441715
theorem B1113389 : Blo 271824 1113389 := bstep (se 3 (by rfl) ⟨208760, by rfl⟩ : syracuseStep 1113389 = 417521) B417521
theorem B327115 : Blo 271824 327115 := bstep (se 1 (by rfl) ⟨245336, by rfl⟩ : syracuseStep 327115 = 490673) B490673
theorem B3505625 : Blo 271824 3505625 := bstep (se 2 (by rfl) ⟨1314609, by rfl⟩ : syracuseStep 3505625 = 2629219) B2629219
theorem B294391 : Blo 271824 294391 := bstep (se 1 (by rfl) ⟨220793, by rfl⟩ : syracuseStep 294391 = 441587) B441587
theorem B491033 : Blo 271824 491033 := bstep (se 2 (by rfl) ⟨184137, by rfl⟩ : syracuseStep 491033 = 368275) B368275
theorem B1408643 : Blo 271824 1408643 := bstep (se 1 (by rfl) ⟨1056482, by rfl⟩ : syracuseStep 1408643 = 2112965) B2112965
theorem B1671005 : Blo 271824 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B1474483 : Blo 271824 1474483 := bstep (se 1 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 1474483 = 2211725) B2211725
theorem B688247 : Blo 271824 688247 := bstep (se 1 (by rfl) ⟨516185, by rfl⟩ : syracuseStep 688247 = 1032371) B1032371
theorem B524407 : Blo 271824 524407 := bstep (se 1 (by rfl) ⟨393305, by rfl⟩ : syracuseStep 524407 = 786611) B786611
theorem B1376513 : Blo 271824 1376513 := bstep (se 2 (by rfl) ⟨516192, by rfl⟩ : syracuseStep 1376513 = 1032385) B1032385
theorem B557327 : Blo 271824 557327 := bstep (se 1 (by rfl) ⟨417995, by rfl⟩ : syracuseStep 557327 = 835991) B835991
theorem B459067 : Blo 271824 459067 := bstep (se 1 (by rfl) ⟨344300, by rfl⟩ : syracuseStep 459067 = 688601) B688601
theorem B917945 : Blo 271824 917945 := bstep (se 2 (by rfl) ⟨344229, by rfl⟩ : syracuseStep 917945 = 688459) B688459
theorem B459209 : Blo 271824 459209 := bstep (se 2 (by rfl) ⟨172203, by rfl⟩ : syracuseStep 459209 = 344407) B344407
theorem B1409501 : Blo 271824 1409501 := bstep (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) B528563
theorem B2622145 : Blo 271824 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B623561 : Blo 271824 623561 := bstep (se 2 (by rfl) ⟨233835, by rfl⟩ : syracuseStep 623561 = 467671) B467671
theorem B328711 : Blo 271824 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B918539 : Blo 271824 918539 := bstep (se 1 (by rfl) ⟨688904, by rfl⟩ : syracuseStep 918539 = 1377809) B1377809
theorem B1377323 : Blo 271824 1377323 := bstep (se 1 (by rfl) ⟨1032992, by rfl⟩ : syracuseStep 1377323 = 2065985) B2065985
theorem B918647 : Blo 271824 918647 := bstep (se 1 (by rfl) ⟨688985, by rfl⟩ : syracuseStep 918647 = 1377971) B1377971
theorem B459911 : Blo 271824 459911 := bstep (se 1 (by rfl) ⟨344933, by rfl⟩ : syracuseStep 459911 = 689867) B689867
theorem B689543 : Blo 271824 689543 := bstep (se 1 (by rfl) ⟨517157, by rfl⟩ : syracuseStep 689543 = 1034315) B1034315
theorem B689593 : Blo 271824 689593 := bstep (se 2 (by rfl) ⟨258597, by rfl⟩ : syracuseStep 689593 = 517195) B517195
theorem B36537925 : Blo 271824 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B788087 : Blo 271824 788087 := bstep (se 1 (by rfl) ⟨591065, by rfl⟩ : syracuseStep 788087 = 1182131) B1182131
theorem B1476215 : Blo 271824 1476215 := bstep (se 1 (by rfl) ⟨1107161, by rfl⟩ : syracuseStep 1476215 = 2214323) B2214323
theorem B919241 : Blo 271824 919241 := bstep (se 2 (by rfl) ⟨344715, by rfl⟩ : syracuseStep 919241 = 689431) B689431
theorem B2328335 : Blo 271824 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B460559 : Blo 271824 460559 := bstep (se 1 (by rfl) ⟨345419, by rfl⟩ : syracuseStep 460559 = 690839) B690839
theorem B952211 : Blo 271824 952211 := bstep (se 1 (by rfl) ⟨714158, by rfl⟩ : syracuseStep 952211 = 1428317) B1428317
theorem B10651661 : Blo 271824 10651661 := bstep (se 3 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 10651661 = 3994373) B3994373
theorem B690191 : Blo 271824 690191 := bstep (se 1 (by rfl) ⟨517643, by rfl⟩ : syracuseStep 690191 = 1035287) B1035287
theorem B4982957 : Blo 271824 4982957 := bstep (se 3 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 4982957 = 1868609) B1868609
theorem B1771721 : Blo 271824 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B461099 : Blo 271824 461099 := bstep (se 1 (by rfl) ⟨345824, by rfl⟩ : syracuseStep 461099 = 691649) B691649
theorem B1378619 : Blo 271824 1378619 := bstep (se 1 (by rfl) ⟨1033964, by rfl⟩ : syracuseStep 1378619 = 2067929) B2067929
theorem B919943 : Blo 271824 919943 := bstep (se 1 (by rfl) ⟨689957, by rfl⟩ : syracuseStep 919943 = 1379915) B1379915
theorem B2001287 : Blo 271824 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B1378781 : Blo 271824 1378781 := bstep (se 3 (by rfl) ⟨258521, by rfl⟩ : syracuseStep 1378781 = 517043) B517043
theorem B2230861 : Blo 271824 2230861 := bstep (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) B836573
theorem B461497 : Blo 271824 461497 := bstep (se 2 (by rfl) ⟨173061, by rfl⟩ : syracuseStep 461497 = 346123) B346123
theorem B690889 : Blo 271824 690889 := bstep (se 2 (by rfl) ⟨259083, by rfl⟩ : syracuseStep 690889 = 518167) B518167
theorem B920321 : Blo 271824 920321 := bstep (se 2 (by rfl) ⟨345120, by rfl⟩ : syracuseStep 920321 = 690241) B690241
theorem B1379105 : Blo 271824 1379105 := bstep (se 2 (by rfl) ⟨517164, by rfl⟩ : syracuseStep 1379105 = 1034329) B1034329
theorem B658219 : Blo 271824 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B691031 : Blo 271824 691031 := bstep (se 1 (by rfl) ⟨518273, by rfl⟩ : syracuseStep 691031 = 1036547) B1036547
theorem B1248185 : Blo 271824 1248185 := bstep (se 2 (by rfl) ⟨468069, by rfl⟩ : syracuseStep 1248185 = 936139) B936139
theorem B625963 : Blo 271824 625963 := bstep (se 1 (by rfl) ⟨469472, by rfl⟩ : syracuseStep 625963 = 938945) B938945
theorem B462199 : Blo 271824 462199 := bstep (se 1 (by rfl) ⟨346649, by rfl⟩ : syracuseStep 462199 = 693299) B693299
theorem B1510859 : Blo 271824 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B1969667 : Blo 271824 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B921131 : Blo 271824 921131 := bstep (se 1 (by rfl) ⟨690848, by rfl⟩ : syracuseStep 921131 = 1381697) B1381697
theorem B462395 : Blo 271824 462395 := bstep (se 1 (by rfl) ⟨346796, by rfl⟩ : syracuseStep 462395 = 693593) B693593
theorem B13471373 : Blo 271824 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B1380077 : Blo 271824 1380077 := bstep (se 3 (by rfl) ⟨258764, by rfl⟩ : syracuseStep 1380077 = 517529) B517529
theorem B1314593 : Blo 271824 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B986995 : Blo 271824 986995 := bstep (se 1 (by rfl) ⟨740246, by rfl⟩ : syracuseStep 986995 = 1480493) B1480493
theorem B462793 : Blo 271824 462793 := bstep (se 2 (by rfl) ⟨173547, by rfl⟩ : syracuseStep 462793 = 347095) B347095
theorem B659603 : Blo 271824 659603 := bstep (se 1 (by rfl) ⟨494702, by rfl⟩ : syracuseStep 659603 = 989405) B989405
theorem B1315207 : Blo 271824 1315207 := bstep (se 1 (by rfl) ⟨986405, by rfl⟩ : syracuseStep 1315207 = 1972811) B1972811
theorem B1380887 : Blo 271824 1380887 := bstep (se 1 (by rfl) ⟨1035665, by rfl⟩ : syracuseStep 1380887 = 2071331) B2071331
theorem B463495 : Blo 271824 463495 := bstep (se 1 (by rfl) ⟨347621, by rfl⟩ : syracuseStep 463495 = 695243) B695243
theorem B1676065 : Blo 271824 1676065 := bstep (se 2 (by rfl) ⟨628524, by rfl⟩ : syracuseStep 1676065 = 1257049) B1257049
theorem B1970993 : Blo 271824 1970993 := bstep (se 2 (by rfl) ⟨739122, by rfl⟩ : syracuseStep 1970993 = 1478245) B1478245
theorem B922427 : Blo 271824 922427 := bstep (se 1 (by rfl) ⟨691820, by rfl⟩ : syracuseStep 922427 = 1383641) B1383641
theorem B693107 : Blo 271824 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B1184887 : Blo 271824 1184887 := bstep (se 1 (by rfl) ⟨888665, by rfl⟩ : syracuseStep 1184887 = 1777331) B1777331
theorem B4658309 : Blo 271824 4658309 := bstep (se 4 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 4658309 = 873433) B873433
theorem B464143 : Blo 271824 464143 := bstep (se 1 (by rfl) ⟨348107, by rfl⟩ : syracuseStep 464143 = 696215) B696215
theorem B922913 : Blo 271824 922913 := bstep (se 2 (by rfl) ⟨346092, by rfl⟩ : syracuseStep 922913 = 692185) B692185
theorem B693623 : Blo 271824 693623 := bstep (se 1 (by rfl) ⟨520217, by rfl⟩ : syracuseStep 693623 = 1040435) B1040435
theorem B628087 : Blo 271824 628087 := bstep (se 1 (by rfl) ⟨471065, by rfl⟩ : syracuseStep 628087 = 942131) B942131
theorem B2233975 : Blo 271824 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B464683 : Blo 271824 464683 := bstep (se 1 (by rfl) ⟨348512, by rfl⟩ : syracuseStep 464683 = 697025) B697025
theorem B923507 : Blo 271824 923507 := bstep (se 1 (by rfl) ⟨692630, by rfl⟩ : syracuseStep 923507 = 1385261) B1385261
theorem B464825 : Blo 271824 464825 := bstep (se 2 (by rfl) ⟨174309, by rfl⟩ : syracuseStep 464825 = 348619) B348619
theorem B891169 : Blo 271824 891169 := bstep (se 2 (by rfl) ⟨334188, by rfl⟩ : syracuseStep 891169 = 668377) B668377
theorem B694615 : Blo 271824 694615 := bstep (se 1 (by rfl) ⟨520961, by rfl⟩ : syracuseStep 694615 = 1041923) B1041923
theorem B11770433 : Blo 271824 11770433 := bstep (se 2 (by rfl) ⟨4413912, by rfl⟩ : syracuseStep 11770433 = 8827825) B8827825
theorem B694919 : Blo 271824 694919 := bstep (se 1 (by rfl) ⟨521189, by rfl⟩ : syracuseStep 694919 = 1042379) B1042379
theorem B1088257 : Blo 271824 1088257 := bstep (se 2 (by rfl) ⟨408096, by rfl⟩ : syracuseStep 1088257 = 816193) B816193
theorem B695051 : Blo 271824 695051 := bstep (se 1 (by rfl) ⟨521288, by rfl⟩ : syracuseStep 695051 = 1042577) B1042577
theorem B334735 : Blo 271824 334735 := bstep (se 1 (by rfl) ⟨251051, by rfl⟩ : syracuseStep 334735 = 502103) B502103
theorem B695567 : Blo 271824 695567 := bstep (se 1 (by rfl) ⟨521675, by rfl⟩ : syracuseStep 695567 = 1043351) B1043351
theorem B695699 : Blo 271824 695699 := bstep (se 1 (by rfl) ⟨521774, by rfl⟩ : syracuseStep 695699 = 1043549) B1043549
theorem B826891 : Blo 271824 826891 := bstep (se 1 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 826891 = 1240337) B1240337
theorem B1383965 : Blo 271824 1383965 := bstep (se 3 (by rfl) ⟨259493, by rfl⟩ : syracuseStep 1383965 = 518987) B518987
theorem B991091 : Blo 271824 991091 := bstep (se 1 (by rfl) ⟨743318, by rfl⟩ : syracuseStep 991091 = 1486637) B1486637
theorem B1384451 : Blo 271824 1384451 := bstep (se 1 (by rfl) ⟨1038338, by rfl⟩ : syracuseStep 1384451 = 2076677) B2076677
theorem B926099 : Blo 271824 926099 := bstep (se 1 (by rfl) ⟨694574, by rfl⟩ : syracuseStep 926099 = 1389149) B1389149
theorem B696833 : Blo 271824 696833 := bstep (se 2 (by rfl) ⟨261312, by rfl⟩ : syracuseStep 696833 = 522625) B522625
theorem B3580483 : Blo 271824 3580483 := bstep (se 1 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 3580483 = 5370725) B5370725
theorem B467831 : Blo 271824 467831 := bstep (se 1 (by rfl) ⟨350873, by rfl⟩ : syracuseStep 467831 = 701747) B701747
theorem B697207 : Blo 271824 697207 := bstep (se 1 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 697207 = 1045811) B1045811
theorem B7611479 : Blo 271824 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B664865 : Blo 271824 664865 := bstep (se 2 (by rfl) ⟨249324, by rfl⟩ : syracuseStep 664865 = 498649) B498649
theorem B697643 : Blo 271824 697643 := bstep (se 1 (by rfl) ⟨523232, by rfl⟩ : syracuseStep 697643 = 1046465) B1046465
theorem B271879 : Blo 271824 271879 := bstep (se 1 (by rfl) ⟨203909, by rfl⟩ : syracuseStep 271879 = 407819) B407819
theorem B271887 : Blo 271824 271887 := bstep (se 1 (by rfl) ⟨203915, by rfl⟩ : syracuseStep 271887 = 407831) B407831
theorem B271931 : Blo 271824 271931 := bstep (se 1 (by rfl) ⟨203948, by rfl⟩ : syracuseStep 271931 = 407897) B407897
theorem B1386071 : Blo 271824 1386071 := bstep (se 1 (by rfl) ⟨1039553, by rfl⟩ : syracuseStep 1386071 = 2079107) B2079107
theorem B861815 : Blo 271824 861815 := bstep (se 1 (by rfl) ⟨646361, by rfl⟩ : syracuseStep 861815 = 1292723) B1292723
theorem B272007 : Blo 271824 272007 := bstep (se 1 (by rfl) ⟨204005, by rfl⟩ : syracuseStep 272007 = 408011) B408011
theorem B272015 : Blo 271824 272015 := bstep (se 1 (by rfl) ⟨204011, by rfl⟩ : syracuseStep 272015 = 408023) B408023
theorem B272059 : Blo 271824 272059 := bstep (se 1 (by rfl) ⟨204044, by rfl⟩ : syracuseStep 272059 = 408089) B408089
theorem B272135 : Blo 271824 272135 := bstep (se 1 (by rfl) ⟨204101, by rfl⟩ : syracuseStep 272135 = 408203) B408203
theorem B272143 : Blo 271824 272143 := bstep (se 1 (by rfl) ⟨204107, by rfl⟩ : syracuseStep 272143 = 408215) B408215
theorem B927503 : Blo 271824 927503 := bstep (se 1 (by rfl) ⟨695627, by rfl⟩ : syracuseStep 927503 = 1391255) B1391255
theorem B272187 : Blo 271824 272187 := bstep (se 1 (by rfl) ⟨204140, by rfl⟩ : syracuseStep 272187 = 408281) B408281
theorem B272263 : Blo 271824 272263 := bstep (se 1 (by rfl) ⟨204197, by rfl⟩ : syracuseStep 272263 = 408395) B408395
theorem B272271 : Blo 271824 272271 := bstep (se 1 (by rfl) ⟨204203, by rfl⟩ : syracuseStep 272271 = 408407) B408407
theorem B894905 : Blo 271824 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B436153 : Blo 271824 436153 := bstep (se 2 (by rfl) ⟨163557, by rfl⟩ : syracuseStep 436153 = 327115) B327115
theorem B272315 : Blo 271824 272315 := bstep (se 1 (by rfl) ⟨204236, by rfl⟩ : syracuseStep 272315 = 408473) B408473
theorem B272391 : Blo 271824 272391 := bstep (se 1 (by rfl) ⟨204293, by rfl⟩ : syracuseStep 272391 = 408587) B408587
theorem B272399 : Blo 271824 272399 := bstep (se 1 (by rfl) ⟨204299, by rfl⟩ : syracuseStep 272399 = 408599) B408599
theorem B927773 : Blo 271824 927773 := bstep (se 3 (by rfl) ⟨173957, by rfl⟩ : syracuseStep 927773 = 347915) B347915
theorem B272443 : Blo 271824 272443 := bstep (se 1 (by rfl) ⟨204332, by rfl⟩ : syracuseStep 272443 = 408665) B408665
theorem B1386557 : Blo 271824 1386557 := bstep (se 3 (by rfl) ⟨259979, by rfl⟩ : syracuseStep 1386557 = 519959) B519959
theorem B272519 : Blo 271824 272519 := bstep (se 1 (by rfl) ⟨204389, by rfl⟩ : syracuseStep 272519 = 408779) B408779
theorem B272527 : Blo 271824 272527 := bstep (se 1 (by rfl) ⟨204395, by rfl⟩ : syracuseStep 272527 = 408791) B408791
theorem B272571 : Blo 271824 272571 := bstep (se 1 (by rfl) ⟨204428, by rfl⟩ : syracuseStep 272571 = 408857) B408857
theorem B272647 : Blo 271824 272647 := bstep (se 1 (by rfl) ⟨204485, by rfl⟩ : syracuseStep 272647 = 408971) B408971
theorem B272655 : Blo 271824 272655 := bstep (se 1 (by rfl) ⟨204491, by rfl⟩ : syracuseStep 272655 = 408983) B408983
theorem B272699 : Blo 271824 272699 := bstep (se 1 (by rfl) ⟨204524, by rfl⟩ : syracuseStep 272699 = 409049) B409049
theorem B2337083 : Blo 271824 2337083 := bstep (se 1 (by rfl) ⟨1752812, by rfl⟩ : syracuseStep 2337083 = 3505625) B3505625
theorem B272775 : Blo 271824 272775 := bstep (se 1 (by rfl) ⟨204581, by rfl⟩ : syracuseStep 272775 = 409163) B409163
theorem B272783 : Blo 271824 272783 := bstep (se 1 (by rfl) ⟨204587, by rfl⟩ : syracuseStep 272783 = 409175) B409175
theorem B272827 : Blo 271824 272827 := bstep (se 1 (by rfl) ⟨204620, by rfl⟩ : syracuseStep 272827 = 409241) B409241
theorem B272903 : Blo 271824 272903 := bstep (se 1 (by rfl) ⟨204677, by rfl⟩ : syracuseStep 272903 = 409355) B409355
theorem B272911 : Blo 271824 272911 := bstep (se 1 (by rfl) ⟨204683, by rfl⟩ : syracuseStep 272911 = 409367) B409367
theorem B272955 : Blo 271824 272955 := bstep (se 1 (by rfl) ⟨204716, by rfl⟩ : syracuseStep 272955 = 409433) B409433
theorem B273031 : Blo 271824 273031 := bstep (se 1 (by rfl) ⟨204773, by rfl⟩ : syracuseStep 273031 = 409547) B409547
theorem B273039 : Blo 271824 273039 := bstep (se 1 (by rfl) ⟨204779, by rfl⟩ : syracuseStep 273039 = 409559) B409559
theorem B305851 : Blo 271824 305851 := bstep (se 1 (by rfl) ⟨229388, by rfl⟩ : syracuseStep 305851 = 458777) B458777
theorem B273083 : Blo 271824 273083 := bstep (se 1 (by rfl) ⟨204812, by rfl⟩ : syracuseStep 273083 = 409625) B409625
theorem B11250373 : Blo 271824 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B273159 : Blo 271824 273159 := bstep (se 1 (by rfl) ⟨204869, by rfl⟩ : syracuseStep 273159 = 409739) B409739
theorem B273167 : Blo 271824 273167 := bstep (se 1 (by rfl) ⟨204875, by rfl⟩ : syracuseStep 273167 = 409751) B409751
theorem B437051 : Blo 271824 437051 := bstep (se 1 (by rfl) ⟨327788, by rfl⟩ : syracuseStep 437051 = 655577) B655577
theorem B273211 : Blo 271824 273211 := bstep (se 1 (by rfl) ⟨204908, by rfl⟩ : syracuseStep 273211 = 409817) B409817
theorem B273287 : Blo 271824 273287 := bstep (se 1 (by rfl) ⟨204965, by rfl⟩ : syracuseStep 273287 = 409931) B409931
theorem B273295 : Blo 271824 273295 := bstep (se 1 (by rfl) ⟨204971, by rfl⟩ : syracuseStep 273295 = 409943) B409943
theorem B2632601 : Blo 271824 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B273339 : Blo 271824 273339 := bstep (se 1 (by rfl) ⟨205004, by rfl⟩ : syracuseStep 273339 = 410009) B410009
theorem B273415 : Blo 271824 273415 := bstep (se 1 (by rfl) ⟨205061, by rfl⟩ : syracuseStep 273415 = 410123) B410123
theorem B371719 : Blo 271824 371719 := bstep (se 1 (by rfl) ⟨278789, by rfl⟩ : syracuseStep 371719 = 557579) B557579
theorem B273423 : Blo 271824 273423 := bstep (se 1 (by rfl) ⟨205067, by rfl⟩ : syracuseStep 273423 = 410135) B410135
theorem B273467 : Blo 271824 273467 := bstep (se 1 (by rfl) ⟨205100, by rfl⟩ : syracuseStep 273467 = 410201) B410201
theorem B699479 : Blo 271824 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B5614679 : Blo 271824 5614679 := bstep (se 1 (by rfl) ⟨4211009, by rfl⟩ : syracuseStep 5614679 = 8422019) B8422019
theorem B470135 : Blo 271824 470135 := bstep (se 1 (by rfl) ⟨352601, by rfl⟩ : syracuseStep 470135 = 705203) B705203
theorem B437383 : Blo 271824 437383 := bstep (se 1 (by rfl) ⟨328037, by rfl⟩ : syracuseStep 437383 = 656075) B656075
theorem B273543 : Blo 271824 273543 := bstep (se 1 (by rfl) ⟨205157, by rfl⟩ : syracuseStep 273543 = 410315) B410315
theorem B306319 : Blo 271824 306319 := bstep (se 1 (by rfl) ⟨229739, by rfl⟩ : syracuseStep 306319 = 459479) B459479
theorem B273551 : Blo 271824 273551 := bstep (se 1 (by rfl) ⟨205163, by rfl⟩ : syracuseStep 273551 = 410327) B410327
theorem B273595 : Blo 271824 273595 := bstep (se 1 (by rfl) ⟨205196, by rfl⟩ : syracuseStep 273595 = 410393) B410393
theorem B273671 : Blo 271824 273671 := bstep (se 1 (by rfl) ⟨205253, by rfl⟩ : syracuseStep 273671 = 410507) B410507
theorem B273679 : Blo 271824 273679 := bstep (se 1 (by rfl) ⟨205259, by rfl⟩ : syracuseStep 273679 = 410519) B410519
theorem B273723 : Blo 271824 273723 := bstep (se 1 (by rfl) ⟨205292, by rfl⟩ : syracuseStep 273723 = 410585) B410585
theorem B273799 : Blo 271824 273799 := bstep (se 1 (by rfl) ⟨205349, by rfl⟩ : syracuseStep 273799 = 410699) B410699
theorem B273807 : Blo 271824 273807 := bstep (se 1 (by rfl) ⟨205355, by rfl⟩ : syracuseStep 273807 = 410711) B410711
theorem B929177 : Blo 271824 929177 := bstep (se 2 (by rfl) ⟨348441, by rfl⟩ : syracuseStep 929177 = 696883) B696883
theorem B273851 : Blo 271824 273851 := bstep (se 1 (by rfl) ⟨205388, by rfl⟩ : syracuseStep 273851 = 410777) B410777
theorem B1420753 : Blo 271824 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B1486289 : Blo 271824 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B273927 : Blo 271824 273927 := bstep (se 1 (by rfl) ⟨205445, by rfl⟩ : syracuseStep 273927 = 410891) B410891
theorem B273935 : Blo 271824 273935 := bstep (se 1 (by rfl) ⟨205451, by rfl⟩ : syracuseStep 273935 = 410903) B410903
theorem B273979 : Blo 271824 273979 := bstep (se 1 (by rfl) ⟨205484, by rfl⟩ : syracuseStep 273979 = 410969) B410969
theorem B306823 : Blo 271824 306823 := bstep (se 1 (by rfl) ⟨230117, by rfl⟩ : syracuseStep 306823 = 460235) B460235
theorem B274055 : Blo 271824 274055 := bstep (se 1 (by rfl) ⟨205541, by rfl⟩ : syracuseStep 274055 = 411083) B411083
theorem B274063 : Blo 271824 274063 := bstep (se 1 (by rfl) ⟨205547, by rfl⟩ : syracuseStep 274063 = 411095) B411095
theorem B274107 : Blo 271824 274107 := bstep (se 1 (by rfl) ⟨205580, by rfl⟩ : syracuseStep 274107 = 411161) B411161
theorem B274183 : Blo 271824 274183 := bstep (se 1 (by rfl) ⟨205637, by rfl⟩ : syracuseStep 274183 = 411275) B411275
theorem B274191 : Blo 271824 274191 := bstep (se 1 (by rfl) ⟨205643, by rfl⟩ : syracuseStep 274191 = 411287) B411287
theorem B700193 : Blo 271824 700193 := bstep (se 2 (by rfl) ⟨262572, by rfl⟩ : syracuseStep 700193 = 525145) B525145
theorem B1388339 : Blo 271824 1388339 := bstep (se 1 (by rfl) ⟨1041254, by rfl⟩ : syracuseStep 1388339 = 2082509) B2082509
theorem B307003 : Blo 271824 307003 := bstep (se 1 (by rfl) ⟨230252, by rfl⟩ : syracuseStep 307003 = 460505) B460505
theorem B274235 : Blo 271824 274235 := bstep (se 1 (by rfl) ⟨205676, by rfl⟩ : syracuseStep 274235 = 411353) B411353
theorem B274311 : Blo 271824 274311 := bstep (se 1 (by rfl) ⟨205733, by rfl⟩ : syracuseStep 274311 = 411467) B411467
theorem B274319 : Blo 271824 274319 := bstep (se 1 (by rfl) ⟨205739, by rfl⟩ : syracuseStep 274319 = 411479) B411479
theorem B274363 : Blo 271824 274363 := bstep (se 1 (by rfl) ⟨205772, by rfl⟩ : syracuseStep 274363 = 411545) B411545
theorem B274439 : Blo 271824 274439 := bstep (se 1 (by rfl) ⟨205829, by rfl⟩ : syracuseStep 274439 = 411659) B411659
theorem B274447 : Blo 271824 274447 := bstep (se 1 (by rfl) ⟨205835, by rfl⟩ : syracuseStep 274447 = 411671) B411671
theorem B1126429 : Blo 271824 1126429 := bstep (se 3 (by rfl) ⟨211205, by rfl⟩ : syracuseStep 1126429 = 422411) B422411
theorem B274491 : Blo 271824 274491 := bstep (se 1 (by rfl) ⟨205868, by rfl⟩ : syracuseStep 274491 = 411737) B411737
theorem B929879 : Blo 271824 929879 := bstep (se 1 (by rfl) ⟨697409, by rfl⟩ : syracuseStep 929879 = 1394819) B1394819
theorem B1388663 : Blo 271824 1388663 := bstep (se 1 (by rfl) ⟨1041497, by rfl⟩ : syracuseStep 1388663 = 2082995) B2082995
theorem B274567 : Blo 271824 274567 := bstep (se 1 (by rfl) ⟨205925, by rfl⟩ : syracuseStep 274567 = 411851) B411851
theorem B274575 : Blo 271824 274575 := bstep (se 1 (by rfl) ⟨205931, by rfl⟩ : syracuseStep 274575 = 411863) B411863
theorem B274619 : Blo 271824 274619 := bstep (se 1 (by rfl) ⟨205964, by rfl⟩ : syracuseStep 274619 = 411929) B411929
theorem B438473 : Blo 271824 438473 := bstep (se 2 (by rfl) ⟨164427, by rfl⟩ : syracuseStep 438473 = 328855) B328855
theorem B274695 : Blo 271824 274695 := bstep (se 1 (by rfl) ⟨206021, by rfl⟩ : syracuseStep 274695 = 412043) B412043
theorem B307471 : Blo 271824 307471 := bstep (se 1 (by rfl) ⟨230603, by rfl⟩ : syracuseStep 307471 = 461207) B461207
theorem B274703 : Blo 271824 274703 := bstep (se 1 (by rfl) ⟨206027, by rfl⟩ : syracuseStep 274703 = 412055) B412055
theorem B274747 : Blo 271824 274747 := bstep (se 1 (by rfl) ⟨206060, by rfl⟩ : syracuseStep 274747 = 412121) B412121
theorem B274823 : Blo 271824 274823 := bstep (se 1 (by rfl) ⟨206117, by rfl⟩ : syracuseStep 274823 = 412235) B412235
theorem B274831 : Blo 271824 274831 := bstep (se 1 (by rfl) ⟨206123, by rfl⟩ : syracuseStep 274831 = 412247) B412247
theorem B1814929 : Blo 271824 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B3322259 : Blo 271824 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B274875 : Blo 271824 274875 := bstep (se 1 (by rfl) ⟨206156, by rfl⟩ : syracuseStep 274875 = 412313) B412313
theorem B274951 : Blo 271824 274951 := bstep (se 1 (by rfl) ⟨206213, by rfl⟩ : syracuseStep 274951 = 412427) B412427
theorem B274959 : Blo 271824 274959 := bstep (se 1 (by rfl) ⟨206219, by rfl⟩ : syracuseStep 274959 = 412439) B412439
theorem B275003 : Blo 271824 275003 := bstep (se 1 (by rfl) ⟨206252, by rfl⟩ : syracuseStep 275003 = 412505) B412505
theorem B930365 : Blo 271824 930365 := bstep (se 3 (by rfl) ⟨174443, by rfl⟩ : syracuseStep 930365 = 348887) B348887
theorem B275079 : Blo 271824 275079 := bstep (se 1 (by rfl) ⟨206309, by rfl⟩ : syracuseStep 275079 = 412619) B412619
theorem B275087 : Blo 271824 275087 := bstep (se 1 (by rfl) ⟨206315, by rfl⟩ : syracuseStep 275087 = 412631) B412631
theorem B275131 : Blo 271824 275131 := bstep (se 1 (by rfl) ⟨206348, by rfl⟩ : syracuseStep 275131 = 412697) B412697
theorem B307975 : Blo 271824 307975 := bstep (se 1 (by rfl) ⟨230981, by rfl⟩ : syracuseStep 307975 = 461963) B461963
theorem B275207 : Blo 271824 275207 := bstep (se 1 (by rfl) ⟨206405, by rfl⟩ : syracuseStep 275207 = 412811) B412811
theorem B275215 : Blo 271824 275215 := bstep (se 1 (by rfl) ⟨206411, by rfl⟩ : syracuseStep 275215 = 412823) B412823
theorem B275259 : Blo 271824 275259 := bstep (se 1 (by rfl) ⟨206444, by rfl⟩ : syracuseStep 275259 = 412889) B412889
theorem B275335 : Blo 271824 275335 := bstep (se 1 (by rfl) ⟨206501, by rfl⟩ : syracuseStep 275335 = 413003) B413003
theorem B275343 : Blo 271824 275343 := bstep (se 1 (by rfl) ⟨206507, by rfl⟩ : syracuseStep 275343 = 413015) B413015
theorem B308155 : Blo 271824 308155 := bstep (se 1 (by rfl) ⟨231116, by rfl⟩ : syracuseStep 308155 = 462233) B462233
theorem B275387 : Blo 271824 275387 := bstep (se 1 (by rfl) ⟨206540, by rfl⟩ : syracuseStep 275387 = 413081) B413081
theorem B275463 : Blo 271824 275463 := bstep (se 1 (by rfl) ⟨206597, by rfl⟩ : syracuseStep 275463 = 413195) B413195
theorem B2208779 : Blo 271824 2208779 := bstep (se 1 (by rfl) ⟨1656584, by rfl⟩ : syracuseStep 2208779 = 3313169) B3313169
theorem B275471 : Blo 271824 275471 := bstep (se 1 (by rfl) ⟨206603, by rfl⟩ : syracuseStep 275471 = 413207) B413207
theorem B275515 : Blo 271824 275515 := bstep (se 1 (by rfl) ⟨206636, by rfl⟩ : syracuseStep 275515 = 413273) B413273
theorem B1389635 : Blo 271824 1389635 := bstep (se 1 (by rfl) ⟨1042226, by rfl⟩ : syracuseStep 1389635 = 2084453) B2084453
theorem B275591 : Blo 271824 275591 := bstep (se 1 (by rfl) ⟨206693, by rfl⟩ : syracuseStep 275591 = 413387) B413387
theorem B275599 : Blo 271824 275599 := bstep (se 1 (by rfl) ⟨206699, by rfl⟩ : syracuseStep 275599 = 413399) B413399
theorem B275643 : Blo 271824 275643 := bstep (se 1 (by rfl) ⟨206732, by rfl⟩ : syracuseStep 275643 = 413465) B413465
theorem B275719 : Blo 271824 275719 := bstep (se 1 (by rfl) ⟨206789, by rfl⟩ : syracuseStep 275719 = 413579) B413579
theorem B275727 : Blo 271824 275727 := bstep (se 1 (by rfl) ⟨206795, by rfl⟩ : syracuseStep 275727 = 413591) B413591
theorem B275771 : Blo 271824 275771 := bstep (se 1 (by rfl) ⟨206828, by rfl⟩ : syracuseStep 275771 = 413657) B413657
theorem B1389959 : Blo 271824 1389959 := bstep (se 1 (by rfl) ⟨1042469, by rfl⟩ : syracuseStep 1389959 = 2084939) B2084939
theorem B308623 : Blo 271824 308623 := bstep (se 1 (by rfl) ⟨231467, by rfl⟩ : syracuseStep 308623 = 462935) B462935
theorem B1488451 : Blo 271824 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B4667057 : Blo 271824 4667057 := bstep (se 2 (by rfl) ⟨1750146, by rfl⟩ : syracuseStep 4667057 = 3500293) B3500293
theorem B2111233 : Blo 271824 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B309127 : Blo 271824 309127 := bstep (se 1 (by rfl) ⟨231845, by rfl⟩ : syracuseStep 309127 = 463691) B463691
theorem B2504611 : Blo 271824 2504611 := bstep (se 1 (by rfl) ⟨1878458, by rfl⟩ : syracuseStep 2504611 = 3756917) B3756917
theorem B309307 : Blo 271824 309307 := bstep (se 1 (by rfl) ⟨231980, by rfl⟩ : syracuseStep 309307 = 463961) B463961
theorem B407753 : Blo 271824 407753 := bstep (se 2 (by rfl) ⟨152907, by rfl⟩ : syracuseStep 407753 = 305815) B305815
theorem B407867 : Blo 271824 407867 := bstep (se 1 (by rfl) ⟨305900, by rfl⟩ : syracuseStep 407867 = 611801) B611801
theorem B407927 : Blo 271824 407927 := bstep (se 1 (by rfl) ⟨305945, by rfl⟩ : syracuseStep 407927 = 611891) B611891
theorem B407951 : Blo 271824 407951 := bstep (se 1 (by rfl) ⟨305963, by rfl⟩ : syracuseStep 407951 = 611927) B611927
theorem B407993 : Blo 271824 407993 := bstep (se 2 (by rfl) ⟨152997, by rfl⟩ : syracuseStep 407993 = 305995) B305995
theorem B408071 : Blo 271824 408071 := bstep (se 1 (by rfl) ⟨306053, by rfl⟩ : syracuseStep 408071 = 612107) B612107
theorem B309775 : Blo 271824 309775 := bstep (se 1 (by rfl) ⟨232331, by rfl⟩ : syracuseStep 309775 = 464663) B464663
theorem B408107 : Blo 271824 408107 := bstep (se 1 (by rfl) ⟨306080, by rfl⟩ : syracuseStep 408107 = 612161) B612161
theorem B408137 : Blo 271824 408137 := bstep (se 2 (by rfl) ⟨153051, by rfl⟩ : syracuseStep 408137 = 306103) B306103
theorem B408251 : Blo 271824 408251 := bstep (se 1 (by rfl) ⟨306188, by rfl⟩ : syracuseStep 408251 = 612377) B612377
theorem B1161965 : Blo 271824 1161965 := bstep (se 3 (by rfl) ⟨217868, by rfl⟩ : syracuseStep 1161965 = 435737) B435737
theorem B408311 : Blo 271824 408311 := bstep (se 1 (by rfl) ⟨306233, by rfl⟩ : syracuseStep 408311 = 612467) B612467
theorem B408335 : Blo 271824 408335 := bstep (se 1 (by rfl) ⟨306251, by rfl⟩ : syracuseStep 408335 = 612503) B612503
theorem B2964275 : Blo 271824 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B408377 : Blo 271824 408377 := bstep (se 2 (by rfl) ⟨153141, by rfl⟩ : syracuseStep 408377 = 306283) B306283
theorem B408455 : Blo 271824 408455 := bstep (se 1 (by rfl) ⟨306341, by rfl⟩ : syracuseStep 408455 = 612683) B612683
theorem B408491 : Blo 271824 408491 := bstep (se 1 (by rfl) ⟨306368, by rfl⟩ : syracuseStep 408491 = 612737) B612737
theorem B408521 : Blo 271824 408521 := bstep (se 2 (by rfl) ⟨153195, by rfl⟩ : syracuseStep 408521 = 306391) B306391
theorem B310279 : Blo 271824 310279 := bstep (se 1 (by rfl) ⟨232709, by rfl⟩ : syracuseStep 310279 = 465419) B465419
theorem B408635 : Blo 271824 408635 := bstep (se 1 (by rfl) ⟨306476, by rfl⟩ : syracuseStep 408635 = 612953) B612953
theorem B408695 : Blo 271824 408695 := bstep (se 1 (by rfl) ⟨306521, by rfl⟩ : syracuseStep 408695 = 613043) B613043
theorem B408719 : Blo 271824 408719 := bstep (se 1 (by rfl) ⟨306539, by rfl⟩ : syracuseStep 408719 = 613079) B613079
theorem B408761 : Blo 271824 408761 := bstep (se 2 (by rfl) ⟨153285, by rfl⟩ : syracuseStep 408761 = 306571) B306571
theorem B408839 : Blo 271824 408839 := bstep (se 1 (by rfl) ⟨306629, by rfl⟩ : syracuseStep 408839 = 613259) B613259
theorem B408875 : Blo 271824 408875 := bstep (se 1 (by rfl) ⟨306656, by rfl⟩ : syracuseStep 408875 = 613313) B613313
theorem B736571 : Blo 271824 736571 := bstep (se 1 (by rfl) ⟨552428, by rfl⟩ : syracuseStep 736571 = 1104857) B1104857
theorem B408905 : Blo 271824 408905 := bstep (se 2 (by rfl) ⟨153339, by rfl⟩ : syracuseStep 408905 = 306679) B306679
theorem B1555847 : Blo 271824 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B1752455 : Blo 271824 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B409019 : Blo 271824 409019 := bstep (se 1 (by rfl) ⟨306764, by rfl⟩ : syracuseStep 409019 = 613529) B613529
theorem B409079 : Blo 271824 409079 := bstep (se 1 (by rfl) ⟨306809, by rfl⟩ : syracuseStep 409079 = 613619) B613619
theorem B409103 : Blo 271824 409103 := bstep (se 1 (by rfl) ⟨306827, by rfl⟩ : syracuseStep 409103 = 613655) B613655
theorem B409145 : Blo 271824 409145 := bstep (se 2 (by rfl) ⟨153429, by rfl⟩ : syracuseStep 409145 = 306859) B306859
theorem B2342519 : Blo 271824 2342519 := bstep (se 1 (by rfl) ⟨1756889, by rfl⟩ : syracuseStep 2342519 = 3513779) B3513779
theorem B409223 : Blo 271824 409223 := bstep (se 1 (by rfl) ⟨306917, by rfl⟩ : syracuseStep 409223 = 613835) B613835
theorem B409259 : Blo 271824 409259 := bstep (se 1 (by rfl) ⟨306944, by rfl⟩ : syracuseStep 409259 = 613889) B613889
theorem B605881 : Blo 271824 605881 := bstep (se 2 (by rfl) ⟨227205, by rfl⟩ : syracuseStep 605881 = 454411) B454411
theorem B409289 : Blo 271824 409289 := bstep (se 2 (by rfl) ⟨153483, by rfl⟩ : syracuseStep 409289 = 306967) B306967
theorem B409403 : Blo 271824 409403 := bstep (se 1 (by rfl) ⟨307052, by rfl⟩ : syracuseStep 409403 = 614105) B614105
theorem B409463 : Blo 271824 409463 := bstep (se 1 (by rfl) ⟨307097, by rfl⟩ : syracuseStep 409463 = 614195) B614195
theorem B409487 : Blo 271824 409487 := bstep (se 1 (by rfl) ⟨307115, by rfl⟩ : syracuseStep 409487 = 614231) B614231
theorem B409529 : Blo 271824 409529 := bstep (se 2 (by rfl) ⟨153573, by rfl⟩ : syracuseStep 409529 = 307147) B307147
theorem B409607 : Blo 271824 409607 := bstep (se 1 (by rfl) ⟨307205, by rfl⟩ : syracuseStep 409607 = 614411) B614411
theorem B1032203 : Blo 271824 1032203 := bstep (se 1 (by rfl) ⟨774152, by rfl⟩ : syracuseStep 1032203 = 1548305) B1548305
theorem B409643 : Blo 271824 409643 := bstep (se 1 (by rfl) ⟨307232, by rfl⟩ : syracuseStep 409643 = 614465) B614465
theorem B409673 : Blo 271824 409673 := bstep (se 2 (by rfl) ⟨153627, by rfl⟩ : syracuseStep 409673 = 307255) B307255
theorem B409787 : Blo 271824 409787 := bstep (se 1 (by rfl) ⟨307340, by rfl⟩ : syracuseStep 409787 = 614681) B614681
theorem B409847 : Blo 271824 409847 := bstep (se 1 (by rfl) ⟨307385, by rfl⟩ : syracuseStep 409847 = 614771) B614771
theorem B409871 : Blo 271824 409871 := bstep (se 1 (by rfl) ⟨307403, by rfl⟩ : syracuseStep 409871 = 614807) B614807
theorem B704783 : Blo 271824 704783 := bstep (se 1 (by rfl) ⟨528587, by rfl⟩ : syracuseStep 704783 = 1057175) B1057175
theorem B409913 : Blo 271824 409913 := bstep (se 2 (by rfl) ⟨153717, by rfl⟩ : syracuseStep 409913 = 307435) B307435
theorem B5030237 : Blo 271824 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B409991 : Blo 271824 409991 := bstep (se 1 (by rfl) ⟨307493, by rfl⟩ : syracuseStep 409991 = 614987) B614987
theorem B410027 : Blo 271824 410027 := bstep (se 1 (by rfl) ⟨307520, by rfl⟩ : syracuseStep 410027 = 615041) B615041
theorem B410057 : Blo 271824 410057 := bstep (se 2 (by rfl) ⟨153771, by rfl⟩ : syracuseStep 410057 = 307543) B307543
theorem B410171 : Blo 271824 410171 := bstep (se 1 (by rfl) ⟨307628, by rfl⟩ : syracuseStep 410171 = 615257) B615257
theorem B1557053 : Blo 271824 1557053 := bstep (se 3 (by rfl) ⟨291947, by rfl⟩ : syracuseStep 1557053 = 583895) B583895
theorem B410231 : Blo 271824 410231 := bstep (se 1 (by rfl) ⟨307673, by rfl⟩ : syracuseStep 410231 = 615347) B615347
theorem B410255 : Blo 271824 410255 := bstep (se 1 (by rfl) ⟨307691, by rfl⟩ : syracuseStep 410255 = 615383) B615383
theorem B410297 : Blo 271824 410297 := bstep (se 2 (by rfl) ⟨153861, by rfl⟩ : syracuseStep 410297 = 307723) B307723
theorem B3556057 : Blo 271824 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B2081537 : Blo 271824 2081537 := bstep (se 2 (by rfl) ⟨780576, by rfl⟩ : syracuseStep 2081537 = 1561153) B1561153
theorem B410375 : Blo 271824 410375 := bstep (se 1 (by rfl) ⟨307781, by rfl⟩ : syracuseStep 410375 = 615563) B615563
theorem B410411 : Blo 271824 410411 := bstep (se 1 (by rfl) ⟨307808, by rfl⟩ : syracuseStep 410411 = 615617) B615617
theorem B410441 : Blo 271824 410441 := bstep (se 2 (by rfl) ⟨153915, by rfl⟩ : syracuseStep 410441 = 307831) B307831
theorem B2212697 : Blo 271824 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B1393523 : Blo 271824 1393523 := bstep (se 1 (by rfl) ⟨1045142, by rfl⟩ : syracuseStep 1393523 = 2090285) B2090285
theorem B1033145 : Blo 271824 1033145 := bstep (se 2 (by rfl) ⟨387429, by rfl⟩ : syracuseStep 1033145 = 774859) B774859
theorem B410555 : Blo 271824 410555 := bstep (se 1 (by rfl) ⟨307916, by rfl⟩ : syracuseStep 410555 = 615833) B615833
theorem B410615 : Blo 271824 410615 := bstep (se 1 (by rfl) ⟨307961, by rfl⟩ : syracuseStep 410615 = 615923) B615923
theorem B410639 : Blo 271824 410639 := bstep (se 1 (by rfl) ⟨307979, by rfl⟩ : syracuseStep 410639 = 615959) B615959
theorem B410681 : Blo 271824 410681 := bstep (se 2 (by rfl) ⟨154005, by rfl⟩ : syracuseStep 410681 = 308011) B308011
theorem B1262659 : Blo 271824 1262659 := bstep (se 1 (by rfl) ⟨946994, by rfl⟩ : syracuseStep 1262659 = 1893989) B1893989
theorem B410759 : Blo 271824 410759 := bstep (se 1 (by rfl) ⟨308069, by rfl⟩ : syracuseStep 410759 = 616139) B616139
theorem B410795 : Blo 271824 410795 := bstep (se 1 (by rfl) ⟨308096, by rfl⟩ : syracuseStep 410795 = 616193) B616193
theorem B2376877 : Blo 271824 2376877 := bstep (se 3 (by rfl) ⟨445664, by rfl⟩ : syracuseStep 2376877 = 891329) B891329
theorem B410825 : Blo 271824 410825 := bstep (se 2 (by rfl) ⟨154059, by rfl⟩ : syracuseStep 410825 = 308119) B308119
theorem B410939 : Blo 271824 410939 := bstep (se 1 (by rfl) ⟨308204, by rfl⟩ : syracuseStep 410939 = 616409) B616409
theorem B1394009 : Blo 271824 1394009 := bstep (se 2 (by rfl) ⟨522753, by rfl⟩ : syracuseStep 1394009 = 1045507) B1045507
theorem B410999 : Blo 271824 410999 := bstep (se 1 (by rfl) ⟨308249, by rfl⟩ : syracuseStep 410999 = 616499) B616499
theorem B411023 : Blo 271824 411023 := bstep (se 1 (by rfl) ⟨308267, by rfl⟩ : syracuseStep 411023 = 616535) B616535
theorem B411065 : Blo 271824 411065 := bstep (se 2 (by rfl) ⟨154149, by rfl⟩ : syracuseStep 411065 = 308299) B308299
theorem B312763 : Blo 271824 312763 := bstep (se 1 (by rfl) ⟨234572, by rfl⟩ : syracuseStep 312763 = 469145) B469145
theorem B1590749 : Blo 271824 1590749 := bstep (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) B596531
theorem B411143 : Blo 271824 411143 := bstep (se 1 (by rfl) ⟨308357, by rfl⟩ : syracuseStep 411143 = 616715) B616715
theorem B411179 : Blo 271824 411179 := bstep (se 1 (by rfl) ⟨308384, by rfl⟩ : syracuseStep 411179 = 616769) B616769
theorem B411209 : Blo 271824 411209 := bstep (se 2 (by rfl) ⟨154203, by rfl⟩ : syracuseStep 411209 = 308407) B308407
theorem B1164887 : Blo 271824 1164887 := bstep (se 1 (by rfl) ⟨873665, by rfl⟩ : syracuseStep 1164887 = 1747331) B1747331
theorem B6670001 : Blo 271824 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B411323 : Blo 271824 411323 := bstep (se 1 (by rfl) ⟨308492, by rfl⟩ : syracuseStep 411323 = 616985) B616985
theorem B411383 : Blo 271824 411383 := bstep (se 1 (by rfl) ⟨308537, by rfl⟩ : syracuseStep 411383 = 617075) B617075
theorem B411407 : Blo 271824 411407 := bstep (se 1 (by rfl) ⟨308555, by rfl⟩ : syracuseStep 411407 = 617111) B617111
theorem B411449 : Blo 271824 411449 := bstep (se 2 (by rfl) ⟨154293, by rfl⟩ : syracuseStep 411449 = 308587) B308587
theorem B476987 : Blo 271824 476987 := bstep (se 1 (by rfl) ⟨357740, by rfl⟩ : syracuseStep 476987 = 715481) B715481
theorem B411527 : Blo 271824 411527 := bstep (se 1 (by rfl) ⟨308645, by rfl⟩ : syracuseStep 411527 = 617291) B617291
theorem B346027 : Blo 271824 346027 := bstep (se 1 (by rfl) ⟨259520, by rfl⟩ : syracuseStep 346027 = 519041) B519041
theorem B411563 : Blo 271824 411563 := bstep (se 1 (by rfl) ⟨308672, by rfl⟩ : syracuseStep 411563 = 617345) B617345
theorem B411593 : Blo 271824 411593 := bstep (se 2 (by rfl) ⟨154347, by rfl⟩ : syracuseStep 411593 = 308695) B308695
theorem B837643 : Blo 271824 837643 := bstep (se 1 (by rfl) ⟨628232, by rfl⟩ : syracuseStep 837643 = 1256465) B1256465
theorem B411707 : Blo 271824 411707 := bstep (se 1 (by rfl) ⟨308780, by rfl⟩ : syracuseStep 411707 = 617561) B617561
theorem B411767 : Blo 271824 411767 := bstep (se 1 (by rfl) ⟨308825, by rfl⟩ : syracuseStep 411767 = 617651) B617651
theorem B575623 : Blo 271824 575623 := bstep (se 1 (by rfl) ⟨431717, by rfl⟩ : syracuseStep 575623 = 863435) B863435
theorem B411791 : Blo 271824 411791 := bstep (se 1 (by rfl) ⟨308843, by rfl⟩ : syracuseStep 411791 = 617687) B617687
theorem B411833 : Blo 271824 411833 := bstep (se 2 (by rfl) ⟨154437, by rfl⟩ : syracuseStep 411833 = 308875) B308875
theorem B411911 : Blo 271824 411911 := bstep (se 1 (by rfl) ⟨308933, by rfl⟩ : syracuseStep 411911 = 617867) B617867
theorem B411947 : Blo 271824 411947 := bstep (se 1 (by rfl) ⟨308960, by rfl⟩ : syracuseStep 411947 = 617921) B617921
theorem B411977 : Blo 271824 411977 := bstep (se 2 (by rfl) ⟨154491, by rfl⟩ : syracuseStep 411977 = 308983) B308983
theorem B3131783 : Blo 271824 3131783 := bstep (se 1 (by rfl) ⟨2348837, by rfl⟩ : syracuseStep 3131783 = 4697675) B4697675
theorem B412091 : Blo 271824 412091 := bstep (se 1 (by rfl) ⟨309068, by rfl⟩ : syracuseStep 412091 = 618137) B618137
theorem B412151 : Blo 271824 412151 := bstep (se 1 (by rfl) ⟨309113, by rfl⟩ : syracuseStep 412151 = 618227) B618227
theorem B412175 : Blo 271824 412175 := bstep (se 1 (by rfl) ⟨309131, by rfl⟩ : syracuseStep 412175 = 618263) B618263
theorem B412217 : Blo 271824 412217 := bstep (se 2 (by rfl) ⟨154581, by rfl⟩ : syracuseStep 412217 = 309163) B309163
theorem B739901 : Blo 271824 739901 := bstep (se 3 (by rfl) ⟨138731, by rfl⟩ : syracuseStep 739901 = 277463) B277463
theorem B412295 : Blo 271824 412295 := bstep (se 1 (by rfl) ⟨309221, by rfl⟩ : syracuseStep 412295 = 618443) B618443
theorem B412331 : Blo 271824 412331 := bstep (se 1 (by rfl) ⟨309248, by rfl⟩ : syracuseStep 412331 = 618497) B618497
theorem B412361 : Blo 271824 412361 := bstep (se 2 (by rfl) ⟨154635, by rfl⟩ : syracuseStep 412361 = 309271) B309271
theorem B5917475 : Blo 271824 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B412475 : Blo 271824 412475 := bstep (se 1 (by rfl) ⟨309356, by rfl⟩ : syracuseStep 412475 = 618713) B618713
theorem B346999 : Blo 271824 346999 := bstep (se 1 (by rfl) ⟨260249, by rfl⟩ : syracuseStep 346999 = 520499) B520499
theorem B412535 : Blo 271824 412535 := bstep (se 1 (by rfl) ⟨309401, by rfl⟩ : syracuseStep 412535 = 618803) B618803
theorem B412559 : Blo 271824 412559 := bstep (se 1 (by rfl) ⟨309419, by rfl⟩ : syracuseStep 412559 = 618839) B618839
theorem B412601 : Blo 271824 412601 := bstep (se 2 (by rfl) ⟨154725, by rfl⟩ : syracuseStep 412601 = 309451) B309451
theorem B412679 : Blo 271824 412679 := bstep (se 1 (by rfl) ⟨309509, by rfl⟩ : syracuseStep 412679 = 619019) B619019
theorem B412715 : Blo 271824 412715 := bstep (se 1 (by rfl) ⟨309536, by rfl⟩ : syracuseStep 412715 = 619073) B619073
theorem B412745 : Blo 271824 412745 := bstep (se 2 (by rfl) ⟨154779, by rfl⟩ : syracuseStep 412745 = 309559) B309559
theorem B347323 : Blo 271824 347323 := bstep (se 1 (by rfl) ⟨260492, by rfl⟩ : syracuseStep 347323 = 520985) B520985
theorem B412859 : Blo 271824 412859 := bstep (se 1 (by rfl) ⟨309644, by rfl⟩ : syracuseStep 412859 = 619289) B619289
theorem B412919 : Blo 271824 412919 := bstep (se 1 (by rfl) ⟨309689, by rfl⟩ : syracuseStep 412919 = 619379) B619379
theorem B412943 : Blo 271824 412943 := bstep (se 1 (by rfl) ⟨309707, by rfl⟩ : syracuseStep 412943 = 619415) B619415
theorem B412985 : Blo 271824 412985 := bstep (se 2 (by rfl) ⟨154869, by rfl⟩ : syracuseStep 412985 = 309739) B309739
theorem B413063 : Blo 271824 413063 := bstep (se 1 (by rfl) ⟨309797, by rfl⟩ : syracuseStep 413063 = 619595) B619595
theorem B2805137 : Blo 271824 2805137 := bstep (se 2 (by rfl) ⟨1051926, by rfl⟩ : syracuseStep 2805137 = 2103853) B2103853
theorem B1396115 : Blo 271824 1396115 := bstep (se 1 (by rfl) ⟨1047086, by rfl⟩ : syracuseStep 1396115 = 2094173) B2094173
theorem B413099 : Blo 271824 413099 := bstep (se 1 (by rfl) ⟨309824, by rfl⟩ : syracuseStep 413099 = 619649) B619649
theorem B413129 : Blo 271824 413129 := bstep (se 2 (by rfl) ⟨154923, by rfl⟩ : syracuseStep 413129 = 309847) B309847
theorem B1035787 : Blo 271824 1035787 := bstep (se 1 (by rfl) ⟨776840, by rfl⟩ : syracuseStep 1035787 = 1553681) B1553681
theorem B413243 : Blo 271824 413243 := bstep (se 1 (by rfl) ⟨309932, by rfl⟩ : syracuseStep 413243 = 619865) B619865
theorem B740983 : Blo 271824 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B413303 : Blo 271824 413303 := bstep (se 1 (by rfl) ⟨309977, by rfl⟩ : syracuseStep 413303 = 619955) B619955
theorem B413327 : Blo 271824 413327 := bstep (se 1 (by rfl) ⟨309995, by rfl⟩ : syracuseStep 413327 = 619991) B619991
theorem B413369 : Blo 271824 413369 := bstep (se 2 (by rfl) ⟨155013, by rfl⟩ : syracuseStep 413369 = 310027) B310027
theorem B413447 : Blo 271824 413447 := bstep (se 1 (by rfl) ⟨310085, by rfl⟩ : syracuseStep 413447 = 620171) B620171
theorem B413483 : Blo 271824 413483 := bstep (se 1 (by rfl) ⟨310112, by rfl⟩ : syracuseStep 413483 = 620225) B620225
theorem B1036091 : Blo 271824 1036091 := bstep (se 1 (by rfl) ⟨777068, by rfl⟩ : syracuseStep 1036091 = 1554137) B1554137
theorem B413513 : Blo 271824 413513 := bstep (se 2 (by rfl) ⟨155067, by rfl⟩ : syracuseStep 413513 = 310135) B310135
theorem B413627 : Blo 271824 413627 := bstep (se 1 (by rfl) ⟨310220, by rfl⟩ : syracuseStep 413627 = 620441) B620441
theorem B413687 : Blo 271824 413687 := bstep (se 1 (by rfl) ⟨310265, by rfl⟩ : syracuseStep 413687 = 620531) B620531
theorem B413711 : Blo 271824 413711 := bstep (se 1 (by rfl) ⟨310283, by rfl⟩ : syracuseStep 413711 = 620567) B620567
theorem B2216069 : Blo 271824 2216069 := bstep (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) B415513
theorem B348295 : Blo 271824 348295 := bstep (se 1 (by rfl) ⟨261221, by rfl⟩ : syracuseStep 348295 = 522443) B522443
theorem B3526901 : Blo 271824 3526901 := bstep (se 5 (by rfl) ⟨165323, by rfl⟩ : syracuseStep 3526901 = 330647) B330647
theorem B1036577 : Blo 271824 1036577 := bstep (se 2 (by rfl) ⟨388716, by rfl⟩ : syracuseStep 1036577 = 777433) B777433
theorem B774461 : Blo 271824 774461 := bstep (se 3 (by rfl) ⟨145211, by rfl⟩ : syracuseStep 774461 = 290423) B290423
theorem B872819 : Blo 271824 872819 := bstep (se 1 (by rfl) ⟨654614, by rfl⟩ : syracuseStep 872819 = 1309229) B1309229
theorem B348715 : Blo 271824 348715 := bstep (se 1 (by rfl) ⟨261536, by rfl⟩ : syracuseStep 348715 = 523073) B523073
theorem B774791 : Blo 271824 774791 := bstep (se 1 (by rfl) ⟨581093, by rfl⟩ : syracuseStep 774791 = 1162187) B1162187
theorem B348943 : Blo 271824 348943 := bstep (se 1 (by rfl) ⟨261707, by rfl⟩ : syracuseStep 348943 = 523415) B523415
theorem B742259 : Blo 271824 742259 := bstep (se 1 (by rfl) ⟨556694, by rfl⟩ : syracuseStep 742259 = 1113389) B1113389
theorem B1168337 : Blo 271824 1168337 := bstep (se 2 (by rfl) ⟨438126, by rfl⟩ : syracuseStep 1168337 = 876253) B876253
theorem B2085911 : Blo 271824 2085911 := bstep (se 1 (by rfl) ⟨1564433, by rfl⟩ : syracuseStep 2085911 = 3128867) B3128867
theorem B939095 : Blo 271824 939095 := bstep (se 1 (by rfl) ⟨704321, by rfl⟩ : syracuseStep 939095 = 1408643) B1408643
theorem B1037549 : Blo 271824 1037549 := bstep (se 3 (by rfl) ⟨194540, by rfl⟩ : syracuseStep 1037549 = 389081) B389081
theorem B2119121 : Blo 271824 2119121 := bstep (se 2 (by rfl) ⟨794670, by rfl⟩ : syracuseStep 2119121 = 1589341) B1589341
theorem B611855 : Blo 271824 611855 := bstep (se 1 (by rfl) ⟨458891, by rfl⟩ : syracuseStep 611855 = 917783) B917783
theorem B611873 : Blo 271824 611873 := bstep (se 2 (by rfl) ⟨229452, by rfl⟩ : syracuseStep 611873 = 458905) B458905
theorem B2643673 : Blo 271824 2643673 := bstep (se 2 (by rfl) ⟨991377, by rfl⟩ : syracuseStep 2643673 = 1982755) B1982755
theorem B612215 : Blo 271824 612215 := bstep (se 1 (by rfl) ⟨459161, by rfl⟩ : syracuseStep 612215 = 918323) B918323
theorem B415751 : Blo 271824 415751 := bstep (se 1 (by rfl) ⟨311813, by rfl⟩ : syracuseStep 415751 = 623627) B623627
theorem B612395 : Blo 271824 612395 := bstep (se 1 (by rfl) ⟨459296, by rfl⟩ : syracuseStep 612395 = 918593) B918593
theorem B842071 : Blo 271824 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B776567 : Blo 271824 776567 := bstep (se 1 (by rfl) ⟨582425, by rfl⟩ : syracuseStep 776567 = 1164851) B1164851
theorem B612755 : Blo 271824 612755 := bstep (se 1 (by rfl) ⟨459566, by rfl⟩ : syracuseStep 612755 = 919133) B919133
theorem B612809 : Blo 271824 612809 := bstep (se 2 (by rfl) ⟨229803, by rfl⟩ : syracuseStep 612809 = 459607) B459607
theorem B875279 : Blo 271824 875279 := bstep (se 1 (by rfl) ⟨656459, by rfl⟩ : syracuseStep 875279 = 1312919) B1312919
theorem B2644751 : Blo 271824 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B613511 : Blo 271824 613511 := bstep (se 1 (by rfl) ⟨460133, by rfl⟩ : syracuseStep 613511 = 920267) B920267
theorem B613691 : Blo 271824 613691 := bstep (se 1 (by rfl) ⟨460268, by rfl⟩ : syracuseStep 613691 = 920537) B920537
theorem B1039675 : Blo 271824 1039675 := bstep (se 1 (by rfl) ⟨779756, by rfl⟩ : syracuseStep 1039675 = 1559513) B1559513
theorem B777559 : Blo 271824 777559 := bstep (se 1 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 777559 = 1166339) B1166339
theorem B613817 : Blo 271824 613817 := bstep (se 2 (by rfl) ⟨230181, by rfl⟩ : syracuseStep 613817 = 460363) B460363
theorem B614159 : Blo 271824 614159 := bstep (se 1 (by rfl) ⟨460619, by rfl⟩ : syracuseStep 614159 = 921239) B921239
theorem B614177 : Blo 271824 614177 := bstep (se 2 (by rfl) ⟨230316, by rfl⟩ : syracuseStep 614177 = 460633) B460633
theorem B1040161 : Blo 271824 1040161 := bstep (se 2 (by rfl) ⟨390060, by rfl⟩ : syracuseStep 1040161 = 780121) B780121
theorem B581435 : Blo 271824 581435 := bstep (se 1 (by rfl) ⟨436076, by rfl⟩ : syracuseStep 581435 = 872153) B872153
theorem B614519 : Blo 271824 614519 := bstep (se 1 (by rfl) ⟨460889, by rfl⟩ : syracuseStep 614519 = 921779) B921779
theorem B614699 : Blo 271824 614699 := bstep (se 1 (by rfl) ⟨461024, by rfl⟩ : syracuseStep 614699 = 922049) B922049
theorem B582187 : Blo 271824 582187 := bstep (se 1 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 582187 = 873281) B873281
theorem B516755 : Blo 271824 516755 := bstep (se 1 (by rfl) ⟨387566, by rfl⟩ : syracuseStep 516755 = 775133) B775133
theorem B615059 : Blo 271824 615059 := bstep (se 1 (by rfl) ⟨461294, by rfl⟩ : syracuseStep 615059 = 922589) B922589
theorem B516793 : Blo 271824 516793 := bstep (se 2 (by rfl) ⟨193797, by rfl⟩ : syracuseStep 516793 = 387595) B387595
theorem B615113 : Blo 271824 615113 := bstep (se 2 (by rfl) ⟨230667, by rfl⟩ : syracuseStep 615113 = 461335) B461335
theorem B1041133 : Blo 271824 1041133 := bstep (se 3 (by rfl) ⟨195212, by rfl⟩ : syracuseStep 1041133 = 390425) B390425
theorem B779051 : Blo 271824 779051 := bstep (se 1 (by rfl) ⟨584288, by rfl⟩ : syracuseStep 779051 = 1168577) B1168577
theorem B4482053 : Blo 271824 4482053 := bstep (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) B840385
theorem B1041437 : Blo 271824 1041437 := bstep (se 3 (by rfl) ⟨195269, by rfl⟩ : syracuseStep 1041437 = 390539) B390539
theorem B615815 : Blo 271824 615815 := bstep (se 1 (by rfl) ⟨461861, by rfl⟩ : syracuseStep 615815 = 923723) B923723
theorem B8381875 : Blo 271824 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B1762859 : Blo 271824 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B615995 : Blo 271824 615995 := bstep (se 1 (by rfl) ⟨461996, by rfl⟩ : syracuseStep 615995 = 923993) B923993
theorem B616121 : Blo 271824 616121 := bstep (se 2 (by rfl) ⟨231045, by rfl⟩ : syracuseStep 616121 = 462091) B462091
theorem B780167 : Blo 271824 780167 := bstep (se 1 (by rfl) ⟨585125, by rfl⟩ : syracuseStep 780167 = 1170251) B1170251
theorem B616463 : Blo 271824 616463 := bstep (se 1 (by rfl) ⟨462347, by rfl⟩ : syracuseStep 616463 = 924695) B924695
theorem B616481 : Blo 271824 616481 := bstep (se 2 (by rfl) ⟨231180, by rfl⟩ : syracuseStep 616481 = 462361) B462361
theorem B780349 : Blo 271824 780349 := bstep (se 3 (by rfl) ⟨146315, by rfl⟩ : syracuseStep 780349 = 292631) B292631
theorem B616823 : Blo 271824 616823 := bstep (se 1 (by rfl) ⟨462617, by rfl⟩ : syracuseStep 616823 = 925235) B925235
theorem B780691 : Blo 271824 780691 := bstep (se 1 (by rfl) ⟨585518, by rfl⟩ : syracuseStep 780691 = 1171037) B1171037
theorem B518699 : Blo 271824 518699 := bstep (se 1 (by rfl) ⟨389024, by rfl⟩ : syracuseStep 518699 = 778049) B778049
theorem B617003 : Blo 271824 617003 := bstep (se 1 (by rfl) ⟨462752, by rfl⟩ : syracuseStep 617003 = 925505) B925505
theorem B387703 : Blo 271824 387703 := bstep (se 1 (by rfl) ⟨290777, by rfl⟩ : syracuseStep 387703 = 581555) B581555
theorem B1043063 : Blo 271824 1043063 := bstep (se 1 (by rfl) ⟨782297, by rfl⟩ : syracuseStep 1043063 = 1564595) B1564595
theorem B584339 : Blo 271824 584339 := bstep (se 1 (by rfl) ⟨438254, by rfl⟩ : syracuseStep 584339 = 876509) B876509
theorem B617363 : Blo 271824 617363 := bstep (se 1 (by rfl) ⟨463022, by rfl⟩ : syracuseStep 617363 = 926045) B926045
theorem B617417 : Blo 271824 617417 := bstep (se 2 (by rfl) ⟨231531, by rfl⟩ : syracuseStep 617417 = 463063) B463063
theorem B781579 : Blo 271824 781579 := bstep (se 1 (by rfl) ⟨586184, by rfl⟩ : syracuseStep 781579 = 1172369) B1172369
theorem B2354579 : Blo 271824 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B388523 : Blo 271824 388523 := bstep (se 1 (by rfl) ⟨291392, by rfl⟩ : syracuseStep 388523 = 582785) B582785
theorem B519625 : Blo 271824 519625 := bstep (se 2 (by rfl) ⟨194859, by rfl⟩ : syracuseStep 519625 = 389719) B389719
theorem B1044035 : Blo 271824 1044035 := bstep (se 1 (by rfl) ⟨783026, by rfl⟩ : syracuseStep 1044035 = 1566053) B1566053
theorem B618119 : Blo 271824 618119 := bstep (se 1 (by rfl) ⟨463589, by rfl⟩ : syracuseStep 618119 = 927179) B927179
theorem B782081 : Blo 271824 782081 := bstep (se 2 (by rfl) ⟨293280, by rfl⟩ : syracuseStep 782081 = 586561) B586561
theorem B1240847 : Blo 271824 1240847 := bstep (se 1 (by rfl) ⟨930635, by rfl⟩ : syracuseStep 1240847 = 1861271) B1861271
theorem B618299 : Blo 271824 618299 := bstep (se 1 (by rfl) ⟨463724, by rfl⟩ : syracuseStep 618299 = 927449) B927449
theorem B1175411 : Blo 271824 1175411 := bstep (se 1 (by rfl) ⟨881558, by rfl⟩ : syracuseStep 1175411 = 1763117) B1763117
theorem B421775 : Blo 271824 421775 := bstep (se 1 (by rfl) ⟨316331, by rfl⟩ : syracuseStep 421775 = 632663) B632663
theorem B618425 : Blo 271824 618425 := bstep (se 2 (by rfl) ⟨231909, by rfl⟩ : syracuseStep 618425 = 463819) B463819
theorem B782423 : Blo 271824 782423 := bstep (se 1 (by rfl) ⟨586817, by rfl⟩ : syracuseStep 782423 = 1173635) B1173635
theorem B520339 : Blo 271824 520339 := bstep (se 1 (by rfl) ⟨390254, by rfl⟩ : syracuseStep 520339 = 780509) B780509
theorem B585929 : Blo 271824 585929 := bstep (se 2 (by rfl) ⟨219723, by rfl⟩ : syracuseStep 585929 = 439447) B439447
theorem B1568969 : Blo 271824 1568969 := bstep (se 2 (by rfl) ⟨588363, by rfl⟩ : syracuseStep 1568969 = 1176727) B1176727
theorem B1765577 : Blo 271824 1765577 := bstep (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) B1324183
theorem B618767 : Blo 271824 618767 := bstep (se 1 (by rfl) ⟨464075, by rfl⟩ : syracuseStep 618767 = 928151) B928151
theorem B618785 : Blo 271824 618785 := bstep (se 2 (by rfl) ⟨232044, by rfl⟩ : syracuseStep 618785 = 464089) B464089
theorem B2355641 : Blo 271824 2355641 := bstep (se 2 (by rfl) ⟨883365, by rfl⟩ : syracuseStep 2355641 = 1766731) B1766731
theorem B1045021 : Blo 271824 1045021 := bstep (se 3 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 1045021 = 391883) B391883
theorem B619127 : Blo 271824 619127 := bstep (se 1 (by rfl) ⟨464345, by rfl⟩ : syracuseStep 619127 = 928691) B928691
theorem B2093687 : Blo 271824 2093687 := bstep (se 1 (by rfl) ⟨1570265, by rfl⟩ : syracuseStep 2093687 = 3140531) B3140531
theorem B619307 : Blo 271824 619307 := bstep (se 1 (by rfl) ⟨464480, by rfl⟩ : syracuseStep 619307 = 928961) B928961
theorem B389947 : Blo 271824 389947 := bstep (se 1 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 389947 = 584921) B584921
theorem B2946071 : Blo 271824 2946071 := bstep (se 1 (by rfl) ⟨2209553, by rfl⟩ : syracuseStep 2946071 = 4419107) B4419107
theorem B619667 : Blo 271824 619667 := bstep (se 1 (by rfl) ⟨464750, by rfl⟩ : syracuseStep 619667 = 929501) B929501
theorem B521417 : Blo 271824 521417 := bstep (se 2 (by rfl) ⟨195531, by rfl⟩ : syracuseStep 521417 = 391063) B391063
theorem B619721 : Blo 271824 619721 := bstep (se 2 (by rfl) ⟨232395, by rfl⟩ : syracuseStep 619721 = 464791) B464791
theorem B587449 : Blo 271824 587449 := bstep (se 2 (by rfl) ⟨220293, by rfl⟩ : syracuseStep 587449 = 440587) B440587
theorem B1177325 : Blo 271824 1177325 := bstep (se 3 (by rfl) ⟨220748, by rfl⟩ : syracuseStep 1177325 = 441497) B441497
theorem B620423 : Blo 271824 620423 := bstep (se 1 (by rfl) ⟨465317, by rfl⟩ : syracuseStep 620423 = 930635) B930635
theorem B784313 : Blo 271824 784313 := bstep (se 2 (by rfl) ⟨294117, by rfl⟩ : syracuseStep 784313 = 588235) B588235
theorem B522283 : Blo 271824 522283 := bstep (se 1 (by rfl) ⟨391712, by rfl⟩ : syracuseStep 522283 = 783425) B783425
theorem B1570859 : Blo 271824 1570859 := bstep (se 1 (by rfl) ⟨1178144, by rfl⟩ : syracuseStep 1570859 = 2356289) B2356289
theorem B620603 : Blo 271824 620603 := bstep (se 1 (by rfl) ⟨465452, by rfl⟩ : syracuseStep 620603 = 930905) B930905
theorem B522359 : Blo 271824 522359 := bstep (se 1 (by rfl) ⟨391769, by rfl⟩ : syracuseStep 522359 = 783539) B783539
theorem B587911 : Blo 271824 587911 := bstep (se 1 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 587911 = 881867) B881867
theorem B981229 : Blo 271824 981229 := bstep (se 3 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 981229 = 367961) B367961
theorem B391439 : Blo 271824 391439 := bstep (se 1 (by rfl) ⟨293579, by rfl⟩ : syracuseStep 391439 = 587159) B587159
theorem B784673 : Blo 271824 784673 := bstep (se 2 (by rfl) ⟨294252, by rfl⟩ : syracuseStep 784673 = 588505) B588505
theorem B293263 : Blo 271824 293263 := bstep (se 1 (by rfl) ⟨219947, by rfl⟩ : syracuseStep 293263 = 439895) B439895
theorem B1178009 : Blo 271824 1178009 := bstep (se 2 (by rfl) ⟨441753, by rfl⟩ : syracuseStep 1178009 = 883507) B883507
theorem B293383 : Blo 271824 293383 := bstep (se 1 (by rfl) ⟨220037, by rfl⟩ : syracuseStep 293383 = 440075) B440075
theorem B1309421 : Blo 271824 1309421 := bstep (se 3 (by rfl) ⟨245516, by rfl⟩ : syracuseStep 1309421 = 491033) B491033
theorem B293639 : Blo 271824 293639 := bstep (se 1 (by rfl) ⟨220229, by rfl⟩ : syracuseStep 293639 = 440459) B440459
theorem B424711 : Blo 271824 424711 := bstep (se 1 (by rfl) ⟨318533, by rfl⟩ : syracuseStep 424711 = 637067) B637067
theorem B326587 : Blo 271824 326587 := bstep (se 1 (by rfl) ⟨244940, by rfl⟩ : syracuseStep 326587 = 489881) B489881
theorem B621611 : Blo 271824 621611 := bstep (se 1 (by rfl) ⟨466208, by rfl⟩ : syracuseStep 621611 = 932417) B932417
theorem B654635 : Blo 271824 654635 := bstep (se 1 (by rfl) ⟨490976, by rfl⟩ : syracuseStep 654635 = 981953) B981953
theorem B294203 : Blo 271824 294203 := bstep (se 1 (by rfl) ⟨220652, by rfl⟩ : syracuseStep 294203 = 441305) B441305
theorem B392521 : Blo 271824 392521 := bstep (se 2 (by rfl) ⟨147195, by rfl⟩ : syracuseStep 392521 = 294391) B294391
theorem B523667 : Blo 271824 523667 := bstep (se 1 (by rfl) ⟨392750, by rfl⟩ : syracuseStep 523667 = 785501) B785501
theorem B392635 : Blo 271824 392635 := bstep (se 1 (by rfl) ⟨294476, by rfl⟩ : syracuseStep 392635 = 588953) B588953
theorem B1114003 : Blo 271824 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B1965977 : Blo 271824 1965977 := bstep (se 2 (by rfl) ⟨737241, by rfl⟩ : syracuseStep 1965977 = 1474483) B1474483
theorem B4751257 : Blo 271824 4751257 := bstep (se 2 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 4751257 = 3563443) B3563443
theorem B688135 : Blo 271824 688135 := bstep (se 1 (by rfl) ⟨516101, by rfl⟩ : syracuseStep 688135 = 1032203) B1032203
theorem B458831 : Blo 271824 458831 := bstep (se 1 (by rfl) ⟨344123, by rfl⟩ : syracuseStep 458831 = 688247) B688247
theorem B917675 : Blo 271824 917675 := bstep (se 1 (by rfl) ⟨688256, by rfl⟩ : syracuseStep 917675 = 1376513) B1376513
theorem B688763 : Blo 271824 688763 := bstep (se 1 (by rfl) ⟨516572, by rfl⟩ : syracuseStep 688763 = 1033145) B1033145
theorem B918215 : Blo 271824 918215 := bstep (se 1 (by rfl) ⟨688661, by rfl⟩ : syracuseStep 918215 = 1377323) B1377323
theorem B689057 : Blo 271824 689057 := bstep (se 2 (by rfl) ⟨258396, by rfl⟩ : syracuseStep 689057 = 516793) B516793
theorem B459695 : Blo 271824 459695 := bstep (se 1 (by rfl) ⟨344771, by rfl⟩ : syracuseStep 459695 = 689543) B689543
theorem B984143 : Blo 271824 984143 := bstep (se 1 (by rfl) ⟨738107, by rfl⟩ : syracuseStep 984143 = 1476215) B1476215
theorem B460127 : Blo 271824 460127 := bstep (se 1 (by rfl) ⟨345095, by rfl⟩ : syracuseStep 460127 = 690191) B690191
theorem B26936725 : Blo 271824 26936725 := bstep (se 6 (by rfl) ⟨631329, by rfl⟩ : syracuseStep 26936725 = 1262659) B1262659
theorem B1181147 : Blo 271824 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B4752901 : Blo 271824 4752901 := bstep (se 4 (by rfl) ⟨445584, by rfl⟩ : syracuseStep 4752901 = 891169) B891169
theorem B919079 : Blo 271824 919079 := bstep (se 1 (by rfl) ⟨689309, by rfl⟩ : syracuseStep 919079 = 1378619) B1378619
theorem B919187 : Blo 271824 919187 := bstep (se 1 (by rfl) ⟨689390, by rfl⟩ : syracuseStep 919187 = 1378781) B1378781
theorem B919403 : Blo 271824 919403 := bstep (se 1 (by rfl) ⟨689552, by rfl⟩ : syracuseStep 919403 = 1379105) B1379105
theorem B460687 : Blo 271824 460687 := bstep (se 1 (by rfl) ⟨345515, by rfl⟩ : syracuseStep 460687 = 691031) B691031
theorem B11175833 : Blo 271824 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B919457 : Blo 271824 919457 := bstep (se 2 (by rfl) ⟨344796, by rfl⟩ : syracuseStep 919457 = 689593) B689593
theorem B5900525 : Blo 271824 5900525 := bstep (se 3 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 5900525 = 2212697) B2212697
theorem B1870091 : Blo 271824 1870091 := bstep (se 1 (by rfl) ⟨1402568, by rfl⟩ : syracuseStep 1870091 = 2805137) B2805137
theorem B1313111 : Blo 271824 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B920051 : Blo 271824 920051 := bstep (se 1 (by rfl) ⟨690038, by rfl⟩ : syracuseStep 920051 = 1380077) B1380077
theorem B690727 : Blo 271824 690727 := bstep (se 1 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 690727 = 1036091) B1036091
theorem B461369 : Blo 271824 461369 := bstep (se 2 (by rfl) ⟨173013, by rfl⟩ : syracuseStep 461369 = 346027) B346027
theorem B1116857 : Blo 271824 1116857 := bstep (se 2 (by rfl) ⟨418821, by rfl⟩ : syracuseStep 1116857 = 837643) B837643
theorem B1477379 : Blo 271824 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B691051 : Blo 271824 691051 := bstep (se 1 (by rfl) ⟨518288, by rfl⟩ : syracuseStep 691051 = 1036577) B1036577
theorem B920591 : Blo 271824 920591 := bstep (se 1 (by rfl) ⟨690443, by rfl⟩ : syracuseStep 920591 = 1380887) B1380887
theorem B1313995 : Blo 271824 1313995 := bstep (se 1 (by rfl) ⟨985496, by rfl⟩ : syracuseStep 1313995 = 1970993) B1970993
theorem B462071 : Blo 271824 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B494839 : Blo 271824 494839 := bstep (se 1 (by rfl) ⟨371129, by rfl⟩ : syracuseStep 494839 = 742259) B742259
theorem B626063 : Blo 271824 626063 := bstep (se 1 (by rfl) ⟨469547, by rfl⟩ : syracuseStep 626063 = 939095) B939095
theorem B691699 : Blo 271824 691699 := bstep (se 1 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 691699 = 1037549) B1037549
theorem B462415 : Blo 271824 462415 := bstep (se 1 (by rfl) ⟨346811, by rfl⟩ : syracuseStep 462415 = 693623) B693623
theorem B921185 : Blo 271824 921185 := bstep (se 2 (by rfl) ⟨345444, by rfl⟩ : syracuseStep 921185 = 690889) B690889
theorem B1412747 : Blo 271824 1412747 := bstep (se 1 (by rfl) ⟨1059560, by rfl⟩ : syracuseStep 1412747 = 2119121) B2119121
theorem B462665 : Blo 271824 462665 := bstep (se 2 (by rfl) ⟨173499, by rfl⟩ : syracuseStep 462665 = 346999) B346999
theorem B463097 : Blo 271824 463097 := bstep (se 2 (by rfl) ⟨173661, by rfl⟩ : syracuseStep 463097 = 347323) B347323
theorem B2101565 : Blo 271824 2101565 := bstep (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) B788087
theorem B463279 : Blo 271824 463279 := bstep (se 1 (by rfl) ⟨347459, by rfl⟩ : syracuseStep 463279 = 694919) B694919
theorem B463367 : Blo 271824 463367 := bstep (se 1 (by rfl) ⟨347525, by rfl⟩ : syracuseStep 463367 = 695051) B695051
theorem B692833 : Blo 271824 692833 := bstep (se 2 (by rfl) ⟨259812, by rfl⟩ : syracuseStep 692833 = 519625) B519625
theorem B1381049 : Blo 271824 1381049 := bstep (se 2 (by rfl) ⟨517893, by rfl⟩ : syracuseStep 1381049 = 1035787) B1035787
theorem B987977 : Blo 271824 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B463711 : Blo 271824 463711 := bstep (se 1 (by rfl) ⟨347783, by rfl⟩ : syracuseStep 463711 = 695567) B695567
theorem B463799 : Blo 271824 463799 := bstep (se 1 (by rfl) ⟨347849, by rfl⟩ : syracuseStep 463799 = 695699) B695699
theorem B922643 : Blo 271824 922643 := bstep (se 1 (by rfl) ⟨691982, by rfl⟩ : syracuseStep 922643 = 1383965) B1383965
theorem B660727 : Blo 271824 660727 := bstep (se 1 (by rfl) ⟨495545, by rfl⟩ : syracuseStep 660727 = 991091) B991091
theorem B922967 : Blo 271824 922967 := bstep (se 1 (by rfl) ⟨692225, by rfl⟩ : syracuseStep 922967 = 1384451) B1384451
theorem B464393 : Blo 271824 464393 := bstep (se 2 (by rfl) ⟨174147, by rfl⟩ : syracuseStep 464393 = 348295) B348295
theorem B693785 : Blo 271824 693785 := bstep (se 2 (by rfl) ⟨260169, by rfl⟩ : syracuseStep 693785 = 520339) B520339
theorem B464555 : Blo 271824 464555 := bstep (se 1 (by rfl) ⟨348416, by rfl⟩ : syracuseStep 464555 = 696833) B696833
theorem B2988035 : Blo 271824 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B694291 : Blo 271824 694291 := bstep (se 1 (by rfl) ⟨520718, by rfl⟩ : syracuseStep 694291 = 1041437) B1041437
theorem B2332709 : Blo 271824 2332709 := bstep (se 4 (by rfl) ⟨218691, by rfl⟩ : syracuseStep 2332709 = 437383) B437383
theorem B464953 : Blo 271824 464953 := bstep (se 2 (by rfl) ⟨174357, by rfl⟩ : syracuseStep 464953 = 348715) B348715
theorem B465095 : Blo 271824 465095 := bstep (se 1 (by rfl) ⟨348821, by rfl⟩ : syracuseStep 465095 = 697643) B697643
theorem B2070845 : Blo 271824 2070845 := bstep (se 3 (by rfl) ⟨388283, by rfl⟩ : syracuseStep 2070845 = 776567) B776567
theorem B465257 : Blo 271824 465257 := bstep (se 2 (by rfl) ⟨174471, by rfl⟩ : syracuseStep 465257 = 348943) B348943
theorem B2234753 : Blo 271824 2234753 := bstep (se 2 (by rfl) ⟨838032, by rfl⟩ : syracuseStep 2234753 = 1676065) B1676065
theorem B924047 : Blo 271824 924047 := bstep (se 1 (by rfl) ⟨693035, by rfl⟩ : syracuseStep 924047 = 1386071) B1386071
theorem B596603 : Blo 271824 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B924371 : Blo 271824 924371 := bstep (se 1 (by rfl) ⟨693278, by rfl⟩ : syracuseStep 924371 = 1386557) B1386557
theorem B1973069 : Blo 271824 1973069 := bstep (se 3 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 1973069 = 739901) B739901
theorem B695375 : Blo 271824 695375 := bstep (se 1 (by rfl) ⟨521531, by rfl⟩ : syracuseStep 695375 = 1043063) B1043063
theorem B466319 : Blo 271824 466319 := bstep (se 1 (by rfl) ⟨349739, by rfl⟩ : syracuseStep 466319 = 699479) B699479
theorem B3743119 : Blo 271824 3743119 := bstep (se 1 (by rfl) ⟨2807339, by rfl⟩ : syracuseStep 3743119 = 5614679) B5614679
theorem B696023 : Blo 271824 696023 := bstep (se 1 (by rfl) ⟨522017, by rfl⟩ : syracuseStep 696023 = 1044035) B1044035
theorem B7020269 : Blo 271824 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B827231 : Blo 271824 827231 := bstep (se 1 (by rfl) ⟨620423, by rfl⟩ : syracuseStep 827231 = 1240847) B1240847
theorem B466795 : Blo 271824 466795 := bstep (se 1 (by rfl) ⟨350096, by rfl⟩ : syracuseStep 466795 = 700193) B700193
theorem B925559 : Blo 271824 925559 := bstep (se 1 (by rfl) ⟨694169, by rfl⟩ : syracuseStep 925559 = 1388339) B1388339
theorem B696377 : Blo 271824 696377 := bstep (se 2 (by rfl) ⟨261141, by rfl⟩ : syracuseStep 696377 = 522283) B522283
theorem B925775 : Blo 271824 925775 := bstep (se 1 (by rfl) ⟨694331, by rfl⟩ : syracuseStep 925775 = 1388663) B1388663
theorem B1253693 : Blo 271824 1253693 := bstep (se 3 (by rfl) ⟨235067, by rfl⟩ : syracuseStep 1253693 = 470135) B470135
theorem B1122761 : Blo 271824 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B926153 : Blo 271824 926153 := bstep (se 2 (by rfl) ⟨347307, by rfl⟩ : syracuseStep 926153 = 694615) B694615
theorem B926423 : Blo 271824 926423 := bstep (se 1 (by rfl) ⟨694817, by rfl⟩ : syracuseStep 926423 = 1389635) B1389635
theorem B926639 : Blo 271824 926639 := bstep (se 1 (by rfl) ⟨694979, by rfl⟩ : syracuseStep 926639 = 1389959) B1389959
theorem B1451009 : Blo 271824 1451009 := bstep (se 2 (by rfl) ⟨544128, by rfl⟩ : syracuseStep 1451009 = 1088257) B1088257
theorem B566281 : Blo 271824 566281 := bstep (se 2 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 566281 = 424711) B424711
theorem B435449 : Blo 271824 435449 := bstep (se 2 (by rfl) ⟨163293, by rfl⟩ : syracuseStep 435449 = 326587) B326587
theorem B271835 : Blo 271824 271835 := bstep (se 1 (by rfl) ⟨203876, by rfl⟩ : syracuseStep 271835 = 407753) B407753
theorem B271911 : Blo 271824 271911 := bstep (se 1 (by rfl) ⟨203933, by rfl⟩ : syracuseStep 271911 = 407867) B407867
theorem B271951 : Blo 271824 271951 := bstep (se 1 (by rfl) ⟨203963, by rfl⟩ : syracuseStep 271951 = 407927) B407927
theorem B271967 : Blo 271824 271967 := bstep (se 1 (by rfl) ⟨203975, by rfl⟩ : syracuseStep 271967 = 407951) B407951
theorem B271995 : Blo 271824 271995 := bstep (se 1 (by rfl) ⟨203996, by rfl⟩ : syracuseStep 271995 = 407993) B407993
theorem B272047 : Blo 271824 272047 := bstep (se 1 (by rfl) ⟨204035, by rfl⟩ : syracuseStep 272047 = 408071) B408071
theorem B272071 : Blo 271824 272071 := bstep (se 1 (by rfl) ⟨204053, by rfl⟩ : syracuseStep 272071 = 408107) B408107
theorem B35923661 : Blo 271824 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B272091 : Blo 271824 272091 := bstep (se 1 (by rfl) ⟨204068, by rfl⟩ : syracuseStep 272091 = 408137) B408137
theorem B1386233 : Blo 271824 1386233 := bstep (se 2 (by rfl) ⟨519837, by rfl⟩ : syracuseStep 1386233 = 1039675) B1039675
theorem B272167 : Blo 271824 272167 := bstep (se 1 (by rfl) ⟨204125, by rfl⟩ : syracuseStep 272167 = 408251) B408251
theorem B272207 : Blo 271824 272207 := bstep (se 1 (by rfl) ⟨204155, by rfl⟩ : syracuseStep 272207 = 408311) B408311
theorem B272223 : Blo 271824 272223 := bstep (se 1 (by rfl) ⟨204167, by rfl⟩ : syracuseStep 272223 = 408335) B408335
theorem B1976183 : Blo 271824 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B272251 : Blo 271824 272251 := bstep (se 1 (by rfl) ⟨204188, by rfl⟩ : syracuseStep 272251 = 408377) B408377
theorem B272303 : Blo 271824 272303 := bstep (se 1 (by rfl) ⟨204227, by rfl⟩ : syracuseStep 272303 = 408455) B408455
theorem B272327 : Blo 271824 272327 := bstep (se 1 (by rfl) ⟨204245, by rfl⟩ : syracuseStep 272327 = 408491) B408491
theorem B272347 : Blo 271824 272347 := bstep (se 1 (by rfl) ⟨204260, by rfl⟩ : syracuseStep 272347 = 408521) B408521
theorem B272423 : Blo 271824 272423 := bstep (se 1 (by rfl) ⟨204317, by rfl⟩ : syracuseStep 272423 = 408635) B408635
theorem B272463 : Blo 271824 272463 := bstep (se 1 (by rfl) ⟨204347, by rfl⟩ : syracuseStep 272463 = 408695) B408695
theorem B272479 : Blo 271824 272479 := bstep (se 1 (by rfl) ⟨204359, by rfl⟩ : syracuseStep 272479 = 408719) B408719
theorem B5941349 : Blo 271824 5941349 := bstep (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) B1114003
theorem B272507 : Blo 271824 272507 := bstep (se 1 (by rfl) ⟨204380, by rfl⟩ : syracuseStep 272507 = 408761) B408761
theorem B272559 : Blo 271824 272559 := bstep (se 1 (by rfl) ⟨204419, by rfl⟩ : syracuseStep 272559 = 408839) B408839
theorem B436423 : Blo 271824 436423 := bstep (se 1 (by rfl) ⟨327317, by rfl⟩ : syracuseStep 436423 = 654635) B654635
theorem B272583 : Blo 271824 272583 := bstep (se 1 (by rfl) ⟨204437, by rfl⟩ : syracuseStep 272583 = 408875) B408875
theorem B272603 : Blo 271824 272603 := bstep (se 1 (by rfl) ⟨204452, by rfl⟩ : syracuseStep 272603 = 408905) B408905
theorem B272679 : Blo 271824 272679 := bstep (se 1 (by rfl) ⟨204509, by rfl⟩ : syracuseStep 272679 = 409019) B409019
theorem B272719 : Blo 271824 272719 := bstep (se 1 (by rfl) ⟨204539, by rfl⟩ : syracuseStep 272719 = 409079) B409079
theorem B272735 : Blo 271824 272735 := bstep (se 1 (by rfl) ⟨204551, by rfl⟩ : syracuseStep 272735 = 409103) B409103
theorem B272763 : Blo 271824 272763 := bstep (se 1 (by rfl) ⟨204572, by rfl⟩ : syracuseStep 272763 = 409145) B409145
theorem B1386881 : Blo 271824 1386881 := bstep (se 2 (by rfl) ⟨520080, by rfl⟩ : syracuseStep 1386881 = 1040161) B1040161
theorem B272815 : Blo 271824 272815 := bstep (se 1 (by rfl) ⟨204611, by rfl⟩ : syracuseStep 272815 = 409223) B409223
theorem B272839 : Blo 271824 272839 := bstep (se 1 (by rfl) ⟨204629, by rfl⟩ : syracuseStep 272839 = 409259) B409259
theorem B272859 : Blo 271824 272859 := bstep (se 1 (by rfl) ⟨204644, by rfl⟩ : syracuseStep 272859 = 409289) B409289
theorem B6335009 : Blo 271824 6335009 := bstep (se 2 (by rfl) ⟨2375628, by rfl⟩ : syracuseStep 6335009 = 4751257) B4751257
theorem B272935 : Blo 271824 272935 := bstep (se 1 (by rfl) ⟨204701, by rfl⟩ : syracuseStep 272935 = 409403) B409403
theorem B272975 : Blo 271824 272975 := bstep (se 1 (by rfl) ⟨204731, by rfl⟩ : syracuseStep 272975 = 409463) B409463
theorem B272991 : Blo 271824 272991 := bstep (se 1 (by rfl) ⟨204743, by rfl⟩ : syracuseStep 272991 = 409487) B409487
theorem B273019 : Blo 271824 273019 := bstep (se 1 (by rfl) ⟨204764, by rfl⟩ : syracuseStep 273019 = 409529) B409529
theorem B273071 : Blo 271824 273071 := bstep (se 1 (by rfl) ⟨204803, by rfl⟩ : syracuseStep 273071 = 409607) B409607
theorem B273095 : Blo 271824 273095 := bstep (se 1 (by rfl) ⟨204821, by rfl⟩ : syracuseStep 273095 = 409643) B409643
theorem B273115 : Blo 271824 273115 := bstep (se 1 (by rfl) ⟨204836, by rfl⟩ : syracuseStep 273115 = 409673) B409673
theorem B273191 : Blo 271824 273191 := bstep (se 1 (by rfl) ⟨204893, by rfl⟩ : syracuseStep 273191 = 409787) B409787
theorem B6007621 : Blo 271824 6007621 := bstep (se 4 (by rfl) ⟨563214, by rfl⟩ : syracuseStep 6007621 = 1126429) B1126429
theorem B699209 : Blo 271824 699209 := bstep (se 2 (by rfl) ⟨262203, by rfl⟩ : syracuseStep 699209 = 524407) B524407
theorem B273231 : Blo 271824 273231 := bstep (se 1 (by rfl) ⟨204923, by rfl⟩ : syracuseStep 273231 = 409847) B409847
theorem B371551 : Blo 271824 371551 := bstep (se 1 (by rfl) ⟨278663, by rfl⟩ : syracuseStep 371551 = 557327) B557327
theorem B273247 : Blo 271824 273247 := bstep (se 1 (by rfl) ⟨204935, by rfl⟩ : syracuseStep 273247 = 409871) B409871
theorem B469855 : Blo 271824 469855 := bstep (se 1 (by rfl) ⟨352391, by rfl⟩ : syracuseStep 469855 = 704783) B704783
theorem B273275 : Blo 271824 273275 := bstep (se 1 (by rfl) ⟨204956, by rfl⟩ : syracuseStep 273275 = 409913) B409913
theorem B3353491 : Blo 271824 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B273327 : Blo 271824 273327 := bstep (se 1 (by rfl) ⟨204995, by rfl⟩ : syracuseStep 273327 = 409991) B409991
theorem B273351 : Blo 271824 273351 := bstep (se 1 (by rfl) ⟨205013, by rfl⟩ : syracuseStep 273351 = 410027) B410027
theorem B306139 : Blo 271824 306139 := bstep (se 1 (by rfl) ⟨229604, by rfl⟩ : syracuseStep 306139 = 459209) B459209
theorem B273371 : Blo 271824 273371 := bstep (se 1 (by rfl) ⟨205028, by rfl⟩ : syracuseStep 273371 = 410057) B410057
theorem B273447 : Blo 271824 273447 := bstep (se 1 (by rfl) ⟨205085, by rfl⟩ : syracuseStep 273447 = 410171) B410171
theorem B273487 : Blo 271824 273487 := bstep (se 1 (by rfl) ⟨205115, by rfl⟩ : syracuseStep 273487 = 410231) B410231
theorem B273503 : Blo 271824 273503 := bstep (se 1 (by rfl) ⟨205127, by rfl⟩ : syracuseStep 273503 = 410255) B410255
theorem B273531 : Blo 271824 273531 := bstep (se 1 (by rfl) ⟨205148, by rfl⟩ : syracuseStep 273531 = 410297) B410297
theorem B1387691 : Blo 271824 1387691 := bstep (se 1 (by rfl) ⟨1040768, by rfl⟩ : syracuseStep 1387691 = 2081537) B2081537
theorem B273583 : Blo 271824 273583 := bstep (se 1 (by rfl) ⟨205187, by rfl⟩ : syracuseStep 273583 = 410375) B410375
theorem B273607 : Blo 271824 273607 := bstep (se 1 (by rfl) ⟨205205, by rfl⟩ : syracuseStep 273607 = 410411) B410411
theorem B273627 : Blo 271824 273627 := bstep (se 1 (by rfl) ⟨205220, by rfl⟩ : syracuseStep 273627 = 410441) B410441
theorem B929015 : Blo 271824 929015 := bstep (se 1 (by rfl) ⟨696761, by rfl⟩ : syracuseStep 929015 = 1393523) B1393523
theorem B273703 : Blo 271824 273703 := bstep (se 1 (by rfl) ⟨205277, by rfl⟩ : syracuseStep 273703 = 410555) B410555
theorem B273743 : Blo 271824 273743 := bstep (se 1 (by rfl) ⟨205307, by rfl⟩ : syracuseStep 273743 = 410615) B410615
theorem B273759 : Blo 271824 273759 := bstep (se 1 (by rfl) ⟨205319, by rfl⟩ : syracuseStep 273759 = 410639) B410639
theorem B273787 : Blo 271824 273787 := bstep (se 1 (by rfl) ⟨205340, by rfl⟩ : syracuseStep 273787 = 410681) B410681
theorem B306607 : Blo 271824 306607 := bstep (se 1 (by rfl) ⟨229955, by rfl⟩ : syracuseStep 306607 = 459911) B459911
theorem B273839 : Blo 271824 273839 := bstep (se 1 (by rfl) ⟨205379, by rfl⟩ : syracuseStep 273839 = 410759) B410759
theorem B273863 : Blo 271824 273863 := bstep (se 1 (by rfl) ⟨205397, by rfl⟩ : syracuseStep 273863 = 410795) B410795
theorem B273883 : Blo 271824 273883 := bstep (se 1 (by rfl) ⟨205412, by rfl⟩ : syracuseStep 273883 = 410825) B410825
theorem B273959 : Blo 271824 273959 := bstep (se 1 (by rfl) ⟨205469, by rfl⟩ : syracuseStep 273959 = 410939) B410939
theorem B929339 : Blo 271824 929339 := bstep (se 1 (by rfl) ⟨697004, by rfl⟩ : syracuseStep 929339 = 1394009) B1394009
theorem B273999 : Blo 271824 273999 := bstep (se 1 (by rfl) ⟨205499, by rfl⟩ : syracuseStep 273999 = 410999) B410999
theorem B274015 : Blo 271824 274015 := bstep (se 1 (by rfl) ⟨205511, by rfl⟩ : syracuseStep 274015 = 411023) B411023
theorem B274043 : Blo 271824 274043 := bstep (se 1 (by rfl) ⟨205532, by rfl⟩ : syracuseStep 274043 = 411065) B411065
theorem B1388177 : Blo 271824 1388177 := bstep (se 2 (by rfl) ⟨520566, by rfl⟩ : syracuseStep 1388177 = 1041133) B1041133
theorem B1060499 : Blo 271824 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B274095 : Blo 271824 274095 := bstep (se 1 (by rfl) ⟨205571, by rfl⟩ : syracuseStep 274095 = 411143) B411143
theorem B274119 : Blo 271824 274119 := bstep (se 1 (by rfl) ⟨205589, by rfl⟩ : syracuseStep 274119 = 411179) B411179
theorem B274139 : Blo 271824 274139 := bstep (se 1 (by rfl) ⟨205604, by rfl⟩ : syracuseStep 274139 = 411209) B411209
theorem B274215 : Blo 271824 274215 := bstep (se 1 (by rfl) ⟨205661, by rfl⟩ : syracuseStep 274215 = 411323) B411323
theorem B929609 : Blo 271824 929609 := bstep (se 2 (by rfl) ⟨348603, by rfl⟩ : syracuseStep 929609 = 697207) B697207
theorem B274255 : Blo 271824 274255 := bstep (se 1 (by rfl) ⟨205691, by rfl⟩ : syracuseStep 274255 = 411383) B411383
theorem B1552223 : Blo 271824 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B307039 : Blo 271824 307039 := bstep (se 1 (by rfl) ⟨230279, by rfl⟩ : syracuseStep 307039 = 460559) B460559
theorem B274271 : Blo 271824 274271 := bstep (se 1 (by rfl) ⟨205703, by rfl⟩ : syracuseStep 274271 = 411407) B411407
theorem B274299 : Blo 271824 274299 := bstep (se 1 (by rfl) ⟨205724, by rfl⟩ : syracuseStep 274299 = 411449) B411449
theorem B274351 : Blo 271824 274351 := bstep (se 1 (by rfl) ⟨205763, by rfl⟩ : syracuseStep 274351 = 411527) B411527
theorem B634807 : Blo 271824 634807 := bstep (se 1 (by rfl) ⟨476105, by rfl⟩ : syracuseStep 634807 = 952211) B952211
theorem B274375 : Blo 271824 274375 := bstep (se 1 (by rfl) ⟨205781, by rfl⟩ : syracuseStep 274375 = 411563) B411563
theorem B274395 : Blo 271824 274395 := bstep (se 1 (by rfl) ⟨205796, by rfl⟩ : syracuseStep 274395 = 411593) B411593
theorem B438281 : Blo 271824 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B274471 : Blo 271824 274471 := bstep (se 1 (by rfl) ⟨205853, by rfl⟩ : syracuseStep 274471 = 411707) B411707
theorem B274511 : Blo 271824 274511 := bstep (se 1 (by rfl) ⟨205883, by rfl⟩ : syracuseStep 274511 = 411767) B411767
theorem B274527 : Blo 271824 274527 := bstep (se 1 (by rfl) ⟨205895, by rfl⟩ : syracuseStep 274527 = 411791) B411791
theorem B3321971 : Blo 271824 3321971 := bstep (se 1 (by rfl) ⟨2491478, by rfl⟩ : syracuseStep 3321971 = 4982957) B4982957
theorem B274555 : Blo 271824 274555 := bstep (se 1 (by rfl) ⟨205916, by rfl⟩ : syracuseStep 274555 = 411833) B411833
theorem B274607 : Blo 271824 274607 := bstep (se 1 (by rfl) ⟨205955, by rfl⟩ : syracuseStep 274607 = 411911) B411911
theorem B307399 : Blo 271824 307399 := bstep (se 1 (by rfl) ⟨230549, by rfl⟩ : syracuseStep 307399 = 461099) B461099
theorem B274631 : Blo 271824 274631 := bstep (se 1 (by rfl) ⟨205973, by rfl⟩ : syracuseStep 274631 = 411947) B411947
theorem B274651 : Blo 271824 274651 := bstep (se 1 (by rfl) ⟨205988, by rfl⟩ : syracuseStep 274651 = 411977) B411977
theorem B274727 : Blo 271824 274727 := bstep (se 1 (by rfl) ⟨206045, by rfl⟩ : syracuseStep 274727 = 412091) B412091
theorem B274767 : Blo 271824 274767 := bstep (se 1 (by rfl) ⟨206075, by rfl⟩ : syracuseStep 274767 = 412151) B412151
theorem B274783 : Blo 271824 274783 := bstep (se 1 (by rfl) ⟨206087, by rfl⟩ : syracuseStep 274783 = 412175) B412175
theorem B274811 : Blo 271824 274811 := bstep (se 1 (by rfl) ⟨206108, by rfl⟩ : syracuseStep 274811 = 412217) B412217
theorem B274863 : Blo 271824 274863 := bstep (se 1 (by rfl) ⟨206147, by rfl⟩ : syracuseStep 274863 = 412295) B412295
theorem B274887 : Blo 271824 274887 := bstep (se 1 (by rfl) ⟨206165, by rfl⟩ : syracuseStep 274887 = 412331) B412331
theorem B274907 : Blo 271824 274907 := bstep (se 1 (by rfl) ⟨206180, by rfl⟩ : syracuseStep 274907 = 412361) B412361
theorem B3944983 : Blo 271824 3944983 := bstep (se 1 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 3944983 = 5917475) B5917475
theorem B274983 : Blo 271824 274983 := bstep (se 1 (by rfl) ⟨206237, by rfl⟩ : syracuseStep 274983 = 412475) B412475
theorem B275023 : Blo 271824 275023 := bstep (se 1 (by rfl) ⟨206267, by rfl⟩ : syracuseStep 275023 = 412535) B412535
theorem B275039 : Blo 271824 275039 := bstep (se 1 (by rfl) ⟨206279, by rfl⟩ : syracuseStep 275039 = 412559) B412559
theorem B832123 : Blo 271824 832123 := bstep (se 1 (by rfl) ⟨624092, by rfl⟩ : syracuseStep 832123 = 1248185) B1248185
theorem B275067 : Blo 271824 275067 := bstep (se 1 (by rfl) ⟨206300, by rfl⟩ : syracuseStep 275067 = 412601) B412601
theorem B275119 : Blo 271824 275119 := bstep (se 1 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 275119 = 412679) B412679
theorem B275143 : Blo 271824 275143 := bstep (se 1 (by rfl) ⟨206357, by rfl⟩ : syracuseStep 275143 = 412715) B412715
theorem B275163 : Blo 271824 275163 := bstep (se 1 (by rfl) ⟨206372, by rfl⟩ : syracuseStep 275163 = 412745) B412745
theorem B9679621 : Blo 271824 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B275239 : Blo 271824 275239 := bstep (se 1 (by rfl) ⟨206429, by rfl⟩ : syracuseStep 275239 = 412859) B412859
theorem B275279 : Blo 271824 275279 := bstep (se 1 (by rfl) ⟨206459, by rfl⟩ : syracuseStep 275279 = 412919) B412919
theorem B275295 : Blo 271824 275295 := bstep (se 1 (by rfl) ⟨206471, by rfl⟩ : syracuseStep 275295 = 412943) B412943
theorem B275323 : Blo 271824 275323 := bstep (se 1 (by rfl) ⟨206492, by rfl⟩ : syracuseStep 275323 = 412985) B412985
theorem B275375 : Blo 271824 275375 := bstep (se 1 (by rfl) ⟨206531, by rfl⟩ : syracuseStep 275375 = 413063) B413063
theorem B930743 : Blo 271824 930743 := bstep (se 1 (by rfl) ⟨698057, by rfl⟩ : syracuseStep 930743 = 1396115) B1396115
theorem B275399 : Blo 271824 275399 := bstep (se 1 (by rfl) ⟨206549, by rfl⟩ : syracuseStep 275399 = 413099) B413099
theorem B275419 : Blo 271824 275419 := bstep (se 1 (by rfl) ⟨206564, by rfl⟩ : syracuseStep 275419 = 413129) B413129
theorem B308263 : Blo 271824 308263 := bstep (se 1 (by rfl) ⟨231197, by rfl⟩ : syracuseStep 308263 = 462395) B462395
theorem B275495 : Blo 271824 275495 := bstep (se 1 (by rfl) ⟨206621, by rfl⟩ : syracuseStep 275495 = 413243) B413243
theorem B275535 : Blo 271824 275535 := bstep (se 1 (by rfl) ⟨206651, by rfl⟩ : syracuseStep 275535 = 413303) B413303
theorem B275551 : Blo 271824 275551 := bstep (se 1 (by rfl) ⟨206663, by rfl⟩ : syracuseStep 275551 = 413327) B413327
theorem B275579 : Blo 271824 275579 := bstep (se 1 (by rfl) ⟨206684, by rfl⟩ : syracuseStep 275579 = 413369) B413369
theorem B275631 : Blo 271824 275631 := bstep (se 1 (by rfl) ⟨206723, by rfl⟩ : syracuseStep 275631 = 413447) B413447
theorem B275655 : Blo 271824 275655 := bstep (se 1 (by rfl) ⟨206741, by rfl⟩ : syracuseStep 275655 = 413483) B413483
theorem B275675 : Blo 271824 275675 := bstep (se 1 (by rfl) ⟨206756, by rfl⟩ : syracuseStep 275675 = 413513) B413513
theorem B275751 : Blo 271824 275751 := bstep (se 1 (by rfl) ⟨206813, by rfl⟩ : syracuseStep 275751 = 413627) B413627
theorem B275791 : Blo 271824 275791 := bstep (se 1 (by rfl) ⟨206843, by rfl⟩ : syracuseStep 275791 = 413687) B413687
theorem B275807 : Blo 271824 275807 := bstep (se 1 (by rfl) ⟨206855, by rfl⟩ : syracuseStep 275807 = 413711) B413711
theorem B767497 : Blo 271824 767497 := bstep (se 2 (by rfl) ⟨287811, by rfl⟩ : syracuseStep 767497 = 575623) B575623
theorem B1390445 : Blo 271824 1390445 := bstep (se 3 (by rfl) ⟨260708, by rfl⟩ : syracuseStep 1390445 = 521417) B521417
theorem B1390607 : Blo 271824 1390607 := bstep (se 1 (by rfl) ⟨1042955, by rfl⟩ : syracuseStep 1390607 = 2085911) B2085911
theorem B407801 : Blo 271824 407801 := bstep (se 2 (by rfl) ⟨152925, by rfl⟩ : syracuseStep 407801 = 305851) B305851
theorem B407903 : Blo 271824 407903 := bstep (se 1 (by rfl) ⟨305927, by rfl⟩ : syracuseStep 407903 = 611855) B611855
theorem B407915 : Blo 271824 407915 := bstep (se 1 (by rfl) ⟨305936, by rfl⟩ : syracuseStep 407915 = 611873) B611873
theorem B408143 : Blo 271824 408143 := bstep (se 1 (by rfl) ⟨306107, by rfl⟩ : syracuseStep 408143 = 612215) B612215
theorem B309883 : Blo 271824 309883 := bstep (se 1 (by rfl) ⟨232412, by rfl⟩ : syracuseStep 309883 = 464825) B464825
theorem B408263 : Blo 271824 408263 := bstep (se 1 (by rfl) ⟨306197, by rfl⟩ : syracuseStep 408263 = 612395) B612395
theorem B408425 : Blo 271824 408425 := bstep (se 2 (by rfl) ⟨153159, by rfl⟩ : syracuseStep 408425 = 306319) B306319
theorem B408503 : Blo 271824 408503 := bstep (se 1 (by rfl) ⟨306377, by rfl⟩ : syracuseStep 408503 = 612755) B612755
theorem B408539 : Blo 271824 408539 := bstep (se 1 (by rfl) ⟨306404, by rfl⟩ : syracuseStep 408539 = 612809) B612809
theorem B7846955 : Blo 271824 7846955 := bstep (se 1 (by rfl) ⟨5885216, by rfl⟩ : syracuseStep 7846955 = 11770433) B11770433
theorem B834617 : Blo 271824 834617 := bstep (se 2 (by rfl) ⟨312981, by rfl⟩ : syracuseStep 834617 = 625963) B625963
theorem B1785253 : Blo 271824 1785253 := bstep (se 4 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 1785253 = 334735) B334735
theorem B409007 : Blo 271824 409007 := bstep (se 1 (by rfl) ⟨306755, by rfl⟩ : syracuseStep 409007 = 613511) B613511
theorem B409097 : Blo 271824 409097 := bstep (se 2 (by rfl) ⟨153411, by rfl⟩ : syracuseStep 409097 = 306823) B306823
theorem B409127 : Blo 271824 409127 := bstep (se 1 (by rfl) ⟨306845, by rfl⟩ : syracuseStep 409127 = 613691) B613691
theorem B409211 : Blo 271824 409211 := bstep (se 1 (by rfl) ⟨306908, by rfl⟩ : syracuseStep 409211 = 613817) B613817
theorem B409337 : Blo 271824 409337 := bstep (se 2 (by rfl) ⟨153501, by rfl⟩ : syracuseStep 409337 = 307003) B307003
theorem B409439 : Blo 271824 409439 := bstep (se 1 (by rfl) ⟨307079, by rfl⟩ : syracuseStep 409439 = 614159) B614159
theorem B409451 : Blo 271824 409451 := bstep (se 1 (by rfl) ⟨307088, by rfl⟩ : syracuseStep 409451 = 614177) B614177
theorem B1982501 : Blo 271824 1982501 := bstep (se 4 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 1982501 = 371719) B371719
theorem B409679 : Blo 271824 409679 := bstep (se 1 (by rfl) ⟨307259, by rfl⟩ : syracuseStep 409679 = 614519) B614519
theorem B409799 : Blo 271824 409799 := bstep (se 1 (by rfl) ⟨307349, by rfl⟩ : syracuseStep 409799 = 614699) B614699
theorem B409961 : Blo 271824 409961 := bstep (se 2 (by rfl) ⟨153735, by rfl⟩ : syracuseStep 409961 = 307471) B307471
theorem B344503 : Blo 271824 344503 := bstep (se 1 (by rfl) ⟨258377, by rfl⟩ : syracuseStep 344503 = 516755) B516755
theorem B410039 : Blo 271824 410039 := bstep (se 1 (by rfl) ⟨307529, by rfl⟩ : syracuseStep 410039 = 615059) B615059
theorem B410075 : Blo 271824 410075 := bstep (se 1 (by rfl) ⟨307556, by rfl⟩ : syracuseStep 410075 = 615113) B615113
theorem B1753609 : Blo 271824 1753609 := bstep (se 2 (by rfl) ⟨657603, by rfl⟩ : syracuseStep 1753609 = 1315207) B1315207
theorem B311887 : Blo 271824 311887 := bstep (se 1 (by rfl) ⟨233915, by rfl⟩ : syracuseStep 311887 = 467831) B467831
theorem B1393361 : Blo 271824 1393361 := bstep (se 2 (by rfl) ⟨522510, by rfl⟩ : syracuseStep 1393361 = 1045021) B1045021
theorem B443243 : Blo 271824 443243 := bstep (se 1 (by rfl) ⟨332432, by rfl⟩ : syracuseStep 443243 = 664865) B664865
theorem B410543 : Blo 271824 410543 := bstep (se 1 (by rfl) ⟨307907, by rfl⟩ : syracuseStep 410543 = 615815) B615815
theorem B410633 : Blo 271824 410633 := bstep (se 2 (by rfl) ⟨153987, by rfl⟩ : syracuseStep 410633 = 307975) B307975
theorem B410663 : Blo 271824 410663 := bstep (se 1 (by rfl) ⟨307997, by rfl⟩ : syracuseStep 410663 = 615995) B615995
theorem B574543 : Blo 271824 574543 := bstep (se 1 (by rfl) ⟨430907, by rfl⟩ : syracuseStep 574543 = 861815) B861815
theorem B410747 : Blo 271824 410747 := bstep (se 1 (by rfl) ⟨308060, by rfl⟩ : syracuseStep 410747 = 616121) B616121
theorem B410873 : Blo 271824 410873 := bstep (se 2 (by rfl) ⟨154077, by rfl⟩ : syracuseStep 410873 = 308155) B308155
theorem B410975 : Blo 271824 410975 := bstep (se 1 (by rfl) ⟨308231, by rfl⟩ : syracuseStep 410975 = 616463) B616463
theorem B410987 : Blo 271824 410987 := bstep (se 1 (by rfl) ⟨308240, by rfl⟩ : syracuseStep 410987 = 616481) B616481
theorem B1558055 : Blo 271824 1558055 := bstep (se 1 (by rfl) ⟨1168541, by rfl⟩ : syracuseStep 1558055 = 2337083) B2337083
theorem B411215 : Blo 271824 411215 := bstep (se 1 (by rfl) ⟨308411, by rfl⟩ : syracuseStep 411215 = 616823) B616823
theorem B345799 : Blo 271824 345799 := bstep (se 1 (by rfl) ⟨259349, by rfl⟩ : syracuseStep 345799 = 518699) B518699
theorem B411335 : Blo 271824 411335 := bstep (se 1 (by rfl) ⟨308501, by rfl⟩ : syracuseStep 411335 = 617003) B617003
theorem B1558237 : Blo 271824 1558237 := bstep (se 3 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 1558237 = 584339) B584339
theorem B837449 : Blo 271824 837449 := bstep (se 2 (by rfl) ⟨314043, by rfl⟩ : syracuseStep 837449 = 628087) B628087
theorem B411497 : Blo 271824 411497 := bstep (se 2 (by rfl) ⟨154311, by rfl⟩ : syracuseStep 411497 = 308623) B308623
theorem B411575 : Blo 271824 411575 := bstep (se 1 (by rfl) ⟨308681, by rfl⟩ : syracuseStep 411575 = 617363) B617363
theorem B411611 : Blo 271824 411611 := bstep (se 1 (by rfl) ⟨308708, by rfl⟩ : syracuseStep 411611 = 617417) B617417
theorem B1984601 : Blo 271824 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B3524897 : Blo 271824 3524897 := bstep (se 2 (by rfl) ⟨1321836, by rfl⟩ : syracuseStep 3524897 = 2643673) B2643673
theorem B412079 : Blo 271824 412079 := bstep (se 1 (by rfl) ⟨309059, by rfl⟩ : syracuseStep 412079 = 618119) B618119
theorem B412169 : Blo 271824 412169 := bstep (se 2 (by rfl) ⟨154563, by rfl⟩ : syracuseStep 412169 = 309127) B309127
theorem B412199 : Blo 271824 412199 := bstep (se 1 (by rfl) ⟨309149, by rfl⟩ : syracuseStep 412199 = 618299) B618299
theorem B281183 : Blo 271824 281183 := bstep (se 1 (by rfl) ⟨210887, by rfl⟩ : syracuseStep 281183 = 421775) B421775
theorem B412283 : Blo 271824 412283 := bstep (se 1 (by rfl) ⟨309212, by rfl⟩ : syracuseStep 412283 = 618425) B618425
theorem B4410085 : Blo 271824 4410085 := bstep (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) B826891
theorem B412409 : Blo 271824 412409 := bstep (se 2 (by rfl) ⟨154653, by rfl⟩ : syracuseStep 412409 = 309307) B309307
theorem B412511 : Blo 271824 412511 := bstep (se 1 (by rfl) ⟨309383, by rfl⟩ : syracuseStep 412511 = 618767) B618767
theorem B412523 : Blo 271824 412523 := bstep (se 1 (by rfl) ⟨309392, by rfl⟩ : syracuseStep 412523 = 618785) B618785
theorem B2214839 : Blo 271824 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B412751 : Blo 271824 412751 := bstep (se 1 (by rfl) ⟨309563, by rfl⟩ : syracuseStep 412751 = 619127) B619127
theorem B1395791 : Blo 271824 1395791 := bstep (se 1 (by rfl) ⟨1046843, by rfl⟩ : syracuseStep 1395791 = 2093687) B2093687
theorem B412871 : Blo 271824 412871 := bstep (se 1 (by rfl) ⟨309653, by rfl⟩ : syracuseStep 412871 = 619307) B619307
theorem B413033 : Blo 271824 413033 := bstep (se 2 (by rfl) ⟨154887, by rfl⟩ : syracuseStep 413033 = 309775) B309775
theorem B413111 : Blo 271824 413111 := bstep (se 1 (by rfl) ⟨309833, by rfl⟩ : syracuseStep 413111 = 619667) B619667
theorem B413147 : Blo 271824 413147 := bstep (se 1 (by rfl) ⟨309860, by rfl⟩ : syracuseStep 413147 = 619721) B619721
theorem B1396445 : Blo 271824 1396445 := bstep (se 3 (by rfl) ⟨261833, by rfl⟩ : syracuseStep 1396445 = 523667) B523667
theorem B1036061 : Blo 271824 1036061 := bstep (se 3 (by rfl) ⟨194261, by rfl⟩ : syracuseStep 1036061 = 388523) B388523
theorem B413615 : Blo 271824 413615 := bstep (se 1 (by rfl) ⟨310211, by rfl⟩ : syracuseStep 413615 = 620423) B620423
theorem B413705 : Blo 271824 413705 := bstep (se 2 (by rfl) ⟨155139, by rfl⟩ : syracuseStep 413705 = 310279) B310279
theorem B413735 : Blo 271824 413735 := bstep (se 1 (by rfl) ⟨310301, by rfl⟩ : syracuseStep 413735 = 620603) B620603
theorem B348239 : Blo 271824 348239 := bstep (se 1 (by rfl) ⟨261179, by rfl⟩ : syracuseStep 348239 = 522359) B522359
theorem B1036745 : Blo 271824 1036745 := bstep (se 2 (by rfl) ⟨388779, by rfl⟩ : syracuseStep 1036745 = 777559) B777559
theorem B774643 : Blo 271824 774643 := bstep (se 1 (by rfl) ⟨580982, by rfl⟩ : syracuseStep 774643 = 1161965) B1161965
theorem B872947 : Blo 271824 872947 := bstep (se 1 (by rfl) ⟨654710, by rfl⟩ : syracuseStep 872947 = 1309421) B1309421
theorem B5263973 : Blo 271824 5263973 := bstep (se 4 (by rfl) ⟨493497, by rfl⟩ : syracuseStep 5263973 = 986995) B986995
theorem B414407 : Blo 271824 414407 := bstep (se 1 (by rfl) ⟨310805, by rfl⟩ : syracuseStep 414407 = 621611) B621611
theorem B807841 : Blo 271824 807841 := bstep (se 2 (by rfl) ⟨302940, by rfl⟩ : syracuseStep 807841 = 605881) B605881
theorem B1037231 : Blo 271824 1037231 := bstep (se 1 (by rfl) ⟨777923, by rfl⟩ : syracuseStep 1037231 = 1555847) B1555847
theorem B1168303 : Blo 271824 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B1561679 : Blo 271824 1561679 := bstep (se 1 (by rfl) ⟨1171259, by rfl⟩ : syracuseStep 1561679 = 2342519) B2342519
theorem B611963 : Blo 271824 611963 := bstep (se 1 (by rfl) ⟨458972, by rfl⟩ : syracuseStep 611963 = 917945) B917945
theorem B1038035 : Blo 271824 1038035 := bstep (se 1 (by rfl) ⟨778526, by rfl⟩ : syracuseStep 1038035 = 1557053) B1557053
theorem B1758941 : Blo 271824 1758941 := bstep (se 3 (by rfl) ⟨329801, by rfl⟩ : syracuseStep 1758941 = 659603) B659603
theorem B612089 : Blo 271824 612089 := bstep (se 2 (by rfl) ⟨229533, by rfl⟩ : syracuseStep 612089 = 459067) B459067
theorem B1169261 : Blo 271824 1169261 := bstep (se 3 (by rfl) ⟨219236, by rfl⟩ : syracuseStep 1169261 = 438473) B438473
theorem B612359 : Blo 271824 612359 := bstep (se 1 (by rfl) ⟨459269, by rfl⟩ : syracuseStep 612359 = 918539) B918539
theorem B776249 : Blo 271824 776249 := bstep (se 2 (by rfl) ⟨291093, by rfl⟩ : syracuseStep 776249 = 582187) B582187
theorem B612431 : Blo 271824 612431 := bstep (se 1 (by rfl) ⟨459323, by rfl⟩ : syracuseStep 612431 = 918647) B918647
theorem B4773977 : Blo 271824 4773977 := bstep (se 2 (by rfl) ⟨1790241, by rfl⟩ : syracuseStep 4773977 = 3580483) B3580483
theorem B3496193 : Blo 271824 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B4741409 : Blo 271824 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B776591 : Blo 271824 776591 := bstep (se 1 (by rfl) ⟨582443, by rfl⟩ : syracuseStep 776591 = 1164887) B1164887
theorem B4446667 : Blo 271824 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B612827 : Blo 271824 612827 := bstep (se 1 (by rfl) ⟨459620, by rfl⟩ : syracuseStep 612827 = 919241) B919241
theorem B3758669 : Blo 271824 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B7101107 : Blo 271824 7101107 := bstep (se 1 (by rfl) ⟨5325830, by rfl⟩ : syracuseStep 7101107 = 10651661) B10651661
theorem B3169169 : Blo 271824 3169169 := bstep (se 2 (by rfl) ⟨1188438, by rfl⟩ : syracuseStep 3169169 = 2376877) B2376877
theorem B613295 : Blo 271824 613295 := bstep (se 1 (by rfl) ⟨459971, by rfl⟩ : syracuseStep 613295 = 919943) B919943
theorem B1334191 : Blo 271824 1334191 := bstep (se 1 (by rfl) ⟨1000643, by rfl⟩ : syracuseStep 1334191 = 2001287) B2001287
theorem B2087855 : Blo 271824 2087855 := bstep (se 1 (by rfl) ⟨1565891, by rfl⟩ : syracuseStep 2087855 = 3131783) B3131783
theorem B613547 : Blo 271824 613547 := bstep (se 1 (by rfl) ⟨460160, by rfl⟩ : syracuseStep 613547 = 920321) B920321
theorem B417017 : Blo 271824 417017 := bstep (se 2 (by rfl) ⟨156381, by rfl⟩ : syracuseStep 417017 = 312763) B312763
theorem B1564069 : Blo 271824 1564069 := bstep (se 4 (by rfl) ⟨146631, by rfl⟩ : syracuseStep 1564069 = 293263) B293263
theorem B48717233 : Blo 271824 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B1007239 : Blo 271824 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B614087 : Blo 271824 614087 := bstep (se 1 (by rfl) ⟨460565, by rfl⟩ : syracuseStep 614087 = 921131) B921131
theorem B876395 : Blo 271824 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B581537 : Blo 271824 581537 := bstep (se 2 (by rfl) ⟨218076, by rfl⟩ : syracuseStep 581537 = 436153) B436153
theorem B1040465 : Blo 271824 1040465 := bstep (se 2 (by rfl) ⟨390174, by rfl⟩ : syracuseStep 1040465 = 780349) B780349
theorem B2351267 : Blo 271824 2351267 := bstep (se 1 (by rfl) ⟨1763450, by rfl⟩ : syracuseStep 2351267 = 3526901) B3526901
theorem B516307 : Blo 271824 516307 := bstep (se 1 (by rfl) ⟨387230, by rfl⟩ : syracuseStep 516307 = 774461) B774461
theorem B581879 : Blo 271824 581879 := bstep (se 1 (by rfl) ⟨436409, by rfl⟩ : syracuseStep 581879 = 872819) B872819
theorem B516527 : Blo 271824 516527 := bstep (se 1 (by rfl) ⟨387395, by rfl⟩ : syracuseStep 516527 = 774791) B774791
theorem B1040921 : Blo 271824 1040921 := bstep (se 2 (by rfl) ⟨390345, by rfl⟩ : syracuseStep 1040921 = 780691) B780691
theorem B614951 : Blo 271824 614951 := bstep (se 1 (by rfl) ⟨461213, by rfl⟩ : syracuseStep 614951 = 922427) B922427
theorem B778891 : Blo 271824 778891 := bstep (se 1 (by rfl) ⟨584168, by rfl⟩ : syracuseStep 778891 = 1168337) B1168337
theorem B3105539 : Blo 271824 3105539 := bstep (se 1 (by rfl) ⟨2329154, by rfl⟩ : syracuseStep 3105539 = 4658309) B4658309
theorem B2974481 : Blo 271824 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B516937 : Blo 271824 516937 := bstep (se 2 (by rfl) ⟨193851, by rfl⟩ : syracuseStep 516937 = 387703) B387703
theorem B615275 : Blo 271824 615275 := bstep (se 1 (by rfl) ⟨461456, by rfl⟩ : syracuseStep 615275 = 922913) B922913
theorem B615329 : Blo 271824 615329 := bstep (se 2 (by rfl) ⟨230748, by rfl⟩ : syracuseStep 615329 = 461497) B461497
theorem B15000497 : Blo 271824 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B877625 : Blo 271824 877625 := bstep (se 2 (by rfl) ⟨329109, by rfl⟩ : syracuseStep 877625 = 658219) B658219
theorem B615671 : Blo 271824 615671 := bstep (se 1 (by rfl) ⟨461753, by rfl⟩ : syracuseStep 615671 = 923507) B923507
theorem B1042105 : Blo 271824 1042105 := bstep (se 2 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 1042105 = 781579) B781579
theorem B616265 : Blo 271824 616265 := bstep (se 2 (by rfl) ⟨231099, by rfl⟩ : syracuseStep 616265 = 462199) B462199
theorem B583519 : Blo 271824 583519 := bstep (se 1 (by rfl) ⟨437639, by rfl⟩ : syracuseStep 583519 = 875279) B875279
theorem B1763167 : Blo 271824 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B1894337 : Blo 271824 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B1271965 : Blo 271824 1271965 := bstep (se 3 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 1271965 = 476987) B476987
theorem B387623 : Blo 271824 387623 := bstep (se 1 (by rfl) ⟨290717, by rfl⟩ : syracuseStep 387623 = 581435) B581435
theorem B617057 : Blo 271824 617057 := bstep (se 2 (by rfl) ⟨231396, by rfl⟩ : syracuseStep 617057 = 462793) B462793
theorem B1108669 : Blo 271824 1108669 := bstep (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) B415751
theorem B617399 : Blo 271824 617399 := bstep (se 1 (by rfl) ⟨463049, by rfl⟩ : syracuseStep 617399 = 926099) B926099
theorem B519367 : Blo 271824 519367 := bstep (se 1 (by rfl) ⟨389525, by rfl⟩ : syracuseStep 519367 = 779051) B779051
theorem B6319397 : Blo 271824 6319397 := bstep (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) B1184887
theorem B1043837 : Blo 271824 1043837 := bstep (se 3 (by rfl) ⟨195719, by rfl⟩ : syracuseStep 1043837 = 391439) B391439
theorem B5074319 : Blo 271824 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B617993 : Blo 271824 617993 := bstep (se 2 (by rfl) ⟨231747, by rfl⟩ : syracuseStep 617993 = 463495) B463495
theorem B1175239 : Blo 271824 1175239 := bstep (se 1 (by rfl) ⟨881429, by rfl⟩ : syracuseStep 1175239 = 1762859) B1762859
theorem B519929 : Blo 271824 519929 := bstep (se 2 (by rfl) ⟨194973, by rfl⟩ : syracuseStep 519929 = 389947) B389947
theorem B618335 : Blo 271824 618335 := bstep (se 1 (by rfl) ⟨463751, by rfl⟩ : syracuseStep 618335 = 927503) B927503
theorem B520111 : Blo 271824 520111 := bstep (se 1 (by rfl) ⟨390083, by rfl⟩ : syracuseStep 520111 = 780167) B780167
theorem B618515 : Blo 271824 618515 := bstep (se 1 (by rfl) ⟨463886, by rfl⟩ : syracuseStep 618515 = 927773) B927773
theorem B618857 : Blo 271824 618857 := bstep (se 2 (by rfl) ⟨232071, by rfl⟩ : syracuseStep 618857 = 464143) B464143
theorem B291367 : Blo 271824 291367 := bstep (se 1 (by rfl) ⟨218525, by rfl⟩ : syracuseStep 291367 = 437051) B437051
theorem B783037 : Blo 271824 783037 := bstep (se 3 (by rfl) ⟨146819, by rfl⟩ : syracuseStep 783037 = 293639) B293639
theorem B2978633 : Blo 271824 2978633 := bstep (se 2 (by rfl) ⟨1116987, by rfl⟩ : syracuseStep 2978633 = 2233975) B2233975
theorem B783265 : Blo 271824 783265 := bstep (se 2 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 783265 = 587449) B587449
theorem B1569719 : Blo 271824 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B619451 : Blo 271824 619451 := bstep (se 1 (by rfl) ⟨464588, by rfl⟩ : syracuseStep 619451 = 929177) B929177
theorem B2814977 : Blo 271824 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B619577 : Blo 271824 619577 := bstep (se 2 (by rfl) ⟨232341, by rfl⟩ : syracuseStep 619577 = 464683) B464683
theorem B521387 : Blo 271824 521387 := bstep (se 1 (by rfl) ⟨391040, by rfl⟩ : syracuseStep 521387 = 782081) B782081
theorem B3339481 : Blo 271824 3339481 := bstep (se 2 (by rfl) ⟨1252305, by rfl⟩ : syracuseStep 3339481 = 2504611) B2504611
theorem B783607 : Blo 271824 783607 := bstep (se 1 (by rfl) ⟨587705, by rfl⟩ : syracuseStep 783607 = 1175411) B1175411
theorem B521615 : Blo 271824 521615 := bstep (se 1 (by rfl) ⟨391211, by rfl⟩ : syracuseStep 521615 = 782423) B782423
theorem B619919 : Blo 271824 619919 := bstep (se 1 (by rfl) ⟨464939, by rfl⟩ : syracuseStep 619919 = 929879) B929879
theorem B390619 : Blo 271824 390619 := bstep (se 1 (by rfl) ⟨292964, by rfl⟩ : syracuseStep 390619 = 585929) B585929
theorem B1045979 : Blo 271824 1045979 := bstep (se 1 (by rfl) ⟨784484, by rfl⟩ : syracuseStep 1045979 = 1568969) B1568969
theorem B1177051 : Blo 271824 1177051 := bstep (se 1 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 1177051 = 1765577) B1765577
theorem B783881 : Blo 271824 783881 := bstep (se 2 (by rfl) ⟨293955, by rfl⟩ : syracuseStep 783881 = 587911) B587911
theorem B1570427 : Blo 271824 1570427 := bstep (se 1 (by rfl) ⟨1177820, by rfl⟩ : syracuseStep 1570427 = 2355641) B2355641
theorem B1308305 : Blo 271824 1308305 := bstep (se 2 (by rfl) ⟨490614, by rfl⟩ : syracuseStep 1308305 = 981229) B981229
theorem B620243 : Blo 271824 620243 := bstep (se 1 (by rfl) ⟨465182, by rfl⟩ : syracuseStep 620243 = 930365) B930365
theorem B1472519 : Blo 271824 1472519 := bstep (se 1 (by rfl) ⟨1104389, by rfl⟩ : syracuseStep 1472519 = 2208779) B2208779
theorem B391177 : Blo 271824 391177 := bstep (se 2 (by rfl) ⟨146691, by rfl⟩ : syracuseStep 391177 = 293383) B293383
theorem B1964047 : Blo 271824 1964047 := bstep (se 1 (by rfl) ⟨1473035, by rfl⟩ : syracuseStep 1964047 = 2946071) B2946071
theorem B1964189 : Blo 271824 1964189 := bstep (se 3 (by rfl) ⟨368285, by rfl⟩ : syracuseStep 1964189 = 736571) B736571
theorem B784541 : Blo 271824 784541 := bstep (se 3 (by rfl) ⟨147101, by rfl⟩ : syracuseStep 784541 = 294203) B294203
theorem B3111371 : Blo 271824 3111371 := bstep (se 1 (by rfl) ⟨2333528, by rfl⟩ : syracuseStep 3111371 = 4667057) B4667057
theorem B784883 : Blo 271824 784883 := bstep (se 1 (by rfl) ⟨588662, by rfl⟩ : syracuseStep 784883 = 1177325) B1177325
theorem B3963437 : Blo 271824 3963437 := bstep (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) B1486289
theorem B522875 : Blo 271824 522875 := bstep (se 1 (by rfl) ⟨392156, by rfl⟩ : syracuseStep 522875 = 784313) B784313
theorem B1047239 : Blo 271824 1047239 := bstep (se 1 (by rfl) ⟨785429, by rfl⟩ : syracuseStep 1047239 = 1570859) B1570859
theorem B523115 : Blo 271824 523115 := bstep (se 1 (by rfl) ⟨392336, by rfl⟩ : syracuseStep 523115 = 784673) B784673
theorem B785339 : Blo 271824 785339 := bstep (se 1 (by rfl) ⟨589004, by rfl⟩ : syracuseStep 785339 = 1178009) B1178009
theorem B523361 : Blo 271824 523361 := bstep (se 2 (by rfl) ⟨196260, by rfl⟩ : syracuseStep 523361 = 392521) B392521
theorem B523513 : Blo 271824 523513 := bstep (se 2 (by rfl) ⟨196317, by rfl⟩ : syracuseStep 523513 = 392635) B392635
theorem B6651317 : Blo 271824 6651317 := bstep (se 5 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 6651317 = 623561) B623561
theorem B1310651 : Blo 271824 1310651 := bstep (se 1 (by rfl) ⟨982988, by rfl⟩ : syracuseStep 1310651 = 1965977) B1965977
theorem B917513 : Blo 271824 917513 := bstep (se 2 (by rfl) ⟨344067, by rfl⟩ : syracuseStep 917513 = 688135) B688135
theorem B688409 : Blo 271824 688409 := bstep (se 2 (by rfl) ⟨258153, by rfl⟩ : syracuseStep 688409 = 516307) B516307
theorem B459175 : Blo 271824 459175 := bstep (se 1 (by rfl) ⟨344381, by rfl⟩ : syracuseStep 459175 = 688763) B688763
theorem B295495 : Blo 271824 295495 := bstep (se 1 (by rfl) ⟨221621, by rfl⟩ : syracuseStep 295495 = 443243) B443243
theorem B459337 : Blo 271824 459337 := bstep (se 2 (by rfl) ⟨172251, by rfl⟩ : syracuseStep 459337 = 344503) B344503
theorem B459371 : Blo 271824 459371 := bstep (se 1 (by rfl) ⟨344528, by rfl⟩ : syracuseStep 459371 = 689057) B689057
theorem B656095 : Blo 271824 656095 := bstep (se 1 (by rfl) ⟨492071, by rfl⟩ : syracuseStep 656095 = 984143) B984143
theorem B5604173 : Blo 271824 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B689249 : Blo 271824 689249 := bstep (se 2 (by rfl) ⟨258468, by rfl⟩ : syracuseStep 689249 = 516937) B516937
theorem B558299 : Blo 271824 558299 := bstep (se 1 (by rfl) ⟨418724, by rfl⟩ : syracuseStep 558299 = 837449) B837449
theorem B3933683 : Blo 271824 3933683 := bstep (se 1 (by rfl) ⟨2950262, by rfl⟩ : syracuseStep 3933683 = 5900525) B5900525
theorem B1246727 : Blo 271824 1246727 := bstep (se 1 (by rfl) ⟨935045, by rfl⟩ : syracuseStep 1246727 = 1870091) B1870091
theorem B35915633 : Blo 271824 35915633 := bstep (se 2 (by rfl) ⟨13468362, by rfl⟩ : syracuseStep 35915633 = 26936725) B26936725
theorem B1476559 : Blo 271824 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B461065 : Blo 271824 461065 := bstep (se 2 (by rfl) ⟨172899, by rfl⟩ : syracuseStep 461065 = 345799) B345799
theorem B690707 : Blo 271824 690707 := bstep (se 1 (by rfl) ⟨518030, by rfl⟩ : syracuseStep 690707 = 1036061) B1036061
theorem B691163 : Blo 271824 691163 := bstep (se 1 (by rfl) ⟨518372, by rfl⟩ : syracuseStep 691163 = 1036745) B1036745
theorem B3509315 : Blo 271824 3509315 := bstep (se 1 (by rfl) ⟨2631986, by rfl⟩ : syracuseStep 3509315 = 5263973) B5263973
theorem B920699 : Blo 271824 920699 := bstep (se 1 (by rfl) ⟨690524, by rfl⟩ : syracuseStep 920699 = 1381049) B1381049
theorem B691487 : Blo 271824 691487 := bstep (se 1 (by rfl) ⟨518615, by rfl⟩ : syracuseStep 691487 = 1037231) B1037231
theorem B920969 : Blo 271824 920969 := bstep (se 2 (by rfl) ⟨345363, by rfl⟩ : syracuseStep 920969 = 690727) B690727
theorem B1478225 : Blo 271824 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B462523 : Blo 271824 462523 := bstep (se 1 (by rfl) ⟨346892, by rfl⟩ : syracuseStep 462523 = 693785) B693785
theorem B626473 : Blo 271824 626473 := bstep (se 2 (by rfl) ⟨234927, by rfl⟩ : syracuseStep 626473 = 469855) B469855
theorem B495401 : Blo 271824 495401 := bstep (se 2 (by rfl) ⟨185775, by rfl⟩ : syracuseStep 495401 = 371551) B371551
theorem B692023 : Blo 271824 692023 := bstep (se 1 (by rfl) ⟨519017, by rfl⟩ : syracuseStep 692023 = 1038035) B1038035
theorem B921401 : Blo 271824 921401 := bstep (se 2 (by rfl) ⟨345525, by rfl⟩ : syracuseStep 921401 = 691051) B691051
theorem B3149725 : Blo 271824 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B3182651 : Blo 271824 3182651 := bstep (se 1 (by rfl) ⟨2386988, by rfl⟩ : syracuseStep 3182651 = 4773977) B4773977
theorem B2330795 : Blo 271824 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B1380563 : Blo 271824 1380563 := bstep (se 1 (by rfl) ⟨1035422, by rfl⟩ : syracuseStep 1380563 = 2070845) B2070845
theorem B692489 : Blo 271824 692489 := bstep (se 2 (by rfl) ⟨259683, by rfl⟩ : syracuseStep 692489 = 519367) B519367
theorem B397735 : Blo 271824 397735 := bstep (se 1 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 397735 = 596603) B596603
theorem B1315379 : Blo 271824 1315379 := bstep (se 1 (by rfl) ⟨986534, by rfl⟩ : syracuseStep 1315379 = 1973069) B1973069
theorem B922265 : Blo 271824 922265 := bstep (se 2 (by rfl) ⟨345849, by rfl⟩ : syracuseStep 922265 = 691699) B691699
theorem B463583 : Blo 271824 463583 := bstep (se 1 (by rfl) ⟨347687, by rfl⟩ : syracuseStep 463583 = 695375) B695375
theorem B32478155 : Blo 271824 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B464015 : Blo 271824 464015 := bstep (se 1 (by rfl) ⟨348011, by rfl⟩ : syracuseStep 464015 = 696023) B696023
theorem B693481 : Blo 271824 693481 := bstep (se 2 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 693481 = 520111) B520111
theorem B464251 : Blo 271824 464251 := bstep (se 1 (by rfl) ⟨348188, by rfl⟩ : syracuseStep 464251 = 696377) B696377
theorem B3020165 : Blo 271824 3020165 := bstep (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) B566281
theorem B693643 : Blo 271824 693643 := bstep (se 1 (by rfl) ⟨520232, by rfl⟩ : syracuseStep 693643 = 1040465) B1040465
theorem B693947 : Blo 271824 693947 := bstep (se 1 (by rfl) ⟨520460, by rfl⟩ : syracuseStep 693947 = 1040921) B1040921
theorem B2070359 : Blo 271824 2070359 := bstep (se 1 (by rfl) ⟨1552769, by rfl⟩ : syracuseStep 2070359 = 3105539) B3105539
theorem B10000331 : Blo 271824 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B923777 : Blo 271824 923777 := bstep (se 2 (by rfl) ⟨346416, by rfl⟩ : syracuseStep 923777 = 692833) B692833
theorem B924155 : Blo 271824 924155 := bstep (se 1 (by rfl) ⟨693116, by rfl⟩ : syracuseStep 924155 = 1386233) B1386233
theorem B1317455 : Blo 271824 1317455 := bstep (se 1 (by rfl) ⟨988091, by rfl⟩ : syracuseStep 1317455 = 1976183) B1976183
theorem B924587 : Blo 271824 924587 := bstep (se 1 (by rfl) ⟨693440, by rfl⟩ : syracuseStep 924587 = 1386881) B1386881
theorem B466139 : Blo 271824 466139 := bstep (se 1 (by rfl) ⟨349604, by rfl⟩ : syracuseStep 466139 = 699209) B699209
theorem B3939677 : Blo 271824 3939677 := bstep (se 3 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 3939677 = 1477379) B1477379
theorem B1023329 : Blo 271824 1023329 := bstep (se 2 (by rfl) ⟨383748, by rfl⟩ : syracuseStep 1023329 = 767497) B767497
theorem B925127 : Blo 271824 925127 := bstep (se 1 (by rfl) ⟨693845, by rfl⟩ : syracuseStep 925127 = 1387691) B1387691
theorem B695891 : Blo 271824 695891 := bstep (se 1 (by rfl) ⟨521918, by rfl⟩ : syracuseStep 695891 = 1043837) B1043837
theorem B3382879 : Blo 271824 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B925451 : Blo 271824 925451 := bstep (se 1 (by rfl) ⟨694088, by rfl⟩ : syracuseStep 925451 = 1388177) B1388177
theorem B925721 : Blo 271824 925721 := bstep (se 2 (by rfl) ⟨347145, by rfl⟩ : syracuseStep 925721 = 694291) B694291
theorem B1876651 : Blo 271824 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B16851725 : Blo 271824 16851725 := bstep (se 3 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 16851725 = 6319397) B6319397
theorem B697319 : Blo 271824 697319 := bstep (se 1 (by rfl) ⟨522989, by rfl⟩ : syracuseStep 697319 = 1045979) B1045979
theorem B1778921 : Blo 271824 1778921 := bstep (se 2 (by rfl) ⟨667095, by rfl⟩ : syracuseStep 1778921 = 1334191) B1334191
theorem B926963 : Blo 271824 926963 := bstep (se 1 (by rfl) ⟨695222, by rfl⟩ : syracuseStep 926963 = 1390445) B1390445
theorem B927071 : Blo 271824 927071 := bstep (se 1 (by rfl) ⟨695303, by rfl⟩ : syracuseStep 927071 = 1390607) B1390607
theorem B271867 : Blo 271824 271867 := bstep (se 1 (by rfl) ⟨203900, by rfl⟩ : syracuseStep 271867 = 407801) B407801
theorem B271935 : Blo 271824 271935 := bstep (se 1 (by rfl) ⟨203951, by rfl⟩ : syracuseStep 271935 = 407903) B407903
theorem B271943 : Blo 271824 271943 := bstep (se 1 (by rfl) ⟨203957, by rfl⟩ : syracuseStep 271943 = 407915) B407915
theorem B2074247 : Blo 271824 2074247 := bstep (se 1 (by rfl) ⟨1555685, by rfl⟩ : syracuseStep 2074247 = 3111371) B3111371
theorem B698017 : Blo 271824 698017 := bstep (se 2 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 698017 = 523513) B523513
theorem B2827997 : Blo 271824 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B272095 : Blo 271824 272095 := bstep (se 1 (by rfl) ⟨204071, by rfl⟩ : syracuseStep 272095 = 408143) B408143
theorem B272175 : Blo 271824 272175 := bstep (se 1 (by rfl) ⟨204131, by rfl⟩ : syracuseStep 272175 = 408263) B408263
theorem B698159 : Blo 271824 698159 := bstep (se 1 (by rfl) ⟨523619, by rfl⟩ : syracuseStep 698159 = 1047239) B1047239
theorem B4990825 : Blo 271824 4990825 := bstep (se 2 (by rfl) ⟨1871559, by rfl⟩ : syracuseStep 4990825 = 3743119) B3743119
theorem B272283 : Blo 271824 272283 := bstep (se 1 (by rfl) ⟨204212, by rfl⟩ : syracuseStep 272283 = 408425) B408425
theorem B272335 : Blo 271824 272335 := bstep (se 1 (by rfl) ⟨204251, by rfl⟩ : syracuseStep 272335 = 408503) B408503
theorem B272359 : Blo 271824 272359 := bstep (se 1 (by rfl) ⟨204269, by rfl⟩ : syracuseStep 272359 = 408539) B408539
theorem B2205949 : Blo 271824 2205949 := bstep (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) B827231
theorem B272671 : Blo 271824 272671 := bstep (se 1 (by rfl) ⟨204503, by rfl⟩ : syracuseStep 272671 = 409007) B409007
theorem B4434211 : Blo 271824 4434211 := bstep (se 1 (by rfl) ⟨3325658, by rfl⟩ : syracuseStep 4434211 = 6651317) B6651317
theorem B3385637 : Blo 271824 3385637 := bstep (se 4 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 3385637 = 634807) B634807
theorem B272731 : Blo 271824 272731 := bstep (se 1 (by rfl) ⟨204548, by rfl⟩ : syracuseStep 272731 = 409097) B409097
theorem B272751 : Blo 271824 272751 := bstep (se 1 (by rfl) ⟨204563, by rfl⟩ : syracuseStep 272751 = 409127) B409127
theorem B272807 : Blo 271824 272807 := bstep (se 1 (by rfl) ⟨204605, by rfl⟩ : syracuseStep 272807 = 409211) B409211
theorem B1550765 : Blo 271824 1550765 := bstep (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) B581537
theorem B272891 : Blo 271824 272891 := bstep (se 1 (by rfl) ⟨204668, by rfl⟩ : syracuseStep 272891 = 409337) B409337
theorem B272959 : Blo 271824 272959 := bstep (se 1 (by rfl) ⟨204719, by rfl⟩ : syracuseStep 272959 = 409439) B409439
theorem B272967 : Blo 271824 272967 := bstep (se 1 (by rfl) ⟨204725, by rfl⟩ : syracuseStep 272967 = 409451) B409451
theorem B1321667 : Blo 271824 1321667 := bstep (se 1 (by rfl) ⟨991250, by rfl⟩ : syracuseStep 1321667 = 1982501) B1982501
theorem B305887 : Blo 271824 305887 := bstep (se 1 (by rfl) ⟨229415, by rfl⟩ : syracuseStep 305887 = 458831) B458831
theorem B273119 : Blo 271824 273119 := bstep (se 1 (by rfl) ⟨204839, by rfl⟩ : syracuseStep 273119 = 409679) B409679
theorem B273199 : Blo 271824 273199 := bstep (se 1 (by rfl) ⟨204899, by rfl⟩ : syracuseStep 273199 = 409799) B409799
theorem B928637 : Blo 271824 928637 := bstep (se 3 (by rfl) ⟨174119, by rfl⟩ : syracuseStep 928637 = 348239) B348239
theorem B273307 : Blo 271824 273307 := bstep (se 1 (by rfl) ⟨204980, by rfl⟩ : syracuseStep 273307 = 409961) B409961
theorem B273359 : Blo 271824 273359 := bstep (se 1 (by rfl) ⟨205019, by rfl⟩ : syracuseStep 273359 = 410039) B410039
theorem B273383 : Blo 271824 273383 := bstep (se 1 (by rfl) ⟨205037, by rfl⟩ : syracuseStep 273383 = 410075) B410075
theorem B928907 : Blo 271824 928907 := bstep (se 1 (by rfl) ⟨696680, by rfl⟩ : syracuseStep 928907 = 1393361) B1393361
theorem B306463 : Blo 271824 306463 := bstep (se 1 (by rfl) ⟨229847, by rfl⟩ : syracuseStep 306463 = 459695) B459695
theorem B273695 : Blo 271824 273695 := bstep (se 1 (by rfl) ⟨205271, by rfl⟩ : syracuseStep 273695 = 410543) B410543
theorem B273755 : Blo 271824 273755 := bstep (se 1 (by rfl) ⟨205316, by rfl⟩ : syracuseStep 273755 = 410633) B410633
theorem B2338145 : Blo 271824 2338145 := bstep (se 2 (by rfl) ⟨876804, by rfl⟩ : syracuseStep 2338145 = 1753609) B1753609
theorem B273775 : Blo 271824 273775 := bstep (se 1 (by rfl) ⟨205331, by rfl⟩ : syracuseStep 273775 = 410663) B410663
theorem B273831 : Blo 271824 273831 := bstep (se 1 (by rfl) ⟨205373, by rfl⟩ : syracuseStep 273831 = 410747) B410747
theorem B273915 : Blo 271824 273915 := bstep (se 1 (by rfl) ⟨205436, by rfl⟩ : syracuseStep 273915 = 410873) B410873
theorem B306751 : Blo 271824 306751 := bstep (se 1 (by rfl) ⟨230063, by rfl⟩ : syracuseStep 306751 = 460127) B460127
theorem B273983 : Blo 271824 273983 := bstep (se 1 (by rfl) ⟨205487, by rfl⟩ : syracuseStep 273983 = 410975) B410975
theorem B273991 : Blo 271824 273991 := bstep (se 1 (by rfl) ⟨205493, by rfl⟩ : syracuseStep 273991 = 410987) B410987
theorem B274143 : Blo 271824 274143 := bstep (se 1 (by rfl) ⟨205607, by rfl⟩ : syracuseStep 274143 = 411215) B411215
theorem B274223 : Blo 271824 274223 := bstep (se 1 (by rfl) ⟨205667, by rfl⟩ : syracuseStep 274223 = 411335) B411335
theorem B2994029 : Blo 271824 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B274331 : Blo 271824 274331 := bstep (se 1 (by rfl) ⟨205748, by rfl⟩ : syracuseStep 274331 = 411497) B411497
theorem B7450555 : Blo 271824 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B274383 : Blo 271824 274383 := bstep (se 1 (by rfl) ⟨205787, by rfl⟩ : syracuseStep 274383 = 411575) B411575
theorem B274407 : Blo 271824 274407 := bstep (se 1 (by rfl) ⟨205805, by rfl⟩ : syracuseStep 274407 = 411611) B411611
theorem B1323067 : Blo 271824 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B766057 : Blo 271824 766057 := bstep (se 2 (by rfl) ⟨287271, by rfl⟩ : syracuseStep 766057 = 574543) B574543
theorem B274719 : Blo 271824 274719 := bstep (se 1 (by rfl) ⟨206039, by rfl⟩ : syracuseStep 274719 = 412079) B412079
theorem B274779 : Blo 271824 274779 := bstep (se 1 (by rfl) ⟨206084, by rfl⟩ : syracuseStep 274779 = 412169) B412169
theorem B274799 : Blo 271824 274799 := bstep (se 1 (by rfl) ⟨206099, by rfl⟩ : syracuseStep 274799 = 412199) B412199
theorem B307579 : Blo 271824 307579 := bstep (se 1 (by rfl) ⟨230684, by rfl⟩ : syracuseStep 307579 = 461369) B461369
theorem B274855 : Blo 271824 274855 := bstep (se 1 (by rfl) ⟨206141, by rfl⟩ : syracuseStep 274855 = 412283) B412283
theorem B274939 : Blo 271824 274939 := bstep (se 1 (by rfl) ⟨206204, by rfl⟩ : syracuseStep 274939 = 412409) B412409
theorem B275007 : Blo 271824 275007 := bstep (se 1 (by rfl) ⟨206255, by rfl⟩ : syracuseStep 275007 = 412511) B412511
theorem B275015 : Blo 271824 275015 := bstep (se 1 (by rfl) ⟨206261, by rfl⟩ : syracuseStep 275015 = 412523) B412523
theorem B6337201 : Blo 271824 6337201 := bstep (se 2 (by rfl) ⟨2376450, by rfl⟩ : syracuseStep 6337201 = 4752901) B4752901
theorem B275167 : Blo 271824 275167 := bstep (se 1 (by rfl) ⟨206375, by rfl⟩ : syracuseStep 275167 = 412751) B412751
theorem B930527 : Blo 271824 930527 := bstep (se 1 (by rfl) ⟨697895, by rfl⟩ : syracuseStep 930527 = 1395791) B1395791
theorem B275247 : Blo 271824 275247 := bstep (se 1 (by rfl) ⟨206435, by rfl⟩ : syracuseStep 275247 = 412871) B412871
theorem B308047 : Blo 271824 308047 := bstep (se 1 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 308047 = 462071) B462071
theorem B2634605 : Blo 271824 2634605 := bstep (se 3 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 2634605 = 987977) B987977
theorem B275355 : Blo 271824 275355 := bstep (se 1 (by rfl) ⟨206516, by rfl⟩ : syracuseStep 275355 = 413033) B413033
theorem B1389473 : Blo 271824 1389473 := bstep (se 2 (by rfl) ⟨521052, by rfl⟩ : syracuseStep 1389473 = 1042105) B1042105
theorem B275407 : Blo 271824 275407 := bstep (se 1 (by rfl) ⟨206555, by rfl⟩ : syracuseStep 275407 = 413111) B413111
theorem B2077649 : Blo 271824 2077649 := bstep (se 2 (by rfl) ⟨779118, by rfl⟩ : syracuseStep 2077649 = 1558237) B1558237
theorem B275431 : Blo 271824 275431 := bstep (se 1 (by rfl) ⟨206573, by rfl⟩ : syracuseStep 275431 = 413147) B413147
theorem B308443 : Blo 271824 308443 := bstep (se 1 (by rfl) ⟨231332, by rfl⟩ : syracuseStep 308443 = 462665) B462665
theorem B275743 : Blo 271824 275743 := bstep (se 1 (by rfl) ⟨206807, by rfl⟩ : syracuseStep 275743 = 413615) B413615
theorem B275803 : Blo 271824 275803 := bstep (se 1 (by rfl) ⟨206852, by rfl⟩ : syracuseStep 275803 = 413705) B413705
theorem B275823 : Blo 271824 275823 := bstep (se 1 (by rfl) ⟨206867, by rfl⟩ : syracuseStep 275823 = 413735) B413735
theorem B308731 : Blo 271824 308731 := bstep (se 1 (by rfl) ⟨231548, by rfl⟩ : syracuseStep 308731 = 463097) B463097
theorem B308911 : Blo 271824 308911 := bstep (se 1 (by rfl) ⟨231683, by rfl⟩ : syracuseStep 308911 = 463367) B463367
theorem B309199 : Blo 271824 309199 := bstep (se 1 (by rfl) ⟨231899, by rfl⟩ : syracuseStep 309199 = 463799) B463799
theorem B5880113 : Blo 271824 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B309595 : Blo 271824 309595 := bstep (se 1 (by rfl) ⟨232196, by rfl⟩ : syracuseStep 309595 = 464393) B464393
theorem B407975 : Blo 271824 407975 := bstep (se 1 (by rfl) ⟨305981, by rfl⟩ : syracuseStep 407975 = 611963) B611963
theorem B8010161 : Blo 271824 8010161 := bstep (se 2 (by rfl) ⟨3003810, by rfl⟩ : syracuseStep 8010161 = 6007621) B6007621
theorem B309703 : Blo 271824 309703 := bstep (se 1 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 309703 = 464555) B464555
theorem B408059 : Blo 271824 408059 := bstep (se 1 (by rfl) ⟨306044, by rfl⟩ : syracuseStep 408059 = 612089) B612089
theorem B408185 : Blo 271824 408185 := bstep (se 2 (by rfl) ⟨153069, by rfl⟩ : syracuseStep 408185 = 306139) B306139
theorem B408239 : Blo 271824 408239 := bstep (se 1 (by rfl) ⟨306179, by rfl⟩ : syracuseStep 408239 = 612359) B612359
theorem B1555139 : Blo 271824 1555139 := bstep (se 1 (by rfl) ⟨1166354, by rfl⟩ : syracuseStep 1555139 = 2332709) B2332709
theorem B408287 : Blo 271824 408287 := bstep (se 1 (by rfl) ⟨306215, by rfl⟩ : syracuseStep 408287 = 612431) B612431
theorem B310063 : Blo 271824 310063 := bstep (se 1 (by rfl) ⟨232547, by rfl⟩ : syracuseStep 310063 = 465095) B465095
theorem B3160939 : Blo 271824 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B310171 : Blo 271824 310171 := bstep (se 1 (by rfl) ⟨232628, by rfl⟩ : syracuseStep 310171 = 465257) B465257
theorem B1489835 : Blo 271824 1489835 := bstep (se 1 (by rfl) ⟨1117376, by rfl⟩ : syracuseStep 1489835 = 2234753) B2234753
theorem B1751993 : Blo 271824 1751993 := bstep (se 2 (by rfl) ⟨656997, by rfl⟩ : syracuseStep 1751993 = 1313995) B1313995
theorem B408551 : Blo 271824 408551 := bstep (se 1 (by rfl) ⟨306413, by rfl⟩ : syracuseStep 408551 = 612827) B612827
theorem B2505779 : Blo 271824 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B4734071 : Blo 271824 4734071 := bstep (se 1 (by rfl) ⟨3550553, by rfl⟩ : syracuseStep 4734071 = 7101107) B7101107
theorem B408809 : Blo 271824 408809 := bstep (se 2 (by rfl) ⟨153303, by rfl⟩ : syracuseStep 408809 = 306607) B306607
theorem B2112779 : Blo 271824 2112779 := bstep (se 1 (by rfl) ⟨1584584, by rfl⟩ : syracuseStep 2112779 = 3169169) B3169169
theorem B408863 : Blo 271824 408863 := bstep (se 1 (by rfl) ⟨306647, by rfl⟩ : syracuseStep 408863 = 613295) B613295
theorem B1391903 : Blo 271824 1391903 := bstep (se 1 (by rfl) ⟨1043927, by rfl⟩ : syracuseStep 1391903 = 2087855) B2087855
theorem B409031 : Blo 271824 409031 := bstep (se 1 (by rfl) ⟨306773, by rfl⟩ : syracuseStep 409031 = 613547) B613547
theorem B278011 : Blo 271824 278011 := bstep (se 1 (by rfl) ⟨208508, by rfl⟩ : syracuseStep 278011 = 417017) B417017
theorem B310879 : Blo 271824 310879 := bstep (se 1 (by rfl) ⟨233159, by rfl⟩ : syracuseStep 310879 = 466319) B466319
theorem B409385 : Blo 271824 409385 := bstep (se 2 (by rfl) ⟨153519, by rfl⟩ : syracuseStep 409385 = 307039) B307039
theorem B409391 : Blo 271824 409391 := bstep (se 1 (by rfl) ⟨307043, by rfl⟩ : syracuseStep 409391 = 614087) B614087
theorem B835795 : Blo 271824 835795 := bstep (se 1 (by rfl) ⟨626846, by rfl⟩ : syracuseStep 835795 = 1253693) B1253693
theorem B409865 : Blo 271824 409865 := bstep (se 2 (by rfl) ⟨153699, by rfl⟩ : syracuseStep 409865 = 307399) B307399
theorem B344351 : Blo 271824 344351 := bstep (se 1 (by rfl) ⟨258263, by rfl⟩ : syracuseStep 344351 = 516527) B516527
theorem B409967 : Blo 271824 409967 := bstep (se 1 (by rfl) ⟨307475, by rfl⟩ : syracuseStep 409967 = 614951) B614951
theorem B1982987 : Blo 271824 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B410183 : Blo 271824 410183 := bstep (se 1 (by rfl) ⟨307637, by rfl⟩ : syracuseStep 410183 = 615275) B615275
theorem B410219 : Blo 271824 410219 := bstep (se 1 (by rfl) ⟨307664, by rfl⟩ : syracuseStep 410219 = 615329) B615329
theorem B1032857 : Blo 271824 1032857 := bstep (se 2 (by rfl) ⟨387321, by rfl⟩ : syracuseStep 1032857 = 774643) B774643
theorem B1163929 : Blo 271824 1163929 := bstep (se 2 (by rfl) ⟨436473, by rfl⟩ : syracuseStep 1163929 = 872947) B872947
theorem B967339 : Blo 271824 967339 := bstep (se 1 (by rfl) ⟨725504, by rfl⟩ : syracuseStep 967339 = 1451009) B1451009
theorem B5259977 : Blo 271824 5259977 := bstep (se 2 (by rfl) ⟨1972491, by rfl⟩ : syracuseStep 5259977 = 3944983) B3944983
theorem B410447 : Blo 271824 410447 := bstep (se 1 (by rfl) ⟨307835, by rfl⟩ : syracuseStep 410447 = 615671) B615671
theorem B410843 : Blo 271824 410843 := bstep (se 1 (by rfl) ⟨308132, by rfl⟩ : syracuseStep 410843 = 616265) B616265
theorem B1557737 : Blo 271824 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B2639141 : Blo 271824 2639141 := bstep (se 4 (by rfl) ⟨247419, by rfl⟩ : syracuseStep 2639141 = 494839) B494839
theorem B1262891 : Blo 271824 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B411017 : Blo 271824 411017 := bstep (se 2 (by rfl) ⟨154131, by rfl⟩ : syracuseStep 411017 = 308263) B308263
theorem B1033661 : Blo 271824 1033661 := bstep (se 3 (by rfl) ⟨193811, by rfl⟩ : syracuseStep 1033661 = 387623) B387623
theorem B1394333 : Blo 271824 1394333 := bstep (se 3 (by rfl) ⟨261437, by rfl⟩ : syracuseStep 1394333 = 522875) B522875
theorem B411371 : Blo 271824 411371 := bstep (se 1 (by rfl) ⟨308528, by rfl⟩ : syracuseStep 411371 = 617057) B617057
theorem B411599 : Blo 271824 411599 := bstep (se 1 (by rfl) ⟨308699, by rfl⟩ : syracuseStep 411599 = 617399) B617399
theorem B411995 : Blo 271824 411995 := bstep (se 1 (by rfl) ⟨308996, by rfl⟩ : syracuseStep 411995 = 617993) B617993
theorem B346619 : Blo 271824 346619 := bstep (se 1 (by rfl) ⟨259964, by rfl⟩ : syracuseStep 346619 = 519929) B519929
theorem B1034815 : Blo 271824 1034815 := bstep (se 1 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 1034815 = 1552223) B1552223
theorem B412223 : Blo 271824 412223 := bstep (se 1 (by rfl) ⟨309167, by rfl⟩ : syracuseStep 412223 = 618335) B618335
theorem B412343 : Blo 271824 412343 := bstep (se 1 (by rfl) ⟨309257, by rfl⟩ : syracuseStep 412343 = 618515) B618515
theorem B2214647 : Blo 271824 2214647 := bstep (se 1 (by rfl) ⟨1660985, by rfl⟩ : syracuseStep 2214647 = 3321971) B3321971
theorem B412571 : Blo 271824 412571 := bstep (se 1 (by rfl) ⟨309428, by rfl⟩ : syracuseStep 412571 = 618857) B618857
theorem B1395629 : Blo 271824 1395629 := bstep (se 3 (by rfl) ⟨261680, by rfl⟩ : syracuseStep 1395629 = 523361) B523361
theorem B1985755 : Blo 271824 1985755 := bstep (se 1 (by rfl) ⟨1489316, by rfl⟩ : syracuseStep 1985755 = 2978633) B2978633
theorem B412967 : Blo 271824 412967 := bstep (se 1 (by rfl) ⟨309725, by rfl⟩ : syracuseStep 412967 = 619451) B619451
theorem B413051 : Blo 271824 413051 := bstep (se 1 (by rfl) ⟨309788, by rfl⟩ : syracuseStep 413051 = 619577) B619577
theorem B347591 : Blo 271824 347591 := bstep (se 1 (by rfl) ⟨260693, by rfl⟩ : syracuseStep 347591 = 521387) B521387
theorem B413177 : Blo 271824 413177 := bstep (se 2 (by rfl) ⟨154941, by rfl⟩ : syracuseStep 413177 = 309883) B309883
theorem B347743 : Blo 271824 347743 := bstep (se 1 (by rfl) ⟨260807, by rfl⟩ : syracuseStep 347743 = 521615) B521615
theorem B413279 : Blo 271824 413279 := bstep (se 1 (by rfl) ⟨309959, by rfl⟩ : syracuseStep 413279 = 619919) B619919
theorem B872203 : Blo 271824 872203 := bstep (se 1 (by rfl) ⟨654152, by rfl⟩ : syracuseStep 872203 = 1308305) B1308305
theorem B413495 : Blo 271824 413495 := bstep (se 1 (by rfl) ⟨310121, by rfl⟩ : syracuseStep 413495 = 620243) B620243
theorem B2642291 : Blo 271824 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B2085425 : Blo 271824 2085425 := bstep (se 2 (by rfl) ⟨782034, by rfl⟩ : syracuseStep 2085425 = 1564069) B1564069
theorem B2380337 : Blo 271824 2380337 := bstep (se 2 (by rfl) ⟨892626, by rfl⟩ : syracuseStep 2380337 = 1785253) B1785253
theorem B348743 : Blo 271824 348743 := bstep (se 1 (by rfl) ⟨261557, by rfl⟩ : syracuseStep 348743 = 523115) B523115
theorem B3723853 : Blo 271824 3723853 := bstep (se 3 (by rfl) ⟨698222, by rfl⟩ : syracuseStep 3723853 = 1396445) B1396445
theorem B5231303 : Blo 271824 5231303 := bstep (se 1 (by rfl) ⟨3923477, by rfl⟩ : syracuseStep 5231303 = 7846955) B7846955
theorem B873767 : Blo 271824 873767 := bstep (se 1 (by rfl) ⟨655325, by rfl⟩ : syracuseStep 873767 = 1310651) B1310651
theorem B611783 : Blo 271824 611783 := bstep (se 1 (by rfl) ⟨458837, by rfl⟩ : syracuseStep 611783 = 917675) B917675
theorem B612143 : Blo 271824 612143 := bstep (se 1 (by rfl) ⟨459107, by rfl⟩ : syracuseStep 612143 = 918215) B918215
theorem B415849 : Blo 271824 415849 := bstep (se 2 (by rfl) ⟨155943, by rfl⟩ : syracuseStep 415849 = 311887) B311887
theorem B1038521 : Blo 271824 1038521 := bstep (se 2 (by rfl) ⟨389445, by rfl⟩ : syracuseStep 1038521 = 778891) B778891
theorem B612719 : Blo 271824 612719 := bstep (se 1 (by rfl) ⟨459539, by rfl⟩ : syracuseStep 612719 = 919079) B919079
theorem B1038703 : Blo 271824 1038703 := bstep (se 1 (by rfl) ⟨779027, by rfl⟩ : syracuseStep 1038703 = 1558055) B1558055
theorem B612791 : Blo 271824 612791 := bstep (se 1 (by rfl) ⟨459593, by rfl⟩ : syracuseStep 612791 = 919187) B919187
theorem B612935 : Blo 271824 612935 := bstep (se 1 (by rfl) ⟨459701, by rfl⟩ : syracuseStep 612935 = 919403) B919403
theorem B612971 : Blo 271824 612971 := bstep (se 1 (by rfl) ⟨459728, by rfl⟩ : syracuseStep 612971 = 919457) B919457
theorem B2349931 : Blo 271824 2349931 := bstep (se 1 (by rfl) ⟨1762448, by rfl⟩ : syracuseStep 2349931 = 3524897) B3524897
theorem B613367 : Blo 271824 613367 := bstep (se 1 (by rfl) ⟨460025, by rfl⟩ : syracuseStep 613367 = 920051) B920051
theorem B744571 : Blo 271824 744571 := bstep (se 1 (by rfl) ⟨558428, by rfl⟩ : syracuseStep 744571 = 1116857) B1116857
theorem B1105085 : Blo 271824 1105085 := bstep (se 3 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 1105085 = 414407) B414407
theorem B613727 : Blo 271824 613727 := bstep (se 1 (by rfl) ⟨460295, by rfl⟩ : syracuseStep 613727 = 920591) B920591
theorem B614123 : Blo 271824 614123 := bstep (se 1 (by rfl) ⟨460592, by rfl⟩ : syracuseStep 614123 = 921185) B921185
theorem B941831 : Blo 271824 941831 := bstep (se 1 (by rfl) ⟨706373, by rfl⟩ : syracuseStep 941831 = 1412747) B1412747
theorem B778025 : Blo 271824 778025 := bstep (se 2 (by rfl) ⟨291759, by rfl⟩ : syracuseStep 778025 = 583519) B583519
theorem B2350889 : Blo 271824 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B614249 : Blo 271824 614249 := bstep (se 2 (by rfl) ⟨230343, by rfl⟩ : syracuseStep 614249 = 460687) B460687
theorem B1695953 : Blo 271824 1695953 := bstep (se 2 (by rfl) ⟨635982, by rfl⟩ : syracuseStep 1695953 = 1271965) B1271965
theorem B581897 : Blo 271824 581897 := bstep (se 2 (by rfl) ⟨218211, by rfl⟩ : syracuseStep 581897 = 436423) B436423
theorem B615095 : Blo 271824 615095 := bstep (se 1 (by rfl) ⟨461321, by rfl⟩ : syracuseStep 615095 = 922643) B922643
theorem B1041119 : Blo 271824 1041119 := bstep (se 1 (by rfl) ⟨780839, by rfl⟩ : syracuseStep 1041119 = 1561679) B1561679
theorem B615311 : Blo 271824 615311 := bstep (se 1 (by rfl) ⟨461483, by rfl⟩ : syracuseStep 615311 = 922967) B922967
theorem B1172627 : Blo 271824 1172627 := bstep (se 1 (by rfl) ⟨879470, by rfl⟩ : syracuseStep 1172627 = 1758941) B1758941
theorem B779507 : Blo 271824 779507 := bstep (se 1 (by rfl) ⟨584630, by rfl⟩ : syracuseStep 779507 = 1169261) B1169261
theorem B1992023 : Blo 271824 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B517499 : Blo 271824 517499 := bstep (se 1 (by rfl) ⟨388124, by rfl⟩ : syracuseStep 517499 = 776249) B776249
theorem B517727 : Blo 271824 517727 := bstep (se 1 (by rfl) ⟨388295, by rfl⟩ : syracuseStep 517727 = 776591) B776591
theorem B616031 : Blo 271824 616031 := bstep (se 1 (by rfl) ⟨462023, by rfl⟩ : syracuseStep 616031 = 924047) B924047
theorem B616247 : Blo 271824 616247 := bstep (se 1 (by rfl) ⟨462185, by rfl⟩ : syracuseStep 616247 = 924371) B924371
theorem B17885285 : Blo 271824 17885285 := bstep (se 4 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 17885285 = 3353491) B3353491
theorem B616553 : Blo 271824 616553 := bstep (se 2 (by rfl) ⟨231207, by rfl⟩ : syracuseStep 616553 = 462415) B462415
theorem B1566985 : Blo 271824 1566985 := bstep (se 2 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 1566985 = 1175239) B1175239
theorem B4680179 : Blo 271824 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B584263 : Blo 271824 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B617039 : Blo 271824 617039 := bstep (se 1 (by rfl) ⟨462779, by rfl⟩ : syracuseStep 617039 = 925559) B925559
theorem B617183 : Blo 271824 617183 := bstep (se 1 (by rfl) ⟨462887, by rfl⟩ : syracuseStep 617183 = 925775) B925775
theorem B1567511 : Blo 271824 1567511 := bstep (se 1 (by rfl) ⟨1175633, by rfl⟩ : syracuseStep 1567511 = 2351267) B2351267
theorem B387919 : Blo 271824 387919 := bstep (se 1 (by rfl) ⟨290939, by rfl⟩ : syracuseStep 387919 = 581879) B581879
theorem B617435 : Blo 271824 617435 := bstep (se 1 (by rfl) ⟨463076, by rfl⟩ : syracuseStep 617435 = 926153) B926153
theorem B617615 : Blo 271824 617615 := bstep (se 1 (by rfl) ⟨463211, by rfl⟩ : syracuseStep 617615 = 926423) B926423
theorem B617705 : Blo 271824 617705 := bstep (se 2 (by rfl) ⟨231639, by rfl⟩ : syracuseStep 617705 = 463279) B463279
theorem B617759 : Blo 271824 617759 := bstep (se 1 (by rfl) ⟨463319, by rfl⟩ : syracuseStep 617759 = 926639) B926639
theorem B585083 : Blo 271824 585083 := bstep (se 1 (by rfl) ⟨438812, by rfl⟩ : syracuseStep 585083 = 877625) B877625
theorem B388489 : Blo 271824 388489 := bstep (se 2 (by rfl) ⟨145683, by rfl⟩ : syracuseStep 388489 = 291367) B291367
theorem B1109497 : Blo 271824 1109497 := bstep (se 2 (by rfl) ⟨416061, by rfl⟩ : syracuseStep 1109497 = 832123) B832123
theorem B290299 : Blo 271824 290299 := bstep (se 1 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 290299 = 435449) B435449
theorem B3501629 : Blo 271824 3501629 := bstep (se 3 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 3501629 = 1313111) B1313111
theorem B1044049 : Blo 271824 1044049 := bstep (se 2 (by rfl) ⟨391518, by rfl⟩ : syracuseStep 1044049 = 783037) B783037
theorem B12906161 : Blo 271824 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B618281 : Blo 271824 618281 := bstep (se 2 (by rfl) ⟨231855, by rfl⟩ : syracuseStep 618281 = 463711) B463711
theorem B23949107 : Blo 271824 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B1077121 : Blo 271824 1077121 := bstep (se 2 (by rfl) ⟨403920, by rfl⟩ : syracuseStep 1077121 = 807841) B807841
theorem B1044353 : Blo 271824 1044353 := bstep (se 2 (by rfl) ⟨391632, by rfl⟩ : syracuseStep 1044353 = 783265) B783265
theorem B3960899 : Blo 271824 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B749821 : Blo 271824 749821 := bstep (se 3 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 749821 = 281183) B281183
theorem B4452641 : Blo 271824 4452641 := bstep (se 2 (by rfl) ⟨1669740, by rfl⟩ : syracuseStep 4452641 = 3339481) B3339481
theorem B880969 : Blo 271824 880969 := bstep (se 2 (by rfl) ⟨330363, by rfl⟩ : syracuseStep 880969 = 660727) B660727
theorem B1044809 : Blo 271824 1044809 := bstep (se 2 (by rfl) ⟨391803, by rfl⟩ : syracuseStep 1044809 = 783607) B783607
theorem B4223339 : Blo 271824 4223339 := bstep (se 1 (by rfl) ⟨3167504, by rfl⟩ : syracuseStep 4223339 = 6335009) B6335009
theorem B520825 : Blo 271824 520825 := bstep (se 2 (by rfl) ⟨195309, by rfl⟩ : syracuseStep 520825 = 390619) B390619
theorem B1569401 : Blo 271824 1569401 := bstep (se 2 (by rfl) ⟨588525, by rfl⟩ : syracuseStep 1569401 = 1177051) B1177051
theorem B619343 : Blo 271824 619343 := bstep (se 1 (by rfl) ⟨464507, by rfl⟩ : syracuseStep 619343 = 929015) B929015
theorem B619559 : Blo 271824 619559 := bstep (se 1 (by rfl) ⟨464669, by rfl⟩ : syracuseStep 619559 = 929339) B929339
theorem B619739 : Blo 271824 619739 := bstep (se 1 (by rfl) ⟨464804, by rfl⟩ : syracuseStep 619739 = 929609) B929609
theorem B292187 : Blo 271824 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B521569 : Blo 271824 521569 := bstep (se 2 (by rfl) ⟨195588, by rfl⟩ : syracuseStep 521569 = 391177) B391177
theorem B2618729 : Blo 271824 2618729 := bstep (se 2 (by rfl) ⟨982023, by rfl⟩ : syracuseStep 2618729 = 1964047) B1964047
theorem B619937 : Blo 271824 619937 := bstep (se 2 (by rfl) ⟨232476, by rfl⟩ : syracuseStep 619937 = 464953) B464953
theorem B5928889 : Blo 271824 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B1046479 : Blo 271824 1046479 := bstep (se 1 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 1046479 = 1569719) B1569719
theorem B620495 : Blo 271824 620495 := bstep (se 1 (by rfl) ⟨465371, by rfl⟩ : syracuseStep 620495 = 930743) B930743
theorem B522587 : Blo 271824 522587 := bstep (se 1 (by rfl) ⟨391940, by rfl⟩ : syracuseStep 522587 = 783881) B783881
theorem B1669501 : Blo 271824 1669501 := bstep (se 3 (by rfl) ⟨313031, by rfl⟩ : syracuseStep 1669501 = 626063) B626063
theorem B1046951 : Blo 271824 1046951 := bstep (se 1 (by rfl) ⟨785213, by rfl⟩ : syracuseStep 1046951 = 1570427) B1570427
theorem B981679 : Blo 271824 981679 := bstep (se 1 (by rfl) ⟨736259, by rfl⟩ : syracuseStep 981679 = 1472519) B1472519
theorem B1309459 : Blo 271824 1309459 := bstep (se 1 (by rfl) ⟨982094, by rfl⟩ : syracuseStep 1309459 = 1964189) B1964189
theorem B523027 : Blo 271824 523027 := bstep (se 1 (by rfl) ⟨392270, by rfl⟩ : syracuseStep 523027 = 784541) B784541
theorem B523255 : Blo 271824 523255 := bstep (se 1 (by rfl) ⟨392441, by rfl⟩ : syracuseStep 523255 = 784883) B784883
theorem B2489573 : Blo 271824 2489573 := bstep (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) B466795
theorem B523559 : Blo 271824 523559 := bstep (se 1 (by rfl) ⟨392669, by rfl⟩ : syracuseStep 523559 = 785339) B785339
theorem B556411 : Blo 271824 556411 := bstep (se 1 (by rfl) ⟨417308, by rfl⟩ : syracuseStep 556411 = 834617) B834617
theorem B1342985 : Blo 271824 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B458939 : Blo 271824 458939 := bstep (se 1 (by rfl) ⟨344204, by rfl⟩ : syracuseStep 458939 = 688409) B688409
theorem B1114393 : Blo 271824 1114393 := bstep (se 2 (by rfl) ⟨417897, by rfl⟩ : syracuseStep 1114393 = 835795) B835795
theorem B688571 : Blo 271824 688571 := bstep (se 1 (by rfl) ⟨516428, by rfl⟩ : syracuseStep 688571 = 1032857) B1032857
theorem B3506651 : Blo 271824 3506651 := bstep (se 1 (by rfl) ⟨2629988, by rfl⟩ : syracuseStep 3506651 = 5259977) B5259977
theorem B3736115 : Blo 271824 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B459499 : Blo 271824 459499 := bstep (se 1 (by rfl) ⟨344624, by rfl⟩ : syracuseStep 459499 = 689249) B689249
theorem B918269 : Blo 271824 918269 := bstep (se 3 (by rfl) ⟨172175, by rfl⟩ : syracuseStep 918269 = 344351) B344351
theorem B689107 : Blo 271824 689107 := bstep (se 1 (by rfl) ⟨516830, by rfl⟩ : syracuseStep 689107 = 1033661) B1033661
theorem B2622455 : Blo 271824 2622455 := bstep (se 1 (by rfl) ⟨1966841, by rfl⟩ : syracuseStep 2622455 = 3933683) B3933683
theorem B460471 : Blo 271824 460471 := bstep (se 1 (by rfl) ⟨345353, by rfl⟩ : syracuseStep 460471 = 690707) B690707
theorem B1476431 : Blo 271824 1476431 := bstep (se 1 (by rfl) ⟨1107323, by rfl⟩ : syracuseStep 1476431 = 2214647) B2214647
theorem B460775 : Blo 271824 460775 := bstep (se 1 (by rfl) ⟨345581, by rfl⟩ : syracuseStep 460775 = 691163) B691163
theorem B460991 : Blo 271824 460991 := bstep (se 1 (by rfl) ⟨345743, by rfl⟩ : syracuseStep 460991 = 691487) B691487
theorem B985483 : Blo 271824 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B6654433 : Blo 271824 6654433 := bstep (se 2 (by rfl) ⟨2495412, by rfl⟩ : syracuseStep 6654433 = 4990825) B4990825
theorem B1968745 : Blo 271824 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B920375 : Blo 271824 920375 := bstep (se 1 (by rfl) ⟨690281, by rfl⟩ : syracuseStep 920375 = 1380563) B1380563
theorem B461659 : Blo 271824 461659 := bstep (se 1 (by rfl) ⟨346244, by rfl⟩ : syracuseStep 461659 = 692489) B692489
theorem B1575973 : Blo 271824 1575973 := bstep (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) B295495
theorem B1379753 : Blo 271824 1379753 := bstep (se 2 (by rfl) ⟨517407, by rfl⟩ : syracuseStep 1379753 = 1034815) B1034815
theorem B2330045 : Blo 271824 2330045 := bstep (se 3 (by rfl) ⟨436883, by rfl⟩ : syracuseStep 2330045 = 873767) B873767
theorem B462631 : Blo 271824 462631 := bstep (se 1 (by rfl) ⟨346973, by rfl⟩ : syracuseStep 462631 = 693947) B693947
theorem B1380239 : Blo 271824 1380239 := bstep (se 1 (by rfl) ⟨1035179, by rfl⟩ : syracuseStep 1380239 = 2070359) B2070359
theorem B692347 : Blo 271824 692347 := bstep (se 1 (by rfl) ⟨519260, by rfl⟩ : syracuseStep 692347 = 1038521) B1038521
theorem B2068901 : Blo 271824 2068901 := bstep (se 4 (by rfl) ⟨193959, by rfl⟩ : syracuseStep 2068901 = 387919) B387919
theorem B1479329 : Blo 271824 1479329 := bstep (se 2 (by rfl) ⟨554748, by rfl⟩ : syracuseStep 1479329 = 1109497) B1109497
theorem B463657 : Blo 271824 463657 := bstep (se 2 (by rfl) ⟨173871, by rfl⟩ : syracuseStep 463657 = 347743) B347743
theorem B2626451 : Blo 271824 2626451 := bstep (se 1 (by rfl) ⟨1969838, by rfl⟩ : syracuseStep 2626451 = 3939677) B3939677
theorem B463927 : Blo 271824 463927 := bstep (se 1 (by rfl) ⟨347945, by rfl⟩ : syracuseStep 463927 = 695891) B695891
theorem B922697 : Blo 271824 922697 := bstep (se 2 (by rfl) ⟨346011, by rfl⟩ : syracuseStep 922697 = 692023) B692023
theorem B627887 : Blo 271824 627887 := bstep (se 1 (by rfl) ⟨470915, by rfl⟩ : syracuseStep 627887 = 941831) B941831
theorem B4199633 : Blo 271824 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B9934073 : Blo 271824 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B1021409 : Blo 271824 1021409 := bstep (se 2 (by rfl) ⟨383028, by rfl⟩ : syracuseStep 1021409 = 766057) B766057
theorem B694079 : Blo 271824 694079 := bstep (se 1 (by rfl) ⟨520559, by rfl⟩ : syracuseStep 694079 = 1041119) B1041119
theorem B3971045 : Blo 271824 3971045 := bstep (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) B744571
theorem B464879 : Blo 271824 464879 := bstep (se 1 (by rfl) ⟨348659, by rfl⟩ : syracuseStep 464879 = 697319) B697319
theorem B1185947 : Blo 271824 1185947 := bstep (se 1 (by rfl) ⟨889460, by rfl⟩ : syracuseStep 1185947 = 1778921) B1778921
theorem B694433 : Blo 271824 694433 := bstep (se 2 (by rfl) ⟨260412, by rfl⟩ : syracuseStep 694433 = 520825) B520825
theorem B1382831 : Blo 271824 1382831 := bstep (se 1 (by rfl) ⟨1037123, by rfl⟩ : syracuseStep 1382831 = 2074247) B2074247
theorem B465439 : Blo 271824 465439 := bstep (se 1 (by rfl) ⟨349079, by rfl⟩ : syracuseStep 465439 = 698159) B698159
theorem B924317 : Blo 271824 924317 := bstep (se 3 (by rfl) ⟨173309, by rfl⟩ : syracuseStep 924317 = 346619) B346619
theorem B924641 : Blo 271824 924641 := bstep (se 2 (by rfl) ⟨346740, by rfl⟩ : syracuseStep 924641 = 693481) B693481
theorem B3120119 : Blo 271824 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B695425 : Blo 271824 695425 := bstep (se 2 (by rfl) ⟨260784, by rfl⟩ : syracuseStep 695425 = 521569) B521569
theorem B924857 : Blo 271824 924857 := bstep (se 2 (by rfl) ⟨346821, by rfl⟩ : syracuseStep 924857 = 693643) B693643
theorem B2334419 : Blo 271824 2334419 := bstep (se 1 (by rfl) ⟨1750814, by rfl⟩ : syracuseStep 2334419 = 3501629) B3501629
theorem B15966071 : Blo 271824 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B7905185 : Blo 271824 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B696235 : Blo 271824 696235 := bstep (se 1 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 696235 = 1044353) B1044353
theorem B1482725 : Blo 271824 1482725 := bstep (se 4 (by rfl) ⟨139005, by rfl⟩ : syracuseStep 1482725 = 278011) B278011
theorem B696539 : Blo 271824 696539 := bstep (se 1 (by rfl) ⟨522404, by rfl⟩ : syracuseStep 696539 = 1044809) B1044809
theorem B1384937 : Blo 271824 1384937 := bstep (se 2 (by rfl) ⟨519351, by rfl⟩ : syracuseStep 1384937 = 1038703) B1038703
theorem B926315 : Blo 271824 926315 := bstep (se 1 (by rfl) ⟨694736, by rfl⟩ : syracuseStep 926315 = 1389473) B1389473
theorem B1385099 : Blo 271824 1385099 := bstep (se 1 (by rfl) ⟨1038824, by rfl⟩ : syracuseStep 1385099 = 2077649) B2077649
theorem B1745819 : Blo 271824 1745819 := bstep (se 1 (by rfl) ⟨1309364, by rfl⟩ : syracuseStep 1745819 = 2618729) B2618729
theorem B1745945 : Blo 271824 1745945 := bstep (se 2 (by rfl) ⟨654729, by rfl⟩ : syracuseStep 1745945 = 1309459) B1309459
theorem B697369 : Blo 271824 697369 := bstep (se 2 (by rfl) ⟨261513, by rfl⟩ : syracuseStep 697369 = 523027) B523027
theorem B926909 : Blo 271824 926909 := bstep (se 3 (by rfl) ⟨173795, by rfl⟩ : syracuseStep 926909 = 347591) B347591
theorem B697673 : Blo 271824 697673 := bstep (se 2 (by rfl) ⟨261627, by rfl⟩ : syracuseStep 697673 = 523255) B523255
theorem B3581293 : Blo 271824 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B271983 : Blo 271824 271983 := bstep (se 1 (by rfl) ⟨203987, by rfl⟩ : syracuseStep 271983 = 407975) B407975
theorem B697967 : Blo 271824 697967 := bstep (se 1 (by rfl) ⟨523475, by rfl⟩ : syracuseStep 697967 = 1046951) B1046951
theorem B272039 : Blo 271824 272039 := bstep (se 1 (by rfl) ⟨204029, by rfl⟩ : syracuseStep 272039 = 408059) B408059
theorem B272123 : Blo 271824 272123 := bstep (se 1 (by rfl) ⟨204092, by rfl⟩ : syracuseStep 272123 = 408185) B408185
theorem B272159 : Blo 271824 272159 := bstep (se 1 (by rfl) ⟨204119, by rfl⟩ : syracuseStep 272159 = 408239) B408239
theorem B272191 : Blo 271824 272191 := bstep (se 1 (by rfl) ⟨204143, by rfl⟩ : syracuseStep 272191 = 408287) B408287
theorem B993223 : Blo 271824 993223 := bstep (se 1 (by rfl) ⟨744917, by rfl⟩ : syracuseStep 993223 = 1489835) B1489835
theorem B272367 : Blo 271824 272367 := bstep (se 1 (by rfl) ⟨204275, by rfl⟩ : syracuseStep 272367 = 408551) B408551
theorem B3156047 : Blo 271824 3156047 := bstep (se 1 (by rfl) ⟨2367035, by rfl⟩ : syracuseStep 3156047 = 4734071) B4734071
theorem B2074733 : Blo 271824 2074733 := bstep (se 3 (by rfl) ⟨389012, by rfl⟩ : syracuseStep 2074733 = 778025) B778025
theorem B1321069 : Blo 271824 1321069 := bstep (se 3 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 1321069 = 495401) B495401
theorem B272539 : Blo 271824 272539 := bstep (se 1 (by rfl) ⟨204404, by rfl⟩ : syracuseStep 272539 = 408809) B408809
theorem B272575 : Blo 271824 272575 := bstep (se 1 (by rfl) ⟨204431, by rfl⟩ : syracuseStep 272575 = 408863) B408863
theorem B927935 : Blo 271824 927935 := bstep (se 1 (by rfl) ⟨695951, by rfl⟩ : syracuseStep 927935 = 1391903) B1391903
theorem B272687 : Blo 271824 272687 := bstep (se 1 (by rfl) ⟨204515, by rfl⟩ : syracuseStep 272687 = 409031) B409031
theorem B272923 : Blo 271824 272923 := bstep (se 1 (by rfl) ⟨204692, by rfl⟩ : syracuseStep 272923 = 409385) B409385
theorem B272927 : Blo 271824 272927 := bstep (se 1 (by rfl) ⟨204695, by rfl⟩ : syracuseStep 272927 = 409391) B409391
theorem B273243 : Blo 271824 273243 := bstep (se 1 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 273243 = 409865) B409865
theorem B273311 : Blo 271824 273311 := bstep (se 1 (by rfl) ⟨204983, by rfl⟩ : syracuseStep 273311 = 409967) B409967
theorem B1321991 : Blo 271824 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B273455 : Blo 271824 273455 := bstep (se 1 (by rfl) ⟨205091, by rfl⟩ : syracuseStep 273455 = 410183) B410183
theorem B306247 : Blo 271824 306247 := bstep (se 1 (by rfl) ⟨229685, by rfl⟩ : syracuseStep 306247 = 459371) B459371
theorem B273479 : Blo 271824 273479 := bstep (se 1 (by rfl) ⟨205109, by rfl⟩ : syracuseStep 273479 = 410219) B410219
theorem B273631 : Blo 271824 273631 := bstep (se 1 (by rfl) ⟨205223, by rfl⟩ : syracuseStep 273631 = 410447) B410447
theorem B273895 : Blo 271824 273895 := bstep (se 1 (by rfl) ⟨205421, by rfl⟩ : syracuseStep 273895 = 410843) B410843
theorem B1551905 : Blo 271824 1551905 := bstep (se 2 (by rfl) ⟨581964, by rfl⟩ : syracuseStep 1551905 = 1163929) B1163929
theorem B1289785 : Blo 271824 1289785 := bstep (se 2 (by rfl) ⟨483669, by rfl⟩ : syracuseStep 1289785 = 967339) B967339
theorem B274011 : Blo 271824 274011 := bstep (se 1 (by rfl) ⟨205508, by rfl⟩ : syracuseStep 274011 = 411017) B411017
theorem B831151 : Blo 271824 831151 := bstep (se 1 (by rfl) ⟨623363, by rfl⟩ : syracuseStep 831151 = 1246727) B1246727
theorem B929555 : Blo 271824 929555 := bstep (se 1 (by rfl) ⟨697166, by rfl⟩ : syracuseStep 929555 = 1394333) B1394333
theorem B274247 : Blo 271824 274247 := bstep (se 1 (by rfl) ⟨205685, by rfl⟩ : syracuseStep 274247 = 411371) B411371
theorem B274399 : Blo 271824 274399 := bstep (se 1 (by rfl) ⟨205799, by rfl⟩ : syracuseStep 274399 = 411599) B411599
theorem B929981 : Blo 271824 929981 := bstep (se 3 (by rfl) ⟨174371, by rfl⟩ : syracuseStep 929981 = 348743) B348743
theorem B274663 : Blo 271824 274663 := bstep (se 1 (by rfl) ⟨205997, by rfl⟩ : syracuseStep 274663 = 411995) B411995
theorem B274815 : Blo 271824 274815 := bstep (se 1 (by rfl) ⟨206111, by rfl⟩ : syracuseStep 274815 = 412223) B412223
theorem B274895 : Blo 271824 274895 := bstep (se 1 (by rfl) ⟨206171, by rfl⟩ : syracuseStep 274895 = 412343) B412343
theorem B275047 : Blo 271824 275047 := bstep (se 1 (by rfl) ⟨206285, by rfl⟩ : syracuseStep 275047 = 412571) B412571
theorem B930419 : Blo 271824 930419 := bstep (se 1 (by rfl) ⟨697814, by rfl⟩ : syracuseStep 930419 = 1395629) B1395629
theorem B2339543 : Blo 271824 2339543 := bstep (se 1 (by rfl) ⟨1754657, by rfl⟩ : syracuseStep 2339543 = 3509315) B3509315
theorem B275311 : Blo 271824 275311 := bstep (se 1 (by rfl) ⟨206483, by rfl⟩ : syracuseStep 275311 = 412967) B412967
theorem B930689 : Blo 271824 930689 := bstep (se 2 (by rfl) ⟨349008, by rfl⟩ : syracuseStep 930689 = 698017) B698017
theorem B275367 : Blo 271824 275367 := bstep (se 1 (by rfl) ⟨206525, by rfl⟩ : syracuseStep 275367 = 413051) B413051
theorem B275451 : Blo 271824 275451 := bstep (se 1 (by rfl) ⟨206588, by rfl⟩ : syracuseStep 275451 = 413177) B413177
theorem B275519 : Blo 271824 275519 := bstep (se 1 (by rfl) ⟨206639, by rfl⟩ : syracuseStep 275519 = 413279) B413279
theorem B275663 : Blo 271824 275663 := bstep (se 1 (by rfl) ⟨206747, by rfl⟩ : syracuseStep 275663 = 413495) B413495
theorem B1553863 : Blo 271824 1553863 := bstep (se 1 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 1553863 = 2330795) B2330795
theorem B1390283 : Blo 271824 1390283 := bstep (se 1 (by rfl) ⟨1042712, by rfl⟩ : syracuseStep 1390283 = 2085425) B2085425
theorem B1586891 : Blo 271824 1586891 := bstep (se 1 (by rfl) ⟨1190168, by rfl⟩ : syracuseStep 1586891 = 2380337) B2380337
theorem B5912281 : Blo 271824 5912281 := bstep (se 2 (by rfl) ⟨2217105, by rfl⟩ : syracuseStep 5912281 = 4434211) B4434211
theorem B3487535 : Blo 271824 3487535 := bstep (se 1 (by rfl) ⟨2615651, by rfl⟩ : syracuseStep 3487535 = 5231303) B5231303
theorem B309055 : Blo 271824 309055 := bstep (se 1 (by rfl) ⟨231791, by rfl⟩ : syracuseStep 309055 = 463583) B463583
theorem B1488797 : Blo 271824 1488797 := bstep (se 3 (by rfl) ⟨279149, by rfl⟩ : syracuseStep 1488797 = 558299) B558299
theorem B309343 : Blo 271824 309343 := bstep (se 1 (by rfl) ⟨232007, by rfl⟩ : syracuseStep 309343 = 464015) B464015
theorem B2013443 : Blo 271824 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B407849 : Blo 271824 407849 := bstep (se 2 (by rfl) ⟨152943, by rfl⟩ : syracuseStep 407849 = 305887) B305887
theorem B407855 : Blo 271824 407855 := bstep (se 1 (by rfl) ⟨305891, by rfl⟩ : syracuseStep 407855 = 611783) B611783
theorem B408095 : Blo 271824 408095 := bstep (se 1 (by rfl) ⟨306071, by rfl⟩ : syracuseStep 408095 = 612143) B612143
theorem B6666887 : Blo 271824 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B408479 : Blo 271824 408479 := bstep (se 1 (by rfl) ⟨306359, by rfl⟩ : syracuseStep 408479 = 612719) B612719
theorem B408527 : Blo 271824 408527 := bstep (se 1 (by rfl) ⟨306395, by rfl⟩ : syracuseStep 408527 = 612791) B612791
theorem B408617 : Blo 271824 408617 := bstep (se 2 (by rfl) ⟨153231, by rfl⟩ : syracuseStep 408617 = 306463) B306463
theorem B408623 : Blo 271824 408623 := bstep (se 1 (by rfl) ⟨306467, by rfl⟩ : syracuseStep 408623 = 612935) B612935
theorem B408647 : Blo 271824 408647 := bstep (se 1 (by rfl) ⟨306485, by rfl⟩ : syracuseStep 408647 = 612971) B612971
theorem B408911 : Blo 271824 408911 := bstep (se 1 (by rfl) ⟨306683, by rfl⟩ : syracuseStep 408911 = 613367) B613367
theorem B409001 : Blo 271824 409001 := bstep (se 2 (by rfl) ⟨153375, by rfl⟩ : syracuseStep 409001 = 306751) B306751
theorem B1392065 : Blo 271824 1392065 := bstep (se 2 (by rfl) ⟨522024, by rfl⟩ : syracuseStep 1392065 = 1044049) B1044049
theorem B736723 : Blo 271824 736723 := bstep (se 1 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 736723 = 1105085) B1105085
theorem B310759 : Blo 271824 310759 := bstep (se 1 (by rfl) ⟨233069, by rfl⟩ : syracuseStep 310759 = 466139) B466139
theorem B409151 : Blo 271824 409151 := bstep (se 1 (by rfl) ⟨306863, by rfl⟩ : syracuseStep 409151 = 613727) B613727
theorem B1162937 : Blo 271824 1162937 := bstep (se 2 (by rfl) ⟨436101, by rfl⟩ : syracuseStep 1162937 = 872203) B872203
theorem B409415 : Blo 271824 409415 := bstep (se 1 (by rfl) ⟨307061, by rfl⟩ : syracuseStep 409415 = 614123) B614123
theorem B409499 : Blo 271824 409499 := bstep (se 1 (by rfl) ⟨307124, by rfl⟩ : syracuseStep 409499 = 614249) B614249
theorem B1130635 : Blo 271824 1130635 := bstep (se 1 (by rfl) ⟨847976, by rfl⟩ : syracuseStep 1130635 = 1695953) B1695953
theorem B999761 : Blo 271824 999761 := bstep (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) B749821
theorem B410063 : Blo 271824 410063 := bstep (se 1 (by rfl) ⟨307547, by rfl⟩ : syracuseStep 410063 = 615095) B615095
theorem B410105 : Blo 271824 410105 := bstep (se 2 (by rfl) ⟨153789, by rfl⟩ : syracuseStep 410105 = 307579) B307579
theorem B410207 : Blo 271824 410207 := bstep (se 1 (by rfl) ⟨307655, by rfl⟩ : syracuseStep 410207 = 615311) B615311
theorem B4965137 : Blo 271824 4965137 := bstep (se 2 (by rfl) ⟨1861926, by rfl⟩ : syracuseStep 4965137 = 3723853) B3723853
theorem B1328015 : Blo 271824 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B344999 : Blo 271824 344999 := bstep (se 1 (by rfl) ⟨258749, by rfl⟩ : syracuseStep 344999 = 517499) B517499
theorem B345151 : Blo 271824 345151 := bstep (se 1 (by rfl) ⟨258863, by rfl⟩ : syracuseStep 345151 = 517727) B517727
theorem B410687 : Blo 271824 410687 := bstep (se 1 (by rfl) ⟨308015, by rfl⟩ : syracuseStep 410687 = 616031) B616031
theorem B410729 : Blo 271824 410729 := bstep (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) B308047
theorem B1885331 : Blo 271824 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B410831 : Blo 271824 410831 := bstep (se 1 (by rfl) ⟨308123, by rfl⟩ : syracuseStep 410831 = 616247) B616247
theorem B411035 : Blo 271824 411035 := bstep (se 1 (by rfl) ⟨308276, by rfl⟩ : syracuseStep 411035 = 616553) B616553
theorem B1033843 : Blo 271824 1033843 := bstep (se 1 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 1033843 = 1550765) B1550765
theorem B411257 : Blo 271824 411257 := bstep (se 2 (by rfl) ⟨154221, by rfl⟩ : syracuseStep 411257 = 308443) B308443
theorem B411359 : Blo 271824 411359 := bstep (se 1 (by rfl) ⟨308519, by rfl⟩ : syracuseStep 411359 = 617039) B617039
theorem B411455 : Blo 271824 411455 := bstep (se 1 (by rfl) ⟨308591, by rfl⟩ : syracuseStep 411455 = 617183) B617183
theorem B411623 : Blo 271824 411623 := bstep (se 1 (by rfl) ⟨308717, by rfl⟩ : syracuseStep 411623 = 617435) B617435
theorem B411641 : Blo 271824 411641 := bstep (se 2 (by rfl) ⟨154365, by rfl⟩ : syracuseStep 411641 = 308731) B308731
theorem B411743 : Blo 271824 411743 := bstep (se 1 (by rfl) ⟨308807, by rfl⟩ : syracuseStep 411743 = 617615) B617615
theorem B411803 : Blo 271824 411803 := bstep (se 1 (by rfl) ⟨308852, by rfl⟩ : syracuseStep 411803 = 617705) B617705
theorem B411839 : Blo 271824 411839 := bstep (se 1 (by rfl) ⟨308879, by rfl⟩ : syracuseStep 411839 = 617759) B617759
theorem B411881 : Blo 271824 411881 := bstep (se 2 (by rfl) ⟨154455, by rfl⟩ : syracuseStep 411881 = 308911) B308911
theorem B1558763 : Blo 271824 1558763 := bstep (se 1 (by rfl) ⟨1169072, by rfl⟩ : syracuseStep 1558763 = 2338145) B2338145
theorem B8604107 : Blo 271824 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B412187 : Blo 271824 412187 := bstep (se 1 (by rfl) ⟨309140, by rfl⟩ : syracuseStep 412187 = 618281) B618281
theorem B412265 : Blo 271824 412265 := bstep (se 2 (by rfl) ⟨154599, by rfl⟩ : syracuseStep 412265 = 309199) B309199
theorem B1395305 : Blo 271824 1395305 := bstep (se 2 (by rfl) ⟨523239, by rfl⟩ : syracuseStep 1395305 = 1046479) B1046479
theorem B2640599 : Blo 271824 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B2968427 : Blo 271824 2968427 := bstep (se 1 (by rfl) ⟨2226320, by rfl⟩ : syracuseStep 2968427 = 4452641) B4452641
theorem B412793 : Blo 271824 412793 := bstep (se 2 (by rfl) ⟨154797, by rfl⟩ : syracuseStep 412793 = 309595) B309595
theorem B412895 : Blo 271824 412895 := bstep (se 1 (by rfl) ⟨309671, by rfl⟩ : syracuseStep 412895 = 619343) B619343
theorem B1756403 : Blo 271824 1756403 := bstep (se 1 (by rfl) ⟨1317302, by rfl⟩ : syracuseStep 1756403 = 2634605) B2634605
theorem B412937 : Blo 271824 412937 := bstep (se 2 (by rfl) ⟨154851, by rfl⟩ : syracuseStep 412937 = 309703) B309703
theorem B6638861 : Blo 271824 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B413039 : Blo 271824 413039 := bstep (se 1 (by rfl) ⟨309779, by rfl⟩ : syracuseStep 413039 = 619559) B619559
theorem B413159 : Blo 271824 413159 := bstep (se 1 (by rfl) ⟨309869, by rfl⟩ : syracuseStep 413159 = 619739) B619739
theorem B413291 : Blo 271824 413291 := bstep (se 1 (by rfl) ⟨309968, by rfl⟩ : syracuseStep 413291 = 619937) B619937
theorem B1560221 : Blo 271824 1560221 := bstep (se 3 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 1560221 = 585083) B585083
theorem B413417 : Blo 271824 413417 := bstep (se 2 (by rfl) ⟨155031, by rfl⟩ : syracuseStep 413417 = 310063) B310063
theorem B4214585 : Blo 271824 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B3133241 : Blo 271824 3133241 := bstep (se 2 (by rfl) ⟨1174965, by rfl⟩ : syracuseStep 3133241 = 2349931) B2349931
theorem B413561 : Blo 271824 413561 := bstep (se 2 (by rfl) ⟨155085, by rfl⟩ : syracuseStep 413561 = 310171) B310171
theorem B413663 : Blo 271824 413663 := bstep (se 1 (by rfl) ⟨310247, by rfl⟩ : syracuseStep 413663 = 620495) B620495
theorem B3920075 : Blo 271824 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B348391 : Blo 271824 348391 := bstep (se 1 (by rfl) ⟨261293, by rfl⟩ : syracuseStep 348391 = 522587) B522587
theorem B1036759 : Blo 271824 1036759 := bstep (se 1 (by rfl) ⟨777569, by rfl⟩ : syracuseStep 1036759 = 1555139) B1555139
theorem B741881 : Blo 271824 741881 := bstep (se 2 (by rfl) ⟨278205, by rfl⟩ : syracuseStep 741881 = 556411) B556411
theorem B1167995 : Blo 271824 1167995 := bstep (se 1 (by rfl) ⟨875996, by rfl⟩ : syracuseStep 1167995 = 1751993) B1751993
theorem B414505 : Blo 271824 414505 := bstep (se 2 (by rfl) ⟨155439, by rfl⟩ : syracuseStep 414505 = 310879) B310879
theorem B4510505 : Blo 271824 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B349039 : Blo 271824 349039 := bstep (se 1 (by rfl) ⟨261779, by rfl⟩ : syracuseStep 349039 = 523559) B523559
theorem B611675 : Blo 271824 611675 := bstep (se 1 (by rfl) ⟨458756, by rfl⟩ : syracuseStep 611675 = 917513) B917513
theorem B612233 : Blo 271824 612233 := bstep (se 2 (by rfl) ⟨229587, by rfl⟩ : syracuseStep 612233 = 459175) B459175
theorem B612449 : Blo 271824 612449 := bstep (se 2 (by rfl) ⟨229668, by rfl⟩ : syracuseStep 612449 = 459337) B459337
theorem B1038491 : Blo 271824 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B1759427 : Blo 271824 1759427 := bstep (se 1 (by rfl) ⟨1319570, by rfl⟩ : syracuseStep 1759427 = 2639141) B2639141
theorem B841927 : Blo 271824 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B874793 : Blo 271824 874793 := bstep (se 2 (by rfl) ⟨328047, by rfl⟩ : syracuseStep 874793 = 656095) B656095
theorem B23943755 : Blo 271824 23943755 := bstep (se 1 (by rfl) ⟨17957816, by rfl⟩ : syracuseStep 23943755 = 35915633) B35915633
theorem B613799 : Blo 271824 613799 := bstep (se 1 (by rfl) ⟨460349, by rfl⟩ : syracuseStep 613799 = 920699) B920699
theorem B613979 : Blo 271824 613979 := bstep (se 1 (by rfl) ⟨460484, by rfl⟩ : syracuseStep 613979 = 920969) B920969
theorem B614267 : Blo 271824 614267 := bstep (se 1 (by rfl) ⟨460700, by rfl⟩ : syracuseStep 614267 = 921401) B921401
theorem B2121767 : Blo 271824 2121767 := bstep (se 1 (by rfl) ⟨1591325, by rfl⟩ : syracuseStep 2121767 = 3182651) B3182651
theorem B1761527 : Blo 271824 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B2941265 : Blo 271824 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B614753 : Blo 271824 614753 := bstep (se 2 (by rfl) ⟨230532, by rfl⟩ : syracuseStep 614753 = 461065) B461065
theorem B2089313 : Blo 271824 2089313 := bstep (se 2 (by rfl) ⟨783492, by rfl⟩ : syracuseStep 2089313 = 1566985) B1566985
theorem B876919 : Blo 271824 876919 := bstep (se 1 (by rfl) ⟨657689, by rfl⟩ : syracuseStep 876919 = 1315379) B1315379
theorem B614843 : Blo 271824 614843 := bstep (se 1 (by rfl) ⟨461132, by rfl⟩ : syracuseStep 614843 = 922265) B922265
theorem B21652103 : Blo 271824 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B779017 : Blo 271824 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B40035221 : Blo 271824 40035221 := bstep (se 6 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 40035221 = 1876651) B1876651
theorem B779165 : Blo 271824 779165 := bstep (se 3 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 779165 = 292187) B292187
theorem B615851 : Blo 271824 615851 := bstep (se 1 (by rfl) ⟨461888, by rfl⟩ : syracuseStep 615851 = 923777) B923777
theorem B2647673 : Blo 271824 2647673 := bstep (se 2 (by rfl) ⟨992877, by rfl⟩ : syracuseStep 2647673 = 1985755) B1985755
theorem B616103 : Blo 271824 616103 := bstep (se 1 (by rfl) ⟨462077, by rfl⟩ : syracuseStep 616103 = 924155) B924155
theorem B878303 : Blo 271824 878303 := bstep (se 1 (by rfl) ⟨658727, by rfl⟩ : syracuseStep 878303 = 1317455) B1317455
theorem B517985 : Blo 271824 517985 := bstep (se 2 (by rfl) ⟨194244, by rfl⟩ : syracuseStep 517985 = 388489) B388489
theorem B616391 : Blo 271824 616391 := bstep (se 1 (by rfl) ⟨462293, by rfl⟩ : syracuseStep 616391 = 924587) B924587
theorem B387065 : Blo 271824 387065 := bstep (se 2 (by rfl) ⟨145149, by rfl⟩ : syracuseStep 387065 = 290299) B290299
theorem B682219 : Blo 271824 682219 := bstep (se 1 (by rfl) ⟨511664, by rfl⟩ : syracuseStep 682219 = 1023329) B1023329
theorem B616697 : Blo 271824 616697 := bstep (se 2 (by rfl) ⟨231261, by rfl⟩ : syracuseStep 616697 = 462523) B462523
theorem B616751 : Blo 271824 616751 := bstep (se 1 (by rfl) ⟨462563, by rfl⟩ : syracuseStep 616751 = 925127) B925127
theorem B1436161 : Blo 271824 1436161 := bstep (se 2 (by rfl) ⟨538560, by rfl⟩ : syracuseStep 1436161 = 1077121) B1077121
theorem B616967 : Blo 271824 616967 := bstep (se 1 (by rfl) ⟨462725, by rfl⟩ : syracuseStep 616967 = 925451) B925451
theorem B1567259 : Blo 271824 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B617147 : Blo 271824 617147 := bstep (se 1 (by rfl) ⟨462860, by rfl⟩ : syracuseStep 617147 = 925721) B925721
theorem B1764089 : Blo 271824 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B387931 : Blo 271824 387931 := bstep (se 1 (by rfl) ⟨290948, by rfl⟩ : syracuseStep 387931 = 581897) B581897
theorem B1174625 : Blo 271824 1174625 := bstep (se 2 (by rfl) ⟨440484, by rfl⟩ : syracuseStep 1174625 = 880969) B880969
theorem B11234483 : Blo 271824 11234483 := bstep (se 1 (by rfl) ⟨8425862, by rfl⟩ : syracuseStep 11234483 = 16851725) B16851725
theorem B781751 : Blo 271824 781751 := bstep (se 1 (by rfl) ⟨586313, by rfl⟩ : syracuseStep 781751 = 1172627) B1172627
theorem B519671 : Blo 271824 519671 := bstep (se 1 (by rfl) ⟨389753, by rfl⟩ : syracuseStep 519671 = 779507) B779507
theorem B617975 : Blo 271824 617975 := bstep (se 1 (by rfl) ⟨463481, by rfl⟩ : syracuseStep 617975 = 926963) B926963
theorem B618047 : Blo 271824 618047 := bstep (se 1 (by rfl) ⟨463535, by rfl⟩ : syracuseStep 618047 = 927071) B927071
theorem B8449601 : Blo 271824 8449601 := bstep (se 2 (by rfl) ⟨3168600, by rfl⟩ : syracuseStep 8449601 = 6337201) B6337201
theorem B11923523 : Blo 271824 11923523 := bstep (se 1 (by rfl) ⟨8942642, by rfl⟩ : syracuseStep 11923523 = 17885285) B17885285
theorem B2257091 : Blo 271824 2257091 := bstep (se 1 (by rfl) ⟨1692818, by rfl⟩ : syracuseStep 2257091 = 3385637) B3385637
theorem B881111 : Blo 271824 881111 := bstep (se 1 (by rfl) ⟨660833, by rfl⟩ : syracuseStep 881111 = 1321667) B1321667
theorem B619001 : Blo 271824 619001 := bstep (se 2 (by rfl) ⟨232125, by rfl⟩ : syracuseStep 619001 = 464251) B464251
theorem B1045007 : Blo 271824 1045007 := bstep (se 1 (by rfl) ⟨783755, by rfl⟩ : syracuseStep 1045007 = 1567511) B1567511
theorem B619091 : Blo 271824 619091 := bstep (se 1 (by rfl) ⟨464318, by rfl⟩ : syracuseStep 619091 = 928637) B928637
theorem B619271 : Blo 271824 619271 := bstep (se 1 (by rfl) ⟨464453, by rfl⟩ : syracuseStep 619271 = 928907) B928907
theorem B1996019 : Blo 271824 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B554465 : Blo 271824 554465 := bstep (se 2 (by rfl) ⟨207924, by rfl⟩ : syracuseStep 554465 = 415849) B415849
theorem B2815559 : Blo 271824 2815559 := bstep (se 1 (by rfl) ⟨2111669, by rfl⟩ : syracuseStep 2815559 = 4223339) B4223339
theorem B1046267 : Blo 271824 1046267 := bstep (se 1 (by rfl) ⟨784700, by rfl⟩ : syracuseStep 1046267 = 1569401) B1569401
theorem B620351 : Blo 271824 620351 := bstep (se 1 (by rfl) ⟨465263, by rfl⟩ : syracuseStep 620351 = 930527) B930527
theorem B2226001 : Blo 271824 2226001 := bstep (se 2 (by rfl) ⟨834750, by rfl⟩ : syracuseStep 2226001 = 1669501) B1669501
theorem B8485013 : Blo 271824 8485013 := bstep (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) B397735
theorem B1308905 : Blo 271824 1308905 := bstep (se 2 (by rfl) ⟨490839, by rfl⟩ : syracuseStep 1308905 = 981679) B981679
theorem B3341189 : Blo 271824 3341189 := bstep (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) B626473
theorem B5340107 : Blo 271824 5340107 := bstep (se 1 (by rfl) ⟨4005080, by rfl⟩ : syracuseStep 5340107 = 8010161) B8010161
theorem B1670519 : Blo 271824 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B1408519 : Blo 271824 1408519 := bstep (se 1 (by rfl) ⟨1056389, by rfl⟩ : syracuseStep 1408519 = 2112779) B2112779
theorem B1507513 : Blo 271824 1507513 := bstep (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) B1130635
theorem B459047 : Blo 271824 459047 := bstep (se 1 (by rfl) ⟨344285, by rfl⟩ : syracuseStep 459047 = 688571) B688571
theorem B2490743 : Blo 271824 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B3310091 : Blo 271824 3310091 := bstep (se 1 (by rfl) ⟨2482568, by rfl⟩ : syracuseStep 3310091 = 4965137) B4965137
theorem B885343 : Blo 271824 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B984287 : Blo 271824 984287 := bstep (se 1 (by rfl) ⟨738215, by rfl⟩ : syracuseStep 984287 = 1476431) B1476431
theorem B918809 : Blo 271824 918809 := bstep (se 2 (by rfl) ⟨344553, by rfl⟩ : syracuseStep 918809 = 689107) B689107
theorem B460201 : Blo 271824 460201 := bstep (se 2 (by rfl) ⟨172575, by rfl⟩ : syracuseStep 460201 = 345151) B345151
theorem B5736071 : Blo 271824 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B1378457 : Blo 271824 1378457 := bstep (se 2 (by rfl) ⟨516921, by rfl⟩ : syracuseStep 1378457 = 1033843) B1033843
theorem B919835 : Blo 271824 919835 := bstep (se 1 (by rfl) ⟨689876, by rfl⟩ : syracuseStep 919835 = 1379753) B1379753
theorem B919997 : Blo 271824 919997 := bstep (se 3 (by rfl) ⟨172499, by rfl⟩ : syracuseStep 919997 = 344999) B344999
theorem B920159 : Blo 271824 920159 := bstep (se 1 (by rfl) ⟨690119, by rfl⟩ : syracuseStep 920159 = 1380239) B1380239
theorem B1379267 : Blo 271824 1379267 := bstep (se 1 (by rfl) ⟨1034450, by rfl⟩ : syracuseStep 1379267 = 2068901) B2068901
theorem B494587 : Blo 271824 494587 := bstep (se 1 (by rfl) ⟨370940, by rfl⟩ : syracuseStep 494587 = 741881) B741881
theorem B986219 : Blo 271824 986219 := bstep (se 1 (by rfl) ⟨739664, by rfl⟩ : syracuseStep 986219 = 1479329) B1479329
theorem B1313977 : Blo 271824 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B2624993 : Blo 271824 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B6622715 : Blo 271824 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B462719 : Blo 271824 462719 := bstep (se 1 (by rfl) ⟨347039, by rfl⟩ : syracuseStep 462719 = 694079) B694079
theorem B1478573 : Blo 271824 1478573 := bstep (se 3 (by rfl) ⟨277232, by rfl⟩ : syracuseStep 1478573 = 554465) B554465
theorem B2101297 : Blo 271824 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B692327 : Blo 271824 692327 := bstep (se 1 (by rfl) ⟨519245, by rfl⟩ : syracuseStep 692327 = 1038491) B1038491
theorem B790631 : Blo 271824 790631 := bstep (se 1 (by rfl) ⟨592973, by rfl⟩ : syracuseStep 790631 = 1185947) B1185947
theorem B462955 : Blo 271824 462955 := bstep (se 1 (by rfl) ⟨347216, by rfl⟩ : syracuseStep 462955 = 694433) B694433
theorem B921887 : Blo 271824 921887 := bstep (se 1 (by rfl) ⟨691415, by rfl⟩ : syracuseStep 921887 = 1382831) B1382831
theorem B15962503 : Blo 271824 15962503 := bstep (se 1 (by rfl) ⟨11971877, by rfl⟩ : syracuseStep 15962503 = 23943755) B23943755
theorem B4231709 : Blo 271824 4231709 := bstep (se 3 (by rfl) ⟨793445, by rfl⟩ : syracuseStep 4231709 = 1586891) B1586891
theorem B10589453 : Blo 271824 10589453 := bstep (se 3 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 10589453 = 3971045) B3971045
theorem B988483 : Blo 271824 988483 := bstep (se 1 (by rfl) ⟨741362, by rfl⟩ : syracuseStep 988483 = 1482725) B1482725
theorem B1414511 : Blo 271824 1414511 := bstep (se 1 (by rfl) ⟨1060883, by rfl⟩ : syracuseStep 1414511 = 2121767) B2121767
theorem B464359 : Blo 271824 464359 := bstep (se 1 (by rfl) ⟨348269, by rfl⟩ : syracuseStep 464359 = 696539) B696539
theorem B923129 : Blo 271824 923129 := bstep (se 2 (by rfl) ⟨346173, by rfl⟩ : syracuseStep 923129 = 692347) B692347
theorem B464521 : Blo 271824 464521 := bstep (se 2 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 464521 = 348391) B348391
theorem B923291 : Blo 271824 923291 := bstep (se 1 (by rfl) ⟨692468, by rfl⟩ : syracuseStep 923291 = 1384937) B1384937
theorem B923399 : Blo 271824 923399 := bstep (se 1 (by rfl) ⟨692549, by rfl⟩ : syracuseStep 923399 = 1385099) B1385099
theorem B1382345 : Blo 271824 1382345 := bstep (se 2 (by rfl) ⟨518379, by rfl⟩ : syracuseStep 1382345 = 1036759) B1036759
theorem B465115 : Blo 271824 465115 := bstep (se 1 (by rfl) ⟨348836, by rfl⟩ : syracuseStep 465115 = 697673) B697673
theorem B465311 : Blo 271824 465311 := bstep (se 1 (by rfl) ⟨348983, by rfl⟩ : syracuseStep 465311 = 697967) B697967
theorem B465385 : Blo 271824 465385 := bstep (se 2 (by rfl) ⟨174519, by rfl⟩ : syracuseStep 465385 = 349039) B349039
theorem B2104031 : Blo 271824 2104031 := bstep (se 1 (by rfl) ⟨1578023, by rfl⟩ : syracuseStep 2104031 = 3156047) B3156047
theorem B1383155 : Blo 271824 1383155 := bstep (se 1 (by rfl) ⟨1037366, by rfl⟩ : syracuseStep 1383155 = 2074733) B2074733
theorem B2071817 : Blo 271824 2071817 := bstep (se 2 (by rfl) ⟨776931, by rfl⟩ : syracuseStep 2071817 = 1553863) B1553863
theorem B1122569 : Blo 271824 1122569 := bstep (se 2 (by rfl) ⟨420963, by rfl⟩ : syracuseStep 1122569 = 841927) B841927
theorem B696671 : Blo 271824 696671 := bstep (se 1 (by rfl) ⟨522503, by rfl⟩ : syracuseStep 696671 = 1045007) B1045007
theorem B17703629 : Blo 271824 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B1877039 : Blo 271824 1877039 := bstep (se 1 (by rfl) ⟨1407779, by rfl⟩ : syracuseStep 1877039 = 2815559) B2815559
theorem B926855 : Blo 271824 926855 := bstep (se 1 (by rfl) ⟨695141, by rfl⟩ : syracuseStep 926855 = 1390283) B1390283
theorem B697511 : Blo 271824 697511 := bstep (se 1 (by rfl) ⟨523133, by rfl⟩ : syracuseStep 697511 = 1046267) B1046267
theorem B992531 : Blo 271824 992531 := bstep (se 1 (by rfl) ⟨744398, by rfl⟩ : syracuseStep 992531 = 1488797) B1488797
theorem B927233 : Blo 271824 927233 := bstep (se 2 (by rfl) ⟨347712, by rfl⟩ : syracuseStep 927233 = 695425) B695425
theorem B271899 : Blo 271824 271899 := bstep (se 1 (by rfl) ⟨203924, by rfl⟩ : syracuseStep 271899 = 407849) B407849
theorem B271903 : Blo 271824 271903 := bstep (se 1 (by rfl) ⟨203927, by rfl⟩ : syracuseStep 271903 = 407855) B407855
theorem B272063 : Blo 271824 272063 := bstep (se 1 (by rfl) ⟨204047, by rfl⟩ : syracuseStep 272063 = 408095) B408095
theorem B272319 : Blo 271824 272319 := bstep (se 1 (by rfl) ⟨204239, by rfl⟩ : syracuseStep 272319 = 408479) B408479
theorem B272351 : Blo 271824 272351 := bstep (se 1 (by rfl) ⟨204263, by rfl⟩ : syracuseStep 272351 = 408527) B408527
theorem B1878025 : Blo 271824 1878025 := bstep (se 2 (by rfl) ⟨704259, by rfl⟩ : syracuseStep 1878025 = 1408519) B1408519
theorem B272411 : Blo 271824 272411 := bstep (se 1 (by rfl) ⟨204308, by rfl⟩ : syracuseStep 272411 = 408617) B408617
theorem B272415 : Blo 271824 272415 := bstep (se 1 (by rfl) ⟨204311, by rfl⟩ : syracuseStep 272415 = 408623) B408623
theorem B272431 : Blo 271824 272431 := bstep (se 1 (by rfl) ⟨204323, by rfl⟩ : syracuseStep 272431 = 408647) B408647
theorem B6629525 : Blo 271824 6629525 := bstep (se 6 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 6629525 = 310759) B310759
theorem B272607 : Blo 271824 272607 := bstep (se 1 (by rfl) ⟨204455, by rfl⟩ : syracuseStep 272607 = 408911) B408911
theorem B272667 : Blo 271824 272667 := bstep (se 1 (by rfl) ⟨204500, by rfl⟩ : syracuseStep 272667 = 409001) B409001
theorem B928043 : Blo 271824 928043 := bstep (se 1 (by rfl) ⟨696032, by rfl⟩ : syracuseStep 928043 = 1392065) B1392065
theorem B272767 : Blo 271824 272767 := bstep (se 1 (by rfl) ⟨204575, by rfl⟩ : syracuseStep 272767 = 409151) B409151
theorem B272943 : Blo 271824 272943 := bstep (se 1 (by rfl) ⟨204707, by rfl⟩ : syracuseStep 272943 = 409415) B409415
theorem B928313 : Blo 271824 928313 := bstep (se 2 (by rfl) ⟨348117, by rfl⟩ : syracuseStep 928313 = 696235) B696235
theorem B272999 : Blo 271824 272999 := bstep (se 1 (by rfl) ⟨204749, by rfl⟩ : syracuseStep 272999 = 409499) B409499
theorem B305959 : Blo 271824 305959 := bstep (se 1 (by rfl) ⟨229469, by rfl⟩ : syracuseStep 305959 = 458939) B458939
theorem B273375 : Blo 271824 273375 := bstep (se 1 (by rfl) ⟨205031, by rfl⟩ : syracuseStep 273375 = 410063) B410063
theorem B2337767 : Blo 271824 2337767 := bstep (se 1 (by rfl) ⟨1753325, by rfl⟩ : syracuseStep 2337767 = 3506651) B3506651
theorem B273403 : Blo 271824 273403 := bstep (se 1 (by rfl) ⟨205052, by rfl⟩ : syracuseStep 273403 = 410105) B410105
theorem B1485857 : Blo 271824 1485857 := bstep (se 2 (by rfl) ⟨557196, by rfl⟩ : syracuseStep 1485857 = 1114393) B1114393
theorem B273471 : Blo 271824 273471 := bstep (se 1 (by rfl) ⟨205103, by rfl⟩ : syracuseStep 273471 = 410207) B410207
theorem B1748303 : Blo 271824 1748303 := bstep (se 1 (by rfl) ⟨1311227, by rfl⟩ : syracuseStep 1748303 = 2622455) B2622455
theorem B273791 : Blo 271824 273791 := bstep (se 1 (by rfl) ⟨205343, by rfl⟩ : syracuseStep 273791 = 410687) B410687
theorem B273819 : Blo 271824 273819 := bstep (se 1 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 273819 = 410729) B410729
theorem B1256887 : Blo 271824 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B273887 : Blo 271824 273887 := bstep (se 1 (by rfl) ⟨205415, by rfl⟩ : syracuseStep 273887 = 410831) B410831
theorem B2666029 : Blo 271824 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B274023 : Blo 271824 274023 := bstep (se 1 (by rfl) ⟨205517, by rfl⟩ : syracuseStep 274023 = 411035) B411035
theorem B274171 : Blo 271824 274171 := bstep (se 1 (by rfl) ⟨205628, by rfl⟩ : syracuseStep 274171 = 411257) B411257
theorem B274239 : Blo 271824 274239 := bstep (se 1 (by rfl) ⟨205679, by rfl⟩ : syracuseStep 274239 = 411359) B411359
theorem B274303 : Blo 271824 274303 := bstep (se 1 (by rfl) ⟨205727, by rfl⟩ : syracuseStep 274303 = 411455) B411455
theorem B307183 : Blo 271824 307183 := bstep (se 1 (by rfl) ⟨230387, by rfl⟩ : syracuseStep 307183 = 460775) B460775
theorem B274415 : Blo 271824 274415 := bstep (se 1 (by rfl) ⟨205811, by rfl⟩ : syracuseStep 274415 = 411623) B411623
theorem B274427 : Blo 271824 274427 := bstep (se 1 (by rfl) ⟨205820, by rfl⟩ : syracuseStep 274427 = 411641) B411641
theorem B929825 : Blo 271824 929825 := bstep (se 2 (by rfl) ⟨348684, by rfl⟩ : syracuseStep 929825 = 697369) B697369
theorem B274495 : Blo 271824 274495 := bstep (se 1 (by rfl) ⟨205871, by rfl⟩ : syracuseStep 274495 = 411743) B411743
theorem B274535 : Blo 271824 274535 := bstep (se 1 (by rfl) ⟨205901, by rfl⟩ : syracuseStep 274535 = 411803) B411803
theorem B307327 : Blo 271824 307327 := bstep (se 1 (by rfl) ⟨230495, by rfl⟩ : syracuseStep 307327 = 460991) B460991
theorem B274559 : Blo 271824 274559 := bstep (se 1 (by rfl) ⟨205919, by rfl⟩ : syracuseStep 274559 = 411839) B411839
theorem B274587 : Blo 271824 274587 := bstep (se 1 (by rfl) ⟨205940, by rfl⟩ : syracuseStep 274587 = 411881) B411881
theorem B274791 : Blo 271824 274791 := bstep (se 1 (by rfl) ⟨206093, by rfl⟩ : syracuseStep 274791 = 412187) B412187
theorem B274843 : Blo 271824 274843 := bstep (se 1 (by rfl) ⟨206132, by rfl⟩ : syracuseStep 274843 = 412265) B412265
theorem B930203 : Blo 271824 930203 := bstep (se 1 (by rfl) ⟨697652, by rfl⟩ : syracuseStep 930203 = 1395305) B1395305
theorem B1978951 : Blo 271824 1978951 := bstep (se 1 (by rfl) ⟨1484213, by rfl⟩ : syracuseStep 1978951 = 2968427) B2968427
theorem B275195 : Blo 271824 275195 := bstep (se 1 (by rfl) ⟨206396, by rfl⟩ : syracuseStep 275195 = 412793) B412793
theorem B275263 : Blo 271824 275263 := bstep (se 1 (by rfl) ⟨206447, by rfl⟩ : syracuseStep 275263 = 412895) B412895
theorem B275291 : Blo 271824 275291 := bstep (se 1 (by rfl) ⟨206468, by rfl⟩ : syracuseStep 275291 = 412937) B412937
theorem B275359 : Blo 271824 275359 := bstep (se 1 (by rfl) ⟨206519, by rfl⟩ : syracuseStep 275359 = 413039) B413039
theorem B1553363 : Blo 271824 1553363 := bstep (se 1 (by rfl) ⟨1165022, by rfl⟩ : syracuseStep 1553363 = 2330045) B2330045
theorem B275439 : Blo 271824 275439 := bstep (se 1 (by rfl) ⟨206579, by rfl⟩ : syracuseStep 275439 = 413159) B413159
theorem B275527 : Blo 271824 275527 := bstep (se 1 (by rfl) ⟨206645, by rfl⟩ : syracuseStep 275527 = 413291) B413291
theorem B275611 : Blo 271824 275611 := bstep (se 1 (by rfl) ⟨206708, by rfl⟩ : syracuseStep 275611 = 413417) B413417
theorem B275707 : Blo 271824 275707 := bstep (se 1 (by rfl) ⟨206780, by rfl⟩ : syracuseStep 275707 = 413561) B413561
theorem B1324297 : Blo 271824 1324297 := bstep (se 2 (by rfl) ⟨496611, by rfl⟩ : syracuseStep 1324297 = 993223) B993223
theorem B275775 : Blo 271824 275775 := bstep (se 1 (by rfl) ⟨206831, by rfl⟩ : syracuseStep 275775 = 413663) B413663
theorem B1750967 : Blo 271824 1750967 := bstep (se 1 (by rfl) ⟨1313225, by rfl⟩ : syracuseStep 1750967 = 2626451) B2626451
theorem B1914881 : Blo 271824 1914881 := bstep (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) B1436161
theorem B2799755 : Blo 271824 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B407783 : Blo 271824 407783 := bstep (se 1 (by rfl) ⟨305837, by rfl⟩ : syracuseStep 407783 = 611675) B611675
theorem B408155 : Blo 271824 408155 := bstep (se 1 (by rfl) ⟨306116, by rfl⟩ : syracuseStep 408155 = 612233) B612233
theorem B309919 : Blo 271824 309919 := bstep (se 1 (by rfl) ⟨232439, by rfl⟩ : syracuseStep 309919 = 464879) B464879
theorem B408299 : Blo 271824 408299 := bstep (se 1 (by rfl) ⟨306224, by rfl⟩ : syracuseStep 408299 = 612449) B612449
theorem B408329 : Blo 271824 408329 := bstep (se 2 (by rfl) ⟨153123, by rfl⟩ : syracuseStep 408329 = 306247) B306247
theorem B2342141 : Blo 271824 2342141 := bstep (se 3 (by rfl) ⟨439151, by rfl⟩ : syracuseStep 2342141 = 878303) B878303
theorem B2080079 : Blo 271824 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B1719713 : Blo 271824 1719713 := bstep (se 2 (by rfl) ⟨644892, by rfl⟩ : syracuseStep 1719713 = 1289785) B1289785
theorem B409199 : Blo 271824 409199 := bstep (se 1 (by rfl) ⟨306899, by rfl⟩ : syracuseStep 409199 = 613799) B613799
theorem B409319 : Blo 271824 409319 := bstep (se 1 (by rfl) ⟨306989, by rfl⟩ : syracuseStep 409319 = 613979) B613979
theorem B1556279 : Blo 271824 1556279 := bstep (se 1 (by rfl) ⟨1167209, by rfl⟩ : syracuseStep 1556279 = 2334419) B2334419
theorem B409511 : Blo 271824 409511 := bstep (se 1 (by rfl) ⟨307133, by rfl⟩ : syracuseStep 409511 = 614267) B614267
theorem B1032173 : Blo 271824 1032173 := bstep (se 3 (by rfl) ⟨193532, by rfl⟩ : syracuseStep 1032173 = 387065) B387065
theorem B409835 : Blo 271824 409835 := bstep (se 1 (by rfl) ⟨307376, by rfl⟩ : syracuseStep 409835 = 614753) B614753
theorem B1392875 : Blo 271824 1392875 := bstep (se 1 (by rfl) ⟨1044656, by rfl⟩ : syracuseStep 1392875 = 2089313) B2089313
theorem B409895 : Blo 271824 409895 := bstep (se 1 (by rfl) ⟨307421, by rfl⟩ : syracuseStep 409895 = 614843) B614843
theorem B14434735 : Blo 271824 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B26690147 : Blo 271824 26690147 := bstep (se 1 (by rfl) ⟨20017610, by rfl⟩ : syracuseStep 26690147 = 40035221) B40035221
theorem B1163879 : Blo 271824 1163879 := bstep (se 1 (by rfl) ⟨872909, by rfl⟩ : syracuseStep 1163879 = 1745819) B1745819
theorem B1163963 : Blo 271824 1163963 := bstep (se 1 (by rfl) ⟨872972, by rfl⟩ : syracuseStep 1163963 = 1745945) B1745945
theorem B410567 : Blo 271824 410567 := bstep (se 1 (by rfl) ⟨307925, by rfl⟩ : syracuseStep 410567 = 615851) B615851
theorem B410735 : Blo 271824 410735 := bstep (se 1 (by rfl) ⟨308051, by rfl⟩ : syracuseStep 410735 = 616103) B616103
theorem B345323 : Blo 271824 345323 := bstep (se 1 (by rfl) ⟨258992, by rfl⟩ : syracuseStep 345323 = 517985) B517985
theorem B410927 : Blo 271824 410927 := bstep (se 1 (by rfl) ⟨308195, by rfl⟩ : syracuseStep 410927 = 616391) B616391
theorem B411131 : Blo 271824 411131 := bstep (se 1 (by rfl) ⟨308348, by rfl⟩ : syracuseStep 411131 = 616697) B616697
theorem B411167 : Blo 271824 411167 := bstep (se 1 (by rfl) ⟨308375, by rfl⟩ : syracuseStep 411167 = 616751) B616751
theorem B411311 : Blo 271824 411311 := bstep (se 1 (by rfl) ⟨308483, by rfl⟩ : syracuseStep 411311 = 616967) B616967
theorem B17778365 : Blo 271824 17778365 := bstep (se 3 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 17778365 = 6666887) B6666887
theorem B411431 : Blo 271824 411431 := bstep (se 1 (by rfl) ⟨308573, by rfl⟩ : syracuseStep 411431 = 617147) B617147
theorem B7489655 : Blo 271824 7489655 := bstep (se 1 (by rfl) ⟨5617241, by rfl⟩ : syracuseStep 7489655 = 11234483) B11234483
theorem B7883041 : Blo 271824 7883041 := bstep (se 2 (by rfl) ⟨2956140, by rfl⟩ : syracuseStep 7883041 = 5912281) B5912281
theorem B411983 : Blo 271824 411983 := bstep (se 1 (by rfl) ⟨308987, by rfl⟩ : syracuseStep 411983 = 617975) B617975
theorem B346447 : Blo 271824 346447 := bstep (se 1 (by rfl) ⟨259835, by rfl⟩ : syracuseStep 346447 = 519671) B519671
theorem B1034603 : Blo 271824 1034603 := bstep (se 1 (by rfl) ⟨775952, by rfl⟩ : syracuseStep 1034603 = 1551905) B1551905
theorem B412031 : Blo 271824 412031 := bstep (se 1 (by rfl) ⟨309023, by rfl⟩ : syracuseStep 412031 = 618047) B618047
theorem B412073 : Blo 271824 412073 := bstep (se 2 (by rfl) ⟨154527, by rfl⟩ : syracuseStep 412073 = 309055) B309055
theorem B2968001 : Blo 271824 2968001 := bstep (se 2 (by rfl) ⟨1113000, by rfl⟩ : syracuseStep 2968001 = 2226001) B2226001
theorem B7949015 : Blo 271824 7949015 := bstep (se 1 (by rfl) ⟨5961761, by rfl⟩ : syracuseStep 7949015 = 11923523) B11923523
theorem B412457 : Blo 271824 412457 := bstep (se 2 (by rfl) ⟨154671, by rfl⟩ : syracuseStep 412457 = 309343) B309343
theorem B412667 : Blo 271824 412667 := bstep (se 1 (by rfl) ⟨309500, by rfl⟩ : syracuseStep 412667 = 619001) B619001
theorem B412727 : Blo 271824 412727 := bstep (se 1 (by rfl) ⟨309545, by rfl⟩ : syracuseStep 412727 = 619091) B619091
theorem B1559695 : Blo 271824 1559695 := bstep (se 1 (by rfl) ⟨1169771, by rfl⟩ : syracuseStep 1559695 = 2339543) B2339543
theorem B412847 : Blo 271824 412847 := bstep (se 1 (by rfl) ⟨309635, by rfl⟩ : syracuseStep 412847 = 619271) B619271
theorem B1330679 : Blo 271824 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B413567 : Blo 271824 413567 := bstep (se 1 (by rfl) ⟨310175, by rfl⟩ : syracuseStep 413567 = 620351) B620351
theorem B5656675 : Blo 271824 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B872603 : Blo 271824 872603 := bstep (se 1 (by rfl) ⟨654452, by rfl⟩ : syracuseStep 872603 = 1308905) B1308905
theorem B22532269 : Blo 271824 22532269 := bstep (se 3 (by rfl) ⟨4224800, by rfl⟩ : syracuseStep 22532269 = 8449601) B8449601
theorem B3101165 : Blo 271824 3101165 := bstep (se 3 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 3101165 = 1162937) B1162937
theorem B3560071 : Blo 271824 3560071 := bstep (se 1 (by rfl) ⟨2670053, by rfl⟩ : syracuseStep 3560071 = 5340107) B5340107
theorem B1169225 : Blo 271824 1169225 := bstep (se 2 (by rfl) ⟨438459, by rfl⟩ : syracuseStep 1169225 = 876919) B876919
theorem B612179 : Blo 271824 612179 := bstep (se 1 (by rfl) ⟨459134, by rfl⟩ : syracuseStep 612179 = 918269) B918269
theorem B612665 : Blo 271824 612665 := bstep (se 2 (by rfl) ⟨229749, by rfl⟩ : syracuseStep 612665 = 459499) B459499
theorem B1038689 : Blo 271824 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B1039175 : Blo 271824 1039175 := bstep (se 1 (by rfl) ⟨779381, by rfl⟩ : syracuseStep 1039175 = 1558763) B1558763
theorem B1760399 : Blo 271824 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B4775057 : Blo 271824 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B613583 : Blo 271824 613583 := bstep (se 1 (by rfl) ⟨460187, by rfl⟩ : syracuseStep 613583 = 920375) B920375
theorem B1170935 : Blo 271824 1170935 := bstep (se 1 (by rfl) ⟨878201, by rfl⟩ : syracuseStep 1170935 = 1756403) B1756403
theorem B613961 : Blo 271824 613961 := bstep (se 2 (by rfl) ⟨230235, by rfl⟩ : syracuseStep 613961 = 460471) B460471
theorem B1040147 : Blo 271824 1040147 := bstep (se 1 (by rfl) ⟨780110, by rfl⟩ : syracuseStep 1040147 = 1560221) B1560221
theorem B2809723 : Blo 271824 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B2088827 : Blo 271824 2088827 := bstep (se 1 (by rfl) ⟨1566620, by rfl⟩ : syracuseStep 2088827 = 3133241) B3133241
theorem B2613383 : Blo 271824 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B1761425 : Blo 271824 1761425 := bstep (se 2 (by rfl) ⟨660534, by rfl⟩ : syracuseStep 1761425 = 1321069) B1321069
theorem B909625 : Blo 271824 909625 := bstep (se 2 (by rfl) ⟨341109, by rfl⟩ : syracuseStep 909625 = 682219) B682219
theorem B778663 : Blo 271824 778663 := bstep (se 1 (by rfl) ⟨583997, by rfl⟩ : syracuseStep 778663 = 1167995) B1167995
theorem B3007003 : Blo 271824 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B8872577 : Blo 271824 8872577 := bstep (se 2 (by rfl) ⟨3327216, by rfl⟩ : syracuseStep 8872577 = 6654433) B6654433
theorem B615131 : Blo 271824 615131 := bstep (se 1 (by rfl) ⟨461348, by rfl⟩ : syracuseStep 615131 = 922697) B922697
theorem B418591 : Blo 271824 418591 := bstep (se 1 (by rfl) ⟨313943, by rfl⟩ : syracuseStep 418591 = 627887) B627887
theorem B680939 : Blo 271824 680939 := bstep (se 1 (by rfl) ⟨510704, by rfl⟩ : syracuseStep 680939 = 1021409) B1021409
theorem B517241 : Blo 271824 517241 := bstep (se 2 (by rfl) ⟨193965, by rfl⟩ : syracuseStep 517241 = 387931) B387931
theorem B615545 : Blo 271824 615545 := bstep (se 2 (by rfl) ⟨230829, by rfl⟩ : syracuseStep 615545 = 461659) B461659
theorem B1172951 : Blo 271824 1172951 := bstep (se 1 (by rfl) ⟨879713, by rfl⟩ : syracuseStep 1172951 = 1759427) B1759427
theorem B583195 : Blo 271824 583195 := bstep (se 1 (by rfl) ⟨437396, by rfl⟩ : syracuseStep 583195 = 874793) B874793
theorem B616211 : Blo 271824 616211 := bstep (se 1 (by rfl) ⟨462158, by rfl⟩ : syracuseStep 616211 = 924317) B924317
theorem B616427 : Blo 271824 616427 := bstep (se 1 (by rfl) ⟨462320, by rfl⟩ : syracuseStep 616427 = 924641) B924641
theorem B616571 : Blo 271824 616571 := bstep (se 1 (by rfl) ⟨462428, by rfl⟩ : syracuseStep 616571 = 924857) B924857
theorem B1108201 : Blo 271824 1108201 := bstep (se 2 (by rfl) ⟨415575, by rfl⟩ : syracuseStep 1108201 = 831151) B831151
theorem B616841 : Blo 271824 616841 := bstep (se 2 (by rfl) ⟨231315, by rfl⟩ : syracuseStep 616841 = 462631) B462631
theorem B10644047 : Blo 271824 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B5270123 : Blo 271824 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B1174351 : Blo 271824 1174351 := bstep (se 1 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 1174351 = 1761527) B1761527
theorem B1960843 : Blo 271824 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B617543 : Blo 271824 617543 := bstep (se 1 (by rfl) ⟨463157, by rfl⟩ : syracuseStep 617543 = 926315) B926315
theorem B519443 : Blo 271824 519443 := bstep (se 1 (by rfl) ⟨389582, by rfl⟩ : syracuseStep 519443 = 779165) B779165
theorem B617939 : Blo 271824 617939 := bstep (se 1 (by rfl) ⟨463454, by rfl⟩ : syracuseStep 617939 = 926909) B926909
theorem B552673 : Blo 271824 552673 := bstep (se 2 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 552673 = 414505) B414505
theorem B618209 : Blo 271824 618209 := bstep (se 2 (by rfl) ⟨231828, by rfl⟩ : syracuseStep 618209 = 463657) B463657
theorem B1765115 : Blo 271824 1765115 := bstep (se 1 (by rfl) ⟨1323836, by rfl⟩ : syracuseStep 1765115 = 2647673) B2647673
theorem B618569 : Blo 271824 618569 := bstep (se 2 (by rfl) ⟨231963, by rfl⟩ : syracuseStep 618569 = 463927) B463927
theorem B618623 : Blo 271824 618623 := bstep (se 1 (by rfl) ⟨463967, by rfl⟩ : syracuseStep 618623 = 927935) B927935
theorem B1044839 : Blo 271824 1044839 := bstep (se 1 (by rfl) ⟨783629, by rfl⟩ : syracuseStep 1044839 = 1567259) B1567259
theorem B1176059 : Blo 271824 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B881327 : Blo 271824 881327 := bstep (se 1 (by rfl) ⟨660995, by rfl⟩ : syracuseStep 881327 = 1321991) B1321991
theorem B783083 : Blo 271824 783083 := bstep (se 1 (by rfl) ⟨587312, by rfl⟩ : syracuseStep 783083 = 1174625) B1174625
theorem B521167 : Blo 271824 521167 := bstep (se 1 (by rfl) ⟨390875, by rfl⟩ : syracuseStep 521167 = 781751) B781751
theorem B8909837 : Blo 271824 8909837 := bstep (se 3 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 8909837 = 3341189) B3341189
theorem B619703 : Blo 271824 619703 := bstep (se 1 (by rfl) ⟨464777, by rfl⟩ : syracuseStep 619703 = 929555) B929555
theorem B619987 : Blo 271824 619987 := bstep (se 1 (by rfl) ⟨464990, by rfl⟩ : syracuseStep 619987 = 929981) B929981
theorem B1504727 : Blo 271824 1504727 := bstep (se 1 (by rfl) ⟨1128545, by rfl⟩ : syracuseStep 1504727 = 2257091) B2257091
theorem B587407 : Blo 271824 587407 := bstep (se 1 (by rfl) ⟨440555, by rfl⟩ : syracuseStep 587407 = 881111) B881111
theorem B620279 : Blo 271824 620279 := bstep (se 1 (by rfl) ⟨465209, by rfl⟩ : syracuseStep 620279 = 930419) B930419
theorem B620459 : Blo 271824 620459 := bstep (se 1 (by rfl) ⟨465344, by rfl⟩ : syracuseStep 620459 = 930689) B930689
theorem B620585 : Blo 271824 620585 := bstep (se 2 (by rfl) ⟨232719, by rfl⟩ : syracuseStep 620585 = 465439) B465439
theorem B2325023 : Blo 271824 2325023 := bstep (se 1 (by rfl) ⟨1743767, by rfl⟩ : syracuseStep 2325023 = 3487535) B3487535
theorem B1342295 : Blo 271824 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B982297 : Blo 271824 982297 := bstep (se 2 (by rfl) ⟨368361, by rfl⟩ : syracuseStep 982297 = 736723) B736723
theorem B1113679 : Blo 271824 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B17793431 : Blo 271824 17793431 := bstep (se 1 (by rfl) ⟨13345073, by rfl⟩ : syracuseStep 17793431 = 26690147) B26690147
theorem B1212833 : Blo 271824 1212833 := bstep (se 2 (by rfl) ⟨454812, by rfl⟩ : syracuseStep 1212833 = 909625) B909625
theorem B1180457 : Blo 271824 1180457 := bstep (se 2 (by rfl) ⟨442671, by rfl⟩ : syracuseStep 1180457 = 885343) B885343
theorem B656191 : Blo 271824 656191 := bstep (se 1 (by rfl) ⟨492143, by rfl⟩ : syracuseStep 656191 = 984287) B984287
theorem B558121 : Blo 271824 558121 := bstep (se 2 (by rfl) ⟨209295, by rfl⟩ : syracuseStep 558121 = 418591) B418591
theorem B918971 : Blo 271824 918971 := bstep (se 1 (by rfl) ⟨689228, by rfl⟩ : syracuseStep 918971 = 1378457) B1378457
theorem B689735 : Blo 271824 689735 := bstep (se 1 (by rfl) ⟨517301, by rfl⟩ : syracuseStep 689735 = 1034603) B1034603
theorem B919511 : Blo 271824 919511 := bstep (se 1 (by rfl) ⟨689633, by rfl⟩ : syracuseStep 919511 = 1379267) B1379267
theorem B657479 : Blo 271824 657479 := bstep (se 1 (by rfl) ⟨493109, by rfl⟩ : syracuseStep 657479 = 986219) B986219
theorem B887119 : Blo 271824 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B985715 : Blo 271824 985715 := bstep (se 1 (by rfl) ⟨739286, by rfl⟩ : syracuseStep 985715 = 1478573) B1478573
theorem B461551 : Blo 271824 461551 := bstep (se 1 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 461551 = 692327) B692327
theorem B527087 : Blo 271824 527087 := bstep (se 1 (by rfl) ⟨395315, by rfl⟩ : syracuseStep 527087 = 790631) B790631
theorem B1477601 : Blo 271824 1477601 := bstep (se 2 (by rfl) ⟨554100, by rfl⟩ : syracuseStep 1477601 = 1108201) B1108201
theorem B2067443 : Blo 271824 2067443 := bstep (se 1 (by rfl) ⟨1550582, by rfl⟩ : syracuseStep 2067443 = 3101165) B3101165
theorem B2821139 : Blo 271824 2821139 := bstep (se 1 (by rfl) ⟨2115854, by rfl⟩ : syracuseStep 2821139 = 4231709) B4231709
theorem B461929 : Blo 271824 461929 := bstep (se 2 (by rfl) ⟨173223, by rfl⟩ : syracuseStep 461929 = 346447) B346447
theorem B920861 : Blo 271824 920861 := bstep (se 3 (by rfl) ⟨172661, by rfl⟩ : syracuseStep 920861 = 345323) B345323
theorem B921563 : Blo 271824 921563 := bstep (se 1 (by rfl) ⟨691172, by rfl⟩ : syracuseStep 921563 = 1382345) B1382345
theorem B659449 : Blo 271824 659449 := bstep (se 2 (by rfl) ⟨247293, by rfl⟩ : syracuseStep 659449 = 494587) B494587
theorem B692459 : Blo 271824 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B922103 : Blo 271824 922103 := bstep (se 1 (by rfl) ⟨691577, by rfl⟩ : syracuseStep 922103 = 1383155) B1383155
theorem B692783 : Blo 271824 692783 := bstep (se 1 (by rfl) ⟨519587, by rfl⟩ : syracuseStep 692783 = 1039175) B1039175
theorem B3183371 : Blo 271824 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B1381211 : Blo 271824 1381211 := bstep (se 1 (by rfl) ⟨1035908, by rfl⟩ : syracuseStep 1381211 = 2071817) B2071817
theorem B693431 : Blo 271824 693431 := bstep (se 1 (by rfl) ⟨520073, by rfl⟩ : syracuseStep 693431 = 1040147) B1040147
theorem B1742255 : Blo 271824 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B7542233 : Blo 271824 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B464447 : Blo 271824 464447 := bstep (se 1 (by rfl) ⟨348335, by rfl⟩ : syracuseStep 464447 = 696671) B696671
theorem B11802419 : Blo 271824 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B1251359 : Blo 271824 1251359 := bstep (se 1 (by rfl) ⟨938519, by rfl⟩ : syracuseStep 1251359 = 1877039) B1877039
theorem B465007 : Blo 271824 465007 := bstep (se 1 (by rfl) ⟨348755, by rfl⟩ : syracuseStep 465007 = 697511) B697511
theorem B694889 : Blo 271824 694889 := bstep (se 2 (by rfl) ⟨260583, by rfl⟩ : syracuseStep 694889 = 521167) B521167
theorem B3513415 : Blo 271824 3513415 := bstep (se 1 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 3513415 = 5270123) B5270123
theorem B1317977 : Blo 271824 1317977 := bstep (se 2 (by rfl) ⟨494241, by rfl⟩ : syracuseStep 1317977 = 988483) B988483
theorem B826649 : Blo 271824 826649 := bstep (se 2 (by rfl) ⟨309993, by rfl⟩ : syracuseStep 826649 = 619987) B619987
theorem B990571 : Blo 271824 990571 := bstep (se 1 (by rfl) ⟨742928, by rfl⟩ : syracuseStep 990571 = 1485857) B1485857
theorem B696559 : Blo 271824 696559 := bstep (se 1 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 696559 = 1044839) B1044839
theorem B5939891 : Blo 271824 5939891 := bstep (se 1 (by rfl) ⟨4454918, by rfl⟩ : syracuseStep 5939891 = 8909837) B8909837
theorem B271855 : Blo 271824 271855 := bstep (se 1 (by rfl) ⟨203891, by rfl⟩ : syracuseStep 271855 = 407783) B407783
theorem B1550015 : Blo 271824 1550015 := bstep (se 1 (by rfl) ⟨1162511, by rfl⟩ : syracuseStep 1550015 = 2325023) B2325023
theorem B272103 : Blo 271824 272103 := bstep (se 1 (by rfl) ⟨204077, by rfl⟩ : syracuseStep 272103 = 408155) B408155
theorem B272199 : Blo 271824 272199 := bstep (se 1 (by rfl) ⟨204149, by rfl⟩ : syracuseStep 272199 = 408299) B408299
theorem B272219 : Blo 271824 272219 := bstep (se 1 (by rfl) ⟨204164, by rfl⟩ : syracuseStep 272219 = 408329) B408329
theorem B894863 : Blo 271824 894863 := bstep (se 1 (by rfl) ⟨671147, by rfl⟩ : syracuseStep 894863 = 1342295) B1342295
theorem B1484905 : Blo 271824 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B1386719 : Blo 271824 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B272799 : Blo 271824 272799 := bstep (se 1 (by rfl) ⟨204599, by rfl⟩ : syracuseStep 272799 = 409199) B409199
theorem B272879 : Blo 271824 272879 := bstep (se 1 (by rfl) ⟨204659, by rfl⟩ : syracuseStep 272879 = 409319) B409319
theorem B3746297 : Blo 271824 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B273007 : Blo 271824 273007 := bstep (se 1 (by rfl) ⟨204755, by rfl⟩ : syracuseStep 273007 = 409511) B409511
theorem B273223 : Blo 271824 273223 := bstep (se 1 (by rfl) ⟨204917, by rfl⟩ : syracuseStep 273223 = 409835) B409835
theorem B928583 : Blo 271824 928583 := bstep (se 1 (by rfl) ⟨696437, by rfl⟩ : syracuseStep 928583 = 1392875) B1392875
theorem B306031 : Blo 271824 306031 := bstep (se 1 (by rfl) ⟨229523, by rfl⟩ : syracuseStep 306031 = 459047) B459047
theorem B273263 : Blo 271824 273263 := bstep (se 1 (by rfl) ⟨204947, by rfl⟩ : syracuseStep 273263 = 409895) B409895
theorem B2010017 : Blo 271824 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B2206727 : Blo 271824 2206727 := bstep (se 1 (by rfl) ⟨1655045, by rfl⟩ : syracuseStep 2206727 = 3310091) B3310091
theorem B19246313 : Blo 271824 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B273711 : Blo 271824 273711 := bstep (se 1 (by rfl) ⟨205283, by rfl⟩ : syracuseStep 273711 = 410567) B410567
theorem B4009337 : Blo 271824 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B273823 : Blo 271824 273823 := bstep (se 1 (by rfl) ⟨205367, by rfl⟩ : syracuseStep 273823 = 410735) B410735
theorem B273951 : Blo 271824 273951 := bstep (se 1 (by rfl) ⟨205463, by rfl⟩ : syracuseStep 273951 = 410927) B410927
theorem B274087 : Blo 271824 274087 := bstep (se 1 (by rfl) ⟨205565, by rfl⟩ : syracuseStep 274087 = 411131) B411131
theorem B274111 : Blo 271824 274111 := bstep (se 1 (by rfl) ⟨205583, by rfl⟩ : syracuseStep 274111 = 411167) B411167
theorem B274207 : Blo 271824 274207 := bstep (se 1 (by rfl) ⟨205655, by rfl⟩ : syracuseStep 274207 = 411311) B411311
theorem B274287 : Blo 271824 274287 := bstep (se 1 (by rfl) ⟨205715, by rfl⟩ : syracuseStep 274287 = 411431) B411431
theorem B4993103 : Blo 271824 4993103 := bstep (se 1 (by rfl) ⟨3744827, by rfl⟩ : syracuseStep 4993103 = 7489655) B7489655
theorem B274655 : Blo 271824 274655 := bstep (se 1 (by rfl) ⟨205991, by rfl⟩ : syracuseStep 274655 = 411983) B411983
theorem B274687 : Blo 271824 274687 := bstep (se 1 (by rfl) ⟨206015, by rfl⟩ : syracuseStep 274687 = 412031) B412031
theorem B274715 : Blo 271824 274715 := bstep (se 1 (by rfl) ⟨206036, by rfl⟩ : syracuseStep 274715 = 412073) B412073
theorem B1978667 : Blo 271824 1978667 := bstep (se 1 (by rfl) ⟨1484000, by rfl⟩ : syracuseStep 1978667 = 2968001) B2968001
theorem B274971 : Blo 271824 274971 := bstep (se 1 (by rfl) ⟨206228, by rfl⟩ : syracuseStep 274971 = 412457) B412457
theorem B275111 : Blo 271824 275111 := bstep (se 1 (by rfl) ⟨206333, by rfl⟩ : syracuseStep 275111 = 412667) B412667
theorem B275151 : Blo 271824 275151 := bstep (se 1 (by rfl) ⟨206363, by rfl⟩ : syracuseStep 275151 = 412727) B412727
theorem B275231 : Blo 271824 275231 := bstep (se 1 (by rfl) ⟨206423, by rfl⟩ : syracuseStep 275231 = 412847) B412847
theorem B1749995 : Blo 271824 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B308479 : Blo 271824 308479 := bstep (se 1 (by rfl) ⟨231359, by rfl⟩ : syracuseStep 308479 = 462719) B462719
theorem B275711 : Blo 271824 275711 := bstep (se 1 (by rfl) ⟨206783, by rfl⟩ : syracuseStep 275711 = 413567) B413567
theorem B2504033 : Blo 271824 2504033 := bstep (se 2 (by rfl) ⟨939012, by rfl⟩ : syracuseStep 2504033 = 1878025) B1878025
theorem B7059635 : Blo 271824 7059635 := bstep (se 1 (by rfl) ⟨5294726, by rfl⟩ : syracuseStep 7059635 = 10589453) B10589453
theorem B407945 : Blo 271824 407945 := bstep (se 2 (by rfl) ⟨152979, by rfl⟩ : syracuseStep 407945 = 305959) B305959
theorem B408119 : Blo 271824 408119 := bstep (se 1 (by rfl) ⟨306089, by rfl⟩ : syracuseStep 408119 = 612179) B612179
theorem B2079593 : Blo 271824 2079593 := bstep (se 2 (by rfl) ⟨779847, by rfl⟩ : syracuseStep 2079593 = 1559695) B1559695
theorem B408443 : Blo 271824 408443 := bstep (se 1 (by rfl) ⟨306332, by rfl⟩ : syracuseStep 408443 = 612665) B612665
theorem B1751969 : Blo 271824 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B310207 : Blo 271824 310207 := bstep (se 1 (by rfl) ⟨232655, by rfl⟩ : syracuseStep 310207 = 465311) B465311
theorem B3554705 : Blo 271824 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B409055 : Blo 271824 409055 := bstep (se 1 (by rfl) ⟨306791, by rfl⟩ : syracuseStep 409055 = 613583) B613583
theorem B736897 : Blo 271824 736897 := bstep (se 2 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 736897 = 552673) B552673
theorem B409307 : Blo 271824 409307 := bstep (se 1 (by rfl) ⟨306980, by rfl⟩ : syracuseStep 409307 = 613961) B613961
theorem B1392551 : Blo 271824 1392551 := bstep (se 1 (by rfl) ⟨1044413, by rfl⟩ : syracuseStep 1392551 = 2088827) B2088827
theorem B409577 : Blo 271824 409577 := bstep (se 2 (by rfl) ⟨153591, by rfl⟩ : syracuseStep 409577 = 307183) B307183
theorem B2801729 : Blo 271824 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B409769 : Blo 271824 409769 := bstep (se 2 (by rfl) ⟨153663, by rfl⟩ : syracuseStep 409769 = 307327) B307327
theorem B5915051 : Blo 271824 5915051 := bstep (se 1 (by rfl) ⟨4436288, by rfl⟩ : syracuseStep 5915051 = 8872577) B8872577
theorem B410087 : Blo 271824 410087 := bstep (se 1 (by rfl) ⟨307565, by rfl⟩ : syracuseStep 410087 = 615131) B615131
theorem B21283337 : Blo 271824 21283337 := bstep (se 2 (by rfl) ⟨7981251, by rfl⟩ : syracuseStep 21283337 = 15962503) B15962503
theorem B344827 : Blo 271824 344827 := bstep (se 1 (by rfl) ⟨258620, by rfl⟩ : syracuseStep 344827 = 517241) B517241
theorem B410363 : Blo 271824 410363 := bstep (se 1 (by rfl) ⟨307772, by rfl⟩ : syracuseStep 410363 = 615545) B615545
theorem B2638601 : Blo 271824 2638601 := bstep (se 2 (by rfl) ⟨989475, by rfl⟩ : syracuseStep 2638601 = 1978951) B1978951
theorem B410807 : Blo 271824 410807 := bstep (se 1 (by rfl) ⟨308105, by rfl⟩ : syracuseStep 410807 = 616211) B616211
theorem B410951 : Blo 271824 410951 := bstep (se 1 (by rfl) ⟨308213, by rfl⟩ : syracuseStep 410951 = 616427) B616427
theorem B411047 : Blo 271824 411047 := bstep (se 1 (by rfl) ⟨308285, by rfl⟩ : syracuseStep 411047 = 616571) B616571
theorem B411227 : Blo 271824 411227 := bstep (se 1 (by rfl) ⟨308420, by rfl⟩ : syracuseStep 411227 = 616841) B616841
theorem B7096031 : Blo 271824 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B1558511 : Blo 271824 1558511 := bstep (se 1 (by rfl) ⟨1168883, by rfl⟩ : syracuseStep 1558511 = 2337767) B2337767
theorem B411695 : Blo 271824 411695 := bstep (se 1 (by rfl) ⟨308771, by rfl⟩ : syracuseStep 411695 = 617543) B617543
theorem B346295 : Blo 271824 346295 := bstep (se 1 (by rfl) ⟨259721, by rfl⟩ : syracuseStep 346295 = 519443) B519443
theorem B1165535 : Blo 271824 1165535 := bstep (se 1 (by rfl) ⟨874151, by rfl⟩ : syracuseStep 1165535 = 1748303) B1748303
theorem B6703397 : Blo 271824 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B411959 : Blo 271824 411959 := bstep (se 1 (by rfl) ⟨308969, by rfl⟩ : syracuseStep 411959 = 617939) B617939
theorem B412139 : Blo 271824 412139 := bstep (se 1 (by rfl) ⟨309104, by rfl⟩ : syracuseStep 412139 = 618209) B618209
theorem B412379 : Blo 271824 412379 := bstep (se 1 (by rfl) ⟨309284, by rfl⟩ : syracuseStep 412379 = 618569) B618569
theorem B412415 : Blo 271824 412415 := bstep (se 1 (by rfl) ⟨309311, by rfl⟩ : syracuseStep 412415 = 618623) B618623
theorem B1035575 : Blo 271824 1035575 := bstep (se 1 (by rfl) ⟨776681, by rfl⟩ : syracuseStep 1035575 = 1553363) B1553363
theorem B413135 : Blo 271824 413135 := bstep (se 1 (by rfl) ⟨309851, by rfl⟩ : syracuseStep 413135 = 619703) B619703
theorem B413225 : Blo 271824 413225 := bstep (se 2 (by rfl) ⟨154959, by rfl⟩ : syracuseStep 413225 = 309919) B309919
theorem B1003151 : Blo 271824 1003151 := bstep (se 1 (by rfl) ⟨752363, by rfl⟩ : syracuseStep 1003151 = 1504727) B1504727
theorem B413519 : Blo 271824 413519 := bstep (se 1 (by rfl) ⟨310139, by rfl⟩ : syracuseStep 413519 = 620279) B620279
theorem B413639 : Blo 271824 413639 := bstep (se 1 (by rfl) ⟨310229, by rfl⟩ : syracuseStep 413639 = 620459) B620459
theorem B1167311 : Blo 271824 1167311 := bstep (se 1 (by rfl) ⟨875483, by rfl⟩ : syracuseStep 1167311 = 1750967) B1750967
theorem B413723 : Blo 271824 413723 := bstep (se 1 (by rfl) ⟨310292, by rfl⟩ : syracuseStep 413723 = 620585) B620585
theorem B1561427 : Blo 271824 1561427 := bstep (se 1 (by rfl) ⟨1171070, by rfl⟩ : syracuseStep 1561427 = 2342141) B2342141
theorem B1037519 : Blo 271824 1037519 := bstep (se 1 (by rfl) ⟨778139, by rfl⟩ : syracuseStep 1037519 = 1556279) B1556279
theorem B1660495 : Blo 271824 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B775919 : Blo 271824 775919 := bstep (se 1 (by rfl) ⟨581939, by rfl⟩ : syracuseStep 775919 = 1163879) B1163879
theorem B775975 : Blo 271824 775975 := bstep (se 1 (by rfl) ⟨581981, by rfl⟩ : syracuseStep 775975 = 1163963) B1163963
theorem B1038217 : Blo 271824 1038217 := bstep (se 2 (by rfl) ⟨389331, by rfl⟩ : syracuseStep 1038217 = 778663) B778663
theorem B612539 : Blo 271824 612539 := bstep (se 1 (by rfl) ⟨459404, by rfl⟩ : syracuseStep 612539 = 918809) B918809
theorem B3824047 : Blo 271824 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B11852243 : Blo 271824 11852243 := bstep (se 1 (by rfl) ⟨8889182, by rfl⟩ : syracuseStep 11852243 = 17778365) B17778365
theorem B3136157 : Blo 271824 3136157 := bstep (se 3 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 3136157 = 1176059) B1176059
theorem B613223 : Blo 271824 613223 := bstep (se 1 (by rfl) ⟨459917, by rfl⟩ : syracuseStep 613223 = 919835) B919835
theorem B613331 : Blo 271824 613331 := bstep (se 1 (by rfl) ⟨459998, by rfl⟩ : syracuseStep 613331 = 919997) B919997
theorem B613439 : Blo 271824 613439 := bstep (se 1 (by rfl) ⟨460079, by rfl⟩ : syracuseStep 613439 = 920159) B920159
theorem B2350205 : Blo 271824 2350205 := bstep (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) B881327
theorem B5299343 : Blo 271824 5299343 := bstep (se 1 (by rfl) ⟨3974507, by rfl⟩ : syracuseStep 5299343 = 7949015) B7949015
theorem B613601 : Blo 271824 613601 := bstep (se 2 (by rfl) ⟨230100, by rfl⟩ : syracuseStep 613601 = 460201) B460201
theorem B777593 : Blo 271824 777593 := bstep (se 2 (by rfl) ⟨291597, by rfl⟩ : syracuseStep 777593 = 583195) B583195
theorem B4415143 : Blo 271824 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B581735 : Blo 271824 581735 := bstep (se 1 (by rfl) ⟨436301, by rfl⟩ : syracuseStep 581735 = 872603) B872603
theorem B614591 : Blo 271824 614591 := bstep (se 1 (by rfl) ⟨460943, by rfl⟩ : syracuseStep 614591 = 921887) B921887
theorem B10510721 : Blo 271824 10510721 := bstep (se 2 (by rfl) ⟨3941520, by rfl⟩ : syracuseStep 10510721 = 7883041) B7883041
theorem B2646749 : Blo 271824 2646749 := bstep (se 3 (by rfl) ⟨496265, by rfl⟩ : syracuseStep 2646749 = 992531) B992531
theorem B943007 : Blo 271824 943007 := bstep (se 1 (by rfl) ⟨707255, by rfl⟩ : syracuseStep 943007 = 1414511) B1414511
theorem B615419 : Blo 271824 615419 := bstep (se 1 (by rfl) ⟨461564, by rfl⟩ : syracuseStep 615419 = 923129) B923129
theorem B615527 : Blo 271824 615527 := bstep (se 1 (by rfl) ⟨461645, by rfl⟩ : syracuseStep 615527 = 923291) B923291
theorem B1565801 : Blo 271824 1565801 := bstep (se 2 (by rfl) ⟨587175, by rfl⟩ : syracuseStep 1565801 = 1174351) B1174351
theorem B615599 : Blo 271824 615599 := bstep (se 1 (by rfl) ⟨461699, by rfl⟩ : syracuseStep 615599 = 923399) B923399
theorem B2614457 : Blo 271824 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B779483 : Blo 271824 779483 := bstep (se 1 (by rfl) ⟨584612, by rfl⟩ : syracuseStep 779483 = 1169225) B1169225
theorem B1402687 : Blo 271824 1402687 := bstep (se 1 (by rfl) ⟨1052015, by rfl⟩ : syracuseStep 1402687 = 2104031) B2104031
theorem B1173599 : Blo 271824 1173599 := bstep (se 1 (by rfl) ⟨880199, by rfl⟩ : syracuseStep 1173599 = 1760399) B1760399
theorem B780623 : Blo 271824 780623 := bstep (se 1 (by rfl) ⟨585467, by rfl⟩ : syracuseStep 780623 = 1170935) B1170935
theorem B5106349 : Blo 271824 5106349 := bstep (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) B1914881
theorem B1174283 : Blo 271824 1174283 := bstep (se 1 (by rfl) ⟨880712, by rfl⟩ : syracuseStep 1174283 = 1761425) B1761425
theorem B617273 : Blo 271824 617273 := bstep (se 2 (by rfl) ⟨231477, by rfl⟩ : syracuseStep 617273 = 462955) B462955
theorem B748379 : Blo 271824 748379 := bstep (se 1 (by rfl) ⟨561284, by rfl⟩ : syracuseStep 748379 = 1122569) B1122569
theorem B30043025 : Blo 271824 30043025 := bstep (se 2 (by rfl) ⟨11266134, by rfl⟩ : syracuseStep 30043025 = 22532269) B22532269
theorem B453959 : Blo 271824 453959 := bstep (se 1 (by rfl) ⟨340469, by rfl⟩ : syracuseStep 453959 = 680939) B680939
theorem B617903 : Blo 271824 617903 := bstep (se 1 (by rfl) ⟨463427, by rfl⟩ : syracuseStep 617903 = 926855) B926855
theorem B4746761 : Blo 271824 4746761 := bstep (se 2 (by rfl) ⟨1780035, by rfl⟩ : syracuseStep 4746761 = 3560071) B3560071
theorem B781967 : Blo 271824 781967 := bstep (se 1 (by rfl) ⟨586475, by rfl⟩ : syracuseStep 781967 = 1172951) B1172951
theorem B618155 : Blo 271824 618155 := bstep (se 1 (by rfl) ⟨463616, by rfl⟩ : syracuseStep 618155 = 927233) B927233
theorem B4419683 : Blo 271824 4419683 := bstep (se 1 (by rfl) ⟨3314762, by rfl⟩ : syracuseStep 4419683 = 6629525) B6629525
theorem B618695 : Blo 271824 618695 := bstep (se 1 (by rfl) ⟨464021, by rfl⟩ : syracuseStep 618695 = 928043) B928043
theorem B1765729 : Blo 271824 1765729 := bstep (se 2 (by rfl) ⟨662148, by rfl⟩ : syracuseStep 1765729 = 1324297) B1324297
theorem B618875 : Blo 271824 618875 := bstep (se 1 (by rfl) ⟨464156, by rfl⟩ : syracuseStep 618875 = 928313) B928313
theorem B619145 : Blo 271824 619145 := bstep (se 2 (by rfl) ⟨232179, by rfl⟩ : syracuseStep 619145 = 464359) B464359
theorem B619361 : Blo 271824 619361 := bstep (se 2 (by rfl) ⟨232260, by rfl⟩ : syracuseStep 619361 = 464521) B464521
theorem B783209 : Blo 271824 783209 := bstep (se 2 (by rfl) ⟨293703, by rfl⟩ : syracuseStep 783209 = 587407) B587407
theorem B1176743 : Blo 271824 1176743 := bstep (se 1 (by rfl) ⟨882557, by rfl⟩ : syracuseStep 1176743 = 1765115) B1765115
theorem B619883 : Blo 271824 619883 := bstep (se 1 (by rfl) ⟨464912, by rfl⟩ : syracuseStep 619883 = 929825) B929825
theorem B620135 : Blo 271824 620135 := bstep (se 1 (by rfl) ⟨465101, by rfl⟩ : syracuseStep 620135 = 930203) B930203
theorem B620153 : Blo 271824 620153 := bstep (se 2 (by rfl) ⟨232557, by rfl⟩ : syracuseStep 620153 = 465115) B465115
theorem B522055 : Blo 271824 522055 := bstep (se 1 (by rfl) ⟨391541, by rfl⟩ : syracuseStep 522055 = 783083) B783083
theorem B620513 : Blo 271824 620513 := bstep (se 2 (by rfl) ⟨232692, by rfl⟩ : syracuseStep 620513 = 465385) B465385
theorem B1866503 : Blo 271824 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B1309729 : Blo 271824 1309729 := bstep (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) B982297
theorem B1146475 : Blo 271824 1146475 := bstep (se 1 (by rfl) ⟨859856, by rfl⟩ : syracuseStep 1146475 = 1719713) B1719713
theorem B688115 : Blo 271824 688115 := bstep (se 1 (by rfl) ⟨516086, by rfl⟩ : syracuseStep 688115 = 1032173) B1032173
theorem B1867819 : Blo 271824 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B11862287 : Blo 271824 11862287 := bstep (se 1 (by rfl) ⟨8896715, by rfl⟩ : syracuseStep 11862287 = 17793431) B17793431
theorem B14188891 : Blo 271824 14188891 := bstep (se 1 (by rfl) ⟨10641668, by rfl⟩ : syracuseStep 14188891 = 21283337) B21283337
theorem B786971 : Blo 271824 786971 := bstep (se 1 (by rfl) ⟨590228, by rfl⟩ : syracuseStep 786971 = 1180457) B1180457
theorem B459769 : Blo 271824 459769 := bstep (se 2 (by rfl) ⟨172413, by rfl⟩ : syracuseStep 459769 = 344827) B344827
theorem B459823 : Blo 271824 459823 := bstep (se 1 (by rfl) ⟨344867, by rfl⟩ : syracuseStep 459823 = 689735) B689735
theorem B657143 : Blo 271824 657143 := bstep (se 1 (by rfl) ⟨492857, by rfl⟩ : syracuseStep 657143 = 985715) B985715
theorem B985067 : Blo 271824 985067 := bstep (se 1 (by rfl) ⟨738800, by rfl⟩ : syracuseStep 985067 = 1477601) B1477601
theorem B1378295 : Blo 271824 1378295 := bstep (se 1 (by rfl) ⟨1033721, by rfl⟩ : syracuseStep 1378295 = 2067443) B2067443
theorem B690383 : Blo 271824 690383 := bstep (se 1 (by rfl) ⟨517787, by rfl⟩ : syracuseStep 690383 = 1035575) B1035575
theorem B1870249 : Blo 271824 1870249 := bstep (se 2 (by rfl) ⟨701343, by rfl⟩ : syracuseStep 1870249 = 1402687) B1402687
theorem B461639 : Blo 271824 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B461855 : Blo 271824 461855 := bstep (se 1 (by rfl) ⟨346391, by rfl⟩ : syracuseStep 461855 = 692783) B692783
theorem B920807 : Blo 271824 920807 := bstep (se 1 (by rfl) ⟨690605, by rfl⟩ : syracuseStep 920807 = 1381211) B1381211
theorem B462287 : Blo 271824 462287 := bstep (se 1 (by rfl) ⟨346715, by rfl⟩ : syracuseStep 462287 = 693431) B693431
theorem B691679 : Blo 271824 691679 := bstep (se 1 (by rfl) ⟨518759, by rfl⟩ : syracuseStep 691679 = 1037519) B1037519
theorem B7868279 : Blo 271824 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B7901495 : Blo 271824 7901495 := bstep (se 1 (by rfl) ⟨5926121, by rfl⟩ : syracuseStep 7901495 = 11852243) B11852243
theorem B463259 : Blo 271824 463259 := bstep (se 1 (by rfl) ⟨347444, by rfl⟩ : syracuseStep 463259 = 694889) B694889
theorem B923453 : Blo 271824 923453 := bstep (se 3 (by rfl) ⟨173147, by rfl⟩ : syracuseStep 923453 = 346295) B346295
theorem B1742971 : Blo 271824 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B596575 : Blo 271824 596575 := bstep (se 1 (by rfl) ⟨447431, by rfl⟩ : syracuseStep 596575 = 894863) B894863
theorem B924479 : Blo 271824 924479 := bstep (se 1 (by rfl) ⟨693359, by rfl⟩ : syracuseStep 924479 = 1386719) B1386719
theorem B498919 : Blo 271824 498919 := bstep (se 1 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 498919 = 748379) B748379
theorem B20028683 : Blo 271824 20028683 := bstep (se 1 (by rfl) ⟨15021512, by rfl⟩ : syracuseStep 20028683 = 30043025) B30043025
theorem B302639 : Blo 271824 302639 := bstep (se 1 (by rfl) ⟨226979, by rfl⟩ : syracuseStep 302639 = 453959) B453959
theorem B696073 : Blo 271824 696073 := bstep (se 2 (by rfl) ⟨261027, by rfl⟩ : syracuseStep 696073 = 522055) B522055
theorem B1384289 : Blo 271824 1384289 := bstep (se 2 (by rfl) ⟨519108, by rfl⟩ : syracuseStep 1384289 = 1038217) B1038217
theorem B1319111 : Blo 271824 1319111 := bstep (se 1 (by rfl) ⟨989333, by rfl⟩ : syracuseStep 1319111 = 1978667) B1978667
theorem B1746305 : Blo 271824 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B271963 : Blo 271824 271963 := bstep (se 1 (by rfl) ⟨203972, by rfl⟩ : syracuseStep 271963 = 407945) B407945
theorem B272079 : Blo 271824 272079 := bstep (se 1 (by rfl) ⟨204059, by rfl⟩ : syracuseStep 272079 = 408119) B408119
theorem B1320761 : Blo 271824 1320761 := bstep (se 2 (by rfl) ⟨495285, by rfl⟩ : syracuseStep 1320761 = 990571) B990571
theorem B1386395 : Blo 271824 1386395 := bstep (se 1 (by rfl) ⟨1039796, by rfl⟩ : syracuseStep 1386395 = 2079593) B2079593
theorem B272295 : Blo 271824 272295 := bstep (se 1 (by rfl) ⟨204221, by rfl⟩ : syracuseStep 272295 = 408443) B408443
theorem B2369803 : Blo 271824 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B272703 : Blo 271824 272703 := bstep (se 1 (by rfl) ⟨204527, by rfl⟩ : syracuseStep 272703 = 409055) B409055
theorem B272871 : Blo 271824 272871 := bstep (se 1 (by rfl) ⟨204653, by rfl⟩ : syracuseStep 272871 = 409307) B409307
theorem B928367 : Blo 271824 928367 := bstep (se 1 (by rfl) ⟨696275, by rfl⟩ : syracuseStep 928367 = 1392551) B1392551
theorem B273051 : Blo 271824 273051 := bstep (se 1 (by rfl) ⟨204788, by rfl⟩ : syracuseStep 273051 = 409577) B409577
theorem B273179 : Blo 271824 273179 := bstep (se 1 (by rfl) ⟨204884, by rfl⟩ : syracuseStep 273179 = 409769) B409769
theorem B3943367 : Blo 271824 3943367 := bstep (se 1 (by rfl) ⟨2957525, by rfl⟩ : syracuseStep 3943367 = 5915051) B5915051
theorem B928745 : Blo 271824 928745 := bstep (se 2 (by rfl) ⟨348279, by rfl⟩ : syracuseStep 928745 = 696559) B696559
theorem B273391 : Blo 271824 273391 := bstep (se 1 (by rfl) ⟨205043, by rfl⟩ : syracuseStep 273391 = 410087) B410087
theorem B273575 : Blo 271824 273575 := bstep (se 1 (by rfl) ⟨205181, by rfl⟩ : syracuseStep 273575 = 410363) B410363
theorem B273871 : Blo 271824 273871 := bstep (se 1 (by rfl) ⟨205403, by rfl⟩ : syracuseStep 273871 = 410807) B410807
theorem B273967 : Blo 271824 273967 := bstep (se 1 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 273967 = 410951) B410951
theorem B274031 : Blo 271824 274031 := bstep (se 1 (by rfl) ⟨205523, by rfl⟩ : syracuseStep 274031 = 411047) B411047
theorem B274151 : Blo 271824 274151 := bstep (se 1 (by rfl) ⟨205613, by rfl⟩ : syracuseStep 274151 = 411227) B411227
theorem B4730687 : Blo 271824 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B274463 : Blo 271824 274463 := bstep (se 1 (by rfl) ⟨205847, by rfl⟩ : syracuseStep 274463 = 411695) B411695
theorem B438319 : Blo 271824 438319 := bstep (se 1 (by rfl) ⟨328739, by rfl⟩ : syracuseStep 438319 = 657479) B657479
theorem B4468931 : Blo 271824 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B274639 : Blo 271824 274639 := bstep (se 1 (by rfl) ⟨205979, by rfl⟩ : syracuseStep 274639 = 411959) B411959
theorem B274759 : Blo 271824 274759 := bstep (se 1 (by rfl) ⟨206069, by rfl⟩ : syracuseStep 274759 = 412139) B412139
theorem B4731301 : Blo 271824 4731301 := bstep (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) B887119
theorem B274919 : Blo 271824 274919 := bstep (se 1 (by rfl) ⟨206189, by rfl⟩ : syracuseStep 274919 = 412379) B412379
theorem B274943 : Blo 271824 274943 := bstep (se 1 (by rfl) ⟨206207, by rfl⟩ : syracuseStep 274943 = 412415) B412415
theorem B1880759 : Blo 271824 1880759 := bstep (se 1 (by rfl) ⟨1410569, by rfl⟩ : syracuseStep 1880759 = 2821139) B2821139
theorem B275423 : Blo 271824 275423 := bstep (se 1 (by rfl) ⟨206567, by rfl⟩ : syracuseStep 275423 = 413135) B413135
theorem B275483 : Blo 271824 275483 := bstep (se 1 (by rfl) ⟨206612, by rfl⟩ : syracuseStep 275483 = 413225) B413225
theorem B275679 : Blo 271824 275679 := bstep (se 1 (by rfl) ⟨206759, by rfl⟩ : syracuseStep 275679 = 413519) B413519
theorem B275759 : Blo 271824 275759 := bstep (se 1 (by rfl) ⟨206819, by rfl⟩ : syracuseStep 275759 = 413639) B413639
theorem B275815 : Blo 271824 275815 := bstep (se 1 (by rfl) ⟨206861, by rfl⟩ : syracuseStep 275815 = 413723) B413723
theorem B1979873 : Blo 271824 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B2078621 : Blo 271824 2078621 := bstep (se 3 (by rfl) ⟨389741, by rfl⟩ : syracuseStep 2078621 = 779483) B779483
theorem B1161503 : Blo 271824 1161503 := bstep (se 1 (by rfl) ⟨871127, by rfl⟩ : syracuseStep 1161503 = 1742255) B1742255
theorem B5028155 : Blo 271824 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B309631 : Blo 271824 309631 := bstep (se 1 (by rfl) ⟨232223, by rfl⟩ : syracuseStep 309631 = 464447) B464447
theorem B408041 : Blo 271824 408041 := bstep (se 2 (by rfl) ⟨153015, by rfl⟩ : syracuseStep 408041 = 306031) B306031
theorem B834239 : Blo 271824 834239 := bstep (se 1 (by rfl) ⟨625679, by rfl⟩ : syracuseStep 834239 = 1251359) B1251359
theorem B408359 : Blo 271824 408359 := bstep (se 1 (by rfl) ⟨306269, by rfl⟩ : syracuseStep 408359 = 612539) B612539
theorem B408815 : Blo 271824 408815 := bstep (se 1 (by rfl) ⟨306611, by rfl⟩ : syracuseStep 408815 = 613223) B613223
theorem B408887 : Blo 271824 408887 := bstep (se 1 (by rfl) ⟨306665, by rfl⟩ : syracuseStep 408887 = 613331) B613331
theorem B408959 : Blo 271824 408959 := bstep (se 1 (by rfl) ⟨306719, by rfl⟩ : syracuseStep 408959 = 613439) B613439
theorem B409067 : Blo 271824 409067 := bstep (se 1 (by rfl) ⟨306800, by rfl⟩ : syracuseStep 409067 = 613601) B613601
theorem B409727 : Blo 271824 409727 := bstep (se 1 (by rfl) ⟨307295, by rfl⟩ : syracuseStep 409727 = 614591) B614591
theorem B410279 : Blo 271824 410279 := bstep (se 1 (by rfl) ⟨307709, by rfl⟩ : syracuseStep 410279 = 615419) B615419
theorem B410351 : Blo 271824 410351 := bstep (se 1 (by rfl) ⟨307763, by rfl⟩ : syracuseStep 410351 = 615527) B615527
theorem B410399 : Blo 271824 410399 := bstep (se 1 (by rfl) ⟨307799, by rfl⟩ : syracuseStep 410399 = 615599) B615599
theorem B1033343 : Blo 271824 1033343 := bstep (se 1 (by rfl) ⟨775007, by rfl⟩ : syracuseStep 1033343 = 1550015) B1550015
theorem B411305 : Blo 271824 411305 := bstep (se 2 (by rfl) ⟨154239, by rfl⟩ : syracuseStep 411305 = 308479) B308479
theorem B411515 : Blo 271824 411515 := bstep (se 1 (by rfl) ⟨308636, by rfl⟩ : syracuseStep 411515 = 617273) B617273
theorem B2213993 : Blo 271824 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B12830875 : Blo 271824 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B2672891 : Blo 271824 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B411935 : Blo 271824 411935 := bstep (se 1 (by rfl) ⟨308951, by rfl⟩ : syracuseStep 411935 = 617903) B617903
theorem B3164507 : Blo 271824 3164507 := bstep (se 1 (by rfl) ⟨2373380, by rfl⟩ : syracuseStep 3164507 = 4746761) B4746761
theorem B1034633 : Blo 271824 1034633 := bstep (se 2 (by rfl) ⟨387987, by rfl⟩ : syracuseStep 1034633 = 775975) B775975
theorem B412103 : Blo 271824 412103 := bstep (se 1 (by rfl) ⟨309077, by rfl⟩ : syracuseStep 412103 = 618155) B618155
theorem B3328735 : Blo 271824 3328735 := bstep (se 1 (by rfl) ⟨2496551, by rfl⟩ : syracuseStep 3328735 = 4993103) B4993103
theorem B412463 : Blo 271824 412463 := bstep (se 1 (by rfl) ⟨309347, by rfl⟩ : syracuseStep 412463 = 618695) B618695
theorem B412583 : Blo 271824 412583 := bstep (se 1 (by rfl) ⟨309437, by rfl⟩ : syracuseStep 412583 = 618875) B618875
theorem B412763 : Blo 271824 412763 := bstep (se 1 (by rfl) ⟨309572, by rfl⟩ : syracuseStep 412763 = 619145) B619145
theorem B5098729 : Blo 271824 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B412907 : Blo 271824 412907 := bstep (se 1 (by rfl) ⟨309680, by rfl⟩ : syracuseStep 412907 = 619361) B619361
theorem B1166663 : Blo 271824 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B413255 : Blo 271824 413255 := bstep (se 1 (by rfl) ⟨309941, by rfl⟩ : syracuseStep 413255 = 619883) B619883
theorem B413423 : Blo 271824 413423 := bstep (se 1 (by rfl) ⟨310067, by rfl⟩ : syracuseStep 413423 = 620135) B620135
theorem B413435 : Blo 271824 413435 := bstep (se 1 (by rfl) ⟨310076, by rfl⟩ : syracuseStep 413435 = 620153) B620153
theorem B413609 : Blo 271824 413609 := bstep (se 2 (by rfl) ⟨155103, by rfl⟩ : syracuseStep 413609 = 310207) B310207
theorem B413675 : Blo 271824 413675 := bstep (se 1 (by rfl) ⟨310256, by rfl⟩ : syracuseStep 413675 = 620513) B620513
theorem B4706423 : Blo 271824 4706423 := bstep (se 1 (by rfl) ⟨3529817, by rfl⟩ : syracuseStep 4706423 = 7059635) B7059635
theorem B2675069 : Blo 271824 2675069 := bstep (se 3 (by rfl) ⟨501575, by rfl⟩ : syracuseStep 2675069 = 1003151) B1003151
theorem B1167979 : Blo 271824 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B1528633 : Blo 271824 1528633 := bstep (se 2 (by rfl) ⟨573237, by rfl⟩ : syracuseStep 1528633 = 1146475) B1146475
theorem B5886857 : Blo 271824 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B808555 : Blo 271824 808555 := bstep (se 1 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 808555 = 1212833) B1212833
theorem B1759067 : Blo 271824 1759067 := bstep (se 1 (by rfl) ⟨1319300, by rfl⟩ : syracuseStep 1759067 = 2638601) B2638601
theorem B612647 : Blo 271824 612647 := bstep (se 1 (by rfl) ⟨459485, by rfl⟩ : syracuseStep 612647 = 918971) B918971
theorem B874921 : Blo 271824 874921 := bstep (se 2 (by rfl) ⟨328095, by rfl⟩ : syracuseStep 874921 = 656191) B656191
theorem B613007 : Blo 271824 613007 := bstep (se 1 (by rfl) ⟨459755, by rfl⟩ : syracuseStep 613007 = 919511) B919511
theorem B1039007 : Blo 271824 1039007 := bstep (se 1 (by rfl) ⟨779255, by rfl⟩ : syracuseStep 1039007 = 1558511) B1558511
theorem B744161 : Blo 271824 744161 := bstep (se 2 (by rfl) ⟨279060, by rfl⟩ : syracuseStep 744161 = 558121) B558121
theorem B777023 : Blo 271824 777023 := bstep (se 1 (by rfl) ⟨582767, by rfl⟩ : syracuseStep 777023 = 1165535) B1165535
theorem B351391 : Blo 271824 351391 := bstep (se 1 (by rfl) ⟨263543, by rfl⟩ : syracuseStep 351391 = 527087) B527087
theorem B613907 : Blo 271824 613907 := bstep (se 1 (by rfl) ⟨460430, by rfl⟩ : syracuseStep 613907 = 920861) B920861
theorem B2514685 : Blo 271824 2514685 := bstep (se 3 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 2514685 = 943007) B943007
theorem B614375 : Blo 271824 614375 := bstep (se 1 (by rfl) ⟨460781, by rfl⟩ : syracuseStep 614375 = 921563) B921563
theorem B614735 : Blo 271824 614735 := bstep (se 1 (by rfl) ⟨461051, by rfl⟩ : syracuseStep 614735 = 922103) B922103
theorem B2122247 : Blo 271824 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B1040951 : Blo 271824 1040951 := bstep (se 1 (by rfl) ⟨780713, by rfl⟩ : syracuseStep 1040951 = 1561427) B1561427
theorem B6808465 : Blo 271824 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B615401 : Blo 271824 615401 := bstep (se 2 (by rfl) ⟨230775, by rfl⟩ : syracuseStep 615401 = 461551) B461551
theorem B517279 : Blo 271824 517279 := bstep (se 1 (by rfl) ⟨387959, by rfl⟩ : syracuseStep 517279 = 775919) B775919
theorem B615905 : Blo 271824 615905 := bstep (se 2 (by rfl) ⟨230964, by rfl⟩ : syracuseStep 615905 = 461929) B461929
theorem B2090771 : Blo 271824 2090771 := bstep (se 1 (by rfl) ⟨1568078, by rfl⟩ : syracuseStep 2090771 = 3136157) B3136157
theorem B878651 : Blo 271824 878651 := bstep (se 1 (by rfl) ⟨658988, by rfl⟩ : syracuseStep 878651 = 1317977) B1317977
theorem B1566803 : Blo 271824 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B3532895 : Blo 271824 3532895 := bstep (se 1 (by rfl) ⟨2649671, by rfl⟩ : syracuseStep 3532895 = 5299343) B5299343
theorem B551099 : Blo 271824 551099 := bstep (se 1 (by rfl) ⟨413324, by rfl⟩ : syracuseStep 551099 = 826649) B826649
theorem B518395 : Blo 271824 518395 := bstep (se 1 (by rfl) ⟨388796, by rfl⟩ : syracuseStep 518395 = 777593) B777593
theorem B879265 : Blo 271824 879265 := bstep (se 2 (by rfl) ⟨329724, by rfl⟩ : syracuseStep 879265 = 659449) B659449
theorem B387823 : Blo 271824 387823 := bstep (se 1 (by rfl) ⟨290867, by rfl⟩ : syracuseStep 387823 = 581735) B581735
theorem B7007147 : Blo 271824 7007147 := bstep (se 1 (by rfl) ⟨5255360, by rfl⟩ : syracuseStep 7007147 = 10510721) B10510721
theorem B3959927 : Blo 271824 3959927 := bstep (se 1 (by rfl) ⟨2969945, by rfl⟩ : syracuseStep 3959927 = 5939891) B5939891
theorem B2354305 : Blo 271824 2354305 := bstep (se 2 (by rfl) ⟨882864, by rfl⟩ : syracuseStep 2354305 = 1765729) B1765729
theorem B1764499 : Blo 271824 1764499 := bstep (se 1 (by rfl) ⟨1323374, by rfl⟩ : syracuseStep 1764499 = 2646749) B2646749
theorem B1043867 : Blo 271824 1043867 := bstep (se 1 (by rfl) ⟨782900, by rfl⟩ : syracuseStep 1043867 = 1565801) B1565801
theorem B9990125 : Blo 271824 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B782399 : Blo 271824 782399 := bstep (se 1 (by rfl) ⟨586799, by rfl⟩ : syracuseStep 782399 = 1173599) B1173599
theorem B520415 : Blo 271824 520415 := bstep (se 1 (by rfl) ⟨390311, by rfl⟩ : syracuseStep 520415 = 780623) B780623
theorem B782855 : Blo 271824 782855 := bstep (se 1 (by rfl) ⟨587141, by rfl⟩ : syracuseStep 782855 = 1174283) B1174283
theorem B619055 : Blo 271824 619055 := bstep (se 1 (by rfl) ⟨464291, by rfl⟩ : syracuseStep 619055 = 928583) B928583
theorem B1340011 : Blo 271824 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B1471151 : Blo 271824 1471151 := bstep (se 1 (by rfl) ⟨1103363, by rfl⟩ : syracuseStep 1471151 = 2206727) B2206727
theorem B521311 : Blo 271824 521311 := bstep (se 1 (by rfl) ⟨390983, by rfl⟩ : syracuseStep 521311 = 781967) B781967
theorem B2946455 : Blo 271824 2946455 := bstep (se 1 (by rfl) ⟨2209841, by rfl⟩ : syracuseStep 2946455 = 4419683) B4419683
theorem B620009 : Blo 271824 620009 := bstep (se 2 (by rfl) ⟨232503, by rfl⟩ : syracuseStep 620009 = 465007) B465007
theorem B522139 : Blo 271824 522139 := bstep (se 1 (by rfl) ⟨391604, by rfl⟩ : syracuseStep 522139 = 783209) B783209
theorem B784495 : Blo 271824 784495 := bstep (se 1 (by rfl) ⟨588371, by rfl⟩ : syracuseStep 784495 = 1176743) B1176743
theorem B1669355 : Blo 271824 1669355 := bstep (se 1 (by rfl) ⟨1252016, by rfl⟩ : syracuseStep 1669355 = 2504033) B2504033
theorem B4684553 : Blo 271824 4684553 := bstep (se 2 (by rfl) ⟨1756707, by rfl⟩ : syracuseStep 4684553 = 3513415) B3513415
theorem B1244335 : Blo 271824 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B982529 : Blo 271824 982529 := bstep (se 2 (by rfl) ⟨368448, by rfl⟩ : syracuseStep 982529 = 736897) B736897
theorem B3112829 : Blo 271824 3112829 := bstep (se 3 (by rfl) ⟨583655, by rfl⟩ : syracuseStep 3112829 = 1167311) B1167311
theorem B458743 : Blo 271824 458743 := bstep (se 1 (by rfl) ⟨344057, by rfl⟩ : syracuseStep 458743 = 688115) B688115
theorem B2490425 : Blo 271824 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B524647 : Blo 271824 524647 := bstep (se 1 (by rfl) ⟨393485, by rfl⟩ : syracuseStep 524647 = 786971) B786971
theorem B688895 : Blo 271824 688895 := bstep (se 1 (by rfl) ⟨516671, by rfl⟩ : syracuseStep 688895 = 1033343) B1033343
theorem B9077953 : Blo 271824 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B656711 : Blo 271824 656711 := bstep (se 1 (by rfl) ⟨492533, by rfl⟩ : syracuseStep 656711 = 985067) B985067
theorem B918863 : Blo 271824 918863 := bstep (se 1 (by rfl) ⟨689147, by rfl⟩ : syracuseStep 918863 = 1378295) B1378295
theorem B1475995 : Blo 271824 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B460255 : Blo 271824 460255 := bstep (se 1 (by rfl) ⟨345191, by rfl⟩ : syracuseStep 460255 = 690383) B690383
theorem B689705 : Blo 271824 689705 := bstep (se 2 (by rfl) ⟨258639, by rfl⟩ : syracuseStep 689705 = 517279) B517279
theorem B689755 : Blo 271824 689755 := bstep (se 1 (by rfl) ⟨517316, by rfl⟩ : syracuseStep 689755 = 1034633) B1034633
theorem B25233605 : Blo 271824 25233605 := bstep (se 4 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 25233605 = 4731301) B4731301
theorem B461119 : Blo 271824 461119 := bstep (se 1 (by rfl) ⟨345839, by rfl⟩ : syracuseStep 461119 = 691679) B691679
theorem B5245519 : Blo 271824 5245519 := bstep (se 1 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 5245519 = 7868279) B7868279
theorem B691193 : Blo 271824 691193 := bstep (se 2 (by rfl) ⟨259197, by rfl⟩ : syracuseStep 691193 = 518395) B518395
theorem B2493665 : Blo 271824 2493665 := bstep (se 2 (by rfl) ⟨935124, by rfl⟩ : syracuseStep 2493665 = 1870249) B1870249
theorem B692671 : Blo 271824 692671 := bstep (se 1 (by rfl) ⟨519503, by rfl⟩ : syracuseStep 692671 = 1039007) B1039007
theorem B922859 : Blo 271824 922859 := bstep (se 1 (by rfl) ⟨692144, by rfl⟩ : syracuseStep 922859 = 1384289) B1384289
theorem B1414831 : Blo 271824 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B693967 : Blo 271824 693967 := bstep (se 1 (by rfl) ⟨520475, by rfl⟩ : syracuseStep 693967 = 1040951) B1040951
theorem B924263 : Blo 271824 924263 := bstep (se 1 (by rfl) ⟨693197, by rfl⟩ : syracuseStep 924263 = 1386395) B1386395
theorem B367399 : Blo 271824 367399 := bstep (se 1 (by rfl) ⟨275549, by rfl⟩ : syracuseStep 367399 = 551099) B551099
theorem B695081 : Blo 271824 695081 := bstep (se 2 (by rfl) ⟨260655, by rfl⟩ : syracuseStep 695081 = 521311) B521311
theorem B2628911 : Blo 271824 2628911 := bstep (se 1 (by rfl) ⟨1971683, by rfl⟩ : syracuseStep 2628911 = 3943367) B3943367
theorem B695911 : Blo 271824 695911 := bstep (se 1 (by rfl) ⟨521933, by rfl⟩ : syracuseStep 695911 = 1043867) B1043867
theorem B696185 : Blo 271824 696185 := bstep (se 2 (by rfl) ⟨261069, by rfl⟩ : syracuseStep 696185 = 522139) B522139
theorem B3153791 : Blo 271824 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B6660083 : Blo 271824 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B1253839 : Blo 271824 1253839 := bstep (se 1 (by rfl) ⟨940379, by rfl⟩ : syracuseStep 1253839 = 1880759) B1880759
theorem B795433 : Blo 271824 795433 := bstep (se 2 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 795433 = 596575) B596575
theorem B1319915 : Blo 271824 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B1385747 : Blo 271824 1385747 := bstep (se 1 (by rfl) ⟨1039310, by rfl⟩ : syracuseStep 1385747 = 2078621) B2078621
theorem B3352103 : Blo 271824 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B468521 : Blo 271824 468521 := bstep (se 2 (by rfl) ⟨175695, by rfl⟩ : syracuseStep 468521 = 351391) B351391
theorem B665225 : Blo 271824 665225 := bstep (se 2 (by rfl) ⟨249459, by rfl⟩ : syracuseStep 665225 = 498919) B498919
theorem B272027 : Blo 271824 272027 := bstep (se 1 (by rfl) ⟨204020, by rfl⟩ : syracuseStep 272027 = 408041) B408041
theorem B3123035 : Blo 271824 3123035 := bstep (se 1 (by rfl) ⟨2342276, by rfl⟩ : syracuseStep 3123035 = 4684553) B4684553
theorem B272239 : Blo 271824 272239 := bstep (se 1 (by rfl) ⟨204179, by rfl⟩ : syracuseStep 272239 = 408359) B408359
theorem B272543 : Blo 271824 272543 := bstep (se 1 (by rfl) ⟨204407, by rfl⟩ : syracuseStep 272543 = 408815) B408815
theorem B272591 : Blo 271824 272591 := bstep (se 1 (by rfl) ⟨204443, by rfl⟩ : syracuseStep 272591 = 408887) B408887
theorem B272639 : Blo 271824 272639 := bstep (se 1 (by rfl) ⟨204479, by rfl⟩ : syracuseStep 272639 = 408959) B408959
theorem B272711 : Blo 271824 272711 := bstep (se 1 (by rfl) ⟨204533, by rfl⟩ : syracuseStep 272711 = 409067) B409067
theorem B3352913 : Blo 271824 3352913 := bstep (se 2 (by rfl) ⟨1257342, by rfl⟩ : syracuseStep 3352913 = 2514685) B2514685
theorem B928097 : Blo 271824 928097 := bstep (se 2 (by rfl) ⟨348036, by rfl⟩ : syracuseStep 928097 = 696073) B696073
theorem B2075219 : Blo 271824 2075219 := bstep (se 1 (by rfl) ⟨1556414, by rfl⟩ : syracuseStep 2075219 = 3112829) B3112829
theorem B273151 : Blo 271824 273151 := bstep (se 1 (by rfl) ⟨204863, by rfl⟩ : syracuseStep 273151 = 409727) B409727
theorem B7908191 : Blo 271824 7908191 := bstep (se 1 (by rfl) ⟨5931143, by rfl⟩ : syracuseStep 7908191 = 11862287) B11862287
theorem B273519 : Blo 271824 273519 := bstep (se 1 (by rfl) ⟨205139, by rfl⟩ : syracuseStep 273519 = 410279) B410279
theorem B18918521 : Blo 271824 18918521 := bstep (se 2 (by rfl) ⟨7094445, by rfl⟩ : syracuseStep 18918521 = 14188891) B14188891
theorem B273567 : Blo 271824 273567 := bstep (se 1 (by rfl) ⟨205175, by rfl⟩ : syracuseStep 273567 = 410351) B410351
theorem B273599 : Blo 271824 273599 := bstep (se 1 (by rfl) ⟨205199, by rfl⟩ : syracuseStep 273599 = 410399) B410399
theorem B68431333 : Blo 271824 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B274203 : Blo 271824 274203 := bstep (se 1 (by rfl) ⟨205652, by rfl⟩ : syracuseStep 274203 = 411305) B411305
theorem B438095 : Blo 271824 438095 := bstep (se 1 (by rfl) ⟨328571, by rfl⟩ : syracuseStep 438095 = 657143) B657143
theorem B274343 : Blo 271824 274343 := bstep (se 1 (by rfl) ⟨205757, by rfl⟩ : syracuseStep 274343 = 411515) B411515
theorem B1781927 : Blo 271824 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B274623 : Blo 271824 274623 := bstep (se 1 (by rfl) ⟨205967, by rfl⟩ : syracuseStep 274623 = 411935) B411935
theorem B2109671 : Blo 271824 2109671 := bstep (se 1 (by rfl) ⟨1582253, by rfl⟩ : syracuseStep 2109671 = 3164507) B3164507
theorem B274735 : Blo 271824 274735 := bstep (se 1 (by rfl) ⟨206051, by rfl⟩ : syracuseStep 274735 = 412103) B412103
theorem B274975 : Blo 271824 274975 := bstep (se 1 (by rfl) ⟨206231, by rfl⟩ : syracuseStep 274975 = 412463) B412463
theorem B307759 : Blo 271824 307759 := bstep (se 1 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 307759 = 461639) B461639
theorem B275055 : Blo 271824 275055 := bstep (se 1 (by rfl) ⟨206291, by rfl⟩ : syracuseStep 275055 = 412583) B412583
theorem B307903 : Blo 271824 307903 := bstep (se 1 (by rfl) ⟨230927, by rfl⟩ : syracuseStep 307903 = 461855) B461855
theorem B275175 : Blo 271824 275175 := bstep (se 1 (by rfl) ⟨206381, by rfl⟩ : syracuseStep 275175 = 412763) B412763
theorem B275271 : Blo 271824 275271 := bstep (se 1 (by rfl) ⟨206453, by rfl⟩ : syracuseStep 275271 = 412907) B412907
theorem B308191 : Blo 271824 308191 := bstep (se 1 (by rfl) ⟨231143, by rfl⟩ : syracuseStep 308191 = 462287) B462287
theorem B275503 : Blo 271824 275503 := bstep (se 1 (by rfl) ⟨206627, by rfl⟩ : syracuseStep 275503 = 413255) B413255
theorem B275615 : Blo 271824 275615 := bstep (se 1 (by rfl) ⟨206711, by rfl⟩ : syracuseStep 275615 = 413423) B413423
theorem B275623 : Blo 271824 275623 := bstep (se 1 (by rfl) ⟨206717, by rfl⟩ : syracuseStep 275623 = 413435) B413435
theorem B275739 : Blo 271824 275739 := bstep (se 1 (by rfl) ⟨206804, by rfl⟩ : syracuseStep 275739 = 413609) B413609
theorem B275783 : Blo 271824 275783 := bstep (se 1 (by rfl) ⟨206837, by rfl⟩ : syracuseStep 275783 = 413675) B413675
theorem B1783379 : Blo 271824 1783379 := bstep (se 1 (by rfl) ⟨1337534, by rfl⟩ : syracuseStep 1783379 = 2675069) B2675069
theorem B308839 : Blo 271824 308839 := bstep (se 1 (by rfl) ⟨231629, by rfl⟩ : syracuseStep 308839 = 463259) B463259
theorem B3159737 : Blo 271824 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B4438313 : Blo 271824 4438313 := bstep (se 2 (by rfl) ⟨1664367, by rfl⟩ : syracuseStep 4438313 = 3328735) B3328735
theorem B408431 : Blo 271824 408431 := bstep (se 1 (by rfl) ⟨306323, by rfl⟩ : syracuseStep 408431 = 612647) B612647
theorem B6798305 : Blo 271824 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B408671 : Blo 271824 408671 := bstep (se 1 (by rfl) ⟨306503, by rfl⟩ : syracuseStep 408671 = 613007) B613007
theorem B13352455 : Blo 271824 13352455 := bstep (se 1 (by rfl) ⟨10014341, by rfl⟩ : syracuseStep 13352455 = 20028683) B20028683
theorem B409271 : Blo 271824 409271 := bstep (se 1 (by rfl) ⟨306953, by rfl⟩ : syracuseStep 409271 = 613907) B613907
theorem B409583 : Blo 271824 409583 := bstep (se 1 (by rfl) ⟨307187, by rfl⟩ : syracuseStep 409583 = 614375) B614375
theorem B409823 : Blo 271824 409823 := bstep (se 1 (by rfl) ⟨307367, by rfl⟩ : syracuseStep 409823 = 614735) B614735
theorem B3228149 : Blo 271824 3228149 := bstep (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) B302639
theorem B410267 : Blo 271824 410267 := bstep (se 1 (by rfl) ⟨307700, by rfl⟩ : syracuseStep 410267 = 615401) B615401
theorem B1557305 : Blo 271824 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B1786681 : Blo 271824 1786681 := bstep (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) B1340011
theorem B1164203 : Blo 271824 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B410603 : Blo 271824 410603 := bstep (se 1 (by rfl) ⟨307952, by rfl⟩ : syracuseStep 410603 = 615905) B615905
theorem B1393847 : Blo 271824 1393847 := bstep (se 1 (by rfl) ⟨1045385, by rfl⟩ : syracuseStep 1393847 = 2090771) B2090771
theorem B1984429 : Blo 271824 1984429 := bstep (se 3 (by rfl) ⟨372080, by rfl⟩ : syracuseStep 1984429 = 744161) B744161
theorem B4671431 : Blo 271824 4671431 := bstep (se 1 (by rfl) ⟨3503573, by rfl⟩ : syracuseStep 4671431 = 7007147) B7007147
theorem B2639951 : Blo 271824 2639951 := bstep (se 1 (by rfl) ⟨1979963, by rfl⟩ : syracuseStep 2639951 = 3959927) B3959927
theorem B346943 : Blo 271824 346943 := bstep (se 1 (by rfl) ⟨260207, by rfl⟩ : syracuseStep 346943 = 520415) B520415
theorem B412703 : Blo 271824 412703 := bstep (se 1 (by rfl) ⟨309527, by rfl⟩ : syracuseStep 412703 = 619055) B619055
theorem B412841 : Blo 271824 412841 := bstep (se 2 (by rfl) ⟨154815, by rfl⟩ : syracuseStep 412841 = 309631) B309631
theorem B1166561 : Blo 271824 1166561 := bstep (se 2 (by rfl) ⟨437460, by rfl⟩ : syracuseStep 1166561 = 874921) B874921
theorem B413339 : Blo 271824 413339 := bstep (se 1 (by rfl) ⟨310004, by rfl⟩ : syracuseStep 413339 = 620009) B620009
theorem B774335 : Blo 271824 774335 := bstep (se 1 (by rfl) ⟨580751, by rfl⟩ : syracuseStep 774335 = 1161503) B1161503
theorem B1659113 : Blo 271824 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B611657 : Blo 271824 611657 := bstep (se 2 (by rfl) ⟨229371, by rfl⟩ : syracuseStep 611657 = 458743) B458743
theorem B2086397 : Blo 271824 2086397 := bstep (se 3 (by rfl) ⟨391199, by rfl⟩ : syracuseStep 2086397 = 782399) B782399
theorem B613025 : Blo 271824 613025 := bstep (se 2 (by rfl) ⟨229884, by rfl⟩ : syracuseStep 613025 = 459769) B459769
theorem B613097 : Blo 271824 613097 := bstep (se 2 (by rfl) ⟨229911, by rfl⟩ : syracuseStep 613097 = 459823) B459823
theorem B613871 : Blo 271824 613871 := bstep (se 1 (by rfl) ⟨460403, by rfl⟩ : syracuseStep 613871 = 920807) B920807
theorem B777775 : Blo 271824 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B3137615 : Blo 271824 3137615 := bstep (se 1 (by rfl) ⟨2353211, by rfl⟩ : syracuseStep 3137615 = 4706423) B4706423
theorem B5267663 : Blo 271824 5267663 := bstep (se 1 (by rfl) ⟨3950747, by rfl⟩ : syracuseStep 5267663 = 7901495) B7901495
theorem B3924571 : Blo 271824 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B1172353 : Blo 271824 1172353 := bstep (se 2 (by rfl) ⟨439632, by rfl⟩ : syracuseStep 1172353 = 879265) B879265
theorem B517097 : Blo 271824 517097 := bstep (se 2 (by rfl) ⟨193911, by rfl⟩ : syracuseStep 517097 = 387823) B387823
theorem B615635 : Blo 271824 615635 := bstep (se 1 (by rfl) ⟨461726, by rfl⟩ : syracuseStep 615635 = 923453) B923453
theorem B1172711 : Blo 271824 1172711 := bstep (se 1 (by rfl) ⟨879533, by rfl⟩ : syracuseStep 1172711 = 1759067) B1759067
theorem B3139073 : Blo 271824 3139073 := bstep (se 2 (by rfl) ⟨1177152, by rfl⟩ : syracuseStep 3139073 = 2354305) B2354305
theorem B2352665 : Blo 271824 2352665 := bstep (se 2 (by rfl) ⟨882249, by rfl⟩ : syracuseStep 2352665 = 1764499) B1764499
theorem B8152709 : Blo 271824 8152709 := bstep (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) B1528633
theorem B518015 : Blo 271824 518015 := bstep (se 1 (by rfl) ⟨388511, by rfl⟩ : syracuseStep 518015 = 777023) B777023
theorem B616319 : Blo 271824 616319 := bstep (se 1 (by rfl) ⟨462239, by rfl⟩ : syracuseStep 616319 = 924479) B924479
theorem B584425 : Blo 271824 584425 := bstep (se 2 (by rfl) ⟨219159, by rfl⟩ : syracuseStep 584425 = 438319) B438319
theorem B879407 : Blo 271824 879407 := bstep (se 1 (by rfl) ⟨659555, by rfl⟩ : syracuseStep 879407 = 1319111) B1319111
theorem B880507 : Blo 271824 880507 := bstep (se 1 (by rfl) ⟨660380, by rfl⟩ : syracuseStep 880507 = 1320761) B1320761
theorem B585767 : Blo 271824 585767 := bstep (se 1 (by rfl) ⟨439325, by rfl⟩ : syracuseStep 585767 = 878651) B878651
theorem B1044535 : Blo 271824 1044535 := bstep (se 1 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 1044535 = 1566803) B1566803
theorem B2355263 : Blo 271824 2355263 := bstep (se 1 (by rfl) ⟨1766447, by rfl⟩ : syracuseStep 2355263 = 3532895) B3532895
theorem B618911 : Blo 271824 618911 := bstep (se 1 (by rfl) ⟨464183, by rfl⟩ : syracuseStep 618911 = 928367) B928367
theorem B619163 : Blo 271824 619163 := bstep (se 1 (by rfl) ⟨464372, by rfl⟩ : syracuseStep 619163 = 928745) B928745
theorem B1078073 : Blo 271824 1078073 := bstep (se 2 (by rfl) ⟨404277, by rfl⟩ : syracuseStep 1078073 = 808555) B808555
theorem B2979287 : Blo 271824 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B1045993 : Blo 271824 1045993 := bstep (se 2 (by rfl) ⟨392247, by rfl⟩ : syracuseStep 1045993 = 784495) B784495
theorem B2323961 : Blo 271824 2323961 := bstep (se 2 (by rfl) ⟨871485, by rfl⟩ : syracuseStep 2323961 = 1742971) B1742971
theorem B521903 : Blo 271824 521903 := bstep (se 1 (by rfl) ⟨391427, by rfl⟩ : syracuseStep 521903 = 782855) B782855
theorem B980767 : Blo 271824 980767 := bstep (se 1 (by rfl) ⟨735575, by rfl⟩ : syracuseStep 980767 = 1471151) B1471151
theorem B1964303 : Blo 271824 1964303 := bstep (se 1 (by rfl) ⟨1473227, by rfl⟩ : syracuseStep 1964303 = 2946455) B2946455
theorem B1112903 : Blo 271824 1112903 := bstep (se 1 (by rfl) ⟨834677, by rfl⟩ : syracuseStep 1112903 = 1669355) B1669355
theorem B556159 : Blo 271824 556159 := bstep (se 1 (by rfl) ⟨417119, by rfl⟩ : syracuseStep 556159 = 834239) B834239
theorem B655019 : Blo 271824 655019 := bstep (se 1 (by rfl) ⟨491264, by rfl⟩ : syracuseStep 655019 = 982529) B982529
theorem B459263 : Blo 271824 459263 := bstep (se 1 (by rfl) ⟨344447, by rfl⟩ : syracuseStep 459263 = 688895) B688895
theorem B1671785 : Blo 271824 1671785 := bstep (se 2 (by rfl) ⟨626919, by rfl⟩ : syracuseStep 1671785 = 1253839) B1253839
theorem B459803 : Blo 271824 459803 := bstep (se 1 (by rfl) ⟨344852, by rfl⟩ : syracuseStep 459803 = 689705) B689705
theorem B3114287 : Blo 271824 3114287 := bstep (se 1 (by rfl) ⟨2335715, by rfl⟩ : syracuseStep 3114287 = 4671431) B4671431
theorem B1967993 : Blo 271824 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B460795 : Blo 271824 460795 := bstep (se 1 (by rfl) ⟨345596, by rfl⟩ : syracuseStep 460795 = 691193) B691193
theorem B919673 : Blo 271824 919673 := bstep (se 2 (by rfl) ⟨344877, by rfl⟩ : syracuseStep 919673 = 689755) B689755
theorem B463387 : Blo 271824 463387 := bstep (se 1 (by rfl) ⟨347540, by rfl⟩ : syracuseStep 463387 = 695081) B695081
theorem B1381373 : Blo 271824 1381373 := bstep (se 3 (by rfl) ⟨259007, by rfl⟩ : syracuseStep 1381373 = 518015) B518015
theorem B464123 : Blo 271824 464123 := bstep (se 1 (by rfl) ⟨348092, by rfl⟩ : syracuseStep 464123 = 696185) B696185
theorem B2102527 : Blo 271824 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B3511775 : Blo 271824 3511775 := bstep (se 1 (by rfl) ⟨2633831, by rfl⟩ : syracuseStep 3511775 = 5267663) B5267663
theorem B923561 : Blo 271824 923561 := bstep (se 2 (by rfl) ⟨346335, by rfl⟩ : syracuseStep 923561 = 692671) B692671
theorem B923831 : Blo 271824 923831 := bstep (se 1 (by rfl) ⟨692873, by rfl⟩ : syracuseStep 923831 = 1385747) B1385747
theorem B2234735 : Blo 271824 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B2235275 : Blo 271824 2235275 := bstep (se 1 (by rfl) ⟨1676456, by rfl⟩ : syracuseStep 2235275 = 3352913) B3352913
theorem B1383479 : Blo 271824 1383479 := bstep (se 1 (by rfl) ⟨1037609, by rfl⟩ : syracuseStep 1383479 = 2075219) B2075219
theorem B925181 : Blo 271824 925181 := bstep (se 3 (by rfl) ⟨173471, by rfl⟩ : syracuseStep 925181 = 346943) B346943
theorem B925289 : Blo 271824 925289 := bstep (se 2 (by rfl) ⟨346983, by rfl⟩ : syracuseStep 925289 = 693967) B693967
theorem B1187951 : Blo 271824 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B1549307 : Blo 271824 1549307 := bstep (se 1 (by rfl) ⟨1161980, by rfl⟩ : syracuseStep 1549307 = 2323961) B2323961
theorem B1188919 : Blo 271824 1188919 := bstep (se 1 (by rfl) ⟨891689, by rfl⟩ : syracuseStep 1188919 = 1783379) B1783379
theorem B2106491 : Blo 271824 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B2958875 : Blo 271824 2958875 := bstep (se 1 (by rfl) ⟨2219156, by rfl⟩ : syracuseStep 2958875 = 4438313) B4438313
theorem B272287 : Blo 271824 272287 := bstep (se 1 (by rfl) ⟨204215, by rfl⟩ : syracuseStep 272287 = 408431) B408431
theorem B4532203 : Blo 271824 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B17803273 : Blo 271824 17803273 := bstep (se 2 (by rfl) ⟨6676227, by rfl⟩ : syracuseStep 17803273 = 13352455) B13352455
theorem B272447 : Blo 271824 272447 := bstep (se 1 (by rfl) ⟨204335, by rfl⟩ : syracuseStep 272447 = 408671) B408671
theorem B927881 : Blo 271824 927881 := bstep (se 2 (by rfl) ⟨347955, by rfl⟩ : syracuseStep 927881 = 695911) B695911
theorem B436679 : Blo 271824 436679 := bstep (se 1 (by rfl) ⟨327509, by rfl⟩ : syracuseStep 436679 = 655019) B655019
theorem B272847 : Blo 271824 272847 := bstep (se 1 (by rfl) ⟨204635, by rfl⟩ : syracuseStep 272847 = 409271) B409271
theorem B273055 : Blo 271824 273055 := bstep (se 1 (by rfl) ⟨204791, by rfl⟩ : syracuseStep 273055 = 409583) B409583
theorem B273215 : Blo 271824 273215 := bstep (se 1 (by rfl) ⟨204911, by rfl⟩ : syracuseStep 273215 = 409823) B409823
theorem B273511 : Blo 271824 273511 := bstep (se 1 (by rfl) ⟨205133, by rfl⟩ : syracuseStep 273511 = 410267) B410267
theorem B699529 : Blo 271824 699529 := bstep (se 2 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 699529 = 524647) B524647
theorem B273735 : Blo 271824 273735 := bstep (se 1 (by rfl) ⟨205301, by rfl⟩ : syracuseStep 273735 = 410603) B410603
theorem B929231 : Blo 271824 929231 := bstep (se 1 (by rfl) ⟨696923, by rfl⟩ : syracuseStep 929231 = 1393847) B1393847
theorem B437807 : Blo 271824 437807 := bstep (se 1 (by rfl) ⟨328355, by rfl⟩ : syracuseStep 437807 = 656711) B656711
theorem B1060577 : Blo 271824 1060577 := bstep (se 2 (by rfl) ⟨397716, by rfl⟩ : syracuseStep 1060577 = 795433) B795433
theorem B16822403 : Blo 271824 16822403 := bstep (se 1 (by rfl) ⟨12616802, by rfl⟩ : syracuseStep 16822403 = 25233605) B25233605
theorem B12103937 : Blo 271824 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B275135 : Blo 271824 275135 := bstep (se 1 (by rfl) ⟨206351, by rfl⟩ : syracuseStep 275135 = 412703) B412703
theorem B275227 : Blo 271824 275227 := bstep (se 1 (by rfl) ⟨206420, by rfl⟩ : syracuseStep 275227 = 412841) B412841
theorem B275559 : Blo 271824 275559 := bstep (se 1 (by rfl) ⟨206669, by rfl⟩ : syracuseStep 275559 = 413339) B413339
theorem B3519773 : Blo 271824 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B6994025 : Blo 271824 6994025 := bstep (se 2 (by rfl) ⟨2622759, by rfl⟩ : syracuseStep 6994025 = 5245519) B5245519
theorem B407771 : Blo 271824 407771 := bstep (se 1 (by rfl) ⟨305828, by rfl⟩ : syracuseStep 407771 = 611657) B611657
theorem B1390931 : Blo 271824 1390931 := bstep (se 1 (by rfl) ⟨1043198, by rfl⟩ : syracuseStep 1390931 = 2086397) B2086397
theorem B21740557 : Blo 271824 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B408683 : Blo 271824 408683 := bstep (se 1 (by rfl) ⟨306512, by rfl⟩ : syracuseStep 408683 = 613025) B613025
theorem B1391741 : Blo 271824 1391741 := bstep (se 3 (by rfl) ⟨260951, by rfl⟩ : syracuseStep 1391741 = 521903) B521903
theorem B408731 : Blo 271824 408731 := bstep (se 1 (by rfl) ⟨306548, by rfl⟩ : syracuseStep 408731 = 613097) B613097
theorem B91241777 : Blo 271824 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B1752607 : Blo 271824 1752607 := bstep (se 1 (by rfl) ⟨1314455, by rfl⟩ : syracuseStep 1752607 = 2628911) B2628911
theorem B409247 : Blo 271824 409247 := bstep (se 1 (by rfl) ⟨306935, by rfl⟩ : syracuseStep 409247 = 613871) B613871
theorem B4440055 : Blo 271824 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B1392713 : Blo 271824 1392713 := bstep (se 2 (by rfl) ⟨522267, by rfl⟩ : syracuseStep 1392713 = 1044535) B1044535
theorem B344731 : Blo 271824 344731 := bstep (se 1 (by rfl) ⟨258548, by rfl⟩ : syracuseStep 344731 = 517097) B517097
theorem B410345 : Blo 271824 410345 := bstep (se 2 (by rfl) ⟨153879, by rfl⟩ : syracuseStep 410345 = 307759) B307759
theorem B410423 : Blo 271824 410423 := bstep (se 1 (by rfl) ⟨307817, by rfl⟩ : syracuseStep 410423 = 615635) B615635
theorem B410537 : Blo 271824 410537 := bstep (se 2 (by rfl) ⟨153951, by rfl⟩ : syracuseStep 410537 = 307903) B307903
theorem B312347 : Blo 271824 312347 := bstep (se 1 (by rfl) ⟨234260, by rfl⟩ : syracuseStep 312347 = 468521) B468521
theorem B443483 : Blo 271824 443483 := bstep (se 1 (by rfl) ⟨332612, by rfl⟩ : syracuseStep 443483 = 665225) B665225
theorem B2082023 : Blo 271824 2082023 := bstep (se 1 (by rfl) ⟨1561517, by rfl⟩ : syracuseStep 2082023 = 3123035) B3123035
theorem B410879 : Blo 271824 410879 := bstep (se 1 (by rfl) ⟨308159, by rfl⟩ : syracuseStep 410879 = 616319) B616319
theorem B410921 : Blo 271824 410921 := bstep (se 2 (by rfl) ⟨154095, by rfl⟩ : syracuseStep 410921 = 308191) B308191
theorem B1394657 : Blo 271824 1394657 := bstep (se 2 (by rfl) ⟨522996, by rfl⟩ : syracuseStep 1394657 = 1045993) B1045993
theorem B411785 : Blo 271824 411785 := bstep (se 2 (by rfl) ⟨154419, by rfl⟩ : syracuseStep 411785 = 308839) B308839
theorem B1886441 : Blo 271824 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B412607 : Blo 271824 412607 := bstep (se 1 (by rfl) ⟨309455, by rfl⟩ : syracuseStep 412607 = 618911) B618911
theorem B412775 : Blo 271824 412775 := bstep (se 1 (by rfl) ⟨309581, by rfl⟩ : syracuseStep 412775 = 619163) B619163
theorem B1986191 : Blo 271824 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B5230757 : Blo 271824 5230757 := bstep (se 4 (by rfl) ⟨490383, by rfl⟩ : syracuseStep 5230757 = 980767) B980767
theorem B741545 : Blo 271824 741545 := bstep (se 2 (by rfl) ⟨278079, by rfl⟩ : syracuseStep 741545 = 556159) B556159
theorem B741935 : Blo 271824 741935 := bstep (se 1 (by rfl) ⟨556451, by rfl⟩ : syracuseStep 741935 = 1112903) B1112903
theorem B1037033 : Blo 271824 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B1168253 : Blo 271824 1168253 := bstep (se 3 (by rfl) ⟨219047, by rfl⟩ : syracuseStep 1168253 = 438095) B438095
theorem B1660283 : Blo 271824 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B2152099 : Blo 271824 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B1038203 : Blo 271824 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B776135 : Blo 271824 776135 := bstep (se 1 (by rfl) ⟨582101, by rfl⟩ : syracuseStep 776135 = 1164203) B1164203
theorem B5232761 : Blo 271824 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B612575 : Blo 271824 612575 := bstep (se 1 (by rfl) ⟨459431, by rfl⟩ : syracuseStep 612575 = 918863) B918863
theorem B1563137 : Blo 271824 1563137 := bstep (se 2 (by rfl) ⟨586176, by rfl⟩ : syracuseStep 1563137 = 1172353) B1172353
theorem B1759967 : Blo 271824 1759967 := bstep (se 1 (by rfl) ⟨1319975, by rfl⟩ : syracuseStep 1759967 = 2639951) B2639951
theorem B613673 : Blo 271824 613673 := bstep (se 2 (by rfl) ⟨230127, by rfl⟩ : syracuseStep 613673 = 460255) B460255
theorem B777707 : Blo 271824 777707 := bstep (se 1 (by rfl) ⟨583280, by rfl⟩ : syracuseStep 777707 = 1166561) B1166561
theorem B1662443 : Blo 271824 1662443 := bstep (se 1 (by rfl) ⟨1246832, by rfl⟩ : syracuseStep 1662443 = 2493665) B2493665
theorem B2645905 : Blo 271824 2645905 := bstep (se 2 (by rfl) ⟨992214, by rfl⟩ : syracuseStep 2645905 = 1984429) B1984429
theorem B516223 : Blo 271824 516223 := bstep (se 1 (by rfl) ⟨387167, by rfl⟩ : syracuseStep 516223 = 774335) B774335
theorem B1106075 : Blo 271824 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B614825 : Blo 271824 614825 := bstep (se 2 (by rfl) ⟨230559, by rfl⟩ : syracuseStep 614825 = 461119) B461119
theorem B615239 : Blo 271824 615239 := bstep (se 1 (by rfl) ⟨461429, by rfl⟩ : syracuseStep 615239 = 922859) B922859
theorem B779233 : Blo 271824 779233 := bstep (se 2 (by rfl) ⟨292212, by rfl⟩ : syracuseStep 779233 = 584425) B584425
theorem B1959461 : Blo 271824 1959461 := bstep (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) B367399
theorem B9528965 : Blo 271824 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B616175 : Blo 271824 616175 := bstep (se 1 (by rfl) ⟨462131, by rfl⟩ : syracuseStep 616175 = 924263) B924263
theorem B1174009 : Blo 271824 1174009 := bstep (se 2 (by rfl) ⟨440253, by rfl⟩ : syracuseStep 1174009 = 880507) B880507
theorem B2091743 : Blo 271824 2091743 := bstep (se 1 (by rfl) ⟨1568807, by rfl⟩ : syracuseStep 2091743 = 3137615) B3137615
theorem B781807 : Blo 271824 781807 := bstep (se 1 (by rfl) ⟨586355, by rfl⟩ : syracuseStep 781807 = 1172711) B1172711
theorem B2092715 : Blo 271824 2092715 := bstep (se 1 (by rfl) ⟨1569536, by rfl⟩ : syracuseStep 2092715 = 3139073) B3139073
theorem B1568443 : Blo 271824 1568443 := bstep (se 1 (by rfl) ⟨1176332, by rfl⟩ : syracuseStep 1568443 = 2352665) B2352665
theorem B618731 : Blo 271824 618731 := bstep (se 1 (by rfl) ⟨464048, by rfl⟩ : syracuseStep 618731 = 928097) B928097
theorem B586271 : Blo 271824 586271 := bstep (se 1 (by rfl) ⟨439703, by rfl⟩ : syracuseStep 586271 = 879407) B879407
theorem B5272127 : Blo 271824 5272127 := bstep (se 1 (by rfl) ⟨3954095, by rfl⟩ : syracuseStep 5272127 = 7908191) B7908191
theorem B12612347 : Blo 271824 12612347 := bstep (se 1 (by rfl) ⟨9459260, by rfl⟩ : syracuseStep 12612347 = 18918521) B18918521
theorem B390511 : Blo 271824 390511 := bstep (se 1 (by rfl) ⟨292883, by rfl⟩ : syracuseStep 390511 = 585767) B585767
theorem B1570175 : Blo 271824 1570175 := bstep (se 1 (by rfl) ⟨1177631, by rfl⟩ : syracuseStep 1570175 = 2355263) B2355263
theorem B1406447 : Blo 271824 1406447 := bstep (se 1 (by rfl) ⟨1054835, by rfl⟩ : syracuseStep 1406447 = 2109671) B2109671
theorem B718715 : Blo 271824 718715 := bstep (se 1 (by rfl) ⟨539036, by rfl⟩ : syracuseStep 718715 = 1078073) B1078073
theorem B1309535 : Blo 271824 1309535 := bstep (se 1 (by rfl) ⟨982151, by rfl⟩ : syracuseStep 1309535 = 1964303) B1964303
theorem B688297 : Blo 271824 688297 := bstep (se 2 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 688297 = 516223) B516223
theorem B1114523 : Blo 271824 1114523 := bstep (se 1 (by rfl) ⟨835892, by rfl⟩ : syracuseStep 1114523 = 1671785) B1671785
theorem B2949533 : Blo 271824 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B295655 : Blo 271824 295655 := bstep (se 1 (by rfl) ⟨221741, by rfl⟩ : syracuseStep 295655 = 443483) B443483
theorem B459641 : Blo 271824 459641 := bstep (se 2 (by rfl) ⟨172365, by rfl⟩ : syracuseStep 459641 = 344731) B344731
theorem B1311995 : Blo 271824 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B20122037 : Blo 271824 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B494363 : Blo 271824 494363 := bstep (se 1 (by rfl) ⟨370772, by rfl⟩ : syracuseStep 494363 = 741545) B741545
theorem B494623 : Blo 271824 494623 := bstep (se 1 (by rfl) ⟨370967, by rfl⟩ : syracuseStep 494623 = 741935) B741935
theorem B691355 : Blo 271824 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B920915 : Blo 271824 920915 := bstep (se 1 (by rfl) ⟨690686, by rfl⟩ : syracuseStep 920915 = 1381373) B1381373
theorem B692135 : Blo 271824 692135 := bstep (se 1 (by rfl) ⟨519101, by rfl⟩ : syracuseStep 692135 = 1038203) B1038203
theorem B922319 : Blo 271824 922319 := bstep (se 1 (by rfl) ⟨691739, by rfl⟩ : syracuseStep 922319 = 1383479) B1383479
theorem B1972583 : Blo 271824 1972583 := bstep (se 1 (by rfl) ⟨1479437, by rfl⟩ : syracuseStep 1972583 = 2958875) B2958875
theorem B11214935 : Blo 271824 11214935 := bstep (se 1 (by rfl) ⟨8411201, by rfl⟩ : syracuseStep 11214935 = 16822403) B16822403
theorem B8069291 : Blo 271824 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B3514751 : Blo 271824 3514751 := bstep (se 1 (by rfl) ⟨2636063, by rfl⟩ : syracuseStep 3514751 = 5272127) B5272127
theorem B4662683 : Blo 271824 4662683 := bstep (se 1 (by rfl) ⟨3497012, by rfl⟩ : syracuseStep 4662683 = 6994025) B6994025
theorem B271847 : Blo 271824 271847 := bstep (se 1 (by rfl) ⟨203885, by rfl⟩ : syracuseStep 271847 = 407771) B407771
theorem B927287 : Blo 271824 927287 := bstep (se 1 (by rfl) ⟨695465, by rfl⟩ : syracuseStep 927287 = 1390931) B1390931
theorem B2336809 : Blo 271824 2336809 := bstep (se 2 (by rfl) ⟨876303, by rfl⟩ : syracuseStep 2336809 = 1752607) B1752607
theorem B272455 : Blo 271824 272455 := bstep (se 1 (by rfl) ⟨204341, by rfl⟩ : syracuseStep 272455 = 408683) B408683
theorem B927827 : Blo 271824 927827 := bstep (se 1 (by rfl) ⟨695870, by rfl⟩ : syracuseStep 927827 = 1391741) B1391741
theorem B272487 : Blo 271824 272487 := bstep (se 1 (by rfl) ⟨204365, by rfl⟩ : syracuseStep 272487 = 408731) B408731
theorem B60827851 : Blo 271824 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B272831 : Blo 271824 272831 := bstep (se 1 (by rfl) ⟨204623, by rfl⟩ : syracuseStep 272831 = 409247) B409247
theorem B928475 : Blo 271824 928475 := bstep (se 1 (by rfl) ⟨696356, by rfl⟩ : syracuseStep 928475 = 1392713) B1392713
theorem B306175 : Blo 271824 306175 := bstep (se 1 (by rfl) ⟨229631, by rfl⟩ : syracuseStep 306175 = 459263) B459263
theorem B273563 : Blo 271824 273563 := bstep (se 1 (by rfl) ⟨205172, by rfl⟩ : syracuseStep 273563 = 410345) B410345
theorem B273615 : Blo 271824 273615 := bstep (se 1 (by rfl) ⟨205211, by rfl⟩ : syracuseStep 273615 = 410423) B410423
theorem B273691 : Blo 271824 273691 := bstep (se 1 (by rfl) ⟨205268, by rfl⟩ : syracuseStep 273691 = 410537) B410537
theorem B306535 : Blo 271824 306535 := bstep (se 1 (by rfl) ⟨229901, by rfl⟩ : syracuseStep 306535 = 459803) B459803
theorem B1388015 : Blo 271824 1388015 := bstep (se 1 (by rfl) ⟨1041011, by rfl⟩ : syracuseStep 1388015 = 2082023) B2082023
theorem B273919 : Blo 271824 273919 := bstep (se 1 (by rfl) ⟨205439, by rfl⟩ : syracuseStep 273919 = 410879) B410879
theorem B273947 : Blo 271824 273947 := bstep (se 1 (by rfl) ⟨205460, by rfl⟩ : syracuseStep 273947 = 410921) B410921
theorem B2076191 : Blo 271824 2076191 := bstep (se 1 (by rfl) ⟨1557143, by rfl⟩ : syracuseStep 2076191 = 3114287) B3114287
theorem B929771 : Blo 271824 929771 := bstep (se 1 (by rfl) ⟨697328, by rfl⟩ : syracuseStep 929771 = 1394657) B1394657
theorem B1585225 : Blo 271824 1585225 := bstep (se 2 (by rfl) ⟨594459, by rfl⟩ : syracuseStep 1585225 = 1188919) B1188919
theorem B274523 : Blo 271824 274523 := bstep (se 1 (by rfl) ⟨205892, by rfl⟩ : syracuseStep 274523 = 411785) B411785
theorem B275071 : Blo 271824 275071 := bstep (se 1 (by rfl) ⟨206303, by rfl⟩ : syracuseStep 275071 = 412607) B412607
theorem B275183 : Blo 271824 275183 := bstep (se 1 (by rfl) ⟨206387, by rfl⟩ : syracuseStep 275183 = 412775) B412775
theorem B1324127 : Blo 271824 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B6042937 : Blo 271824 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B23737697 : Blo 271824 23737697 := bstep (se 2 (by rfl) ⟨8901636, by rfl⟩ : syracuseStep 23737697 = 17803273) B17803273
theorem B832925 : Blo 271824 832925 := bstep (se 3 (by rfl) ⟨156173, by rfl⟩ : syracuseStep 832925 = 312347) B312347
theorem B3487171 : Blo 271824 3487171 := bstep (se 1 (by rfl) ⟨2615378, by rfl⟩ : syracuseStep 3487171 = 5230757) B5230757
theorem B5617309 : Blo 271824 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B309415 : Blo 271824 309415 := bstep (se 1 (by rfl) ⟨232061, by rfl⟩ : syracuseStep 309415 = 464123) B464123
theorem B2341183 : Blo 271824 2341183 := bstep (se 1 (by rfl) ⟨1755887, by rfl⟩ : syracuseStep 2341183 = 3511775) B3511775
theorem B3488507 : Blo 271824 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B408383 : Blo 271824 408383 := bstep (se 1 (by rfl) ⟨306287, by rfl⟩ : syracuseStep 408383 = 612575) B612575
theorem B932705 : Blo 271824 932705 := bstep (se 2 (by rfl) ⟨349764, by rfl⟩ : syracuseStep 932705 = 699529) B699529
theorem B1489823 : Blo 271824 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B1490183 : Blo 271824 1490183 := bstep (se 1 (by rfl) ⟨1117637, by rfl⟩ : syracuseStep 1490183 = 2235275) B2235275
theorem B409115 : Blo 271824 409115 := bstep (se 1 (by rfl) ⟨306836, by rfl⟩ : syracuseStep 409115 = 613673) B613673
theorem B409883 : Blo 271824 409883 := bstep (se 1 (by rfl) ⟨307412, by rfl⟩ : syracuseStep 409883 = 614825) B614825
theorem B410159 : Blo 271824 410159 := bstep (se 1 (by rfl) ⟨307619, by rfl⟩ : syracuseStep 410159 = 615239) B615239
theorem B1032871 : Blo 271824 1032871 := bstep (se 1 (by rfl) ⟨774653, by rfl⟩ : syracuseStep 1032871 = 1549307) B1549307
theorem B410783 : Blo 271824 410783 := bstep (se 1 (by rfl) ⟨308087, by rfl⟩ : syracuseStep 410783 = 616175) B616175
theorem B2803369 : Blo 271824 2803369 := bstep (se 2 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 2803369 = 2102527) B2102527
theorem B1394495 : Blo 271824 1394495 := bstep (se 1 (by rfl) ⟨1045871, by rfl⟩ : syracuseStep 1394495 = 2091743) B2091743
theorem B2869465 : Blo 271824 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B1395143 : Blo 271824 1395143 := bstep (se 1 (by rfl) ⟨1046357, by rfl⟩ : syracuseStep 1395143 = 2092715) B2092715
theorem B707051 : Blo 271824 707051 := bstep (se 1 (by rfl) ⟨530288, by rfl⟩ : syracuseStep 707051 = 1060577) B1060577
theorem B412487 : Blo 271824 412487 := bstep (se 1 (by rfl) ⟨309365, by rfl⟩ : syracuseStep 412487 = 618731) B618731
theorem B8408231 : Blo 271824 8408231 := bstep (se 1 (by rfl) ⟨6306173, by rfl⟩ : syracuseStep 8408231 = 12612347) B12612347
theorem B2346515 : Blo 271824 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B937631 : Blo 271824 937631 := bstep (se 1 (by rfl) ⟨703223, by rfl⟩ : syracuseStep 937631 = 1406447) B1406447
theorem B479143 : Blo 271824 479143 := bstep (se 1 (by rfl) ⟨359357, by rfl⟩ : syracuseStep 479143 = 718715) B718715
theorem B28987409 : Blo 271824 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B873023 : Blo 271824 873023 := bstep (se 1 (by rfl) ⟨654767, by rfl⟩ : syracuseStep 873023 = 1309535) B1309535
theorem B3527873 : Blo 271824 3527873 := bstep (se 2 (by rfl) ⟨1322952, by rfl⟩ : syracuseStep 3527873 = 2645905) B2645905
theorem B5920073 : Blo 271824 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B12671477 : Blo 271824 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B1038977 : Blo 271824 1038977 := bstep (se 2 (by rfl) ⟨389616, by rfl⟩ : syracuseStep 1038977 = 779233) B779233
theorem B613115 : Blo 271824 613115 := bstep (se 1 (by rfl) ⟨459836, by rfl⟩ : syracuseStep 613115 = 919673) B919673
theorem B614393 : Blo 271824 614393 := bstep (se 2 (by rfl) ⟨230397, by rfl⟩ : syracuseStep 614393 = 460795) B460795
theorem B778835 : Blo 271824 778835 := bstep (se 1 (by rfl) ⟨584126, by rfl⟩ : syracuseStep 778835 = 1168253) B1168253
theorem B1565345 : Blo 271824 1565345 := bstep (se 2 (by rfl) ⟨587004, by rfl⟩ : syracuseStep 1565345 = 1174009) B1174009
theorem B1106855 : Blo 271824 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B615707 : Blo 271824 615707 := bstep (se 1 (by rfl) ⟨461780, by rfl⟩ : syracuseStep 615707 = 923561) B923561
theorem B517423 : Blo 271824 517423 := bstep (se 1 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 517423 = 776135) B776135
theorem B615887 : Blo 271824 615887 := bstep (se 1 (by rfl) ⟨461915, by rfl⟩ : syracuseStep 615887 = 923831) B923831
theorem B1042091 : Blo 271824 1042091 := bstep (se 1 (by rfl) ⟨781568, by rfl⟩ : syracuseStep 1042091 = 1563137) B1563137
theorem B1173311 : Blo 271824 1173311 := bstep (se 1 (by rfl) ⟨879983, by rfl⟩ : syracuseStep 1173311 = 1759967) B1759967
theorem B1042409 : Blo 271824 1042409 := bstep (se 2 (by rfl) ⟨390903, by rfl⟩ : syracuseStep 1042409 = 781807) B781807
theorem B2091257 : Blo 271824 2091257 := bstep (se 2 (by rfl) ⟨784221, by rfl⟩ : syracuseStep 2091257 = 1568443) B1568443
theorem B518471 : Blo 271824 518471 := bstep (se 1 (by rfl) ⟨388853, by rfl⟩ : syracuseStep 518471 = 777707) B777707
theorem B1108295 : Blo 271824 1108295 := bstep (se 1 (by rfl) ⟨831221, by rfl⟩ : syracuseStep 1108295 = 1662443) B1662443
theorem B616787 : Blo 271824 616787 := bstep (se 1 (by rfl) ⟨462590, by rfl⟩ : syracuseStep 616787 = 925181) B925181
theorem B616859 : Blo 271824 616859 := bstep (se 1 (by rfl) ⟨462644, by rfl⟩ : syracuseStep 616859 = 925289) B925289
theorem B617849 : Blo 271824 617849 := bstep (se 2 (by rfl) ⟨231693, by rfl⟩ : syracuseStep 617849 = 463387) B463387
theorem B1306307 : Blo 271824 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B6352643 : Blo 271824 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B618587 : Blo 271824 618587 := bstep (se 1 (by rfl) ⟨463940, by rfl⟩ : syracuseStep 618587 = 927881) B927881
theorem B291119 : Blo 271824 291119 := bstep (se 1 (by rfl) ⟨218339, by rfl⟩ : syracuseStep 291119 = 436679) B436679
theorem B520681 : Blo 271824 520681 := bstep (se 2 (by rfl) ⟨195255, by rfl⟩ : syracuseStep 520681 = 390511) B390511
theorem B619487 : Blo 271824 619487 := bstep (se 1 (by rfl) ⟨464615, by rfl⟩ : syracuseStep 619487 = 929231) B929231
theorem B291871 : Blo 271824 291871 := bstep (se 1 (by rfl) ⟨218903, by rfl⟩ : syracuseStep 291871 = 437807) B437807
theorem B390847 : Blo 271824 390847 := bstep (se 1 (by rfl) ⟨293135, by rfl⟩ : syracuseStep 390847 = 586271) B586271
theorem B1046783 : Blo 271824 1046783 := bstep (se 1 (by rfl) ⟨785087, by rfl⟩ : syracuseStep 1046783 = 1570175) B1570175
theorem B77299757 : Blo 271824 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B917729 : Blo 271824 917729 := bstep (se 2 (by rfl) ⟨344148, by rfl⟩ : syracuseStep 917729 = 688297) B688297
theorem B1966355 : Blo 271824 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B1377161 : Blo 271824 1377161 := bstep (se 2 (by rfl) ⟨516435, by rfl⟩ : syracuseStep 1377161 = 1032871) B1032871
theorem B2328061 : Blo 271824 2328061 := bstep (se 3 (by rfl) ⟨436511, by rfl⟩ : syracuseStep 2328061 = 873023) B873023
theorem B689897 : Blo 271824 689897 := bstep (se 2 (by rfl) ⟨258711, by rfl⟩ : syracuseStep 689897 = 517423) B517423
theorem B460903 : Blo 271824 460903 := bstep (se 1 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 460903 = 691355) B691355
theorem B5605487 : Blo 271824 5605487 := bstep (se 1 (by rfl) ⟨4204115, by rfl⟩ : syracuseStep 5605487 = 8408231) B8408231
theorem B3737825 : Blo 271824 3737825 := bstep (se 2 (by rfl) ⟨1401684, by rfl⟩ : syracuseStep 3737825 = 2803369) B2803369
theorem B625087 : Blo 271824 625087 := bstep (se 1 (by rfl) ⟨468815, by rfl⟩ : syracuseStep 625087 = 937631) B937631
theorem B461423 : Blo 271824 461423 := bstep (se 1 (by rfl) ⟨346067, by rfl⟩ : syracuseStep 461423 = 692135) B692135
theorem B3115745 : Blo 271824 3115745 := bstep (se 2 (by rfl) ⟨1168404, by rfl⟩ : syracuseStep 3115745 = 2336809) B2336809
theorem B81103801 : Blo 271824 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B659497 : Blo 271824 659497 := bstep (se 2 (by rfl) ⟨247311, by rfl⟩ : syracuseStep 659497 = 494623) B494623
theorem B1315055 : Blo 271824 1315055 := bstep (se 1 (by rfl) ⟨986291, by rfl⟩ : syracuseStep 1315055 = 1972583) B1972583
theorem B692651 : Blo 271824 692651 := bstep (se 1 (by rfl) ⟨519488, by rfl⟩ : syracuseStep 692651 = 1038977) B1038977
theorem B7476623 : Blo 271824 7476623 := bstep (se 1 (by rfl) ⟨5607467, by rfl⟩ : syracuseStep 7476623 = 11214935) B11214935
theorem B5379527 : Blo 271824 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B694241 : Blo 271824 694241 := bstep (se 2 (by rfl) ⟨260340, by rfl⟩ : syracuseStep 694241 = 520681) B520681
theorem B694727 : Blo 271824 694727 := bstep (se 1 (by rfl) ⟨521045, by rfl⟩ : syracuseStep 694727 = 1042091) B1042091
theorem B694939 : Blo 271824 694939 := bstep (se 1 (by rfl) ⟨521204, by rfl⟩ : syracuseStep 694939 = 1042409) B1042409
theorem B1318301 : Blo 271824 1318301 := bstep (se 3 (by rfl) ⟨247181, by rfl⟩ : syracuseStep 1318301 = 494363) B494363
theorem B925343 : Blo 271824 925343 := bstep (se 1 (by rfl) ⟨694007, by rfl⟩ : syracuseStep 925343 = 1388015) B1388015
theorem B1384127 : Blo 271824 1384127 := bstep (se 1 (by rfl) ⟨1038095, by rfl⟩ : syracuseStep 1384127 = 2076191) B2076191
theorem B3153653 : Blo 271824 3153653 := bstep (se 5 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 3153653 = 295655) B295655
theorem B4235095 : Blo 271824 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B3121577 : Blo 271824 3121577 := bstep (se 2 (by rfl) ⟨1170591, by rfl⟩ : syracuseStep 3121577 = 2341183) B2341183
theorem B697855 : Blo 271824 697855 := bstep (se 1 (by rfl) ⟨523391, by rfl⟩ : syracuseStep 697855 = 1046783) B1046783
theorem B272255 : Blo 271824 272255 := bstep (se 1 (by rfl) ⟨204191, by rfl⟩ : syracuseStep 272255 = 408383) B408383
theorem B993215 : Blo 271824 993215 := bstep (se 1 (by rfl) ⟨744911, by rfl⟩ : syracuseStep 993215 = 1489823) B1489823
theorem B993455 : Blo 271824 993455 := bstep (se 1 (by rfl) ⟨745091, by rfl⟩ : syracuseStep 993455 = 1490183) B1490183
theorem B272743 : Blo 271824 272743 := bstep (se 1 (by rfl) ⟨204557, by rfl⟩ : syracuseStep 272743 = 409115) B409115
theorem B273255 : Blo 271824 273255 := bstep (se 1 (by rfl) ⟨204941, by rfl⟩ : syracuseStep 273255 = 409883) B409883
theorem B273439 : Blo 271824 273439 := bstep (se 1 (by rfl) ⟨205079, by rfl⟩ : syracuseStep 273439 = 410159) B410159
theorem B306427 : Blo 271824 306427 := bstep (se 1 (by rfl) ⟨229820, by rfl⟩ : syracuseStep 306427 = 459641) B459641
theorem B273855 : Blo 271824 273855 := bstep (se 1 (by rfl) ⟨205391, by rfl⟩ : syracuseStep 273855 = 410783) B410783
theorem B929663 : Blo 271824 929663 := bstep (se 1 (by rfl) ⟨697247, by rfl⟩ : syracuseStep 929663 = 1394495) B1394495
theorem B13414691 : Blo 271824 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B930095 : Blo 271824 930095 := bstep (se 1 (by rfl) ⟨697571, by rfl⟩ : syracuseStep 930095 = 1395143) B1395143
theorem B471367 : Blo 271824 471367 := bstep (se 1 (by rfl) ⟨353525, by rfl⟩ : syracuseStep 471367 = 707051) B707051
theorem B274991 : Blo 271824 274991 := bstep (se 1 (by rfl) ⟨206243, by rfl⟩ : syracuseStep 274991 = 412487) B412487
theorem B3946715 : Blo 271824 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B408233 : Blo 271824 408233 := bstep (se 2 (by rfl) ⟨153087, by rfl⟩ : syracuseStep 408233 = 306175) B306175
theorem B408713 : Blo 271824 408713 := bstep (se 2 (by rfl) ⟨153267, by rfl⟩ : syracuseStep 408713 = 306535) B306535
theorem B408743 : Blo 271824 408743 := bstep (se 1 (by rfl) ⟨306557, by rfl⟩ : syracuseStep 408743 = 613115) B613115
theorem B638857 : Blo 271824 638857 := bstep (se 2 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 638857 = 479143) B479143
theorem B409595 : Blo 271824 409595 := bstep (se 1 (by rfl) ⟨307196, by rfl⟩ : syracuseStep 409595 = 614393) B614393
theorem B2113633 : Blo 271824 2113633 := bstep (se 2 (by rfl) ⟨792612, by rfl⟩ : syracuseStep 2113633 = 1585225) B1585225
theorem B2343167 : Blo 271824 2343167 := bstep (se 1 (by rfl) ⟨1757375, by rfl⟩ : syracuseStep 2343167 = 3514751) B3514751
theorem B737903 : Blo 271824 737903 := bstep (se 1 (by rfl) ⟨553427, by rfl⟩ : syracuseStep 737903 = 1106855) B1106855
theorem B410471 : Blo 271824 410471 := bstep (se 1 (by rfl) ⟨307853, by rfl⟩ : syracuseStep 410471 = 615707) B615707
theorem B410591 : Blo 271824 410591 := bstep (se 1 (by rfl) ⟨307943, by rfl⟩ : syracuseStep 410591 = 615887) B615887
theorem B1394171 : Blo 271824 1394171 := bstep (se 1 (by rfl) ⟨1045628, by rfl⟩ : syracuseStep 1394171 = 2091257) B2091257
theorem B345647 : Blo 271824 345647 := bstep (se 1 (by rfl) ⟨259235, by rfl⟩ : syracuseStep 345647 = 518471) B518471
theorem B738863 : Blo 271824 738863 := bstep (se 1 (by rfl) ⟨554147, by rfl⟩ : syracuseStep 738863 = 1108295) B1108295
theorem B411191 : Blo 271824 411191 := bstep (se 1 (by rfl) ⟨308393, by rfl⟩ : syracuseStep 411191 = 616787) B616787
theorem B411239 : Blo 271824 411239 := bstep (se 1 (by rfl) ⟨308429, by rfl⟩ : syracuseStep 411239 = 616859) B616859
theorem B7489745 : Blo 271824 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B411899 : Blo 271824 411899 := bstep (se 1 (by rfl) ⟨308924, by rfl⟩ : syracuseStep 411899 = 617849) B617849
theorem B870871 : Blo 271824 870871 := bstep (se 1 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 870871 = 1306307) B1306307
theorem B412391 : Blo 271824 412391 := bstep (se 1 (by rfl) ⟨309293, by rfl⟩ : syracuseStep 412391 = 618587) B618587
theorem B412553 : Blo 271824 412553 := bstep (se 2 (by rfl) ⟨154707, by rfl⟩ : syracuseStep 412553 = 309415) B309415
theorem B412991 : Blo 271824 412991 := bstep (se 1 (by rfl) ⟨309743, by rfl⟩ : syracuseStep 412991 = 619487) B619487
theorem B743015 : Blo 271824 743015 := bstep (se 1 (by rfl) ⟨557261, by rfl⟩ : syracuseStep 743015 = 1114523) B1114523
theorem B776317 : Blo 271824 776317 := bstep (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) B291119
theorem B613943 : Blo 271824 613943 := bstep (se 1 (by rfl) ⟨460457, by rfl⟩ : syracuseStep 613943 = 920915) B920915
theorem B1564343 : Blo 271824 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B3825953 : Blo 271824 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B614879 : Blo 271824 614879 := bstep (se 1 (by rfl) ⟨461159, by rfl⟩ : syracuseStep 614879 = 922319) B922319
theorem B3498653 : Blo 271824 3498653 := bstep (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) B1311995
theorem B2351915 : Blo 271824 2351915 := bstep (se 1 (by rfl) ⟨1763936, by rfl⟩ : syracuseStep 2351915 = 3527873) B3527873
theorem B8447651 : Blo 271824 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B519223 : Blo 271824 519223 := bstep (se 1 (by rfl) ⟨389417, by rfl⟩ : syracuseStep 519223 = 778835) B778835
theorem B1043563 : Blo 271824 1043563 := bstep (se 1 (by rfl) ⟨782672, by rfl⟩ : syracuseStep 1043563 = 1565345) B1565345
theorem B3108455 : Blo 271824 3108455 := bstep (se 1 (by rfl) ⟨2331341, by rfl⟩ : syracuseStep 3108455 = 4662683) B4662683
theorem B618191 : Blo 271824 618191 := bstep (se 1 (by rfl) ⟨463643, by rfl⟩ : syracuseStep 618191 = 927287) B927287
theorem B782207 : Blo 271824 782207 := bstep (se 1 (by rfl) ⟨586655, by rfl⟩ : syracuseStep 782207 = 1173311) B1173311
theorem B389161 : Blo 271824 389161 := bstep (se 2 (by rfl) ⟨145935, by rfl⟩ : syracuseStep 389161 = 291871) B291871
theorem B618551 : Blo 271824 618551 := bstep (se 1 (by rfl) ⟨463913, by rfl⟩ : syracuseStep 618551 = 927827) B927827
theorem B8057249 : Blo 271824 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B618983 : Blo 271824 618983 := bstep (se 1 (by rfl) ⟨464237, by rfl⟩ : syracuseStep 618983 = 928475) B928475
theorem B4649561 : Blo 271824 4649561 := bstep (se 2 (by rfl) ⟨1743585, by rfl⟩ : syracuseStep 4649561 = 3487171) B3487171
theorem B521129 : Blo 271824 521129 := bstep (se 2 (by rfl) ⟨195423, by rfl⟩ : syracuseStep 521129 = 390847) B390847
theorem B619847 : Blo 271824 619847 := bstep (se 1 (by rfl) ⟨464885, by rfl⟩ : syracuseStep 619847 = 929771) B929771
theorem B882751 : Blo 271824 882751 := bstep (se 1 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 882751 = 1324127) B1324127
theorem B15825131 : Blo 271824 15825131 := bstep (se 1 (by rfl) ⟨11868848, by rfl⟩ : syracuseStep 15825131 = 23737697) B23737697
theorem B555283 : Blo 271824 555283 := bstep (se 1 (by rfl) ⟨416462, by rfl⟩ : syracuseStep 555283 = 832925) B832925
theorem B2325671 : Blo 271824 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B621803 : Blo 271824 621803 := bstep (se 1 (by rfl) ⟨466352, by rfl⟩ : syracuseStep 621803 = 932705) B932705
theorem B1310903 : Blo 271824 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B491935 : Blo 271824 491935 := bstep (se 1 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 491935 = 737903) B737903
theorem B11272709 : Blo 271824 11272709 := bstep (se 4 (by rfl) ⟨1056816, by rfl⟩ : syracuseStep 11272709 = 2113633) B2113633
theorem B918107 : Blo 271824 918107 := bstep (se 1 (by rfl) ⟨688580, by rfl⟩ : syracuseStep 918107 = 1377161) B1377161
theorem B492575 : Blo 271824 492575 := bstep (se 1 (by rfl) ⟨369431, by rfl⟩ : syracuseStep 492575 = 738863) B738863
theorem B459931 : Blo 271824 459931 := bstep (se 1 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 459931 = 689897) B689897
theorem B3736991 : Blo 271824 3736991 := bstep (se 1 (by rfl) ⟨2802743, by rfl⟩ : syracuseStep 3736991 = 5605487) B5605487
theorem B2491883 : Blo 271824 2491883 := bstep (se 1 (by rfl) ⟨1868912, by rfl⟩ : syracuseStep 2491883 = 3737825) B3737825
theorem B461767 : Blo 271824 461767 := bstep (se 1 (by rfl) ⟨346325, by rfl⟩ : syracuseStep 461767 = 692651) B692651
theorem B4984415 : Blo 271824 4984415 := bstep (se 1 (by rfl) ⟨3738311, by rfl⟩ : syracuseStep 4984415 = 7476623) B7476623
theorem B495343 : Blo 271824 495343 := bstep (se 1 (by rfl) ⟨371507, by rfl⟩ : syracuseStep 495343 = 743015) B743015
theorem B108138401 : Blo 271824 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B462827 : Blo 271824 462827 := bstep (se 1 (by rfl) ⟨347120, by rfl⟩ : syracuseStep 462827 = 694241) B694241
theorem B692297 : Blo 271824 692297 := bstep (se 2 (by rfl) ⟨259611, by rfl⟩ : syracuseStep 692297 = 519223) B519223
theorem B921725 : Blo 271824 921725 := bstep (se 3 (by rfl) ⟨172823, by rfl⟩ : syracuseStep 921725 = 345647) B345647
theorem B463151 : Blo 271824 463151 := bstep (se 1 (by rfl) ⟨347363, by rfl⟩ : syracuseStep 463151 = 694727) B694727
theorem B922751 : Blo 271824 922751 := bstep (se 1 (by rfl) ⟨692063, by rfl⟩ : syracuseStep 922751 = 1384127) B1384127
theorem B2102435 : Blo 271824 2102435 := bstep (se 1 (by rfl) ⟨1576826, by rfl⟩ : syracuseStep 2102435 = 3153653) B3153653
theorem B628489 : Blo 271824 628489 := bstep (se 2 (by rfl) ⟨235683, by rfl⟩ : syracuseStep 628489 = 471367) B471367
theorem B2332435 : Blo 271824 2332435 := bstep (se 1 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 2332435 = 3498653) B3498653
theorem B662143 : Blo 271824 662143 := bstep (se 1 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 662143 = 993215) B993215
theorem B662303 : Blo 271824 662303 := bstep (se 1 (by rfl) ⟨496727, by rfl⟩ : syracuseStep 662303 = 993455) B993455
theorem B2072303 : Blo 271824 2072303 := bstep (se 1 (by rfl) ⟨1554227, by rfl⟩ : syracuseStep 2072303 = 3108455) B3108455
theorem B926585 : Blo 271824 926585 := bstep (se 2 (by rfl) ⟨347469, by rfl⟩ : syracuseStep 926585 = 694939) B694939
theorem B2631143 : Blo 271824 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B272155 : Blo 271824 272155 := bstep (se 1 (by rfl) ⟨204116, by rfl⟩ : syracuseStep 272155 = 408233) B408233
theorem B272475 : Blo 271824 272475 := bstep (se 1 (by rfl) ⟨204356, by rfl⟩ : syracuseStep 272475 = 408713) B408713
theorem B1550447 : Blo 271824 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B272495 : Blo 271824 272495 := bstep (se 1 (by rfl) ⟨204371, by rfl⟩ : syracuseStep 272495 = 408743) B408743
theorem B5646793 : Blo 271824 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B273063 : Blo 271824 273063 := bstep (se 1 (by rfl) ⟨204797, by rfl⟩ : syracuseStep 273063 = 409595) B409595
theorem B273647 : Blo 271824 273647 := bstep (se 1 (by rfl) ⟨205235, by rfl⟩ : syracuseStep 273647 = 410471) B410471
theorem B273727 : Blo 271824 273727 := bstep (se 1 (by rfl) ⟨205295, by rfl⟩ : syracuseStep 273727 = 410591) B410591
theorem B929447 : Blo 271824 929447 := bstep (se 1 (by rfl) ⟨697085, by rfl⟩ : syracuseStep 929447 = 1394171) B1394171
theorem B274127 : Blo 271824 274127 := bstep (se 1 (by rfl) ⟨205595, by rfl⟩ : syracuseStep 274127 = 411191) B411191
theorem B274159 : Blo 271824 274159 := bstep (se 1 (by rfl) ⟨205619, by rfl⟩ : syracuseStep 274159 = 411239) B411239
theorem B4993163 : Blo 271824 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B274599 : Blo 271824 274599 := bstep (se 1 (by rfl) ⟨205949, by rfl⟩ : syracuseStep 274599 = 411899) B411899
theorem B307615 : Blo 271824 307615 := bstep (se 1 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 307615 = 461423) B461423
theorem B2077163 : Blo 271824 2077163 := bstep (se 1 (by rfl) ⟨1557872, by rfl⟩ : syracuseStep 2077163 = 3115745) B3115745
theorem B274927 : Blo 271824 274927 := bstep (se 1 (by rfl) ⟨206195, by rfl⟩ : syracuseStep 274927 = 412391) B412391
theorem B275035 : Blo 271824 275035 := bstep (se 1 (by rfl) ⟨206276, by rfl⟩ : syracuseStep 275035 = 412553) B412553
theorem B930473 : Blo 271824 930473 := bstep (se 2 (by rfl) ⟨348927, by rfl⟩ : syracuseStep 930473 = 697855) B697855
theorem B275327 : Blo 271824 275327 := bstep (se 1 (by rfl) ⟨206495, by rfl⟩ : syracuseStep 275327 = 412991) B412991
theorem B833449 : Blo 271824 833449 := bstep (se 2 (by rfl) ⟨312543, by rfl⟩ : syracuseStep 833449 = 625087) B625087
theorem B1161161 : Blo 271824 1161161 := bstep (se 2 (by rfl) ⟨435435, by rfl⟩ : syracuseStep 1161161 = 870871) B870871
theorem B1391417 : Blo 271824 1391417 := bstep (se 2 (by rfl) ⟨521781, by rfl⟩ : syracuseStep 1391417 = 1043563) B1043563
theorem B408569 : Blo 271824 408569 := bstep (se 2 (by rfl) ⟨153213, by rfl⟩ : syracuseStep 408569 = 306427) B306427
theorem B409295 : Blo 271824 409295 := bstep (se 1 (by rfl) ⟨306971, by rfl⟩ : syracuseStep 409295 = 613943) B613943
theorem B2081051 : Blo 271824 2081051 := bstep (se 1 (by rfl) ⟨1560788, by rfl⟩ : syracuseStep 2081051 = 3121577) B3121577
theorem B409919 : Blo 271824 409919 := bstep (se 1 (by rfl) ⟨307439, by rfl⟩ : syracuseStep 409919 = 614879) B614879
theorem B412127 : Blo 271824 412127 := bstep (se 1 (by rfl) ⟨309095, by rfl⟩ : syracuseStep 412127 = 618191) B618191
theorem B412367 : Blo 271824 412367 := bstep (se 1 (by rfl) ⟨309275, by rfl⟩ : syracuseStep 412367 = 618551) B618551
theorem B1035089 : Blo 271824 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B412655 : Blo 271824 412655 := bstep (se 1 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 412655 = 618983) B618983
theorem B740377 : Blo 271824 740377 := bstep (se 2 (by rfl) ⟨277641, by rfl⟩ : syracuseStep 740377 = 555283) B555283
theorem B3099707 : Blo 271824 3099707 := bstep (se 1 (by rfl) ⟨2324780, by rfl⟩ : syracuseStep 3099707 = 4649561) B4649561
theorem B347419 : Blo 271824 347419 := bstep (se 1 (by rfl) ⟨260564, by rfl⟩ : syracuseStep 347419 = 521129) B521129
theorem B1658141 : Blo 271824 1658141 := bstep (se 3 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 1658141 = 621803) B621803
theorem B413231 : Blo 271824 413231 := bstep (se 1 (by rfl) ⟨309923, by rfl⟩ : syracuseStep 413231 = 619847) B619847
theorem B51533171 : Blo 271824 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B611819 : Blo 271824 611819 := bstep (se 1 (by rfl) ⟨458864, by rfl⟩ : syracuseStep 611819 = 917729) B917729
theorem B1562111 : Blo 271824 1562111 := bstep (se 1 (by rfl) ⟨1171583, by rfl⟩ : syracuseStep 1562111 = 2343167) B2343167
theorem B35772509 : Blo 271824 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B3104081 : Blo 271824 3104081 := bstep (se 2 (by rfl) ⟨1164030, by rfl⟩ : syracuseStep 3104081 = 2328061) B2328061
theorem B614537 : Blo 271824 614537 := bstep (se 2 (by rfl) ⟨230451, by rfl⟩ : syracuseStep 614537 = 460903) B460903
theorem B876703 : Blo 271824 876703 := bstep (se 1 (by rfl) ⟨657527, by rfl⟩ : syracuseStep 876703 = 1315055) B1315055
theorem B14345405 : Blo 271824 14345405 := bstep (se 3 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 14345405 = 5379527) B5379527
theorem B878867 : Blo 271824 878867 := bstep (se 1 (by rfl) ⟨659150, by rfl⟩ : syracuseStep 878867 = 1318301) B1318301
theorem B616895 : Blo 271824 616895 := bstep (se 1 (by rfl) ⟨462671, by rfl⟩ : syracuseStep 616895 = 925343) B925343
theorem B1042895 : Blo 271824 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B518881 : Blo 271824 518881 := bstep (se 2 (by rfl) ⟨194580, by rfl⟩ : syracuseStep 518881 = 389161) B389161
theorem B879329 : Blo 271824 879329 := bstep (se 2 (by rfl) ⟨329748, by rfl⟩ : syracuseStep 879329 = 659497) B659497
theorem B2550635 : Blo 271824 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B1567943 : Blo 271824 1567943 := bstep (se 1 (by rfl) ⟨1175957, by rfl⟩ : syracuseStep 1567943 = 2351915) B2351915
theorem B5631767 : Blo 271824 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B521471 : Blo 271824 521471 := bstep (se 1 (by rfl) ⟨391103, by rfl⟩ : syracuseStep 521471 = 782207) B782207
theorem B619775 : Blo 271824 619775 := bstep (se 1 (by rfl) ⟨464831, by rfl⟩ : syracuseStep 619775 = 929663) B929663
theorem B1177001 : Blo 271824 1177001 := bstep (se 2 (by rfl) ⟨441375, by rfl⟩ : syracuseStep 1177001 = 882751) B882751
theorem B620063 : Blo 271824 620063 := bstep (se 1 (by rfl) ⟨465047, by rfl⟩ : syracuseStep 620063 = 930095) B930095
theorem B5371499 : Blo 271824 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B10550087 : Blo 271824 10550087 := bstep (se 1 (by rfl) ⟨7912565, by rfl⟩ : syracuseStep 10550087 = 15825131) B15825131
theorem B851809 : Blo 271824 851809 := bstep (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) B638857
theorem B655913 : Blo 271824 655913 := bstep (se 2 (by rfl) ⟨245967, by rfl⟩ : syracuseStep 655913 = 491935) B491935
theorem B2491327 : Blo 271824 2491327 := bstep (se 1 (by rfl) ⟨1868495, by rfl⟩ : syracuseStep 2491327 = 3736991) B3736991
theorem B690059 : Blo 271824 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B2066471 : Blo 271824 2066471 := bstep (se 1 (by rfl) ⟨1549853, by rfl⟩ : syracuseStep 2066471 = 3099707) B3099707
theorem B72092267 : Blo 271824 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B461531 : Blo 271824 461531 := bstep (se 1 (by rfl) ⟨346148, by rfl⟩ : syracuseStep 461531 = 692297) B692297
theorem B1313533 : Blo 271824 1313533 := bstep (se 3 (by rfl) ⟨246287, by rfl⟩ : syracuseStep 1313533 = 492575) B492575
theorem B691841 : Blo 271824 691841 := bstep (se 2 (by rfl) ⟨259440, by rfl⟩ : syracuseStep 691841 = 518881) B518881
theorem B987169 : Blo 271824 987169 := bstep (se 2 (by rfl) ⟨370188, by rfl⟩ : syracuseStep 987169 = 740377) B740377
theorem B463225 : Blo 271824 463225 := bstep (se 2 (by rfl) ⟨173709, by rfl⟩ : syracuseStep 463225 = 347419) B347419
theorem B2069387 : Blo 271824 2069387 := bstep (se 1 (by rfl) ⟨1552040, by rfl⟩ : syracuseStep 2069387 = 3104081) B3104081
theorem B660457 : Blo 271824 660457 := bstep (se 2 (by rfl) ⟨247671, by rfl⟩ : syracuseStep 660457 = 495343) B495343
theorem B1381535 : Blo 271824 1381535 := bstep (se 1 (by rfl) ⟨1036151, by rfl⟩ : syracuseStep 1381535 = 2072303) B2072303
theorem B695263 : Blo 271824 695263 := bstep (se 1 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 695263 = 1042895) B1042895
theorem B1384775 : Blo 271824 1384775 := bstep (se 1 (by rfl) ⟨1038581, by rfl⟩ : syracuseStep 1384775 = 2077163) B2077163
theorem B3580999 : Blo 271824 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B3351941 : Blo 271824 3351941 := bstep (se 4 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 3351941 = 628489) B628489
theorem B927611 : Blo 271824 927611 := bstep (se 1 (by rfl) ⟨695708, by rfl⟩ : syracuseStep 927611 = 1391417) B1391417
theorem B272379 : Blo 271824 272379 := bstep (se 1 (by rfl) ⟨204284, by rfl⟩ : syracuseStep 272379 = 408569) B408569
theorem B272863 : Blo 271824 272863 := bstep (se 1 (by rfl) ⟨204647, by rfl⟩ : syracuseStep 272863 = 409295) B409295
theorem B1387367 : Blo 271824 1387367 := bstep (se 1 (by rfl) ⟨1040525, by rfl⟩ : syracuseStep 1387367 = 2081051) B2081051
theorem B273279 : Blo 271824 273279 := bstep (se 1 (by rfl) ⟨204959, by rfl⟩ : syracuseStep 273279 = 409919) B409919
theorem B30060557 : Blo 271824 30060557 := bstep (se 3 (by rfl) ⟨5636354, by rfl⟩ : syracuseStep 30060557 = 11272709) B11272709
theorem B274751 : Blo 271824 274751 := bstep (se 1 (by rfl) ⟨206063, by rfl⟩ : syracuseStep 274751 = 412127) B412127
theorem B274911 : Blo 271824 274911 := bstep (se 1 (by rfl) ⟨206183, by rfl⟩ : syracuseStep 274911 = 412367) B412367
theorem B275103 : Blo 271824 275103 := bstep (se 1 (by rfl) ⟨206327, by rfl⟩ : syracuseStep 275103 = 412655) B412655
theorem B275487 : Blo 271824 275487 := bstep (se 1 (by rfl) ⟨206615, by rfl⟩ : syracuseStep 275487 = 413231) B413231
theorem B3322943 : Blo 271824 3322943 := bstep (se 1 (by rfl) ⟨2492207, by rfl⟩ : syracuseStep 3322943 = 4984415) B4984415
theorem B308551 : Blo 271824 308551 := bstep (se 1 (by rfl) ⟨231413, by rfl⟩ : syracuseStep 308551 = 462827) B462827
theorem B308767 : Blo 271824 308767 := bstep (se 1 (by rfl) ⟨231575, by rfl⟩ : syracuseStep 308767 = 463151) B463151
theorem B34355447 : Blo 271824 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B407879 : Blo 271824 407879 := bstep (se 1 (by rfl) ⟨305909, by rfl⟩ : syracuseStep 407879 = 611819) B611819
theorem B441535 : Blo 271824 441535 := bstep (se 1 (by rfl) ⟨331151, by rfl⟩ : syracuseStep 441535 = 662303) B662303
theorem B409691 : Blo 271824 409691 := bstep (se 1 (by rfl) ⟨307268, by rfl⟩ : syracuseStep 409691 = 614537) B614537
theorem B410153 : Blo 271824 410153 := bstep (se 2 (by rfl) ⟨153807, by rfl⟩ : syracuseStep 410153 = 307615) B307615
theorem B1754095 : Blo 271824 1754095 := bstep (se 1 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 1754095 = 2631143) B2631143
theorem B1033631 : Blo 271824 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B411263 : Blo 271824 411263 := bstep (se 1 (by rfl) ⟨308447, by rfl⟩ : syracuseStep 411263 = 616895) B616895
theorem B3754511 : Blo 271824 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B3328775 : Blo 271824 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B347647 : Blo 271824 347647 := bstep (se 1 (by rfl) ⟨260735, by rfl⟩ : syracuseStep 347647 = 521471) B521471
theorem B413183 : Blo 271824 413183 := bstep (se 1 (by rfl) ⟨309887, by rfl⟩ : syracuseStep 413183 = 619775) B619775
theorem B413375 : Blo 271824 413375 := bstep (se 1 (by rfl) ⟨310031, by rfl⟩ : syracuseStep 413375 = 620063) B620063
theorem B774107 : Blo 271824 774107 := bstep (se 1 (by rfl) ⟨580580, by rfl⟩ : syracuseStep 774107 = 1161161) B1161161
theorem B7033391 : Blo 271824 7033391 := bstep (se 1 (by rfl) ⟨5275043, by rfl⟩ : syracuseStep 7033391 = 10550087) B10550087
theorem B1135745 : Blo 271824 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B873935 : Blo 271824 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B1168937 : Blo 271824 1168937 := bstep (se 2 (by rfl) ⟨438351, by rfl⟩ : syracuseStep 1168937 = 876703) B876703
theorem B612071 : Blo 271824 612071 := bstep (se 1 (by rfl) ⟨459053, by rfl⟩ : syracuseStep 612071 = 918107) B918107
theorem B1661255 : Blo 271824 1661255 := bstep (se 1 (by rfl) ⟨1245941, by rfl⟩ : syracuseStep 1661255 = 2491883) B2491883
theorem B613241 : Blo 271824 613241 := bstep (se 2 (by rfl) ⟨229965, by rfl⟩ : syracuseStep 613241 = 459931) B459931
theorem B1105427 : Blo 271824 1105427 := bstep (se 1 (by rfl) ⟨829070, by rfl⟩ : syracuseStep 1105427 = 1658141) B1658141
theorem B614483 : Blo 271824 614483 := bstep (se 1 (by rfl) ⟨460862, by rfl⟩ : syracuseStep 614483 = 921725) B921725
theorem B7529057 : Blo 271824 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B615167 : Blo 271824 615167 := bstep (se 1 (by rfl) ⟨461375, by rfl⟩ : syracuseStep 615167 = 922751) B922751
theorem B1401623 : Blo 271824 1401623 := bstep (se 1 (by rfl) ⟨1051217, by rfl⟩ : syracuseStep 1401623 = 2102435) B2102435
theorem B1041407 : Blo 271824 1041407 := bstep (se 1 (by rfl) ⟨781055, by rfl⟩ : syracuseStep 1041407 = 1562111) B1562111
theorem B615689 : Blo 271824 615689 := bstep (se 2 (by rfl) ⟨230883, by rfl⟩ : syracuseStep 615689 = 461767) B461767
theorem B23848339 : Blo 271824 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B617723 : Blo 271824 617723 := bstep (se 1 (by rfl) ⟨463292, by rfl⟩ : syracuseStep 617723 = 926585) B926585
theorem B9563603 : Blo 271824 9563603 := bstep (se 1 (by rfl) ⟨7172702, by rfl⟩ : syracuseStep 9563603 = 14345405) B14345405
theorem B585911 : Blo 271824 585911 := bstep (se 1 (by rfl) ⟨439433, by rfl⟩ : syracuseStep 585911 = 878867) B878867
theorem B586219 : Blo 271824 586219 := bstep (se 1 (by rfl) ⟨439664, by rfl⟩ : syracuseStep 586219 = 879329) B879329
theorem B1700423 : Blo 271824 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B1045295 : Blo 271824 1045295 := bstep (se 1 (by rfl) ⟨783971, by rfl⟩ : syracuseStep 1045295 = 1567943) B1567943
theorem B3109913 : Blo 271824 3109913 := bstep (se 2 (by rfl) ⟨1166217, by rfl⟩ : syracuseStep 3109913 = 2332435) B2332435
theorem B619631 : Blo 271824 619631 := bstep (se 1 (by rfl) ⟨464723, by rfl⟩ : syracuseStep 619631 = 929447) B929447
theorem B1111265 : Blo 271824 1111265 := bstep (se 2 (by rfl) ⟨416724, by rfl⟩ : syracuseStep 1111265 = 833449) B833449
theorem B620315 : Blo 271824 620315 := bstep (se 1 (by rfl) ⟨465236, by rfl⟩ : syracuseStep 620315 = 930473) B930473
theorem B882857 : Blo 271824 882857 := bstep (se 2 (by rfl) ⟨331071, by rfl⟩ : syracuseStep 882857 = 662143) B662143
theorem B784667 : Blo 271824 784667 := bstep (se 1 (by rfl) ⟨588500, by rfl⟩ : syracuseStep 784667 = 1177001) B1177001
theorem B689087 : Blo 271824 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B460039 : Blo 271824 460039 := bstep (se 1 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 460039 = 690059) B690059
theorem B1377647 : Blo 271824 1377647 := bstep (se 1 (by rfl) ⟨1033235, by rfl⟩ : syracuseStep 1377647 = 2066471) B2066471
theorem B461227 : Blo 271824 461227 := bstep (se 1 (by rfl) ⟨345920, by rfl⟩ : syracuseStep 461227 = 691841) B691841
theorem B4688927 : Blo 271824 4688927 := bstep (se 1 (by rfl) ⟨3516695, by rfl⟩ : syracuseStep 4688927 = 7033391) B7033391
theorem B1379591 : Blo 271824 1379591 := bstep (se 1 (by rfl) ⟨1034693, by rfl⟩ : syracuseStep 1379591 = 2069387) B2069387
theorem B921023 : Blo 271824 921023 := bstep (se 1 (by rfl) ⟨690767, by rfl⟩ : syracuseStep 921023 = 1381535) B1381535
theorem B463529 : Blo 271824 463529 := bstep (se 2 (by rfl) ⟨173823, by rfl⟩ : syracuseStep 463529 = 347647) B347647
theorem B1316225 : Blo 271824 1316225 := bstep (se 2 (by rfl) ⟨493584, by rfl⟩ : syracuseStep 1316225 = 987169) B987169
theorem B923183 : Blo 271824 923183 := bstep (se 1 (by rfl) ⟨692387, by rfl⟩ : syracuseStep 923183 = 1384775) B1384775
theorem B5019371 : Blo 271824 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B694271 : Blo 271824 694271 := bstep (se 1 (by rfl) ⟨520703, by rfl⟩ : syracuseStep 694271 = 1041407) B1041407
theorem B2234627 : Blo 271824 2234627 := bstep (se 1 (by rfl) ⟨1675970, by rfl⟩ : syracuseStep 2234627 = 3351941) B3351941
theorem B924911 : Blo 271824 924911 := bstep (se 1 (by rfl) ⟨693683, by rfl⟩ : syracuseStep 924911 = 1387367) B1387367
theorem B696863 : Blo 271824 696863 := bstep (se 1 (by rfl) ⟨522647, by rfl⟩ : syracuseStep 696863 = 1045295) B1045295
theorem B2073275 : Blo 271824 2073275 := bstep (se 1 (by rfl) ⟨1554956, by rfl⟩ : syracuseStep 2073275 = 3109913) B3109913
theorem B25502941 : Blo 271824 25502941 := bstep (se 3 (by rfl) ⟨4781801, by rfl⟩ : syracuseStep 25502941 = 9563603) B9563603
theorem B927017 : Blo 271824 927017 := bstep (se 2 (by rfl) ⟨347631, by rfl⟩ : syracuseStep 927017 = 695263) B695263
theorem B271919 : Blo 271824 271919 := bstep (se 1 (by rfl) ⟨203939, by rfl⟩ : syracuseStep 271919 = 407879) B407879
theorem B273127 : Blo 271824 273127 := bstep (se 1 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 273127 = 409691) B409691
theorem B437275 : Blo 271824 437275 := bstep (se 1 (by rfl) ⟨327956, by rfl⟩ : syracuseStep 437275 = 655913) B655913
theorem B273435 : Blo 271824 273435 := bstep (se 1 (by rfl) ⟨205076, by rfl⟩ : syracuseStep 273435 = 410153) B410153
theorem B274175 : Blo 271824 274175 := bstep (se 1 (by rfl) ⟨205631, by rfl⟩ : syracuseStep 274175 = 411263) B411263
theorem B3321769 : Blo 271824 3321769 := bstep (se 2 (by rfl) ⟨1245663, by rfl⟩ : syracuseStep 3321769 = 2491327) B2491327
theorem B2338793 : Blo 271824 2338793 := bstep (se 2 (by rfl) ⟨877047, by rfl⟩ : syracuseStep 2338793 = 1754095) B1754095
theorem B2503007 : Blo 271824 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B307687 : Blo 271824 307687 := bstep (se 1 (by rfl) ⟨230765, by rfl⟩ : syracuseStep 307687 = 461531) B461531
theorem B31797785 : Blo 271824 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B275455 : Blo 271824 275455 := bstep (se 1 (by rfl) ⟨206591, by rfl⟩ : syracuseStep 275455 = 413183) B413183
theorem B275583 : Blo 271824 275583 := bstep (se 1 (by rfl) ⟨206687, by rfl⟩ : syracuseStep 275583 = 413375) B413375
theorem B1751377 : Blo 271824 1751377 := bstep (se 2 (by rfl) ⟨656766, by rfl⟩ : syracuseStep 1751377 = 1313533) B1313533
theorem B408047 : Blo 271824 408047 := bstep (se 1 (by rfl) ⟨306035, by rfl⟩ : syracuseStep 408047 = 612071) B612071
theorem B408827 : Blo 271824 408827 := bstep (se 1 (by rfl) ⟨306620, by rfl⟩ : syracuseStep 408827 = 613241) B613241
theorem B736951 : Blo 271824 736951 := bstep (se 1 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 736951 = 1105427) B1105427
theorem B3522437 : Blo 271824 3522437 := bstep (se 4 (by rfl) ⟨330228, by rfl⟩ : syracuseStep 3522437 = 660457) B660457
theorem B409655 : Blo 271824 409655 := bstep (se 1 (by rfl) ⟨307241, by rfl⟩ : syracuseStep 409655 = 614483) B614483
theorem B410111 : Blo 271824 410111 := bstep (se 1 (by rfl) ⟨307583, by rfl⟩ : syracuseStep 410111 = 615167) B615167
theorem B934415 : Blo 271824 934415 := bstep (se 1 (by rfl) ⟨700811, by rfl⟩ : syracuseStep 934415 = 1401623) B1401623
theorem B410459 : Blo 271824 410459 := bstep (se 1 (by rfl) ⟨307844, by rfl⟩ : syracuseStep 410459 = 615689) B615689
theorem B411401 : Blo 271824 411401 := bstep (se 2 (by rfl) ⟨154275, by rfl⟩ : syracuseStep 411401 = 308551) B308551
theorem B411689 : Blo 271824 411689 := bstep (se 2 (by rfl) ⟨154383, by rfl⟩ : syracuseStep 411689 = 308767) B308767
theorem B411815 : Blo 271824 411815 := bstep (se 1 (by rfl) ⟨308861, by rfl⟩ : syracuseStep 411815 = 617723) B617723
theorem B20040371 : Blo 271824 20040371 := bstep (se 1 (by rfl) ⟨15030278, by rfl⟩ : syracuseStep 20040371 = 30060557) B30060557
theorem B1133615 : Blo 271824 1133615 := bstep (se 1 (by rfl) ⟨850211, by rfl⟩ : syracuseStep 1133615 = 1700423) B1700423
theorem B2215295 : Blo 271824 2215295 := bstep (se 1 (by rfl) ⟨1661471, by rfl⟩ : syracuseStep 2215295 = 3322943) B3322943
theorem B413087 : Blo 271824 413087 := bstep (se 1 (by rfl) ⟨309815, by rfl⟩ : syracuseStep 413087 = 619631) B619631
theorem B740843 : Blo 271824 740843 := bstep (se 1 (by rfl) ⟨555632, by rfl⟩ : syracuseStep 740843 = 1111265) B1111265
theorem B413543 : Blo 271824 413543 := bstep (se 1 (by rfl) ⟨310157, by rfl⟩ : syracuseStep 413543 = 620315) B620315
theorem B1562429 : Blo 271824 1562429 := bstep (se 3 (by rfl) ⟨292955, by rfl⟩ : syracuseStep 1562429 = 585911) B585911
theorem B12114613 : Blo 271824 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B48061511 : Blo 271824 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B2219183 : Blo 271824 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B516071 : Blo 271824 516071 := bstep (se 1 (by rfl) ⟨387053, by rfl⟩ : syracuseStep 516071 = 774107) B774107
theorem B582623 : Blo 271824 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B779291 : Blo 271824 779291 := bstep (se 1 (by rfl) ⟨584468, by rfl⟩ : syracuseStep 779291 = 1168937) B1168937
theorem B1107503 : Blo 271824 1107503 := bstep (se 1 (by rfl) ⟨830627, by rfl⟩ : syracuseStep 1107503 = 1661255) B1661255
theorem B19098661 : Blo 271824 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B2354285 : Blo 271824 2354285 := bstep (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) B882857
theorem B617633 : Blo 271824 617633 := bstep (se 2 (by rfl) ⟨231612, by rfl⟩ : syracuseStep 617633 = 463225) B463225
theorem B781625 : Blo 271824 781625 := bstep (se 2 (by rfl) ⟨293109, by rfl⟩ : syracuseStep 781625 = 586219) B586219
theorem B618407 : Blo 271824 618407 := bstep (se 1 (by rfl) ⟨463805, by rfl⟩ : syracuseStep 618407 = 927611) B927611
theorem B22903631 : Blo 271824 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B523111 : Blo 271824 523111 := bstep (se 1 (by rfl) ⟨392333, by rfl⟩ : syracuseStep 523111 = 784667) B784667
theorem B588713 : Blo 271824 588713 := bstep (se 2 (by rfl) ⟨220767, by rfl⟩ : syracuseStep 588713 = 441535) B441535
theorem B622943 : Blo 271824 622943 := bstep (se 1 (by rfl) ⟨467207, by rfl⟩ : syracuseStep 622943 = 934415) B934415
theorem B459391 : Blo 271824 459391 := bstep (se 1 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 459391 = 689087) B689087
theorem B918431 : Blo 271824 918431 := bstep (se 1 (by rfl) ⟨688823, by rfl⟩ : syracuseStep 918431 = 1377647) B1377647
theorem B755743 : Blo 271824 755743 := bstep (se 1 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 755743 = 1133615) B1133615
theorem B919727 : Blo 271824 919727 := bstep (se 1 (by rfl) ⟨689795, by rfl⟩ : syracuseStep 919727 = 1379591) B1379591
theorem B1476863 : Blo 271824 1476863 := bstep (se 1 (by rfl) ⟨1107647, by rfl⟩ : syracuseStep 1476863 = 2215295) B2215295
theorem B493895 : Blo 271824 493895 := bstep (se 1 (by rfl) ⟨370421, by rfl⟩ : syracuseStep 493895 = 740843) B740843
theorem B3346247 : Blo 271824 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B462847 : Blo 271824 462847 := bstep (se 1 (by rfl) ⟨347135, by rfl⟩ : syracuseStep 462847 = 694271) B694271
theorem B25464881 : Blo 271824 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B1479455 : Blo 271824 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B4429025 : Blo 271824 4429025 := bstep (se 2 (by rfl) ⟨1660884, by rfl⟩ : syracuseStep 4429025 = 3321769) B3321769
theorem B464575 : Blo 271824 464575 := bstep (se 1 (by rfl) ⟨348431, by rfl⟩ : syracuseStep 464575 = 696863) B696863
theorem B1382183 : Blo 271824 1382183 := bstep (se 1 (by rfl) ⟨1036637, by rfl⟩ : syracuseStep 1382183 = 2073275) B2073275
theorem B2335169 : Blo 271824 2335169 := bstep (se 2 (by rfl) ⟨875688, by rfl⟩ : syracuseStep 2335169 = 1751377) B1751377
theorem B697481 : Blo 271824 697481 := bstep (se 2 (by rfl) ⟨261555, by rfl⟩ : syracuseStep 697481 = 523111) B523111
theorem B272031 : Blo 271824 272031 := bstep (se 1 (by rfl) ⟨204023, by rfl⟩ : syracuseStep 272031 = 408047) B408047
theorem B272551 : Blo 271824 272551 := bstep (se 1 (by rfl) ⟨204413, by rfl⟩ : syracuseStep 272551 = 408827) B408827
theorem B273103 : Blo 271824 273103 := bstep (se 1 (by rfl) ⟨204827, by rfl⟩ : syracuseStep 273103 = 409655) B409655
theorem B273407 : Blo 271824 273407 := bstep (se 1 (by rfl) ⟨205055, by rfl⟩ : syracuseStep 273407 = 410111) B410111
theorem B273639 : Blo 271824 273639 := bstep (se 1 (by rfl) ⟨205229, by rfl⟩ : syracuseStep 273639 = 410459) B410459
theorem B274267 : Blo 271824 274267 := bstep (se 1 (by rfl) ⟨205700, by rfl⟩ : syracuseStep 274267 = 411401) B411401
theorem B274459 : Blo 271824 274459 := bstep (se 1 (by rfl) ⟨205844, by rfl⟩ : syracuseStep 274459 = 411689) B411689
theorem B274543 : Blo 271824 274543 := bstep (se 1 (by rfl) ⟨205907, by rfl⟩ : syracuseStep 274543 = 411815) B411815
theorem B3125951 : Blo 271824 3125951 := bstep (se 1 (by rfl) ⟨2344463, by rfl⟩ : syracuseStep 3125951 = 4688927) B4688927
theorem B275391 : Blo 271824 275391 := bstep (se 1 (by rfl) ⟨206543, by rfl⟩ : syracuseStep 275391 = 413087) B413087
theorem B275695 : Blo 271824 275695 := bstep (se 1 (by rfl) ⟨206771, by rfl⟩ : syracuseStep 275695 = 413543) B413543
theorem B309019 : Blo 271824 309019 := bstep (se 1 (by rfl) ⟨231764, by rfl⟩ : syracuseStep 309019 = 463529) B463529
theorem B1489751 : Blo 271824 1489751 := bstep (se 1 (by rfl) ⟨1117313, by rfl⟩ : syracuseStep 1489751 = 2234627) B2234627
theorem B410249 : Blo 271824 410249 := bstep (se 2 (by rfl) ⟨153843, by rfl⟩ : syracuseStep 410249 = 307687) B307687
theorem B738335 : Blo 271824 738335 := bstep (se 1 (by rfl) ⟨553751, by rfl⟩ : syracuseStep 738335 = 1107503) B1107503
theorem B411755 : Blo 271824 411755 := bstep (se 1 (by rfl) ⟨308816, by rfl⟩ : syracuseStep 411755 = 617633) B617633
theorem B412271 : Blo 271824 412271 := bstep (se 1 (by rfl) ⟨309203, by rfl⟩ : syracuseStep 412271 = 618407) B618407
theorem B1559195 : Blo 271824 1559195 := bstep (se 1 (by rfl) ⟨1169396, by rfl⟩ : syracuseStep 1559195 = 2338793) B2338793
theorem B6278093 : Blo 271824 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B2348291 : Blo 271824 2348291 := bstep (se 1 (by rfl) ⟨1761218, by rfl⟩ : syracuseStep 2348291 = 3522437) B3522437
theorem B34003921 : Blo 271824 34003921 := bstep (se 2 (by rfl) ⟨12751470, by rfl⟩ : syracuseStep 34003921 = 25502941) B25502941
theorem B613385 : Blo 271824 613385 := bstep (se 2 (by rfl) ⟨230019, by rfl⟩ : syracuseStep 613385 = 460039) B460039
theorem B13360247 : Blo 271824 13360247 := bstep (se 1 (by rfl) ⟨10020185, by rfl⟩ : syracuseStep 13360247 = 20040371) B20040371
theorem B614015 : Blo 271824 614015 := bstep (se 1 (by rfl) ⟨460511, by rfl⟩ : syracuseStep 614015 = 921023) B921023
theorem B614969 : Blo 271824 614969 := bstep (se 2 (by rfl) ⟨230613, by rfl⟩ : syracuseStep 614969 = 461227) B461227
theorem B877483 : Blo 271824 877483 := bstep (se 1 (by rfl) ⟨658112, by rfl⟩ : syracuseStep 877483 = 1316225) B1316225
theorem B615455 : Blo 271824 615455 := bstep (se 1 (by rfl) ⟨461591, by rfl⟩ : syracuseStep 615455 = 923183) B923183
theorem B1041619 : Blo 271824 1041619 := bstep (se 1 (by rfl) ⟨781214, by rfl⟩ : syracuseStep 1041619 = 1562429) B1562429
theorem B583033 : Blo 271824 583033 := bstep (se 2 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 583033 = 437275) B437275
theorem B32041007 : Blo 271824 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B616607 : Blo 271824 616607 := bstep (se 1 (by rfl) ⟨462455, by rfl⟩ : syracuseStep 616607 = 924911) B924911
theorem B388415 : Blo 271824 388415 := bstep (se 1 (by rfl) ⟨291311, by rfl⟩ : syracuseStep 388415 = 582623) B582623
theorem B519527 : Blo 271824 519527 := bstep (se 1 (by rfl) ⟨389645, by rfl⟩ : syracuseStep 519527 = 779291) B779291
theorem B618011 : Blo 271824 618011 := bstep (se 1 (by rfl) ⟨463508, by rfl⟩ : syracuseStep 618011 = 927017) B927017
theorem B521083 : Blo 271824 521083 := bstep (se 1 (by rfl) ⟨390812, by rfl⟩ : syracuseStep 521083 = 781625) B781625
theorem B1569901 : Blo 271824 1569901 := bstep (se 3 (by rfl) ⟨294356, by rfl⟩ : syracuseStep 1569901 = 588713) B588713
theorem B1668671 : Blo 271824 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B21198523 : Blo 271824 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B16152817 : Blo 271824 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B15269087 : Blo 271824 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B982601 : Blo 271824 982601 := bstep (se 2 (by rfl) ⟨368475, by rfl⟩ : syracuseStep 982601 = 736951) B736951
theorem B1376189 : Blo 271824 1376189 := bstep (se 3 (by rfl) ⟨258035, by rfl⟩ : syracuseStep 1376189 = 516071) B516071
theorem B984575 : Blo 271824 984575 := bstep (se 1 (by rfl) ⟨738431, by rfl⟩ : syracuseStep 984575 = 1476863) B1476863
theorem B2230831 : Blo 271824 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B16976587 : Blo 271824 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B1968893 : Blo 271824 1968893 := bstep (se 3 (by rfl) ⟨369167, by rfl⟩ : syracuseStep 1968893 = 738335) B738335
theorem B986303 : Blo 271824 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B2952683 : Blo 271824 2952683 := bstep (se 1 (by rfl) ⟨2214512, by rfl⟩ : syracuseStep 2952683 = 4429025) B4429025
theorem B921455 : Blo 271824 921455 := bstep (se 1 (by rfl) ⟨691091, by rfl⟩ : syracuseStep 921455 = 1382183) B1382183
theorem B464987 : Blo 271824 464987 := bstep (se 1 (by rfl) ⟨348740, by rfl⟩ : syracuseStep 464987 = 697481) B697481
theorem B1317053 : Blo 271824 1317053 := bstep (se 3 (by rfl) ⟨246947, by rfl⟩ : syracuseStep 1317053 = 493895) B493895
theorem B694777 : Blo 271824 694777 := bstep (se 2 (by rfl) ⟨260541, by rfl⟩ : syracuseStep 694777 = 521083) B521083
theorem B21537089 : Blo 271824 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B993167 : Blo 271824 993167 := bstep (se 1 (by rfl) ⟨744875, by rfl⟩ : syracuseStep 993167 = 1489751) B1489751
theorem B273499 : Blo 271824 273499 := bstep (se 1 (by rfl) ⟨205124, by rfl⟩ : syracuseStep 273499 = 410249) B410249
theorem B274503 : Blo 271824 274503 := bstep (se 1 (by rfl) ⟨205877, by rfl⟩ : syracuseStep 274503 = 411755) B411755
theorem B1388825 : Blo 271824 1388825 := bstep (se 2 (by rfl) ⟨520809, by rfl⟩ : syracuseStep 1388825 = 1041619) B1041619
theorem B274847 : Blo 271824 274847 := bstep (se 1 (by rfl) ⟨206135, by rfl⟩ : syracuseStep 274847 = 412271) B412271
theorem B408923 : Blo 271824 408923 := bstep (se 1 (by rfl) ⟨306692, by rfl⟩ : syracuseStep 408923 = 613385) B613385
theorem B409343 : Blo 271824 409343 := bstep (se 1 (by rfl) ⟨307007, by rfl⟩ : syracuseStep 409343 = 614015) B614015
theorem B1556779 : Blo 271824 1556779 := bstep (se 1 (by rfl) ⟨1167584, by rfl⟩ : syracuseStep 1556779 = 2335169) B2335169
theorem B409979 : Blo 271824 409979 := bstep (se 1 (by rfl) ⟨307484, by rfl⟩ : syracuseStep 409979 = 614969) B614969
theorem B410303 : Blo 271824 410303 := bstep (se 1 (by rfl) ⟨307727, by rfl⟩ : syracuseStep 410303 = 615455) B615455
theorem B411071 : Blo 271824 411071 := bstep (se 1 (by rfl) ⟨308303, by rfl⟩ : syracuseStep 411071 = 616607) B616607
theorem B346351 : Blo 271824 346351 := bstep (se 1 (by rfl) ⟨259763, by rfl⟩ : syracuseStep 346351 = 519527) B519527
theorem B28264697 : Blo 271824 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B412007 : Blo 271824 412007 := bstep (se 1 (by rfl) ⟨309005, by rfl⟩ : syracuseStep 412007 = 618011) B618011
theorem B412025 : Blo 271824 412025 := bstep (se 2 (by rfl) ⟨154509, by rfl⟩ : syracuseStep 412025 = 309019) B309019
theorem B2083967 : Blo 271824 2083967 := bstep (se 1 (by rfl) ⟨1562975, by rfl⟩ : syracuseStep 2083967 = 3125951) B3125951
theorem B40717565 : Blo 271824 40717565 := bstep (se 3 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 40717565 = 15269087) B15269087
theorem B1035773 : Blo 271824 1035773 := bstep (se 3 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 1035773 = 388415) B388415
theorem B45338561 : Blo 271824 45338561 := bstep (se 2 (by rfl) ⟨17001960, by rfl⟩ : syracuseStep 45338561 = 34003921) B34003921
theorem B415295 : Blo 271824 415295 := bstep (se 1 (by rfl) ⟨311471, by rfl⟩ : syracuseStep 415295 = 622943) B622943
theorem B612287 : Blo 271824 612287 := bstep (se 1 (by rfl) ⟨459215, by rfl⟩ : syracuseStep 612287 = 918431) B918431
theorem B612521 : Blo 271824 612521 := bstep (se 2 (by rfl) ⟨229695, by rfl⟩ : syracuseStep 612521 = 459391) B459391
theorem B1169977 : Blo 271824 1169977 := bstep (se 2 (by rfl) ⟨438741, by rfl⟩ : syracuseStep 1169977 = 877483) B877483
theorem B613151 : Blo 271824 613151 := bstep (se 1 (by rfl) ⟨459863, by rfl⟩ : syracuseStep 613151 = 919727) B919727
theorem B1039463 : Blo 271824 1039463 := bstep (se 1 (by rfl) ⟨779597, by rfl⟩ : syracuseStep 1039463 = 1559195) B1559195
theorem B777377 : Blo 271824 777377 := bstep (se 2 (by rfl) ⟨291516, by rfl⟩ : syracuseStep 777377 = 583033) B583033
theorem B4185395 : Blo 271824 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B1007657 : Blo 271824 1007657 := bstep (se 2 (by rfl) ⟨377871, by rfl⟩ : syracuseStep 1007657 = 755743) B755743
theorem B1565527 : Blo 271824 1565527 := bstep (se 1 (by rfl) ⟨1174145, by rfl⟩ : syracuseStep 1565527 = 2348291) B2348291
theorem B8906831 : Blo 271824 8906831 := bstep (se 1 (by rfl) ⟨6680123, by rfl⟩ : syracuseStep 8906831 = 13360247) B13360247
theorem B617129 : Blo 271824 617129 := bstep (se 2 (by rfl) ⟨231423, by rfl⟩ : syracuseStep 617129 = 462847) B462847
theorem B21360671 : Blo 271824 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B2093201 : Blo 271824 2093201 := bstep (se 2 (by rfl) ⟨784950, by rfl⟩ : syracuseStep 2093201 = 1569901) B1569901
theorem B619433 : Blo 271824 619433 := bstep (se 2 (by rfl) ⟨232287, by rfl⟩ : syracuseStep 619433 = 464575) B464575
theorem B1112447 : Blo 271824 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B655067 : Blo 271824 655067 := bstep (se 1 (by rfl) ⟨491300, by rfl⟩ : syracuseStep 655067 = 982601) B982601
theorem B917459 : Blo 271824 917459 := bstep (se 1 (by rfl) ⟨688094, by rfl⟩ : syracuseStep 917459 = 1376189) B1376189
theorem B656383 : Blo 271824 656383 := bstep (se 1 (by rfl) ⟨492287, by rfl⟩ : syracuseStep 656383 = 984575) B984575
theorem B18843131 : Blo 271824 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B1312595 : Blo 271824 1312595 := bstep (se 1 (by rfl) ⟨984446, by rfl⟩ : syracuseStep 1312595 = 1968893) B1968893
theorem B1968455 : Blo 271824 1968455 := bstep (se 1 (by rfl) ⟨1476341, by rfl⟩ : syracuseStep 1968455 = 2952683) B2952683
theorem B690515 : Blo 271824 690515 := bstep (se 1 (by rfl) ⟨517886, by rfl⟩ : syracuseStep 690515 = 1035773) B1035773
theorem B461801 : Blo 271824 461801 := bstep (se 2 (by rfl) ⟨173175, by rfl⟩ : syracuseStep 461801 = 346351) B346351
theorem B692975 : Blo 271824 692975 := bstep (se 1 (by rfl) ⟨519731, by rfl⟩ : syracuseStep 692975 = 1039463) B1039463
theorem B2790263 : Blo 271824 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B14358059 : Blo 271824 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B662111 : Blo 271824 662111 := bstep (se 1 (by rfl) ⟨496583, by rfl⟩ : syracuseStep 662111 = 993167) B993167
theorem B5937887 : Blo 271824 5937887 := bstep (se 1 (by rfl) ⟨4453415, by rfl⟩ : syracuseStep 5937887 = 8906831) B8906831
theorem B925883 : Blo 271824 925883 := bstep (se 1 (by rfl) ⟨694412, by rfl⟩ : syracuseStep 925883 = 1388825) B1388825
theorem B2630141 : Blo 271824 2630141 := bstep (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) B986303
theorem B926369 : Blo 271824 926369 := bstep (se 2 (by rfl) ⟨347388, by rfl⟩ : syracuseStep 926369 = 694777) B694777
theorem B1746845 : Blo 271824 1746845 := bstep (se 3 (by rfl) ⟨327533, by rfl⟩ : syracuseStep 1746845 = 655067) B655067
theorem B272615 : Blo 271824 272615 := bstep (se 1 (by rfl) ⟨204461, by rfl⟩ : syracuseStep 272615 = 408923) B408923
theorem B272895 : Blo 271824 272895 := bstep (se 1 (by rfl) ⟨204671, by rfl⟩ : syracuseStep 272895 = 409343) B409343
theorem B273319 : Blo 271824 273319 := bstep (se 1 (by rfl) ⟨204989, by rfl⟩ : syracuseStep 273319 = 409979) B409979
theorem B2075705 : Blo 271824 2075705 := bstep (se 2 (by rfl) ⟨778389, by rfl⟩ : syracuseStep 2075705 = 1556779) B1556779
theorem B273535 : Blo 271824 273535 := bstep (se 1 (by rfl) ⟨205151, by rfl⟩ : syracuseStep 273535 = 410303) B410303
theorem B274047 : Blo 271824 274047 := bstep (se 1 (by rfl) ⟨205535, by rfl⟩ : syracuseStep 274047 = 411071) B411071
theorem B274671 : Blo 271824 274671 := bstep (se 1 (by rfl) ⟨206003, by rfl⟩ : syracuseStep 274671 = 412007) B412007
theorem B274683 : Blo 271824 274683 := bstep (se 1 (by rfl) ⟨206012, by rfl⟩ : syracuseStep 274683 = 412025) B412025
theorem B1389311 : Blo 271824 1389311 := bstep (se 1 (by rfl) ⟨1041983, by rfl⟩ : syracuseStep 1389311 = 2083967) B2083967
theorem B27145043 : Blo 271824 27145043 := bstep (se 1 (by rfl) ⟨20358782, by rfl⟩ : syracuseStep 27145043 = 40717565) B40717565
theorem B30225707 : Blo 271824 30225707 := bstep (se 1 (by rfl) ⟨22669280, by rfl⟩ : syracuseStep 30225707 = 45338561) B45338561
theorem B276863 : Blo 271824 276863 := bstep (se 1 (by rfl) ⟨207647, by rfl⟩ : syracuseStep 276863 = 415295) B415295
theorem B408191 : Blo 271824 408191 := bstep (se 1 (by rfl) ⟨306143, by rfl⟩ : syracuseStep 408191 = 612287) B612287
theorem B309991 : Blo 271824 309991 := bstep (se 1 (by rfl) ⟨232493, by rfl⟩ : syracuseStep 309991 = 464987) B464987
theorem B408347 : Blo 271824 408347 := bstep (se 1 (by rfl) ⟨306260, by rfl⟩ : syracuseStep 408347 = 612521) B612521
theorem B408767 : Blo 271824 408767 := bstep (se 1 (by rfl) ⟨306575, by rfl⟩ : syracuseStep 408767 = 613151) B613151
theorem B671771 : Blo 271824 671771 := bstep (se 1 (by rfl) ⟨503828, by rfl⟩ : syracuseStep 671771 = 1007657) B1007657
theorem B411419 : Blo 271824 411419 := bstep (se 1 (by rfl) ⟨308564, by rfl⟩ : syracuseStep 411419 = 617129) B617129
theorem B14240447 : Blo 271824 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B1395467 : Blo 271824 1395467 := bstep (se 1 (by rfl) ⟨1046600, by rfl⟩ : syracuseStep 1395467 = 2093201) B2093201
theorem B412955 : Blo 271824 412955 := bstep (se 1 (by rfl) ⟨309716, by rfl⟩ : syracuseStep 412955 = 619433) B619433
theorem B1559969 : Blo 271824 1559969 := bstep (se 2 (by rfl) ⟨584988, by rfl⟩ : syracuseStep 1559969 = 1169977) B1169977
theorem B741631 : Blo 271824 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B611639 : Blo 271824 611639 := bstep (se 1 (by rfl) ⟨458729, by rfl⟩ : syracuseStep 611639 = 917459) B917459
theorem B2087369 : Blo 271824 2087369 := bstep (se 2 (by rfl) ⟨782763, by rfl⟩ : syracuseStep 2087369 = 1565527) B1565527
theorem B614303 : Blo 271824 614303 := bstep (se 1 (by rfl) ⟨460727, by rfl⟩ : syracuseStep 614303 = 921455) B921455
theorem B2974441 : Blo 271824 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B22635449 : Blo 271824 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B878035 : Blo 271824 878035 := bstep (se 1 (by rfl) ⟨658526, by rfl⟩ : syracuseStep 878035 = 1317053) B1317053
theorem B518251 : Blo 271824 518251 := bstep (se 1 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 518251 = 777377) B777377
theorem B3965921 : Blo 271824 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B1312303 : Blo 271824 1312303 := bstep (se 1 (by rfl) ⟨984227, by rfl⟩ : syracuseStep 1312303 = 1968455) B1968455
theorem B460343 : Blo 271824 460343 := bstep (se 1 (by rfl) ⟨345257, by rfl⟩ : syracuseStep 460343 = 690515) B690515
theorem B691001 : Blo 271824 691001 := bstep (se 2 (by rfl) ⟨259125, by rfl⟩ : syracuseStep 691001 = 518251) B518251
theorem B461983 : Blo 271824 461983 := bstep (se 1 (by rfl) ⟨346487, by rfl⟩ : syracuseStep 461983 = 692975) B692975
theorem B9572039 : Blo 271824 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B988841 : Blo 271824 988841 := bstep (se 2 (by rfl) ⟨370815, by rfl⟩ : syracuseStep 988841 = 741631) B741631
theorem B1383803 : Blo 271824 1383803 := bstep (se 1 (by rfl) ⟨1037852, by rfl⟩ : syracuseStep 1383803 = 2075705) B2075705
theorem B926207 : Blo 271824 926207 := bstep (se 1 (by rfl) ⟨694655, by rfl⟩ : syracuseStep 926207 = 1389311) B1389311
theorem B18096695 : Blo 271824 18096695 := bstep (se 1 (by rfl) ⟨13572521, by rfl⟩ : syracuseStep 18096695 = 27145043) B27145043
theorem B272127 : Blo 271824 272127 := bstep (se 1 (by rfl) ⟨204095, by rfl⟩ : syracuseStep 272127 = 408191) B408191
theorem B272231 : Blo 271824 272231 := bstep (se 1 (by rfl) ⟨204173, by rfl⟩ : syracuseStep 272231 = 408347) B408347
theorem B272511 : Blo 271824 272511 := bstep (se 1 (by rfl) ⟨204383, by rfl⟩ : syracuseStep 272511 = 408767) B408767
theorem B12562087 : Blo 271824 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B274279 : Blo 271824 274279 := bstep (se 1 (by rfl) ⟨205709, by rfl⟩ : syracuseStep 274279 = 411419) B411419
theorem B930311 : Blo 271824 930311 := bstep (se 1 (by rfl) ⟨697733, by rfl⟩ : syracuseStep 930311 = 1395467) B1395467
theorem B307867 : Blo 271824 307867 := bstep (se 1 (by rfl) ⟨230900, by rfl⟩ : syracuseStep 307867 = 461801) B461801
theorem B275303 : Blo 271824 275303 := bstep (se 1 (by rfl) ⟨206477, by rfl⟩ : syracuseStep 275303 = 412955) B412955
theorem B407759 : Blo 271824 407759 := bstep (se 1 (by rfl) ⟨305819, by rfl⟩ : syracuseStep 407759 = 611639) B611639
theorem B1391579 : Blo 271824 1391579 := bstep (se 1 (by rfl) ⟨1043684, by rfl⟩ : syracuseStep 1391579 = 2087369) B2087369
theorem B441407 : Blo 271824 441407 := bstep (se 1 (by rfl) ⟨331055, by rfl⟩ : syracuseStep 441407 = 662111) B662111
theorem B409535 : Blo 271824 409535 := bstep (se 1 (by rfl) ⟨307151, by rfl⟩ : syracuseStep 409535 = 614303) B614303
theorem B1753427 : Blo 271824 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B15090299 : Blo 271824 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B738301 : Blo 271824 738301 := bstep (se 3 (by rfl) ⟨138431, by rfl⟩ : syracuseStep 738301 = 276863) B276863
theorem B1164563 : Blo 271824 1164563 := bstep (se 1 (by rfl) ⟨873422, by rfl⟩ : syracuseStep 1164563 = 1746845) B1746845
theorem B413321 : Blo 271824 413321 := bstep (se 2 (by rfl) ⟨154995, by rfl⟩ : syracuseStep 413321 = 309991) B309991
theorem B1791389 : Blo 271824 1791389 := bstep (se 3 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 1791389 = 671771) B671771
theorem B875063 : Blo 271824 875063 := bstep (se 1 (by rfl) ⟨656297, by rfl⟩ : syracuseStep 875063 = 1312595) B1312595
theorem B875177 : Blo 271824 875177 := bstep (se 2 (by rfl) ⟨328191, by rfl⟩ : syracuseStep 875177 = 656383) B656383
theorem B9493631 : Blo 271824 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B1170713 : Blo 271824 1170713 := bstep (se 2 (by rfl) ⟨439017, by rfl⟩ : syracuseStep 1170713 = 878035) B878035
theorem B1039979 : Blo 271824 1039979 := bstep (se 1 (by rfl) ⟨779984, by rfl⟩ : syracuseStep 1039979 = 1559969) B1559969
theorem B1860175 : Blo 271824 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B3958591 : Blo 271824 3958591 := bstep (se 1 (by rfl) ⟨2968943, by rfl⟩ : syracuseStep 3958591 = 5937887) B5937887
theorem B617255 : Blo 271824 617255 := bstep (se 1 (by rfl) ⟨462941, by rfl⟩ : syracuseStep 617255 = 925883) B925883
theorem B617579 : Blo 271824 617579 := bstep (se 1 (by rfl) ⟨463184, by rfl⟩ : syracuseStep 617579 = 926369) B926369
theorem B20150471 : Blo 271824 20150471 := bstep (se 1 (by rfl) ⟨15112853, by rfl⟩ : syracuseStep 20150471 = 30225707) B30225707
theorem B10060199 : Blo 271824 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B984401 : Blo 271824 984401 := bstep (se 2 (by rfl) ⟨369150, by rfl⟩ : syracuseStep 984401 = 738301) B738301
theorem B460667 : Blo 271824 460667 := bstep (se 1 (by rfl) ⟨345500, by rfl⟩ : syracuseStep 460667 = 691001) B691001
theorem B5278121 : Blo 271824 5278121 := bstep (se 2 (by rfl) ⟨1979295, by rfl⟩ : syracuseStep 5278121 = 3958591) B3958591
theorem B659227 : Blo 271824 659227 := bstep (se 1 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 659227 = 988841) B988841
theorem B6329087 : Blo 271824 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B16749449 : Blo 271824 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B922535 : Blo 271824 922535 := bstep (se 1 (by rfl) ⟨691901, by rfl⟩ : syracuseStep 922535 = 1383803) B1383803
theorem B693319 : Blo 271824 693319 := bstep (se 1 (by rfl) ⟨519989, by rfl⟩ : syracuseStep 693319 = 1039979) B1039979
theorem B12064463 : Blo 271824 12064463 := bstep (se 1 (by rfl) ⟨9048347, by rfl⟩ : syracuseStep 12064463 = 18096695) B18096695
theorem B271839 : Blo 271824 271839 := bstep (se 1 (by rfl) ⟨203879, by rfl⟩ : syracuseStep 271839 = 407759) B407759
theorem B927719 : Blo 271824 927719 := bstep (se 1 (by rfl) ⟨695789, by rfl⟩ : syracuseStep 927719 = 1391579) B1391579
theorem B273023 : Blo 271824 273023 := bstep (se 1 (by rfl) ⟨204767, by rfl⟩ : syracuseStep 273023 = 409535) B409535
theorem B306895 : Blo 271824 306895 := bstep (se 1 (by rfl) ⟨230171, by rfl⟩ : syracuseStep 306895 = 460343) B460343
theorem B1749737 : Blo 271824 1749737 := bstep (se 2 (by rfl) ⟨656151, by rfl⟩ : syracuseStep 1749737 = 1312303) B1312303
theorem B275547 : Blo 271824 275547 := bstep (se 1 (by rfl) ⟨206660, by rfl⟩ : syracuseStep 275547 = 413321) B413321
theorem B1194259 : Blo 271824 1194259 := bstep (se 1 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 1194259 = 1791389) B1791389
theorem B410489 : Blo 271824 410489 := bstep (se 2 (by rfl) ⟨153933, by rfl⟩ : syracuseStep 410489 = 307867) B307867
theorem B411503 : Blo 271824 411503 := bstep (se 1 (by rfl) ⟨308627, by rfl⟩ : syracuseStep 411503 = 617255) B617255
theorem B411719 : Blo 271824 411719 := bstep (se 1 (by rfl) ⟨308789, by rfl⟩ : syracuseStep 411719 = 617579) B617579
theorem B2643947 : Blo 271824 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B2480233 : Blo 271824 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B776375 : Blo 271824 776375 := bstep (se 1 (by rfl) ⟨582281, by rfl⟩ : syracuseStep 776375 = 1164563) B1164563
theorem B4675805 : Blo 271824 4675805 := bstep (se 3 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 4675805 = 1753427) B1753427
theorem B6381359 : Blo 271824 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B615977 : Blo 271824 615977 := bstep (se 2 (by rfl) ⟨230991, by rfl⟩ : syracuseStep 615977 = 461983) B461983
theorem B583375 : Blo 271824 583375 := bstep (se 1 (by rfl) ⟨437531, by rfl⟩ : syracuseStep 583375 = 875063) B875063
theorem B583451 : Blo 271824 583451 := bstep (se 1 (by rfl) ⟨437588, by rfl⟩ : syracuseStep 583451 = 875177) B875177
theorem B780475 : Blo 271824 780475 := bstep (se 1 (by rfl) ⟨585356, by rfl⟩ : syracuseStep 780475 = 1170713) B1170713
theorem B617471 : Blo 271824 617471 := bstep (se 1 (by rfl) ⟨463103, by rfl⟩ : syracuseStep 617471 = 926207) B926207
theorem B1177085 : Blo 271824 1177085 := bstep (se 3 (by rfl) ⟨220703, by rfl⟩ : syracuseStep 1177085 = 441407) B441407
theorem B620207 : Blo 271824 620207 := bstep (se 1 (by rfl) ⟨465155, by rfl⟩ : syracuseStep 620207 = 930311) B930311
theorem B13433647 : Blo 271824 13433647 := bstep (se 1 (by rfl) ⟨10075235, by rfl⟩ : syracuseStep 13433647 = 20150471) B20150471
theorem B656267 : Blo 271824 656267 := bstep (se 1 (by rfl) ⟨492200, by rfl⟩ : syracuseStep 656267 = 984401) B984401
theorem B3117203 : Blo 271824 3117203 := bstep (se 1 (by rfl) ⟨2337902, by rfl⟩ : syracuseStep 3117203 = 4675805) B4675805
theorem B924425 : Blo 271824 924425 := bstep (se 2 (by rfl) ⟨346659, by rfl⟩ : syracuseStep 924425 = 693319) B693319
theorem B273659 : Blo 271824 273659 := bstep (se 1 (by rfl) ⟨205244, by rfl⟩ : syracuseStep 273659 = 410489) B410489
theorem B274335 : Blo 271824 274335 := bstep (se 1 (by rfl) ⟨205751, by rfl⟩ : syracuseStep 274335 = 411503) B411503
theorem B307111 : Blo 271824 307111 := bstep (se 1 (by rfl) ⟨230333, by rfl⟩ : syracuseStep 307111 = 460667) B460667
theorem B274479 : Blo 271824 274479 := bstep (se 1 (by rfl) ⟨205859, by rfl⟩ : syracuseStep 274479 = 411719) B411719
theorem B3518747 : Blo 271824 3518747 := bstep (se 1 (by rfl) ⟨2639060, by rfl⟩ : syracuseStep 3518747 = 5278121) B5278121
theorem B8042975 : Blo 271824 8042975 := bstep (se 1 (by rfl) ⟨6032231, by rfl⟩ : syracuseStep 8042975 = 12064463) B12064463
theorem B409193 : Blo 271824 409193 := bstep (se 2 (by rfl) ⟨153447, by rfl⟩ : syracuseStep 409193 = 306895) B306895
theorem B410651 : Blo 271824 410651 := bstep (se 1 (by rfl) ⟨307988, by rfl⟩ : syracuseStep 410651 = 615977) B615977
theorem B411647 : Blo 271824 411647 := bstep (se 1 (by rfl) ⟨308735, by rfl⟩ : syracuseStep 411647 = 617471) B617471
theorem B1592345 : Blo 271824 1592345 := bstep (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) B1194259
theorem B1166491 : Blo 271824 1166491 := bstep (se 1 (by rfl) ⟨874868, by rfl⟩ : syracuseStep 1166491 = 1749737) B1749737
theorem B17911529 : Blo 271824 17911529 := bstep (se 2 (by rfl) ⟨6716823, by rfl⟩ : syracuseStep 17911529 = 13433647) B13433647
theorem B413471 : Blo 271824 413471 := bstep (se 1 (by rfl) ⟨310103, by rfl⟩ : syracuseStep 413471 = 620207) B620207
theorem B6706799 : Blo 271824 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B777833 : Blo 271824 777833 := bstep (se 2 (by rfl) ⟨291687, by rfl⟩ : syracuseStep 777833 = 583375) B583375
theorem B1040633 : Blo 271824 1040633 := bstep (se 2 (by rfl) ⟨390237, by rfl⟩ : syracuseStep 1040633 = 780475) B780475
theorem B4219391 : Blo 271824 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B11166299 : Blo 271824 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B615023 : Blo 271824 615023 := bstep (se 1 (by rfl) ⟨461267, by rfl⟩ : syracuseStep 615023 = 922535) B922535
theorem B1762631 : Blo 271824 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B517583 : Blo 271824 517583 := bstep (se 1 (by rfl) ⟨388187, by rfl⟩ : syracuseStep 517583 = 776375) B776375
theorem B878969 : Blo 271824 878969 := bstep (se 2 (by rfl) ⟨329613, by rfl⟩ : syracuseStep 878969 = 659227) B659227
theorem B4254239 : Blo 271824 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B388967 : Blo 271824 388967 := bstep (se 1 (by rfl) ⟨291725, by rfl⟩ : syracuseStep 388967 = 583451) B583451
theorem B618479 : Blo 271824 618479 := bstep (se 1 (by rfl) ⟨463859, by rfl⟩ : syracuseStep 618479 = 927719) B927719
theorem B3306977 : Blo 271824 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B784723 : Blo 271824 784723 := bstep (se 1 (by rfl) ⟨588542, by rfl⟩ : syracuseStep 784723 = 1177085) B1177085
theorem B693755 : Blo 271824 693755 := bstep (se 1 (by rfl) ⟨520316, by rfl⟩ : syracuseStep 693755 = 1040633) B1040633
theorem B7444199 : Blo 271824 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B11344637 : Blo 271824 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B2204651 : Blo 271824 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B272795 : Blo 271824 272795 := bstep (se 1 (by rfl) ⟨204596, by rfl⟩ : syracuseStep 272795 = 409193) B409193
theorem B273767 : Blo 271824 273767 := bstep (se 1 (by rfl) ⟨205325, by rfl⟩ : syracuseStep 273767 = 410651) B410651
theorem B274431 : Blo 271824 274431 := bstep (se 1 (by rfl) ⟨205823, by rfl⟩ : syracuseStep 274431 = 411647) B411647
theorem B1750045 : Blo 271824 1750045 := bstep (se 3 (by rfl) ⟨328133, by rfl⟩ : syracuseStep 1750045 = 656267) B656267
theorem B11941019 : Blo 271824 11941019 := bstep (se 1 (by rfl) ⟨8955764, by rfl⟩ : syracuseStep 11941019 = 17911529) B17911529
theorem B275647 : Blo 271824 275647 := bstep (se 1 (by rfl) ⟨206735, by rfl⟩ : syracuseStep 275647 = 413471) B413471
theorem B2078135 : Blo 271824 2078135 := bstep (se 1 (by rfl) ⟨1558601, by rfl⟩ : syracuseStep 2078135 = 3117203) B3117203
theorem B4471199 : Blo 271824 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B1555321 : Blo 271824 1555321 := bstep (se 2 (by rfl) ⟨583245, by rfl⟩ : syracuseStep 1555321 = 1166491) B1166491
theorem B409481 : Blo 271824 409481 := bstep (se 2 (by rfl) ⟨153555, by rfl⟩ : syracuseStep 409481 = 307111) B307111
theorem B410015 : Blo 271824 410015 := bstep (se 1 (by rfl) ⟨307511, by rfl⟩ : syracuseStep 410015 = 615023) B615023
theorem B345055 : Blo 271824 345055 := bstep (se 1 (by rfl) ⟨258791, by rfl⟩ : syracuseStep 345055 = 517583) B517583
theorem B2343917 : Blo 271824 2343917 := bstep (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) B878969
theorem B412319 : Blo 271824 412319 := bstep (se 1 (by rfl) ⟨309239, by rfl⟩ : syracuseStep 412319 = 618479) B618479
theorem B4246253 : Blo 271824 4246253 := bstep (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) B1592345
theorem B2345831 : Blo 271824 2345831 := bstep (se 1 (by rfl) ⟨1759373, by rfl⟩ : syracuseStep 2345831 = 3518747) B3518747
theorem B5361983 : Blo 271824 5361983 := bstep (se 1 (by rfl) ⟨4021487, by rfl⟩ : syracuseStep 5361983 = 8042975) B8042975
theorem B1037245 : Blo 271824 1037245 := bstep (se 3 (by rfl) ⟨194483, by rfl⟩ : syracuseStep 1037245 = 388967) B388967
theorem B616283 : Blo 271824 616283 := bstep (se 1 (by rfl) ⟨462212, by rfl⟩ : syracuseStep 616283 = 924425) B924425
theorem B518555 : Blo 271824 518555 := bstep (se 1 (by rfl) ⟨388916, by rfl⟩ : syracuseStep 518555 = 777833) B777833
theorem B2812927 : Blo 271824 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B1175087 : Blo 271824 1175087 := bstep (se 1 (by rfl) ⟨881315, by rfl⟩ : syracuseStep 1175087 = 1762631) B1762631
theorem B1046297 : Blo 271824 1046297 := bstep (se 2 (by rfl) ⟨392361, by rfl⟩ : syracuseStep 1046297 = 784723) B784723
theorem B460073 : Blo 271824 460073 := bstep (se 2 (by rfl) ⟨172527, by rfl⟩ : syracuseStep 460073 = 345055) B345055
theorem B3574655 : Blo 271824 3574655 := bstep (se 1 (by rfl) ⟨2680991, by rfl⟩ : syracuseStep 3574655 = 5361983) B5361983
theorem B462503 : Blo 271824 462503 := bstep (se 1 (by rfl) ⟨346877, by rfl⟩ : syracuseStep 462503 = 693755) B693755
theorem B1382993 : Blo 271824 1382993 := bstep (se 2 (by rfl) ⟨518622, by rfl⟩ : syracuseStep 1382993 = 1037245) B1037245
theorem B2333393 : Blo 271824 2333393 := bstep (se 2 (by rfl) ⟨875022, by rfl⟩ : syracuseStep 2333393 = 1750045) B1750045
theorem B1385423 : Blo 271824 1385423 := bstep (se 1 (by rfl) ⟨1039067, by rfl⟩ : syracuseStep 1385423 = 2078135) B2078135
theorem B2073761 : Blo 271824 2073761 := bstep (se 2 (by rfl) ⟨777660, by rfl⟩ : syracuseStep 2073761 = 1555321) B1555321
theorem B697531 : Blo 271824 697531 := bstep (se 1 (by rfl) ⟨523148, by rfl⟩ : syracuseStep 697531 = 1046297) B1046297
theorem B272987 : Blo 271824 272987 := bstep (se 1 (by rfl) ⟨204740, by rfl⟩ : syracuseStep 272987 = 409481) B409481
theorem B273343 : Blo 271824 273343 := bstep (se 1 (by rfl) ⟨205007, by rfl⟩ : syracuseStep 273343 = 410015) B410015
theorem B274879 : Blo 271824 274879 := bstep (se 1 (by rfl) ⟨206159, by rfl⟩ : syracuseStep 274879 = 412319) B412319
theorem B2830835 : Blo 271824 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B4962799 : Blo 271824 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B3750569 : Blo 271824 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B410855 : Blo 271824 410855 := bstep (se 1 (by rfl) ⟨308141, by rfl⟩ : syracuseStep 410855 = 616283) B616283
theorem B345703 : Blo 271824 345703 := bstep (se 1 (by rfl) ⟨259277, by rfl⟩ : syracuseStep 345703 = 518555) B518555
theorem B1562611 : Blo 271824 1562611 := bstep (se 1 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 1562611 = 2343917) B2343917
theorem B1563887 : Blo 271824 1563887 := bstep (se 1 (by rfl) ⟨1172915, by rfl⟩ : syracuseStep 1563887 = 2345831) B2345831
theorem B7563091 : Blo 271824 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B1469767 : Blo 271824 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B783391 : Blo 271824 783391 := bstep (se 1 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 783391 = 1175087) B1175087
theorem B7960679 : Blo 271824 7960679 := bstep (se 1 (by rfl) ⟨5970509, by rfl⟩ : syracuseStep 7960679 = 11941019) B11941019
theorem B2980799 : Blo 271824 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B460937 : Blo 271824 460937 := bstep (se 2 (by rfl) ⟨172851, by rfl⟩ : syracuseStep 460937 = 345703) B345703
theorem B921995 : Blo 271824 921995 := bstep (se 1 (by rfl) ⟨691496, by rfl⟩ : syracuseStep 921995 = 1382993) B1382993
theorem B923615 : Blo 271824 923615 := bstep (se 1 (by rfl) ⟨692711, by rfl⟩ : syracuseStep 923615 = 1385423) B1385423
theorem B1382507 : Blo 271824 1382507 := bstep (se 1 (by rfl) ⟨1036880, by rfl⟩ : syracuseStep 1382507 = 2073761) B2073761
theorem B2500379 : Blo 271824 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B273903 : Blo 271824 273903 := bstep (se 1 (by rfl) ⟨205427, by rfl⟩ : syracuseStep 273903 = 410855) B410855
theorem B306715 : Blo 271824 306715 := bstep (se 1 (by rfl) ⟨230036, by rfl⟩ : syracuseStep 306715 = 460073) B460073
theorem B7548893 : Blo 271824 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B930041 : Blo 271824 930041 := bstep (se 2 (by rfl) ⟨348765, by rfl⟩ : syracuseStep 930041 = 697531) B697531
theorem B308335 : Blo 271824 308335 := bstep (se 1 (by rfl) ⟨231251, by rfl⟩ : syracuseStep 308335 = 462503) B462503
theorem B1555595 : Blo 271824 1555595 := bstep (se 1 (by rfl) ⟨1166696, by rfl⟩ : syracuseStep 1555595 = 2333393) B2333393
theorem B2083481 : Blo 271824 2083481 := bstep (se 2 (by rfl) ⟨781305, by rfl⟩ : syracuseStep 2083481 = 1562611) B1562611
theorem B1987199 : Blo 271824 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B2383103 : Blo 271824 2383103 := bstep (se 1 (by rfl) ⟨1787327, by rfl⟩ : syracuseStep 2383103 = 3574655) B3574655
theorem B10084121 : Blo 271824 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B1959689 : Blo 271824 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B1042591 : Blo 271824 1042591 := bstep (se 1 (by rfl) ⟨781943, by rfl⟩ : syracuseStep 1042591 = 1563887) B1563887
theorem B1044521 : Blo 271824 1044521 := bstep (se 2 (by rfl) ⟨391695, by rfl⟩ : syracuseStep 1044521 = 783391) B783391
theorem B6617065 : Blo 271824 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B5307119 : Blo 271824 5307119 := bstep (se 1 (by rfl) ⟨3980339, by rfl⟩ : syracuseStep 5307119 = 7960679) B7960679
theorem B921671 : Blo 271824 921671 := bstep (se 1 (by rfl) ⟨691253, by rfl⟩ : syracuseStep 921671 = 1382507) B1382507
theorem B6722747 : Blo 271824 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B8822753 : Blo 271824 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B696347 : Blo 271824 696347 := bstep (se 1 (by rfl) ⟨522260, by rfl⟩ : syracuseStep 696347 = 1044521) B1044521
theorem B307291 : Blo 271824 307291 := bstep (se 1 (by rfl) ⟨230468, by rfl⟩ : syracuseStep 307291 = 460937) B460937
theorem B1388987 : Blo 271824 1388987 := bstep (se 1 (by rfl) ⟨1041740, by rfl⟩ : syracuseStep 1388987 = 2083481) B2083481
theorem B1390121 : Blo 271824 1390121 := bstep (se 2 (by rfl) ⟨521295, by rfl⟩ : syracuseStep 1390121 = 1042591) B1042591
theorem B1324799 : Blo 271824 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B408953 : Blo 271824 408953 := bstep (se 2 (by rfl) ⟨153357, by rfl⟩ : syracuseStep 408953 = 306715) B306715
theorem B1588735 : Blo 271824 1588735 := bstep (se 1 (by rfl) ⟨1191551, by rfl⟩ : syracuseStep 1588735 = 2383103) B2383103
theorem B411113 : Blo 271824 411113 := bstep (se 2 (by rfl) ⟨154167, by rfl⟩ : syracuseStep 411113 = 308335) B308335
theorem B5032595 : Blo 271824 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B1037063 : Blo 271824 1037063 := bstep (se 1 (by rfl) ⟨777797, by rfl⟩ : syracuseStep 1037063 = 1555595) B1555595
theorem B614663 : Blo 271824 614663 := bstep (se 1 (by rfl) ⟨460997, by rfl⟩ : syracuseStep 614663 = 921995) B921995
theorem B615743 : Blo 271824 615743 := bstep (se 1 (by rfl) ⟨461807, by rfl⟩ : syracuseStep 615743 = 923615) B923615
theorem B1306459 : Blo 271824 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B1666919 : Blo 271824 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B620027 : Blo 271824 620027 := bstep (se 1 (by rfl) ⟨465020, by rfl⟩ : syracuseStep 620027 = 930041) B930041
theorem B3538079 : Blo 271824 3538079 := bstep (se 1 (by rfl) ⟨2653559, by rfl⟩ : syracuseStep 3538079 = 5307119) B5307119
theorem B691375 : Blo 271824 691375 := bstep (se 1 (by rfl) ⟨518531, by rfl⟩ : syracuseStep 691375 = 1037063) B1037063
theorem B464231 : Blo 271824 464231 := bstep (se 1 (by rfl) ⟨348173, by rfl⟩ : syracuseStep 464231 = 696347) B696347
theorem B925991 : Blo 271824 925991 := bstep (se 1 (by rfl) ⟨694493, by rfl⟩ : syracuseStep 925991 = 1388987) B1388987
theorem B926747 : Blo 271824 926747 := bstep (se 1 (by rfl) ⟨695060, by rfl⟩ : syracuseStep 926747 = 1390121) B1390121
theorem B272635 : Blo 271824 272635 := bstep (se 1 (by rfl) ⟨204476, by rfl⟩ : syracuseStep 272635 = 408953) B408953
theorem B274075 : Blo 271824 274075 := bstep (se 1 (by rfl) ⟨205556, by rfl⟩ : syracuseStep 274075 = 411113) B411113
theorem B3355063 : Blo 271824 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B5881835 : Blo 271824 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B409721 : Blo 271824 409721 := bstep (se 2 (by rfl) ⟨153645, by rfl⟩ : syracuseStep 409721 = 307291) B307291
theorem B409775 : Blo 271824 409775 := bstep (se 1 (by rfl) ⟨307331, by rfl⟩ : syracuseStep 409775 = 614663) B614663
theorem B410495 : Blo 271824 410495 := bstep (se 1 (by rfl) ⟨307871, by rfl⟩ : syracuseStep 410495 = 615743) B615743
theorem B413351 : Blo 271824 413351 := bstep (se 1 (by rfl) ⟨310013, by rfl⟩ : syracuseStep 413351 = 620027) B620027
theorem B6967781 : Blo 271824 6967781 := bstep (se 4 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 6967781 = 1306459) B1306459
theorem B2118313 : Blo 271824 2118313 := bstep (se 2 (by rfl) ⟨794367, by rfl⟩ : syracuseStep 2118313 = 1588735) B1588735
theorem B614447 : Blo 271824 614447 := bstep (se 1 (by rfl) ⟨460835, by rfl⟩ : syracuseStep 614447 = 921671) B921671
theorem B4481831 : Blo 271824 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B1111279 : Blo 271824 1111279 := bstep (se 1 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 1111279 = 1666919) B1666919
theorem B883199 : Blo 271824 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B2358719 : Blo 271824 2358719 := bstep (se 1 (by rfl) ⟨1769039, by rfl⟩ : syracuseStep 2358719 = 3538079) B3538079
theorem B17893669 : Blo 271824 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B921833 : Blo 271824 921833 := bstep (se 2 (by rfl) ⟨345687, by rfl⟩ : syracuseStep 921833 = 691375) B691375
theorem B2987887 : Blo 271824 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B2824417 : Blo 271824 2824417 := bstep (se 2 (by rfl) ⟨1059156, by rfl⟩ : syracuseStep 2824417 = 2118313) B2118313
theorem B1481705 : Blo 271824 1481705 := bstep (se 2 (by rfl) ⟨555639, by rfl⟩ : syracuseStep 1481705 = 1111279) B1111279
theorem B273147 : Blo 271824 273147 := bstep (se 1 (by rfl) ⟨204860, by rfl⟩ : syracuseStep 273147 = 409721) B409721
theorem B273183 : Blo 271824 273183 := bstep (se 1 (by rfl) ⟨204887, by rfl⟩ : syracuseStep 273183 = 409775) B409775
theorem B273663 : Blo 271824 273663 := bstep (se 1 (by rfl) ⟨205247, by rfl⟩ : syracuseStep 273663 = 410495) B410495
theorem B275567 : Blo 271824 275567 := bstep (se 1 (by rfl) ⟨206675, by rfl⟩ : syracuseStep 275567 = 413351) B413351
theorem B309487 : Blo 271824 309487 := bstep (se 1 (by rfl) ⟨232115, by rfl⟩ : syracuseStep 309487 = 464231) B464231
theorem B409631 : Blo 271824 409631 := bstep (se 1 (by rfl) ⟨307223, by rfl⟩ : syracuseStep 409631 = 614447) B614447
theorem B3921223 : Blo 271824 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B4645187 : Blo 271824 4645187 := bstep (se 1 (by rfl) ⟨3483890, by rfl⟩ : syracuseStep 4645187 = 6967781) B6967781
theorem B617327 : Blo 271824 617327 := bstep (se 1 (by rfl) ⟨462995, by rfl⟩ : syracuseStep 617327 = 925991) B925991
theorem B617831 : Blo 271824 617831 := bstep (se 1 (by rfl) ⟨463373, by rfl⟩ : syracuseStep 617831 = 926747) B926747
theorem B588799 : Blo 271824 588799 := bstep (se 1 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 588799 = 883199) B883199
theorem B1572479 : Blo 271824 1572479 := bstep (se 1 (by rfl) ⟨1179359, by rfl⟩ : syracuseStep 1572479 = 2358719) B2358719
theorem B23858225 : Blo 271824 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B987803 : Blo 271824 987803 := bstep (se 1 (by rfl) ⟨740852, by rfl⟩ : syracuseStep 987803 = 1481705) B1481705
theorem B273087 : Blo 271824 273087 := bstep (se 1 (by rfl) ⟨204815, by rfl⟩ : syracuseStep 273087 = 409631) B409631
theorem B3096791 : Blo 271824 3096791 := bstep (se 1 (by rfl) ⟨2322593, by rfl⟩ : syracuseStep 3096791 = 4645187) B4645187
theorem B5228297 : Blo 271824 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B411551 : Blo 271824 411551 := bstep (se 1 (by rfl) ⟨308663, by rfl⟩ : syracuseStep 411551 = 617327) B617327
theorem B411887 : Blo 271824 411887 := bstep (se 1 (by rfl) ⟨308915, by rfl⟩ : syracuseStep 411887 = 617831) B617831
theorem B3983849 : Blo 271824 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B412649 : Blo 271824 412649 := bstep (se 2 (by rfl) ⟨154743, by rfl⟩ : syracuseStep 412649 = 309487) B309487
theorem B614555 : Blo 271824 614555 := bstep (se 1 (by rfl) ⟨460916, by rfl⟩ : syracuseStep 614555 = 921833) B921833
theorem B3765889 : Blo 271824 3765889 := bstep (se 2 (by rfl) ⟨1412208, by rfl⟩ : syracuseStep 3765889 = 2824417) B2824417
theorem B785065 : Blo 271824 785065 := bstep (se 2 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 785065 = 588799) B588799
theorem B1048319 : Blo 271824 1048319 := bstep (se 1 (by rfl) ⟨786239, by rfl⟩ : syracuseStep 1048319 = 1572479) B1572479
theorem B2064527 : Blo 271824 2064527 := bstep (se 1 (by rfl) ⟨1548395, by rfl⟩ : syracuseStep 2064527 = 3096791) B3096791
theorem B2655899 : Blo 271824 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B658535 : Blo 271824 658535 := bstep (se 1 (by rfl) ⟨493901, by rfl⟩ : syracuseStep 658535 = 987803) B987803
theorem B5021185 : Blo 271824 5021185 := bstep (se 2 (by rfl) ⟨1882944, by rfl⟩ : syracuseStep 5021185 = 3765889) B3765889
theorem B698879 : Blo 271824 698879 := bstep (se 1 (by rfl) ⟨524159, by rfl⟩ : syracuseStep 698879 = 1048319) B1048319
theorem B3485531 : Blo 271824 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B274367 : Blo 271824 274367 := bstep (se 1 (by rfl) ⟨205775, by rfl⟩ : syracuseStep 274367 = 411551) B411551
theorem B274591 : Blo 271824 274591 := bstep (se 1 (by rfl) ⟨205943, by rfl⟩ : syracuseStep 274591 = 411887) B411887
theorem B275099 : Blo 271824 275099 := bstep (se 1 (by rfl) ⟨206324, by rfl⟩ : syracuseStep 275099 = 412649) B412649
theorem B15905483 : Blo 271824 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B409703 : Blo 271824 409703 := bstep (se 1 (by rfl) ⟨307277, by rfl⟩ : syracuseStep 409703 = 614555) B614555
theorem B1046753 : Blo 271824 1046753 := bstep (se 2 (by rfl) ⟨392532, by rfl⟩ : syracuseStep 1046753 = 785065) B785065
theorem B1376351 : Blo 271824 1376351 := bstep (se 1 (by rfl) ⟨1032263, by rfl⟩ : syracuseStep 1376351 = 2064527) B2064527
theorem B1770599 : Blo 271824 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B697835 : Blo 271824 697835 := bstep (se 1 (by rfl) ⟨523376, by rfl⟩ : syracuseStep 697835 = 1046753) B1046753
theorem B6694913 : Blo 271824 6694913 := bstep (se 2 (by rfl) ⟨2510592, by rfl⟩ : syracuseStep 6694913 = 5021185) B5021185
theorem B273135 : Blo 271824 273135 := bstep (se 1 (by rfl) ⟨204851, by rfl⟩ : syracuseStep 273135 = 409703) B409703
theorem B1756093 : Blo 271824 1756093 := bstep (se 3 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 1756093 = 658535) B658535
theorem B10603655 : Blo 271824 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B1863677 : Blo 271824 1863677 := bstep (se 3 (by rfl) ⟨349439, by rfl⟩ : syracuseStep 1863677 = 698879) B698879
theorem B2323687 : Blo 271824 2323687 := bstep (se 1 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 2323687 = 3485531) B3485531
theorem B917567 : Blo 271824 917567 := bstep (se 1 (by rfl) ⟨688175, by rfl⟩ : syracuseStep 917567 = 1376351) B1376351
theorem B4721597 : Blo 271824 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B465223 : Blo 271824 465223 := bstep (se 1 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 465223 = 697835) B697835
theorem B4463275 : Blo 271824 4463275 := bstep (se 1 (by rfl) ⟨3347456, by rfl⟩ : syracuseStep 4463275 = 6694913) B6694913
theorem B2341457 : Blo 271824 2341457 := bstep (se 2 (by rfl) ⟨878046, by rfl⟩ : syracuseStep 2341457 = 1756093) B1756093
theorem B3098249 : Blo 271824 3098249 := bstep (se 2 (by rfl) ⟨1161843, by rfl⟩ : syracuseStep 3098249 = 2323687) B2323687
theorem B7069103 : Blo 271824 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B1860893 : Blo 271824 1860893 := bstep (se 3 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 1860893 = 697835) B697835
theorem B1242451 : Blo 271824 1242451 := bstep (se 1 (by rfl) ⟨931838, by rfl⟩ : syracuseStep 1242451 = 1863677) B1863677
theorem B2065499 : Blo 271824 2065499 := bstep (se 1 (by rfl) ⟨1549124, by rfl⟩ : syracuseStep 2065499 = 3098249) B3098249
theorem B3147731 : Blo 271824 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B6626405 : Blo 271824 6626405 := bstep (se 4 (by rfl) ⟨621225, by rfl⟩ : syracuseStep 6626405 = 1242451) B1242451
theorem B5951033 : Blo 271824 5951033 := bstep (se 2 (by rfl) ⟨2231637, by rfl⟩ : syracuseStep 5951033 = 4463275) B4463275
theorem B1560971 : Blo 271824 1560971 := bstep (se 1 (by rfl) ⟨1170728, by rfl⟩ : syracuseStep 1560971 = 2341457) B2341457
theorem B611711 : Blo 271824 611711 := bstep (se 1 (by rfl) ⟨458783, by rfl⟩ : syracuseStep 611711 = 917567) B917567
theorem B4712735 : Blo 271824 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B1240595 : Blo 271824 1240595 := bstep (se 1 (by rfl) ⟨930446, by rfl⟩ : syracuseStep 1240595 = 1860893) B1860893
theorem B620297 : Blo 271824 620297 := bstep (se 2 (by rfl) ⟨232611, by rfl⟩ : syracuseStep 620297 = 465223) B465223
theorem B1376999 : Blo 271824 1376999 := bstep (se 1 (by rfl) ⟨1032749, by rfl⟩ : syracuseStep 1376999 = 2065499) B2065499
theorem B2098487 : Blo 271824 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B3967355 : Blo 271824 3967355 := bstep (se 1 (by rfl) ⟨2975516, by rfl⟩ : syracuseStep 3967355 = 5951033) B5951033
theorem B827063 : Blo 271824 827063 := bstep (se 1 (by rfl) ⟨620297, by rfl⟩ : syracuseStep 827063 = 1240595) B1240595
theorem B17670413 : Blo 271824 17670413 := bstep (se 3 (by rfl) ⟨3313202, by rfl⟩ : syracuseStep 17670413 = 6626405) B6626405
theorem B407807 : Blo 271824 407807 := bstep (se 1 (by rfl) ⟨305855, by rfl⟩ : syracuseStep 407807 = 611711) B611711
theorem B413531 : Blo 271824 413531 := bstep (se 1 (by rfl) ⟨310148, by rfl⟩ : syracuseStep 413531 = 620297) B620297
theorem B1040647 : Blo 271824 1040647 := bstep (se 1 (by rfl) ⟨780485, by rfl⟩ : syracuseStep 1040647 = 1560971) B1560971
theorem B3141823 : Blo 271824 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B917999 : Blo 271824 917999 := bstep (se 1 (by rfl) ⟨688499, by rfl⟩ : syracuseStep 917999 = 1376999) B1376999
theorem B271871 : Blo 271824 271871 := bstep (se 1 (by rfl) ⟨203903, by rfl⟩ : syracuseStep 271871 = 407807) B407807
theorem B1387529 : Blo 271824 1387529 := bstep (se 2 (by rfl) ⟨520323, by rfl⟩ : syracuseStep 1387529 = 1040647) B1040647
theorem B275687 : Blo 271824 275687 := bstep (se 1 (by rfl) ⟨206765, by rfl⟩ : syracuseStep 275687 = 413531) B413531
theorem B11780275 : Blo 271824 11780275 := bstep (se 1 (by rfl) ⟨8835206, by rfl⟩ : syracuseStep 11780275 = 17670413) B17670413
theorem B2644903 : Blo 271824 2644903 := bstep (se 1 (by rfl) ⟨1983677, by rfl⟩ : syracuseStep 2644903 = 3967355) B3967355
theorem B5595965 : Blo 271824 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B551375 : Blo 271824 551375 := bstep (se 1 (by rfl) ⟨413531, by rfl⟩ : syracuseStep 551375 = 827063) B827063
theorem B4189097 : Blo 271824 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B367583 : Blo 271824 367583 := bstep (se 1 (by rfl) ⟨275687, by rfl⟩ : syracuseStep 367583 = 551375) B551375
theorem B2792731 : Blo 271824 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B925019 : Blo 271824 925019 := bstep (se 1 (by rfl) ⟨693764, by rfl⟩ : syracuseStep 925019 = 1387529) B1387529
theorem B15707033 : Blo 271824 15707033 := bstep (se 2 (by rfl) ⟨5890137, by rfl⟩ : syracuseStep 15707033 = 11780275) B11780275
theorem B3526537 : Blo 271824 3526537 := bstep (se 2 (by rfl) ⟨1322451, by rfl⟩ : syracuseStep 3526537 = 2644903) B2644903
theorem B611999 : Blo 271824 611999 := bstep (se 1 (by rfl) ⟨458999, by rfl⟩ : syracuseStep 611999 = 917999) B917999
theorem B3730643 : Blo 271824 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B407999 : Blo 271824 407999 := bstep (se 1 (by rfl) ⟨305999, by rfl⟩ : syracuseStep 407999 = 611999) B611999
theorem B4702049 : Blo 271824 4702049 := bstep (se 2 (by rfl) ⟨1763268, by rfl⟩ : syracuseStep 4702049 = 3526537) B3526537
theorem B10471355 : Blo 271824 10471355 := bstep (se 1 (by rfl) ⟨7853516, by rfl⟩ : syracuseStep 10471355 = 15707033) B15707033
theorem B3723641 : Blo 271824 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B616679 : Blo 271824 616679 := bstep (se 1 (by rfl) ⟨462509, by rfl⟩ : syracuseStep 616679 = 925019) B925019
theorem B2487095 : Blo 271824 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B980221 : Blo 271824 980221 := bstep (se 3 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 980221 = 367583) B367583
theorem B6980903 : Blo 271824 6980903 := bstep (se 1 (by rfl) ⟨5235677, by rfl⟩ : syracuseStep 6980903 = 10471355) B10471355
theorem B271999 : Blo 271824 271999 := bstep (se 1 (by rfl) ⟨203999, by rfl⟩ : syracuseStep 271999 = 407999) B407999
theorem B411119 : Blo 271824 411119 := bstep (se 1 (by rfl) ⟨308339, by rfl⟩ : syracuseStep 411119 = 616679) B616679
theorem B1658063 : Blo 271824 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B3134699 : Blo 271824 3134699 := bstep (se 1 (by rfl) ⟨2351024, by rfl⟩ : syracuseStep 3134699 = 4702049) B4702049
theorem B2482427 : Blo 271824 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B1306961 : Blo 271824 1306961 := bstep (se 2 (by rfl) ⟨490110, by rfl⟩ : syracuseStep 1306961 = 980221) B980221
theorem B4653935 : Blo 271824 4653935 := bstep (se 1 (by rfl) ⟨3490451, by rfl⟩ : syracuseStep 4653935 = 6980903) B6980903
theorem B274079 : Blo 271824 274079 := bstep (se 1 (by rfl) ⟨205559, by rfl⟩ : syracuseStep 274079 = 411119) B411119
theorem B1654951 : Blo 271824 1654951 := bstep (se 1 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 1654951 = 2482427) B2482427
theorem B871307 : Blo 271824 871307 := bstep (se 1 (by rfl) ⟨653480, by rfl⟩ : syracuseStep 871307 = 1306961) B1306961
theorem B1105375 : Blo 271824 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B2089799 : Blo 271824 2089799 := bstep (se 1 (by rfl) ⟨1567349, by rfl⟩ : syracuseStep 2089799 = 3134699) B3134699
theorem B2206601 : Blo 271824 2206601 := bstep (se 2 (by rfl) ⟨827475, by rfl⟩ : syracuseStep 2206601 = 1654951) B1654951
theorem B1393199 : Blo 271824 1393199 := bstep (se 1 (by rfl) ⟨1044899, by rfl⟩ : syracuseStep 1393199 = 2089799) B2089799
theorem B3102623 : Blo 271824 3102623 := bstep (se 1 (by rfl) ⟨2326967, by rfl⟩ : syracuseStep 3102623 = 4653935) B4653935
theorem B580871 : Blo 271824 580871 := bstep (se 1 (by rfl) ⟨435653, by rfl⟩ : syracuseStep 580871 = 871307) B871307
theorem B1473833 : Blo 271824 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B2068415 : Blo 271824 2068415 := bstep (se 1 (by rfl) ⟨1551311, by rfl⟩ : syracuseStep 2068415 = 3102623) B3102623
theorem B1548989 : Blo 271824 1548989 := bstep (se 3 (by rfl) ⟨290435, by rfl⟩ : syracuseStep 1548989 = 580871) B580871
theorem B928799 : Blo 271824 928799 := bstep (se 1 (by rfl) ⟨696599, by rfl⟩ : syracuseStep 928799 = 1393199) B1393199
theorem B1471067 : Blo 271824 1471067 := bstep (se 1 (by rfl) ⟨1103300, by rfl⟩ : syracuseStep 1471067 = 2206601) B2206601
theorem B3930221 : Blo 271824 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B1378943 : Blo 271824 1378943 := bstep (se 1 (by rfl) ⟨1034207, by rfl⟩ : syracuseStep 1378943 = 2068415) B2068415
theorem B1032659 : Blo 271824 1032659 := bstep (se 1 (by rfl) ⟨774494, by rfl⟩ : syracuseStep 1032659 = 1548989) B1548989
theorem B619199 : Blo 271824 619199 := bstep (se 1 (by rfl) ⟨464399, by rfl⟩ : syracuseStep 619199 = 928799) B928799
theorem B980711 : Blo 271824 980711 := bstep (se 1 (by rfl) ⟨735533, by rfl⟩ : syracuseStep 980711 = 1471067) B1471067
theorem B2620147 : Blo 271824 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B688439 : Blo 271824 688439 := bstep (se 1 (by rfl) ⟨516329, by rfl⟩ : syracuseStep 688439 = 1032659) B1032659
theorem B919295 : Blo 271824 919295 := bstep (se 1 (by rfl) ⟨689471, by rfl⟩ : syracuseStep 919295 = 1378943) B1378943
theorem B412799 : Blo 271824 412799 := bstep (se 1 (by rfl) ⟨309599, by rfl⟩ : syracuseStep 412799 = 619199) B619199
theorem B3493529 : Blo 271824 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B653807 : Blo 271824 653807 := bstep (se 1 (by rfl) ⟨490355, by rfl⟩ : syracuseStep 653807 = 980711) B980711
theorem B458959 : Blo 271824 458959 := bstep (se 1 (by rfl) ⟨344219, by rfl⟩ : syracuseStep 458959 = 688439) B688439
theorem B2329019 : Blo 271824 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B435871 : Blo 271824 435871 := bstep (se 1 (by rfl) ⟨326903, by rfl⟩ : syracuseStep 435871 = 653807) B653807
theorem B275199 : Blo 271824 275199 := bstep (se 1 (by rfl) ⟨206399, by rfl⟩ : syracuseStep 275199 = 412799) B412799
theorem B612863 : Blo 271824 612863 := bstep (se 1 (by rfl) ⟨459647, by rfl⟩ : syracuseStep 612863 = 919295) B919295
theorem B1552679 : Blo 271824 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B408575 : Blo 271824 408575 := bstep (se 1 (by rfl) ⟨306431, by rfl⟩ : syracuseStep 408575 = 612863) B612863
theorem B611945 : Blo 271824 611945 := bstep (se 2 (by rfl) ⟨229479, by rfl⟩ : syracuseStep 611945 = 458959) B458959
theorem B2324645 : Blo 271824 2324645 := bstep (se 4 (by rfl) ⟨217935, by rfl⟩ : syracuseStep 2324645 = 435871) B435871
theorem B1549763 : Blo 271824 1549763 := bstep (se 1 (by rfl) ⟨1162322, by rfl⟩ : syracuseStep 1549763 = 2324645) B2324645
theorem B272383 : Blo 271824 272383 := bstep (se 1 (by rfl) ⟨204287, by rfl⟩ : syracuseStep 272383 = 408575) B408575
theorem B407963 : Blo 271824 407963 := bstep (se 1 (by rfl) ⟨305972, by rfl⟩ : syracuseStep 407963 = 611945) B611945
theorem B1035119 : Blo 271824 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B690079 : Blo 271824 690079 := bstep (se 1 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 690079 = 1035119) B1035119
theorem B271975 : Blo 271824 271975 := bstep (se 1 (by rfl) ⟨203981, by rfl⟩ : syracuseStep 271975 = 407963) B407963
theorem B1033175 : Blo 271824 1033175 := bstep (se 1 (by rfl) ⟨774881, by rfl⟩ : syracuseStep 1033175 = 1549763) B1549763
theorem B688783 : Blo 271824 688783 := bstep (se 1 (by rfl) ⟨516587, by rfl⟩ : syracuseStep 688783 = 1033175) B1033175
theorem B920105 : Blo 271824 920105 := bstep (se 2 (by rfl) ⟨345039, by rfl⟩ : syracuseStep 920105 = 690079) B690079
theorem B918377 : Blo 271824 918377 := bstep (se 2 (by rfl) ⟨344391, by rfl⟩ : syracuseStep 918377 = 688783) B688783
theorem B613403 : Blo 271824 613403 := bstep (se 1 (by rfl) ⟨460052, by rfl⟩ : syracuseStep 613403 = 920105) B920105
theorem B408935 : Blo 271824 408935 := bstep (se 1 (by rfl) ⟨306701, by rfl⟩ : syracuseStep 408935 = 613403) B613403
theorem B612251 : Blo 271824 612251 := bstep (se 1 (by rfl) ⟨459188, by rfl⟩ : syracuseStep 612251 = 918377) B918377
theorem B272623 : Blo 271824 272623 := bstep (se 1 (by rfl) ⟨204467, by rfl⟩ : syracuseStep 272623 = 408935) B408935
theorem B408167 : Blo 271824 408167 := bstep (se 1 (by rfl) ⟨306125, by rfl⟩ : syracuseStep 408167 = 612251) B612251
theorem B272111 : Blo 271824 272111 := bstep (se 1 (by rfl) ⟨204083, by rfl⟩ : syracuseStep 272111 = 408167) B408167

theorem C0 (j : ℕ) (h1 : 67956 ≤ j) (h2 : j ≤ 68655) : Blo 271824 (4 * j + 3) := by
  interval_cases j
  · exact B271827
  · exact B271831
  · exact B271835
  · exact B271839
  · exact B271843
  · exact B271847
  · exact B271851
  · exact B271855
  · exact B271859
  · exact B271863
  · exact B271867
  · exact B271871
  · exact B271875
  · exact B271879
  · exact B271883
  · exact B271887
  · exact B271891
  · exact B271895
  · exact B271899
  · exact B271903
  · exact B271907
  · exact B271911
  · exact B271915
  · exact B271919
  · exact B271923
  · exact B271927
  · exact B271931
  · exact B271935
  · exact B271939
  · exact B271943
  · exact B271947
  · exact B271951
  · exact B271955
  · exact B271959
  · exact B271963
  · exact B271967
  · exact B271971
  · exact B271975
  · exact B271979
  · exact B271983
  · exact B271987
  · exact B271991
  · exact B271995
  · exact B271999
  · exact B272003
  · exact B272007
  · exact B272011
  · exact B272015
  · exact B272019
  · exact B272023
  · exact B272027
  · exact B272031
  · exact B272035
  · exact B272039
  · exact B272043
  · exact B272047
  · exact B272051
  · exact B272055
  · exact B272059
  · exact B272063
  · exact B272067
  · exact B272071
  · exact B272075
  · exact B272079
  · exact B272083
  · exact B272087
  · exact B272091
  · exact B272095
  · exact B272099
  · exact B272103
  · exact B272107
  · exact B272111
  · exact B272115
  · exact B272119
  · exact B272123
  · exact B272127
  · exact B272131
  · exact B272135
  · exact B272139
  · exact B272143
  · exact B272147
  · exact B272151
  · exact B272155
  · exact B272159
  · exact B272163
  · exact B272167
  · exact B272171
  · exact B272175
  · exact B272179
  · exact B272183
  · exact B272187
  · exact B272191
  · exact B272195
  · exact B272199
  · exact B272203
  · exact B272207
  · exact B272211
  · exact B272215
  · exact B272219
  · exact B272223
  · exact B272227
  · exact B272231
  · exact B272235
  · exact B272239
  · exact B272243
  · exact B272247
  · exact B272251
  · exact B272255
  · exact B272259
  · exact B272263
  · exact B272267
  · exact B272271
  · exact B272275
  · exact B272279
  · exact B272283
  · exact B272287
  · exact B272291
  · exact B272295
  · exact B272299
  · exact B272303
  · exact B272307
  · exact B272311
  · exact B272315
  · exact B272319
  · exact B272323
  · exact B272327
  · exact B272331
  · exact B272335
  · exact B272339
  · exact B272343
  · exact B272347
  · exact B272351
  · exact B272355
  · exact B272359
  · exact B272363
  · exact B272367
  · exact B272371
  · exact B272375
  · exact B272379
  · exact B272383
  · exact B272387
  · exact B272391
  · exact B272395
  · exact B272399
  · exact B272403
  · exact B272407
  · exact B272411
  · exact B272415
  · exact B272419
  · exact B272423
  · exact B272427
  · exact B272431
  · exact B272435
  · exact B272439
  · exact B272443
  · exact B272447
  · exact B272451
  · exact B272455
  · exact B272459
  · exact B272463
  · exact B272467
  · exact B272471
  · exact B272475
  · exact B272479
  · exact B272483
  · exact B272487
  · exact B272491
  · exact B272495
  · exact B272499
  · exact B272503
  · exact B272507
  · exact B272511
  · exact B272515
  · exact B272519
  · exact B272523
  · exact B272527
  · exact B272531
  · exact B272535
  · exact B272539
  · exact B272543
  · exact B272547
  · exact B272551
  · exact B272555
  · exact B272559
  · exact B272563
  · exact B272567
  · exact B272571
  · exact B272575
  · exact B272579
  · exact B272583
  · exact B272587
  · exact B272591
  · exact B272595
  · exact B272599
  · exact B272603
  · exact B272607
  · exact B272611
  · exact B272615
  · exact B272619
  · exact B272623
  · exact B272627
  · exact B272631
  · exact B272635
  · exact B272639
  · exact B272643
  · exact B272647
  · exact B272651
  · exact B272655
  · exact B272659
  · exact B272663
  · exact B272667
  · exact B272671
  · exact B272675
  · exact B272679
  · exact B272683
  · exact B272687
  · exact B272691
  · exact B272695
  · exact B272699
  · exact B272703
  · exact B272707
  · exact B272711
  · exact B272715
  · exact B272719
  · exact B272723
  · exact B272727
  · exact B272731
  · exact B272735
  · exact B272739
  · exact B272743
  · exact B272747
  · exact B272751
  · exact B272755
  · exact B272759
  · exact B272763
  · exact B272767
  · exact B272771
  · exact B272775
  · exact B272779
  · exact B272783
  · exact B272787
  · exact B272791
  · exact B272795
  · exact B272799
  · exact B272803
  · exact B272807
  · exact B272811
  · exact B272815
  · exact B272819
  · exact B272823
  · exact B272827
  · exact B272831
  · exact B272835
  · exact B272839
  · exact B272843
  · exact B272847
  · exact B272851
  · exact B272855
  · exact B272859
  · exact B272863
  · exact B272867
  · exact B272871
  · exact B272875
  · exact B272879
  · exact B272883
  · exact B272887
  · exact B272891
  · exact B272895
  · exact B272899
  · exact B272903
  · exact B272907
  · exact B272911
  · exact B272915
  · exact B272919
  · exact B272923
  · exact B272927
  · exact B272931
  · exact B272935
  · exact B272939
  · exact B272943
  · exact B272947
  · exact B272951
  · exact B272955
  · exact B272959
  · exact B272963
  · exact B272967
  · exact B272971
  · exact B272975
  · exact B272979
  · exact B272983
  · exact B272987
  · exact B272991
  · exact B272995
  · exact B272999
  · exact B273003
  · exact B273007
  · exact B273011
  · exact B273015
  · exact B273019
  · exact B273023
  · exact B273027
  · exact B273031
  · exact B273035
  · exact B273039
  · exact B273043
  · exact B273047
  · exact B273051
  · exact B273055
  · exact B273059
  · exact B273063
  · exact B273067
  · exact B273071
  · exact B273075
  · exact B273079
  · exact B273083
  · exact B273087
  · exact B273091
  · exact B273095
  · exact B273099
  · exact B273103
  · exact B273107
  · exact B273111
  · exact B273115
  · exact B273119
  · exact B273123
  · exact B273127
  · exact B273131
  · exact B273135
  · exact B273139
  · exact B273143
  · exact B273147
  · exact B273151
  · exact B273155
  · exact B273159
  · exact B273163
  · exact B273167
  · exact B273171
  · exact B273175
  · exact B273179
  · exact B273183
  · exact B273187
  · exact B273191
  · exact B273195
  · exact B273199
  · exact B273203
  · exact B273207
  · exact B273211
  · exact B273215
  · exact B273219
  · exact B273223
  · exact B273227
  · exact B273231
  · exact B273235
  · exact B273239
  · exact B273243
  · exact B273247
  · exact B273251
  · exact B273255
  · exact B273259
  · exact B273263
  · exact B273267
  · exact B273271
  · exact B273275
  · exact B273279
  · exact B273283
  · exact B273287
  · exact B273291
  · exact B273295
  · exact B273299
  · exact B273303
  · exact B273307
  · exact B273311
  · exact B273315
  · exact B273319
  · exact B273323
  · exact B273327
  · exact B273331
  · exact B273335
  · exact B273339
  · exact B273343
  · exact B273347
  · exact B273351
  · exact B273355
  · exact B273359
  · exact B273363
  · exact B273367
  · exact B273371
  · exact B273375
  · exact B273379
  · exact B273383
  · exact B273387
  · exact B273391
  · exact B273395
  · exact B273399
  · exact B273403
  · exact B273407
  · exact B273411
  · exact B273415
  · exact B273419
  · exact B273423
  · exact B273427
  · exact B273431
  · exact B273435
  · exact B273439
  · exact B273443
  · exact B273447
  · exact B273451
  · exact B273455
  · exact B273459
  · exact B273463
  · exact B273467
  · exact B273471
  · exact B273475
  · exact B273479
  · exact B273483
  · exact B273487
  · exact B273491
  · exact B273495
  · exact B273499
  · exact B273503
  · exact B273507
  · exact B273511
  · exact B273515
  · exact B273519
  · exact B273523
  · exact B273527
  · exact B273531
  · exact B273535
  · exact B273539
  · exact B273543
  · exact B273547
  · exact B273551
  · exact B273555
  · exact B273559
  · exact B273563
  · exact B273567
  · exact B273571
  · exact B273575
  · exact B273579
  · exact B273583
  · exact B273587
  · exact B273591
  · exact B273595
  · exact B273599
  · exact B273603
  · exact B273607
  · exact B273611
  · exact B273615
  · exact B273619
  · exact B273623
  · exact B273627
  · exact B273631
  · exact B273635
  · exact B273639
  · exact B273643
  · exact B273647
  · exact B273651
  · exact B273655
  · exact B273659
  · exact B273663
  · exact B273667
  · exact B273671
  · exact B273675
  · exact B273679
  · exact B273683
  · exact B273687
  · exact B273691
  · exact B273695
  · exact B273699
  · exact B273703
  · exact B273707
  · exact B273711
  · exact B273715
  · exact B273719
  · exact B273723
  · exact B273727
  · exact B273731
  · exact B273735
  · exact B273739
  · exact B273743
  · exact B273747
  · exact B273751
  · exact B273755
  · exact B273759
  · exact B273763
  · exact B273767
  · exact B273771
  · exact B273775
  · exact B273779
  · exact B273783
  · exact B273787
  · exact B273791
  · exact B273795
  · exact B273799
  · exact B273803
  · exact B273807
  · exact B273811
  · exact B273815
  · exact B273819
  · exact B273823
  · exact B273827
  · exact B273831
  · exact B273835
  · exact B273839
  · exact B273843
  · exact B273847
  · exact B273851
  · exact B273855
  · exact B273859
  · exact B273863
  · exact B273867
  · exact B273871
  · exact B273875
  · exact B273879
  · exact B273883
  · exact B273887
  · exact B273891
  · exact B273895
  · exact B273899
  · exact B273903
  · exact B273907
  · exact B273911
  · exact B273915
  · exact B273919
  · exact B273923
  · exact B273927
  · exact B273931
  · exact B273935
  · exact B273939
  · exact B273943
  · exact B273947
  · exact B273951
  · exact B273955
  · exact B273959
  · exact B273963
  · exact B273967
  · exact B273971
  · exact B273975
  · exact B273979
  · exact B273983
  · exact B273987
  · exact B273991
  · exact B273995
  · exact B273999
  · exact B274003
  · exact B274007
  · exact B274011
  · exact B274015
  · exact B274019
  · exact B274023
  · exact B274027
  · exact B274031
  · exact B274035
  · exact B274039
  · exact B274043
  · exact B274047
  · exact B274051
  · exact B274055
  · exact B274059
  · exact B274063
  · exact B274067
  · exact B274071
  · exact B274075
  · exact B274079
  · exact B274083
  · exact B274087
  · exact B274091
  · exact B274095
  · exact B274099
  · exact B274103
  · exact B274107
  · exact B274111
  · exact B274115
  · exact B274119
  · exact B274123
  · exact B274127
  · exact B274131
  · exact B274135
  · exact B274139
  · exact B274143
  · exact B274147
  · exact B274151
  · exact B274155
  · exact B274159
  · exact B274163
  · exact B274167
  · exact B274171
  · exact B274175
  · exact B274179
  · exact B274183
  · exact B274187
  · exact B274191
  · exact B274195
  · exact B274199
  · exact B274203
  · exact B274207
  · exact B274211
  · exact B274215
  · exact B274219
  · exact B274223
  · exact B274227
  · exact B274231
  · exact B274235
  · exact B274239
  · exact B274243
  · exact B274247
  · exact B274251
  · exact B274255
  · exact B274259
  · exact B274263
  · exact B274267
  · exact B274271
  · exact B274275
  · exact B274279
  · exact B274283
  · exact B274287
  · exact B274291
  · exact B274295
  · exact B274299
  · exact B274303
  · exact B274307
  · exact B274311
  · exact B274315
  · exact B274319
  · exact B274323
  · exact B274327
  · exact B274331
  · exact B274335
  · exact B274339
  · exact B274343
  · exact B274347
  · exact B274351
  · exact B274355
  · exact B274359
  · exact B274363
  · exact B274367
  · exact B274371
  · exact B274375
  · exact B274379
  · exact B274383
  · exact B274387
  · exact B274391
  · exact B274395
  · exact B274399
  · exact B274403
  · exact B274407
  · exact B274411
  · exact B274415
  · exact B274419
  · exact B274423
  · exact B274427
  · exact B274431
  · exact B274435
  · exact B274439
  · exact B274443
  · exact B274447
  · exact B274451
  · exact B274455
  · exact B274459
  · exact B274463
  · exact B274467
  · exact B274471
  · exact B274475
  · exact B274479
  · exact B274483
  · exact B274487
  · exact B274491
  · exact B274495
  · exact B274499
  · exact B274503
  · exact B274507
  · exact B274511
  · exact B274515
  · exact B274519
  · exact B274523
  · exact B274527
  · exact B274531
  · exact B274535
  · exact B274539
  · exact B274543
  · exact B274547
  · exact B274551
  · exact B274555
  · exact B274559
  · exact B274563
  · exact B274567
  · exact B274571
  · exact B274575
  · exact B274579
  · exact B274583
  · exact B274587
  · exact B274591
  · exact B274595
  · exact B274599
  · exact B274603
  · exact B274607
  · exact B274611
  · exact B274615
  · exact B274619
  · exact B274623

theorem C1 (j : ℕ) (h1 : 68656 ≤ j) (h2 : j ≤ 68955) : Blo 271824 (4 * j + 3) := by
  interval_cases j
  · exact B274627
  · exact B274631
  · exact B274635
  · exact B274639
  · exact B274643
  · exact B274647
  · exact B274651
  · exact B274655
  · exact B274659
  · exact B274663
  · exact B274667
  · exact B274671
  · exact B274675
  · exact B274679
  · exact B274683
  · exact B274687
  · exact B274691
  · exact B274695
  · exact B274699
  · exact B274703
  · exact B274707
  · exact B274711
  · exact B274715
  · exact B274719
  · exact B274723
  · exact B274727
  · exact B274731
  · exact B274735
  · exact B274739
  · exact B274743
  · exact B274747
  · exact B274751
  · exact B274755
  · exact B274759
  · exact B274763
  · exact B274767
  · exact B274771
  · exact B274775
  · exact B274779
  · exact B274783
  · exact B274787
  · exact B274791
  · exact B274795
  · exact B274799
  · exact B274803
  · exact B274807
  · exact B274811
  · exact B274815
  · exact B274819
  · exact B274823
  · exact B274827
  · exact B274831
  · exact B274835
  · exact B274839
  · exact B274843
  · exact B274847
  · exact B274851
  · exact B274855
  · exact B274859
  · exact B274863
  · exact B274867
  · exact B274871
  · exact B274875
  · exact B274879
  · exact B274883
  · exact B274887
  · exact B274891
  · exact B274895
  · exact B274899
  · exact B274903
  · exact B274907
  · exact B274911
  · exact B274915
  · exact B274919
  · exact B274923
  · exact B274927
  · exact B274931
  · exact B274935
  · exact B274939
  · exact B274943
  · exact B274947
  · exact B274951
  · exact B274955
  · exact B274959
  · exact B274963
  · exact B274967
  · exact B274971
  · exact B274975
  · exact B274979
  · exact B274983
  · exact B274987
  · exact B274991
  · exact B274995
  · exact B274999
  · exact B275003
  · exact B275007
  · exact B275011
  · exact B275015
  · exact B275019
  · exact B275023
  · exact B275027
  · exact B275031
  · exact B275035
  · exact B275039
  · exact B275043
  · exact B275047
  · exact B275051
  · exact B275055
  · exact B275059
  · exact B275063
  · exact B275067
  · exact B275071
  · exact B275075
  · exact B275079
  · exact B275083
  · exact B275087
  · exact B275091
  · exact B275095
  · exact B275099
  · exact B275103
  · exact B275107
  · exact B275111
  · exact B275115
  · exact B275119
  · exact B275123
  · exact B275127
  · exact B275131
  · exact B275135
  · exact B275139
  · exact B275143
  · exact B275147
  · exact B275151
  · exact B275155
  · exact B275159
  · exact B275163
  · exact B275167
  · exact B275171
  · exact B275175
  · exact B275179
  · exact B275183
  · exact B275187
  · exact B275191
  · exact B275195
  · exact B275199
  · exact B275203
  · exact B275207
  · exact B275211
  · exact B275215
  · exact B275219
  · exact B275223
  · exact B275227
  · exact B275231
  · exact B275235
  · exact B275239
  · exact B275243
  · exact B275247
  · exact B275251
  · exact B275255
  · exact B275259
  · exact B275263
  · exact B275267
  · exact B275271
  · exact B275275
  · exact B275279
  · exact B275283
  · exact B275287
  · exact B275291
  · exact B275295
  · exact B275299
  · exact B275303
  · exact B275307
  · exact B275311
  · exact B275315
  · exact B275319
  · exact B275323
  · exact B275327
  · exact B275331
  · exact B275335
  · exact B275339
  · exact B275343
  · exact B275347
  · exact B275351
  · exact B275355
  · exact B275359
  · exact B275363
  · exact B275367
  · exact B275371
  · exact B275375
  · exact B275379
  · exact B275383
  · exact B275387
  · exact B275391
  · exact B275395
  · exact B275399
  · exact B275403
  · exact B275407
  · exact B275411
  · exact B275415
  · exact B275419
  · exact B275423
  · exact B275427
  · exact B275431
  · exact B275435
  · exact B275439
  · exact B275443
  · exact B275447
  · exact B275451
  · exact B275455
  · exact B275459
  · exact B275463
  · exact B275467
  · exact B275471
  · exact B275475
  · exact B275479
  · exact B275483
  · exact B275487
  · exact B275491
  · exact B275495
  · exact B275499
  · exact B275503
  · exact B275507
  · exact B275511
  · exact B275515
  · exact B275519
  · exact B275523
  · exact B275527
  · exact B275531
  · exact B275535
  · exact B275539
  · exact B275543
  · exact B275547
  · exact B275551
  · exact B275555
  · exact B275559
  · exact B275563
  · exact B275567
  · exact B275571
  · exact B275575
  · exact B275579
  · exact B275583
  · exact B275587
  · exact B275591
  · exact B275595
  · exact B275599
  · exact B275603
  · exact B275607
  · exact B275611
  · exact B275615
  · exact B275619
  · exact B275623
  · exact B275627
  · exact B275631
  · exact B275635
  · exact B275639
  · exact B275643
  · exact B275647
  · exact B275651
  · exact B275655
  · exact B275659
  · exact B275663
  · exact B275667
  · exact B275671
  · exact B275675
  · exact B275679
  · exact B275683
  · exact B275687
  · exact B275691
  · exact B275695
  · exact B275699
  · exact B275703
  · exact B275707
  · exact B275711
  · exact B275715
  · exact B275719
  · exact B275723
  · exact B275727
  · exact B275731
  · exact B275735
  · exact B275739
  · exact B275743
  · exact B275747
  · exact B275751
  · exact B275755
  · exact B275759
  · exact B275763
  · exact B275767
  · exact B275771
  · exact B275775
  · exact B275779
  · exact B275783
  · exact B275787
  · exact B275791
  · exact B275795
  · exact B275799
  · exact B275803
  · exact B275807
  · exact B275811
  · exact B275815
  · exact B275819
  · exact B275823

theorem solution (m : ℕ) (hlo : 271824 ≤ m) (hhi : m ≤ 275824) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 67956 ≤ j := by omega
    have hj2 : j ≤ 68955 := by omega
    have hb : Blo 271824 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 68656 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
