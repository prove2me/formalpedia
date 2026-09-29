-- Prove2me | solution 1 for syracuse_descends_range_1877140_1879140
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:16:33.865252+00:00
-- url     : https://prove2.me/submissions/db068625-178c-481a-ad94-2172cdff7728

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


theorem B2113537 : Blo 1877140 2113537 := bbase (se 2 (by rfl) ⟨792576, by rfl⟩ : syracuseStep 2113537 = 1585153) (by norm_num)
theorem B2818061 : Blo 1877140 2818061 := bbase (se 3 (by rfl) ⟨528386, by rfl⟩ : syracuseStep 2818061 = 1056773) (by norm_num)
theorem B4227101 : Blo 1877140 4227101 := bbase (se 3 (by rfl) ⟨792581, by rfl⟩ : syracuseStep 4227101 = 1585163) (by norm_num)
theorem B3170333 : Blo 1877140 3170333 := bbase (se 3 (by rfl) ⟨594437, by rfl⟩ : syracuseStep 3170333 = 1188875) (by norm_num)
theorem B2818085 : Blo 1877140 2818085 := bbase (se 4 (by rfl) ⟨264195, by rfl⟩ : syracuseStep 2818085 = 528391) (by norm_num)
theorem B2113573 : Blo 1877140 2113573 := bbase (se 4 (by rfl) ⟨198147, by rfl⟩ : syracuseStep 2113573 = 396295) (by norm_num)
theorem B2818109 : Blo 1877140 2818109 := bbase (se 3 (by rfl) ⟨528395, by rfl⟩ : syracuseStep 2818109 = 1056791) (by norm_num)
theorem B2113609 : Blo 1877140 2113609 := bbase (se 2 (by rfl) ⟨792603, by rfl⟩ : syracuseStep 2113609 = 1585207) (by norm_num)
theorem B2818133 : Blo 1877140 2818133 := bbase (se 8 (by rfl) ⟨16512, by rfl⟩ : syracuseStep 2818133 = 33025) (by norm_num)
theorem B4227173 : Blo 1877140 4227173 := bbase (se 4 (by rfl) ⟨396297, by rfl⟩ : syracuseStep 4227173 = 792595) (by norm_num)
theorem B2818157 : Blo 1877140 2818157 := bbase (se 3 (by rfl) ⟨528404, by rfl⟩ : syracuseStep 2818157 = 1056809) (by norm_num)
theorem B2113645 : Blo 1877140 2113645 := bbase (se 3 (by rfl) ⟨396308, by rfl⟩ : syracuseStep 2113645 = 792617) (by norm_num)
theorem B5349493 : Blo 1877140 5349493 := bbase (se 5 (by rfl) ⟨250757, by rfl⟩ : syracuseStep 5349493 = 501515) (by norm_num)
theorem B2818181 : Blo 1877140 2818181 := bbase (se 4 (by rfl) ⟨264204, by rfl⟩ : syracuseStep 2818181 = 528409) (by norm_num)
theorem B2375821 : Blo 1877140 2375821 := bbase (se 3 (by rfl) ⟨445466, by rfl⟩ : syracuseStep 2375821 = 890933) (by norm_num)
theorem B2113681 : Blo 1877140 2113681 := bbase (se 2 (by rfl) ⟨792630, by rfl⟩ : syracuseStep 2113681 = 1585261) (by norm_num)
theorem B3170461 : Blo 1877140 3170461 := bbase (se 3 (by rfl) ⟨594461, by rfl⟩ : syracuseStep 3170461 = 1188923) (by norm_num)
theorem B2818205 : Blo 1877140 2818205 := bbase (se 3 (by rfl) ⟨528413, by rfl⟩ : syracuseStep 2818205 = 1056827) (by norm_num)
theorem B4227245 : Blo 1877140 4227245 := bbase (se 3 (by rfl) ⟨792608, by rfl⟩ : syracuseStep 4227245 = 1585217) (by norm_num)
theorem B2818229 : Blo 1877140 2818229 := bbase (se 5 (by rfl) ⟨132104, by rfl⟩ : syracuseStep 2818229 = 264209) (by norm_num)
theorem B2113717 : Blo 1877140 2113717 := bbase (se 5 (by rfl) ⟨99080, by rfl⟩ : syracuseStep 2113717 = 198161) (by norm_num)
theorem B2818253 : Blo 1877140 2818253 := bbase (se 3 (by rfl) ⟨528422, by rfl⟩ : syracuseStep 2818253 = 1056845) (by norm_num)
theorem B10698965 : Blo 1877140 10698965 := bbase (se 7 (by rfl) ⟨125378, by rfl⟩ : syracuseStep 10698965 = 250757) (by norm_num)
theorem B2113753 : Blo 1877140 2113753 := bbase (se 2 (by rfl) ⟨792657, by rfl⟩ : syracuseStep 2113753 = 1585315) (by norm_num)
theorem B4751581 : Blo 1877140 4751581 := bbase (se 3 (by rfl) ⟨890921, by rfl⟩ : syracuseStep 4751581 = 1781843) (by norm_num)
theorem B2818277 : Blo 1877140 2818277 := bbase (se 4 (by rfl) ⟨264213, by rfl⟩ : syracuseStep 2818277 = 528427) (by norm_num)
theorem B4227317 : Blo 1877140 4227317 := bbase (se 5 (by rfl) ⟨198155, by rfl⟩ : syracuseStep 4227317 = 396311) (by norm_num)
theorem B3170549 : Blo 1877140 3170549 := bbase (se 5 (by rfl) ⟨148619, by rfl⟩ : syracuseStep 3170549 = 297239) (by norm_num)
theorem B2818301 : Blo 1877140 2818301 := bbase (se 3 (by rfl) ⟨528431, by rfl⟩ : syracuseStep 2818301 = 1056863) (by norm_num)
theorem B2113789 : Blo 1877140 2113789 := bbase (se 3 (by rfl) ⟨396335, by rfl⟩ : syracuseStep 2113789 = 792671) (by norm_num)
theorem B2818325 : Blo 1877140 2818325 := bbase (se 6 (by rfl) ⟨66054, by rfl⟩ : syracuseStep 2818325 = 132109) (by norm_num)
theorem B2113825 : Blo 1877140 2113825 := bbase (se 2 (by rfl) ⟨792684, by rfl⟩ : syracuseStep 2113825 = 1585369) (by norm_num)
theorem B2818349 : Blo 1877140 2818349 := bbase (se 3 (by rfl) ⟨528440, by rfl⟩ : syracuseStep 2818349 = 1056881) (by norm_num)
theorem B2375993 : Blo 1877140 2375993 := bbase (se 2 (by rfl) ⟨890997, by rfl⟩ : syracuseStep 2375993 = 1781995) (by norm_num)
theorem B4227389 : Blo 1877140 4227389 := bbase (se 3 (by rfl) ⟨792635, by rfl⟩ : syracuseStep 4227389 = 1585271) (by norm_num)
theorem B2818373 : Blo 1877140 2818373 := bbase (se 4 (by rfl) ⟨264222, by rfl⟩ : syracuseStep 2818373 = 528445) (by norm_num)
theorem B2113861 : Blo 1877140 2113861 := bbase (se 4 (by rfl) ⟨198174, by rfl⟩ : syracuseStep 2113861 = 396349) (by norm_num)
theorem B4751693 : Blo 1877140 4751693 := bbase (se 3 (by rfl) ⟨890942, by rfl⟩ : syracuseStep 4751693 = 1781885) (by norm_num)
theorem B3211597 : Blo 1877140 3211597 := bbase (se 3 (by rfl) ⟨602174, by rfl⟩ : syracuseStep 3211597 = 1204349) (by norm_num)
theorem B6340949 : Blo 1877140 6340949 := bbase (se 10 (by rfl) ⟨9288, by rfl⟩ : syracuseStep 6340949 = 18577) (by norm_num)
theorem B2818397 : Blo 1877140 2818397 := bbase (se 3 (by rfl) ⟨528449, by rfl⟩ : syracuseStep 2818397 = 1056899) (by norm_num)
theorem B2113897 : Blo 1877140 2113897 := bbase (se 2 (by rfl) ⟨792711, by rfl⟩ : syracuseStep 2113897 = 1585423) (by norm_num)
theorem B3006829 : Blo 1877140 3006829 := bbase (se 3 (by rfl) ⟨563780, by rfl⟩ : syracuseStep 3006829 = 1127561) (by norm_num)
theorem B2376049 : Blo 1877140 2376049 := bbase (se 2 (by rfl) ⟨891018, by rfl⟩ : syracuseStep 2376049 = 1782037) (by norm_num)
theorem B3170677 : Blo 1877140 3170677 := bbase (se 5 (by rfl) ⟨148625, by rfl⟩ : syracuseStep 3170677 = 297251) (by norm_num)
theorem B2818421 : Blo 1877140 2818421 := bbase (se 5 (by rfl) ⟨132113, by rfl⟩ : syracuseStep 2818421 = 264227) (by norm_num)
theorem B4514173 : Blo 1877140 4514173 := bbase (se 3 (by rfl) ⟨846407, by rfl⟩ : syracuseStep 4514173 = 1692815) (by norm_num)
theorem B4227461 : Blo 1877140 4227461 := bbase (se 4 (by rfl) ⟨396324, by rfl⟩ : syracuseStep 4227461 = 792649) (by norm_num)
theorem B2818445 : Blo 1877140 2818445 := bbase (se 3 (by rfl) ⟨528458, by rfl⟩ : syracuseStep 2818445 = 1056917) (by norm_num)
theorem B2113933 : Blo 1877140 2113933 := bbase (se 3 (by rfl) ⟨396362, by rfl⟩ : syracuseStep 2113933 = 792725) (by norm_num)
theorem B2818469 : Blo 1877140 2818469 := bbase (se 4 (by rfl) ⟨264231, by rfl⟩ : syracuseStep 2818469 = 528463) (by norm_num)
theorem B3211693 : Blo 1877140 3211693 := bbase (se 3 (by rfl) ⟨602192, by rfl⟩ : syracuseStep 3211693 = 1204385) (by norm_num)
theorem B2113969 : Blo 1877140 2113969 := bbase (se 2 (by rfl) ⟨792738, by rfl⟩ : syracuseStep 2113969 = 1585477) (by norm_num)
theorem B2818493 : Blo 1877140 2818493 := bbase (se 3 (by rfl) ⟨528467, by rfl⟩ : syracuseStep 2818493 = 1056935) (by norm_num)
theorem B4227533 : Blo 1877140 4227533 := bbase (se 3 (by rfl) ⟨792662, by rfl⟩ : syracuseStep 4227533 = 1585325) (by norm_num)
theorem B3170765 : Blo 1877140 3170765 := bbase (se 3 (by rfl) ⟨594518, by rfl⟩ : syracuseStep 3170765 = 1189037) (by norm_num)
theorem B2376145 : Blo 1877140 2376145 := bbase (se 2 (by rfl) ⟨891054, by rfl⟩ : syracuseStep 2376145 = 1782109) (by norm_num)
theorem B3211733 : Blo 1877140 3211733 := bbase (se 7 (by rfl) ⟨37637, by rfl⟩ : syracuseStep 3211733 = 75275) (by norm_num)
theorem B2818517 : Blo 1877140 2818517 := bbase (se 7 (by rfl) ⟨33029, by rfl⟩ : syracuseStep 2818517 = 66059) (by norm_num)
theorem B2114005 : Blo 1877140 2114005 := bbase (se 7 (by rfl) ⟨24773, by rfl⟩ : syracuseStep 2114005 = 49547) (by norm_num)
theorem B3564013 : Blo 1877140 3564013 := bbase (se 3 (by rfl) ⟨668252, by rfl⟩ : syracuseStep 3564013 = 1336505) (by norm_num)
theorem B2818541 : Blo 1877140 2818541 := bbase (se 3 (by rfl) ⟨528476, by rfl⟩ : syracuseStep 2818541 = 1056953) (by norm_num)
theorem B2818565 : Blo 1877140 2818565 := bbase (se 4 (by rfl) ⟨264240, by rfl⟩ : syracuseStep 2818565 = 528481) (by norm_num)
theorem B4751885 : Blo 1877140 4751885 := bbase (se 3 (by rfl) ⟨890978, by rfl⟩ : syracuseStep 4751885 = 1781957) (by norm_num)
theorem B4227605 : Blo 1877140 4227605 := bbase (se 6 (by rfl) ⟨99084, by rfl⟩ : syracuseStep 4227605 = 198169) (by norm_num)
theorem B2818589 : Blo 1877140 2818589 := bbase (se 3 (by rfl) ⟨528485, by rfl⟩ : syracuseStep 2818589 = 1056971) (by norm_num)
theorem B2818613 : Blo 1877140 2818613 := bbase (se 5 (by rfl) ⟨132122, by rfl⟩ : syracuseStep 2818613 = 264245) (by norm_num)
theorem B8020549 : Blo 1877140 8020549 := bbase (se 4 (by rfl) ⟨751926, by rfl⟩ : syracuseStep 8020549 = 1503853) (by norm_num)
theorem B3170893 : Blo 1877140 3170893 := bbase (se 3 (by rfl) ⟨594542, by rfl⟩ : syracuseStep 3170893 = 1189085) (by norm_num)
theorem B2818637 : Blo 1877140 2818637 := bbase (se 3 (by rfl) ⟨528494, by rfl⟩ : syracuseStep 2818637 = 1056989) (by norm_num)
theorem B4227677 : Blo 1877140 4227677 := bbase (se 3 (by rfl) ⟨792689, by rfl⟩ : syracuseStep 4227677 = 1585379) (by norm_num)
theorem B2818661 : Blo 1877140 2818661 := bbase (se 4 (by rfl) ⟨264249, by rfl⟩ : syracuseStep 2818661 = 528499) (by norm_num)
theorem B3564157 : Blo 1877140 3564157 := bbase (se 3 (by rfl) ⟨668279, by rfl⟩ : syracuseStep 3564157 = 1336559) (by norm_num)
theorem B2376317 : Blo 1877140 2376317 := bbase (se 3 (by rfl) ⟨445559, by rfl⟩ : syracuseStep 2376317 = 891119) (by norm_num)
theorem B2818685 : Blo 1877140 2818685 := bbase (se 3 (by rfl) ⟨528503, by rfl⟩ : syracuseStep 2818685 = 1057007) (by norm_num)
theorem B2818709 : Blo 1877140 2818709 := bbase (se 6 (by rfl) ⟨66063, by rfl⟩ : syracuseStep 2818709 = 132127) (by norm_num)
theorem B4227749 : Blo 1877140 4227749 := bbase (se 4 (by rfl) ⟨396351, by rfl⟩ : syracuseStep 4227749 = 792703) (by norm_num)
theorem B3170981 : Blo 1877140 3170981 := bbase (se 4 (by rfl) ⟨297279, by rfl⟩ : syracuseStep 3170981 = 594559) (by norm_num)
theorem B2376373 : Blo 1877140 2376373 := bbase (se 5 (by rfl) ⟨111392, by rfl⟩ : syracuseStep 2376373 = 222785) (by norm_num)
theorem B2474725 : Blo 1877140 2474725 := bbase (se 4 (by rfl) ⟨232005, by rfl⟩ : syracuseStep 2474725 = 464011) (by norm_num)
theorem B4227821 : Blo 1877140 4227821 := bbase (se 3 (by rfl) ⟨792716, by rfl⟩ : syracuseStep 4227821 = 1585433) (by norm_num)
theorem B7127797 : Blo 1877140 7127797 := bbase (se 5 (by rfl) ⟨334115, by rfl⟩ : syracuseStep 7127797 = 668231) (by norm_num)
theorem B6341381 : Blo 1877140 6341381 := bbase (se 4 (by rfl) ⟨594504, by rfl⟩ : syracuseStep 6341381 = 1189009) (by norm_num)
theorem B2376469 : Blo 1877140 2376469 := bbase (se 6 (by rfl) ⟨55698, by rfl⟩ : syracuseStep 2376469 = 111397) (by norm_num)
theorem B3564317 : Blo 1877140 3564317 := bbase (se 3 (by rfl) ⟨668309, by rfl⟩ : syracuseStep 3564317 = 1336619) (by norm_num)
theorem B4227893 : Blo 1877140 4227893 := bbase (se 5 (by rfl) ⟨198182, by rfl⟩ : syracuseStep 4227893 = 396365) (by norm_num)
theorem B4752229 : Blo 1877140 4752229 := bbase (se 4 (by rfl) ⟨445521, by rfl⟩ : syracuseStep 4752229 = 891043) (by norm_num)
theorem B4227965 : Blo 1877140 4227965 := bbase (se 3 (by rfl) ⟨792743, by rfl⟩ : syracuseStep 4227965 = 1585487) (by norm_num)
theorem B3007373 : Blo 1877140 3007373 := bbase (se 3 (by rfl) ⟨563882, by rfl⟩ : syracuseStep 3007373 = 1127765) (by norm_num)
theorem B4285325 : Blo 1877140 4285325 := bbase (se 3 (by rfl) ⟨803498, by rfl⟩ : syracuseStep 4285325 = 1606997) (by norm_num)
theorem B9511829 : Blo 1877140 9511829 := bbase (se 6 (by rfl) ⟨222933, by rfl⟩ : syracuseStep 9511829 = 445867) (by norm_num)
theorem B3564461 : Blo 1877140 3564461 := bbase (se 3 (by rfl) ⟨668336, by rfl⟩ : syracuseStep 3564461 = 1336673) (by norm_num)
theorem B2376641 : Blo 1877140 2376641 := bbase (se 2 (by rfl) ⟨891240, by rfl⟩ : syracuseStep 2376641 = 1782481) (by norm_num)
theorem B4228037 : Blo 1877140 4228037 := bbase (se 4 (by rfl) ⟨396378, by rfl⟩ : syracuseStep 4228037 = 792757) (by norm_num)
theorem B4752341 : Blo 1877140 4752341 := bbase (se 7 (by rfl) ⟨55691, by rfl⟩ : syracuseStep 4752341 = 111383) (by norm_num)
theorem B2409437 : Blo 1877140 2409437 := bbase (se 3 (by rfl) ⟨451769, by rfl⟩ : syracuseStep 2409437 = 903539) (by norm_num)
theorem B2376697 : Blo 1877140 2376697 := bbase (se 2 (by rfl) ⟨891261, by rfl⟩ : syracuseStep 2376697 = 1782523) (by norm_num)
theorem B7128101 : Blo 1877140 7128101 := bbase (se 4 (by rfl) ⟨668259, by rfl⟩ : syracuseStep 7128101 = 1336519) (by norm_num)
theorem B2376793 : Blo 1877140 2376793 := bbase (se 2 (by rfl) ⟨891297, by rfl⟩ : syracuseStep 2376793 = 1782595) (by norm_num)
theorem B4752533 : Blo 1877140 4752533 := bbase (se 6 (by rfl) ⟨111387, by rfl⟩ : syracuseStep 4752533 = 222775) (by norm_num)
theorem B6341813 : Blo 1877140 6341813 := bbase (se 5 (by rfl) ⟨297272, by rfl⟩ : syracuseStep 6341813 = 594545) (by norm_num)
theorem B3564749 : Blo 1877140 3564749 := bbase (se 3 (by rfl) ⟨668390, by rfl⟩ : syracuseStep 3564749 = 1336781) (by norm_num)
theorem B2376965 : Blo 1877140 2376965 := bbase (se 4 (by rfl) ⟨222840, by rfl⟩ : syracuseStep 2376965 = 445681) (by norm_num)
theorem B3212549 : Blo 1877140 3212549 := bbase (se 4 (by rfl) ⟨301176, by rfl⟩ : syracuseStep 3212549 = 602353) (by norm_num)
theorem B4818197 : Blo 1877140 4818197 := bbase (se 6 (by rfl) ⟨112926, by rfl⟩ : syracuseStep 4818197 = 225853) (by norm_num)
theorem B9504053 : Blo 1877140 9504053 := bbase (se 5 (by rfl) ⟨445502, by rfl⟩ : syracuseStep 9504053 = 891005) (by norm_num)
theorem B2377021 : Blo 1877140 2377021 := bbase (se 3 (by rfl) ⟨445691, by rfl⟩ : syracuseStep 2377021 = 891383) (by norm_num)
theorem B3564901 : Blo 1877140 3564901 := bbase (se 4 (by rfl) ⟨334209, by rfl⟩ : syracuseStep 3564901 = 668419) (by norm_num)
theorem B2377117 : Blo 1877140 2377117 := bbase (se 3 (by rfl) ⟨445709, by rfl⟩ : syracuseStep 2377117 = 891419) (by norm_num)
theorem B3007925 : Blo 1877140 3007925 := bbase (se 5 (by rfl) ⟨140996, by rfl⟩ : syracuseStep 3007925 = 281993) (by norm_num)
theorem B3007957 : Blo 1877140 3007957 := bbase (se 7 (by rfl) ⟨35249, by rfl⟩ : syracuseStep 3007957 = 70499) (by norm_num)
theorem B4752877 : Blo 1877140 4752877 := bbase (se 3 (by rfl) ⟨891164, by rfl⟩ : syracuseStep 4752877 = 1782329) (by norm_num)
theorem B9020965 : Blo 1877140 9020965 := bbase (se 4 (by rfl) ⟨845715, by rfl⟩ : syracuseStep 9020965 = 1691431) (by norm_num)
theorem B2377289 : Blo 1877140 2377289 := bbase (se 2 (by rfl) ⟨891483, by rfl⟩ : syracuseStep 2377289 = 1782967) (by norm_num)
theorem B5350997 : Blo 1877140 5350997 := bbase (se 8 (by rfl) ⟨31353, by rfl⟩ : syracuseStep 5350997 = 62707) (by norm_num)
theorem B4752989 : Blo 1877140 4752989 := bbase (se 3 (by rfl) ⟨891185, by rfl⟩ : syracuseStep 4752989 = 1782371) (by norm_num)
theorem B2377345 : Blo 1877140 2377345 := bbase (se 2 (by rfl) ⟨891504, by rfl⟩ : syracuseStep 2377345 = 1783009) (by norm_num)
theorem B3565205 : Blo 1877140 3565205 := bbase (se 6 (by rfl) ⟨83559, by rfl⟩ : syracuseStep 3565205 = 167119) (by norm_num)
theorem B9029269 : Blo 1877140 9029269 := bbase (se 6 (by rfl) ⟨211623, by rfl⟩ : syracuseStep 9029269 = 423247) (by norm_num)
theorem B6014645 : Blo 1877140 6014645 := bbase (se 5 (by rfl) ⟨281936, by rfl⟩ : syracuseStep 6014645 = 563873) (by norm_num)
theorem B2377441 : Blo 1877140 2377441 := bbase (se 2 (by rfl) ⟨891540, by rfl⟩ : syracuseStep 2377441 = 1783081) (by norm_num)
theorem B4343549 : Blo 1877140 4343549 := bbase (se 3 (by rfl) ⟨814415, by rfl⟩ : syracuseStep 4343549 = 1628831) (by norm_num)
theorem B4753181 : Blo 1877140 4753181 := bbase (se 3 (by rfl) ⟨891221, by rfl⟩ : syracuseStep 4753181 = 1782443) (by norm_num)
theorem B87934805 : Blo 1877140 87934805 := bbase (se 9 (by rfl) ⟨257621, by rfl⟩ : syracuseStep 87934805 = 515243) (by norm_num)
theorem B3614557 : Blo 1877140 3614557 := bbase (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) (by norm_num)
theorem B9144181 : Blo 1877140 9144181 := bbase (se 5 (by rfl) ⟨428633, by rfl⟩ : syracuseStep 9144181 = 857267) (by norm_num)
theorem B6096757 : Blo 1877140 6096757 := bbase (se 5 (by rfl) ⟨285785, by rfl⟩ : syracuseStep 6096757 = 571571) (by norm_num)
theorem B2377613 : Blo 1877140 2377613 := bbase (se 3 (by rfl) ⟨445802, by rfl⟩ : syracuseStep 2377613 = 891605) (by norm_num)
theorem B2377669 : Blo 1877140 2377669 := bbase (se 4 (by rfl) ⟨222906, by rfl⟩ : syracuseStep 2377669 = 445813) (by norm_num)
theorem B12036053 : Blo 1877140 12036053 := bbase (se 7 (by rfl) ⟨141047, by rfl⟩ : syracuseStep 12036053 = 282095) (by norm_num)
theorem B8022037 : Blo 1877140 8022037 := bbase (se 6 (by rfl) ⟨188016, by rfl⟩ : syracuseStep 8022037 = 376033) (by norm_num)
theorem B8022053 : Blo 1877140 8022053 := bbase (se 4 (by rfl) ⟨752067, by rfl⟩ : syracuseStep 8022053 = 1504135) (by norm_num)
theorem B2377765 : Blo 1877140 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B4753525 : Blo 1877140 4753525 := bbase (se 5 (by rfl) ⟨222821, by rfl⟩ : syracuseStep 4753525 = 445643) (by norm_num)
theorem B9513125 : Blo 1877140 9513125 := bbase (se 4 (by rfl) ⟨891855, by rfl⟩ : syracuseStep 9513125 = 1783711) (by norm_num)
theorem B2377937 : Blo 1877140 2377937 := bbase (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) (by norm_num)
theorem B4753637 : Blo 1877140 4753637 := bbase (se 4 (by rfl) ⟨445653, by rfl⟩ : syracuseStep 4753637 = 891307) (by norm_num)
theorem B1902857 : Blo 1877140 1902857 := bbase (se 2 (by rfl) ⟨713571, by rfl⟩ : syracuseStep 1902857 = 1427143) (by norm_num)
theorem B2377993 : Blo 1877140 2377993 := bbase (se 2 (by rfl) ⟨891747, by rfl⟩ : syracuseStep 2377993 = 1783495) (by norm_num)
theorem B2378089 : Blo 1877140 2378089 := bbase (se 2 (by rfl) ⟨891783, by rfl⟩ : syracuseStep 2378089 = 1783567) (by norm_num)
theorem B2255213 : Blo 1877140 2255213 := bbase (se 3 (by rfl) ⟨422852, by rfl⟩ : syracuseStep 2255213 = 845705) (by norm_num)
theorem B3008885 : Blo 1877140 3008885 := bbase (se 5 (by rfl) ⟨141041, by rfl⟩ : syracuseStep 3008885 = 282083) (by norm_num)
theorem B10701173 : Blo 1877140 10701173 := bbase (se 5 (by rfl) ⟨501617, by rfl⟩ : syracuseStep 10701173 = 1003235) (by norm_num)
theorem B3565957 : Blo 1877140 3565957 := bbase (se 4 (by rfl) ⟨334308, by rfl⟩ : syracuseStep 3565957 = 668617) (by norm_num)
theorem B4753829 : Blo 1877140 4753829 := bbase (se 4 (by rfl) ⟨445671, by rfl⟩ : syracuseStep 4753829 = 891343) (by norm_num)
theorem B2673101 : Blo 1877140 2673101 := bbase (se 3 (by rfl) ⟨501206, by rfl⟩ : syracuseStep 2673101 = 1002413) (by norm_num)
theorem B7227877 : Blo 1877140 7227877 := bbase (se 4 (by rfl) ⟨677613, by rfl⟩ : syracuseStep 7227877 = 1355227) (by norm_num)
theorem B3566101 : Blo 1877140 3566101 := bbase (se 6 (by rfl) ⟨83580, by rfl⟩ : syracuseStep 3566101 = 167161) (by norm_num)
theorem B2378261 : Blo 1877140 2378261 := bbase (se 6 (by rfl) ⟨55740, by rfl⟩ : syracuseStep 2378261 = 111481) (by norm_num)
theorem B6015541 : Blo 1877140 6015541 := bbase (se 5 (by rfl) ⟨281978, by rfl⟩ : syracuseStep 6015541 = 563957) (by norm_num)
theorem B9505349 : Blo 1877140 9505349 := bbase (se 4 (by rfl) ⟨891126, by rfl⟩ : syracuseStep 9505349 = 1782253) (by norm_num)
theorem B2255521 : Blo 1877140 2255521 := bbase (se 2 (by rfl) ⟨845820, by rfl⟩ : syracuseStep 2255521 = 1691641) (by norm_num)
theorem B3566261 : Blo 1877140 3566261 := bbase (se 5 (by rfl) ⟨167168, by rfl⟩ : syracuseStep 3566261 = 334337) (by norm_num)
theorem B4754173 : Blo 1877140 4754173 := bbase (se 3 (by rfl) ⟨891407, by rfl⟩ : syracuseStep 4754173 = 1782815) (by norm_num)
theorem B3566405 : Blo 1877140 3566405 := bbase (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) (by norm_num)
theorem B4754285 : Blo 1877140 4754285 := bbase (se 3 (by rfl) ⟨891428, by rfl⟩ : syracuseStep 4754285 = 1782857) (by norm_num)
theorem B2255737 : Blo 1877140 2255737 := bbase (se 2 (by rfl) ⟨845901, by rfl⟩ : syracuseStep 2255737 = 1691803) (by norm_num)
theorem B24054677 : Blo 1877140 24054677 := bbase (se 6 (by rfl) ⟨563781, by rfl⟩ : syracuseStep 24054677 = 1127563) (by norm_num)
theorem B4066237 : Blo 1877140 4066237 := bbase (se 3 (by rfl) ⟨762419, by rfl⟩ : syracuseStep 4066237 = 1524839) (by norm_num)
theorem B2673653 : Blo 1877140 2673653 := bbase (se 5 (by rfl) ⟨125327, by rfl⟩ : syracuseStep 2673653 = 250655) (by norm_num)
theorem B3009565 : Blo 1877140 3009565 := bbase (se 3 (by rfl) ⟨564293, by rfl⟩ : syracuseStep 3009565 = 1128587) (by norm_num)
theorem B4754477 : Blo 1877140 4754477 := bbase (se 3 (by rfl) ⟨891464, by rfl⟩ : syracuseStep 4754477 = 1782929) (by norm_num)
theorem B9767989 : Blo 1877140 9767989 := bbase (se 5 (by rfl) ⟨457874, by rfl⟩ : syracuseStep 9767989 = 915749) (by norm_num)
theorem B3009629 : Blo 1877140 3009629 := bbase (se 3 (by rfl) ⟨564305, by rfl⟩ : syracuseStep 3009629 = 1128611) (by norm_num)
theorem B7130213 : Blo 1877140 7130213 := bbase (se 4 (by rfl) ⟨668457, by rfl⟩ : syracuseStep 7130213 = 1336915) (by norm_num)
theorem B3566693 : Blo 1877140 3566693 := bbase (se 4 (by rfl) ⟨334377, by rfl⟩ : syracuseStep 3566693 = 668755) (by norm_num)
theorem B13544597 : Blo 1877140 13544597 := bbase (se 6 (by rfl) ⟨317451, by rfl⟩ : syracuseStep 13544597 = 634903) (by norm_num)
theorem B2256049 : Blo 1877140 2256049 := bbase (se 2 (by rfl) ⟨846018, by rfl⟩ : syracuseStep 2256049 = 1692037) (by norm_num)
theorem B14265557 : Blo 1877140 14265557 := bbase (se 7 (by rfl) ⟨167174, by rfl⟩ : syracuseStep 14265557 = 334349) (by norm_num)
theorem B4009181 : Blo 1877140 4009181 := bbase (se 3 (by rfl) ⟨751721, by rfl⟩ : syracuseStep 4009181 = 1503443) (by norm_num)
theorem B12201205 : Blo 1877140 12201205 := bbase (se 5 (by rfl) ⟨571931, by rfl⟩ : syracuseStep 12201205 = 1143863) (by norm_num)
theorem B3566845 : Blo 1877140 3566845 := bbase (se 3 (by rfl) ⟨668783, by rfl⟩ : syracuseStep 3566845 = 1337567) (by norm_num)
theorem B6335765 : Blo 1877140 6335765 := bbase (se 6 (by rfl) ⟨148494, by rfl⟩ : syracuseStep 6335765 = 296989) (by norm_num)
theorem B16043285 : Blo 1877140 16043285 := bbase (se 6 (by rfl) ⟨376014, by rfl⟩ : syracuseStep 16043285 = 752029) (by norm_num)
theorem B9637157 : Blo 1877140 9637157 := bbase (se 4 (by rfl) ⟨903483, by rfl⟩ : syracuseStep 9637157 = 1806967) (by norm_num)
theorem B2895173 : Blo 1877140 2895173 := bbase (se 4 (by rfl) ⟨271422, by rfl⟩ : syracuseStep 2895173 = 542845) (by norm_num)
theorem B7130501 : Blo 1877140 7130501 := bbase (se 4 (by rfl) ⟨668484, by rfl⟩ : syracuseStep 7130501 = 1336969) (by norm_num)
theorem B4754821 : Blo 1877140 4754821 := bbase (se 4 (by rfl) ⟨445764, by rfl⟩ : syracuseStep 4754821 = 891529) (by norm_num)
theorem B4009421 : Blo 1877140 4009421 := bbase (se 3 (by rfl) ⟨751766, by rfl⟩ : syracuseStep 4009421 = 1503533) (by norm_num)
theorem B3476957 : Blo 1877140 3476957 := bbase (se 3 (by rfl) ⟨651929, by rfl⟩ : syracuseStep 3476957 = 1303859) (by norm_num)
theorem B2141677 : Blo 1877140 2141677 := bbase (se 3 (by rfl) ⟨401564, by rfl⟩ : syracuseStep 2141677 = 803129) (by norm_num)
theorem B4754933 : Blo 1877140 4754933 := bbase (se 5 (by rfl) ⟨222887, by rfl⟩ : syracuseStep 4754933 = 445775) (by norm_num)
theorem B3567149 : Blo 1877140 3567149 := bbase (se 3 (by rfl) ⟨668840, by rfl⟩ : syracuseStep 3567149 = 1337681) (by norm_num)
theorem B4951637 : Blo 1877140 4951637 := bbase (se 8 (by rfl) ⟨29013, by rfl⟩ : syracuseStep 4951637 = 58027) (by norm_num)
theorem B14257781 : Blo 1877140 14257781 := bbase (se 5 (by rfl) ⟨668333, by rfl⟩ : syracuseStep 14257781 = 1336667) (by norm_num)
theorem B4755125 : Blo 1877140 4755125 := bbase (se 5 (by rfl) ⟨222896, by rfl⟩ : syracuseStep 4755125 = 445793) (by norm_num)
theorem B6336197 : Blo 1877140 6336197 := bbase (se 4 (by rfl) ⟨594018, by rfl⟩ : syracuseStep 6336197 = 1188037) (by norm_num)
theorem B2674405 : Blo 1877140 2674405 := bbase (se 4 (by rfl) ⟨250725, by rfl⟩ : syracuseStep 2674405 = 501451) (by norm_num)
theorem B1904369 : Blo 1877140 1904369 := bbase (se 2 (by rfl) ⟨714138, by rfl⟩ : syracuseStep 1904369 = 1428277) (by norm_num)
theorem B1904393 : Blo 1877140 1904393 := bbase (se 2 (by rfl) ⟨714147, by rfl⟩ : syracuseStep 1904393 = 1428295) (by norm_num)
theorem B1904401 : Blo 1877140 1904401 := bbase (se 2 (by rfl) ⟨714150, by rfl⟩ : syracuseStep 1904401 = 1428301) (by norm_num)
theorem B9506645 : Blo 1877140 9506645 := bbase (se 9 (by rfl) ⟨27851, by rfl⟩ : syracuseStep 9506645 = 55703) (by norm_num)
theorem B4575061 : Blo 1877140 4575061 := bbase (se 9 (by rfl) ⟨13403, by rfl⟩ : syracuseStep 4575061 = 26807) (by norm_num)
theorem B1929085 : Blo 1877140 1929085 := bbase (se 3 (by rfl) ⟨361703, by rfl⟩ : syracuseStep 1929085 = 723407) (by norm_num)
theorem B4820885 : Blo 1877140 4820885 := bbase (se 6 (by rfl) ⟨112989, by rfl⟩ : syracuseStep 4820885 = 225979) (by norm_num)
theorem B4009925 : Blo 1877140 4009925 := bbase (se 4 (by rfl) ⟨375930, by rfl⟩ : syracuseStep 4009925 = 751861) (by norm_num)
theorem B9637829 : Blo 1877140 9637829 := bbase (se 4 (by rfl) ⟨903546, by rfl⟩ : syracuseStep 9637829 = 1807093) (by norm_num)
theorem B4009933 : Blo 1877140 4009933 := bbase (se 3 (by rfl) ⟨751862, by rfl⟩ : syracuseStep 4009933 = 1503725) (by norm_num)
theorem B4755469 : Blo 1877140 4755469 := bbase (se 3 (by rfl) ⟨891650, by rfl⟩ : syracuseStep 4755469 = 1783301) (by norm_num)
theorem B2854997 : Blo 1877140 2854997 := bbase (se 8 (by rfl) ⟨16728, by rfl⟩ : syracuseStep 2854997 = 33457) (by norm_num)
theorem B6336629 : Blo 1877140 6336629 := bbase (se 5 (by rfl) ⟨297029, by rfl⟩ : syracuseStep 6336629 = 594059) (by norm_num)
theorem B4755581 : Blo 1877140 4755581 := bbase (se 3 (by rfl) ⟨891671, by rfl⟩ : syracuseStep 4755581 = 1783343) (by norm_num)
theorem B2855045 : Blo 1877140 2855045 := bbase (se 4 (by rfl) ⟨267660, by rfl⟩ : syracuseStep 2855045 = 535321) (by norm_num)
theorem B2855069 : Blo 1877140 2855069 := bbase (se 3 (by rfl) ⟨535325, by rfl⟩ : syracuseStep 2855069 = 1070651) (by norm_num)
theorem B1929377 : Blo 1877140 1929377 := bbase (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) (by norm_num)
theorem B5714117 : Blo 1877140 5714117 := bbase (se 4 (by rfl) ⟨535698, by rfl⟩ : syracuseStep 5714117 = 1071397) (by norm_num)
theorem B8024309 : Blo 1877140 8024309 := bbase (se 5 (by rfl) ⟨376139, by rfl⟩ : syracuseStep 8024309 = 752279) (by norm_num)
theorem B5075237 : Blo 1877140 5075237 := bbase (se 4 (by rfl) ⟨475803, by rfl⟩ : syracuseStep 5075237 = 951607) (by norm_num)
theorem B4755773 : Blo 1877140 4755773 := bbase (se 3 (by rfl) ⟨891707, by rfl⟩ : syracuseStep 4755773 = 1783415) (by norm_num)
theorem B5345621 : Blo 1877140 5345621 := bbase (se 10 (by rfl) ⟨7830, by rfl⟩ : syracuseStep 5345621 = 15661) (by norm_num)
theorem B2675197 : Blo 1877140 2675197 := bbase (se 3 (by rfl) ⟨501599, by rfl⟩ : syracuseStep 2675197 = 1003199) (by norm_num)
theorem B6337061 : Blo 1877140 6337061 := bbase (se 4 (by rfl) ⟨594099, by rfl⟩ : syracuseStep 6337061 = 1188199) (by norm_num)
theorem B7131685 : Blo 1877140 7131685 := bbase (se 4 (by rfl) ⟨668595, by rfl⟩ : syracuseStep 7131685 = 1337191) (by norm_num)
theorem B2142761 : Blo 1877140 2142761 := bbase (se 2 (by rfl) ⟨803535, by rfl⟩ : syracuseStep 2142761 = 1607071) (by norm_num)
theorem B6427189 : Blo 1877140 6427189 := bbase (se 5 (by rfl) ⟨301274, by rfl⟩ : syracuseStep 6427189 = 602549) (by norm_num)
theorem B4223573 : Blo 1877140 4223573 := bbase (se 8 (by rfl) ⟨24747, by rfl⟩ : syracuseStep 4223573 = 49495) (by norm_num)
theorem B11424341 : Blo 1877140 11424341 := bbase (se 8 (by rfl) ⟨66939, by rfl⟩ : syracuseStep 11424341 = 133879) (by norm_num)
theorem B4756117 : Blo 1877140 4756117 := bbase (se 6 (by rfl) ⟨111471, by rfl⟩ : syracuseStep 4756117 = 222943) (by norm_num)
theorem B4223645 : Blo 1877140 4223645 := bbase (se 3 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 4223645 = 1583867) (by norm_num)
theorem B4223717 : Blo 1877140 4223717 := bbase (se 4 (by rfl) ⟨395973, by rfl⟩ : syracuseStep 4223717 = 791947) (by norm_num)
theorem B7615237 : Blo 1877140 7615237 := bbase (se 4 (by rfl) ⟨713928, by rfl⟩ : syracuseStep 7615237 = 1427857) (by norm_num)
theorem B6427397 : Blo 1877140 6427397 := bbase (se 4 (by rfl) ⟨602568, by rfl⟩ : syracuseStep 6427397 = 1205137) (by norm_num)
theorem B4756229 : Blo 1877140 4756229 := bbase (se 4 (by rfl) ⟨445896, by rfl⟩ : syracuseStep 4756229 = 891793) (by norm_num)
theorem B2855701 : Blo 1877140 2855701 := bbase (se 6 (by rfl) ⟨66930, by rfl⟩ : syracuseStep 2855701 = 133861) (by norm_num)
theorem B4223789 : Blo 1877140 4223789 := bbase (se 3 (by rfl) ⟨791960, by rfl⟩ : syracuseStep 4223789 = 1583921) (by norm_num)
theorem B2675533 : Blo 1877140 2675533 := bbase (se 3 (by rfl) ⟨501662, by rfl⟩ : syracuseStep 2675533 = 1003325) (by norm_num)
theorem B7131989 : Blo 1877140 7131989 := bbase (se 9 (by rfl) ⟨20894, by rfl⟩ : syracuseStep 7131989 = 41789) (by norm_num)
theorem B3806045 : Blo 1877140 3806045 := bbase (se 3 (by rfl) ⟨713633, by rfl⟩ : syracuseStep 3806045 = 1427267) (by norm_num)
theorem B4223861 : Blo 1877140 4223861 := bbase (se 5 (by rfl) ⟨197993, by rfl⟩ : syracuseStep 4223861 = 395987) (by norm_num)
theorem B4510637 : Blo 1877140 4510637 := bbase (se 3 (by rfl) ⟨845744, by rfl⟩ : syracuseStep 4510637 = 1691489) (by norm_num)
theorem B4223933 : Blo 1877140 4223933 := bbase (se 3 (by rfl) ⟨791987, by rfl⟩ : syracuseStep 4223933 = 1583975) (by norm_num)
theorem B4756421 : Blo 1877140 4756421 := bbase (se 4 (by rfl) ⟨445914, by rfl⟩ : syracuseStep 4756421 = 891829) (by norm_num)
theorem B6337493 : Blo 1877140 6337493 := bbase (se 7 (by rfl) ⟨74267, by rfl⟩ : syracuseStep 6337493 = 148535) (by norm_num)
theorem B4224005 : Blo 1877140 4224005 := bbase (se 4 (by rfl) ⟨396000, by rfl⟩ : syracuseStep 4224005 = 792001) (by norm_num)
theorem B4510733 : Blo 1877140 4510733 := bbase (se 3 (by rfl) ⟨845762, by rfl⟩ : syracuseStep 4510733 = 1691525) (by norm_num)
theorem B4011061 : Blo 1877140 4011061 := bbase (se 5 (by rfl) ⟨188018, by rfl⟩ : syracuseStep 4011061 = 376037) (by norm_num)
theorem B4224077 : Blo 1877140 4224077 := bbase (se 3 (by rfl) ⟨792014, by rfl⟩ : syracuseStep 4224077 = 1584029) (by norm_num)
theorem B4576349 : Blo 1877140 4576349 := bbase (se 3 (by rfl) ⟨858065, by rfl⟩ : syracuseStep 4576349 = 1716131) (by norm_num)
theorem B9507941 : Blo 1877140 9507941 := bbase (se 4 (by rfl) ⟨891369, by rfl⟩ : syracuseStep 9507941 = 1782739) (by norm_num)
theorem B10695797 : Blo 1877140 10695797 := bbase (se 5 (by rfl) ⟨501365, by rfl⟩ : syracuseStep 10695797 = 1002731) (by norm_num)
theorem B4224149 : Blo 1877140 4224149 := bbase (se 6 (by rfl) ⟨99003, by rfl⟩ : syracuseStep 4224149 = 198007) (by norm_num)
theorem B4224221 : Blo 1877140 4224221 := bbase (se 3 (by rfl) ⟨792041, by rfl⟩ : syracuseStep 4224221 = 1584083) (by norm_num)
theorem B4224293 : Blo 1877140 4224293 := bbase (se 4 (by rfl) ⟨396027, by rfl⟩ : syracuseStep 4224293 = 792055) (by norm_num)
theorem B4224365 : Blo 1877140 4224365 := bbase (se 3 (by rfl) ⟨792068, by rfl⟩ : syracuseStep 4224365 = 1584137) (by norm_num)
theorem B18052469 : Blo 1877140 18052469 := bbase (se 5 (by rfl) ⟨846209, by rfl⟩ : syracuseStep 18052469 = 1692419) (by norm_num)
theorem B6337925 : Blo 1877140 6337925 := bbase (se 4 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 6337925 = 1188361) (by norm_num)
theorem B6018437 : Blo 1877140 6018437 := bbase (se 4 (by rfl) ⟨564228, by rfl⟩ : syracuseStep 6018437 = 1128457) (by norm_num)
theorem B4011437 : Blo 1877140 4011437 := bbase (se 3 (by rfl) ⟨752144, by rfl⟩ : syracuseStep 4011437 = 1504289) (by norm_num)
theorem B4224437 : Blo 1877140 4224437 := bbase (se 5 (by rfl) ⟨198020, by rfl⟩ : syracuseStep 4224437 = 396041) (by norm_num)
theorem B9024965 : Blo 1877140 9024965 := bbase (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) (by norm_num)
theorem B5346805 : Blo 1877140 5346805 := bbase (se 5 (by rfl) ⟨250631, by rfl⟩ : syracuseStep 5346805 = 501263) (by norm_num)
theorem B3167741 : Blo 1877140 3167741 := bbase (se 3 (by rfl) ⟨593951, by rfl⟩ : syracuseStep 3167741 = 1187903) (by norm_num)
theorem B4224509 : Blo 1877140 4224509 := bbase (se 3 (by rfl) ⟨792095, by rfl⟩ : syracuseStep 4224509 = 1584191) (by norm_num)
theorem B2856493 : Blo 1877140 2856493 := bbase (se 3 (by rfl) ⟨535592, by rfl⟩ : syracuseStep 2856493 = 1071185) (by norm_num)
theorem B4224581 : Blo 1877140 4224581 := bbase (se 4 (by rfl) ⟨396054, by rfl⟩ : syracuseStep 4224581 = 792109) (by norm_num)
theorem B3167869 : Blo 1877140 3167869 := bbase (se 3 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 3167869 = 1187951) (by norm_num)
theorem B9025157 : Blo 1877140 9025157 := bbase (se 4 (by rfl) ⟨846108, by rfl⟩ : syracuseStep 9025157 = 1692217) (by norm_num)
theorem B4224653 : Blo 1877140 4224653 := bbase (se 3 (by rfl) ⟨792122, by rfl⟩ : syracuseStep 4224653 = 1584245) (by norm_num)
theorem B2004625 : Blo 1877140 2004625 := bbase (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) (by norm_num)
theorem B5346965 : Blo 1877140 5346965 := bbase (se 6 (by rfl) ⟨125319, by rfl⟩ : syracuseStep 5346965 = 250639) (by norm_num)
theorem B2537125 : Blo 1877140 2537125 := bbase (se 4 (by rfl) ⟨237855, by rfl⟩ : syracuseStep 2537125 = 475711) (by norm_num)
theorem B3167957 : Blo 1877140 3167957 := bbase (se 7 (by rfl) ⟨37124, by rfl⟩ : syracuseStep 3167957 = 74249) (by norm_num)
theorem B4224725 : Blo 1877140 4224725 := bbase (se 7 (by rfl) ⟨49508, by rfl⟩ : syracuseStep 4224725 = 99017) (by norm_num)
theorem B2815733 : Blo 1877140 2815733 := bbase (se 5 (by rfl) ⟨131987, by rfl⟩ : syracuseStep 2815733 = 263975) (by norm_num)
theorem B2815757 : Blo 1877140 2815757 := bbase (se 3 (by rfl) ⟨527954, by rfl⟩ : syracuseStep 2815757 = 1055909) (by norm_num)
theorem B2537245 : Blo 1877140 2537245 := bbase (se 3 (by rfl) ⟨475733, by rfl⟩ : syracuseStep 2537245 = 951467) (by norm_num)
theorem B4224797 : Blo 1877140 4224797 := bbase (se 3 (by rfl) ⟨792149, by rfl⟩ : syracuseStep 4224797 = 1584299) (by norm_num)
theorem B2815781 : Blo 1877140 2815781 := bbase (se 4 (by rfl) ⟨263979, by rfl⟩ : syracuseStep 2815781 = 527959) (by norm_num)
theorem B6772517 : Blo 1877140 6772517 := bbase (se 4 (by rfl) ⟨634923, by rfl⟩ : syracuseStep 6772517 = 1269847) (by norm_num)
theorem B6338357 : Blo 1877140 6338357 := bbase (se 5 (by rfl) ⟨297110, by rfl⟩ : syracuseStep 6338357 = 594221) (by norm_num)
theorem B2815805 : Blo 1877140 2815805 := bbase (se 3 (by rfl) ⟨527963, by rfl⟩ : syracuseStep 2815805 = 1055927) (by norm_num)
theorem B2815829 : Blo 1877140 2815829 := bbase (se 9 (by rfl) ⟨8249, by rfl⟩ : syracuseStep 2815829 = 16499) (by norm_num)
theorem B3168085 : Blo 1877140 3168085 := bbase (se 9 (by rfl) ⟨9281, by rfl⟩ : syracuseStep 3168085 = 18563) (by norm_num)
theorem B4224869 : Blo 1877140 4224869 := bbase (se 4 (by rfl) ⟨396081, by rfl⟩ : syracuseStep 4224869 = 792163) (by norm_num)
theorem B2815853 : Blo 1877140 2815853 := bbase (se 3 (by rfl) ⟨527972, by rfl⟩ : syracuseStep 2815853 = 1055945) (by norm_num)
theorem B3807101 : Blo 1877140 3807101 := bbase (se 3 (by rfl) ⟨713831, by rfl⟩ : syracuseStep 3807101 = 1427663) (by norm_num)
theorem B2815877 : Blo 1877140 2815877 := bbase (se 4 (by rfl) ⟨263988, by rfl⟩ : syracuseStep 2815877 = 527977) (by norm_num)
theorem B5347205 : Blo 1877140 5347205 := bbase (se 4 (by rfl) ⟨501300, by rfl⟩ : syracuseStep 5347205 = 1002601) (by norm_num)
theorem B16267157 : Blo 1877140 16267157 := bbase (se 6 (by rfl) ⟨381261, by rfl⟩ : syracuseStep 16267157 = 762523) (by norm_num)
theorem B2815901 : Blo 1877140 2815901 := bbase (se 3 (by rfl) ⟨527981, by rfl⟩ : syracuseStep 2815901 = 1055963) (by norm_num)
theorem B3168173 : Blo 1877140 3168173 := bbase (se 3 (by rfl) ⟨594032, by rfl⟩ : syracuseStep 3168173 = 1188065) (by norm_num)
theorem B4224941 : Blo 1877140 4224941 := bbase (se 3 (by rfl) ⟨792176, by rfl⟩ : syracuseStep 4224941 = 1584353) (by norm_num)
theorem B2815925 : Blo 1877140 2815925 := bbase (se 5 (by rfl) ⟨131996, by rfl⟩ : syracuseStep 2815925 = 263993) (by norm_num)
theorem B2815949 : Blo 1877140 2815949 := bbase (se 3 (by rfl) ⟨527990, by rfl⟩ : syracuseStep 2815949 = 1055981) (by norm_num)
theorem B2815973 : Blo 1877140 2815973 := bbase (se 4 (by rfl) ⟨263997, by rfl⟩ : syracuseStep 2815973 = 527995) (by norm_num)
theorem B4225013 : Blo 1877140 4225013 := bbase (se 5 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 4225013 = 396095) (by norm_num)
theorem B2815997 : Blo 1877140 2815997 := bbase (se 3 (by rfl) ⟨527999, by rfl⟩ : syracuseStep 2815997 = 1055999) (by norm_num)
theorem B2816021 : Blo 1877140 2816021 := bbase (se 6 (by rfl) ⟨66000, by rfl⟩ : syracuseStep 2816021 = 132001) (by norm_num)
theorem B2816045 : Blo 1877140 2816045 := bbase (se 3 (by rfl) ⟨528008, by rfl⟩ : syracuseStep 2816045 = 1056017) (by norm_num)
theorem B3168301 : Blo 1877140 3168301 := bbase (se 3 (by rfl) ⟨594056, by rfl⟩ : syracuseStep 3168301 = 1188113) (by norm_num)
theorem B4225085 : Blo 1877140 4225085 := bbase (se 3 (by rfl) ⟨792203, by rfl⟩ : syracuseStep 4225085 = 1584407) (by norm_num)
theorem B2816069 : Blo 1877140 2816069 := bbase (se 4 (by rfl) ⟨264006, by rfl⟩ : syracuseStep 2816069 = 528013) (by norm_num)
theorem B5347397 : Blo 1877140 5347397 := bbase (se 4 (by rfl) ⟨501318, by rfl⟩ : syracuseStep 5347397 = 1002637) (by norm_num)
theorem B2816093 : Blo 1877140 2816093 := bbase (se 3 (by rfl) ⟨528017, by rfl⟩ : syracuseStep 2816093 = 1056035) (by norm_num)
theorem B2816117 : Blo 1877140 2816117 := bbase (se 5 (by rfl) ⟨132005, by rfl⟩ : syracuseStep 2816117 = 264011) (by norm_num)
theorem B3168389 : Blo 1877140 3168389 := bbase (se 4 (by rfl) ⟨297036, by rfl⟩ : syracuseStep 3168389 = 594073) (by norm_num)
theorem B4225157 : Blo 1877140 4225157 := bbase (se 4 (by rfl) ⟨396108, by rfl⟩ : syracuseStep 4225157 = 792217) (by norm_num)
theorem B2816141 : Blo 1877140 2816141 := bbase (se 3 (by rfl) ⟨528026, by rfl⟩ : syracuseStep 2816141 = 1056053) (by norm_num)
theorem B2816165 : Blo 1877140 2816165 := bbase (se 4 (by rfl) ⟨264015, by rfl⟩ : syracuseStep 2816165 = 528031) (by norm_num)
theorem B16046261 : Blo 1877140 16046261 := bbase (se 5 (by rfl) ⟨752168, by rfl⟩ : syracuseStep 16046261 = 1504337) (by norm_num)
theorem B2816189 : Blo 1877140 2816189 := bbase (se 3 (by rfl) ⟨528035, by rfl⟩ : syracuseStep 2816189 = 1056071) (by norm_num)
theorem B4225229 : Blo 1877140 4225229 := bbase (se 3 (by rfl) ⟨792230, by rfl⟩ : syracuseStep 4225229 = 1584461) (by norm_num)
theorem B2816213 : Blo 1877140 2816213 := bbase (se 7 (by rfl) ⟨33002, by rfl⟩ : syracuseStep 2816213 = 66005) (by norm_num)
theorem B6338789 : Blo 1877140 6338789 := bbase (se 4 (by rfl) ⟨594261, by rfl⟩ : syracuseStep 6338789 = 1188523) (by norm_num)
theorem B2816237 : Blo 1877140 2816237 := bbase (se 3 (by rfl) ⟨528044, by rfl⟩ : syracuseStep 2816237 = 1056089) (by norm_num)
theorem B2816261 : Blo 1877140 2816261 := bbase (se 4 (by rfl) ⟨264024, by rfl⟩ : syracuseStep 2816261 = 528049) (by norm_num)
theorem B3168517 : Blo 1877140 3168517 := bbase (se 4 (by rfl) ⟨297048, by rfl⟩ : syracuseStep 3168517 = 594097) (by norm_num)
theorem B4225301 : Blo 1877140 4225301 := bbase (se 6 (by rfl) ⟨99030, by rfl⟩ : syracuseStep 4225301 = 198061) (by norm_num)
theorem B10696981 : Blo 1877140 10696981 := bbase (se 6 (by rfl) ⟨250710, by rfl⟩ : syracuseStep 10696981 = 501421) (by norm_num)
theorem B2816285 : Blo 1877140 2816285 := bbase (se 3 (by rfl) ⟨528053, by rfl⟩ : syracuseStep 2816285 = 1056107) (by norm_num)
theorem B2816309 : Blo 1877140 2816309 := bbase (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) (by norm_num)
theorem B2111809 : Blo 1877140 2111809 := bbase (se 2 (by rfl) ⟨791928, by rfl⟩ : syracuseStep 2111809 = 1583857) (by norm_num)
theorem B2816333 : Blo 1877140 2816333 := bbase (se 3 (by rfl) ⟨528062, by rfl⟩ : syracuseStep 2816333 = 1056125) (by norm_num)
theorem B8018261 : Blo 1877140 8018261 := bbase (se 10 (by rfl) ⟨11745, by rfl⟩ : syracuseStep 8018261 = 23491) (by norm_num)
theorem B10156373 : Blo 1877140 10156373 := bbase (se 10 (by rfl) ⟨14877, by rfl⟩ : syracuseStep 10156373 = 29755) (by norm_num)
theorem B3168605 : Blo 1877140 3168605 := bbase (se 3 (by rfl) ⟨594113, by rfl⟩ : syracuseStep 3168605 = 1188227) (by norm_num)
theorem B4225373 : Blo 1877140 4225373 := bbase (se 3 (by rfl) ⟨792257, by rfl⟩ : syracuseStep 4225373 = 1584515) (by norm_num)
theorem B2111845 : Blo 1877140 2111845 := bbase (se 4 (by rfl) ⟨197985, by rfl⟩ : syracuseStep 2111845 = 395971) (by norm_num)
theorem B2816357 : Blo 1877140 2816357 := bbase (se 4 (by rfl) ⟨264033, by rfl⟩ : syracuseStep 2816357 = 528067) (by norm_num)
theorem B9509237 : Blo 1877140 9509237 := bbase (se 5 (by rfl) ⟨445745, by rfl⟩ : syracuseStep 9509237 = 891491) (by norm_num)
theorem B2816381 : Blo 1877140 2816381 := bbase (se 3 (by rfl) ⟨528071, by rfl⟩ : syracuseStep 2816381 = 1056143) (by norm_num)
theorem B2111881 : Blo 1877140 2111881 := bbase (se 2 (by rfl) ⟨791955, by rfl⟩ : syracuseStep 2111881 = 1583911) (by norm_num)
theorem B2816405 : Blo 1877140 2816405 := bbase (se 6 (by rfl) ⟨66009, by rfl⟩ : syracuseStep 2816405 = 132019) (by norm_num)
theorem B4225445 : Blo 1877140 4225445 := bbase (se 4 (by rfl) ⟨396135, by rfl⟩ : syracuseStep 4225445 = 792271) (by norm_num)
theorem B2111917 : Blo 1877140 2111917 := bbase (se 3 (by rfl) ⟨395984, by rfl⟩ : syracuseStep 2111917 = 791969) (by norm_num)
theorem B2816429 : Blo 1877140 2816429 := bbase (se 3 (by rfl) ⟨528080, by rfl⟩ : syracuseStep 2816429 = 1056161) (by norm_num)
theorem B6863285 : Blo 1877140 6863285 := bbase (se 5 (by rfl) ⟨321716, by rfl⟩ : syracuseStep 6863285 = 643433) (by norm_num)
theorem B2816453 : Blo 1877140 2816453 := bbase (se 4 (by rfl) ⟨264042, by rfl⟩ : syracuseStep 2816453 = 528085) (by norm_num)
theorem B2005445 : Blo 1877140 2005445 := bbase (se 4 (by rfl) ⟨188010, by rfl⟩ : syracuseStep 2005445 = 376021) (by norm_num)
theorem B2111953 : Blo 1877140 2111953 := bbase (se 2 (by rfl) ⟨791982, by rfl⟩ : syracuseStep 2111953 = 1583965) (by norm_num)
theorem B2816477 : Blo 1877140 2816477 := bbase (se 3 (by rfl) ⟨528089, by rfl⟩ : syracuseStep 2816477 = 1056179) (by norm_num)
theorem B3168733 : Blo 1877140 3168733 := bbase (se 3 (by rfl) ⟨594137, by rfl⟩ : syracuseStep 3168733 = 1188275) (by norm_num)
theorem B4225517 : Blo 1877140 4225517 := bbase (se 3 (by rfl) ⟨792284, by rfl⟩ : syracuseStep 4225517 = 1584569) (by norm_num)
theorem B2111989 : Blo 1877140 2111989 := bbase (se 5 (by rfl) ⟨98999, by rfl⟩ : syracuseStep 2111989 = 197999) (by norm_num)
theorem B2816501 : Blo 1877140 2816501 := bbase (se 5 (by rfl) ⟨132023, by rfl⟩ : syracuseStep 2816501 = 264047) (by norm_num)
theorem B3807749 : Blo 1877140 3807749 := bbase (se 4 (by rfl) ⟨356976, by rfl⟩ : syracuseStep 3807749 = 713953) (by norm_num)
theorem B2816525 : Blo 1877140 2816525 := bbase (se 3 (by rfl) ⟨528098, by rfl⟩ : syracuseStep 2816525 = 1056197) (by norm_num)
theorem B2112025 : Blo 1877140 2112025 := bbase (se 2 (by rfl) ⟨792009, by rfl⟩ : syracuseStep 2112025 = 1584019) (by norm_num)
theorem B2816549 : Blo 1877140 2816549 := bbase (se 4 (by rfl) ⟨264051, by rfl⟩ : syracuseStep 2816549 = 528103) (by norm_num)
theorem B3168821 : Blo 1877140 3168821 := bbase (se 5 (by rfl) ⟨148538, by rfl⟩ : syracuseStep 3168821 = 297077) (by norm_num)
theorem B4225589 : Blo 1877140 4225589 := bbase (se 5 (by rfl) ⟨198074, by rfl⟩ : syracuseStep 4225589 = 396149) (by norm_num)
theorem B2112061 : Blo 1877140 2112061 := bbase (se 3 (by rfl) ⟨396011, by rfl⟩ : syracuseStep 2112061 = 792023) (by norm_num)
theorem B2816573 : Blo 1877140 2816573 := bbase (se 3 (by rfl) ⟨528107, by rfl⟩ : syracuseStep 2816573 = 1056215) (by norm_num)
theorem B2816597 : Blo 1877140 2816597 := bbase (se 8 (by rfl) ⟨16503, by rfl⟩ : syracuseStep 2816597 = 33007) (by norm_num)
theorem B2112097 : Blo 1877140 2112097 := bbase (se 2 (by rfl) ⟨792036, by rfl⟩ : syracuseStep 2112097 = 1584073) (by norm_num)
theorem B2816621 : Blo 1877140 2816621 := bbase (se 3 (by rfl) ⟨528116, by rfl⟩ : syracuseStep 2816621 = 1056233) (by norm_num)
theorem B4225661 : Blo 1877140 4225661 := bbase (se 3 (by rfl) ⟨792311, by rfl⟩ : syracuseStep 4225661 = 1584623) (by norm_num)
theorem B2112133 : Blo 1877140 2112133 := bbase (se 4 (by rfl) ⟨198012, by rfl⟩ : syracuseStep 2112133 = 396025) (by norm_num)
theorem B2816645 : Blo 1877140 2816645 := bbase (se 4 (by rfl) ⟨264060, by rfl⟩ : syracuseStep 2816645 = 528121) (by norm_num)
theorem B6339221 : Blo 1877140 6339221 := bbase (se 6 (by rfl) ⟨148575, by rfl⟩ : syracuseStep 6339221 = 297151) (by norm_num)
theorem B2816669 : Blo 1877140 2816669 := bbase (se 3 (by rfl) ⟨528125, by rfl⟩ : syracuseStep 2816669 = 1056251) (by norm_num)
theorem B2112169 : Blo 1877140 2112169 := bbase (se 2 (by rfl) ⟨792063, by rfl⟩ : syracuseStep 2112169 = 1584127) (by norm_num)
theorem B2816693 : Blo 1877140 2816693 := bbase (se 5 (by rfl) ⟨132032, by rfl⟩ : syracuseStep 2816693 = 264065) (by norm_num)
theorem B3168949 : Blo 1877140 3168949 := bbase (se 5 (by rfl) ⟨148544, by rfl⟩ : syracuseStep 3168949 = 297089) (by norm_num)
theorem B4225733 : Blo 1877140 4225733 := bbase (se 4 (by rfl) ⟨396162, by rfl⟩ : syracuseStep 4225733 = 792325) (by norm_num)
theorem B2112205 : Blo 1877140 2112205 := bbase (se 3 (by rfl) ⟨396038, by rfl⟩ : syracuseStep 2112205 = 792077) (by norm_num)
theorem B2816717 : Blo 1877140 2816717 := bbase (se 3 (by rfl) ⟨528134, by rfl⟩ : syracuseStep 2816717 = 1056269) (by norm_num)
theorem B2816741 : Blo 1877140 2816741 := bbase (se 4 (by rfl) ⟨264069, by rfl⟩ : syracuseStep 2816741 = 528139) (by norm_num)
theorem B2112241 : Blo 1877140 2112241 := bbase (se 2 (by rfl) ⟨792090, by rfl⟩ : syracuseStep 2112241 = 1584181) (by norm_num)
theorem B2816765 : Blo 1877140 2816765 := bbase (se 3 (by rfl) ⟨528143, by rfl⟩ : syracuseStep 2816765 = 1056287) (by norm_num)
theorem B3169037 : Blo 1877140 3169037 := bbase (se 3 (by rfl) ⟨594194, by rfl⟩ : syracuseStep 3169037 = 1188389) (by norm_num)
theorem B4225805 : Blo 1877140 4225805 := bbase (se 3 (by rfl) ⟨792338, by rfl⟩ : syracuseStep 4225805 = 1584677) (by norm_num)
theorem B2112277 : Blo 1877140 2112277 := bbase (se 6 (by rfl) ⟨49506, by rfl⟩ : syracuseStep 2112277 = 99013) (by norm_num)
theorem B2816789 : Blo 1877140 2816789 := bbase (se 6 (by rfl) ⟨66018, by rfl⟩ : syracuseStep 2816789 = 132037) (by norm_num)
theorem B2816813 : Blo 1877140 2816813 := bbase (se 3 (by rfl) ⟨528152, by rfl⟩ : syracuseStep 2816813 = 1056305) (by norm_num)
theorem B2112313 : Blo 1877140 2112313 := bbase (se 2 (by rfl) ⟨792117, by rfl⟩ : syracuseStep 2112313 = 1584235) (by norm_num)
theorem B2816837 : Blo 1877140 2816837 := bbase (se 4 (by rfl) ⟨264078, by rfl⟩ : syracuseStep 2816837 = 528157) (by norm_num)
theorem B4225877 : Blo 1877140 4225877 := bbase (se 9 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 4225877 = 24761) (by norm_num)
theorem B2112349 : Blo 1877140 2112349 := bbase (se 3 (by rfl) ⟨396065, by rfl⟩ : syracuseStep 2112349 = 792131) (by norm_num)
theorem B2816861 : Blo 1877140 2816861 := bbase (se 3 (by rfl) ⟨528161, by rfl⟩ : syracuseStep 2816861 = 1056323) (by norm_num)
theorem B2816885 : Blo 1877140 2816885 := bbase (se 5 (by rfl) ⟨132041, by rfl⟩ : syracuseStep 2816885 = 264083) (by norm_num)
theorem B13540213 : Blo 1877140 13540213 := bbase (se 5 (by rfl) ⟨634697, by rfl⟩ : syracuseStep 13540213 = 1269395) (by norm_num)
theorem B2112385 : Blo 1877140 2112385 := bbase (se 2 (by rfl) ⟨792144, by rfl⟩ : syracuseStep 2112385 = 1584289) (by norm_num)
theorem B2005889 : Blo 1877140 2005889 := bbase (se 2 (by rfl) ⟨752208, by rfl⟩ : syracuseStep 2005889 = 1504417) (by norm_num)
theorem B2816909 : Blo 1877140 2816909 := bbase (se 3 (by rfl) ⟨528170, by rfl⟩ : syracuseStep 2816909 = 1056341) (by norm_num)
theorem B3169165 : Blo 1877140 3169165 := bbase (se 3 (by rfl) ⟨594218, by rfl⟩ : syracuseStep 3169165 = 1188437) (by norm_num)
theorem B7134101 : Blo 1877140 7134101 := bbase (se 6 (by rfl) ⟨167205, by rfl⟩ : syracuseStep 7134101 = 334411) (by norm_num)
theorem B4225949 : Blo 1877140 4225949 := bbase (se 3 (by rfl) ⟨792365, by rfl⟩ : syracuseStep 4225949 = 1584731) (by norm_num)
theorem B2112421 : Blo 1877140 2112421 := bbase (se 4 (by rfl) ⟨198039, by rfl⟩ : syracuseStep 2112421 = 396079) (by norm_num)
theorem B2816933 : Blo 1877140 2816933 := bbase (se 4 (by rfl) ⟨264087, by rfl⟩ : syracuseStep 2816933 = 528175) (by norm_num)
theorem B2816957 : Blo 1877140 2816957 := bbase (se 3 (by rfl) ⟨528179, by rfl⟩ : syracuseStep 2816957 = 1056359) (by norm_num)
theorem B2112457 : Blo 1877140 2112457 := bbase (se 2 (by rfl) ⟨792171, by rfl⟩ : syracuseStep 2112457 = 1584343) (by norm_num)
theorem B2816981 : Blo 1877140 2816981 := bbase (se 7 (by rfl) ⟨33011, by rfl⟩ : syracuseStep 2816981 = 66023) (by norm_num)
theorem B4021213 : Blo 1877140 4021213 := bbase (se 3 (by rfl) ⟨753977, by rfl⟩ : syracuseStep 4021213 = 1507955) (by norm_num)
theorem B3169253 : Blo 1877140 3169253 := bbase (se 4 (by rfl) ⟨297117, by rfl⟩ : syracuseStep 3169253 = 594235) (by norm_num)
theorem B4226021 : Blo 1877140 4226021 := bbase (se 4 (by rfl) ⟨396189, by rfl⟩ : syracuseStep 4226021 = 792379) (by norm_num)
theorem B2112493 : Blo 1877140 2112493 := bbase (se 3 (by rfl) ⟨396092, by rfl⟩ : syracuseStep 2112493 = 792185) (by norm_num)
theorem B2817005 : Blo 1877140 2817005 := bbase (se 3 (by rfl) ⟨528188, by rfl⟩ : syracuseStep 2817005 = 1056377) (by norm_num)
theorem B2817029 : Blo 1877140 2817029 := bbase (se 4 (by rfl) ⟨264096, by rfl⟩ : syracuseStep 2817029 = 528193) (by norm_num)
theorem B2538509 : Blo 1877140 2538509 := bbase (se 3 (by rfl) ⟨475970, by rfl⟩ : syracuseStep 2538509 = 951941) (by norm_num)
theorem B2112529 : Blo 1877140 2112529 := bbase (se 2 (by rfl) ⟨792198, by rfl⟩ : syracuseStep 2112529 = 1584397) (by norm_num)
theorem B4013077 : Blo 1877140 4013077 := bbase (se 6 (by rfl) ⟨94056, by rfl⟩ : syracuseStep 4013077 = 188113) (by norm_num)
theorem B2817053 : Blo 1877140 2817053 := bbase (se 3 (by rfl) ⟨528197, by rfl⟩ : syracuseStep 2817053 = 1056395) (by norm_num)
theorem B5348389 : Blo 1877140 5348389 := bbase (se 4 (by rfl) ⟨501411, by rfl⟩ : syracuseStep 5348389 = 1002823) (by norm_num)
theorem B4226093 : Blo 1877140 4226093 := bbase (se 3 (by rfl) ⟨792392, by rfl⟩ : syracuseStep 4226093 = 1584785) (by norm_num)
theorem B2112565 : Blo 1877140 2112565 := bbase (se 5 (by rfl) ⟨99026, by rfl⟩ : syracuseStep 2112565 = 198053) (by norm_num)
theorem B2817077 : Blo 1877140 2817077 := bbase (se 5 (by rfl) ⟨132050, by rfl⟩ : syracuseStep 2817077 = 264101) (by norm_num)
theorem B4512829 : Blo 1877140 4512829 := bbase (se 3 (by rfl) ⟨846155, by rfl⟩ : syracuseStep 4512829 = 1692311) (by norm_num)
theorem B6339653 : Blo 1877140 6339653 := bbase (se 4 (by rfl) ⟨594342, by rfl⟩ : syracuseStep 6339653 = 1188685) (by norm_num)
theorem B2817101 : Blo 1877140 2817101 := bbase (se 3 (by rfl) ⟨528206, by rfl⟩ : syracuseStep 2817101 = 1056413) (by norm_num)
theorem B2112601 : Blo 1877140 2112601 := bbase (se 2 (by rfl) ⟨792225, by rfl⟩ : syracuseStep 2112601 = 1584451) (by norm_num)
theorem B2817125 : Blo 1877140 2817125 := bbase (se 4 (by rfl) ⟨264105, by rfl⟩ : syracuseStep 2817125 = 528211) (by norm_num)
theorem B3169381 : Blo 1877140 3169381 := bbase (se 4 (by rfl) ⟨297129, by rfl⟩ : syracuseStep 3169381 = 594259) (by norm_num)
theorem B4226165 : Blo 1877140 4226165 := bbase (se 5 (by rfl) ⟨198101, by rfl⟩ : syracuseStep 4226165 = 396203) (by norm_num)
theorem B2006137 : Blo 1877140 2006137 := bbase (se 2 (by rfl) ⟨752301, by rfl⟩ : syracuseStep 2006137 = 1504603) (by norm_num)
theorem B2112637 : Blo 1877140 2112637 := bbase (se 3 (by rfl) ⟨396119, by rfl⟩ : syracuseStep 2112637 = 792239) (by norm_num)
theorem B2817149 : Blo 1877140 2817149 := bbase (se 3 (by rfl) ⟨528215, by rfl⟩ : syracuseStep 2817149 = 1056431) (by norm_num)
theorem B2784397 : Blo 1877140 2784397 := bbase (se 3 (by rfl) ⟨522074, by rfl⟩ : syracuseStep 2784397 = 1044149) (by norm_num)
theorem B2817173 : Blo 1877140 2817173 := bbase (se 6 (by rfl) ⟨66027, by rfl⟩ : syracuseStep 2817173 = 132055) (by norm_num)
theorem B2112673 : Blo 1877140 2112673 := bbase (se 2 (by rfl) ⟨792252, by rfl⟩ : syracuseStep 2112673 = 1584505) (by norm_num)
theorem B2817197 : Blo 1877140 2817197 := bbase (se 3 (by rfl) ⟨528224, by rfl⟩ : syracuseStep 2817197 = 1056449) (by norm_num)
theorem B7134389 : Blo 1877140 7134389 := bbase (se 5 (by rfl) ⟨334424, by rfl⟩ : syracuseStep 7134389 = 668849) (by norm_num)
theorem B3169469 : Blo 1877140 3169469 := bbase (se 3 (by rfl) ⟨594275, by rfl⟩ : syracuseStep 3169469 = 1188551) (by norm_num)
theorem B4226237 : Blo 1877140 4226237 := bbase (se 3 (by rfl) ⟨792419, by rfl⟩ : syracuseStep 4226237 = 1584839) (by norm_num)
theorem B2112709 : Blo 1877140 2112709 := bbase (se 4 (by rfl) ⟨198066, by rfl⟩ : syracuseStep 2112709 = 396133) (by norm_num)
theorem B2817221 : Blo 1877140 2817221 := bbase (se 4 (by rfl) ⟨264114, by rfl⟩ : syracuseStep 2817221 = 528229) (by norm_num)
theorem B2817245 : Blo 1877140 2817245 := bbase (se 3 (by rfl) ⟨528233, by rfl⟩ : syracuseStep 2817245 = 1056467) (by norm_num)
theorem B2112745 : Blo 1877140 2112745 := bbase (se 2 (by rfl) ⟨792279, by rfl⟩ : syracuseStep 2112745 = 1584559) (by norm_num)
theorem B2817269 : Blo 1877140 2817269 := bbase (se 5 (by rfl) ⟨132059, by rfl⟩ : syracuseStep 2817269 = 264119) (by norm_num)
theorem B4226309 : Blo 1877140 4226309 := bbase (se 4 (by rfl) ⟨396216, by rfl⟩ : syracuseStep 4226309 = 792433) (by norm_num)
theorem B2112781 : Blo 1877140 2112781 := bbase (se 3 (by rfl) ⟨396146, by rfl⟩ : syracuseStep 2112781 = 792293) (by norm_num)
theorem B2817293 : Blo 1877140 2817293 := bbase (se 3 (by rfl) ⟨528242, by rfl⟩ : syracuseStep 2817293 = 1056485) (by norm_num)
theorem B2817317 : Blo 1877140 2817317 := bbase (se 4 (by rfl) ⟨264123, by rfl⟩ : syracuseStep 2817317 = 528247) (by norm_num)
theorem B2112817 : Blo 1877140 2112817 := bbase (se 2 (by rfl) ⟨792306, by rfl⟩ : syracuseStep 2112817 = 1584613) (by norm_num)
theorem B2817341 : Blo 1877140 2817341 := bbase (se 3 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 2817341 = 1056503) (by norm_num)
theorem B3169597 : Blo 1877140 3169597 := bbase (se 3 (by rfl) ⟨594299, by rfl⟩ : syracuseStep 3169597 = 1188599) (by norm_num)
theorem B4226381 : Blo 1877140 4226381 := bbase (se 3 (by rfl) ⟨792446, by rfl⟩ : syracuseStep 4226381 = 1584893) (by norm_num)
theorem B2112853 : Blo 1877140 2112853 := bbase (se 11 (by rfl) ⟨1547, by rfl⟩ : syracuseStep 2112853 = 3095) (by norm_num)
theorem B2817365 : Blo 1877140 2817365 := bbase (se 11 (by rfl) ⟨2063, by rfl⟩ : syracuseStep 2817365 = 4127) (by norm_num)
theorem B2817389 : Blo 1877140 2817389 := bbase (se 3 (by rfl) ⟨528260, by rfl⟩ : syracuseStep 2817389 = 1056521) (by norm_num)
theorem B2112889 : Blo 1877140 2112889 := bbase (se 2 (by rfl) ⟨792333, by rfl⟩ : syracuseStep 2112889 = 1584667) (by norm_num)
theorem B2817413 : Blo 1877140 2817413 := bbase (se 4 (by rfl) ⟨264132, by rfl⟩ : syracuseStep 2817413 = 528265) (by norm_num)
theorem B3169685 : Blo 1877140 3169685 := bbase (se 6 (by rfl) ⟨74289, by rfl⟩ : syracuseStep 3169685 = 148579) (by norm_num)
theorem B4226453 : Blo 1877140 4226453 := bbase (se 6 (by rfl) ⟨99057, by rfl⟩ : syracuseStep 4226453 = 198115) (by norm_num)
theorem B2112925 : Blo 1877140 2112925 := bbase (se 3 (by rfl) ⟨396173, by rfl⟩ : syracuseStep 2112925 = 792347) (by norm_num)
theorem B2817437 : Blo 1877140 2817437 := bbase (se 3 (by rfl) ⟨528269, by rfl⟩ : syracuseStep 2817437 = 1056539) (by norm_num)
theorem B2817461 : Blo 1877140 2817461 := bbase (se 5 (by rfl) ⟨132068, by rfl⟩ : syracuseStep 2817461 = 264137) (by norm_num)
theorem B2112961 : Blo 1877140 2112961 := bbase (se 2 (by rfl) ⟨792360, by rfl⟩ : syracuseStep 2112961 = 1584721) (by norm_num)
theorem B2817485 : Blo 1877140 2817485 := bbase (se 3 (by rfl) ⟨528278, by rfl⟩ : syracuseStep 2817485 = 1056557) (by norm_num)
theorem B4226525 : Blo 1877140 4226525 := bbase (se 3 (by rfl) ⟨792473, by rfl⟩ : syracuseStep 4226525 = 1584947) (by norm_num)
theorem B2112997 : Blo 1877140 2112997 := bbase (se 4 (by rfl) ⟨198093, by rfl⟩ : syracuseStep 2112997 = 396187) (by norm_num)
theorem B2817509 : Blo 1877140 2817509 := bbase (se 4 (by rfl) ⟨264141, by rfl⟩ : syracuseStep 2817509 = 528283) (by norm_num)
theorem B6340085 : Blo 1877140 6340085 := bbase (se 5 (by rfl) ⟨297191, by rfl⟩ : syracuseStep 6340085 = 594383) (by norm_num)
theorem B2817533 : Blo 1877140 2817533 := bbase (se 3 (by rfl) ⟨528287, by rfl⟩ : syracuseStep 2817533 = 1056575) (by norm_num)
theorem B5078533 : Blo 1877140 5078533 := bbase (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) (by norm_num)
theorem B2113033 : Blo 1877140 2113033 := bbase (se 2 (by rfl) ⟨792387, by rfl⟩ : syracuseStep 2113033 = 1584775) (by norm_num)
theorem B2817557 : Blo 1877140 2817557 := bbase (se 6 (by rfl) ⟨66036, by rfl⟩ : syracuseStep 2817557 = 132073) (by norm_num)
theorem B3169813 : Blo 1877140 3169813 := bbase (se 6 (by rfl) ⟨74292, by rfl⟩ : syracuseStep 3169813 = 148585) (by norm_num)
theorem B4226597 : Blo 1877140 4226597 := bbase (se 4 (by rfl) ⟨396243, by rfl⟩ : syracuseStep 4226597 = 792487) (by norm_num)
theorem B2006569 : Blo 1877140 2006569 := bbase (se 2 (by rfl) ⟨752463, by rfl⟩ : syracuseStep 2006569 = 1504927) (by norm_num)
theorem B2113069 : Blo 1877140 2113069 := bbase (se 3 (by rfl) ⟨396200, by rfl⟩ : syracuseStep 2113069 = 792401) (by norm_num)
theorem B2817581 : Blo 1877140 2817581 := bbase (se 3 (by rfl) ⟨528296, by rfl⟩ : syracuseStep 2817581 = 1056593) (by norm_num)
theorem B2817605 : Blo 1877140 2817605 := bbase (se 4 (by rfl) ⟨264150, by rfl⟩ : syracuseStep 2817605 = 528301) (by norm_num)
theorem B2113105 : Blo 1877140 2113105 := bbase (se 2 (by rfl) ⟨792414, by rfl⟩ : syracuseStep 2113105 = 1584829) (by norm_num)
theorem B2817629 : Blo 1877140 2817629 := bbase (se 3 (by rfl) ⟨528305, by rfl⟩ : syracuseStep 2817629 = 1056611) (by norm_num)
theorem B3169901 : Blo 1877140 3169901 := bbase (se 3 (by rfl) ⟨594356, by rfl⟩ : syracuseStep 3169901 = 1188713) (by norm_num)
theorem B4226669 : Blo 1877140 4226669 := bbase (se 3 (by rfl) ⟨792500, by rfl⟩ : syracuseStep 4226669 = 1585001) (by norm_num)
theorem B2006641 : Blo 1877140 2006641 := bbase (se 2 (by rfl) ⟨752490, by rfl⟩ : syracuseStep 2006641 = 1504981) (by norm_num)
theorem B2113141 : Blo 1877140 2113141 := bbase (se 5 (by rfl) ⟨99053, by rfl⟩ : syracuseStep 2113141 = 198107) (by norm_num)
theorem B2817653 : Blo 1877140 2817653 := bbase (se 5 (by rfl) ⟨132077, by rfl⟩ : syracuseStep 2817653 = 264155) (by norm_num)
theorem B9510533 : Blo 1877140 9510533 := bbase (se 4 (by rfl) ⟨891612, by rfl⟩ : syracuseStep 9510533 = 1783225) (by norm_num)
theorem B2817677 : Blo 1877140 2817677 := bbase (se 3 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 2817677 = 1056629) (by norm_num)
theorem B2113177 : Blo 1877140 2113177 := bbase (se 2 (by rfl) ⟨792441, by rfl⟩ : syracuseStep 2113177 = 1584883) (by norm_num)
theorem B2817701 : Blo 1877140 2817701 := bbase (se 4 (by rfl) ⟨264159, by rfl⟩ : syracuseStep 2817701 = 528319) (by norm_num)
theorem B4513445 : Blo 1877140 4513445 := bbase (se 4 (by rfl) ⟨423135, by rfl⟩ : syracuseStep 4513445 = 846271) (by norm_num)
theorem B4226741 : Blo 1877140 4226741 := bbase (se 5 (by rfl) ⟨198128, by rfl⟩ : syracuseStep 4226741 = 396257) (by norm_num)
theorem B2113213 : Blo 1877140 2113213 := bbase (se 3 (by rfl) ⟨396227, by rfl⟩ : syracuseStep 2113213 = 792455) (by norm_num)
theorem B2817725 : Blo 1877140 2817725 := bbase (se 3 (by rfl) ⟨528323, by rfl⟩ : syracuseStep 2817725 = 1056647) (by norm_num)
theorem B2817749 : Blo 1877140 2817749 := bbase (se 7 (by rfl) ⟨33020, by rfl⟩ : syracuseStep 2817749 = 66041) (by norm_num)
theorem B2113249 : Blo 1877140 2113249 := bbase (se 2 (by rfl) ⟨792468, by rfl⟩ : syracuseStep 2113249 = 1584937) (by norm_num)
theorem B2817773 : Blo 1877140 2817773 := bbase (se 3 (by rfl) ⟨528332, by rfl⟩ : syracuseStep 2817773 = 1056665) (by norm_num)
theorem B3170029 : Blo 1877140 3170029 := bbase (se 3 (by rfl) ⟨594380, by rfl⟩ : syracuseStep 3170029 = 1188761) (by norm_num)
theorem B4226813 : Blo 1877140 4226813 := bbase (se 3 (by rfl) ⟨792527, by rfl⟩ : syracuseStep 4226813 = 1585055) (by norm_num)
theorem B2539261 : Blo 1877140 2539261 := bbase (se 3 (by rfl) ⟨476111, by rfl⟩ : syracuseStep 2539261 = 952223) (by norm_num)
theorem B2113285 : Blo 1877140 2113285 := bbase (se 4 (by rfl) ⟨198120, by rfl⟩ : syracuseStep 2113285 = 396241) (by norm_num)
theorem B2817797 : Blo 1877140 2817797 := bbase (se 4 (by rfl) ⟨264168, by rfl⟩ : syracuseStep 2817797 = 528337) (by norm_num)
theorem B2817821 : Blo 1877140 2817821 := bbase (se 3 (by rfl) ⟨528341, by rfl⟩ : syracuseStep 2817821 = 1056683) (by norm_num)
theorem B2113321 : Blo 1877140 2113321 := bbase (se 2 (by rfl) ⟨792495, by rfl⟩ : syracuseStep 2113321 = 1584991) (by norm_num)
theorem B3383093 : Blo 1877140 3383093 := bbase (se 5 (by rfl) ⟨158582, by rfl⟩ : syracuseStep 3383093 = 317165) (by norm_num)
theorem B2817845 : Blo 1877140 2817845 := bbase (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) (by norm_num)
theorem B3170117 : Blo 1877140 3170117 := bbase (se 4 (by rfl) ⟨297198, by rfl⟩ : syracuseStep 3170117 = 594397) (by norm_num)
theorem B4226885 : Blo 1877140 4226885 := bbase (se 4 (by rfl) ⟨396270, by rfl⟩ : syracuseStep 4226885 = 792541) (by norm_num)
theorem B2113357 : Blo 1877140 2113357 := bbase (se 3 (by rfl) ⟨396254, by rfl⟩ : syracuseStep 2113357 = 792509) (by norm_num)
theorem B2817869 : Blo 1877140 2817869 := bbase (se 3 (by rfl) ⟨528350, by rfl⟩ : syracuseStep 2817869 = 1056701) (by norm_num)
theorem B2817893 : Blo 1877140 2817893 := bbase (se 4 (by rfl) ⟨264177, by rfl⟩ : syracuseStep 2817893 = 528355) (by norm_num)
theorem B2113393 : Blo 1877140 2113393 := bbase (se 2 (by rfl) ⟨792522, by rfl⟩ : syracuseStep 2113393 = 1585045) (by norm_num)
theorem B2817917 : Blo 1877140 2817917 := bbase (se 3 (by rfl) ⟨528359, by rfl⟩ : syracuseStep 2817917 = 1056719) (by norm_num)
theorem B4226957 : Blo 1877140 4226957 := bbase (se 3 (by rfl) ⟨792554, by rfl⟩ : syracuseStep 4226957 = 1585109) (by norm_num)
theorem B2113429 : Blo 1877140 2113429 := bbase (se 6 (by rfl) ⟨49533, by rfl⟩ : syracuseStep 2113429 = 99067) (by norm_num)
theorem B2817941 : Blo 1877140 2817941 := bbase (se 6 (by rfl) ⟨66045, by rfl⟩ : syracuseStep 2817941 = 132091) (by norm_num)
theorem B6340517 : Blo 1877140 6340517 := bbase (se 4 (by rfl) ⟨594423, by rfl⟩ : syracuseStep 6340517 = 1188847) (by norm_num)
theorem B2817965 : Blo 1877140 2817965 := bbase (se 3 (by rfl) ⟨528368, by rfl⟩ : syracuseStep 2817965 = 1056737) (by norm_num)
theorem B2113465 : Blo 1877140 2113465 := bbase (se 2 (by rfl) ⟨792549, by rfl⟩ : syracuseStep 2113465 = 1585099) (by norm_num)
theorem B2817989 : Blo 1877140 2817989 := bbase (se 4 (by rfl) ⟨264186, by rfl⟩ : syracuseStep 2817989 = 528373) (by norm_num)
theorem B3170245 : Blo 1877140 3170245 := bbase (se 4 (by rfl) ⟨297210, by rfl⟩ : syracuseStep 3170245 = 594421) (by norm_num)
theorem B4227029 : Blo 1877140 4227029 := bbase (se 7 (by rfl) ⟨49535, by rfl⟩ : syracuseStep 4227029 = 99071) (by norm_num)
theorem B2113501 : Blo 1877140 2113501 := bbase (se 3 (by rfl) ⟨396281, by rfl⟩ : syracuseStep 2113501 = 792563) (by norm_num)
theorem B2818013 : Blo 1877140 2818013 := bbase (se 3 (by rfl) ⟨528377, by rfl⟩ : syracuseStep 2818013 = 1056755) (by norm_num)
theorem B4513781 : Blo 1877140 4513781 := bbase (se 5 (by rfl) ⟨211583, by rfl⟩ : syracuseStep 4513781 = 423167) (by norm_num)
theorem B2818037 : Blo 1877140 2818037 := bbase (se 5 (by rfl) ⟨132095, by rfl⟩ : syracuseStep 2818037 = 264191) (by norm_num)
theorem B2818049 : Blo 1877140 2818049 := bstep (se 2 (by rfl) ⟨1056768, by rfl⟩ : syracuseStep 2818049 = 2113537) B2113537
theorem B6340625 : Blo 1877140 6340625 := bstep (se 2 (by rfl) ⟨2377734, by rfl⟩ : syracuseStep 6340625 = 4755469) B4755469
theorem B2818067 : Blo 1877140 2818067 := bstep (se 1 (by rfl) ⟨2113550, by rfl⟩ : syracuseStep 2818067 = 4227101) B4227101
theorem B2113555 : Blo 1877140 2113555 := bstep (se 1 (by rfl) ⟨1585166, by rfl⟩ : syracuseStep 2113555 = 3170333) B3170333
theorem B3170353 : Blo 1877140 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B2818097 : Blo 1877140 2818097 := bstep (se 2 (by rfl) ⟨1056786, by rfl⟩ : syracuseStep 2818097 = 2113573) B2113573
theorem B2818115 : Blo 1877140 2818115 := bstep (se 1 (by rfl) ⟨2113586, by rfl⟩ : syracuseStep 2818115 = 4227173) B4227173
theorem B3170387 : Blo 1877140 3170387 := bstep (se 1 (by rfl) ⟨2377790, by rfl⟩ : syracuseStep 3170387 = 4755581) B4755581
theorem B2818145 : Blo 1877140 2818145 := bstep (se 2 (by rfl) ⟨1056804, by rfl⟩ : syracuseStep 2818145 = 2113609) B2113609
theorem B2818163 : Blo 1877140 2818163 := bstep (se 1 (by rfl) ⟨2113622, by rfl⟩ : syracuseStep 2818163 = 4227245) B4227245
theorem B3809411 : Blo 1877140 3809411 := bstep (se 1 (by rfl) ⟨2857058, by rfl⟩ : syracuseStep 3809411 = 5714117) B5714117
theorem B2818193 : Blo 1877140 2818193 := bstep (se 2 (by rfl) ⟨1056822, by rfl⟩ : syracuseStep 2818193 = 2113645) B2113645
theorem B5349539 : Blo 1877140 5349539 := bstep (se 1 (by rfl) ⟨4012154, by rfl⟩ : syracuseStep 5349539 = 8024309) B8024309
theorem B2818211 : Blo 1877140 2818211 := bstep (se 1 (by rfl) ⟨2113658, by rfl⟩ : syracuseStep 2818211 = 4227317) B4227317
theorem B2113699 : Blo 1877140 2113699 := bstep (se 1 (by rfl) ⟨1585274, by rfl⟩ : syracuseStep 2113699 = 3170549) B3170549
theorem B2818241 : Blo 1877140 2818241 := bstep (se 2 (by rfl) ⟨1056840, by rfl⟩ : syracuseStep 2818241 = 2113681) B2113681
theorem B3383491 : Blo 1877140 3383491 := bstep (se 1 (by rfl) ⟨2537618, by rfl⟩ : syracuseStep 3383491 = 5075237) B5075237
theorem B4227281 : Blo 1877140 4227281 := bstep (se 2 (by rfl) ⟨1585230, by rfl⟩ : syracuseStep 4227281 = 3170461) B3170461
theorem B3170515 : Blo 1877140 3170515 := bstep (se 1 (by rfl) ⟨2377886, by rfl⟩ : syracuseStep 3170515 = 4755773) B4755773
theorem B2818259 : Blo 1877140 2818259 := bstep (se 1 (by rfl) ⟨2113694, by rfl⟩ : syracuseStep 2818259 = 4227389) B4227389
theorem B3563747 : Blo 1877140 3563747 := bstep (se 1 (by rfl) ⟨2672810, by rfl⟩ : syracuseStep 3563747 = 5345621) B5345621
theorem B4227299 : Blo 1877140 4227299 := bstep (se 1 (by rfl) ⟨3170474, by rfl⟩ : syracuseStep 4227299 = 6340949) B6340949
theorem B2818289 : Blo 1877140 2818289 := bstep (se 2 (by rfl) ⟨1056858, by rfl⟩ : syracuseStep 2818289 = 2113717) B2113717
theorem B2818307 : Blo 1877140 2818307 := bstep (se 1 (by rfl) ⟨2113730, by rfl⟩ : syracuseStep 2818307 = 4227461) B4227461
theorem B9511181 : Blo 1877140 9511181 := bstep (se 3 (by rfl) ⟨1783346, by rfl⟩ : syracuseStep 9511181 = 3566693) B3566693
theorem B2818337 : Blo 1877140 2818337 := bstep (se 2 (by rfl) ⟨1056876, by rfl⟩ : syracuseStep 2818337 = 2113753) B2113753
theorem B2818355 : Blo 1877140 2818355 := bstep (se 1 (by rfl) ⟨2113766, by rfl⟩ : syracuseStep 2818355 = 4227533) B4227533
theorem B2113843 : Blo 1877140 2113843 := bstep (se 1 (by rfl) ⟨1585382, by rfl⟩ : syracuseStep 2113843 = 3170765) B3170765
theorem B2818385 : Blo 1877140 2818385 := bstep (se 2 (by rfl) ⟨1056894, by rfl⟩ : syracuseStep 2818385 = 2113789) B2113789
theorem B3170657 : Blo 1877140 3170657 := bstep (se 2 (by rfl) ⟨1188996, by rfl⟩ : syracuseStep 3170657 = 2377993) B2377993
theorem B2818403 : Blo 1877140 2818403 := bstep (se 1 (by rfl) ⟨2113802, by rfl⟩ : syracuseStep 2818403 = 4227605) B4227605
theorem B14262641 : Blo 1877140 14262641 := bstep (se 2 (by rfl) ⟨5348490, by rfl⟩ : syracuseStep 14262641 = 10696981) B10696981
theorem B2818433 : Blo 1877140 2818433 := bstep (se 2 (by rfl) ⟨1056912, by rfl⟩ : syracuseStep 2818433 = 2113825) B2113825
theorem B2818451 : Blo 1877140 2818451 := bstep (se 1 (by rfl) ⟨2113838, by rfl⟩ : syracuseStep 2818451 = 4227677) B4227677
theorem B5145005 : Blo 1877140 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B2818481 : Blo 1877140 2818481 := bstep (se 2 (by rfl) ⟨1056930, by rfl⟩ : syracuseStep 2818481 = 2113861) B2113861
theorem B2818499 : Blo 1877140 2818499 := bstep (se 1 (by rfl) ⟨2113874, by rfl⟩ : syracuseStep 2818499 = 4227749) B4227749
theorem B2113987 : Blo 1877140 2113987 := bstep (se 1 (by rfl) ⟨1585490, by rfl⟩ : syracuseStep 2113987 = 3170981) B3170981
theorem B3170785 : Blo 1877140 3170785 := bstep (se 2 (by rfl) ⟨1189044, by rfl⟩ : syracuseStep 3170785 = 2378089) B2378089
theorem B2818529 : Blo 1877140 2818529 := bstep (se 2 (by rfl) ⟨1056948, by rfl⟩ : syracuseStep 2818529 = 2113897) B2113897
theorem B4227569 : Blo 1877140 4227569 := bstep (se 2 (by rfl) ⟨1585338, by rfl⟩ : syracuseStep 4227569 = 3170677) B3170677
theorem B2818547 : Blo 1877140 2818547 := bstep (se 1 (by rfl) ⟨2113910, by rfl⟩ : syracuseStep 2818547 = 4227821) B4227821
theorem B4227587 : Blo 1877140 4227587 := bstep (se 1 (by rfl) ⟨3170690, by rfl⟩ : syracuseStep 4227587 = 6341381) B6341381
theorem B3170819 : Blo 1877140 3170819 := bstep (se 1 (by rfl) ⟨2378114, by rfl⟩ : syracuseStep 3170819 = 4756229) B4756229
theorem B2818577 : Blo 1877140 2818577 := bstep (se 2 (by rfl) ⟨1056966, by rfl⟩ : syracuseStep 2818577 = 2113933) B2113933
theorem B2376211 : Blo 1877140 2376211 := bstep (se 1 (by rfl) ⟨1782158, by rfl⟩ : syracuseStep 2376211 = 3564317) B3564317
theorem B2818595 : Blo 1877140 2818595 := bstep (se 1 (by rfl) ⟨2113946, by rfl⟩ : syracuseStep 2818595 = 4227893) B4227893
theorem B6341165 : Blo 1877140 6341165 := bstep (se 3 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 6341165 = 2377937) B2377937
theorem B2818625 : Blo 1877140 2818625 := bstep (se 2 (by rfl) ⟨1056984, by rfl⟩ : syracuseStep 2818625 = 2113969) B2113969
theorem B10691149 : Blo 1877140 10691149 := bstep (se 3 (by rfl) ⟨2004590, by rfl⟩ : syracuseStep 10691149 = 4009181) B4009181
theorem B2818643 : Blo 1877140 2818643 := bstep (se 1 (by rfl) ⟨2113982, by rfl⟩ : syracuseStep 2818643 = 4227965) B4227965
theorem B6341219 : Blo 1877140 6341219 := bstep (se 1 (by rfl) ⟨4755914, by rfl⟩ : syracuseStep 6341219 = 9511829) B9511829
theorem B2818673 : Blo 1877140 2818673 := bstep (se 2 (by rfl) ⟨1057002, by rfl⟩ : syracuseStep 2818673 = 2114005) B2114005
theorem B3007091 : Blo 1877140 3007091 := bstep (se 1 (by rfl) ⟨2255318, by rfl⟩ : syracuseStep 3007091 = 4510637) B4510637
theorem B2376307 : Blo 1877140 2376307 := bstep (se 1 (by rfl) ⟨1782230, by rfl⟩ : syracuseStep 2376307 = 3564461) B3564461
theorem B3170947 : Blo 1877140 3170947 := bstep (se 1 (by rfl) ⟨2378210, by rfl⟩ : syracuseStep 3170947 = 4756421) B4756421
theorem B2818691 : Blo 1877140 2818691 := bstep (se 1 (by rfl) ⟨2114018, by rfl⟩ : syracuseStep 2818691 = 4228037) B4228037
theorem B10699397 : Blo 1877140 10699397 := bstep (se 4 (by rfl) ⟨1003068, by rfl⟩ : syracuseStep 10699397 = 2006137) B2006137
theorem B4752017 : Blo 1877140 4752017 := bstep (se 2 (by rfl) ⟨1782006, by rfl⟩ : syracuseStep 4752017 = 3564013) B3564013
theorem B4752067 : Blo 1877140 4752067 := bstep (se 1 (by rfl) ⟨3564050, by rfl⟩ : syracuseStep 4752067 = 7128101) B7128101
theorem B8020721 : Blo 1877140 8020721 := bstep (se 2 (by rfl) ⟨3007770, by rfl⟩ : syracuseStep 8020721 = 6015541) B6015541
theorem B8569585 : Blo 1877140 8569585 := bstep (se 2 (by rfl) ⟨3213594, by rfl⟩ : syracuseStep 8569585 = 6427189) B6427189
theorem B4227857 : Blo 1877140 4227857 := bstep (se 2 (by rfl) ⟨1585446, by rfl⟩ : syracuseStep 4227857 = 3170893) B3170893
theorem B54125333 : Blo 1877140 54125333 := bstep (se 6 (by rfl) ⟨1268562, by rfl⟩ : syracuseStep 54125333 = 2537125) B2537125
theorem B4227875 : Blo 1877140 4227875 := bstep (se 1 (by rfl) ⟨3170906, by rfl⟩ : syracuseStep 4227875 = 6341813) B6341813
theorem B4752209 : Blo 1877140 4752209 := bstep (se 2 (by rfl) ⟨1782078, by rfl⟩ : syracuseStep 4752209 = 3564157) B3564157
theorem B3212131 : Blo 1877140 3212131 := bstep (se 1 (by rfl) ⟨2409098, by rfl⟩ : syracuseStep 3212131 = 4818197) B4818197
theorem B6341489 : Blo 1877140 6341489 := bstep (se 2 (by rfl) ⟨2378058, by rfl⟩ : syracuseStep 6341489 = 4756117) B4756117
theorem B3007361 : Blo 1877140 3007361 := bstep (se 2 (by rfl) ⟨1127760, by rfl⟩ : syracuseStep 3007361 = 2255521) B2255521
theorem B12034979 : Blo 1877140 12034979 := bstep (se 1 (by rfl) ⟨9026234, by rfl⟩ : syracuseStep 12034979 = 18052469) B18052469
theorem B6013901 : Blo 1877140 6013901 := bstep (se 3 (by rfl) ⟨1127606, by rfl⟩ : syracuseStep 6013901 = 2255213) B2255213
theorem B9503729 : Blo 1877140 9503729 := bstep (se 2 (by rfl) ⟨3563898, by rfl⟩ : syracuseStep 9503729 = 7127797) B7127797
theorem B3564643 : Blo 1877140 3564643 := bstep (se 1 (by rfl) ⟨2673482, by rfl⟩ : syracuseStep 3564643 = 5346965) B5346965
theorem B2376803 : Blo 1877140 2376803 := bstep (se 1 (by rfl) ⟨1782602, by rfl⟩ : syracuseStep 2376803 = 3565205) B3565205
theorem B3007649 : Blo 1877140 3007649 := bstep (se 2 (by rfl) ⟨1127868, by rfl⟩ : syracuseStep 3007649 = 2255737) B2255737
theorem B1877155 : Blo 1877140 1877155 := bstep (se 1 (by rfl) ⟨1407866, by rfl⟩ : syracuseStep 1877155 = 2815733) B2815733
theorem B1877171 : Blo 1877140 1877171 := bstep (se 1 (by rfl) ⟨1407878, by rfl⟩ : syracuseStep 1877171 = 2815757) B2815757
theorem B1877187 : Blo 1877140 1877187 := bstep (se 1 (by rfl) ⟨1407890, by rfl⟩ : syracuseStep 1877187 = 2815781) B2815781
theorem B4515011 : Blo 1877140 4515011 := bstep (se 1 (by rfl) ⟨3386258, by rfl⟩ : syracuseStep 4515011 = 6772517) B6772517
theorem B7128269 : Blo 1877140 7128269 := bstep (se 3 (by rfl) ⟨1336550, by rfl⟩ : syracuseStep 7128269 = 2673101) B2673101
theorem B1877203 : Blo 1877140 1877203 := bstep (se 1 (by rfl) ⟨1407902, by rfl⟩ : syracuseStep 1877203 = 2815805) B2815805
theorem B1877219 : Blo 1877140 1877219 := bstep (se 1 (by rfl) ⟨1407914, by rfl⟩ : syracuseStep 1877219 = 2815829) B2815829
theorem B58623203 : Blo 1877140 58623203 := bstep (se 1 (by rfl) ⟨43967402, by rfl⟩ : syracuseStep 58623203 = 87934805) B87934805
theorem B1877235 : Blo 1877140 1877235 := bstep (se 1 (by rfl) ⟨1407926, by rfl⟩ : syracuseStep 1877235 = 2815853) B2815853
theorem B1877251 : Blo 1877140 1877251 := bstep (se 1 (by rfl) ⟨1407938, by rfl⟩ : syracuseStep 1877251 = 2815877) B2815877
theorem B3564803 : Blo 1877140 3564803 := bstep (se 1 (by rfl) ⟨2673602, by rfl⟩ : syracuseStep 3564803 = 5347205) B5347205
theorem B1877267 : Blo 1877140 1877267 := bstep (se 1 (by rfl) ⟨1407950, by rfl⟩ : syracuseStep 1877267 = 2815901) B2815901
theorem B1877283 : Blo 1877140 1877283 := bstep (se 1 (by rfl) ⟨1407962, by rfl⟩ : syracuseStep 1877283 = 2815925) B2815925
theorem B1877299 : Blo 1877140 1877299 := bstep (se 1 (by rfl) ⟨1407974, by rfl⟩ : syracuseStep 1877299 = 2815949) B2815949
theorem B1877315 : Blo 1877140 1877315 := bstep (se 1 (by rfl) ⟨1407986, by rfl⟩ : syracuseStep 1877315 = 2815973) B2815973
theorem B1877331 : Blo 1877140 1877331 := bstep (se 1 (by rfl) ⟨1407998, by rfl⟩ : syracuseStep 1877331 = 2815997) B2815997
theorem B1877347 : Blo 1877140 1877347 := bstep (se 1 (by rfl) ⟨1408010, by rfl⟩ : syracuseStep 1877347 = 2816021) B2816021
theorem B5350769 : Blo 1877140 5350769 := bstep (se 2 (by rfl) ⟨2006538, by rfl⟩ : syracuseStep 5350769 = 4013077) B4013077
theorem B1877363 : Blo 1877140 1877363 := bstep (se 1 (by rfl) ⟨1408022, by rfl⟩ : syracuseStep 1877363 = 2816045) B2816045
theorem B1877379 : Blo 1877140 1877379 := bstep (se 1 (by rfl) ⟨1408034, by rfl⟩ : syracuseStep 1877379 = 2816069) B2816069
theorem B6342029 : Blo 1877140 6342029 := bstep (se 3 (by rfl) ⟨1189130, by rfl⟩ : syracuseStep 6342029 = 2378261) B2378261
theorem B1877395 : Blo 1877140 1877395 := bstep (se 1 (by rfl) ⟨1408046, by rfl⟩ : syracuseStep 1877395 = 2816093) B2816093
theorem B1877411 : Blo 1877140 1877411 := bstep (se 1 (by rfl) ⟨1408058, by rfl⟩ : syracuseStep 1877411 = 2816117) B2816117
theorem B1877427 : Blo 1877140 1877427 := bstep (se 1 (by rfl) ⟨1408070, by rfl⟩ : syracuseStep 1877427 = 2816141) B2816141
theorem B1877443 : Blo 1877140 1877443 := bstep (se 1 (by rfl) ⟨1408082, by rfl⟩ : syracuseStep 1877443 = 2816165) B2816165
theorem B6342083 : Blo 1877140 6342083 := bstep (se 1 (by rfl) ⟨4756562, by rfl⟩ : syracuseStep 6342083 = 9513125) B9513125
theorem B15230405 : Blo 1877140 15230405 := bstep (se 4 (by rfl) ⟨1427850, by rfl⟩ : syracuseStep 15230405 = 2855701) B2855701
theorem B1877459 : Blo 1877140 1877459 := bstep (se 1 (by rfl) ⟨1408094, by rfl⟩ : syracuseStep 1877459 = 2816189) B2816189
theorem B1877475 : Blo 1877140 1877475 := bstep (se 1 (by rfl) ⟨1408106, by rfl⟩ : syracuseStep 1877475 = 2816213) B2816213
theorem B1877491 : Blo 1877140 1877491 := bstep (se 1 (by rfl) ⟨1408118, by rfl⟩ : syracuseStep 1877491 = 2816237) B2816237
theorem B1877507 : Blo 1877140 1877507 := bstep (se 1 (by rfl) ⟨1408130, by rfl⟩ : syracuseStep 1877507 = 2816261) B2816261
theorem B3712529 : Blo 1877140 3712529 := bstep (se 2 (by rfl) ⟨1392198, by rfl⟩ : syracuseStep 3712529 = 2784397) B2784397
theorem B1877523 : Blo 1877140 1877523 := bstep (se 1 (by rfl) ⟨1408142, by rfl⟩ : syracuseStep 1877523 = 2816285) B2816285
theorem B1877539 : Blo 1877140 1877539 := bstep (se 1 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 1877539 = 2816309) B2816309
theorem B1877555 : Blo 1877140 1877555 := bstep (se 1 (by rfl) ⟨1408166, by rfl⟩ : syracuseStep 1877555 = 2816333) B2816333
theorem B3008065 : Blo 1877140 3008065 := bstep (se 2 (by rfl) ⟨1128024, by rfl⟩ : syracuseStep 3008065 = 2256049) B2256049
theorem B1877571 : Blo 1877140 1877571 := bstep (se 1 (by rfl) ⟨1408178, by rfl⟩ : syracuseStep 1877571 = 2816357) B2816357
theorem B1877587 : Blo 1877140 1877587 := bstep (se 1 (by rfl) ⟨1408190, by rfl⟩ : syracuseStep 1877587 = 2816381) B2816381
theorem B1877603 : Blo 1877140 1877603 := bstep (se 1 (by rfl) ⟨1408202, by rfl⟩ : syracuseStep 1877603 = 2816405) B2816405
theorem B1877619 : Blo 1877140 1877619 := bstep (se 1 (by rfl) ⟨1408214, by rfl⟩ : syracuseStep 1877619 = 2816429) B2816429
theorem B1877635 : Blo 1877140 1877635 := bstep (se 1 (by rfl) ⟨1408226, by rfl⟩ : syracuseStep 1877635 = 2816453) B2816453
theorem B1877651 : Blo 1877140 1877651 := bstep (se 1 (by rfl) ⟨1408238, by rfl⟩ : syracuseStep 1877651 = 2816477) B2816477
theorem B1877667 : Blo 1877140 1877667 := bstep (se 1 (by rfl) ⟨1408250, by rfl⟩ : syracuseStep 1877667 = 2816501) B2816501
theorem B1877683 : Blo 1877140 1877683 := bstep (se 1 (by rfl) ⟨1408262, by rfl⟩ : syracuseStep 1877683 = 2816525) B2816525
theorem B1877699 : Blo 1877140 1877699 := bstep (se 1 (by rfl) ⟨1408274, by rfl⟩ : syracuseStep 1877699 = 2816549) B2816549
theorem B1877715 : Blo 1877140 1877715 := bstep (se 1 (by rfl) ⟨1408286, by rfl⟩ : syracuseStep 1877715 = 2816573) B2816573
theorem B1877731 : Blo 1877140 1877731 := bstep (se 1 (by rfl) ⟨1408298, by rfl⟩ : syracuseStep 1877731 = 2816597) B2816597
theorem B1877747 : Blo 1877140 1877747 := bstep (se 1 (by rfl) ⟨1408310, by rfl⟩ : syracuseStep 1877747 = 2816621) B2816621
theorem B1877763 : Blo 1877140 1877763 := bstep (se 1 (by rfl) ⟨1408322, by rfl⟩ : syracuseStep 1877763 = 2816645) B2816645
theorem B1877779 : Blo 1877140 1877779 := bstep (se 1 (by rfl) ⟨1408334, by rfl⟩ : syracuseStep 1877779 = 2816669) B2816669
theorem B1877795 : Blo 1877140 1877795 := bstep (se 1 (by rfl) ⟨1408346, by rfl⟩ : syracuseStep 1877795 = 2816693) B2816693
theorem B2377507 : Blo 1877140 2377507 := bstep (se 1 (by rfl) ⟨1783130, by rfl⟩ : syracuseStep 2377507 = 3566261) B3566261
theorem B4753201 : Blo 1877140 4753201 := bstep (se 2 (by rfl) ⟨1782450, by rfl⟩ : syracuseStep 4753201 = 3564901) B3564901
theorem B1877811 : Blo 1877140 1877811 := bstep (se 1 (by rfl) ⟨1408358, by rfl⟩ : syracuseStep 1877811 = 2816717) B2816717
theorem B1877827 : Blo 1877140 1877827 := bstep (se 1 (by rfl) ⟨1408370, by rfl⟩ : syracuseStep 1877827 = 2816741) B2816741
theorem B1877843 : Blo 1877140 1877843 := bstep (se 1 (by rfl) ⟨1408382, by rfl⟩ : syracuseStep 1877843 = 2816765) B2816765
theorem B1877859 : Blo 1877140 1877859 := bstep (se 1 (by rfl) ⟨1408394, by rfl⟩ : syracuseStep 1877859 = 2816789) B2816789
theorem B1877875 : Blo 1877140 1877875 := bstep (se 1 (by rfl) ⟨1408406, by rfl⟩ : syracuseStep 1877875 = 2816813) B2816813
theorem B1877891 : Blo 1877140 1877891 := bstep (se 1 (by rfl) ⟨1408418, by rfl⟩ : syracuseStep 1877891 = 2816837) B2816837
theorem B2377603 : Blo 1877140 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B1877907 : Blo 1877140 1877907 := bstep (se 1 (by rfl) ⟨1408430, by rfl⟩ : syracuseStep 1877907 = 2816861) B2816861
theorem B1877923 : Blo 1877140 1877923 := bstep (se 1 (by rfl) ⟨1408442, by rfl⟩ : syracuseStep 1877923 = 2816885) B2816885
theorem B1877939 : Blo 1877140 1877939 := bstep (se 1 (by rfl) ⟨1408454, by rfl⟩ : syracuseStep 1877939 = 2816909) B2816909
theorem B1877955 : Blo 1877140 1877955 := bstep (se 1 (by rfl) ⟨1408466, by rfl⟩ : syracuseStep 1877955 = 2816933) B2816933
theorem B1877971 : Blo 1877140 1877971 := bstep (se 1 (by rfl) ⟨1408478, by rfl⟩ : syracuseStep 1877971 = 2816957) B2816957
theorem B1877987 : Blo 1877140 1877987 := bstep (se 1 (by rfl) ⟨1408490, by rfl⟩ : syracuseStep 1877987 = 2816981) B2816981
theorem B7129073 : Blo 1877140 7129073 := bstep (se 2 (by rfl) ⟨2673402, by rfl⟩ : syracuseStep 7129073 = 5346805) B5346805
theorem B1878003 : Blo 1877140 1878003 := bstep (se 1 (by rfl) ⟨1408502, by rfl⟩ : syracuseStep 1878003 = 2817005) B2817005
theorem B1878019 : Blo 1877140 1878019 := bstep (se 1 (by rfl) ⟨1408514, by rfl⟩ : syracuseStep 1878019 = 2817029) B2817029
theorem B17139725 : Blo 1877140 17139725 := bstep (se 3 (by rfl) ⟨3213698, by rfl⟩ : syracuseStep 17139725 = 6427397) B6427397
theorem B1878035 : Blo 1877140 1878035 := bstep (se 1 (by rfl) ⟨1408526, by rfl⟩ : syracuseStep 1878035 = 2817053) B2817053
theorem B1878051 : Blo 1877140 1878051 := bstep (se 1 (by rfl) ⟨1408538, by rfl⟩ : syracuseStep 1878051 = 2817077) B2817077
theorem B12027953 : Blo 1877140 12027953 := bstep (se 2 (by rfl) ⟨4510482, by rfl⟩ : syracuseStep 12027953 = 9020965) B9020965
theorem B1878067 : Blo 1877140 1878067 := bstep (se 1 (by rfl) ⟨1408550, by rfl⟩ : syracuseStep 1878067 = 2817101) B2817101
theorem B4753475 : Blo 1877140 4753475 := bstep (se 1 (by rfl) ⟨3565106, by rfl⟩ : syracuseStep 4753475 = 7130213) B7130213
theorem B1878083 : Blo 1877140 1878083 := bstep (se 1 (by rfl) ⟨1408562, by rfl⟩ : syracuseStep 1878083 = 2817125) B2817125
theorem B1878099 : Blo 1877140 1878099 := bstep (se 1 (by rfl) ⟨1408574, by rfl⟩ : syracuseStep 1878099 = 2817149) B2817149
theorem B1878115 : Blo 1877140 1878115 := bstep (se 1 (by rfl) ⟨1408586, by rfl⟩ : syracuseStep 1878115 = 2817173) B2817173
theorem B9029731 : Blo 1877140 9029731 := bstep (se 1 (by rfl) ⟨6772298, by rfl⟩ : syracuseStep 9029731 = 13544597) B13544597
theorem B1878131 : Blo 1877140 1878131 := bstep (se 1 (by rfl) ⟨1408598, by rfl⟩ : syracuseStep 1878131 = 2817197) B2817197
theorem B1878147 : Blo 1877140 1878147 := bstep (se 1 (by rfl) ⟨1408610, by rfl⟩ : syracuseStep 1878147 = 2817221) B2817221
theorem B9021581 : Blo 1877140 9021581 := bstep (se 3 (by rfl) ⟨1691546, by rfl⟩ : syracuseStep 9021581 = 3383093) B3383093
theorem B1878163 : Blo 1877140 1878163 := bstep (se 1 (by rfl) ⟨1408622, by rfl⟩ : syracuseStep 1878163 = 2817245) B2817245
theorem B1878179 : Blo 1877140 1878179 := bstep (se 1 (by rfl) ⟨1408634, by rfl⟩ : syracuseStep 1878179 = 2817269) B2817269
theorem B1878195 : Blo 1877140 1878195 := bstep (se 1 (by rfl) ⟨1408646, by rfl⟩ : syracuseStep 1878195 = 2817293) B2817293
theorem B2672833 : Blo 1877140 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B6424771 : Blo 1877140 6424771 := bstep (se 1 (by rfl) ⟨4818578, by rfl⟩ : syracuseStep 6424771 = 9637157) B9637157
theorem B1878211 : Blo 1877140 1878211 := bstep (se 1 (by rfl) ⟨1408658, by rfl⟩ : syracuseStep 1878211 = 2817317) B2817317
theorem B1878227 : Blo 1877140 1878227 := bstep (se 1 (by rfl) ⟨1408670, by rfl⟩ : syracuseStep 1878227 = 2817341) B2817341
theorem B1878243 : Blo 1877140 1878243 := bstep (se 1 (by rfl) ⟨1408682, by rfl⟩ : syracuseStep 1878243 = 2817365) B2817365
theorem B1878259 : Blo 1877140 1878259 := bstep (se 1 (by rfl) ⟨1408694, by rfl⟩ : syracuseStep 1878259 = 2817389) B2817389
theorem B4753667 : Blo 1877140 4753667 := bstep (se 1 (by rfl) ⟨3565250, by rfl⟩ : syracuseStep 4753667 = 7130501) B7130501
theorem B1878275 : Blo 1877140 1878275 := bstep (se 1 (by rfl) ⟨1408706, by rfl⟩ : syracuseStep 1878275 = 2817413) B2817413
theorem B1878291 : Blo 1877140 1878291 := bstep (se 1 (by rfl) ⟨1408718, by rfl⟩ : syracuseStep 1878291 = 2817437) B2817437
theorem B1878307 : Blo 1877140 1878307 := bstep (se 1 (by rfl) ⟨1408730, by rfl⟩ : syracuseStep 1878307 = 2817461) B2817461
theorem B3565873 : Blo 1877140 3565873 := bstep (se 2 (by rfl) ⟨1337202, by rfl⟩ : syracuseStep 3565873 = 2674405) B2674405
theorem B2672947 : Blo 1877140 2672947 := bstep (se 1 (by rfl) ⟨2004710, by rfl⟩ : syracuseStep 2672947 = 4009421) B4009421
theorem B1878323 : Blo 1877140 1878323 := bstep (se 1 (by rfl) ⟨1408742, by rfl⟩ : syracuseStep 1878323 = 2817485) B2817485
theorem B37087541 : Blo 1877140 37087541 := bstep (se 5 (by rfl) ⟨1738478, by rfl⟩ : syracuseStep 37087541 = 3476957) B3476957
theorem B1878339 : Blo 1877140 1878339 := bstep (se 1 (by rfl) ⟨1408754, by rfl⟩ : syracuseStep 1878339 = 2817509) B2817509
theorem B3385681 : Blo 1877140 3385681 := bstep (se 2 (by rfl) ⟨1269630, by rfl⟩ : syracuseStep 3385681 = 2539261) B2539261
theorem B1878355 : Blo 1877140 1878355 := bstep (se 1 (by rfl) ⟨1408766, by rfl⟩ : syracuseStep 1878355 = 2817533) B2817533
theorem B1878371 : Blo 1877140 1878371 := bstep (se 1 (by rfl) ⟨1408778, by rfl⟩ : syracuseStep 1878371 = 2817557) B2817557
theorem B1878387 : Blo 1877140 1878387 := bstep (se 1 (by rfl) ⟨1408790, by rfl⟩ : syracuseStep 1878387 = 2817581) B2817581
theorem B2378099 : Blo 1877140 2378099 := bstep (se 1 (by rfl) ⟨1783574, by rfl⟩ : syracuseStep 2378099 = 3567149) B3567149
theorem B1878403 : Blo 1877140 1878403 := bstep (se 1 (by rfl) ⟨1408802, by rfl⟩ : syracuseStep 1878403 = 2817605) B2817605
theorem B1878419 : Blo 1877140 1878419 := bstep (se 1 (by rfl) ⟨1408814, by rfl⟩ : syracuseStep 1878419 = 2817629) B2817629
theorem B9505187 : Blo 1877140 9505187 := bstep (se 1 (by rfl) ⟨7128890, by rfl⟩ : syracuseStep 9505187 = 14257781) B14257781
theorem B1878435 : Blo 1877140 1878435 := bstep (se 1 (by rfl) ⟨1408826, by rfl⟩ : syracuseStep 1878435 = 2817653) B2817653
theorem B1878451 : Blo 1877140 1878451 := bstep (se 1 (by rfl) ⟨1408838, by rfl⟩ : syracuseStep 1878451 = 2817677) B2817677
theorem B1878467 : Blo 1877140 1878467 := bstep (se 1 (by rfl) ⟨1408850, by rfl⟩ : syracuseStep 1878467 = 2817701) B2817701
theorem B3008963 : Blo 1877140 3008963 := bstep (se 1 (by rfl) ⟨2256722, by rfl⟩ : syracuseStep 3008963 = 4513445) B4513445
theorem B4819409 : Blo 1877140 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B1878483 : Blo 1877140 1878483 := bstep (se 1 (by rfl) ⟨1408862, by rfl⟩ : syracuseStep 1878483 = 2817725) B2817725
theorem B1878499 : Blo 1877140 1878499 := bstep (se 1 (by rfl) ⟨1408874, by rfl⟩ : syracuseStep 1878499 = 2817749) B2817749
theorem B12192241 : Blo 1877140 12192241 := bstep (se 2 (by rfl) ⟨4572090, by rfl⟩ : syracuseStep 12192241 = 9144181) B9144181
theorem B8129009 : Blo 1877140 8129009 := bstep (se 2 (by rfl) ⟨3048378, by rfl⟩ : syracuseStep 8129009 = 6096757) B6096757
theorem B1878515 : Blo 1877140 1878515 := bstep (se 1 (by rfl) ⟨1408886, by rfl⟩ : syracuseStep 1878515 = 2817773) B2817773
theorem B1878531 : Blo 1877140 1878531 := bstep (se 1 (by rfl) ⟨1408898, by rfl⟩ : syracuseStep 1878531 = 2817797) B2817797
theorem B10693133 : Blo 1877140 10693133 := bstep (se 3 (by rfl) ⟨2004962, by rfl⟩ : syracuseStep 10693133 = 4009925) B4009925
theorem B1878547 : Blo 1877140 1878547 := bstep (se 1 (by rfl) ⟨1408910, by rfl⟩ : syracuseStep 1878547 = 2817821) B2817821
theorem B1878563 : Blo 1877140 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B1878579 : Blo 1877140 1878579 := bstep (se 1 (by rfl) ⟨1408934, by rfl⟩ : syracuseStep 1878579 = 2817869) B2817869
theorem B1878595 : Blo 1877140 1878595 := bstep (se 1 (by rfl) ⟨1408946, by rfl⟩ : syracuseStep 1878595 = 2817893) B2817893
theorem B6425165 : Blo 1877140 6425165 := bstep (se 3 (by rfl) ⟨1204718, by rfl⟩ : syracuseStep 6425165 = 2409437) B2409437
theorem B1878611 : Blo 1877140 1878611 := bstep (se 1 (by rfl) ⟨1408958, by rfl⟩ : syracuseStep 1878611 = 2817917) B2817917
theorem B1878627 : Blo 1877140 1878627 := bstep (se 1 (by rfl) ⟨1408970, by rfl⟩ : syracuseStep 1878627 = 2817941) B2817941
theorem B3213923 : Blo 1877140 3213923 := bstep (se 1 (by rfl) ⟨2410442, by rfl⟩ : syracuseStep 3213923 = 4820885) B4820885
theorem B1878643 : Blo 1877140 1878643 := bstep (se 1 (by rfl) ⟨1408982, by rfl⟩ : syracuseStep 1878643 = 2817965) B2817965
theorem B6425219 : Blo 1877140 6425219 := bstep (se 1 (by rfl) ⟨4818914, by rfl⟩ : syracuseStep 6425219 = 9637829) B9637829
theorem B1878659 : Blo 1877140 1878659 := bstep (se 1 (by rfl) ⟨1408994, by rfl⟩ : syracuseStep 1878659 = 2817989) B2817989
theorem B7129741 : Blo 1877140 7129741 := bstep (se 3 (by rfl) ⟨1336826, by rfl⟩ : syracuseStep 7129741 = 2673653) B2673653
theorem B1878675 : Blo 1877140 1878675 := bstep (se 1 (by rfl) ⟨1409006, by rfl⟩ : syracuseStep 1878675 = 2818013) B2818013
theorem B3009187 : Blo 1877140 3009187 := bstep (se 1 (by rfl) ⟨2256890, by rfl⟩ : syracuseStep 3009187 = 4513781) B4513781
theorem B1878691 : Blo 1877140 1878691 := bstep (se 1 (by rfl) ⟨1409018, by rfl⟩ : syracuseStep 1878691 = 2818037) B2818037
theorem B1878707 : Blo 1877140 1878707 := bstep (se 1 (by rfl) ⟨1409030, by rfl⟩ : syracuseStep 1878707 = 2818061) B2818061
theorem B1878723 : Blo 1877140 1878723 := bstep (se 1 (by rfl) ⟨1409042, by rfl⟩ : syracuseStep 1878723 = 2818085) B2818085
theorem B12028621 : Blo 1877140 12028621 := bstep (se 3 (by rfl) ⟨2255366, by rfl⟩ : syracuseStep 12028621 = 4510733) B4510733
theorem B1878739 : Blo 1877140 1878739 := bstep (se 1 (by rfl) ⟨1409054, by rfl⟩ : syracuseStep 1878739 = 2818109) B2818109
theorem B1903331 : Blo 1877140 1903331 := bstep (se 1 (by rfl) ⟨1427498, by rfl⟩ : syracuseStep 1903331 = 2854997) B2854997
theorem B1878755 : Blo 1877140 1878755 := bstep (se 1 (by rfl) ⟨1409066, by rfl⟩ : syracuseStep 1878755 = 2818133) B2818133
theorem B1878771 : Blo 1877140 1878771 := bstep (se 1 (by rfl) ⟨1409078, by rfl⟩ : syracuseStep 1878771 = 2818157) B2818157
theorem B1878787 : Blo 1877140 1878787 := bstep (se 1 (by rfl) ⟨1409090, by rfl⟩ : syracuseStep 1878787 = 2818181) B2818181
theorem B1903379 : Blo 1877140 1903379 := bstep (se 1 (by rfl) ⟨1427534, by rfl⟩ : syracuseStep 1903379 = 2855069) B2855069
theorem B1878803 : Blo 1877140 1878803 := bstep (se 1 (by rfl) ⟨1409102, by rfl⟩ : syracuseStep 1878803 = 2818205) B2818205
theorem B1878819 : Blo 1877140 1878819 := bstep (se 1 (by rfl) ⟨1409114, by rfl⟩ : syracuseStep 1878819 = 2818229) B2818229
theorem B1878835 : Blo 1877140 1878835 := bstep (se 1 (by rfl) ⟨1409126, by rfl⟩ : syracuseStep 1878835 = 2818253) B2818253
theorem B27077429 : Blo 1877140 27077429 := bstep (se 5 (by rfl) ⟨1269254, by rfl⟩ : syracuseStep 27077429 = 2538509) B2538509
theorem B1878851 : Blo 1877140 1878851 := bstep (se 1 (by rfl) ⟨1409138, by rfl⟩ : syracuseStep 1878851 = 2818277) B2818277
theorem B1878867 : Blo 1877140 1878867 := bstep (se 1 (by rfl) ⟨1409150, by rfl⟩ : syracuseStep 1878867 = 2818301) B2818301
theorem B1878883 : Blo 1877140 1878883 := bstep (se 1 (by rfl) ⟨1409162, by rfl⟩ : syracuseStep 1878883 = 2818325) B2818325
theorem B1878899 : Blo 1877140 1878899 := bstep (se 1 (by rfl) ⟨1409174, by rfl⟩ : syracuseStep 1878899 = 2818349) B2818349
theorem B1878915 : Blo 1877140 1878915 := bstep (se 1 (by rfl) ⟨1409186, by rfl⟩ : syracuseStep 1878915 = 2818373) B2818373
theorem B1878931 : Blo 1877140 1878931 := bstep (se 1 (by rfl) ⟨1409198, by rfl⟩ : syracuseStep 1878931 = 2818397) B2818397
theorem B1878947 : Blo 1877140 1878947 := bstep (se 1 (by rfl) ⟨1409210, by rfl⟩ : syracuseStep 1878947 = 2818421) B2818421
theorem B1878963 : Blo 1877140 1878963 := bstep (se 1 (by rfl) ⟨1409222, by rfl⟩ : syracuseStep 1878963 = 2818445) B2818445
theorem B1878979 : Blo 1877140 1878979 := bstep (se 1 (by rfl) ⟨1409234, by rfl⟩ : syracuseStep 1878979 = 2818469) B2818469
theorem B6335441 : Blo 1877140 6335441 := bstep (se 2 (by rfl) ⟨2375790, by rfl⟩ : syracuseStep 6335441 = 4751581) B4751581
theorem B1878995 : Blo 1877140 1878995 := bstep (se 1 (by rfl) ⟨1409246, by rfl⟩ : syracuseStep 1878995 = 2818493) B2818493
theorem B1879011 : Blo 1877140 1879011 := bstep (se 1 (by rfl) ⟨1409258, by rfl⟩ : syracuseStep 1879011 = 2818517) B2818517
theorem B1879027 : Blo 1877140 1879027 := bstep (se 1 (by rfl) ⟨1409270, by rfl⟩ : syracuseStep 1879027 = 2818541) B2818541
theorem B1879043 : Blo 1877140 1879043 := bstep (se 1 (by rfl) ⟨1409282, by rfl⟩ : syracuseStep 1879043 = 2818565) B2818565
theorem B7613453 : Blo 1877140 7613453 := bstep (se 3 (by rfl) ⟨1427522, by rfl⟩ : syracuseStep 7613453 = 2855045) B2855045
theorem B1879059 : Blo 1877140 1879059 := bstep (se 1 (by rfl) ⟨1409294, by rfl⟩ : syracuseStep 1879059 = 2818589) B2818589
theorem B1879075 : Blo 1877140 1879075 := bstep (se 1 (by rfl) ⟨1409306, by rfl⟩ : syracuseStep 1879075 = 2818613) B2818613
theorem B1879091 : Blo 1877140 1879091 := bstep (se 1 (by rfl) ⟨1409318, by rfl⟩ : syracuseStep 1879091 = 2818637) B2818637
theorem B1879107 : Blo 1877140 1879107 := bstep (se 1 (by rfl) ⟨1409330, by rfl⟩ : syracuseStep 1879107 = 2818661) B2818661
theorem B1879123 : Blo 1877140 1879123 := bstep (se 1 (by rfl) ⟨1409342, by rfl⟩ : syracuseStep 1879123 = 2818685) B2818685
theorem B1879139 : Blo 1877140 1879139 := bstep (se 1 (by rfl) ⟨1409354, by rfl⟩ : syracuseStep 1879139 = 2818709) B2818709
theorem B4009105 : Blo 1877140 4009105 := bstep (se 2 (by rfl) ⟨1503414, by rfl⟩ : syracuseStep 4009105 = 3006829) B3006829
theorem B4754609 : Blo 1877140 4754609 := bstep (se 2 (by rfl) ⟨1782978, by rfl⟩ : syracuseStep 4754609 = 3565957) B3565957
theorem B9505997 : Blo 1877140 9505997 := bstep (se 3 (by rfl) ⟨1782374, by rfl⟩ : syracuseStep 9505997 = 3564749) B3564749
theorem B4754659 : Blo 1877140 4754659 := bstep (se 1 (by rfl) ⟨3565994, by rfl⟩ : syracuseStep 4754659 = 7131989) B7131989
theorem B9637169 : Blo 1877140 9637169 := bstep (se 2 (by rfl) ⟨3613938, by rfl⟩ : syracuseStep 9637169 = 7227877) B7227877
theorem B3566929 : Blo 1877140 3566929 := bstep (se 2 (by rfl) ⟨1337598, by rfl⟩ : syracuseStep 3566929 = 2675197) B2675197
theorem B5074285 : Blo 1877140 5074285 := bstep (se 3 (by rfl) ⟨951428, by rfl⟩ : syracuseStep 5074285 = 1902857) B1902857
theorem B4754801 : Blo 1877140 4754801 := bstep (se 2 (by rfl) ⟨1783050, by rfl⟩ : syracuseStep 4754801 = 3566101) B3566101
theorem B7130531 : Blo 1877140 7130531 := bstep (se 1 (by rfl) ⟨5347898, by rfl⟩ : syracuseStep 7130531 = 10695797) B10695797
theorem B10694065 : Blo 1877140 10694065 := bstep (se 2 (by rfl) ⟨4010274, by rfl⟩ : syracuseStep 10694065 = 8020549) B8020549
theorem B6335981 : Blo 1877140 6335981 := bstep (se 3 (by rfl) ⟨1187996, by rfl⟩ : syracuseStep 6335981 = 2375993) B2375993
theorem B2141699 : Blo 1877140 2141699 := bstep (se 1 (by rfl) ⟨1606274, by rfl⟩ : syracuseStep 2141699 = 3212549) B3212549
theorem B6336035 : Blo 1877140 6336035 := bstep (se 1 (by rfl) ⟨4752026, by rfl⟩ : syracuseStep 6336035 = 9504053) B9504053
theorem B2674291 : Blo 1877140 2674291 := bstep (se 1 (by rfl) ⟨2005718, by rfl⟩ : syracuseStep 2674291 = 4011437) B4011437
theorem B6016643 : Blo 1877140 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B8023693 : Blo 1877140 8023693 := bstep (se 3 (by rfl) ⟨1504442, by rfl⟩ : syracuseStep 8023693 = 3008885) B3008885
theorem B10153649 : Blo 1877140 10153649 := bstep (se 2 (by rfl) ⟨3807618, by rfl⟩ : syracuseStep 10153649 = 7615237) B7615237
theorem B3567331 : Blo 1877140 3567331 := bstep (se 1 (by rfl) ⟨2675498, by rfl⟩ : syracuseStep 3567331 = 5350997) B5350997
theorem B6016771 : Blo 1877140 6016771 := bstep (se 1 (by rfl) ⟨4512578, by rfl⟩ : syracuseStep 6016771 = 9025157) B9025157
theorem B3567377 : Blo 1877140 3567377 := bstep (se 2 (by rfl) ⟨1337766, by rfl⟩ : syracuseStep 3567377 = 2675533) B2675533
theorem B4009763 : Blo 1877140 4009763 := bstep (se 1 (by rfl) ⟨3007322, by rfl⟩ : syracuseStep 4009763 = 6014645) B6014645
theorem B6336305 : Blo 1877140 6336305 := bstep (se 2 (by rfl) ⟨2376114, by rfl⟩ : syracuseStep 6336305 = 4752229) B4752229
theorem B8564621 : Blo 1877140 8564621 := bstep (se 3 (by rfl) ⟨1605866, by rfl⟩ : syracuseStep 8564621 = 3211733) B3211733
theorem B5361617 : Blo 1877140 5361617 := bstep (se 2 (by rfl) ⟨2010606, by rfl⟩ : syracuseStep 5361617 = 4021213) B4021213
theorem B8024035 : Blo 1877140 8024035 := bstep (se 1 (by rfl) ⟨6018026, by rfl⟩ : syracuseStep 8024035 = 12036053) B12036053
theorem B10153997 : Blo 1877140 10153997 := bstep (se 3 (by rfl) ⟨1903874, by rfl⟩ : syracuseStep 10153997 = 3807749) B3807749
theorem B7131185 : Blo 1877140 7131185 := bstep (se 2 (by rfl) ⟨2674194, by rfl⟩ : syracuseStep 7131185 = 5348389) B5348389
theorem B6017105 : Blo 1877140 6017105 := bstep (se 2 (by rfl) ⟨2256414, by rfl⟩ : syracuseStep 6017105 = 4512829) B4512829
theorem B5714029 : Blo 1877140 5714029 := bstep (se 3 (by rfl) ⟨1071380, by rfl⟩ : syracuseStep 5714029 = 2142761) B2142761
theorem B5345507 : Blo 1877140 5345507 := bstep (se 1 (by rfl) ⟨4009130, by rfl⟩ : syracuseStep 5345507 = 8018261) B8018261
theorem B6770915 : Blo 1877140 6770915 := bstep (se 1 (by rfl) ⟨5078186, by rfl⟩ : syracuseStep 6770915 = 10156373) B10156373
theorem B4575523 : Blo 1877140 4575523 := bstep (se 1 (by rfl) ⟨3431642, by rfl⟩ : syracuseStep 4575523 = 6863285) B6863285
theorem B6336845 : Blo 1877140 6336845 := bstep (se 3 (by rfl) ⟨1188158, by rfl⟩ : syracuseStep 6336845 = 2376317) B2376317
theorem B4755793 : Blo 1877140 4755793 := bstep (se 2 (by rfl) ⟨1783422, by rfl⟩ : syracuseStep 4755793 = 3566845) B3566845
theorem B6336899 : Blo 1877140 6336899 := bstep (se 1 (by rfl) ⟨4752674, by rfl⟩ : syracuseStep 6336899 = 9505349) B9505349
theorem B24400325 : Blo 1877140 24400325 := bstep (se 4 (by rfl) ⟨2287530, by rfl⟩ : syracuseStep 24400325 = 4575061) B4575061
theorem B16036451 : Blo 1877140 16036451 := bstep (se 1 (by rfl) ⟨12027338, by rfl⟩ : syracuseStep 16036451 = 24054677) B24054677
theorem B4756067 : Blo 1877140 4756067 := bstep (se 1 (by rfl) ⟨3567050, by rfl⟩ : syracuseStep 4756067 = 7134101) B7134101
theorem B4010609 : Blo 1877140 4010609 := bstep (se 2 (by rfl) ⟨1503978, by rfl⟩ : syracuseStep 4010609 = 3007957) B3007957
theorem B6337169 : Blo 1877140 6337169 := bstep (se 2 (by rfl) ⟨2376438, by rfl⟩ : syracuseStep 6337169 = 4752877) B4752877
theorem B2855569 : Blo 1877140 2855569 := bstep (se 2 (by rfl) ⟨1070838, by rfl⟩ : syracuseStep 2855569 = 2141677) B2141677
theorem B6771377 : Blo 1877140 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B2675425 : Blo 1877140 2675425 := bstep (se 2 (by rfl) ⟨1003284, by rfl⟩ : syracuseStep 2675425 = 2006569) B2006569
theorem B4756259 : Blo 1877140 4756259 := bstep (se 1 (by rfl) ⟨3567194, by rfl⟩ : syracuseStep 4756259 = 7134389) B7134389
theorem B2675521 : Blo 1877140 2675521 := bstep (se 2 (by rfl) ⟨1003320, by rfl⟩ : syracuseStep 2675521 = 2006641) B2006641
theorem B4223825 : Blo 1877140 4223825 := bstep (se 2 (by rfl) ⟨1583934, by rfl⟩ : syracuseStep 4223825 = 3167869) B3167869
theorem B4223843 : Blo 1877140 4223843 := bstep (se 1 (by rfl) ⟨3167882, by rfl⟩ : syracuseStep 4223843 = 6335765) B6335765
theorem B10695523 : Blo 1877140 10695523 := bstep (se 1 (by rfl) ⟨8021642, by rfl⟩ : syracuseStep 10695523 = 16043285) B16043285
theorem B12039025 : Blo 1877140 12039025 := bstep (se 2 (by rfl) ⟨4514634, by rfl⟩ : syracuseStep 12039025 = 9029269) B9029269
theorem B1930115 : Blo 1877140 1930115 := bstep (se 1 (by rfl) ⟨1447586, by rfl⟩ : syracuseStep 1930115 = 2895173) B2895173
theorem B4224113 : Blo 1877140 4224113 := bstep (se 2 (by rfl) ⟨1584042, by rfl⟩ : syracuseStep 4224113 = 3168085) B3168085
theorem B4224131 : Blo 1877140 4224131 := bstep (se 1 (by rfl) ⟨3168098, by rfl⟩ : syracuseStep 4224131 = 6336197) B6336197
theorem B6337709 : Blo 1877140 6337709 := bstep (se 3 (by rfl) ⟨1188320, by rfl⟩ : syracuseStep 6337709 = 2376641) B2376641
theorem B6337763 : Blo 1877140 6337763 := bstep (se 1 (by rfl) ⟨4753322, by rfl⟩ : syracuseStep 6337763 = 9506645) B9506645
theorem B5346577 : Blo 1877140 5346577 := bstep (se 2 (by rfl) ⟨2004966, by rfl⟩ : syracuseStep 5346577 = 4009933) B4009933
theorem B10696049 : Blo 1877140 10696049 := bstep (se 2 (by rfl) ⟨4011018, by rfl⟩ : syracuseStep 10696049 = 8022037) B8022037
theorem B4224401 : Blo 1877140 4224401 := bstep (se 2 (by rfl) ⟨1584150, by rfl⟩ : syracuseStep 4224401 = 3168301) B3168301
theorem B4224419 : Blo 1877140 4224419 := bstep (se 1 (by rfl) ⟨3168314, by rfl⟩ : syracuseStep 4224419 = 6336629) B6336629
theorem B7132643 : Blo 1877140 7132643 := bstep (se 1 (by rfl) ⟨5349482, by rfl⟩ : syracuseStep 7132643 = 10698965) B10698965
theorem B6338033 : Blo 1877140 6338033 := bstep (se 2 (by rfl) ⟨2376762, by rfl⟩ : syracuseStep 6338033 = 4753525) B4753525
theorem B7132657 : Blo 1877140 7132657 := bstep (se 2 (by rfl) ⟨2674746, by rfl⟩ : syracuseStep 7132657 = 5349493) B5349493
theorem B14259725 : Blo 1877140 14259725 := bstep (se 3 (by rfl) ⟨2673698, by rfl⟩ : syracuseStep 14259725 = 5347397) B5347397
theorem B3167761 : Blo 1877140 3167761 := bstep (se 2 (by rfl) ⟨1187910, by rfl⟩ : syracuseStep 3167761 = 2375821) B2375821
theorem B3167795 : Blo 1877140 3167795 := bstep (se 1 (by rfl) ⟨2375846, by rfl⟩ : syracuseStep 3167795 = 4751693) B4751693
theorem B12203597 : Blo 1877140 12203597 := bstep (se 3 (by rfl) ⟨2288174, by rfl⟩ : syracuseStep 12203597 = 4576349) B4576349
theorem B4224689 : Blo 1877140 4224689 := bstep (se 2 (by rfl) ⟨1584258, by rfl⟩ : syracuseStep 4224689 = 3168517) B3168517
theorem B3167923 : Blo 1877140 3167923 := bstep (se 1 (by rfl) ⟨2375942, by rfl⟩ : syracuseStep 3167923 = 4751885) B4751885
theorem B4224707 : Blo 1877140 4224707 := bstep (se 1 (by rfl) ⟨3168530, by rfl⟩ : syracuseStep 4224707 = 6337061) B6337061
theorem B2815715 : Blo 1877140 2815715 := bstep (se 1 (by rfl) ⟨2111786, by rfl⟩ : syracuseStep 2815715 = 4223573) B4223573
theorem B2815745 : Blo 1877140 2815745 := bstep (se 2 (by rfl) ⟨1055904, by rfl⟩ : syracuseStep 2815745 = 2111809) B2111809
theorem B4282129 : Blo 1877140 4282129 := bstep (se 2 (by rfl) ⟨1605798, by rfl⟩ : syracuseStep 4282129 = 3211597) B3211597
theorem B2815763 : Blo 1877140 2815763 := bstep (se 1 (by rfl) ⟨2111822, by rfl⟩ : syracuseStep 2815763 = 4223645) B4223645
theorem B2815793 : Blo 1877140 2815793 := bstep (se 2 (by rfl) ⟨1055922, by rfl⟩ : syracuseStep 2815793 = 2111845) B2111845
theorem B3168065 : Blo 1877140 3168065 := bstep (se 2 (by rfl) ⟨1188024, by rfl⟩ : syracuseStep 3168065 = 2376049) B2376049
theorem B2815811 : Blo 1877140 2815811 := bstep (se 1 (by rfl) ⟨2111858, by rfl⟩ : syracuseStep 2815811 = 4223717) B4223717
theorem B2815841 : Blo 1877140 2815841 := bstep (se 2 (by rfl) ⟨1055940, by rfl⟩ : syracuseStep 2815841 = 2111881) B2111881
theorem B2815859 : Blo 1877140 2815859 := bstep (se 1 (by rfl) ⟨2111894, by rfl⟩ : syracuseStep 2815859 = 4223789) B4223789
theorem B2815889 : Blo 1877140 2815889 := bstep (se 2 (by rfl) ⟨1055958, by rfl⟩ : syracuseStep 2815889 = 2111917) B2111917
theorem B2537363 : Blo 1877140 2537363 := bstep (se 1 (by rfl) ⟨1903022, by rfl⟩ : syracuseStep 2537363 = 3806045) B3806045
theorem B2815907 : Blo 1877140 2815907 := bstep (se 1 (by rfl) ⟨2111930, by rfl⟩ : syracuseStep 2815907 = 4223861) B4223861
theorem B2856883 : Blo 1877140 2856883 := bstep (se 1 (by rfl) ⟨2142662, by rfl⟩ : syracuseStep 2856883 = 4285325) B4285325
theorem B2815937 : Blo 1877140 2815937 := bstep (se 2 (by rfl) ⟨1055976, by rfl⟩ : syracuseStep 2815937 = 2111953) B2111953
theorem B3168193 : Blo 1877140 3168193 := bstep (se 2 (by rfl) ⟨1188072, by rfl⟩ : syracuseStep 3168193 = 2376145) B2376145
theorem B4224977 : Blo 1877140 4224977 := bstep (se 2 (by rfl) ⟨1584366, by rfl⟩ : syracuseStep 4224977 = 3168733) B3168733
theorem B2815955 : Blo 1877140 2815955 := bstep (se 1 (by rfl) ⟨2111966, by rfl⟩ : syracuseStep 2815955 = 4223933) B4223933
theorem B3168227 : Blo 1877140 3168227 := bstep (se 1 (by rfl) ⟨2376170, by rfl⟩ : syracuseStep 3168227 = 4752341) B4752341
theorem B4224995 : Blo 1877140 4224995 := bstep (se 1 (by rfl) ⟨3168746, by rfl⟩ : syracuseStep 4224995 = 6337493) B6337493
theorem B2815985 : Blo 1877140 2815985 := bstep (se 2 (by rfl) ⟨1055994, by rfl⟩ : syracuseStep 2815985 = 2111989) B2111989
theorem B2816003 : Blo 1877140 2816003 := bstep (se 1 (by rfl) ⟨2112002, by rfl⟩ : syracuseStep 2816003 = 4224005) B4224005
theorem B6338573 : Blo 1877140 6338573 := bstep (se 3 (by rfl) ⟨1188482, by rfl⟩ : syracuseStep 6338573 = 2376965) B2376965
theorem B2816033 : Blo 1877140 2816033 := bstep (se 2 (by rfl) ⟨1056012, by rfl⟩ : syracuseStep 2816033 = 2112025) B2112025
theorem B9508913 : Blo 1877140 9508913 := bstep (se 2 (by rfl) ⟨3565842, by rfl⟩ : syracuseStep 9508913 = 7131685) B7131685
theorem B2816051 : Blo 1877140 2816051 := bstep (se 1 (by rfl) ⟨2112038, by rfl⟩ : syracuseStep 2816051 = 4224077) B4224077
theorem B6338627 : Blo 1877140 6338627 := bstep (se 1 (by rfl) ⟨4753970, by rfl⟩ : syracuseStep 6338627 = 9507941) B9507941
theorem B2816081 : Blo 1877140 2816081 := bstep (se 2 (by rfl) ⟨1056030, by rfl⟩ : syracuseStep 2816081 = 2112061) B2112061
theorem B2816099 : Blo 1877140 2816099 := bstep (se 1 (by rfl) ⟨2112074, by rfl⟩ : syracuseStep 2816099 = 4224149) B4224149
theorem B3168355 : Blo 1877140 3168355 := bstep (se 1 (by rfl) ⟨2376266, by rfl⟩ : syracuseStep 3168355 = 4752533) B4752533
theorem B2816129 : Blo 1877140 2816129 := bstep (se 2 (by rfl) ⟨1056048, by rfl⟩ : syracuseStep 2816129 = 2112097) B2112097
theorem B2816147 : Blo 1877140 2816147 := bstep (se 1 (by rfl) ⟨2112110, by rfl⟩ : syracuseStep 2816147 = 4224221) B4224221
theorem B2816177 : Blo 1877140 2816177 := bstep (se 2 (by rfl) ⟨1056066, by rfl⟩ : syracuseStep 2816177 = 2112133) B2112133
theorem B2816195 : Blo 1877140 2816195 := bstep (se 1 (by rfl) ⟨2112146, by rfl⟩ : syracuseStep 2816195 = 4224293) B4224293
theorem B2816225 : Blo 1877140 2816225 := bstep (se 2 (by rfl) ⟨1056084, by rfl⟩ : syracuseStep 2816225 = 2112169) B2112169
theorem B3168497 : Blo 1877140 3168497 := bstep (se 2 (by rfl) ⟨1188186, by rfl⟩ : syracuseStep 3168497 = 2376373) B2376373
theorem B4225265 : Blo 1877140 4225265 := bstep (se 2 (by rfl) ⟨1584474, by rfl⟩ : syracuseStep 4225265 = 3168949) B3168949
theorem B2816243 : Blo 1877140 2816243 := bstep (se 1 (by rfl) ⟨2112182, by rfl⟩ : syracuseStep 2816243 = 4224365) B4224365
theorem B4225283 : Blo 1877140 4225283 := bstep (se 1 (by rfl) ⟨3168962, by rfl⟩ : syracuseStep 4225283 = 6337925) B6337925
theorem B4012291 : Blo 1877140 4012291 := bstep (se 1 (by rfl) ⟨3009218, by rfl⟩ : syracuseStep 4012291 = 6018437) B6018437
theorem B2816273 : Blo 1877140 2816273 := bstep (se 2 (by rfl) ⟨1056102, by rfl⟩ : syracuseStep 2816273 = 2112205) B2112205
theorem B2816291 : Blo 1877140 2816291 := bstep (se 1 (by rfl) ⟨2112218, by rfl⟩ : syracuseStep 2816291 = 4224437) B4224437
theorem B2005283 : Blo 1877140 2005283 := bstep (se 1 (by rfl) ⟨1503962, by rfl⟩ : syracuseStep 2005283 = 3007925) B3007925
theorem B3299633 : Blo 1877140 3299633 := bstep (se 2 (by rfl) ⟨1237362, by rfl⟩ : syracuseStep 3299633 = 2474725) B2474725
theorem B2816321 : Blo 1877140 2816321 := bstep (se 2 (by rfl) ⟨1056120, by rfl⟩ : syracuseStep 2816321 = 2112241) B2112241
theorem B6338897 : Blo 1877140 6338897 := bstep (se 2 (by rfl) ⟨2377086, by rfl⟩ : syracuseStep 6338897 = 4754173) B4754173
theorem B2111827 : Blo 1877140 2111827 := bstep (se 1 (by rfl) ⟨1583870, by rfl⟩ : syracuseStep 2111827 = 3167741) B3167741
theorem B2816339 : Blo 1877140 2816339 := bstep (se 1 (by rfl) ⟨2112254, by rfl⟩ : syracuseStep 2816339 = 4224509) B4224509
theorem B2816369 : Blo 1877140 2816369 := bstep (se 2 (by rfl) ⟨1056138, by rfl⟩ : syracuseStep 2816369 = 2112277) B2112277
theorem B3168625 : Blo 1877140 3168625 := bstep (se 2 (by rfl) ⟨1188234, by rfl⟩ : syracuseStep 3168625 = 2376469) B2376469
theorem B2816387 : Blo 1877140 2816387 := bstep (se 1 (by rfl) ⟨2112290, by rfl⟩ : syracuseStep 2816387 = 4224581) B4224581
theorem B3168659 : Blo 1877140 3168659 := bstep (se 1 (by rfl) ⟨2376494, by rfl⟩ : syracuseStep 3168659 = 4752989) B4752989
theorem B2816417 : Blo 1877140 2816417 := bstep (se 2 (by rfl) ⟨1056156, by rfl⟩ : syracuseStep 2816417 = 2112313) B2112313
theorem B2816435 : Blo 1877140 2816435 := bstep (se 1 (by rfl) ⟨2112326, by rfl⟩ : syracuseStep 2816435 = 4224653) B4224653
theorem B2816465 : Blo 1877140 2816465 := bstep (se 2 (by rfl) ⟨1056174, by rfl⟩ : syracuseStep 2816465 = 2112349) B2112349
theorem B2111971 : Blo 1877140 2111971 := bstep (se 1 (by rfl) ⟨1583978, by rfl⟩ : syracuseStep 2111971 = 3167957) B3167957
theorem B2816483 : Blo 1877140 2816483 := bstep (se 1 (by rfl) ⟨2112362, by rfl⟩ : syracuseStep 2816483 = 4224725) B4224725
theorem B18053617 : Blo 1877140 18053617 := bstep (se 2 (by rfl) ⟨6770106, by rfl⟩ : syracuseStep 18053617 = 13540213) B13540213
theorem B2816513 : Blo 1877140 2816513 := bstep (se 2 (by rfl) ⟨1056192, by rfl⟩ : syracuseStep 2816513 = 2112385) B2112385
theorem B5347853 : Blo 1877140 5347853 := bstep (se 3 (by rfl) ⟨1002722, by rfl⟩ : syracuseStep 5347853 = 2005445) B2005445
theorem B4225553 : Blo 1877140 4225553 := bstep (se 2 (by rfl) ⟨1584582, by rfl⟩ : syracuseStep 4225553 = 3169165) B3169165
theorem B2816531 : Blo 1877140 2816531 := bstep (se 1 (by rfl) ⟨2112398, by rfl⟩ : syracuseStep 2816531 = 4224797) B4224797
theorem B3168787 : Blo 1877140 3168787 := bstep (se 1 (by rfl) ⟨2376590, by rfl⟩ : syracuseStep 3168787 = 4753181) B4753181
theorem B4225571 : Blo 1877140 4225571 := bstep (se 1 (by rfl) ⟨3169178, by rfl⟩ : syracuseStep 4225571 = 6338357) B6338357
theorem B2816561 : Blo 1877140 2816561 := bstep (se 2 (by rfl) ⟨1056210, by rfl⟩ : syracuseStep 2816561 = 2112421) B2112421
theorem B2816579 : Blo 1877140 2816579 := bstep (se 1 (by rfl) ⟨2112434, by rfl⟩ : syracuseStep 2816579 = 4224869) B4224869
theorem B5421649 : Blo 1877140 5421649 := bstep (se 2 (by rfl) ⟨2033118, by rfl⟩ : syracuseStep 5421649 = 4066237) B4066237
theorem B2538067 : Blo 1877140 2538067 := bstep (se 1 (by rfl) ⟨1903550, by rfl⟩ : syracuseStep 2538067 = 3807101) B3807101
theorem B2816609 : Blo 1877140 2816609 := bstep (se 2 (by rfl) ⟨1056228, by rfl⟩ : syracuseStep 2816609 = 2112457) B2112457
theorem B10844771 : Blo 1877140 10844771 := bstep (se 1 (by rfl) ⟨8133578, by rfl⟩ : syracuseStep 10844771 = 16267157) B16267157
theorem B2112115 : Blo 1877140 2112115 := bstep (se 1 (by rfl) ⟨1584086, by rfl⟩ : syracuseStep 2112115 = 3168173) B3168173
theorem B2816627 : Blo 1877140 2816627 := bstep (se 1 (by rfl) ⟨2112470, by rfl⟩ : syracuseStep 2816627 = 4224941) B4224941
theorem B2816657 : Blo 1877140 2816657 := bstep (se 2 (by rfl) ⟨1056246, by rfl⟩ : syracuseStep 2816657 = 2112493) B2112493
theorem B3168929 : Blo 1877140 3168929 := bstep (se 2 (by rfl) ⟨1188348, by rfl⟩ : syracuseStep 3168929 = 2376697) B2376697
theorem B2816675 : Blo 1877140 2816675 := bstep (se 1 (by rfl) ⟨2112506, by rfl⟩ : syracuseStep 2816675 = 4225013) B4225013
theorem B21396149 : Blo 1877140 21396149 := bstep (se 5 (by rfl) ⟨1002944, by rfl⟩ : syracuseStep 21396149 = 2005889) B2005889
theorem B2816705 : Blo 1877140 2816705 := bstep (se 2 (by rfl) ⟨1056264, by rfl⟩ : syracuseStep 2816705 = 2112529) B2112529
theorem B5348035 : Blo 1877140 5348035 := bstep (se 1 (by rfl) ⟨4011026, by rfl⟩ : syracuseStep 5348035 = 8022053) B8022053
theorem B4012753 : Blo 1877140 4012753 := bstep (se 2 (by rfl) ⟨1504782, by rfl⟩ : syracuseStep 4012753 = 3009565) B3009565
theorem B2816723 : Blo 1877140 2816723 := bstep (se 1 (by rfl) ⟨2112542, by rfl⟩ : syracuseStep 2816723 = 4225085) B4225085
theorem B2816753 : Blo 1877140 2816753 := bstep (se 2 (by rfl) ⟨1056282, by rfl⟩ : syracuseStep 2816753 = 2112565) B2112565
theorem B13023985 : Blo 1877140 13023985 := bstep (se 2 (by rfl) ⟨4883994, by rfl⟩ : syracuseStep 13023985 = 9767989) B9767989
theorem B5348081 : Blo 1877140 5348081 := bstep (se 2 (by rfl) ⟨2005530, by rfl⟩ : syracuseStep 5348081 = 4011061) B4011061
theorem B2112259 : Blo 1877140 2112259 := bstep (se 1 (by rfl) ⟨1584194, by rfl⟩ : syracuseStep 2112259 = 3168389) B3168389
theorem B2816771 : Blo 1877140 2816771 := bstep (se 1 (by rfl) ⟨2112578, by rfl⟩ : syracuseStep 2816771 = 4225157) B4225157
theorem B10156805 : Blo 1877140 10156805 := bstep (se 4 (by rfl) ⟨952200, by rfl⟩ : syracuseStep 10156805 = 1904401) B1904401
theorem B2816801 : Blo 1877140 2816801 := bstep (se 2 (by rfl) ⟨1056300, by rfl⟩ : syracuseStep 2816801 = 2112601) B2112601
theorem B3169057 : Blo 1877140 3169057 := bstep (se 2 (by rfl) ⟨1188396, by rfl⟩ : syracuseStep 3169057 = 2376793) B2376793
theorem B10697507 : Blo 1877140 10697507 := bstep (se 1 (by rfl) ⟨8023130, by rfl⟩ : syracuseStep 10697507 = 16046261) B16046261
theorem B4225841 : Blo 1877140 4225841 := bstep (se 2 (by rfl) ⟨1584690, by rfl⟩ : syracuseStep 4225841 = 3169381) B3169381
theorem B2816819 : Blo 1877140 2816819 := bstep (se 1 (by rfl) ⟨2112614, by rfl⟩ : syracuseStep 2816819 = 4225229) B4225229
theorem B3169091 : Blo 1877140 3169091 := bstep (se 1 (by rfl) ⟨2376818, by rfl⟩ : syracuseStep 3169091 = 4753637) B4753637
theorem B4225859 : Blo 1877140 4225859 := bstep (se 1 (by rfl) ⟨3169394, by rfl⟩ : syracuseStep 4225859 = 6338789) B6338789
theorem B2816849 : Blo 1877140 2816849 := bstep (se 2 (by rfl) ⟨1056318, by rfl⟩ : syracuseStep 2816849 = 2112637) B2112637
theorem B2816867 : Blo 1877140 2816867 := bstep (se 1 (by rfl) ⟨2112650, by rfl⟩ : syracuseStep 2816867 = 4225301) B4225301
theorem B6339437 : Blo 1877140 6339437 := bstep (se 3 (by rfl) ⟨1188644, by rfl⟩ : syracuseStep 6339437 = 2377289) B2377289
theorem B2816897 : Blo 1877140 2816897 := bstep (se 2 (by rfl) ⟨1056336, by rfl⟩ : syracuseStep 2816897 = 2112673) B2112673
theorem B30464909 : Blo 1877140 30464909 := bstep (se 3 (by rfl) ⟨5712170, by rfl⟩ : syracuseStep 30464909 = 11424341) B11424341
theorem B2112403 : Blo 1877140 2112403 := bstep (se 1 (by rfl) ⟨1584302, by rfl⟩ : syracuseStep 2112403 = 3168605) B3168605
theorem B2816915 : Blo 1877140 2816915 := bstep (se 1 (by rfl) ⟨2112686, by rfl⟩ : syracuseStep 2816915 = 4225373) B4225373
theorem B6339491 : Blo 1877140 6339491 := bstep (se 1 (by rfl) ⟨4754618, by rfl⟩ : syracuseStep 6339491 = 9509237) B9509237
theorem B7134115 : Blo 1877140 7134115 := bstep (se 1 (by rfl) ⟨5350586, by rfl⟩ : syracuseStep 7134115 = 10701173) B10701173
theorem B2816945 : Blo 1877140 2816945 := bstep (se 2 (by rfl) ⟨1056354, by rfl⟩ : syracuseStep 2816945 = 2112709) B2112709
theorem B2816963 : Blo 1877140 2816963 := bstep (se 1 (by rfl) ⟨2112722, by rfl⟩ : syracuseStep 2816963 = 4225445) B4225445
theorem B3169219 : Blo 1877140 3169219 := bstep (se 1 (by rfl) ⟨2376914, by rfl⟩ : syracuseStep 3169219 = 4753829) B4753829
theorem B2816993 : Blo 1877140 2816993 := bstep (se 2 (by rfl) ⟨1056372, by rfl⟩ : syracuseStep 2816993 = 2112745) B2112745
theorem B16268273 : Blo 1877140 16268273 := bstep (se 2 (by rfl) ⟨6100602, by rfl⟩ : syracuseStep 16268273 = 12201205) B12201205
theorem B2817011 : Blo 1877140 2817011 := bstep (se 1 (by rfl) ⟨2112758, by rfl⟩ : syracuseStep 2817011 = 4225517) B4225517
theorem B2817041 : Blo 1877140 2817041 := bstep (se 2 (by rfl) ⟨1056390, by rfl⟩ : syracuseStep 2817041 = 2112781) B2112781
theorem B2112547 : Blo 1877140 2112547 := bstep (se 1 (by rfl) ⟨1584410, by rfl⟩ : syracuseStep 2112547 = 3168821) B3168821
theorem B2817059 : Blo 1877140 2817059 := bstep (se 1 (by rfl) ⟨2112794, by rfl⟩ : syracuseStep 2817059 = 4225589) B4225589
theorem B2817089 : Blo 1877140 2817089 := bstep (se 2 (by rfl) ⟨1056408, by rfl⟩ : syracuseStep 2817089 = 2112817) B2112817
theorem B3169361 : Blo 1877140 3169361 := bstep (se 2 (by rfl) ⟨1188510, by rfl⟩ : syracuseStep 3169361 = 2377021) B2377021
theorem B4226129 : Blo 1877140 4226129 := bstep (se 2 (by rfl) ⟨1584798, by rfl⟩ : syracuseStep 4226129 = 3169597) B3169597
theorem B2817107 : Blo 1877140 2817107 := bstep (se 1 (by rfl) ⟨2112830, by rfl⟩ : syracuseStep 2817107 = 4225661) B4225661
theorem B4226147 : Blo 1877140 4226147 := bstep (se 1 (by rfl) ⟨3169610, by rfl⟩ : syracuseStep 4226147 = 6339221) B6339221
theorem B2817137 : Blo 1877140 2817137 := bstep (se 2 (by rfl) ⟨1056426, by rfl⟩ : syracuseStep 2817137 = 2112853) B2112853
theorem B2817155 : Blo 1877140 2817155 := bstep (se 1 (by rfl) ⟨2112866, by rfl⟩ : syracuseStep 2817155 = 4225733) B4225733
theorem B2817185 : Blo 1877140 2817185 := bstep (se 2 (by rfl) ⟨1056444, by rfl⟩ : syracuseStep 2817185 = 2112889) B2112889
theorem B6339761 : Blo 1877140 6339761 := bstep (se 2 (by rfl) ⟨2377410, by rfl⟩ : syracuseStep 6339761 = 4754821) B4754821
theorem B2112691 : Blo 1877140 2112691 := bstep (se 1 (by rfl) ⟨1584518, by rfl⟩ : syracuseStep 2112691 = 3169037) B3169037
theorem B2817203 : Blo 1877140 2817203 := bstep (se 1 (by rfl) ⟨2112902, by rfl⟩ : syracuseStep 2817203 = 4225805) B4225805
theorem B2817233 : Blo 1877140 2817233 := bstep (se 2 (by rfl) ⟨1056462, by rfl⟩ : syracuseStep 2817233 = 2112925) B2112925
theorem B3169489 : Blo 1877140 3169489 := bstep (se 2 (by rfl) ⟨1188558, by rfl⟩ : syracuseStep 3169489 = 2377117) B2377117
theorem B2817251 : Blo 1877140 2817251 := bstep (se 1 (by rfl) ⟨2112938, by rfl⟩ : syracuseStep 2817251 = 4225877) B4225877
theorem B3169523 : Blo 1877140 3169523 := bstep (se 1 (by rfl) ⟨2377142, by rfl⟩ : syracuseStep 3169523 = 4754285) B4754285
theorem B2817281 : Blo 1877140 2817281 := bstep (se 2 (by rfl) ⟨1056480, by rfl⟩ : syracuseStep 2817281 = 2112961) B2112961
theorem B2817299 : Blo 1877140 2817299 := bstep (se 1 (by rfl) ⟨2112974, by rfl⟩ : syracuseStep 2817299 = 4225949) B4225949
theorem B5078317 : Blo 1877140 5078317 := bstep (se 3 (by rfl) ⟨952184, by rfl⟩ : syracuseStep 5078317 = 1904369) B1904369
theorem B2817329 : Blo 1877140 2817329 := bstep (se 2 (by rfl) ⟨1056498, by rfl⟩ : syracuseStep 2817329 = 2112997) B2112997
theorem B2112835 : Blo 1877140 2112835 := bstep (se 1 (by rfl) ⟨1584626, by rfl⟩ : syracuseStep 2112835 = 3169253) B3169253
theorem B2817347 : Blo 1877140 2817347 := bstep (se 1 (by rfl) ⟨2113010, by rfl⟩ : syracuseStep 2817347 = 4226021) B4226021
theorem B10288453 : Blo 1877140 10288453 := bstep (se 4 (by rfl) ⟨964542, by rfl⟩ : syracuseStep 10288453 = 1929085) B1929085
theorem B24075589 : Blo 1877140 24075589 := bstep (se 4 (by rfl) ⟨2257086, by rfl⟩ : syracuseStep 24075589 = 4514173) B4514173
theorem B11582797 : Blo 1877140 11582797 := bstep (se 3 (by rfl) ⟨2171774, by rfl⟩ : syracuseStep 11582797 = 4343549) B4343549
theorem B2817377 : Blo 1877140 2817377 := bstep (se 2 (by rfl) ⟨1056516, by rfl⟩ : syracuseStep 2817377 = 2113033) B2113033
theorem B5078381 : Blo 1877140 5078381 := bstep (se 3 (by rfl) ⟨952196, by rfl⟩ : syracuseStep 5078381 = 1904393) B1904393
theorem B4226417 : Blo 1877140 4226417 := bstep (se 2 (by rfl) ⟨1584906, by rfl⟩ : syracuseStep 4226417 = 3169813) B3169813
theorem B2817395 : Blo 1877140 2817395 := bstep (se 1 (by rfl) ⟨2113046, by rfl⟩ : syracuseStep 2817395 = 4226093) B4226093
theorem B3169651 : Blo 1877140 3169651 := bstep (se 1 (by rfl) ⟨2377238, by rfl⟩ : syracuseStep 3169651 = 4754477) B4754477
theorem B4226435 : Blo 1877140 4226435 := bstep (se 1 (by rfl) ⟨3169826, by rfl⟩ : syracuseStep 4226435 = 6339653) B6339653
theorem B2817425 : Blo 1877140 2817425 := bstep (se 2 (by rfl) ⟨1056534, by rfl⟩ : syracuseStep 2817425 = 2113069) B2113069
theorem B3808657 : Blo 1877140 3808657 := bstep (se 2 (by rfl) ⟨1428246, by rfl⟩ : syracuseStep 3808657 = 2856493) B2856493
theorem B2006419 : Blo 1877140 2006419 := bstep (se 1 (by rfl) ⟨1504814, by rfl⟩ : syracuseStep 2006419 = 3009629) B3009629
theorem B2817443 : Blo 1877140 2817443 := bstep (se 1 (by rfl) ⟨2113082, by rfl⟩ : syracuseStep 2817443 = 4226165) B4226165
theorem B2817473 : Blo 1877140 2817473 := bstep (se 2 (by rfl) ⟨1056552, by rfl⟩ : syracuseStep 2817473 = 2113105) B2113105
theorem B2112979 : Blo 1877140 2112979 := bstep (se 1 (by rfl) ⟨1584734, by rfl⟩ : syracuseStep 2112979 = 3169469) B3169469
theorem B2817491 : Blo 1877140 2817491 := bstep (se 1 (by rfl) ⟨2113118, by rfl⟩ : syracuseStep 2817491 = 4226237) B4226237
theorem B9510371 : Blo 1877140 9510371 := bstep (se 1 (by rfl) ⟨7132778, by rfl⟩ : syracuseStep 9510371 = 14265557) B14265557
theorem B2817521 : Blo 1877140 2817521 := bstep (se 2 (by rfl) ⟨1056570, by rfl⟩ : syracuseStep 2817521 = 2113141) B2113141
theorem B3169793 : Blo 1877140 3169793 := bstep (se 2 (by rfl) ⟨1188672, by rfl⟩ : syracuseStep 3169793 = 2377345) B2377345
theorem B2817539 : Blo 1877140 2817539 := bstep (se 1 (by rfl) ⟨2113154, by rfl⟩ : syracuseStep 2817539 = 4226309) B4226309
theorem B2817569 : Blo 1877140 2817569 := bstep (se 2 (by rfl) ⟨1056588, by rfl⟩ : syracuseStep 2817569 = 2113177) B2113177
theorem B2817587 : Blo 1877140 2817587 := bstep (se 1 (by rfl) ⟨2113190, by rfl⟩ : syracuseStep 2817587 = 4226381) B4226381
theorem B17129029 : Blo 1877140 17129029 := bstep (se 4 (by rfl) ⟨1605846, by rfl⟩ : syracuseStep 17129029 = 3211693) B3211693
theorem B2817617 : Blo 1877140 2817617 := bstep (se 2 (by rfl) ⟨1056606, by rfl⟩ : syracuseStep 2817617 = 2113213) B2113213
theorem B2113123 : Blo 1877140 2113123 := bstep (se 1 (by rfl) ⟨1584842, by rfl⟩ : syracuseStep 2113123 = 3169685) B3169685
theorem B2817635 : Blo 1877140 2817635 := bstep (se 1 (by rfl) ⟨2113226, by rfl⟩ : syracuseStep 2817635 = 4226453) B4226453
theorem B2817665 : Blo 1877140 2817665 := bstep (se 2 (by rfl) ⟨1056624, by rfl⟩ : syracuseStep 2817665 = 2113249) B2113249
theorem B3169921 : Blo 1877140 3169921 := bstep (se 2 (by rfl) ⟨1188720, by rfl⟩ : syracuseStep 3169921 = 2377441) B2377441
theorem B4226705 : Blo 1877140 4226705 := bstep (se 2 (by rfl) ⟨1585014, by rfl⟩ : syracuseStep 4226705 = 3170029) B3170029
theorem B2817683 : Blo 1877140 2817683 := bstep (se 1 (by rfl) ⟨2113262, by rfl⟩ : syracuseStep 2817683 = 4226525) B4226525
theorem B3169955 : Blo 1877140 3169955 := bstep (se 1 (by rfl) ⟨2377466, by rfl⟩ : syracuseStep 3169955 = 4754933) B4754933
theorem B4226723 : Blo 1877140 4226723 := bstep (se 1 (by rfl) ⟨3170042, by rfl⟩ : syracuseStep 4226723 = 6340085) B6340085
theorem B2817713 : Blo 1877140 2817713 := bstep (se 2 (by rfl) ⟨1056642, by rfl⟩ : syracuseStep 2817713 = 2113285) B2113285
theorem B2817731 : Blo 1877140 2817731 := bstep (se 1 (by rfl) ⟨2113298, by rfl⟩ : syracuseStep 2817731 = 4226597) B4226597
theorem B8019661 : Blo 1877140 8019661 := bstep (se 3 (by rfl) ⟨1503686, by rfl⟩ : syracuseStep 8019661 = 3007373) B3007373
theorem B6340301 : Blo 1877140 6340301 := bstep (se 3 (by rfl) ⟨1188806, by rfl⟩ : syracuseStep 6340301 = 2377613) B2377613
theorem B3382993 : Blo 1877140 3382993 := bstep (se 2 (by rfl) ⟨1268622, by rfl⟩ : syracuseStep 3382993 = 2537245) B2537245
theorem B2817761 : Blo 1877140 2817761 := bstep (se 2 (by rfl) ⟨1056660, by rfl⟩ : syracuseStep 2817761 = 2113321) B2113321
theorem B3301091 : Blo 1877140 3301091 := bstep (se 1 (by rfl) ⟨2475818, by rfl⟩ : syracuseStep 3301091 = 4951637) B4951637
theorem B2113267 : Blo 1877140 2113267 := bstep (se 1 (by rfl) ⟨1584950, by rfl⟩ : syracuseStep 2113267 = 3169901) B3169901
theorem B2817779 : Blo 1877140 2817779 := bstep (se 1 (by rfl) ⟨2113334, by rfl⟩ : syracuseStep 2817779 = 4226669) B4226669
theorem B6340355 : Blo 1877140 6340355 := bstep (se 1 (by rfl) ⟨4755266, by rfl⟩ : syracuseStep 6340355 = 9510533) B9510533
theorem B2817809 : Blo 1877140 2817809 := bstep (se 2 (by rfl) ⟨1056678, by rfl⟩ : syracuseStep 2817809 = 2113357) B2113357
theorem B2817827 : Blo 1877140 2817827 := bstep (se 1 (by rfl) ⟨2113370, by rfl⟩ : syracuseStep 2817827 = 4226741) B4226741
theorem B3170083 : Blo 1877140 3170083 := bstep (se 1 (by rfl) ⟨2377562, by rfl⟩ : syracuseStep 3170083 = 4755125) B4755125
theorem B2817857 : Blo 1877140 2817857 := bstep (se 2 (by rfl) ⟨1056696, by rfl⟩ : syracuseStep 2817857 = 2113393) B2113393
theorem B2817875 : Blo 1877140 2817875 := bstep (se 1 (by rfl) ⟨2113406, by rfl⟩ : syracuseStep 2817875 = 4226813) B4226813
theorem B2817905 : Blo 1877140 2817905 := bstep (se 2 (by rfl) ⟨1056714, by rfl⟩ : syracuseStep 2817905 = 2113429) B2113429
theorem B2113411 : Blo 1877140 2113411 := bstep (se 1 (by rfl) ⟨1585058, by rfl⟩ : syracuseStep 2113411 = 3170117) B3170117
theorem B2817923 : Blo 1877140 2817923 := bstep (se 1 (by rfl) ⟨2113442, by rfl⟩ : syracuseStep 2817923 = 4226885) B4226885
theorem B2817953 : Blo 1877140 2817953 := bstep (se 2 (by rfl) ⟨1056732, by rfl⟩ : syracuseStep 2817953 = 2113465) B2113465
theorem B3170225 : Blo 1877140 3170225 := bstep (se 2 (by rfl) ⟨1188834, by rfl⟩ : syracuseStep 3170225 = 2377669) B2377669
theorem B4226993 : Blo 1877140 4226993 := bstep (se 2 (by rfl) ⟨1585122, by rfl⟩ : syracuseStep 4226993 = 3170245) B3170245
theorem B2817971 : Blo 1877140 2817971 := bstep (se 1 (by rfl) ⟨2113478, by rfl⟩ : syracuseStep 2817971 = 4226957) B4226957
theorem B4227011 : Blo 1877140 4227011 := bstep (se 1 (by rfl) ⟨3170258, by rfl⟩ : syracuseStep 4227011 = 6340517) B6340517
theorem B2818001 : Blo 1877140 2818001 := bstep (se 2 (by rfl) ⟨1056750, by rfl⟩ : syracuseStep 2818001 = 2113501) B2113501
theorem B2818019 : Blo 1877140 2818019 := bstep (se 1 (by rfl) ⟨2113514, by rfl⟩ : syracuseStep 2818019 = 4227029) B4227029
theorem B4227083 : Blo 1877140 4227083 := bstep (se 1 (by rfl) ⟨3170312, by rfl⟩ : syracuseStep 4227083 = 6340625) B6340625
theorem B2818073 : Blo 1877140 2818073 := bstep (se 2 (by rfl) ⟨1056777, by rfl⟩ : syracuseStep 2818073 = 2113555) B2113555
theorem B2113591 : Blo 1877140 2113591 := bstep (se 1 (by rfl) ⟨1585193, by rfl⟩ : syracuseStep 2113591 = 3170387) B3170387
theorem B4227137 : Blo 1877140 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B2539607 : Blo 1877140 2539607 := bstep (se 1 (by rfl) ⟨1904705, by rfl⟩ : syracuseStep 2539607 = 3809411) B3809411
theorem B2818187 : Blo 1877140 2818187 := bstep (se 1 (by rfl) ⟨2113640, by rfl⟩ : syracuseStep 2818187 = 4227281) B4227281
theorem B7618705 : Blo 1877140 7618705 := bstep (se 2 (by rfl) ⟨2857014, by rfl⟩ : syracuseStep 7618705 = 5714029) B5714029
theorem B3563671 : Blo 1877140 3563671 := bstep (se 1 (by rfl) ⟨2672753, by rfl⟩ : syracuseStep 3563671 = 5345507) B5345507
theorem B2375831 : Blo 1877140 2375831 := bstep (se 1 (by rfl) ⟨1781873, by rfl⟩ : syracuseStep 2375831 = 3563747) B3563747
theorem B4513943 : Blo 1877140 4513943 := bstep (se 1 (by rfl) ⟨3385457, by rfl⟩ : syracuseStep 4513943 = 6770915) B6770915
theorem B2818199 : Blo 1877140 2818199 := bstep (se 1 (by rfl) ⟨2113649, by rfl⟩ : syracuseStep 2818199 = 4227299) B4227299
theorem B6340787 : Blo 1877140 6340787 := bstep (se 1 (by rfl) ⟨4755590, by rfl⟩ : syracuseStep 6340787 = 9511181) B9511181
theorem B2818265 : Blo 1877140 2818265 := bstep (se 2 (by rfl) ⟨1056849, by rfl⟩ : syracuseStep 2818265 = 2113699) B2113699
theorem B2113771 : Blo 1877140 2113771 := bstep (se 1 (by rfl) ⟨1585328, by rfl⟩ : syracuseStep 2113771 = 3170657) B3170657
theorem B3563777 : Blo 1877140 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B4227353 : Blo 1877140 4227353 := bstep (se 2 (by rfl) ⟨1585257, by rfl⟩ : syracuseStep 4227353 = 3170515) B3170515
theorem B2818379 : Blo 1877140 2818379 := bstep (se 1 (by rfl) ⟨2113784, by rfl⟩ : syracuseStep 2818379 = 4227569) B4227569
theorem B2818391 : Blo 1877140 2818391 := bstep (se 1 (by rfl) ⟨2113793, by rfl⟩ : syracuseStep 2818391 = 4227587) B4227587
theorem B5349721 : Blo 1877140 5349721 := bstep (se 2 (by rfl) ⟨2006145, by rfl⟩ : syracuseStep 5349721 = 4012291) B4012291
theorem B2113879 : Blo 1877140 2113879 := bstep (se 1 (by rfl) ⟨1585409, by rfl⟩ : syracuseStep 2113879 = 3170819) B3170819
theorem B4227443 : Blo 1877140 4227443 := bstep (se 1 (by rfl) ⟨3170582, by rfl⟩ : syracuseStep 4227443 = 6341165) B6341165
theorem B10690967 : Blo 1877140 10690967 := bstep (se 1 (by rfl) ⟨8018225, by rfl⟩ : syracuseStep 10690967 = 16036451) B16036451
theorem B4227479 : Blo 1877140 4227479 := bstep (se 1 (by rfl) ⟨3170609, by rfl⟩ : syracuseStep 4227479 = 6341219) B6341219
theorem B3563929 : Blo 1877140 3563929 := bstep (se 2 (by rfl) ⟨1336473, by rfl⟩ : syracuseStep 3563929 = 2672947) B2672947
theorem B3170711 : Blo 1877140 3170711 := bstep (se 1 (by rfl) ⟨2378033, by rfl⟩ : syracuseStep 3170711 = 4756067) B4756067
theorem B2818457 : Blo 1877140 2818457 := bstep (se 2 (by rfl) ⟨1056921, by rfl⟩ : syracuseStep 2818457 = 2113843) B2113843
theorem B8020397 : Blo 1877140 8020397 := bstep (se 3 (by rfl) ⟨1503824, by rfl⟩ : syracuseStep 8020397 = 3007649) B3007649
theorem B6341057 : Blo 1877140 6341057 := bstep (se 2 (by rfl) ⟨2377896, by rfl⟩ : syracuseStep 6341057 = 4755793) B4755793
theorem B4514251 : Blo 1877140 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B2818571 : Blo 1877140 2818571 := bstep (se 1 (by rfl) ⟨2113928, by rfl⟩ : syracuseStep 2818571 = 4227857) B4227857
theorem B3170839 : Blo 1877140 3170839 := bstep (se 1 (by rfl) ⟨2378129, by rfl⟩ : syracuseStep 3170839 = 4756259) B4756259
theorem B2818583 : Blo 1877140 2818583 := bstep (se 1 (by rfl) ⟨2113937, by rfl⟩ : syracuseStep 2818583 = 4227875) B4227875
theorem B4227659 : Blo 1877140 4227659 := bstep (se 1 (by rfl) ⟨3170744, by rfl⟩ : syracuseStep 4227659 = 6341489) B6341489
theorem B2818649 : Blo 1877140 2818649 := bstep (se 2 (by rfl) ⟨1056993, by rfl⟩ : syracuseStep 2818649 = 2113987) B2113987
theorem B4227713 : Blo 1877140 4227713 := bstep (se 2 (by rfl) ⟨1585392, by rfl⟩ : syracuseStep 4227713 = 3170785) B3170785
theorem B14254865 : Blo 1877140 14254865 := bstep (se 2 (by rfl) ⟨5345574, by rfl⟩ : syracuseStep 14254865 = 10691149) B10691149
theorem B3384089 : Blo 1877140 3384089 := bstep (se 2 (by rfl) ⟨1269033, by rfl⟩ : syracuseStep 3384089 = 2538067) B2538067
theorem B25699117 : Blo 1877140 25699117 := bstep (se 3 (by rfl) ⟨4818584, by rfl⟩ : syracuseStep 25699117 = 9637169) B9637169
theorem B4752179 : Blo 1877140 4752179 := bstep (se 1 (by rfl) ⟨3564134, by rfl⟩ : syracuseStep 4752179 = 7128269) B7128269
theorem B2376535 : Blo 1877140 2376535 := bstep (se 1 (by rfl) ⟨1782401, by rfl⟩ : syracuseStep 2376535 = 3564803) B3564803
theorem B4227929 : Blo 1877140 4227929 := bstep (se 2 (by rfl) ⟨1585473, by rfl⟩ : syracuseStep 4227929 = 3170947) B3170947
theorem B4228019 : Blo 1877140 4228019 := bstep (se 1 (by rfl) ⟨3171014, by rfl⟩ : syracuseStep 4228019 = 6342029) B6342029
theorem B5350337 : Blo 1877140 5350337 := bstep (se 2 (by rfl) ⟨2006376, by rfl⟩ : syracuseStep 5350337 = 4012753) B4012753
theorem B13542349 : Blo 1877140 13542349 := bstep (se 3 (by rfl) ⟨2539190, by rfl⟩ : syracuseStep 13542349 = 5078381) B5078381
theorem B4228055 : Blo 1877140 4228055 := bstep (se 1 (by rfl) ⟨3171041, by rfl⟩ : syracuseStep 4228055 = 6342083) B6342083
theorem B6341597 : Blo 1877140 6341597 := bstep (se 3 (by rfl) ⟨1189049, by rfl⟩ : syracuseStep 6341597 = 2378099) B2378099
theorem B2475019 : Blo 1877140 2475019 := bstep (se 1 (by rfl) ⟨1856264, by rfl⟩ : syracuseStep 2475019 = 3712529) B3712529
theorem B8135731 : Blo 1877140 8135731 := bstep (se 1 (by rfl) ⟨6101798, by rfl⟩ : syracuseStep 8135731 = 12203597) B12203597
theorem B1877143 : Blo 1877140 1877143 := bstep (se 1 (by rfl) ⟨1407857, by rfl⟩ : syracuseStep 1877143 = 2815715) B2815715
theorem B1877163 : Blo 1877140 1877163 := bstep (se 1 (by rfl) ⟨1407872, by rfl⟩ : syracuseStep 1877163 = 2815745) B2815745
theorem B1877175 : Blo 1877140 1877175 := bstep (se 1 (by rfl) ⟨1407881, by rfl⟩ : syracuseStep 1877175 = 2815763) B2815763
theorem B1877195 : Blo 1877140 1877195 := bstep (se 1 (by rfl) ⟨1407896, by rfl⟩ : syracuseStep 1877195 = 2815793) B2815793
theorem B1877207 : Blo 1877140 1877207 := bstep (se 1 (by rfl) ⟨1407905, by rfl⟩ : syracuseStep 1877207 = 2815811) B2815811
theorem B9512153 : Blo 1877140 9512153 := bstep (se 2 (by rfl) ⟨3567057, by rfl⟩ : syracuseStep 9512153 = 7134115) B7134115
theorem B1877227 : Blo 1877140 1877227 := bstep (se 1 (by rfl) ⟨1407920, by rfl⟩ : syracuseStep 1877227 = 2815841) B2815841
theorem B1877239 : Blo 1877140 1877239 := bstep (se 1 (by rfl) ⟨1407929, by rfl⟩ : syracuseStep 1877239 = 2815859) B2815859
theorem B1877259 : Blo 1877140 1877259 := bstep (se 1 (by rfl) ⟨1407944, by rfl⟩ : syracuseStep 1877259 = 2815889) B2815889
theorem B1877271 : Blo 1877140 1877271 := bstep (se 1 (by rfl) ⟨1407953, by rfl⟩ : syracuseStep 1877271 = 2815907) B2815907
theorem B1877291 : Blo 1877140 1877291 := bstep (se 1 (by rfl) ⟨1407968, by rfl⟩ : syracuseStep 1877291 = 2815937) B2815937
theorem B21677357 : Blo 1877140 21677357 := bstep (se 3 (by rfl) ⟨4064504, by rfl⟩ : syracuseStep 21677357 = 8129009) B8129009
theorem B1877303 : Blo 1877140 1877303 := bstep (se 1 (by rfl) ⟨1407977, by rfl⟩ : syracuseStep 1877303 = 2815955) B2815955
theorem B1877323 : Blo 1877140 1877323 := bstep (se 1 (by rfl) ⟨1407992, by rfl⟩ : syracuseStep 1877323 = 2815985) B2815985
theorem B4752715 : Blo 1877140 4752715 := bstep (se 1 (by rfl) ⟨3564536, by rfl⟩ : syracuseStep 4752715 = 7129073) B7129073
theorem B1877335 : Blo 1877140 1877335 := bstep (se 1 (by rfl) ⟨1408001, by rfl⟩ : syracuseStep 1877335 = 2816003) B2816003
theorem B5711197 : Blo 1877140 5711197 := bstep (se 3 (by rfl) ⟨1070849, by rfl⟩ : syracuseStep 5711197 = 2141699) B2141699
theorem B1877355 : Blo 1877140 1877355 := bstep (se 1 (by rfl) ⟨1408016, by rfl⟩ : syracuseStep 1877355 = 2816033) B2816033
theorem B1877367 : Blo 1877140 1877367 := bstep (se 1 (by rfl) ⟨1408025, by rfl⟩ : syracuseStep 1877367 = 2816051) B2816051
theorem B1877387 : Blo 1877140 1877387 := bstep (se 1 (by rfl) ⟨1408040, by rfl⟩ : syracuseStep 1877387 = 2816081) B2816081
theorem B1877399 : Blo 1877140 1877399 := bstep (se 1 (by rfl) ⟨1408049, by rfl⟩ : syracuseStep 1877399 = 2816099) B2816099
theorem B1877419 : Blo 1877140 1877419 := bstep (se 1 (by rfl) ⟨1408064, by rfl⟩ : syracuseStep 1877419 = 2816129) B2816129
theorem B6014387 : Blo 1877140 6014387 := bstep (se 1 (by rfl) ⟨4510790, by rfl⟩ : syracuseStep 6014387 = 9021581) B9021581
theorem B1877431 : Blo 1877140 1877431 := bstep (se 1 (by rfl) ⟨1408073, by rfl⟩ : syracuseStep 1877431 = 2816147) B2816147
theorem B1877451 : Blo 1877140 1877451 := bstep (se 1 (by rfl) ⟨1408088, by rfl⟩ : syracuseStep 1877451 = 2816177) B2816177
theorem B1877463 : Blo 1877140 1877463 := bstep (se 1 (by rfl) ⟨1408097, by rfl⟩ : syracuseStep 1877463 = 2816195) B2816195
theorem B4752857 : Blo 1877140 4752857 := bstep (se 2 (by rfl) ⟨1782321, by rfl⟩ : syracuseStep 4752857 = 3564643) B3564643
theorem B1877483 : Blo 1877140 1877483 := bstep (se 1 (by rfl) ⟨1408112, by rfl⟩ : syracuseStep 1877483 = 2816225) B2816225
theorem B1877495 : Blo 1877140 1877495 := bstep (se 1 (by rfl) ⟨1408121, by rfl⟩ : syracuseStep 1877495 = 2816243) B2816243
theorem B1877515 : Blo 1877140 1877515 := bstep (se 1 (by rfl) ⟨1408136, by rfl⟩ : syracuseStep 1877515 = 2816273) B2816273
theorem B1877527 : Blo 1877140 1877527 := bstep (se 1 (by rfl) ⟨1408145, by rfl⟩ : syracuseStep 1877527 = 2816291) B2816291
theorem B24725027 : Blo 1877140 24725027 := bstep (se 1 (by rfl) ⟨18543770, by rfl⟩ : syracuseStep 24725027 = 37087541) B37087541
theorem B1877547 : Blo 1877140 1877547 := bstep (se 1 (by rfl) ⟨1408160, by rfl⟩ : syracuseStep 1877547 = 2816321) B2816321
theorem B1877559 : Blo 1877140 1877559 := bstep (se 1 (by rfl) ⟨1408169, by rfl⟩ : syracuseStep 1877559 = 2816339) B2816339
theorem B1877579 : Blo 1877140 1877579 := bstep (se 1 (by rfl) ⟨1408184, by rfl⟩ : syracuseStep 1877579 = 2816369) B2816369
theorem B1877591 : Blo 1877140 1877591 := bstep (se 1 (by rfl) ⟨1408193, by rfl⟩ : syracuseStep 1877591 = 2816387) B2816387
theorem B8570461 : Blo 1877140 8570461 := bstep (se 3 (by rfl) ⟨1606961, by rfl⟩ : syracuseStep 8570461 = 3213923) B3213923
theorem B1877611 : Blo 1877140 1877611 := bstep (se 1 (by rfl) ⟨1408208, by rfl⟩ : syracuseStep 1877611 = 2816417) B2816417
theorem B1877623 : Blo 1877140 1877623 := bstep (se 1 (by rfl) ⟨1408217, by rfl⟩ : syracuseStep 1877623 = 2816435) B2816435
theorem B1877643 : Blo 1877140 1877643 := bstep (se 1 (by rfl) ⟨1408232, by rfl⟩ : syracuseStep 1877643 = 2816465) B2816465
theorem B3212939 : Blo 1877140 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B1877655 : Blo 1877140 1877655 := bstep (se 1 (by rfl) ⟨1408241, by rfl⟩ : syracuseStep 1877655 = 2816483) B2816483
theorem B1877675 : Blo 1877140 1877675 := bstep (se 1 (by rfl) ⟨1408256, by rfl⟩ : syracuseStep 1877675 = 2816513) B2816513
theorem B7128755 : Blo 1877140 7128755 := bstep (se 1 (by rfl) ⟨5346566, by rfl⟩ : syracuseStep 7128755 = 10693133) B10693133
theorem B3565235 : Blo 1877140 3565235 := bstep (se 1 (by rfl) ⟨2673926, by rfl⟩ : syracuseStep 3565235 = 5347853) B5347853
theorem B1877687 : Blo 1877140 1877687 := bstep (se 1 (by rfl) ⟨1408265, by rfl⟩ : syracuseStep 1877687 = 2816531) B2816531
theorem B7128769 : Blo 1877140 7128769 := bstep (se 2 (by rfl) ⟨2673288, by rfl⟩ : syracuseStep 7128769 = 5346577) B5346577
theorem B1877707 : Blo 1877140 1877707 := bstep (se 1 (by rfl) ⟨1408280, by rfl⟩ : syracuseStep 1877707 = 2816561) B2816561
theorem B1877719 : Blo 1877140 1877719 := bstep (se 1 (by rfl) ⟨1408289, by rfl⟩ : syracuseStep 1877719 = 2816579) B2816579
theorem B1877739 : Blo 1877140 1877739 := bstep (se 1 (by rfl) ⟨1408304, by rfl⟩ : syracuseStep 1877739 = 2816609) B2816609
theorem B1877751 : Blo 1877140 1877751 := bstep (se 1 (by rfl) ⟨1408313, by rfl⟩ : syracuseStep 1877751 = 2816627) B2816627
theorem B18056965 : Blo 1877140 18056965 := bstep (se 4 (by rfl) ⟨1692840, by rfl⟩ : syracuseStep 18056965 = 3385681) B3385681
theorem B1877771 : Blo 1877140 1877771 := bstep (se 1 (by rfl) ⟨1408328, by rfl⟩ : syracuseStep 1877771 = 2816657) B2816657
theorem B15443729 : Blo 1877140 15443729 := bstep (se 2 (by rfl) ⟨5791398, by rfl⟩ : syracuseStep 15443729 = 11582797) B11582797
theorem B1877783 : Blo 1877140 1877783 := bstep (se 1 (by rfl) ⟨1408337, by rfl⟩ : syracuseStep 1877783 = 2816675) B2816675
theorem B14264099 : Blo 1877140 14264099 := bstep (se 1 (by rfl) ⟨10698074, by rfl⟩ : syracuseStep 14264099 = 21396149) B21396149
theorem B1877803 : Blo 1877140 1877803 := bstep (se 1 (by rfl) ⟨1408352, by rfl⟩ : syracuseStep 1877803 = 2816705) B2816705
theorem B1877815 : Blo 1877140 1877815 := bstep (se 1 (by rfl) ⟨1408361, by rfl⟩ : syracuseStep 1877815 = 2816723) B2816723
theorem B1877835 : Blo 1877140 1877835 := bstep (se 1 (by rfl) ⟨1408376, by rfl⟩ : syracuseStep 1877835 = 2816753) B2816753
theorem B3565387 : Blo 1877140 3565387 := bstep (se 1 (by rfl) ⟨2674040, by rfl⟩ : syracuseStep 3565387 = 5348081) B5348081
theorem B1877847 : Blo 1877140 1877847 := bstep (se 1 (by rfl) ⟨1408385, by rfl⟩ : syracuseStep 1877847 = 2816771) B2816771
theorem B1877867 : Blo 1877140 1877867 := bstep (se 1 (by rfl) ⟨1408400, by rfl⟩ : syracuseStep 1877867 = 2816801) B2816801
theorem B1877879 : Blo 1877140 1877879 := bstep (se 1 (by rfl) ⟨1408409, by rfl⟩ : syracuseStep 1877879 = 2816819) B2816819
theorem B1877899 : Blo 1877140 1877899 := bstep (se 1 (by rfl) ⟨1408424, by rfl⟩ : syracuseStep 1877899 = 2816849) B2816849
theorem B1877911 : Blo 1877140 1877911 := bstep (se 1 (by rfl) ⟨1408433, by rfl⟩ : syracuseStep 1877911 = 2816867) B2816867
theorem B1877931 : Blo 1877140 1877931 := bstep (se 1 (by rfl) ⟨1408448, by rfl⟩ : syracuseStep 1877931 = 2816897) B2816897
theorem B20309939 : Blo 1877140 20309939 := bstep (se 1 (by rfl) ⟨15232454, by rfl⟩ : syracuseStep 20309939 = 30464909) B30464909
theorem B1877943 : Blo 1877140 1877943 := bstep (se 1 (by rfl) ⟨1408457, by rfl⟩ : syracuseStep 1877943 = 2816915) B2816915
theorem B1877963 : Blo 1877140 1877963 := bstep (se 1 (by rfl) ⟨1408472, by rfl⟩ : syracuseStep 1877963 = 2816945) B2816945
theorem B1877975 : Blo 1877140 1877975 := bstep (se 1 (by rfl) ⟨1408481, by rfl⟩ : syracuseStep 1877975 = 2816963) B2816963
theorem B1877995 : Blo 1877140 1877995 := bstep (se 1 (by rfl) ⟨1408496, by rfl⟩ : syracuseStep 1877995 = 2816993) B2816993
theorem B1878007 : Blo 1877140 1878007 := bstep (se 1 (by rfl) ⟨1408505, by rfl⟩ : syracuseStep 1878007 = 2817011) B2817011
theorem B1878027 : Blo 1877140 1878027 := bstep (se 1 (by rfl) ⟨1408520, by rfl⟩ : syracuseStep 1878027 = 2817041) B2817041
theorem B1878039 : Blo 1877140 1878039 := bstep (se 1 (by rfl) ⟨1408529, by rfl⟩ : syracuseStep 1878039 = 2817059) B2817059
theorem B1878059 : Blo 1877140 1878059 := bstep (se 1 (by rfl) ⟨1408544, by rfl⟩ : syracuseStep 1878059 = 2817089) B2817089
theorem B1878071 : Blo 1877140 1878071 := bstep (se 1 (by rfl) ⟨1408553, by rfl⟩ : syracuseStep 1878071 = 2817107) B2817107
theorem B1878091 : Blo 1877140 1878091 := bstep (se 1 (by rfl) ⟨1408568, by rfl⟩ : syracuseStep 1878091 = 2817137) B2817137
theorem B1878103 : Blo 1877140 1878103 := bstep (se 1 (by rfl) ⟨1408577, by rfl⟩ : syracuseStep 1878103 = 2817155) B2817155
theorem B1878123 : Blo 1877140 1878123 := bstep (se 1 (by rfl) ⟨1408592, by rfl⟩ : syracuseStep 1878123 = 2817185) B2817185
theorem B1878135 : Blo 1877140 1878135 := bstep (se 1 (by rfl) ⟨1408601, by rfl⟩ : syracuseStep 1878135 = 2817203) B2817203
theorem B1878155 : Blo 1877140 1878155 := bstep (se 1 (by rfl) ⟨1408616, by rfl⟩ : syracuseStep 1878155 = 2817233) B2817233
theorem B1878167 : Blo 1877140 1878167 := bstep (se 1 (by rfl) ⟨1408625, by rfl⟩ : syracuseStep 1878167 = 2817251) B2817251
theorem B3565721 : Blo 1877140 3565721 := bstep (se 2 (by rfl) ⟨1337145, by rfl⟩ : syracuseStep 3565721 = 2674291) B2674291
theorem B1878187 : Blo 1877140 1878187 := bstep (se 1 (by rfl) ⟨1408640, by rfl⟩ : syracuseStep 1878187 = 2817281) B2817281
theorem B1878199 : Blo 1877140 1878199 := bstep (se 1 (by rfl) ⟨1408649, by rfl⟩ : syracuseStep 1878199 = 2817299) B2817299
theorem B1878219 : Blo 1877140 1878219 := bstep (se 1 (by rfl) ⟨1408664, by rfl⟩ : syracuseStep 1878219 = 2817329) B2817329
theorem B1878231 : Blo 1877140 1878231 := bstep (se 1 (by rfl) ⟨1408673, by rfl⟩ : syracuseStep 1878231 = 2817347) B2817347
theorem B1878251 : Blo 1877140 1878251 := bstep (se 1 (by rfl) ⟨1408688, by rfl⟩ : syracuseStep 1878251 = 2817377) B2817377
theorem B1878263 : Blo 1877140 1878263 := bstep (se 1 (by rfl) ⟨1408697, by rfl⟩ : syracuseStep 1878263 = 2817395) B2817395
theorem B1878283 : Blo 1877140 1878283 := bstep (se 1 (by rfl) ⟨1408712, by rfl⟩ : syracuseStep 1878283 = 2817425) B2817425
theorem B10692881 : Blo 1877140 10692881 := bstep (se 2 (by rfl) ⟨4009830, by rfl⟩ : syracuseStep 10692881 = 8019661) B8019661
theorem B4753687 : Blo 1877140 4753687 := bstep (se 1 (by rfl) ⟨3565265, by rfl⟩ : syracuseStep 4753687 = 7130531) B7130531
theorem B1878295 : Blo 1877140 1878295 := bstep (se 1 (by rfl) ⟨1408721, by rfl⟩ : syracuseStep 1878295 = 2817443) B2817443
theorem B1878315 : Blo 1877140 1878315 := bstep (se 1 (by rfl) ⟨1408736, by rfl⟩ : syracuseStep 1878315 = 2817473) B2817473
theorem B1878327 : Blo 1877140 1878327 := bstep (se 1 (by rfl) ⟨1408745, by rfl⟩ : syracuseStep 1878327 = 2817491) B2817491
theorem B1878347 : Blo 1877140 1878347 := bstep (se 1 (by rfl) ⟨1408760, by rfl⟩ : syracuseStep 1878347 = 2817521) B2817521
theorem B1878359 : Blo 1877140 1878359 := bstep (se 1 (by rfl) ⟨1408769, by rfl⟩ : syracuseStep 1878359 = 2817539) B2817539
theorem B8022361 : Blo 1877140 8022361 := bstep (se 2 (by rfl) ⟨3008385, by rfl⟩ : syracuseStep 8022361 = 6016771) B6016771
theorem B5146973 : Blo 1877140 5146973 := bstep (se 3 (by rfl) ⟨965057, by rfl⟩ : syracuseStep 5146973 = 1930115) B1930115
theorem B1878379 : Blo 1877140 1878379 := bstep (se 1 (by rfl) ⟨1408784, by rfl⟩ : syracuseStep 1878379 = 2817569) B2817569
theorem B1878391 : Blo 1877140 1878391 := bstep (se 1 (by rfl) ⟨1408793, by rfl⟩ : syracuseStep 1878391 = 2817587) B2817587
theorem B1878411 : Blo 1877140 1878411 := bstep (se 1 (by rfl) ⟨1408808, by rfl⟩ : syracuseStep 1878411 = 2817617) B2817617
theorem B1878423 : Blo 1877140 1878423 := bstep (se 1 (by rfl) ⟨1408817, by rfl⟩ : syracuseStep 1878423 = 2817635) B2817635
theorem B1878443 : Blo 1877140 1878443 := bstep (se 1 (by rfl) ⟨1408832, by rfl⟩ : syracuseStep 1878443 = 2817665) B2817665
theorem B1878455 : Blo 1877140 1878455 := bstep (se 1 (by rfl) ⟨1408841, by rfl⟩ : syracuseStep 1878455 = 2817683) B2817683
theorem B6769099 : Blo 1877140 6769099 := bstep (se 1 (by rfl) ⟨5076824, by rfl⟩ : syracuseStep 6769099 = 10153649) B10153649
theorem B1878475 : Blo 1877140 1878475 := bstep (se 1 (by rfl) ⟨1408856, by rfl⟩ : syracuseStep 1878475 = 2817713) B2817713
theorem B1878487 : Blo 1877140 1878487 := bstep (se 1 (by rfl) ⟨1408865, by rfl⟩ : syracuseStep 1878487 = 2817731) B2817731
theorem B1878507 : Blo 1877140 1878507 := bstep (se 1 (by rfl) ⟨1408880, by rfl⟩ : syracuseStep 1878507 = 2817761) B2817761
theorem B1878519 : Blo 1877140 1878519 := bstep (se 1 (by rfl) ⟨1408889, by rfl⟩ : syracuseStep 1878519 = 2817779) B2817779
theorem B1878539 : Blo 1877140 1878539 := bstep (se 1 (by rfl) ⟨1408904, by rfl⟩ : syracuseStep 1878539 = 2817809) B2817809
theorem B2378251 : Blo 1877140 2378251 := bstep (se 1 (by rfl) ⟨1783688, by rfl⟩ : syracuseStep 2378251 = 3567377) B3567377
theorem B2673175 : Blo 1877140 2673175 := bstep (se 1 (by rfl) ⟨2004881, by rfl⟩ : syracuseStep 2673175 = 4009763) B4009763
theorem B1878551 : Blo 1877140 1878551 := bstep (se 1 (by rfl) ⟨1408913, by rfl⟩ : syracuseStep 1878551 = 2817827) B2817827
theorem B1878571 : Blo 1877140 1878571 := bstep (se 1 (by rfl) ⟨1408928, by rfl⟩ : syracuseStep 1878571 = 2817857) B2817857
theorem B1878583 : Blo 1877140 1878583 := bstep (se 1 (by rfl) ⟨1408937, by rfl⟩ : syracuseStep 1878583 = 2817875) B2817875
theorem B1878603 : Blo 1877140 1878603 := bstep (se 1 (by rfl) ⟨1408952, by rfl⟩ : syracuseStep 1878603 = 2817905) B2817905
theorem B1878615 : Blo 1877140 1878615 := bstep (se 1 (by rfl) ⟨1408961, by rfl⟩ : syracuseStep 1878615 = 2817923) B2817923
theorem B1878635 : Blo 1877140 1878635 := bstep (se 1 (by rfl) ⟨1408976, by rfl⟩ : syracuseStep 1878635 = 2817953) B2817953
theorem B1878647 : Blo 1877140 1878647 := bstep (se 1 (by rfl) ⟨1408985, by rfl⟩ : syracuseStep 1878647 = 2817971) B2817971
theorem B1878667 : Blo 1877140 1878667 := bstep (se 1 (by rfl) ⟨1409000, by rfl⟩ : syracuseStep 1878667 = 2818001) B2818001
theorem B3574411 : Blo 1877140 3574411 := bstep (se 1 (by rfl) ⟨2680808, by rfl⟩ : syracuseStep 3574411 = 5361617) B5361617
theorem B1878679 : Blo 1877140 1878679 := bstep (se 1 (by rfl) ⟨1409009, by rfl⟩ : syracuseStep 1878679 = 2818019) B2818019
theorem B1878699 : Blo 1877140 1878699 := bstep (se 1 (by rfl) ⟨1409024, by rfl⟩ : syracuseStep 1878699 = 2818049) B2818049
theorem B6769331 : Blo 1877140 6769331 := bstep (se 1 (by rfl) ⟨5076998, by rfl⟩ : syracuseStep 6769331 = 10153997) B10153997
theorem B1878711 : Blo 1877140 1878711 := bstep (se 1 (by rfl) ⟨1409033, by rfl⟩ : syracuseStep 1878711 = 2818067) B2818067
theorem B4754123 : Blo 1877140 4754123 := bstep (se 1 (by rfl) ⟨3565592, by rfl⟩ : syracuseStep 4754123 = 7131185) B7131185
theorem B1878731 : Blo 1877140 1878731 := bstep (se 1 (by rfl) ⟨1409048, by rfl⟩ : syracuseStep 1878731 = 2818097) B2818097
theorem B1878743 : Blo 1877140 1878743 := bstep (se 1 (by rfl) ⟨1409057, by rfl⟩ : syracuseStep 1878743 = 2818115) B2818115
theorem B1878763 : Blo 1877140 1878763 := bstep (se 1 (by rfl) ⟨1409072, by rfl⟩ : syracuseStep 1878763 = 2818145) B2818145
theorem B1878775 : Blo 1877140 1878775 := bstep (se 1 (by rfl) ⟨1409081, by rfl⟩ : syracuseStep 1878775 = 2818163) B2818163
theorem B1878795 : Blo 1877140 1878795 := bstep (se 1 (by rfl) ⟨1409096, by rfl⟩ : syracuseStep 1878795 = 2818193) B2818193
theorem B3566359 : Blo 1877140 3566359 := bstep (se 1 (by rfl) ⟨2674769, by rfl⟩ : syracuseStep 3566359 = 5349539) B5349539
theorem B1878807 : Blo 1877140 1878807 := bstep (se 1 (by rfl) ⟨1409105, by rfl⟩ : syracuseStep 1878807 = 2818211) B2818211
theorem B1878827 : Blo 1877140 1878827 := bstep (se 1 (by rfl) ⟨1409120, by rfl⟩ : syracuseStep 1878827 = 2818241) B2818241
theorem B32074541 : Blo 1877140 32074541 := bstep (se 3 (by rfl) ⟨6013976, by rfl⟩ : syracuseStep 32074541 = 12027953) B12027953
theorem B1878839 : Blo 1877140 1878839 := bstep (se 1 (by rfl) ⟨1409129, by rfl⟩ : syracuseStep 1878839 = 2818259) B2818259
theorem B1878859 : Blo 1877140 1878859 := bstep (se 1 (by rfl) ⟨1409144, by rfl⟩ : syracuseStep 1878859 = 2818289) B2818289
theorem B1878871 : Blo 1877140 1878871 := bstep (se 1 (by rfl) ⟨1409153, by rfl⟩ : syracuseStep 1878871 = 2818307) B2818307
theorem B1878891 : Blo 1877140 1878891 := bstep (se 1 (by rfl) ⟨1409168, by rfl⟩ : syracuseStep 1878891 = 2818337) B2818337
theorem B1878903 : Blo 1877140 1878903 := bstep (se 1 (by rfl) ⟨1409177, by rfl⟩ : syracuseStep 1878903 = 2818355) B2818355
theorem B1878923 : Blo 1877140 1878923 := bstep (se 1 (by rfl) ⟨1409192, by rfl⟩ : syracuseStep 1878923 = 2818385) B2818385
theorem B1878935 : Blo 1877140 1878935 := bstep (se 1 (by rfl) ⟨1409201, by rfl⟩ : syracuseStep 1878935 = 2818403) B2818403
theorem B1878955 : Blo 1877140 1878955 := bstep (se 1 (by rfl) ⟨1409216, by rfl⟩ : syracuseStep 1878955 = 2818433) B2818433
theorem B1878967 : Blo 1877140 1878967 := bstep (se 1 (by rfl) ⟨1409225, by rfl⟩ : syracuseStep 1878967 = 2818451) B2818451
theorem B1878987 : Blo 1877140 1878987 := bstep (se 1 (by rfl) ⟨1409240, by rfl⟩ : syracuseStep 1878987 = 2818481) B2818481
theorem B1878999 : Blo 1877140 1878999 := bstep (se 1 (by rfl) ⟨1409249, by rfl⟩ : syracuseStep 1878999 = 2818499) B2818499
theorem B1879019 : Blo 1877140 1879019 := bstep (se 1 (by rfl) ⟨1409264, by rfl⟩ : syracuseStep 1879019 = 2818529) B2818529
theorem B1879031 : Blo 1877140 1879031 := bstep (se 1 (by rfl) ⟨1409273, by rfl⟩ : syracuseStep 1879031 = 2818547) B2818547
theorem B1879051 : Blo 1877140 1879051 := bstep (se 1 (by rfl) ⟨1409288, by rfl⟩ : syracuseStep 1879051 = 2818577) B2818577
theorem B1879063 : Blo 1877140 1879063 := bstep (se 1 (by rfl) ⟨1409297, by rfl⟩ : syracuseStep 1879063 = 2818595) B2818595
theorem B1879083 : Blo 1877140 1879083 := bstep (se 1 (by rfl) ⟨1409312, by rfl⟩ : syracuseStep 1879083 = 2818625) B2818625
theorem B1879095 : Blo 1877140 1879095 := bstep (se 1 (by rfl) ⟨1409321, by rfl⟩ : syracuseStep 1879095 = 2818643) B2818643
theorem B4754497 : Blo 1877140 4754497 := bstep (se 2 (by rfl) ⟨1782936, by rfl⟩ : syracuseStep 4754497 = 3565873) B3565873
theorem B2673739 : Blo 1877140 2673739 := bstep (se 1 (by rfl) ⟨2005304, by rfl⟩ : syracuseStep 2673739 = 4010609) B4010609
theorem B1879115 : Blo 1877140 1879115 := bstep (se 1 (by rfl) ⟨1409336, by rfl⟩ : syracuseStep 1879115 = 2818673) B2818673
theorem B1879127 : Blo 1877140 1879127 := bstep (se 1 (by rfl) ⟨1409345, by rfl⟩ : syracuseStep 1879127 = 2818691) B2818691
theorem B8023319 : Blo 1877140 8023319 := bstep (se 1 (by rfl) ⟨6017489, by rfl⟩ : syracuseStep 8023319 = 12034979) B12034979
theorem B4009267 : Blo 1877140 4009267 := bstep (se 1 (by rfl) ⟨3006950, by rfl⟩ : syracuseStep 4009267 = 6013901) B6013901
theorem B16256321 : Blo 1877140 16256321 := bstep (se 2 (by rfl) ⟨6096120, by rfl⟩ : syracuseStep 16256321 = 12192241) B12192241
theorem B24071489 : Blo 1877140 24071489 := bstep (se 2 (by rfl) ⟨9026808, by rfl⟩ : syracuseStep 24071489 = 18053617) B18053617
theorem B6335819 : Blo 1877140 6335819 := bstep (se 1 (by rfl) ⟨4751864, by rfl⟩ : syracuseStep 6335819 = 9503729) B9503729
theorem B7228865 : Blo 1877140 7228865 := bstep (se 2 (by rfl) ⟨2710824, by rfl⟩ : syracuseStep 7228865 = 5421649) B5421649
theorem B3010007 : Blo 1877140 3010007 := bstep (se 1 (by rfl) ⟨2257505, by rfl⟩ : syracuseStep 3010007 = 4515011) B4515011
theorem B9506321 : Blo 1877140 9506321 := bstep (se 2 (by rfl) ⟨3564870, by rfl⟩ : syracuseStep 9506321 = 7129741) B7129741
theorem B7130699 : Blo 1877140 7130699 := bstep (se 1 (by rfl) ⟨5348024, by rfl⟩ : syracuseStep 7130699 = 10696049) B10696049
theorem B3567179 : Blo 1877140 3567179 := bstep (se 1 (by rfl) ⟨2675384, by rfl⟩ : syracuseStep 3567179 = 5350769) B5350769
theorem B6336089 : Blo 1877140 6336089 := bstep (se 2 (by rfl) ⟨2376033, by rfl⟩ : syracuseStep 6336089 = 4752067) B4752067
theorem B7130713 : Blo 1877140 7130713 := bstep (se 2 (by rfl) ⟨2674017, by rfl⟩ : syracuseStep 7130713 = 5348035) B5348035
theorem B3567233 : Blo 1877140 3567233 := bstep (se 2 (by rfl) ⟨1337712, by rfl⟩ : syracuseStep 3567233 = 2675425) B2675425
theorem B10153603 : Blo 1877140 10153603 := bstep (se 1 (by rfl) ⟨7615202, by rfl⟩ : syracuseStep 10153603 = 15230405) B15230405
theorem B4755095 : Blo 1877140 4755095 := bstep (se 1 (by rfl) ⟨3566321, by rfl⟩ : syracuseStep 4755095 = 7132643) B7132643
theorem B9506483 : Blo 1877140 9506483 := bstep (se 1 (by rfl) ⟨7129862, by rfl⟩ : syracuseStep 9506483 = 14259725) B14259725
theorem B16052033 : Blo 1877140 16052033 := bstep (se 2 (by rfl) ⟨6019512, by rfl⟩ : syracuseStep 16052033 = 12039025) B12039025
theorem B5345473 : Blo 1877140 5345473 := bstep (se 2 (by rfl) ⟨2004552, by rfl⟩ : syracuseStep 5345473 = 4009105) B4009105
theorem B2199755 : Blo 1877140 2199755 := bstep (se 1 (by rfl) ⟨1649816, by rfl⟩ : syracuseStep 2199755 = 3299633) B3299633
theorem B6336791 : Blo 1877140 6336791 := bstep (se 1 (by rfl) ⟨4752593, by rfl⟩ : syracuseStep 6336791 = 9505187) B9505187
theorem B6771089 : Blo 1877140 6771089 := bstep (se 2 (by rfl) ⟨2539158, by rfl⟩ : syracuseStep 6771089 = 5078317) B5078317
theorem B13717937 : Blo 1877140 13717937 := bstep (se 2 (by rfl) ⟨5144226, by rfl⟩ : syracuseStep 13717937 = 10288453) B10288453
theorem B32100785 : Blo 1877140 32100785 := bstep (se 2 (by rfl) ⟨12037794, by rfl⟩ : syracuseStep 32100785 = 24075589) B24075589
theorem B4755905 : Blo 1877140 4755905 := bstep (se 2 (by rfl) ⟨1783464, by rfl⟩ : syracuseStep 4755905 = 3566929) B3566929
theorem B6771203 : Blo 1877140 6771203 := bstep (se 1 (by rfl) ⟨5078402, by rfl⟩ : syracuseStep 6771203 = 10156805) B10156805
theorem B7131671 : Blo 1877140 7131671 := bstep (se 1 (by rfl) ⟨5348753, by rfl⟩ : syracuseStep 7131671 = 10697507) B10697507
theorem B2675225 : Blo 1877140 2675225 := bstep (se 2 (by rfl) ⟨1003209, by rfl⟩ : syracuseStep 2675225 = 2006419) B2006419
theorem B18051619 : Blo 1877140 18051619 := bstep (se 1 (by rfl) ⟨13538714, by rfl⟩ : syracuseStep 18051619 = 27077429) B27077429
theorem B14258753 : Blo 1877140 14258753 := bstep (se 2 (by rfl) ⟨5347032, by rfl⟩ : syracuseStep 14258753 = 10694065) B10694065
theorem B5075549 : Blo 1877140 5075549 := bstep (se 3 (by rfl) ⟨951665, by rfl⟩ : syracuseStep 5075549 = 1903331) B1903331
theorem B4223627 : Blo 1877140 4223627 := bstep (se 1 (by rfl) ⟨3167720, by rfl⟩ : syracuseStep 4223627 = 6335441) B6335441
theorem B5075635 : Blo 1877140 5075635 := bstep (se 1 (by rfl) ⟨3806726, by rfl⟩ : syracuseStep 5075635 = 7613453) B7613453
theorem B4223681 : Blo 1877140 4223681 := bstep (se 2 (by rfl) ⟨1583880, by rfl⟩ : syracuseStep 4223681 = 3167761) B3167761
theorem B5075677 : Blo 1877140 5075677 := bstep (se 3 (by rfl) ⟨951689, by rfl⟩ : syracuseStep 5075677 = 1903379) B1903379
theorem B4010753 : Blo 1877140 4010753 := bstep (se 2 (by rfl) ⟨1504032, by rfl⟩ : syracuseStep 4010753 = 3008065) B3008065
theorem B6337331 : Blo 1877140 6337331 := bstep (se 1 (by rfl) ⟨4752998, by rfl⟩ : syracuseStep 6337331 = 9505997) B9505997
theorem B4223897 : Blo 1877140 4223897 := bstep (se 2 (by rfl) ⟨1583961, by rfl⟩ : syracuseStep 4223897 = 3167923) B3167923
theorem B4510657 : Blo 1877140 4510657 := bstep (se 2 (by rfl) ⟨1691496, by rfl⟩ : syracuseStep 4510657 = 3382993) B3382993
theorem B4756441 : Blo 1877140 4756441 := bstep (se 2 (by rfl) ⟨1783665, by rfl⟩ : syracuseStep 4756441 = 3567331) B3567331
theorem B4223987 : Blo 1877140 4223987 := bstep (se 1 (by rfl) ⟨3167990, by rfl⟩ : syracuseStep 4223987 = 6335981) B6335981
theorem B4224023 : Blo 1877140 4224023 := bstep (se 1 (by rfl) ⟨3168017, by rfl⟩ : syracuseStep 4224023 = 6336035) B6336035
theorem B6337601 : Blo 1877140 6337601 := bstep (se 2 (by rfl) ⟨2376600, by rfl⟩ : syracuseStep 6337601 = 4753201) B4753201
theorem B4011095 : Blo 1877140 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B2200727 : Blo 1877140 2200727 := bstep (se 1 (by rfl) ⟨1650545, by rfl⟩ : syracuseStep 2200727 = 3301091) B3301091
theorem B4224203 : Blo 1877140 4224203 := bstep (se 1 (by rfl) ⟨3168152, by rfl⟩ : syracuseStep 4224203 = 6336305) B6336305
theorem B4224257 : Blo 1877140 4224257 := bstep (se 2 (by rfl) ⟨1584096, by rfl⟩ : syracuseStep 4224257 = 3168193) B3168193
theorem B4011403 : Blo 1877140 4011403 := bstep (se 1 (by rfl) ⟨3008552, by rfl⟩ : syracuseStep 4011403 = 6017105) B6017105
theorem B4224473 : Blo 1877140 4224473 := bstep (se 2 (by rfl) ⟨1584177, by rfl⟩ : syracuseStep 4224473 = 3168355) B3168355
theorem B12039641 : Blo 1877140 12039641 := bstep (se 2 (by rfl) ⟨4514865, by rfl⟩ : syracuseStep 12039641 = 9029731) B9029731
theorem B4224563 : Blo 1877140 4224563 := bstep (se 1 (by rfl) ⟨3168422, by rfl⟩ : syracuseStep 4224563 = 6336845) B6336845
theorem B9508427 : Blo 1877140 9508427 := bstep (se 1 (by rfl) ⟨7131320, by rfl⟩ : syracuseStep 9508427 = 14262641) B14262641
theorem B4224599 : Blo 1877140 4224599 := bstep (se 1 (by rfl) ⟨3168449, by rfl⟩ : syracuseStep 4224599 = 6336899) B6336899
theorem B4511321 : Blo 1877140 4511321 := bstep (se 2 (by rfl) ⟨1691745, by rfl⟩ : syracuseStep 4511321 = 3383491) B3383491
theorem B8566361 : Blo 1877140 8566361 := bstep (se 2 (by rfl) ⟨3212385, by rfl⟩ : syracuseStep 8566361 = 6424771) B6424771
theorem B6338141 : Blo 1877140 6338141 := bstep (se 3 (by rfl) ⟨1188401, by rfl⟩ : syracuseStep 6338141 = 2376803) B2376803
theorem B6100697 : Blo 1877140 6100697 := bstep (se 2 (by rfl) ⟨2287761, by rfl⟩ : syracuseStep 6100697 = 4575523) B4575523
theorem B7132931 : Blo 1877140 7132931 := bstep (se 1 (by rfl) ⟨5349698, by rfl⟩ : syracuseStep 7132931 = 10699397) B10699397
theorem B3168011 : Blo 1877140 3168011 := bstep (se 1 (by rfl) ⟨2376008, by rfl⟩ : syracuseStep 3168011 = 4752017) B4752017
theorem B4224779 : Blo 1877140 4224779 := bstep (se 1 (by rfl) ⟨3168584, by rfl⟩ : syracuseStep 4224779 = 6337169) B6337169
theorem B2815769 : Blo 1877140 2815769 := bstep (se 2 (by rfl) ⟨1055913, by rfl⟩ : syracuseStep 2815769 = 2111827) B2111827
theorem B4224833 : Blo 1877140 4224833 := bstep (se 2 (by rfl) ⟨1584312, by rfl⟩ : syracuseStep 4224833 = 3168625) B3168625
theorem B5347147 : Blo 1877140 5347147 := bstep (se 1 (by rfl) ⟨4010360, by rfl⟩ : syracuseStep 5347147 = 8020721) B8020721
theorem B36083555 : Blo 1877140 36083555 := bstep (se 1 (by rfl) ⟨27062666, by rfl⟩ : syracuseStep 36083555 = 54125333) B54125333
theorem B2815883 : Blo 1877140 2815883 := bstep (se 1 (by rfl) ⟨2111912, by rfl⟩ : syracuseStep 2815883 = 4223825) B4223825
theorem B3168139 : Blo 1877140 3168139 := bstep (se 1 (by rfl) ⟨2376104, by rfl⟩ : syracuseStep 3168139 = 4752209) B4752209
theorem B2815895 : Blo 1877140 2815895 := bstep (se 1 (by rfl) ⟨2111921, by rfl⟩ : syracuseStep 2815895 = 4223843) B4223843
theorem B2004907 : Blo 1877140 2004907 := bstep (se 1 (by rfl) ⟨1503680, by rfl⟩ : syracuseStep 2004907 = 3007361) B3007361
theorem B2815961 : Blo 1877140 2815961 := bstep (se 2 (by rfl) ⟨1055985, by rfl⟩ : syracuseStep 2815961 = 2111971) B2111971
theorem B3168281 : Blo 1877140 3168281 := bstep (se 2 (by rfl) ⟨1188105, by rfl⟩ : syracuseStep 3168281 = 2376211) B2376211
theorem B4225049 : Blo 1877140 4225049 := bstep (se 2 (by rfl) ⟨1584393, by rfl⟩ : syracuseStep 4225049 = 3168787) B3168787
theorem B2816075 : Blo 1877140 2816075 := bstep (se 1 (by rfl) ⟨2112056, by rfl⟩ : syracuseStep 2816075 = 4224113) B4224113
theorem B2816087 : Blo 1877140 2816087 := bstep (se 1 (by rfl) ⟨2112065, by rfl⟩ : syracuseStep 2816087 = 4224131) B4224131
theorem B5347421 : Blo 1877140 5347421 := bstep (se 3 (by rfl) ⟨1002641, by rfl⟩ : syracuseStep 5347421 = 2005283) B2005283
theorem B4225139 : Blo 1877140 4225139 := bstep (se 1 (by rfl) ⟨3168854, by rfl⟩ : syracuseStep 4225139 = 6337709) B6337709
theorem B4225175 : Blo 1877140 4225175 := bstep (se 1 (by rfl) ⟨3168881, by rfl⟩ : syracuseStep 4225175 = 6337763) B6337763
theorem B39082135 : Blo 1877140 39082135 := bstep (se 1 (by rfl) ⟨29311601, by rfl⟩ : syracuseStep 39082135 = 58623203) B58623203
theorem B2816153 : Blo 1877140 2816153 := bstep (se 2 (by rfl) ⟨1056057, by rfl⟩ : syracuseStep 2816153 = 2112115) B2112115
theorem B3168409 : Blo 1877140 3168409 := bstep (se 2 (by rfl) ⟨1188153, by rfl⟩ : syracuseStep 3168409 = 2376307) B2376307
theorem B3807425 : Blo 1877140 3807425 := bstep (se 2 (by rfl) ⟨1427784, by rfl⟩ : syracuseStep 3807425 = 2855569) B2855569
theorem B4012249 : Blo 1877140 4012249 := bstep (se 2 (by rfl) ⟨1504593, by rfl⟩ : syracuseStep 4012249 = 3009187) B3009187
theorem B2816267 : Blo 1877140 2816267 := bstep (se 1 (by rfl) ⟨2112200, by rfl⟩ : syracuseStep 2816267 = 4224401) B4224401
theorem B16038161 : Blo 1877140 16038161 := bstep (se 2 (by rfl) ⟨6014310, by rfl⟩ : syracuseStep 16038161 = 12028621) B12028621
theorem B2816279 : Blo 1877140 2816279 := bstep (se 1 (by rfl) ⟨2112209, by rfl⟩ : syracuseStep 2816279 = 4224419) B4224419
theorem B17365313 : Blo 1877140 17365313 := bstep (se 2 (by rfl) ⟨6511992, by rfl⟩ : syracuseStep 17365313 = 13023985) B13023985
theorem B11426113 : Blo 1877140 11426113 := bstep (se 2 (by rfl) ⟨4284792, by rfl⟩ : syracuseStep 11426113 = 8569585) B8569585
theorem B4225355 : Blo 1877140 4225355 := bstep (se 1 (by rfl) ⟨3169016, by rfl⟩ : syracuseStep 4225355 = 6338033) B6338033
theorem B2816345 : Blo 1877140 2816345 := bstep (se 2 (by rfl) ⟨1056129, by rfl⟩ : syracuseStep 2816345 = 2112259) B2112259
theorem B115677557 : Blo 1877140 115677557 := bstep (se 5 (by rfl) ⟨5422385, by rfl⟩ : syracuseStep 115677557 = 10844771) B10844771
theorem B2111863 : Blo 1877140 2111863 := bstep (se 1 (by rfl) ⟨1583897, by rfl⟩ : syracuseStep 2111863 = 3167795) B3167795
theorem B4225409 : Blo 1877140 4225409 := bstep (se 2 (by rfl) ⟨1584528, by rfl⟩ : syracuseStep 4225409 = 3169057) B3169057
theorem B2816459 : Blo 1877140 2816459 := bstep (se 1 (by rfl) ⟨2112344, by rfl⟩ : syracuseStep 2816459 = 4224689) B4224689
theorem B13720013 : Blo 1877140 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B2816471 : Blo 1877140 2816471 := bstep (se 1 (by rfl) ⟨2112353, by rfl⟩ : syracuseStep 2816471 = 4224707) B4224707
theorem B4282841 : Blo 1877140 4282841 := bstep (se 2 (by rfl) ⟨1606065, by rfl⟩ : syracuseStep 4282841 = 3212131) B3212131
theorem B14260697 : Blo 1877140 14260697 := bstep (se 2 (by rfl) ⟨5347761, by rfl⟩ : syracuseStep 14260697 = 10695523) B10695523
theorem B65067533 : Blo 1877140 65067533 := bstep (se 3 (by rfl) ⟨12200162, by rfl⟩ : syracuseStep 65067533 = 24400325) B24400325
theorem B2816537 : Blo 1877140 2816537 := bstep (se 2 (by rfl) ⟨1056201, by rfl⟩ : syracuseStep 2816537 = 2112403) B2112403
theorem B2112043 : Blo 1877140 2112043 := bstep (se 1 (by rfl) ⟨1584032, by rfl⟩ : syracuseStep 2112043 = 3168065) B3168065
theorem B4225625 : Blo 1877140 4225625 := bstep (se 2 (by rfl) ⟨1584609, by rfl⟩ : syracuseStep 4225625 = 3169219) B3169219
theorem B2816651 : Blo 1877140 2816651 := bstep (se 1 (by rfl) ⟨2112488, by rfl⟩ : syracuseStep 2816651 = 4224977) B4224977
theorem B2112151 : Blo 1877140 2112151 := bstep (se 1 (by rfl) ⟨1584113, by rfl⟩ : syracuseStep 2112151 = 3168227) B3168227
theorem B2816663 : Blo 1877140 2816663 := bstep (se 1 (by rfl) ⟨2112497, by rfl⟩ : syracuseStep 2816663 = 4224995) B4224995
theorem B4225715 : Blo 1877140 4225715 := bstep (se 1 (by rfl) ⟨3169286, by rfl⟩ : syracuseStep 4225715 = 6338573) B6338573
theorem B11426483 : Blo 1877140 11426483 := bstep (se 1 (by rfl) ⟨8569862, by rfl⟩ : syracuseStep 11426483 = 17139725) B17139725
theorem B6339275 : Blo 1877140 6339275 := bstep (se 1 (by rfl) ⟨4754456, by rfl⟩ : syracuseStep 6339275 = 9508913) B9508913
theorem B3168983 : Blo 1877140 3168983 := bstep (se 1 (by rfl) ⟨2376737, by rfl⟩ : syracuseStep 3168983 = 4753475) B4753475
theorem B4225751 : Blo 1877140 4225751 := bstep (se 1 (by rfl) ⟨3169313, by rfl⟩ : syracuseStep 4225751 = 6338627) B6338627
theorem B2816729 : Blo 1877140 2816729 := bstep (se 2 (by rfl) ⟨1056273, by rfl⟩ : syracuseStep 2816729 = 2112547) B2112547
theorem B22838021 : Blo 1877140 22838021 := bstep (se 4 (by rfl) ⟨2141064, by rfl⟩ : syracuseStep 22838021 = 4282129) B4282129
theorem B91355957 : Blo 1877140 91355957 := bstep (se 5 (by rfl) ⟨4282310, by rfl⟩ : syracuseStep 91355957 = 8564621) B8564621
theorem B2112331 : Blo 1877140 2112331 := bstep (se 1 (by rfl) ⟨1584248, by rfl⟩ : syracuseStep 2112331 = 3168497) B3168497
theorem B2816843 : Blo 1877140 2816843 := bstep (se 1 (by rfl) ⟨2112632, by rfl⟩ : syracuseStep 2816843 = 4225265) B4225265
theorem B2816855 : Blo 1877140 2816855 := bstep (se 1 (by rfl) ⟨2112641, by rfl⟩ : syracuseStep 2816855 = 4225283) B4225283
theorem B3169111 : Blo 1877140 3169111 := bstep (se 1 (by rfl) ⟨2376833, by rfl⟩ : syracuseStep 3169111 = 4753667) B4753667
theorem B4225931 : Blo 1877140 4225931 := bstep (se 1 (by rfl) ⟨3169448, by rfl⟩ : syracuseStep 4225931 = 6338897) B6338897
theorem B2816921 : Blo 1877140 2816921 := bstep (se 2 (by rfl) ⟨1056345, by rfl⟩ : syracuseStep 2816921 = 2112691) B2112691
theorem B2112439 : Blo 1877140 2112439 := bstep (se 1 (by rfl) ⟨1584329, by rfl⟩ : syracuseStep 2112439 = 3168659) B3168659
theorem B4225985 : Blo 1877140 4225985 := bstep (se 2 (by rfl) ⟨1584744, by rfl⟩ : syracuseStep 4225985 = 3169489) B3169489
theorem B2005975 : Blo 1877140 2005975 := bstep (se 1 (by rfl) ⟨1504481, by rfl⟩ : syracuseStep 2005975 = 3008963) B3008963
theorem B6339545 : Blo 1877140 6339545 := bstep (se 2 (by rfl) ⟨2377329, by rfl⟩ : syracuseStep 6339545 = 4754659) B4754659
theorem B8018909 : Blo 1877140 8018909 := bstep (se 3 (by rfl) ⟨1503545, by rfl⟩ : syracuseStep 8018909 = 3007091) B3007091
theorem B14269445 : Blo 1877140 14269445 := bstep (se 4 (by rfl) ⟨1337760, by rfl⟩ : syracuseStep 14269445 = 2675521) B2675521
theorem B2817035 : Blo 1877140 2817035 := bstep (se 1 (by rfl) ⟨2112776, by rfl⟩ : syracuseStep 2817035 = 4225553) B4225553
theorem B2817047 : Blo 1877140 2817047 := bstep (se 1 (by rfl) ⟨2112785, by rfl⟩ : syracuseStep 2817047 = 4225571) B4225571
theorem B4283443 : Blo 1877140 4283443 := bstep (se 1 (by rfl) ⟨3212582, by rfl⟩ : syracuseStep 4283443 = 6425165) B6425165
theorem B4283479 : Blo 1877140 4283479 := bstep (se 1 (by rfl) ⟨3212609, by rfl⟩ : syracuseStep 4283479 = 6425219) B6425219
theorem B2817113 : Blo 1877140 2817113 := bstep (se 2 (by rfl) ⟨1056417, by rfl⟩ : syracuseStep 2817113 = 2112835) B2112835
theorem B2112619 : Blo 1877140 2112619 := bstep (se 1 (by rfl) ⟨1584464, by rfl⟩ : syracuseStep 2112619 = 3168929) B3168929
theorem B6765713 : Blo 1877140 6765713 := bstep (se 2 (by rfl) ⟨2537142, by rfl⟩ : syracuseStep 6765713 = 5074285) B5074285
theorem B4226201 : Blo 1877140 4226201 := bstep (se 2 (by rfl) ⟨1584825, by rfl⟩ : syracuseStep 4226201 = 3169651) B3169651
theorem B5078209 : Blo 1877140 5078209 := bstep (se 2 (by rfl) ⟨1904328, by rfl⟩ : syracuseStep 5078209 = 3808657) B3808657
theorem B2817227 : Blo 1877140 2817227 := bstep (se 1 (by rfl) ⟨2112920, by rfl⟩ : syracuseStep 2817227 = 4225841) B4225841
theorem B2112727 : Blo 1877140 2112727 := bstep (se 1 (by rfl) ⟨1584545, by rfl⟩ : syracuseStep 2112727 = 3169091) B3169091
theorem B2817239 : Blo 1877140 2817239 := bstep (se 1 (by rfl) ⟨2112929, by rfl⟩ : syracuseStep 2817239 = 4225859) B4225859
theorem B4226291 : Blo 1877140 4226291 := bstep (se 1 (by rfl) ⟨3169718, by rfl⟩ : syracuseStep 4226291 = 6339437) B6339437
theorem B4226327 : Blo 1877140 4226327 := bstep (se 1 (by rfl) ⟨3169745, by rfl⟩ : syracuseStep 4226327 = 6339491) B6339491
theorem B2817305 : Blo 1877140 2817305 := bstep (se 2 (by rfl) ⟨1056489, by rfl⟩ : syracuseStep 2817305 = 2112979) B2112979
theorem B9510209 : Blo 1877140 9510209 := bstep (se 2 (by rfl) ⟨3566328, by rfl⟩ : syracuseStep 9510209 = 7132657) B7132657
theorem B10845515 : Blo 1877140 10845515 := bstep (se 1 (by rfl) ⟨8134136, by rfl⟩ : syracuseStep 10845515 = 16268273) B16268273
theorem B2112907 : Blo 1877140 2112907 := bstep (se 1 (by rfl) ⟨1584680, by rfl⟩ : syracuseStep 2112907 = 3169361) B3169361
theorem B2817419 : Blo 1877140 2817419 := bstep (se 1 (by rfl) ⟨2113064, by rfl⟩ : syracuseStep 2817419 = 4226129) B4226129
theorem B2817431 : Blo 1877140 2817431 := bstep (se 1 (by rfl) ⟨2113073, by rfl⟩ : syracuseStep 2817431 = 4226147) B4226147
theorem B22838705 : Blo 1877140 22838705 := bstep (se 2 (by rfl) ⟨8564514, by rfl⟩ : syracuseStep 22838705 = 17129029) B17129029
theorem B3169739 : Blo 1877140 3169739 := bstep (se 1 (by rfl) ⟨2377304, by rfl⟩ : syracuseStep 3169739 = 4754609) B4754609
theorem B4226507 : Blo 1877140 4226507 := bstep (se 1 (by rfl) ⟨3169880, by rfl⟩ : syracuseStep 4226507 = 6339761) B6339761
theorem B2817497 : Blo 1877140 2817497 := bstep (se 2 (by rfl) ⟨1056561, by rfl⟩ : syracuseStep 2817497 = 2113123) B2113123
theorem B2113015 : Blo 1877140 2113015 := bstep (se 1 (by rfl) ⟨1584761, by rfl⟩ : syracuseStep 2113015 = 3169523) B3169523
theorem B4226561 : Blo 1877140 4226561 := bstep (se 2 (by rfl) ⟨1584960, by rfl⟩ : syracuseStep 4226561 = 3169921) B3169921
theorem B10698257 : Blo 1877140 10698257 := bstep (se 2 (by rfl) ⟨4011846, by rfl⟩ : syracuseStep 10698257 = 8023693) B8023693
theorem B2817611 : Blo 1877140 2817611 := bstep (se 1 (by rfl) ⟨2113208, by rfl⟩ : syracuseStep 2817611 = 4226417) B4226417
theorem B3169867 : Blo 1877140 3169867 := bstep (se 1 (by rfl) ⟨2377400, by rfl⟩ : syracuseStep 3169867 = 4754801) B4754801
theorem B2817623 : Blo 1877140 2817623 := bstep (se 1 (by rfl) ⟨2113217, by rfl⟩ : syracuseStep 2817623 = 4226435) B4226435
theorem B6340247 : Blo 1877140 6340247 := bstep (se 1 (by rfl) ⟨4755185, by rfl⟩ : syracuseStep 6340247 = 9510371) B9510371
theorem B2817689 : Blo 1877140 2817689 := bstep (se 2 (by rfl) ⟨1056633, by rfl⟩ : syracuseStep 2817689 = 2113267) B2113267
theorem B2113195 : Blo 1877140 2113195 := bstep (se 1 (by rfl) ⟨1584896, by rfl⟩ : syracuseStep 2113195 = 3169793) B3169793
theorem B3170009 : Blo 1877140 3170009 := bstep (se 2 (by rfl) ⟨1188753, by rfl⟩ : syracuseStep 3170009 = 2377507) B2377507
theorem B4226777 : Blo 1877140 4226777 := bstep (se 2 (by rfl) ⟨1585041, by rfl⟩ : syracuseStep 4226777 = 3170083) B3170083
theorem B6766301 : Blo 1877140 6766301 := bstep (se 3 (by rfl) ⟨1268681, by rfl⟩ : syracuseStep 6766301 = 2537363) B2537363
theorem B2817803 : Blo 1877140 2817803 := bstep (se 1 (by rfl) ⟨2113352, by rfl⟩ : syracuseStep 2817803 = 4226705) B4226705
theorem B2113303 : Blo 1877140 2113303 := bstep (se 1 (by rfl) ⟨1584977, by rfl⟩ : syracuseStep 2113303 = 3169955) B3169955
theorem B2817815 : Blo 1877140 2817815 := bstep (se 1 (by rfl) ⟨2113361, by rfl⟩ : syracuseStep 2817815 = 4226723) B4226723
theorem B4226867 : Blo 1877140 4226867 := bstep (se 1 (by rfl) ⟨3170150, by rfl⟩ : syracuseStep 4226867 = 6340301) B6340301
theorem B4226903 : Blo 1877140 4226903 := bstep (se 1 (by rfl) ⟨3170177, by rfl⟩ : syracuseStep 4226903 = 6340355) B6340355
theorem B2817881 : Blo 1877140 2817881 := bstep (se 2 (by rfl) ⟨1056705, by rfl⟩ : syracuseStep 2817881 = 2113411) B2113411
theorem B3170137 : Blo 1877140 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B3809177 : Blo 1877140 3809177 := bstep (se 2 (by rfl) ⟨1428441, by rfl⟩ : syracuseStep 3809177 = 2856883) B2856883
theorem B2113483 : Blo 1877140 2113483 := bstep (se 1 (by rfl) ⟨1585112, by rfl⟩ : syracuseStep 2113483 = 3170225) B3170225
theorem B2817995 : Blo 1877140 2817995 := bstep (se 1 (by rfl) ⟨2113496, by rfl⟩ : syracuseStep 2817995 = 4226993) B4226993
theorem B2818007 : Blo 1877140 2818007 := bstep (se 1 (by rfl) ⟨2113505, by rfl⟩ : syracuseStep 2818007 = 4227011) B4227011
theorem B10698713 : Blo 1877140 10698713 := bstep (se 2 (by rfl) ⟨4012017, by rfl⟩ : syracuseStep 10698713 = 8024035) B8024035
theorem B2818055 : Blo 1877140 2818055 := bstep (se 1 (by rfl) ⟨2113541, by rfl⟩ : syracuseStep 2818055 = 4227083) B4227083
theorem B2818091 : Blo 1877140 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B2818121 : Blo 1877140 2818121 := bstep (se 2 (by rfl) ⟨1056795, by rfl⟩ : syracuseStep 2818121 = 2113591) B2113591
theorem B4227191 : Blo 1877140 4227191 := bstep (se 1 (by rfl) ⟨3170393, by rfl⟩ : syracuseStep 4227191 = 6340787) B6340787
theorem B2818235 : Blo 1877140 2818235 := bstep (se 1 (by rfl) ⟨2113676, by rfl⟩ : syracuseStep 2818235 = 4227353) B4227353
theorem B4751561 : Blo 1877140 4751561 := bstep (se 2 (by rfl) ⟨1781835, by rfl⟩ : syracuseStep 4751561 = 3563671) B3563671
theorem B52109513 : Blo 1877140 52109513 := bstep (se 2 (by rfl) ⟨19541067, by rfl⟩ : syracuseStep 52109513 = 39082135) B39082135
theorem B2818295 : Blo 1877140 2818295 := bstep (se 1 (by rfl) ⟨2113721, by rfl⟩ : syracuseStep 2818295 = 4227443) B4227443
theorem B7127297 : Blo 1877140 7127297 := bstep (se 2 (by rfl) ⟨2672736, by rfl⟩ : syracuseStep 7127297 = 5345473) B5345473
theorem B4514059 : Blo 1877140 4514059 := bstep (se 1 (by rfl) ⟨3385544, by rfl⟩ : syracuseStep 4514059 = 6771089) B6771089
theorem B7127311 : Blo 1877140 7127311 := bstep (se 1 (by rfl) ⟨5345483, by rfl⟩ : syracuseStep 7127311 = 10690967) B10690967
theorem B2818319 : Blo 1877140 2818319 := bstep (se 1 (by rfl) ⟨2113739, by rfl⟩ : syracuseStep 2818319 = 4227479) B4227479
theorem B2113807 : Blo 1877140 2113807 := bstep (se 1 (by rfl) ⟨1585355, by rfl⟩ : syracuseStep 2113807 = 3170711) B3170711
theorem B5349665 : Blo 1877140 5349665 := bstep (se 2 (by rfl) ⟨2006124, by rfl⟩ : syracuseStep 5349665 = 4012249) B4012249
theorem B4227371 : Blo 1877140 4227371 := bstep (se 1 (by rfl) ⟨3170528, by rfl⟩ : syracuseStep 4227371 = 6341057) B6341057
theorem B3170603 : Blo 1877140 3170603 := bstep (se 1 (by rfl) ⟨2377952, by rfl⟩ : syracuseStep 3170603 = 4755905) B4755905
theorem B2818361 : Blo 1877140 2818361 := bstep (se 2 (by rfl) ⟨1056885, by rfl⟩ : syracuseStep 2818361 = 2113771) B2113771
theorem B4514135 : Blo 1877140 4514135 := bstep (se 1 (by rfl) ⟨3385601, by rfl⟩ : syracuseStep 4514135 = 6771203) B6771203
theorem B2818439 : Blo 1877140 2818439 := bstep (se 1 (by rfl) ⟨2113829, by rfl⟩ : syracuseStep 2818439 = 4227659) B4227659
theorem B3383699 : Blo 1877140 3383699 := bstep (se 1 (by rfl) ⟨2537774, by rfl⟩ : syracuseStep 3383699 = 5075549) B5075549
theorem B2818475 : Blo 1877140 2818475 := bstep (se 1 (by rfl) ⟨2113856, by rfl⟩ : syracuseStep 2818475 = 4227713) B4227713
theorem B2818505 : Blo 1877140 2818505 := bstep (se 2 (by rfl) ⟨1056939, by rfl⟩ : syracuseStep 2818505 = 2113879) B2113879
theorem B9503243 : Blo 1877140 9503243 := bstep (se 1 (by rfl) ⟨7127432, by rfl⟩ : syracuseStep 9503243 = 14254865) B14254865
theorem B5866013 : Blo 1877140 5866013 := bstep (se 3 (by rfl) ⟨1099877, by rfl⟩ : syracuseStep 5866013 = 2199755) B2199755
theorem B4751905 : Blo 1877140 4751905 := bstep (se 2 (by rfl) ⟨1781964, by rfl⟩ : syracuseStep 4751905 = 3563929) B3563929
theorem B2818619 : Blo 1877140 2818619 := bstep (se 1 (by rfl) ⟨2113964, by rfl⟩ : syracuseStep 2818619 = 4227929) B4227929
theorem B2818679 : Blo 1877140 2818679 := bstep (se 1 (by rfl) ⟨2114009, by rfl⟩ : syracuseStep 2818679 = 4228019) B4228019
theorem B2818703 : Blo 1877140 2818703 := bstep (se 1 (by rfl) ⟨2114027, by rfl⟩ : syracuseStep 2818703 = 4228055) B4228055
theorem B4227731 : Blo 1877140 4227731 := bstep (se 1 (by rfl) ⟨3170798, by rfl⟩ : syracuseStep 4227731 = 6341597) B6341597
theorem B9503405 : Blo 1877140 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B3171001 : Blo 1877140 3171001 := bstep (se 2 (by rfl) ⟨1189125, by rfl⟩ : syracuseStep 3171001 = 2378251) B2378251
theorem B3564233 : Blo 1877140 3564233 := bstep (se 2 (by rfl) ⟨1336587, by rfl⟩ : syracuseStep 3564233 = 2673175) B2673175
theorem B4227785 : Blo 1877140 4227785 := bstep (se 2 (by rfl) ⟨1585419, by rfl⟩ : syracuseStep 4227785 = 3170839) B3170839
theorem B24068825 : Blo 1877140 24068825 := bstep (se 2 (by rfl) ⟨9025809, by rfl⟩ : syracuseStep 24068825 = 18051619) B18051619
theorem B19063525 : Blo 1877140 19063525 := bstep (se 4 (by rfl) ⟨1787205, by rfl⟩ : syracuseStep 19063525 = 3574411) B3574411
theorem B40633093 : Blo 1877140 40633093 := bstep (se 4 (by rfl) ⟨3809352, by rfl⟩ : syracuseStep 40633093 = 7618705) B7618705
theorem B6341435 : Blo 1877140 6341435 := bstep (se 1 (by rfl) ⟨4756076, by rfl⟩ : syracuseStep 6341435 = 9512153) B9512153
theorem B14451571 : Blo 1877140 14451571 := bstep (se 1 (by rfl) ⟨10838678, by rfl⟩ : syracuseStep 14451571 = 21677357) B21677357
theorem B6767513 : Blo 1877140 6767513 := bstep (se 2 (by rfl) ⟨2537817, by rfl⟩ : syracuseStep 6767513 = 5075635) B5075635
theorem B6767569 : Blo 1877140 6767569 := bstep (se 2 (by rfl) ⟨2537838, by rfl⟩ : syracuseStep 6767569 = 5075677) B5075677
theorem B16483351 : Blo 1877140 16483351 := bstep (se 1 (by rfl) ⟨12362513, by rfl⟩ : syracuseStep 16483351 = 24725027) B24725027
theorem B3007547 : Blo 1877140 3007547 := bstep (se 1 (by rfl) ⟨2255660, by rfl⟩ : syracuseStep 3007547 = 4511321) B4511321
theorem B5710907 : Blo 1877140 5710907 := bstep (se 1 (by rfl) ⟨4283180, by rfl⟩ : syracuseStep 5710907 = 8566361) B8566361
theorem B4752503 : Blo 1877140 4752503 := bstep (se 1 (by rfl) ⟨3564377, by rfl⟩ : syracuseStep 4752503 = 7128755) B7128755
theorem B1877179 : Blo 1877140 1877179 := bstep (se 1 (by rfl) ⟨1407884, by rfl⟩ : syracuseStep 1877179 = 2815769) B2815769
theorem B6014209 : Blo 1877140 6014209 := bstep (se 2 (by rfl) ⟨2255328, by rfl⟩ : syracuseStep 6014209 = 4510657) B4510657
theorem B1877255 : Blo 1877140 1877255 := bstep (se 1 (by rfl) ⟨1407941, by rfl⟩ : syracuseStep 1877255 = 2815883) B2815883
theorem B1877263 : Blo 1877140 1877263 := bstep (se 1 (by rfl) ⟨1407947, by rfl⟩ : syracuseStep 1877263 = 2815895) B2815895
theorem B18056465 : Blo 1877140 18056465 := bstep (se 2 (by rfl) ⟨6771174, by rfl⟩ : syracuseStep 18056465 = 13542349) B13542349
theorem B6341921 : Blo 1877140 6341921 := bstep (se 2 (by rfl) ⟨2378220, by rfl⟩ : syracuseStep 6341921 = 4756441) B4756441
theorem B1877307 : Blo 1877140 1877307 := bstep (se 1 (by rfl) ⟨1407980, by rfl⟩ : syracuseStep 1877307 = 2815961) B2815961
theorem B1877383 : Blo 1877140 1877383 := bstep (se 1 (by rfl) ⟨1408037, by rfl⟩ : syracuseStep 1877383 = 2816075) B2816075
theorem B1877391 : Blo 1877140 1877391 := bstep (se 1 (by rfl) ⟨1408043, by rfl⟩ : syracuseStep 1877391 = 2816087) B2816087
theorem B3564947 : Blo 1877140 3564947 := bstep (se 1 (by rfl) ⟨2673710, by rfl⟩ : syracuseStep 3564947 = 5347421) B5347421
theorem B5711257 : Blo 1877140 5711257 := bstep (se 2 (by rfl) ⟨2141721, by rfl⟩ : syracuseStep 5711257 = 4283443) B4283443
theorem B10847641 : Blo 1877140 10847641 := bstep (se 2 (by rfl) ⟨4067865, by rfl⟩ : syracuseStep 10847641 = 8135731) B8135731
theorem B3564985 : Blo 1877140 3564985 := bstep (se 2 (by rfl) ⟨1336869, by rfl⟩ : syracuseStep 3564985 = 2673739) B2673739
theorem B1877435 : Blo 1877140 1877435 := bstep (se 1 (by rfl) ⟨1408076, by rfl⟩ : syracuseStep 1877435 = 2816153) B2816153
theorem B5711305 : Blo 1877140 5711305 := bstep (se 2 (by rfl) ⟨2141739, by rfl⟩ : syracuseStep 5711305 = 4283479) B4283479
theorem B1877511 : Blo 1877140 1877511 := bstep (se 1 (by rfl) ⟨1408133, by rfl⟩ : syracuseStep 1877511 = 2816267) B2816267
theorem B10692107 : Blo 1877140 10692107 := bstep (se 1 (by rfl) ⟨8019080, by rfl⟩ : syracuseStep 10692107 = 16038161) B16038161
theorem B7128587 : Blo 1877140 7128587 := bstep (se 1 (by rfl) ⟨5346440, by rfl⟩ : syracuseStep 7128587 = 10692881) B10692881
theorem B1877519 : Blo 1877140 1877519 := bstep (se 1 (by rfl) ⟨1408139, by rfl⟩ : syracuseStep 1877519 = 2816279) B2816279
theorem B9512477 : Blo 1877140 9512477 := bstep (se 3 (by rfl) ⟨1783589, by rfl⟩ : syracuseStep 9512477 = 3567179) B3567179
theorem B1877563 : Blo 1877140 1877563 := bstep (se 1 (by rfl) ⟨1408172, by rfl⟩ : syracuseStep 1877563 = 2816345) B2816345
theorem B1877639 : Blo 1877140 1877639 := bstep (se 1 (by rfl) ⟨1408229, by rfl⟩ : syracuseStep 1877639 = 2816459) B2816459
theorem B1877647 : Blo 1877140 1877647 := bstep (se 1 (by rfl) ⟨1408235, by rfl⟩ : syracuseStep 1877647 = 2816471) B2816471
theorem B43378355 : Blo 1877140 43378355 := bstep (se 1 (by rfl) ⟨32533766, by rfl⟩ : syracuseStep 43378355 = 65067533) B65067533
theorem B1877691 : Blo 1877140 1877691 := bstep (se 1 (by rfl) ⟨1408268, by rfl⟩ : syracuseStep 1877691 = 2816537) B2816537
theorem B1877767 : Blo 1877140 1877767 := bstep (se 1 (by rfl) ⟨1408325, by rfl⟩ : syracuseStep 1877767 = 2816651) B2816651
theorem B1877775 : Blo 1877140 1877775 := bstep (se 1 (by rfl) ⟨1408331, by rfl⟩ : syracuseStep 1877775 = 2816663) B2816663
theorem B1877819 : Blo 1877140 1877819 := bstep (se 1 (by rfl) ⟨1408364, by rfl⟩ : syracuseStep 1877819 = 2816729) B2816729
theorem B21383027 : Blo 1877140 21383027 := bstep (se 1 (by rfl) ⟨16037270, by rfl⟩ : syracuseStep 21383027 = 32074541) B32074541
theorem B1877895 : Blo 1877140 1877895 := bstep (se 1 (by rfl) ⟨1408421, by rfl⟩ : syracuseStep 1877895 = 2816843) B2816843
theorem B1877903 : Blo 1877140 1877903 := bstep (se 1 (by rfl) ⟨1408427, by rfl⟩ : syracuseStep 1877903 = 2816855) B2816855
theorem B1877947 : Blo 1877140 1877947 := bstep (se 1 (by rfl) ⟨1408460, by rfl⟩ : syracuseStep 1877947 = 2816921) B2816921
theorem B9512963 : Blo 1877140 9512963 := bstep (se 1 (by rfl) ⟨7134722, by rfl⟩ : syracuseStep 9512963 = 14269445) B14269445
theorem B1878023 : Blo 1877140 1878023 := bstep (se 1 (by rfl) ⟨1408517, by rfl⟩ : syracuseStep 1878023 = 2817035) B2817035
theorem B1878031 : Blo 1877140 1878031 := bstep (se 1 (by rfl) ⟨1408523, by rfl⟩ : syracuseStep 1878031 = 2817047) B2817047
theorem B1878075 : Blo 1877140 1878075 := bstep (se 1 (by rfl) ⟨1408556, by rfl⟩ : syracuseStep 1878075 = 2817113) B2817113
theorem B1878151 : Blo 1877140 1878151 := bstep (se 1 (by rfl) ⟨1408613, by rfl⟩ : syracuseStep 1878151 = 2817227) B2817227
theorem B1878159 : Blo 1877140 1878159 := bstep (se 1 (by rfl) ⟨1408619, by rfl⟩ : syracuseStep 1878159 = 2817239) B2817239
theorem B1878203 : Blo 1877140 1878203 := bstep (se 1 (by rfl) ⟨1408652, by rfl⟩ : syracuseStep 1878203 = 2817305) B2817305
theorem B9505025 : Blo 1877140 9505025 := bstep (se 2 (by rfl) ⟨3564384, by rfl⟩ : syracuseStep 9505025 = 7128769) B7128769
theorem B1878279 : Blo 1877140 1878279 := bstep (se 1 (by rfl) ⟨1408709, by rfl⟩ : syracuseStep 1878279 = 2817419) B2817419
theorem B1878287 : Blo 1877140 1878287 := bstep (se 1 (by rfl) ⟨1408715, by rfl⟩ : syracuseStep 1878287 = 2817431) B2817431
theorem B4819243 : Blo 1877140 4819243 := bstep (se 1 (by rfl) ⟨3614432, by rfl⟩ : syracuseStep 4819243 = 7228865) B7228865
theorem B1878331 : Blo 1877140 1878331 := bstep (se 1 (by rfl) ⟨1408748, by rfl⟩ : syracuseStep 1878331 = 2817497) B2817497
theorem B4753799 : Blo 1877140 4753799 := bstep (se 1 (by rfl) ⟨3565349, by rfl⟩ : syracuseStep 4753799 = 7130699) B7130699
theorem B1878407 : Blo 1877140 1878407 := bstep (se 1 (by rfl) ⟨1408805, by rfl⟩ : syracuseStep 1878407 = 2817611) B2817611
theorem B1878415 : Blo 1877140 1878415 := bstep (se 1 (by rfl) ⟨1408811, by rfl⟩ : syracuseStep 1878415 = 2817623) B2817623
theorem B2378155 : Blo 1877140 2378155 := bstep (se 1 (by rfl) ⟨1783616, by rfl⟩ : syracuseStep 2378155 = 3567233) B3567233
theorem B7129529 : Blo 1877140 7129529 := bstep (se 2 (by rfl) ⟨2673573, by rfl⟩ : syracuseStep 7129529 = 5347147) B5347147
theorem B4753849 : Blo 1877140 4753849 := bstep (se 2 (by rfl) ⟨1782693, by rfl⟩ : syracuseStep 4753849 = 3565387) B3565387
theorem B1878459 : Blo 1877140 1878459 := bstep (se 1 (by rfl) ⟨1408844, by rfl⟩ : syracuseStep 1878459 = 2817689) B2817689
theorem B1878535 : Blo 1877140 1878535 := bstep (se 1 (by rfl) ⟨1408901, by rfl⟩ : syracuseStep 1878535 = 2817803) B2817803
theorem B1878543 : Blo 1877140 1878543 := bstep (se 1 (by rfl) ⟨1408907, by rfl⟩ : syracuseStep 1878543 = 2817815) B2817815
theorem B10701355 : Blo 1877140 10701355 := bstep (se 1 (by rfl) ⟨8026016, by rfl⟩ : syracuseStep 10701355 = 16052033) B16052033
theorem B2673209 : Blo 1877140 2673209 := bstep (se 2 (by rfl) ⟨1002453, by rfl⟩ : syracuseStep 2673209 = 2004907) B2004907
theorem B1878587 : Blo 1877140 1878587 := bstep (se 1 (by rfl) ⟨1408940, by rfl⟩ : syracuseStep 1878587 = 2817881) B2817881
theorem B1878663 : Blo 1877140 1878663 := bstep (se 1 (by rfl) ⟨1408997, by rfl⟩ : syracuseStep 1878663 = 2817995) B2817995
theorem B1878671 : Blo 1877140 1878671 := bstep (se 1 (by rfl) ⟨1409003, by rfl⟩ : syracuseStep 1878671 = 2818007) B2818007
theorem B1878715 : Blo 1877140 1878715 := bstep (se 1 (by rfl) ⟨1409036, by rfl⟩ : syracuseStep 1878715 = 2818073) B2818073
theorem B13200101 : Blo 1877140 13200101 := bstep (se 4 (by rfl) ⟨1237509, by rfl⟩ : syracuseStep 13200101 = 2475019) B2475019
theorem B1878791 : Blo 1877140 1878791 := bstep (se 1 (by rfl) ⟨1409093, by rfl⟩ : syracuseStep 1878791 = 2818187) B2818187
theorem B3009295 : Blo 1877140 3009295 := bstep (se 1 (by rfl) ⟨2256971, by rfl⟩ : syracuseStep 3009295 = 4513943) B4513943
theorem B1878799 : Blo 1877140 1878799 := bstep (se 1 (by rfl) ⟨1409099, by rfl⟩ : syracuseStep 1878799 = 2818199) B2818199
theorem B1878843 : Blo 1877140 1878843 := bstep (se 1 (by rfl) ⟨1409132, by rfl⟩ : syracuseStep 1878843 = 2818265) B2818265
theorem B1878919 : Blo 1877140 1878919 := bstep (se 1 (by rfl) ⟨1409189, by rfl⟩ : syracuseStep 1878919 = 2818379) B2818379
theorem B1878927 : Blo 1877140 1878927 := bstep (se 1 (by rfl) ⟨1409195, by rfl⟩ : syracuseStep 1878927 = 2818391) B2818391
theorem B1878971 : Blo 1877140 1878971 := bstep (se 1 (by rfl) ⟨1409228, by rfl⟩ : syracuseStep 1878971 = 2818457) B2818457
theorem B21400523 : Blo 1877140 21400523 := bstep (se 1 (by rfl) ⟨16050392, by rfl⟩ : syracuseStep 21400523 = 32100785) B32100785
theorem B1879047 : Blo 1877140 1879047 := bstep (se 1 (by rfl) ⟨1409285, by rfl⟩ : syracuseStep 1879047 = 2818571) B2818571
theorem B4754447 : Blo 1877140 4754447 := bstep (se 1 (by rfl) ⟨3565835, by rfl⟩ : syracuseStep 4754447 = 7131671) B7131671
theorem B1879055 : Blo 1877140 1879055 := bstep (se 1 (by rfl) ⟨1409291, by rfl⟩ : syracuseStep 1879055 = 2818583) B2818583
theorem B9505835 : Blo 1877140 9505835 := bstep (se 1 (by rfl) ⟨7129376, by rfl⟩ : syracuseStep 9505835 = 14258753) B14258753
theorem B1879099 : Blo 1877140 1879099 := bstep (se 1 (by rfl) ⟨1409324, by rfl⟩ : syracuseStep 1879099 = 2818649) B2818649
theorem B6335549 : Blo 1877140 6335549 := bstep (se 3 (by rfl) ⟨1187915, by rfl⟩ : syracuseStep 6335549 = 2375831) B2375831
theorem B5868605 : Blo 1877140 5868605 := bstep (se 3 (by rfl) ⟨1100363, by rfl⟩ : syracuseStep 5868605 = 2200727) B2200727
theorem B10153133 : Blo 1877140 10153133 := bstep (se 3 (by rfl) ⟨1903712, by rfl⟩ : syracuseStep 10153133 = 3807425) B3807425
theorem B2256059 : Blo 1877140 2256059 := bstep (se 1 (by rfl) ⟨1692044, by rfl⟩ : syracuseStep 2256059 = 3384089) B3384089
theorem B3566891 : Blo 1877140 3566891 := bstep (se 1 (by rfl) ⟨2675168, by rfl⟩ : syracuseStep 3566891 = 5350337) B5350337
theorem B54152549 : Blo 1877140 54152549 := bstep (se 4 (by rfl) ⟨5076801, by rfl⟩ : syracuseStep 54152549 = 10153603) B10153603
theorem B2674063 : Blo 1877140 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B4009591 : Blo 1877140 4009591 := bstep (se 1 (by rfl) ⟨3007193, by rfl⟩ : syracuseStep 4009591 = 6014387) B6014387
theorem B4755145 : Blo 1877140 4755145 := bstep (se 2 (by rfl) ⟨1783179, by rfl⟩ : syracuseStep 4755145 = 3566359) B3566359
theorem B2141959 : Blo 1877140 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B36581165 : Blo 1877140 36581165 := bstep (se 3 (by rfl) ⟨6858968, by rfl⟩ : syracuseStep 36581165 = 13717937) B13717937
theorem B4755287 : Blo 1877140 4755287 := bstep (se 1 (by rfl) ⟨3566465, by rfl⟩ : syracuseStep 4755287 = 7132931) B7132931
theorem B24055703 : Blo 1877140 24055703 := bstep (se 1 (by rfl) ⟨18041777, by rfl⟩ : syracuseStep 24055703 = 36083555) B36083555
theorem B2674633 : Blo 1877140 2674633 := bstep (se 2 (by rfl) ⟨1002987, by rfl⟩ : syracuseStep 2674633 = 2005975) B2005975
theorem B6770945 : Blo 1877140 6770945 := bstep (se 2 (by rfl) ⟨2539104, by rfl⟩ : syracuseStep 6770945 = 5078209) B5078209
theorem B9146675 : Blo 1877140 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B2855227 : Blo 1877140 2855227 := bstep (se 1 (by rfl) ⟨2141420, by rfl⟩ : syracuseStep 2855227 = 4282841) B4282841
theorem B9507131 : Blo 1877140 9507131 := bstep (se 1 (by rfl) ⟨7130348, by rfl⟩ : syracuseStep 9507131 = 14260697) B14260697
theorem B5345689 : Blo 1877140 5345689 := bstep (se 2 (by rfl) ⟨2004633, by rfl⟩ : syracuseStep 5345689 = 4009267) B4009267
theorem B6336953 : Blo 1877140 6336953 := bstep (se 2 (by rfl) ⟨2376357, by rfl⟩ : syracuseStep 6336953 = 4752715) B4752715
theorem B7614929 : Blo 1877140 7614929 := bstep (se 2 (by rfl) ⟨2855598, by rfl⟩ : syracuseStep 7614929 = 5711197) B5711197
theorem B9507293 : Blo 1877140 9507293 := bstep (se 3 (by rfl) ⟨1782617, by rfl⟩ : syracuseStep 9507293 = 3565235) B3565235
theorem B15225347 : Blo 1877140 15225347 := bstep (se 1 (by rfl) ⟨11419010, by rfl⟩ : syracuseStep 15225347 = 22838021) B22838021
theorem B60903971 : Blo 1877140 60903971 := bstep (se 1 (by rfl) ⟨45677978, by rfl⟩ : syracuseStep 60903971 = 91355957) B91355957
theorem B18043469 : Blo 1877140 18043469 := bstep (se 3 (by rfl) ⟨3383150, by rfl⟩ : syracuseStep 18043469 = 6766301) B6766301
theorem B5345939 : Blo 1877140 5345939 := bstep (se 1 (by rfl) ⟨4009454, by rfl⟩ : syracuseStep 5345939 = 8018909) B8018909
theorem B10695341 : Blo 1877140 10695341 := bstep (se 3 (by rfl) ⟨2005376, by rfl⟩ : syracuseStep 10695341 = 4010753) B4010753
theorem B4510475 : Blo 1877140 4510475 := bstep (se 1 (by rfl) ⟨3382856, by rfl⟩ : syracuseStep 4510475 = 6765713) B6765713
theorem B9507617 : Blo 1877140 9507617 := bstep (se 2 (by rfl) ⟨3565356, by rfl⟩ : syracuseStep 9507617 = 7130713) B7130713
theorem B4223879 : Blo 1877140 4223879 := bstep (se 1 (by rfl) ⟨3167909, by rfl⟩ : syracuseStep 4223879 = 6335819) B6335819
theorem B7230343 : Blo 1877140 7230343 := bstep (se 1 (by rfl) ⟨5422757, by rfl⟩ : syracuseStep 7230343 = 10845515) B10845515
theorem B15225803 : Blo 1877140 15225803 := bstep (se 1 (by rfl) ⟨11419352, by rfl⟩ : syracuseStep 15225803 = 22838705) B22838705
theorem B6337547 : Blo 1877140 6337547 := bstep (se 1 (by rfl) ⟨4753160, by rfl⟩ : syracuseStep 6337547 = 9506321) B9506321
theorem B7132171 : Blo 1877140 7132171 := bstep (se 1 (by rfl) ⟨5349128, by rfl⟩ : syracuseStep 7132171 = 10698257) B10698257
theorem B4224059 : Blo 1877140 4224059 := bstep (se 1 (by rfl) ⟨3168044, by rfl⟩ : syracuseStep 4224059 = 6336089) B6336089
theorem B6337655 : Blo 1877140 6337655 := bstep (se 1 (by rfl) ⟨4753241, by rfl⟩ : syracuseStep 6337655 = 9506483) B9506483
theorem B4224185 : Blo 1877140 4224185 := bstep (se 2 (by rfl) ⟨1584069, by rfl⟩ : syracuseStep 4224185 = 3168139) B3168139
theorem B7132475 : Blo 1877140 7132475 := bstep (se 1 (by rfl) ⟨5349356, by rfl⟩ : syracuseStep 7132475 = 10698713) B10698713
theorem B4224527 : Blo 1877140 4224527 := bstep (se 1 (by rfl) ⟨3168395, by rfl⟩ : syracuseStep 4224527 = 6336791) B6336791
theorem B4224545 : Blo 1877140 4224545 := bstep (se 2 (by rfl) ⟨1584204, by rfl⟩ : syracuseStep 4224545 = 3168409) B3168409
theorem B6772285 : Blo 1877140 6772285 := bstep (se 3 (by rfl) ⟨1269803, by rfl⟩ : syracuseStep 6772285 = 2539607) B2539607
theorem B5346931 : Blo 1877140 5346931 := bstep (se 1 (by rfl) ⟨4010198, by rfl⟩ : syracuseStep 5346931 = 8020397) B8020397
theorem B6338249 : Blo 1877140 6338249 := bstep (se 2 (by rfl) ⟨2376843, by rfl⟩ : syracuseStep 6338249 = 4753687) B4753687
theorem B9508589 : Blo 1877140 9508589 := bstep (se 3 (by rfl) ⟨1782860, by rfl⟩ : syracuseStep 9508589 = 3565721) B3565721
theorem B15234817 : Blo 1877140 15234817 := bstep (se 2 (by rfl) ⟨5713056, by rfl⟩ : syracuseStep 15234817 = 11426113) B11426113
theorem B2815751 : Blo 1877140 2815751 := bstep (se 1 (by rfl) ⟨2111813, by rfl⟩ : syracuseStep 2815751 = 4223627) B4223627
theorem B10696481 : Blo 1877140 10696481 := bstep (se 2 (by rfl) ⟨4011180, by rfl⟩ : syracuseStep 10696481 = 8022361) B8022361
theorem B7132961 : Blo 1877140 7132961 := bstep (se 2 (by rfl) ⟨2674860, by rfl⟩ : syracuseStep 7132961 = 5349721) B5349721
theorem B2815787 : Blo 1877140 2815787 := bstep (se 1 (by rfl) ⟨2111840, by rfl⟩ : syracuseStep 2815787 = 4223681) B4223681
theorem B2815817 : Blo 1877140 2815817 := bstep (se 2 (by rfl) ⟨1055931, by rfl⟩ : syracuseStep 2815817 = 2111863) B2111863
theorem B3168119 : Blo 1877140 3168119 := bstep (se 1 (by rfl) ⟨2376089, by rfl⟩ : syracuseStep 3168119 = 4752179) B4752179
theorem B4224887 : Blo 1877140 4224887 := bstep (se 1 (by rfl) ⟨3168665, by rfl⟩ : syracuseStep 4224887 = 6337331) B6337331
theorem B9025465 : Blo 1877140 9025465 := bstep (se 2 (by rfl) ⟨3384549, by rfl⟩ : syracuseStep 9025465 = 6769099) B6769099
theorem B6019001 : Blo 1877140 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B2815931 : Blo 1877140 2815931 := bstep (se 1 (by rfl) ⟨2111948, by rfl⟩ : syracuseStep 2815931 = 4223897) B4223897
theorem B2815991 : Blo 1877140 2815991 := bstep (se 1 (by rfl) ⟨2111993, by rfl⟩ : syracuseStep 2815991 = 4223987) B4223987
theorem B2816015 : Blo 1877140 2816015 := bstep (se 1 (by rfl) ⟨2112011, by rfl⟩ : syracuseStep 2816015 = 4224023) B4224023
theorem B4225067 : Blo 1877140 4225067 := bstep (se 1 (by rfl) ⟨3168800, by rfl⟩ : syracuseStep 4225067 = 6337601) B6337601
theorem B2816057 : Blo 1877140 2816057 := bstep (se 2 (by rfl) ⟨1056021, by rfl⟩ : syracuseStep 2816057 = 2112043) B2112043
theorem B2816135 : Blo 1877140 2816135 := bstep (se 1 (by rfl) ⟨2112101, by rfl⟩ : syracuseStep 2816135 = 4224203) B4224203
theorem B2816171 : Blo 1877140 2816171 := bstep (se 1 (by rfl) ⟨2112128, by rfl⟩ : syracuseStep 2816171 = 4224257) B4224257
theorem B46307501 : Blo 1877140 46307501 := bstep (se 3 (by rfl) ⟨8682656, by rfl⟩ : syracuseStep 46307501 = 17365313) B17365313
theorem B2816201 : Blo 1877140 2816201 := bstep (se 2 (by rfl) ⟨1056075, by rfl⟩ : syracuseStep 2816201 = 2112151) B2112151
theorem B2816315 : Blo 1877140 2816315 := bstep (se 1 (by rfl) ⟨2112236, by rfl⟩ : syracuseStep 2816315 = 4224473) B4224473
theorem B3168571 : Blo 1877140 3168571 := bstep (se 1 (by rfl) ⟨2376428, by rfl⟩ : syracuseStep 3168571 = 4752857) B4752857
theorem B8026427 : Blo 1877140 8026427 := bstep (se 1 (by rfl) ⟨6019820, by rfl⟩ : syracuseStep 8026427 = 12039641) B12039641
theorem B2816375 : Blo 1877140 2816375 := bstep (se 1 (by rfl) ⟨2112281, by rfl⟩ : syracuseStep 2816375 = 4224563) B4224563
theorem B6338951 : Blo 1877140 6338951 := bstep (se 1 (by rfl) ⟨4754213, by rfl⟩ : syracuseStep 6338951 = 9508427) B9508427
theorem B2816399 : Blo 1877140 2816399 := bstep (se 1 (by rfl) ⟨2112299, by rfl⟩ : syracuseStep 2816399 = 4224599) B4224599
theorem B34265489 : Blo 1877140 34265489 := bstep (se 2 (by rfl) ⟨12849558, by rfl⟩ : syracuseStep 34265489 = 25699117) B25699117
theorem B4225427 : Blo 1877140 4225427 := bstep (se 1 (by rfl) ⟨3169070, by rfl⟩ : syracuseStep 4225427 = 6338141) B6338141
theorem B2816441 : Blo 1877140 2816441 := bstep (se 2 (by rfl) ⟨1056165, by rfl⟩ : syracuseStep 2816441 = 2112331) B2112331
theorem B3168713 : Blo 1877140 3168713 := bstep (se 2 (by rfl) ⟨1188267, by rfl⟩ : syracuseStep 3168713 = 2376535) B2376535
theorem B4225481 : Blo 1877140 4225481 := bstep (se 2 (by rfl) ⟨1584555, by rfl⟩ : syracuseStep 4225481 = 3169111) B3169111
theorem B2112007 : Blo 1877140 2112007 := bstep (se 1 (by rfl) ⟨1584005, by rfl⟩ : syracuseStep 2112007 = 3168011) B3168011
theorem B2816519 : Blo 1877140 2816519 := bstep (se 1 (by rfl) ⟨2112389, by rfl⟩ : syracuseStep 2816519 = 4224779) B4224779
theorem B10295819 : Blo 1877140 10295819 := bstep (se 1 (by rfl) ⟨7721864, by rfl⟩ : syracuseStep 10295819 = 15443729) B15443729
theorem B9509399 : Blo 1877140 9509399 := bstep (se 1 (by rfl) ⟨7132049, by rfl⟩ : syracuseStep 9509399 = 14264099) B14264099
theorem B2816555 : Blo 1877140 2816555 := bstep (se 1 (by rfl) ⟨2112416, by rfl⟩ : syracuseStep 2816555 = 4224833) B4224833
theorem B8026685 : Blo 1877140 8026685 := bstep (se 3 (by rfl) ⟨1505003, by rfl⟩ : syracuseStep 8026685 = 3010007) B3010007
theorem B2816585 : Blo 1877140 2816585 := bstep (se 2 (by rfl) ⟨1056219, by rfl⟩ : syracuseStep 2816585 = 2112439) B2112439
theorem B13539959 : Blo 1877140 13539959 := bstep (se 1 (by rfl) ⟨10154969, by rfl⟩ : syracuseStep 13539959 = 20309939) B20309939
theorem B2112187 : Blo 1877140 2112187 := bstep (se 1 (by rfl) ⟨1584140, by rfl⟩ : syracuseStep 2112187 = 3168281) B3168281
theorem B2816699 : Blo 1877140 2816699 := bstep (se 1 (by rfl) ⟨2112524, by rfl⟩ : syracuseStep 2816699 = 4225049) B4225049
theorem B7133933 : Blo 1877140 7133933 := bstep (se 3 (by rfl) ⟨1337612, by rfl⟩ : syracuseStep 7133933 = 2675225) B2675225
theorem B2816759 : Blo 1877140 2816759 := bstep (se 1 (by rfl) ⟨2112569, by rfl⟩ : syracuseStep 2816759 = 4225139) B4225139
theorem B6339329 : Blo 1877140 6339329 := bstep (se 2 (by rfl) ⟨2377248, by rfl⟩ : syracuseStep 6339329 = 4754497) B4754497
theorem B2816783 : Blo 1877140 2816783 := bstep (se 1 (by rfl) ⟨2112587, by rfl⟩ : syracuseStep 2816783 = 4225175) B4225175
theorem B2816825 : Blo 1877140 2816825 := bstep (se 2 (by rfl) ⟨1056309, by rfl⟩ : syracuseStep 2816825 = 2112619) B2112619
theorem B2816903 : Blo 1877140 2816903 := bstep (se 1 (by rfl) ⟨2112677, by rfl⟩ : syracuseStep 2816903 = 4225355) B4225355
theorem B3431315 : Blo 1877140 3431315 := bstep (se 1 (by rfl) ⟨2573486, by rfl⟩ : syracuseStep 3431315 = 5146973) B5146973
theorem B77118371 : Blo 1877140 77118371 := bstep (se 1 (by rfl) ⟨57838778, by rfl⟩ : syracuseStep 77118371 = 115677557) B115677557
theorem B2816939 : Blo 1877140 2816939 := bstep (se 1 (by rfl) ⟨2112704, by rfl⟩ : syracuseStep 2816939 = 4225409) B4225409
theorem B2816969 : Blo 1877140 2816969 := bstep (se 2 (by rfl) ⟨1056363, by rfl⟩ : syracuseStep 2816969 = 2112727) B2112727
theorem B2817083 : Blo 1877140 2817083 := bstep (se 1 (by rfl) ⟨2112812, by rfl⟩ : syracuseStep 2817083 = 4225625) B4225625
theorem B2817143 : Blo 1877140 2817143 := bstep (se 1 (by rfl) ⟨2112857, by rfl⟩ : syracuseStep 2817143 = 4225715) B4225715
theorem B4512887 : Blo 1877140 4512887 := bstep (se 1 (by rfl) ⟨3384665, by rfl⟩ : syracuseStep 4512887 = 6769331) B6769331
theorem B7617655 : Blo 1877140 7617655 := bstep (se 1 (by rfl) ⟨5713241, by rfl⟩ : syracuseStep 7617655 = 11426483) B11426483
theorem B3169415 : Blo 1877140 3169415 := bstep (se 1 (by rfl) ⟨2377061, by rfl⟩ : syracuseStep 3169415 = 4754123) B4754123
theorem B4226183 : Blo 1877140 4226183 := bstep (se 1 (by rfl) ⟨3169637, by rfl⟩ : syracuseStep 4226183 = 6339275) B6339275
theorem B2112655 : Blo 1877140 2112655 := bstep (se 1 (by rfl) ⟨1584491, by rfl⟩ : syracuseStep 2112655 = 3168983) B3168983
theorem B2817167 : Blo 1877140 2817167 := bstep (se 1 (by rfl) ⟨2112875, by rfl⟩ : syracuseStep 2817167 = 4225751) B4225751
theorem B2817209 : Blo 1877140 2817209 := bstep (se 2 (by rfl) ⟨1056453, by rfl⟩ : syracuseStep 2817209 = 2112907) B2112907
theorem B5348537 : Blo 1877140 5348537 := bstep (se 2 (by rfl) ⟨2005701, by rfl⟩ : syracuseStep 5348537 = 4011403) B4011403
theorem B16268525 : Blo 1877140 16268525 := bstep (se 3 (by rfl) ⟨3050348, by rfl⟩ : syracuseStep 16268525 = 6100697) B6100697
theorem B2817287 : Blo 1877140 2817287 := bstep (se 1 (by rfl) ⟨2112965, by rfl⟩ : syracuseStep 2817287 = 4225931) B4225931
theorem B2817323 : Blo 1877140 2817323 := bstep (se 1 (by rfl) ⟨2112992, by rfl⟩ : syracuseStep 2817323 = 4225985) B4225985
theorem B4226363 : Blo 1877140 4226363 := bstep (se 1 (by rfl) ⟨3169772, by rfl⟩ : syracuseStep 4226363 = 6339545) B6339545
theorem B2817353 : Blo 1877140 2817353 := bstep (se 2 (by rfl) ⟨1056507, by rfl⟩ : syracuseStep 2817353 = 2113015) B2113015
theorem B4226489 : Blo 1877140 4226489 := bstep (se 2 (by rfl) ⟨1584933, by rfl⟩ : syracuseStep 4226489 = 3169867) B3169867
theorem B2817467 : Blo 1877140 2817467 := bstep (se 1 (by rfl) ⟨2113100, by rfl⟩ : syracuseStep 2817467 = 4226201) B4226201
theorem B11427281 : Blo 1877140 11427281 := bstep (se 2 (by rfl) ⟨4285230, by rfl⟩ : syracuseStep 11427281 = 8570461) B8570461
theorem B2817527 : Blo 1877140 2817527 := bstep (se 1 (by rfl) ⟨2113145, by rfl⟩ : syracuseStep 2817527 = 4226291) B4226291
theorem B5348879 : Blo 1877140 5348879 := bstep (se 1 (by rfl) ⟨4011659, by rfl⟩ : syracuseStep 5348879 = 8023319) B8023319
theorem B2817551 : Blo 1877140 2817551 := bstep (se 1 (by rfl) ⟨2113163, by rfl⟩ : syracuseStep 2817551 = 4226327) B4226327
theorem B10837547 : Blo 1877140 10837547 := bstep (se 1 (by rfl) ⟨8128160, by rfl⟩ : syracuseStep 10837547 = 16256321) B16256321
theorem B16047659 : Blo 1877140 16047659 := bstep (se 1 (by rfl) ⟨12035744, by rfl⟩ : syracuseStep 16047659 = 24071489) B24071489
theorem B6340139 : Blo 1877140 6340139 := bstep (se 1 (by rfl) ⟨4755104, by rfl⟩ : syracuseStep 6340139 = 9510209) B9510209
theorem B2817593 : Blo 1877140 2817593 := bstep (se 2 (by rfl) ⟨1056597, by rfl⟩ : syracuseStep 2817593 = 2113195) B2113195
theorem B2113159 : Blo 1877140 2113159 := bstep (se 1 (by rfl) ⟨1584869, by rfl⟩ : syracuseStep 2113159 = 3169739) B3169739
theorem B2817671 : Blo 1877140 2817671 := bstep (se 1 (by rfl) ⟨2113253, by rfl⟩ : syracuseStep 2817671 = 4226507) B4226507
theorem B2817707 : Blo 1877140 2817707 := bstep (se 1 (by rfl) ⟨2113280, by rfl⟩ : syracuseStep 2817707 = 4226561) B4226561
theorem B24075953 : Blo 1877140 24075953 := bstep (se 2 (by rfl) ⟨9028482, by rfl⟩ : syracuseStep 24075953 = 18056965) B18056965
theorem B2817737 : Blo 1877140 2817737 := bstep (se 2 (by rfl) ⟨1056651, by rfl⟩ : syracuseStep 2817737 = 2113303) B2113303
theorem B3170063 : Blo 1877140 3170063 := bstep (se 1 (by rfl) ⟨2377547, by rfl⟩ : syracuseStep 3170063 = 4755095) B4755095
theorem B4226831 : Blo 1877140 4226831 := bstep (se 1 (by rfl) ⟨3170123, by rfl⟩ : syracuseStep 4226831 = 6340247) B6340247
theorem B4226849 : Blo 1877140 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B2113339 : Blo 1877140 2113339 := bstep (se 1 (by rfl) ⟨1585004, by rfl⟩ : syracuseStep 2113339 = 3170009) B3170009
theorem B2817851 : Blo 1877140 2817851 := bstep (se 1 (by rfl) ⟨2113388, by rfl⟩ : syracuseStep 2817851 = 4226777) B4226777
theorem B2817911 : Blo 1877140 2817911 := bstep (se 1 (by rfl) ⟨2113433, by rfl⟩ : syracuseStep 2817911 = 4226867) B4226867
theorem B2817935 : Blo 1877140 2817935 := bstep (se 1 (by rfl) ⟨2113451, by rfl⟩ : syracuseStep 2817935 = 4226903) B4226903
theorem B2817977 : Blo 1877140 2817977 := bstep (se 2 (by rfl) ⟨1056741, by rfl⟩ : syracuseStep 2817977 = 2113483) B2113483
theorem B2539451 : Blo 1877140 2539451 := bstep (se 1 (by rfl) ⟨1904588, by rfl⟩ : syracuseStep 2539451 = 3809177) B3809177
theorem B2818127 : Blo 1877140 2818127 := bstep (se 1 (by rfl) ⟨2113595, by rfl⟩ : syracuseStep 2818127 = 4227191) B4227191
theorem B4751531 : Blo 1877140 4751531 := bstep (se 1 (by rfl) ⟨3563648, by rfl⟩ : syracuseStep 4751531 = 7127297) B7127297
theorem B4513963 : Blo 1877140 4513963 := bstep (se 1 (by rfl) ⟨3385472, by rfl⟩ : syracuseStep 4513963 = 6770945) B6770945
theorem B2818247 : Blo 1877140 2818247 := bstep (se 1 (by rfl) ⟨2113685, by rfl⟩ : syracuseStep 2818247 = 4227371) B4227371
theorem B2113735 : Blo 1877140 2113735 := bstep (se 1 (by rfl) ⟨1585301, by rfl⟩ : syracuseStep 2113735 = 3170603) B3170603
theorem B9503081 : Blo 1877140 9503081 := bstep (se 2 (by rfl) ⟨3563655, by rfl⟩ : syracuseStep 9503081 = 7127311) B7127311
theorem B2818409 : Blo 1877140 2818409 := bstep (se 2 (by rfl) ⟨1056903, by rfl⟩ : syracuseStep 2818409 = 2113807) B2113807
theorem B2818487 : Blo 1877140 2818487 := bstep (se 1 (by rfl) ⟨2113865, by rfl⟩ : syracuseStep 2818487 = 4227731) B4227731
theorem B2376155 : Blo 1877140 2376155 := bstep (se 1 (by rfl) ⟨1782116, by rfl⟩ : syracuseStep 2376155 = 3564233) B3564233
theorem B2818523 : Blo 1877140 2818523 := bstep (se 1 (by rfl) ⟨2113892, by rfl⟩ : syracuseStep 2818523 = 4227785) B4227785
theorem B3006983 : Blo 1877140 3006983 := bstep (se 1 (by rfl) ⟨2255237, by rfl⟩ : syracuseStep 3006983 = 4510475) B4510475
theorem B7127585 : Blo 1877140 7127585 := bstep (se 2 (by rfl) ⟨2672844, by rfl⟩ : syracuseStep 7127585 = 5345689) B5345689
theorem B4227623 : Blo 1877140 4227623 := bstep (se 1 (by rfl) ⟨3170717, by rfl⟩ : syracuseStep 4227623 = 6341435) B6341435
theorem B3170873 : Blo 1877140 3170873 := bstep (se 2 (by rfl) ⟨1189077, by rfl⟩ : syracuseStep 3170873 = 2378155) B2378155
theorem B10150535 : Blo 1877140 10150535 := bstep (se 1 (by rfl) ⟨7612901, by rfl⟩ : syracuseStep 10150535 = 15225803) B15225803
theorem B4227947 : Blo 1877140 4227947 := bstep (se 1 (by rfl) ⟨3170960, by rfl⟩ : syracuseStep 4227947 = 6341921) B6341921
theorem B4228001 : Blo 1877140 4228001 := bstep (se 2 (by rfl) ⟨1585500, by rfl⟩ : syracuseStep 4228001 = 3171001) B3171001
theorem B2376631 : Blo 1877140 2376631 := bstep (se 1 (by rfl) ⟨1782473, by rfl⟩ : syracuseStep 2376631 = 3564947) B3564947
theorem B7128071 : Blo 1877140 7128071 := bstep (se 1 (by rfl) ⟨5346053, by rfl⟩ : syracuseStep 7128071 = 10692107) B10692107
theorem B4752391 : Blo 1877140 4752391 := bstep (se 1 (by rfl) ⟨3564293, by rfl⟩ : syracuseStep 4752391 = 7128587) B7128587
theorem B6341651 : Blo 1877140 6341651 := bstep (se 1 (by rfl) ⟨4756238, by rfl⟩ : syracuseStep 6341651 = 9512477) B9512477
theorem B91374637 : Blo 1877140 91374637 := bstep (se 3 (by rfl) ⟨17132744, by rfl⟩ : syracuseStep 91374637 = 34265489) B34265489
theorem B28918903 : Blo 1877140 28918903 := bstep (se 1 (by rfl) ⟨21689177, by rfl⟩ : syracuseStep 28918903 = 43378355) B43378355
theorem B19268761 : Blo 1877140 19268761 := bstep (se 2 (by rfl) ⟨7225785, by rfl⟩ : syracuseStep 19268761 = 14451571) B14451571
theorem B1877167 : Blo 1877140 1877167 := bstep (se 1 (by rfl) ⟨1407875, by rfl⟩ : syracuseStep 1877167 = 2815751) B2815751
theorem B1877191 : Blo 1877140 1877191 := bstep (se 1 (by rfl) ⟨1407893, by rfl⟩ : syracuseStep 1877191 = 2815787) B2815787
theorem B1877211 : Blo 1877140 1877211 := bstep (se 1 (by rfl) ⟨1407908, by rfl⟩ : syracuseStep 1877211 = 2815817) B2815817
theorem B14255351 : Blo 1877140 14255351 := bstep (se 1 (by rfl) ⟨10691513, by rfl⟩ : syracuseStep 14255351 = 21383027) B21383027
theorem B1877287 : Blo 1877140 1877287 := bstep (se 1 (by rfl) ⟨1407965, by rfl⟩ : syracuseStep 1877287 = 2815931) B2815931
theorem B1877327 : Blo 1877140 1877327 := bstep (se 1 (by rfl) ⟨1407995, by rfl⟩ : syracuseStep 1877327 = 2815991) B2815991
theorem B6341975 : Blo 1877140 6341975 := bstep (se 1 (by rfl) ⟨4756481, by rfl⟩ : syracuseStep 6341975 = 9512963) B9512963
theorem B40600925 : Blo 1877140 40600925 := bstep (se 3 (by rfl) ⟨7612673, by rfl⟩ : syracuseStep 40600925 = 15225347) B15225347
theorem B1877343 : Blo 1877140 1877343 := bstep (se 1 (by rfl) ⟨1408007, by rfl⟩ : syracuseStep 1877343 = 2816015) B2816015
theorem B1877371 : Blo 1877140 1877371 := bstep (se 1 (by rfl) ⟨1408028, by rfl⟩ : syracuseStep 1877371 = 2816057) B2816057
theorem B16049573 : Blo 1877140 16049573 := bstep (se 4 (by rfl) ⟨1504647, by rfl⟩ : syracuseStep 16049573 = 3009295) B3009295
theorem B1877423 : Blo 1877140 1877423 := bstep (se 1 (by rfl) ⟨1408067, by rfl⟩ : syracuseStep 1877423 = 2816135) B2816135
theorem B1877447 : Blo 1877140 1877447 := bstep (se 1 (by rfl) ⟨1408085, by rfl⟩ : syracuseStep 1877447 = 2816171) B2816171
theorem B1877467 : Blo 1877140 1877467 := bstep (se 1 (by rfl) ⟨1408100, by rfl⟩ : syracuseStep 1877467 = 2816201) B2816201
theorem B7128557 : Blo 1877140 7128557 := bstep (se 3 (by rfl) ⟨1336604, by rfl⟩ : syracuseStep 7128557 = 2673209) B2673209
theorem B1877543 : Blo 1877140 1877543 := bstep (se 1 (by rfl) ⟨1408157, by rfl⟩ : syracuseStep 1877543 = 2816315) B2816315
theorem B5350951 : Blo 1877140 5350951 := bstep (se 1 (by rfl) ⟨4013213, by rfl⟩ : syracuseStep 5350951 = 8026427) B8026427
theorem B1877583 : Blo 1877140 1877583 := bstep (se 1 (by rfl) ⟨1408187, by rfl⟩ : syracuseStep 1877583 = 2816375) B2816375
theorem B1877599 : Blo 1877140 1877599 := bstep (se 1 (by rfl) ⟨1408199, by rfl⟩ : syracuseStep 1877599 = 2816399) B2816399
theorem B1877627 : Blo 1877140 1877627 := bstep (se 1 (by rfl) ⟨1408220, by rfl⟩ : syracuseStep 1877627 = 2816441) B2816441
theorem B4753019 : Blo 1877140 4753019 := bstep (se 1 (by rfl) ⟨3564764, by rfl⟩ : syracuseStep 4753019 = 7129529) B7129529
theorem B1877679 : Blo 1877140 1877679 := bstep (se 1 (by rfl) ⟨1408259, by rfl⟩ : syracuseStep 1877679 = 2816519) B2816519
theorem B1877703 : Blo 1877140 1877703 := bstep (se 1 (by rfl) ⟨1408277, by rfl⟩ : syracuseStep 1877703 = 2816555) B2816555
theorem B5351123 : Blo 1877140 5351123 := bstep (se 1 (by rfl) ⟨4013342, by rfl⟩ : syracuseStep 5351123 = 8026685) B8026685
theorem B1877723 : Blo 1877140 1877723 := bstep (se 1 (by rfl) ⟨1408292, by rfl⟩ : syracuseStep 1877723 = 2816585) B2816585
theorem B14255837 : Blo 1877140 14255837 := bstep (se 3 (by rfl) ⟨2672969, by rfl⟩ : syracuseStep 14255837 = 5345939) B5345939
theorem B1877799 : Blo 1877140 1877799 := bstep (se 1 (by rfl) ⟨1408349, by rfl⟩ : syracuseStep 1877799 = 2816699) B2816699
theorem B8800067 : Blo 1877140 8800067 := bstep (se 1 (by rfl) ⟨6600050, by rfl⟩ : syracuseStep 8800067 = 13200101) B13200101
theorem B1877839 : Blo 1877140 1877839 := bstep (se 1 (by rfl) ⟨1408379, by rfl⟩ : syracuseStep 1877839 = 2816759) B2816759
theorem B1877855 : Blo 1877140 1877855 := bstep (se 1 (by rfl) ⟨1408391, by rfl⟩ : syracuseStep 1877855 = 2816783) B2816783
theorem B1877883 : Blo 1877140 1877883 := bstep (se 1 (by rfl) ⟨1408412, by rfl⟩ : syracuseStep 1877883 = 2816825) B2816825
theorem B4753313 : Blo 1877140 4753313 := bstep (se 2 (by rfl) ⟨1782492, by rfl⟩ : syracuseStep 4753313 = 3564985) B3564985
theorem B1877935 : Blo 1877140 1877935 := bstep (se 1 (by rfl) ⟨1408451, by rfl⟩ : syracuseStep 1877935 = 2816903) B2816903
theorem B2287543 : Blo 1877140 2287543 := bstep (se 1 (by rfl) ⟨1715657, by rfl⟩ : syracuseStep 2287543 = 3431315) B3431315
theorem B1877959 : Blo 1877140 1877959 := bstep (se 1 (by rfl) ⟨1408469, by rfl⟩ : syracuseStep 1877959 = 2816939) B2816939
theorem B1877979 : Blo 1877140 1877979 := bstep (se 1 (by rfl) ⟨1408484, by rfl⟩ : syracuseStep 1877979 = 2816969) B2816969
theorem B1878055 : Blo 1877140 1878055 := bstep (se 1 (by rfl) ⟨1408541, by rfl⟩ : syracuseStep 1878055 = 2817083) B2817083
theorem B1878095 : Blo 1877140 1878095 := bstep (se 1 (by rfl) ⟨1408571, by rfl⟩ : syracuseStep 1878095 = 2817143) B2817143
theorem B3008591 : Blo 1877140 3008591 := bstep (se 1 (by rfl) ⟨2256443, by rfl⟩ : syracuseStep 3008591 = 4512887) B4512887
theorem B9029713 : Blo 1877140 9029713 := bstep (se 2 (by rfl) ⟨3386142, by rfl⟩ : syracuseStep 9029713 = 6772285) B6772285
theorem B1878111 : Blo 1877140 1878111 := bstep (se 1 (by rfl) ⟨1408583, by rfl⟩ : syracuseStep 1878111 = 2817167) B2817167
theorem B6768755 : Blo 1877140 6768755 := bstep (se 1 (by rfl) ⟨5076566, by rfl⟩ : syracuseStep 6768755 = 10153133) B10153133
theorem B1878139 : Blo 1877140 1878139 := bstep (se 1 (by rfl) ⟨1408604, by rfl⟩ : syracuseStep 1878139 = 2817209) B2817209
theorem B3565691 : Blo 1877140 3565691 := bstep (se 1 (by rfl) ⟨2674268, by rfl⟩ : syracuseStep 3565691 = 5348537) B5348537
theorem B7129241 : Blo 1877140 7129241 := bstep (se 2 (by rfl) ⟨2673465, by rfl⟩ : syracuseStep 7129241 = 5346931) B5346931
theorem B1878191 : Blo 1877140 1878191 := bstep (se 1 (by rfl) ⟨1408643, by rfl⟩ : syracuseStep 1878191 = 2817287) B2817287
theorem B1878215 : Blo 1877140 1878215 := bstep (se 1 (by rfl) ⟨1408661, by rfl⟩ : syracuseStep 1878215 = 2817323) B2817323
theorem B2377927 : Blo 1877140 2377927 := bstep (se 1 (by rfl) ⟨1783445, by rfl⟩ : syracuseStep 2377927 = 3566891) B3566891
theorem B1878235 : Blo 1877140 1878235 := bstep (se 1 (by rfl) ⟨1408676, by rfl⟩ : syracuseStep 1878235 = 2817353) B2817353
theorem B1878311 : Blo 1877140 1878311 := bstep (se 1 (by rfl) ⟨1408733, by rfl⟩ : syracuseStep 1878311 = 2817467) B2817467
theorem B1878351 : Blo 1877140 1878351 := bstep (se 1 (by rfl) ⟨1408763, by rfl⟩ : syracuseStep 1878351 = 2817527) B2817527
theorem B3565919 : Blo 1877140 3565919 := bstep (se 1 (by rfl) ⟨2674439, by rfl⟩ : syracuseStep 3565919 = 5348879) B5348879
theorem B1878367 : Blo 1877140 1878367 := bstep (se 1 (by rfl) ⟨1408775, by rfl⟩ : syracuseStep 1878367 = 2817551) B2817551
theorem B1878395 : Blo 1877140 1878395 := bstep (se 1 (by rfl) ⟨1408796, by rfl⟩ : syracuseStep 1878395 = 2817593) B2817593
theorem B1878447 : Blo 1877140 1878447 := bstep (se 1 (by rfl) ⟨1408835, by rfl⟩ : syracuseStep 1878447 = 2817671) B2817671
theorem B1878471 : Blo 1877140 1878471 := bstep (se 1 (by rfl) ⟨1408853, by rfl⟩ : syracuseStep 1878471 = 2817707) B2817707
theorem B16050635 : Blo 1877140 16050635 := bstep (se 1 (by rfl) ⟨12037976, by rfl⟩ : syracuseStep 16050635 = 24075953) B24075953
theorem B1878491 : Blo 1877140 1878491 := bstep (se 1 (by rfl) ⟨1408868, by rfl⟩ : syracuseStep 1878491 = 2817737) B2817737
theorem B1878567 : Blo 1877140 1878567 := bstep (se 1 (by rfl) ⟨1408925, by rfl⟩ : syracuseStep 1878567 = 2817851) B2817851
theorem B1878607 : Blo 1877140 1878607 := bstep (se 1 (by rfl) ⟨1408955, by rfl⟩ : syracuseStep 1878607 = 2817911) B2817911
theorem B1878623 : Blo 1877140 1878623 := bstep (se 1 (by rfl) ⟨1408967, by rfl⟩ : syracuseStep 1878623 = 2817935) B2817935
theorem B3566177 : Blo 1877140 3566177 := bstep (se 2 (by rfl) ⟨1337316, by rfl⟩ : syracuseStep 3566177 = 2674633) B2674633
theorem B1878651 : Blo 1877140 1878651 := bstep (se 1 (by rfl) ⟨1408988, by rfl⟩ : syracuseStep 1878651 = 2817977) B2817977
theorem B1878703 : Blo 1877140 1878703 := bstep (se 1 (by rfl) ⟨1409027, by rfl⟩ : syracuseStep 1878703 = 2818055) B2818055
theorem B1878727 : Blo 1877140 1878727 := bstep (se 1 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 1878727 = 2818091) B2818091
theorem B1878747 : Blo 1877140 1878747 := bstep (se 1 (by rfl) ⟨1409060, by rfl⟩ : syracuseStep 1878747 = 2818121) B2818121
theorem B1878823 : Blo 1877140 1878823 := bstep (se 1 (by rfl) ⟨1409117, by rfl⟩ : syracuseStep 1878823 = 2818235) B2818235
theorem B1878863 : Blo 1877140 1878863 := bstep (se 1 (by rfl) ⟨1409147, by rfl⟩ : syracuseStep 1878863 = 2818295) B2818295
theorem B1878879 : Blo 1877140 1878879 := bstep (se 1 (by rfl) ⟨1409159, by rfl⟩ : syracuseStep 1878879 = 2818319) B2818319
theorem B3566443 : Blo 1877140 3566443 := bstep (se 1 (by rfl) ⟨2674832, by rfl⟩ : syracuseStep 3566443 = 5349665) B5349665
theorem B6097783 : Blo 1877140 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B1878907 : Blo 1877140 1878907 := bstep (se 1 (by rfl) ⟨1409180, by rfl⟩ : syracuseStep 1878907 = 2818361) B2818361
theorem B1878959 : Blo 1877140 1878959 := bstep (se 1 (by rfl) ⟨1409219, by rfl⟩ : syracuseStep 1878959 = 2818439) B2818439
theorem B1878983 : Blo 1877140 1878983 := bstep (se 1 (by rfl) ⟨1409237, by rfl⟩ : syracuseStep 1878983 = 2818475) B2818475
theorem B1879003 : Blo 1877140 1879003 := bstep (se 1 (by rfl) ⟨1409252, by rfl⟩ : syracuseStep 1879003 = 2818505) B2818505
theorem B6335495 : Blo 1877140 6335495 := bstep (se 1 (by rfl) ⟨4751621, by rfl⟩ : syracuseStep 6335495 = 9503243) B9503243
theorem B3910675 : Blo 1877140 3910675 := bstep (se 1 (by rfl) ⟨2933006, by rfl⟩ : syracuseStep 3910675 = 5866013) B5866013
theorem B40602647 : Blo 1877140 40602647 := bstep (se 1 (by rfl) ⟨30451985, by rfl⟩ : syracuseStep 40602647 = 60903971) B60903971
theorem B1879079 : Blo 1877140 1879079 := bstep (se 1 (by rfl) ⟨1409309, by rfl⟩ : syracuseStep 1879079 = 2818619) B2818619
theorem B12028979 : Blo 1877140 12028979 := bstep (se 1 (by rfl) ⟨9021734, by rfl⟩ : syracuseStep 12028979 = 18043469) B18043469
theorem B6425657 : Blo 1877140 6425657 := bstep (se 2 (by rfl) ⟨2409621, by rfl⟩ : syracuseStep 6425657 = 4819243) B4819243
theorem B1879119 : Blo 1877140 1879119 := bstep (se 1 (by rfl) ⟨1409339, by rfl⟩ : syracuseStep 1879119 = 2818679) B2818679
theorem B1879135 : Blo 1877140 1879135 := bstep (se 1 (by rfl) ⟨1409351, by rfl⟩ : syracuseStep 1879135 = 2818703) B2818703
theorem B6335603 : Blo 1877140 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B7130227 : Blo 1877140 7130227 := bstep (se 1 (by rfl) ⟨5347670, by rfl⟩ : syracuseStep 7130227 = 10695341) B10695341
theorem B6016157 : Blo 1877140 6016157 := bstep (se 3 (by rfl) ⟨1128029, by rfl⟩ : syracuseStep 6016157 = 2256059) B2256059
theorem B21384485 : Blo 1877140 21384485 := bstep (se 4 (by rfl) ⟨2004795, by rfl⟩ : syracuseStep 21384485 = 4009591) B4009591
theorem B6335873 : Blo 1877140 6335873 := bstep (se 2 (by rfl) ⟨2375952, by rfl⟩ : syracuseStep 6335873 = 4751905) B4751905
theorem B12037643 : Blo 1877140 12037643 := bstep (se 1 (by rfl) ⟨9028232, by rfl⟩ : syracuseStep 12037643 = 18056465) B18056465
theorem B4754983 : Blo 1877140 4754983 := bstep (se 1 (by rfl) ⟨3566237, by rfl⟩ : syracuseStep 4754983 = 7132475) B7132475
theorem B12037693 : Blo 1877140 12037693 := bstep (se 3 (by rfl) ⟨2257067, by rfl⟩ : syracuseStep 12037693 = 4514135) B4514135
theorem B54177457 : Blo 1877140 54177457 := bstep (se 2 (by rfl) ⟨20316546, by rfl⟩ : syracuseStep 54177457 = 40633093) B40633093
theorem B9023197 : Blo 1877140 9023197 := bstep (se 3 (by rfl) ⟨1691849, by rfl⟩ : syracuseStep 9023197 = 3383699) B3383699
theorem B7130987 : Blo 1877140 7130987 := bstep (se 1 (by rfl) ⟨5348240, by rfl⟩ : syracuseStep 7130987 = 10696481) B10696481
theorem B4755307 : Blo 1877140 4755307 := bstep (se 1 (by rfl) ⟨3566480, by rfl⟩ : syracuseStep 4755307 = 7132961) B7132961
theorem B30871667 : Blo 1877140 30871667 := bstep (se 1 (by rfl) ⟨23153750, by rfl⟩ : syracuseStep 30871667 = 46307501) B46307501
theorem B6336683 : Blo 1877140 6336683 := bstep (se 1 (by rfl) ⟨4752512, by rfl⟩ : syracuseStep 6336683 = 9505025) B9505025
theorem B4755955 : Blo 1877140 4755955 := bstep (se 1 (by rfl) ⟨3566966, by rfl⟩ : syracuseStep 4755955 = 7133933) B7133933
theorem B7615009 : Blo 1877140 7615009 := bstep (se 2 (by rfl) ⟨2855628, by rfl⟩ : syracuseStep 7615009 = 5711257) B5711257
theorem B14463521 : Blo 1877140 14463521 := bstep (se 2 (by rfl) ⟨5423820, by rfl⟩ : syracuseStep 14463521 = 10847641) B10847641
theorem B7615073 : Blo 1877140 7615073 := bstep (se 2 (by rfl) ⟨2855652, by rfl⟩ : syracuseStep 7615073 = 5711305) B5711305
theorem B14267015 : Blo 1877140 14267015 := bstep (se 1 (by rfl) ⟨10700261, by rfl⟩ : syracuseStep 14267015 = 21400523) B21400523
theorem B6337223 : Blo 1877140 6337223 := bstep (se 1 (by rfl) ⟨4752917, by rfl⟩ : syracuseStep 6337223 = 9505835) B9505835
theorem B4223699 : Blo 1877140 4223699 := bstep (se 1 (by rfl) ⟨3167774, by rfl⟩ : syracuseStep 4223699 = 6335549) B6335549
theorem B3912403 : Blo 1877140 3912403 := bstep (se 1 (by rfl) ⟨2934302, by rfl⟩ : syracuseStep 3912403 = 5868605) B5868605
theorem B20313089 : Blo 1877140 20313089 := bstep (se 2 (by rfl) ⟨7617408, by rfl⟩ : syracuseStep 20313089 = 15234817) B15234817
theorem B2855945 : Blo 1877140 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B6771869 : Blo 1877140 6771869 := bstep (se 3 (by rfl) ⟨1269725, by rfl⟩ : syracuseStep 6771869 = 2539451) B2539451
theorem B16037135 : Blo 1877140 16037135 := bstep (se 1 (by rfl) ⟨12027851, by rfl⟩ : syracuseStep 16037135 = 24055703) B24055703
theorem B3167707 : Blo 1877140 3167707 := bstep (se 1 (by rfl) ⟨2375780, by rfl⟩ : syracuseStep 3167707 = 4751561) B4751561
theorem B34739675 : Blo 1877140 34739675 := bstep (se 1 (by rfl) ⟨26054756, by rfl⟩ : syracuseStep 34739675 = 52109513) B52109513
theorem B6338087 : Blo 1877140 6338087 := bstep (se 1 (by rfl) ⟨4753565, by rfl⟩ : syracuseStep 6338087 = 9507131) B9507131
theorem B4224635 : Blo 1877140 4224635 := bstep (se 1 (by rfl) ⟨3168476, by rfl⟩ : syracuseStep 4224635 = 6336953) B6336953
theorem B6338195 : Blo 1877140 6338195 := bstep (se 1 (by rfl) ⟨4753646, by rfl⟩ : syracuseStep 6338195 = 9507293) B9507293
theorem B6018745 : Blo 1877140 6018745 := bstep (se 2 (by rfl) ⟨2257029, by rfl⟩ : syracuseStep 6018745 = 4514059) B4514059
theorem B4224761 : Blo 1877140 4224761 := bstep (se 2 (by rfl) ⟨1584285, by rfl⟩ : syracuseStep 4224761 = 3168571) B3168571
theorem B3806969 : Blo 1877140 3806969 := bstep (se 2 (by rfl) ⟨1427613, by rfl⟩ : syracuseStep 3806969 = 2855227) B2855227
theorem B16045883 : Blo 1877140 16045883 := bstep (se 1 (by rfl) ⟨12034412, by rfl⟩ : syracuseStep 16045883 = 24068825) B24068825
theorem B6338411 : Blo 1877140 6338411 := bstep (se 1 (by rfl) ⟨4753808, by rfl⟩ : syracuseStep 6338411 = 9507617) B9507617
theorem B6338465 : Blo 1877140 6338465 := bstep (se 2 (by rfl) ⟨2376924, by rfl⟩ : syracuseStep 6338465 = 4753849) B4753849
theorem B2815919 : Blo 1877140 2815919 := bstep (se 1 (by rfl) ⟨2111939, by rfl⟩ : syracuseStep 2815919 = 4223879) B4223879
theorem B4511675 : Blo 1877140 4511675 := bstep (se 1 (by rfl) ⟨3383756, by rfl⟩ : syracuseStep 4511675 = 6767513) B6767513
theorem B4225031 : Blo 1877140 4225031 := bstep (se 1 (by rfl) ⟨3168773, by rfl⟩ : syracuseStep 4225031 = 6337547) B6337547
theorem B2816009 : Blo 1877140 2816009 := bstep (se 2 (by rfl) ⟨1056003, by rfl⟩ : syracuseStep 2816009 = 2112007) B2112007
theorem B2816039 : Blo 1877140 2816039 := bstep (se 1 (by rfl) ⟨2112029, by rfl⟩ : syracuseStep 2816039 = 4224059) B4224059
theorem B2005031 : Blo 1877140 2005031 := bstep (se 1 (by rfl) ⟨1503773, by rfl⟩ : syracuseStep 2005031 = 3007547) B3007547
theorem B3807271 : Blo 1877140 3807271 := bstep (se 1 (by rfl) ⟨2855453, by rfl⟩ : syracuseStep 3807271 = 5710907) B5710907
theorem B14268473 : Blo 1877140 14268473 := bstep (se 2 (by rfl) ⟨5350677, by rfl⟩ : syracuseStep 14268473 = 10701355) B10701355
theorem B3168335 : Blo 1877140 3168335 := bstep (se 1 (by rfl) ⟨2376251, by rfl⟩ : syracuseStep 3168335 = 4752503) B4752503
theorem B4225103 : Blo 1877140 4225103 := bstep (se 1 (by rfl) ⟨3168827, by rfl⟩ : syracuseStep 4225103 = 6337655) B6337655
theorem B2816123 : Blo 1877140 2816123 := bstep (se 1 (by rfl) ⟨2112092, by rfl⟩ : syracuseStep 2816123 = 4224185) B4224185
theorem B2816249 : Blo 1877140 2816249 := bstep (se 2 (by rfl) ⟨1056093, by rfl⟩ : syracuseStep 2816249 = 2112187) B2112187
theorem B25418033 : Blo 1877140 25418033 := bstep (se 2 (by rfl) ⟨9531762, by rfl⟩ : syracuseStep 25418033 = 19063525) B19063525
theorem B2816351 : Blo 1877140 2816351 := bstep (se 1 (by rfl) ⟨2112263, by rfl⟩ : syracuseStep 2816351 = 4224527) B4224527
theorem B2816363 : Blo 1877140 2816363 := bstep (se 1 (by rfl) ⟨2112272, by rfl⟩ : syracuseStep 2816363 = 4224545) B4224545
theorem B4225499 : Blo 1877140 4225499 := bstep (se 1 (by rfl) ⟨3169124, by rfl⟩ : syracuseStep 4225499 = 6338249) B6338249
theorem B6339059 : Blo 1877140 6339059 := bstep (se 1 (by rfl) ⟨4754294, by rfl⟩ : syracuseStep 6339059 = 9508589) B9508589
theorem B9640457 : Blo 1877140 9640457 := bstep (se 2 (by rfl) ⟨3615171, by rfl⟩ : syracuseStep 9640457 = 7230343) B7230343
theorem B20306477 : Blo 1877140 20306477 := bstep (se 3 (by rfl) ⟨3807464, by rfl⟩ : syracuseStep 20306477 = 7614929) B7614929
theorem B2112079 : Blo 1877140 2112079 := bstep (se 1 (by rfl) ⟨1584059, by rfl⟩ : syracuseStep 2112079 = 3168119) B3168119
theorem B2816591 : Blo 1877140 2816591 := bstep (se 1 (by rfl) ⟨2112443, by rfl⟩ : syracuseStep 2816591 = 4224887) B4224887
theorem B4012667 : Blo 1877140 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B9509561 : Blo 1877140 9509561 := bstep (se 2 (by rfl) ⟨3566085, by rfl⟩ : syracuseStep 9509561 = 7132171) B7132171
theorem B2816711 : Blo 1877140 2816711 := bstep (se 1 (by rfl) ⟨2112533, by rfl⟩ : syracuseStep 2816711 = 4225067) B4225067
theorem B21977801 : Blo 1877140 21977801 := bstep (se 2 (by rfl) ⟨8241675, by rfl⟩ : syracuseStep 21977801 = 16483351) B16483351
theorem B10156873 : Blo 1877140 10156873 := bstep (se 2 (by rfl) ⟨3808827, by rfl⟩ : syracuseStep 10156873 = 7617655) B7617655
theorem B2816873 : Blo 1877140 2816873 := bstep (se 2 (by rfl) ⟨1056327, by rfl⟩ : syracuseStep 2816873 = 2112655) B2112655
theorem B3169199 : Blo 1877140 3169199 := bstep (se 1 (by rfl) ⟨2376899, by rfl⟩ : syracuseStep 3169199 = 4753799) B4753799
theorem B4225967 : Blo 1877140 4225967 := bstep (se 1 (by rfl) ⟨3169475, by rfl⟩ : syracuseStep 4225967 = 6338951) B6338951
theorem B2816951 : Blo 1877140 2816951 := bstep (se 1 (by rfl) ⟨2112713, by rfl⟩ : syracuseStep 2816951 = 4225427) B4225427
theorem B2112475 : Blo 1877140 2112475 := bstep (se 1 (by rfl) ⟨1584356, by rfl⟩ : syracuseStep 2112475 = 3168713) B3168713
theorem B2816987 : Blo 1877140 2816987 := bstep (se 1 (by rfl) ⟨2112740, by rfl⟩ : syracuseStep 2816987 = 4225481) B4225481
theorem B8018945 : Blo 1877140 8018945 := bstep (se 2 (by rfl) ⟨3007104, by rfl⟩ : syracuseStep 8018945 = 6014209) B6014209
theorem B6863879 : Blo 1877140 6863879 := bstep (se 1 (by rfl) ⟨5147909, by rfl⟩ : syracuseStep 6863879 = 10295819) B10295819
theorem B6339599 : Blo 1877140 6339599 := bstep (se 1 (by rfl) ⟨4754699, by rfl⟩ : syracuseStep 6339599 = 9509399) B9509399
theorem B9026639 : Blo 1877140 9026639 := bstep (se 1 (by rfl) ⟨6769979, by rfl⟩ : syracuseStep 9026639 = 13539959) B13539959
theorem B4226219 : Blo 1877140 4226219 := bstep (se 1 (by rfl) ⟨3169664, by rfl⟩ : syracuseStep 4226219 = 6339329) B6339329
theorem B51412247 : Blo 1877140 51412247 := bstep (se 1 (by rfl) ⟨38559185, by rfl⟩ : syracuseStep 51412247 = 77118371) B77118371
theorem B3169631 : Blo 1877140 3169631 := bstep (se 1 (by rfl) ⟨2377223, by rfl⟩ : syracuseStep 3169631 = 4754447) B4754447
theorem B14261669 : Blo 1877140 14261669 := bstep (se 4 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 14261669 = 2674063) B2674063
theorem B2112943 : Blo 1877140 2112943 := bstep (se 1 (by rfl) ⟨1584707, by rfl⟩ : syracuseStep 2112943 = 3169415) B3169415
theorem B2817455 : Blo 1877140 2817455 := bstep (se 1 (by rfl) ⟨2113091, by rfl⟩ : syracuseStep 2817455 = 4226183) B4226183
theorem B10845683 : Blo 1877140 10845683 := bstep (se 1 (by rfl) ⟨8134262, by rfl⟩ : syracuseStep 10845683 = 16268525) B16268525
theorem B2817545 : Blo 1877140 2817545 := bstep (se 2 (by rfl) ⟨1056579, by rfl⟩ : syracuseStep 2817545 = 2113159) B2113159
theorem B2817575 : Blo 1877140 2817575 := bstep (se 1 (by rfl) ⟨2113181, by rfl⟩ : syracuseStep 2817575 = 4226363) B4226363
theorem B36101699 : Blo 1877140 36101699 := bstep (se 1 (by rfl) ⟨27076274, by rfl⟩ : syracuseStep 36101699 = 54152549) B54152549
theorem B6340193 : Blo 1877140 6340193 := bstep (se 2 (by rfl) ⟨2377572, by rfl⟩ : syracuseStep 6340193 = 4755145) B4755145
theorem B2817659 : Blo 1877140 2817659 := bstep (se 1 (by rfl) ⟨2113244, by rfl⟩ : syracuseStep 2817659 = 4226489) B4226489
theorem B7618187 : Blo 1877140 7618187 := bstep (se 1 (by rfl) ⟨5713640, by rfl⟩ : syracuseStep 7618187 = 11427281) B11427281
theorem B7225031 : Blo 1877140 7225031 := bstep (se 1 (by rfl) ⟨5418773, by rfl⟩ : syracuseStep 7225031 = 10837547) B10837547
theorem B10698439 : Blo 1877140 10698439 := bstep (se 1 (by rfl) ⟨8023829, by rfl⟩ : syracuseStep 10698439 = 16047659) B16047659
theorem B4226759 : Blo 1877140 4226759 := bstep (se 1 (by rfl) ⟨3170069, by rfl⟩ : syracuseStep 4226759 = 6340139) B6340139
theorem B2817785 : Blo 1877140 2817785 := bstep (se 2 (by rfl) ⟨1056669, by rfl⟩ : syracuseStep 2817785 = 2113339) B2113339
theorem B36093701 : Blo 1877140 36093701 := bstep (se 4 (by rfl) ⟨3383784, by rfl⟩ : syracuseStep 36093701 = 6767569) B6767569
theorem B2113375 : Blo 1877140 2113375 := bstep (se 1 (by rfl) ⟨1585031, by rfl⟩ : syracuseStep 2113375 = 3170063) B3170063
theorem B2817887 : Blo 1877140 2817887 := bstep (se 1 (by rfl) ⟨2113415, by rfl⟩ : syracuseStep 2817887 = 4226831) B4226831
theorem B2817899 : Blo 1877140 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B24387443 : Blo 1877140 24387443 := bstep (se 1 (by rfl) ⟨18290582, by rfl⟩ : syracuseStep 24387443 = 36581165) B36581165
theorem B3170191 : Blo 1877140 3170191 := bstep (se 1 (by rfl) ⟨2377643, by rfl⟩ : syracuseStep 3170191 = 4755287) B4755287
theorem B12033953 : Blo 1877140 12033953 := bstep (se 2 (by rfl) ⟨4512732, by rfl⟩ : syracuseStep 12033953 = 9025465) B9025465
theorem B3170569 : Blo 1877140 3170569 := bstep (se 2 (by rfl) ⟨1188963, by rfl⟩ : syracuseStep 3170569 = 2377927) B2377927
theorem B2818313 : Blo 1877140 2818313 := bstep (se 2 (by rfl) ⟨1056867, by rfl⟩ : syracuseStep 2818313 = 2113735) B2113735
theorem B4751723 : Blo 1877140 4751723 := bstep (se 1 (by rfl) ⟨3563792, by rfl⟩ : syracuseStep 4751723 = 7127585) B7127585
theorem B9642347 : Blo 1877140 9642347 := bstep (se 1 (by rfl) ⟨7231760, by rfl⟩ : syracuseStep 9642347 = 14463521) B14463521
theorem B2818415 : Blo 1877140 2818415 := bstep (se 1 (by rfl) ⟨2113811, by rfl⟩ : syracuseStep 2818415 = 4227623) B4227623
theorem B2113915 : Blo 1877140 2113915 := bstep (se 1 (by rfl) ⟨1585436, by rfl⟩ : syracuseStep 2113915 = 3170873) B3170873
theorem B6767023 : Blo 1877140 6767023 := bstep (se 1 (by rfl) ⟨5075267, by rfl⟩ : syracuseStep 6767023 = 10150535) B10150535
theorem B9511343 : Blo 1877140 9511343 := bstep (se 1 (by rfl) ⟨7133507, by rfl⟩ : syracuseStep 9511343 = 14267015) B14267015
theorem B2818631 : Blo 1877140 2818631 := bstep (se 1 (by rfl) ⟨2113973, by rfl⟩ : syracuseStep 2818631 = 4227947) B4227947
theorem B2818667 : Blo 1877140 2818667 := bstep (se 1 (by rfl) ⟨2114000, by rfl⟩ : syracuseStep 2818667 = 4228001) B4228001
theorem B6341273 : Blo 1877140 6341273 := bstep (se 2 (by rfl) ⟨2377977, by rfl⟩ : syracuseStep 6341273 = 4755955) B4755955
theorem B13542059 : Blo 1877140 13542059 := bstep (se 1 (by rfl) ⟨10156544, by rfl⟩ : syracuseStep 13542059 = 20313089) B20313089
theorem B4752047 : Blo 1877140 4752047 := bstep (se 1 (by rfl) ⟨3564035, by rfl⟩ : syracuseStep 4752047 = 7128071) B7128071
theorem B4227767 : Blo 1877140 4227767 := bstep (se 1 (by rfl) ⟨3170825, by rfl⟩ : syracuseStep 4227767 = 6341651) B6341651
theorem B4514579 : Blo 1877140 4514579 := bstep (se 1 (by rfl) ⟨3385934, by rfl⟩ : syracuseStep 4514579 = 6771869) B6771869
theorem B9503567 : Blo 1877140 9503567 := bstep (se 1 (by rfl) ⟨7127675, by rfl⟩ : syracuseStep 9503567 = 14255351) B14255351
theorem B10691423 : Blo 1877140 10691423 := bstep (se 1 (by rfl) ⟨8018567, by rfl⟩ : syracuseStep 10691423 = 16037135) B16037135
theorem B4227983 : Blo 1877140 4227983 := bstep (se 1 (by rfl) ⟨3170987, by rfl⟩ : syracuseStep 4227983 = 6341975) B6341975
theorem B27067283 : Blo 1877140 27067283 := bstep (se 1 (by rfl) ⟨20300462, by rfl⟩ : syracuseStep 27067283 = 40600925) B40600925
theorem B10699715 : Blo 1877140 10699715 := bstep (se 1 (by rfl) ⟨8024786, by rfl⟩ : syracuseStep 10699715 = 16049573) B16049573
theorem B23159783 : Blo 1877140 23159783 := bstep (se 1 (by rfl) ⟨17369837, by rfl⟩ : syracuseStep 23159783 = 34739675) B34739675
theorem B4752371 : Blo 1877140 4752371 := bstep (se 1 (by rfl) ⟨3564278, by rfl⟩ : syracuseStep 4752371 = 7128557) B7128557
theorem B13542497 : Blo 1877140 13542497 := bstep (se 2 (by rfl) ⟨5078436, by rfl⟩ : syracuseStep 13542497 = 10156873) B10156873
theorem B9503891 : Blo 1877140 9503891 := bstep (se 1 (by rfl) ⟨7127918, by rfl⟩ : syracuseStep 9503891 = 14255837) B14255837
theorem B5866711 : Blo 1877140 5866711 := bstep (se 1 (by rfl) ⟨4400033, by rfl⟩ : syracuseStep 5866711 = 8800067) B8800067
theorem B1877279 : Blo 1877140 1877279 := bstep (se 1 (by rfl) ⟨1407959, by rfl⟩ : syracuseStep 1877279 = 2815919) B2815919
theorem B3007783 : Blo 1877140 3007783 := bstep (se 1 (by rfl) ⟨2255837, by rfl⟩ : syracuseStep 3007783 = 4511675) B4511675
theorem B1877339 : Blo 1877140 1877339 := bstep (se 1 (by rfl) ⟨1408004, by rfl⟩ : syracuseStep 1877339 = 2816009) B2816009
theorem B1877359 : Blo 1877140 1877359 := bstep (se 1 (by rfl) ⟨1408019, by rfl⟩ : syracuseStep 1877359 = 2816039) B2816039
theorem B9512315 : Blo 1877140 9512315 := bstep (se 1 (by rfl) ⟨7134236, by rfl⟩ : syracuseStep 9512315 = 14268473) B14268473
theorem B121832849 : Blo 1877140 121832849 := bstep (se 2 (by rfl) ⟨45687318, by rfl⟩ : syracuseStep 121832849 = 91374637) B91374637
theorem B1877415 : Blo 1877140 1877415 := bstep (se 1 (by rfl) ⟨1408061, by rfl⟩ : syracuseStep 1877415 = 2816123) B2816123
theorem B2377127 : Blo 1877140 2377127 := bstep (se 1 (by rfl) ⟨1782845, by rfl⟩ : syracuseStep 2377127 = 3565691) B3565691
theorem B4752827 : Blo 1877140 4752827 := bstep (se 1 (by rfl) ⟨3564620, by rfl⟩ : syracuseStep 4752827 = 7129241) B7129241
theorem B1877499 : Blo 1877140 1877499 := bstep (se 1 (by rfl) ⟨1408124, by rfl⟩ : syracuseStep 1877499 = 2816249) B2816249
theorem B25691681 : Blo 1877140 25691681 := bstep (se 2 (by rfl) ⟨9634380, by rfl⟩ : syracuseStep 25691681 = 19268761) B19268761
theorem B1877567 : Blo 1877140 1877567 := bstep (se 1 (by rfl) ⟨1408175, by rfl⟩ : syracuseStep 1877567 = 2816351) B2816351
theorem B2377279 : Blo 1877140 2377279 := bstep (se 1 (by rfl) ⟨1782959, by rfl⟩ : syracuseStep 2377279 = 3565919) B3565919
theorem B1877575 : Blo 1877140 1877575 := bstep (se 1 (by rfl) ⟨1408181, by rfl⟩ : syracuseStep 1877575 = 2816363) B2816363
theorem B10700423 : Blo 1877140 10700423 := bstep (se 1 (by rfl) ⟨8025317, by rfl⟩ : syracuseStep 10700423 = 16050635) B16050635
theorem B1877727 : Blo 1877140 1877727 := bstep (se 1 (by rfl) ⟨1408295, by rfl⟩ : syracuseStep 1877727 = 2816591) B2816591
theorem B2377451 : Blo 1877140 2377451 := bstep (se 1 (by rfl) ⟨1783088, by rfl⟩ : syracuseStep 2377451 = 3566177) B3566177
theorem B1877807 : Blo 1877140 1877807 := bstep (se 1 (by rfl) ⟨1408355, by rfl⟩ : syracuseStep 1877807 = 2816711) B2816711
theorem B1877915 : Blo 1877140 1877915 := bstep (se 1 (by rfl) ⟨1408436, by rfl⟩ : syracuseStep 1877915 = 2816873) B2816873
theorem B1877967 : Blo 1877140 1877967 := bstep (se 1 (by rfl) ⟨1408475, by rfl⟩ : syracuseStep 1877967 = 2816951) B2816951
theorem B1877991 : Blo 1877140 1877991 := bstep (se 1 (by rfl) ⟨1408493, by rfl⟩ : syracuseStep 1877991 = 2816987) B2816987
theorem B27068431 : Blo 1877140 27068431 := bstep (se 1 (by rfl) ⟨20301323, by rfl⟩ : syracuseStep 27068431 = 40602647) B40602647
theorem B16050257 : Blo 1877140 16050257 := bstep (se 2 (by rfl) ⟨6018846, by rfl⟩ : syracuseStep 16050257 = 12037693) B12037693
theorem B14256323 : Blo 1877140 14256323 := bstep (se 1 (by rfl) ⟨10692242, by rfl⟩ : syracuseStep 14256323 = 21384485) B21384485
theorem B14264585 : Blo 1877140 14264585 := bstep (se 2 (by rfl) ⟨5349219, by rfl⟩ : syracuseStep 14264585 = 10698439) B10698439
theorem B1878303 : Blo 1877140 1878303 := bstep (se 1 (by rfl) ⟨1408727, by rfl⟩ : syracuseStep 1878303 = 2817455) B2817455
theorem B1878363 : Blo 1877140 1878363 := bstep (se 1 (by rfl) ⟨1408772, by rfl⟩ : syracuseStep 1878363 = 2817545) B2817545
theorem B1878383 : Blo 1877140 1878383 := bstep (se 1 (by rfl) ⟨1408787, by rfl⟩ : syracuseStep 1878383 = 2817575) B2817575
theorem B1878439 : Blo 1877140 1878439 := bstep (se 1 (by rfl) ⟨1408829, by rfl⟩ : syracuseStep 1878439 = 2817659) B2817659
theorem B1878523 : Blo 1877140 1878523 := bstep (se 1 (by rfl) ⟨1408892, by rfl⟩ : syracuseStep 1878523 = 2817785) B2817785
theorem B24062467 : Blo 1877140 24062467 := bstep (se 1 (by rfl) ⟨18046850, by rfl⟩ : syracuseStep 24062467 = 36093701) B36093701
theorem B1878591 : Blo 1877140 1878591 := bstep (se 1 (by rfl) ⟨1408943, by rfl⟩ : syracuseStep 1878591 = 2817887) B2817887
theorem B4753991 : Blo 1877140 4753991 := bstep (se 1 (by rfl) ⟨3565493, by rfl⟩ : syracuseStep 4753991 = 7130987) B7130987
theorem B1878599 : Blo 1877140 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B3050057 : Blo 1877140 3050057 := bstep (se 2 (by rfl) ⟨1143771, by rfl⟩ : syracuseStep 3050057 = 2287543) B2287543
theorem B8022635 : Blo 1877140 8022635 := bstep (se 1 (by rfl) ⟨6016976, by rfl⟩ : syracuseStep 8022635 = 12033953) B12033953
theorem B18303677 : Blo 1877140 18303677 := bstep (se 3 (by rfl) ⟨3431939, by rfl⟩ : syracuseStep 18303677 = 6863879) B6863879
theorem B1878751 : Blo 1877140 1878751 := bstep (se 1 (by rfl) ⟨1409063, by rfl⟩ : syracuseStep 1878751 = 2818127) B2818127
theorem B20581111 : Blo 1877140 20581111 := bstep (se 1 (by rfl) ⟨15435833, by rfl⟩ : syracuseStep 20581111 = 30871667) B30871667
theorem B1878831 : Blo 1877140 1878831 := bstep (se 1 (by rfl) ⟨1409123, by rfl⟩ : syracuseStep 1878831 = 2818247) B2818247
theorem B6335387 : Blo 1877140 6335387 := bstep (se 1 (by rfl) ⟨4751540, by rfl⟩ : syracuseStep 6335387 = 9503081) B9503081
theorem B1878939 : Blo 1877140 1878939 := bstep (se 1 (by rfl) ⟨1409204, by rfl⟩ : syracuseStep 1878939 = 2818409) B2818409
theorem B1878991 : Blo 1877140 1878991 := bstep (se 1 (by rfl) ⟨1409243, by rfl⟩ : syracuseStep 1878991 = 2818487) B2818487
theorem B1879015 : Blo 1877140 1879015 := bstep (se 1 (by rfl) ⟨1409261, by rfl⟩ : syracuseStep 1879015 = 2818523) B2818523
theorem B10153345 : Blo 1877140 10153345 := bstep (se 2 (by rfl) ⟨3807504, by rfl⟩ : syracuseStep 10153345 = 7615009) B7615009
theorem B3567415 : Blo 1877140 3567415 := bstep (se 1 (by rfl) ⟨2675561, by rfl⟩ : syracuseStep 3567415 = 5351123) B5351123
theorem B4755257 : Blo 1877140 4755257 := bstep (se 2 (by rfl) ⟨1783221, by rfl⟩ : syracuseStep 4755257 = 3566443) B3566443
theorem B8130377 : Blo 1877140 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B6336413 : Blo 1877140 6336413 := bstep (se 3 (by rfl) ⟨1188077, by rfl⟩ : syracuseStep 6336413 = 2376155) B2376155
theorem B6336521 : Blo 1877140 6336521 := bstep (se 2 (by rfl) ⟨2376195, by rfl⟩ : syracuseStep 6336521 = 4752391) B4752391
theorem B5214233 : Blo 1877140 5214233 := bstep (se 2 (by rfl) ⟨1955337, by rfl⟩ : syracuseStep 5214233 = 3910675) B3910675
theorem B9506969 : Blo 1877140 9506969 := bstep (se 2 (by rfl) ⟨3565113, by rfl⟩ : syracuseStep 9506969 = 7130227) B7130227
theorem B16945355 : Blo 1877140 16945355 := bstep (se 1 (by rfl) ⟨12709016, by rfl⟩ : syracuseStep 16945355 = 25418033) B25418033
theorem B6426971 : Blo 1877140 6426971 := bstep (se 1 (by rfl) ⟨4820228, by rfl⟩ : syracuseStep 6426971 = 9640457) B9640457
theorem B13537651 : Blo 1877140 13537651 := bstep (se 1 (by rfl) ⟨10153238, by rfl⟩ : syracuseStep 13537651 = 20306477) B20306477
theorem B2675111 : Blo 1877140 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B14651867 : Blo 1877140 14651867 := bstep (se 1 (by rfl) ⟨10988900, by rfl⟩ : syracuseStep 14651867 = 21977801) B21977801
theorem B4223609 : Blo 1877140 4223609 := bstep (se 2 (by rfl) ⟨1583853, by rfl⟩ : syracuseStep 4223609 = 3167707) B3167707
theorem B5345963 : Blo 1877140 5345963 := bstep (se 1 (by rfl) ⟨4009472, by rfl⟩ : syracuseStep 5345963 = 8018945) B8018945
theorem B4223663 : Blo 1877140 4223663 := bstep (se 1 (by rfl) ⟨3167747, by rfl⟩ : syracuseStep 4223663 = 6335495) B6335495
theorem B6017759 : Blo 1877140 6017759 := bstep (se 1 (by rfl) ⟨4513319, by rfl⟩ : syracuseStep 6017759 = 9026639) B9026639
theorem B4223735 : Blo 1877140 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B4010771 : Blo 1877140 4010771 := bstep (se 1 (by rfl) ⟨3008078, by rfl⟩ : syracuseStep 4010771 = 6016157) B6016157
theorem B8024993 : Blo 1877140 8024993 := bstep (se 2 (by rfl) ⟨3009372, by rfl⟩ : syracuseStep 8024993 = 6018745) B6018745
theorem B4223915 : Blo 1877140 4223915 := bstep (se 1 (by rfl) ⟨3167936, by rfl⟩ : syracuseStep 4223915 = 6335873) B6335873
theorem B9507779 : Blo 1877140 9507779 := bstep (se 1 (by rfl) ⟨7130834, by rfl⟩ : syracuseStep 9507779 = 14261669) B14261669
theorem B12030929 : Blo 1877140 12030929 := bstep (se 2 (by rfl) ⟨4511598, by rfl⟩ : syracuseStep 12030929 = 9023197) B9023197
theorem B7230455 : Blo 1877140 7230455 := bstep (se 1 (by rfl) ⟨5422841, by rfl⟩ : syracuseStep 7230455 = 10845683) B10845683
theorem B8025095 : Blo 1877140 8025095 := bstep (se 1 (by rfl) ⟨6018821, by rfl⟩ : syracuseStep 8025095 = 12037643) B12037643
theorem B16258295 : Blo 1877140 16258295 := bstep (se 1 (by rfl) ⟨12193721, by rfl⟩ : syracuseStep 16258295 = 24387443) B24387443
theorem B7615853 : Blo 1877140 7615853 := bstep (se 3 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 7615853 = 2855945) B2855945
theorem B5076361 : Blo 1877140 5076361 := bstep (se 2 (by rfl) ⟨1903635, by rfl⟩ : syracuseStep 5076361 = 3807271) B3807271
theorem B5346749 : Blo 1877140 5346749 := bstep (se 3 (by rfl) ⟨1002515, by rfl⟩ : syracuseStep 5346749 = 2005031) B2005031
theorem B12039617 : Blo 1877140 12039617 := bstep (se 2 (by rfl) ⟨4514856, by rfl⟩ : syracuseStep 12039617 = 9029713) B9029713
theorem B3167687 : Blo 1877140 3167687 := bstep (se 1 (by rfl) ⟨2375765, by rfl⟩ : syracuseStep 3167687 = 4751531) B4751531
theorem B4224455 : Blo 1877140 4224455 := bstep (se 1 (by rfl) ⟨3168341, by rfl⟩ : syracuseStep 4224455 = 6336683) B6336683
theorem B6018617 : Blo 1877140 6018617 := bstep (se 2 (by rfl) ⟨2256981, by rfl⟩ : syracuseStep 6018617 = 4513963) B4513963
theorem B4224815 : Blo 1877140 4224815 := bstep (se 1 (by rfl) ⟨3168611, by rfl⟩ : syracuseStep 4224815 = 6337223) B6337223
theorem B2815799 : Blo 1877140 2815799 := bstep (se 1 (by rfl) ⟨2111849, by rfl⟩ : syracuseStep 2815799 = 4223699) B4223699
theorem B2816105 : Blo 1877140 2816105 := bstep (se 2 (by rfl) ⟨1056039, by rfl⟩ : syracuseStep 2816105 = 2112079) B2112079
theorem B5216537 : Blo 1877140 5216537 := bstep (se 2 (by rfl) ⟨1956201, by rfl⟩ : syracuseStep 5216537 = 3912403) B3912403
theorem B4225391 : Blo 1877140 4225391 := bstep (se 1 (by rfl) ⟨3169043, by rfl⟩ : syracuseStep 4225391 = 6338087) B6338087
theorem B2816423 : Blo 1877140 2816423 := bstep (se 1 (by rfl) ⟨2112317, by rfl⟩ : syracuseStep 2816423 = 4224635) B4224635
theorem B3168679 : Blo 1877140 3168679 := bstep (se 1 (by rfl) ⟨2376509, by rfl⟩ : syracuseStep 3168679 = 4753019) B4753019
theorem B4225463 : Blo 1877140 4225463 := bstep (se 1 (by rfl) ⟨3169097, by rfl⟩ : syracuseStep 4225463 = 6338195) B6338195
theorem B2816507 : Blo 1877140 2816507 := bstep (se 1 (by rfl) ⟨2112380, by rfl⟩ : syracuseStep 2816507 = 4224761) B4224761
theorem B10697255 : Blo 1877140 10697255 := bstep (se 1 (by rfl) ⟨8022941, by rfl⟩ : syracuseStep 10697255 = 16045883) B16045883
theorem B4225607 : Blo 1877140 4225607 := bstep (se 1 (by rfl) ⟨3169205, by rfl⟩ : syracuseStep 4225607 = 6338411) B6338411
theorem B3168841 : Blo 1877140 3168841 := bstep (se 2 (by rfl) ⟨1188315, by rfl⟩ : syracuseStep 3168841 = 2376631) B2376631
theorem B3168875 : Blo 1877140 3168875 := bstep (se 1 (by rfl) ⟨2376656, by rfl⟩ : syracuseStep 3168875 = 4753313) B4753313
theorem B4225643 : Blo 1877140 4225643 := bstep (se 1 (by rfl) ⟨3169232, by rfl⟩ : syracuseStep 4225643 = 6338465) B6338465
theorem B2816633 : Blo 1877140 2816633 := bstep (se 2 (by rfl) ⟨1056237, by rfl⟩ : syracuseStep 2816633 = 2112475) B2112475
theorem B2816687 : Blo 1877140 2816687 := bstep (se 1 (by rfl) ⟨2112515, by rfl⟩ : syracuseStep 2816687 = 4225031) B4225031
theorem B8018621 : Blo 1877140 8018621 := bstep (se 3 (by rfl) ⟨1503491, by rfl⟩ : syracuseStep 8018621 = 3006983) B3006983
theorem B2112223 : Blo 1877140 2112223 := bstep (se 1 (by rfl) ⟨1584167, by rfl⟩ : syracuseStep 2112223 = 3168335) B3168335
theorem B2816735 : Blo 1877140 2816735 := bstep (se 1 (by rfl) ⟨2112551, by rfl⟩ : syracuseStep 2816735 = 4225103) B4225103
theorem B2005727 : Blo 1877140 2005727 := bstep (se 1 (by rfl) ⟨1504295, by rfl⟩ : syracuseStep 2005727 = 3008591) B3008591
theorem B4512503 : Blo 1877140 4512503 := bstep (se 1 (by rfl) ⟨3384377, by rfl⟩ : syracuseStep 4512503 = 6768755) B6768755
theorem B38558537 : Blo 1877140 38558537 := bstep (se 2 (by rfl) ⟨14459451, by rfl⟩ : syracuseStep 38558537 = 28918903) B28918903
theorem B20306861 : Blo 1877140 20306861 := bstep (se 3 (by rfl) ⟨3807536, by rfl⟩ : syracuseStep 20306861 = 7615073) B7615073
theorem B2816999 : Blo 1877140 2816999 := bstep (se 1 (by rfl) ⟨2112749, by rfl⟩ : syracuseStep 2816999 = 4225499) B4225499
theorem B4226039 : Blo 1877140 4226039 := bstep (se 1 (by rfl) ⟨3169529, by rfl⟩ : syracuseStep 4226039 = 6339059) B6339059
theorem B6339707 : Blo 1877140 6339707 := bstep (se 1 (by rfl) ⟨4754780, by rfl⟩ : syracuseStep 6339707 = 9509561) B9509561
theorem B19266749 : Blo 1877140 19266749 := bstep (se 3 (by rfl) ⟨3612515, by rfl⟩ : syracuseStep 19266749 = 7225031) B7225031
theorem B2817257 : Blo 1877140 2817257 := bstep (se 2 (by rfl) ⟨1056471, by rfl⟩ : syracuseStep 2817257 = 2112943) B2112943
theorem B2112799 : Blo 1877140 2112799 := bstep (se 1 (by rfl) ⟨1584599, by rfl⟩ : syracuseStep 2112799 = 3169199) B3169199
theorem B2817311 : Blo 1877140 2817311 := bstep (se 1 (by rfl) ⟨2112983, by rfl⟩ : syracuseStep 2817311 = 4225967) B4225967
theorem B4226399 : Blo 1877140 4226399 := bstep (se 1 (by rfl) ⟨3169799, by rfl⟩ : syracuseStep 4226399 = 6339599) B6339599
theorem B8019319 : Blo 1877140 8019319 := bstep (se 1 (by rfl) ⟨6014489, by rfl⟩ : syracuseStep 8019319 = 12028979) B12028979
theorem B4283771 : Blo 1877140 4283771 := bstep (se 1 (by rfl) ⟨3212828, by rfl⟩ : syracuseStep 4283771 = 6425657) B6425657
theorem B6339977 : Blo 1877140 6339977 := bstep (se 2 (by rfl) ⟨2377491, by rfl⟩ : syracuseStep 6339977 = 4754983) B4754983
theorem B7134601 : Blo 1877140 7134601 := bstep (se 2 (by rfl) ⟨2675475, by rfl⟩ : syracuseStep 7134601 = 5350951) B5350951
theorem B2817479 : Blo 1877140 2817479 := bstep (se 1 (by rfl) ⟨2113109, by rfl⟩ : syracuseStep 2817479 = 4226219) B4226219
theorem B34274831 : Blo 1877140 34274831 := bstep (se 1 (by rfl) ⟨25706123, by rfl⟩ : syracuseStep 34274831 = 51412247) B51412247
theorem B2113087 : Blo 1877140 2113087 := bstep (se 1 (by rfl) ⟨1584815, by rfl⟩ : syracuseStep 2113087 = 3169631) B3169631
theorem B72236609 : Blo 1877140 72236609 := bstep (se 2 (by rfl) ⟨27088728, by rfl⟩ : syracuseStep 72236609 = 54177457) B54177457
theorem B24067799 : Blo 1877140 24067799 := bstep (se 1 (by rfl) ⟨18050849, by rfl⟩ : syracuseStep 24067799 = 36101699) B36101699
theorem B4226795 : Blo 1877140 4226795 := bstep (se 1 (by rfl) ⟨3170096, by rfl⟩ : syracuseStep 4226795 = 6340193) B6340193
theorem B5078791 : Blo 1877140 5078791 := bstep (se 1 (by rfl) ⟨3809093, by rfl⟩ : syracuseStep 5078791 = 7618187) B7618187
theorem B2817833 : Blo 1877140 2817833 := bstep (se 2 (by rfl) ⟨1056687, by rfl⟩ : syracuseStep 2817833 = 2113375) B2113375
theorem B2817839 : Blo 1877140 2817839 := bstep (se 1 (by rfl) ⟨2113379, by rfl⟩ : syracuseStep 2817839 = 4226759) B4226759
theorem B6340409 : Blo 1877140 6340409 := bstep (se 2 (by rfl) ⟨2377653, by rfl⟩ : syracuseStep 6340409 = 4755307) B4755307
theorem B4226921 : Blo 1877140 4226921 := bstep (se 2 (by rfl) ⟨1585095, by rfl⟩ : syracuseStep 4226921 = 3170191) B3170191
theorem B40607669 : Blo 1877140 40607669 := bstep (se 5 (by rfl) ⟨1903484, by rfl⟩ : syracuseStep 40607669 = 3806969) B3806969
theorem B11296903 : Blo 1877140 11296903 := bstep (se 1 (by rfl) ⟨8472677, by rfl⟩ : syracuseStep 11296903 = 16945355) B16945355
theorem B4284647 : Blo 1877140 4284647 := bstep (se 1 (by rfl) ⟨3213485, by rfl⟩ : syracuseStep 4284647 = 6426971) B6426971
theorem B6340895 : Blo 1877140 6340895 := bstep (se 1 (by rfl) ⟨4755671, by rfl⟩ : syracuseStep 6340895 = 9511343) B9511343
theorem B4227425 : Blo 1877140 4227425 := bstep (se 2 (by rfl) ⟨1585284, by rfl⟩ : syracuseStep 4227425 = 3170569) B3170569
theorem B4227515 : Blo 1877140 4227515 := bstep (se 1 (by rfl) ⟨3170636, by rfl⟩ : syracuseStep 4227515 = 6341273) B6341273
theorem B3563975 : Blo 1877140 3563975 := bstep (se 1 (by rfl) ⟨2672981, by rfl⟩ : syracuseStep 3563975 = 5345963) B5345963
theorem B9028039 : Blo 1877140 9028039 := bstep (se 1 (by rfl) ⟨6771029, by rfl⟩ : syracuseStep 9028039 = 13542059) B13542059
theorem B2818511 : Blo 1877140 2818511 := bstep (se 1 (by rfl) ⟨2113883, by rfl⟩ : syracuseStep 2818511 = 4227767) B4227767
theorem B2818553 : Blo 1877140 2818553 := bstep (se 2 (by rfl) ⟨1056957, by rfl⟩ : syracuseStep 2818553 = 2113915) B2113915
theorem B7127615 : Blo 1877140 7127615 := bstep (se 1 (by rfl) ⟨5345711, by rfl⟩ : syracuseStep 7127615 = 10691423) B10691423
theorem B2818655 : Blo 1877140 2818655 := bstep (se 1 (by rfl) ⟨2113991, by rfl⟩ : syracuseStep 2818655 = 4227983) B4227983
theorem B5349995 : Blo 1877140 5349995 := bstep (se 1 (by rfl) ⟨4012496, by rfl⟩ : syracuseStep 5349995 = 8024993) B8024993
theorem B8020619 : Blo 1877140 8020619 := bstep (se 1 (by rfl) ⟨6015464, by rfl⟩ : syracuseStep 8020619 = 12030929) B12030929
theorem B5350063 : Blo 1877140 5350063 := bstep (se 1 (by rfl) ⟨4012547, by rfl⟩ : syracuseStep 5350063 = 8025095) B8025095
theorem B9028331 : Blo 1877140 9028331 := bstep (se 1 (by rfl) ⟨6771248, by rfl⟩ : syracuseStep 9028331 = 13542497) B13542497
theorem B10838863 : Blo 1877140 10838863 := bstep (se 1 (by rfl) ⟨8129147, by rfl⟩ : syracuseStep 10838863 = 16258295) B16258295
theorem B6341543 : Blo 1877140 6341543 := bstep (se 1 (by rfl) ⟨4756157, by rfl⟩ : syracuseStep 6341543 = 9512315) B9512315
theorem B3564499 : Blo 1877140 3564499 := bstep (se 1 (by rfl) ⟨2673374, by rfl⟩ : syracuseStep 3564499 = 5346749) B5346749
theorem B1877199 : Blo 1877140 1877199 := bstep (se 1 (by rfl) ⟨1407899, by rfl⟩ : syracuseStep 1877199 = 2815799) B2815799
theorem B109765925 : Blo 1877140 109765925 := bstep (se 4 (by rfl) ⟨10290555, by rfl⟩ : syracuseStep 109765925 = 20581111) B20581111
theorem B91399549 : Blo 1877140 91399549 := bstep (se 3 (by rfl) ⟨17137415, by rfl⟩ : syracuseStep 91399549 = 34274831) B34274831
theorem B10700171 : Blo 1877140 10700171 := bstep (se 1 (by rfl) ⟨8025128, by rfl⟩ : syracuseStep 10700171 = 16050257) B16050257
theorem B1877403 : Blo 1877140 1877403 := bstep (se 1 (by rfl) ⟨1408052, by rfl⟩ : syracuseStep 1877403 = 2816105) B2816105
theorem B9504215 : Blo 1877140 9504215 := bstep (se 1 (by rfl) ⟨7128161, by rfl⟩ : syracuseStep 9504215 = 14256323) B14256323
theorem B16041509 : Blo 1877140 16041509 := bstep (se 4 (by rfl) ⟨1503891, by rfl⟩ : syracuseStep 16041509 = 3007783) B3007783
theorem B1877615 : Blo 1877140 1877615 := bstep (se 1 (by rfl) ⟨1408211, by rfl⟩ : syracuseStep 1877615 = 2816423) B2816423
theorem B1877671 : Blo 1877140 1877671 := bstep (se 1 (by rfl) ⟨1408253, by rfl⟩ : syracuseStep 1877671 = 2816507) B2816507
theorem B2033371 : Blo 1877140 2033371 := bstep (se 1 (by rfl) ⟨1525028, by rfl⟩ : syracuseStep 2033371 = 3050057) B3050057
theorem B1877755 : Blo 1877140 1877755 := bstep (se 1 (by rfl) ⟨1408316, by rfl⟩ : syracuseStep 1877755 = 2816633) B2816633
theorem B1877791 : Blo 1877140 1877791 := bstep (se 1 (by rfl) ⟨1408343, by rfl⟩ : syracuseStep 1877791 = 2816687) B2816687
theorem B1877823 : Blo 1877140 1877823 := bstep (se 1 (by rfl) ⟨1408367, by rfl⟩ : syracuseStep 1877823 = 2816735) B2816735
theorem B10692425 : Blo 1877140 10692425 := bstep (se 2 (by rfl) ⟨4009659, by rfl⟩ : syracuseStep 10692425 = 8019319) B8019319
theorem B3008335 : Blo 1877140 3008335 := bstep (se 1 (by rfl) ⟨2256251, by rfl⟩ : syracuseStep 3008335 = 4512503) B4512503
theorem B6768481 : Blo 1877140 6768481 := bstep (se 2 (by rfl) ⟨2538180, by rfl⟩ : syracuseStep 6768481 = 5076361) B5076361
theorem B9512801 : Blo 1877140 9512801 := bstep (se 2 (by rfl) ⟨3567300, by rfl⟩ : syracuseStep 9512801 = 7134601) B7134601
theorem B1877999 : Blo 1877140 1877999 := bstep (se 1 (by rfl) ⟨1408499, by rfl⟩ : syracuseStep 1877999 = 2816999) B2816999
theorem B1878171 : Blo 1877140 1878171 := bstep (se 1 (by rfl) ⟨1408628, by rfl⟩ : syracuseStep 1878171 = 2817257) B2817257
theorem B1878207 : Blo 1877140 1878207 := bstep (se 1 (by rfl) ⟨1408655, by rfl⟩ : syracuseStep 1878207 = 2817311) B2817311
theorem B1878319 : Blo 1877140 1878319 := bstep (se 1 (by rfl) ⟨1408739, by rfl⟩ : syracuseStep 1878319 = 2817479) B2817479
theorem B1878555 : Blo 1877140 1878555 := bstep (se 1 (by rfl) ⟨1408916, by rfl⟩ : syracuseStep 1878555 = 2817833) B2817833
theorem B1878559 : Blo 1877140 1878559 := bstep (se 1 (by rfl) ⟨1408919, by rfl⟩ : syracuseStep 1878559 = 2817839) B2817839
theorem B13904621 : Blo 1877140 13904621 := bstep (se 3 (by rfl) ⟨2607116, by rfl⟩ : syracuseStep 13904621 = 5214233) B5214233
theorem B1878875 : Blo 1877140 1878875 := bstep (se 1 (by rfl) ⟨1409156, by rfl⟩ : syracuseStep 1878875 = 2818313) B2818313
theorem B1878943 : Blo 1877140 1878943 := bstep (se 1 (by rfl) ⟨1409207, by rfl⟩ : syracuseStep 1878943 = 2818415) B2818415
theorem B1879087 : Blo 1877140 1879087 := bstep (se 1 (by rfl) ⟨1409315, by rfl⟩ : syracuseStep 1879087 = 2818631) B2818631
theorem B1879111 : Blo 1877140 1879111 := bstep (se 1 (by rfl) ⟨1409333, by rfl⟩ : syracuseStep 1879111 = 2818667) B2818667
theorem B18050201 : Blo 1877140 18050201 := bstep (se 2 (by rfl) ⟨6768825, by rfl⟩ : syracuseStep 18050201 = 13537651) B13537651
theorem B2673847 : Blo 1877140 2673847 := bstep (se 1 (by rfl) ⟨2005385, by rfl⟩ : syracuseStep 2673847 = 4010771) B4010771
theorem B3009719 : Blo 1877140 3009719 := bstep (se 1 (by rfl) ⟨2257289, by rfl⟩ : syracuseStep 3009719 = 4514579) B4514579
theorem B6335711 : Blo 1877140 6335711 := bstep (se 1 (by rfl) ⟨4751783, by rfl⟩ : syracuseStep 6335711 = 9503567) B9503567
theorem B9022697 : Blo 1877140 9022697 := bstep (se 2 (by rfl) ⟨3383511, by rfl⟩ : syracuseStep 9022697 = 6767023) B6767023
theorem B4820303 : Blo 1877140 4820303 := bstep (se 1 (by rfl) ⟨3615227, by rfl⟩ : syracuseStep 4820303 = 7230455) B7230455
theorem B32083289 : Blo 1877140 32083289 := bstep (se 2 (by rfl) ⟨12031233, by rfl⟩ : syracuseStep 32083289 = 24062467) B24062467
theorem B6335927 : Blo 1877140 6335927 := bstep (se 1 (by rfl) ⟨4751945, by rfl⟩ : syracuseStep 6335927 = 9503891) B9503891
theorem B11423389 : Blo 1877140 11423389 := bstep (se 3 (by rfl) ⟨2141885, by rfl⟩ : syracuseStep 11423389 = 4283771) B4283771
theorem B31289125 : Blo 1877140 31289125 := bstep (se 4 (by rfl) ⟨2933355, by rfl⟩ : syracuseStep 31289125 = 5866711) B5866711
theorem B39071645 : Blo 1877140 39071645 := bstep (se 3 (by rfl) ⟨7325933, by rfl⟩ : syracuseStep 39071645 = 14651867) B14651867
theorem B27086885 : Blo 1877140 27086885 := bstep (se 4 (by rfl) ⟨2539395, by rfl⟩ : syracuseStep 27086885 = 5078791) B5078791
theorem B3477691 : Blo 1877140 3477691 := bstep (se 1 (by rfl) ⟨2608268, by rfl⟩ : syracuseStep 3477691 = 5216537) B5216537
theorem B7131503 : Blo 1877140 7131503 := bstep (se 1 (by rfl) ⟨5348627, by rfl⟩ : syracuseStep 7131503 = 10697255) B10697255
theorem B5345747 : Blo 1877140 5345747 := bstep (se 1 (by rfl) ⟨4009310, by rfl⟩ : syracuseStep 5345747 = 8018621) B8018621
theorem B12202451 : Blo 1877140 12202451 := bstep (se 1 (by rfl) ⟨9151838, by rfl⟩ : syracuseStep 12202451 = 18303677) B18303677
theorem B13537793 : Blo 1877140 13537793 := bstep (se 2 (by rfl) ⟨5076672, by rfl⟩ : syracuseStep 13537793 = 10153345) B10153345
theorem B4223591 : Blo 1877140 4223591 := bstep (se 1 (by rfl) ⟨3167693, by rfl⟩ : syracuseStep 4223591 = 6335387) B6335387
theorem B13537907 : Blo 1877140 13537907 := bstep (se 1 (by rfl) ⟨10153430, by rfl⟩ : syracuseStep 13537907 = 20306861) B20306861
theorem B48157739 : Blo 1877140 48157739 := bstep (se 1 (by rfl) ⟨36118304, by rfl⟩ : syracuseStep 48157739 = 72236609) B72236609
theorem B4756553 : Blo 1877140 4756553 := bstep (se 2 (by rfl) ⟨1783707, by rfl⟩ : syracuseStep 4756553 = 3567415) B3567415
theorem B16045199 : Blo 1877140 16045199 := bstep (se 1 (by rfl) ⟨12033899, by rfl⟩ : syracuseStep 16045199 = 24067799) B24067799
theorem B5420251 : Blo 1877140 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B4224275 : Blo 1877140 4224275 := bstep (se 1 (by rfl) ⟨3168206, by rfl⟩ : syracuseStep 4224275 = 6336413) B6336413
theorem B27071779 : Blo 1877140 27071779 := bstep (se 1 (by rfl) ⟨20303834, by rfl⟩ : syracuseStep 27071779 = 40607669) B40607669
theorem B4224347 : Blo 1877140 4224347 := bstep (se 1 (by rfl) ⟨3168260, by rfl⟩ : syracuseStep 4224347 = 6336521) B6336521
theorem B36091241 : Blo 1877140 36091241 := bstep (se 2 (by rfl) ⟨13534215, by rfl⟩ : syracuseStep 36091241 = 27068431) B27068431
theorem B6337979 : Blo 1877140 6337979 := bstep (se 1 (by rfl) ⟨4753484, by rfl⟩ : syracuseStep 6337979 = 9506969) B9506969
theorem B3167815 : Blo 1877140 3167815 := bstep (se 1 (by rfl) ⟨2375861, by rfl⟩ : syracuseStep 3167815 = 4751723) B4751723
theorem B6428231 : Blo 1877140 6428231 := bstep (se 1 (by rfl) ⟨4821173, by rfl⟩ : syracuseStep 6428231 = 9642347) B9642347
theorem B2815739 : Blo 1877140 2815739 := bstep (se 1 (by rfl) ⟨2111804, by rfl⟩ : syracuseStep 2815739 = 4223609) B4223609
theorem B2815775 : Blo 1877140 2815775 := bstep (se 1 (by rfl) ⟨2111831, by rfl⟩ : syracuseStep 2815775 = 4223663) B4223663
theorem B3168031 : Blo 1877140 3168031 := bstep (se 1 (by rfl) ⟨2376023, by rfl⟩ : syracuseStep 3168031 = 4752047) B4752047
theorem B4011839 : Blo 1877140 4011839 := bstep (se 1 (by rfl) ⟨3008879, by rfl⟩ : syracuseStep 4011839 = 6017759) B6017759
theorem B2815823 : Blo 1877140 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B4224905 : Blo 1877140 4224905 := bstep (se 2 (by rfl) ⟨1584339, by rfl⟩ : syracuseStep 4224905 = 3168679) B3168679
theorem B18044855 : Blo 1877140 18044855 := bstep (se 1 (by rfl) ⟨13533641, by rfl⟩ : syracuseStep 18044855 = 27067283) B27067283
theorem B2815943 : Blo 1877140 2815943 := bstep (se 1 (by rfl) ⟨2111957, by rfl⟩ : syracuseStep 2815943 = 4223915) B4223915
theorem B6338519 : Blo 1877140 6338519 := bstep (se 1 (by rfl) ⟨4753889, by rfl⟩ : syracuseStep 6338519 = 9507779) B9507779
theorem B7133143 : Blo 1877140 7133143 := bstep (se 1 (by rfl) ⟨5349857, by rfl⟩ : syracuseStep 7133143 = 10699715) B10699715
theorem B15439855 : Blo 1877140 15439855 := bstep (se 1 (by rfl) ⟨11579891, by rfl⟩ : syracuseStep 15439855 = 23159783) B23159783
theorem B3168247 : Blo 1877140 3168247 := bstep (se 1 (by rfl) ⟨2376185, by rfl⟩ : syracuseStep 3168247 = 4752371) B4752371
theorem B4225121 : Blo 1877140 4225121 := bstep (se 2 (by rfl) ⟨1584420, by rfl⟩ : syracuseStep 4225121 = 3168841) B3168841
theorem B5077235 : Blo 1877140 5077235 := bstep (se 1 (by rfl) ⟨3807926, by rfl⟩ : syracuseStep 5077235 = 7615853) B7615853
theorem B81221899 : Blo 1877140 81221899 := bstep (se 1 (by rfl) ⟨60916424, by rfl⟩ : syracuseStep 81221899 = 121832849) B121832849
theorem B3168551 : Blo 1877140 3168551 := bstep (se 1 (by rfl) ⟨2376413, by rfl⟩ : syracuseStep 3168551 = 4752827) B4752827
theorem B2816297 : Blo 1877140 2816297 := bstep (se 2 (by rfl) ⟨1056111, by rfl⟩ : syracuseStep 2816297 = 2112223) B2112223
theorem B8026411 : Blo 1877140 8026411 := bstep (se 1 (by rfl) ⟨6019808, by rfl⟩ : syracuseStep 8026411 = 12039617) B12039617
theorem B2111791 : Blo 1877140 2111791 := bstep (se 1 (by rfl) ⟨1583843, by rfl⟩ : syracuseStep 2111791 = 3167687) B3167687
theorem B2816303 : Blo 1877140 2816303 := bstep (se 1 (by rfl) ⟨2112227, by rfl⟩ : syracuseStep 2816303 = 4224455) B4224455
theorem B17127787 : Blo 1877140 17127787 := bstep (se 1 (by rfl) ⟨12845840, by rfl⟩ : syracuseStep 17127787 = 25691681) B25691681
theorem B4012411 : Blo 1877140 4012411 := bstep (se 1 (by rfl) ⟨3009308, by rfl⟩ : syracuseStep 4012411 = 6018617) B6018617
theorem B7133615 : Blo 1877140 7133615 := bstep (se 1 (by rfl) ⟨5350211, by rfl⟩ : syracuseStep 7133615 = 10700423) B10700423
theorem B6339005 : Blo 1877140 6339005 := bstep (se 3 (by rfl) ⟨1188563, by rfl⟩ : syracuseStep 6339005 = 2377127) B2377127
theorem B7133629 : Blo 1877140 7133629 := bstep (se 3 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 7133629 = 2675111) B2675111
theorem B2816543 : Blo 1877140 2816543 := bstep (se 1 (by rfl) ⟨2112407, by rfl⟩ : syracuseStep 2816543 = 4224815) B4224815
theorem B9509723 : Blo 1877140 9509723 := bstep (se 1 (by rfl) ⟨7132292, by rfl⟩ : syracuseStep 9509723 = 14264585) B14264585
theorem B2816927 : Blo 1877140 2816927 := bstep (se 1 (by rfl) ⟨2112695, by rfl⟩ : syracuseStep 2816927 = 4225391) B4225391
theorem B2816975 : Blo 1877140 2816975 := bstep (se 1 (by rfl) ⟨2112731, by rfl⟩ : syracuseStep 2816975 = 4225463) B4225463
theorem B2817065 : Blo 1877140 2817065 := bstep (se 2 (by rfl) ⟨1056399, by rfl⟩ : syracuseStep 2817065 = 2112799) B2112799
theorem B2817071 : Blo 1877140 2817071 := bstep (se 1 (by rfl) ⟨2112803, by rfl⟩ : syracuseStep 2817071 = 4225607) B4225607
theorem B3169327 : Blo 1877140 3169327 := bstep (se 1 (by rfl) ⟨2376995, by rfl⟩ : syracuseStep 3169327 = 4753991) B4753991
theorem B2112583 : Blo 1877140 2112583 := bstep (se 1 (by rfl) ⟨1584437, by rfl⟩ : syracuseStep 2112583 = 3168875) B3168875
theorem B2817095 : Blo 1877140 2817095 := bstep (se 1 (by rfl) ⟨2112821, by rfl⟩ : syracuseStep 2817095 = 4225643) B4225643
theorem B5348423 : Blo 1877140 5348423 := bstep (se 1 (by rfl) ⟨4011317, by rfl⟩ : syracuseStep 5348423 = 8022635) B8022635
theorem B25705691 : Blo 1877140 25705691 := bstep (se 1 (by rfl) ⟨19279268, by rfl⟩ : syracuseStep 25705691 = 38558537) B38558537
theorem B5348605 : Blo 1877140 5348605 := bstep (se 3 (by rfl) ⟨1002863, by rfl⟩ : syracuseStep 5348605 = 2005727) B2005727
theorem B6339869 : Blo 1877140 6339869 := bstep (se 3 (by rfl) ⟨1188725, by rfl⟩ : syracuseStep 6339869 = 2377451) B2377451
theorem B2817359 : Blo 1877140 2817359 := bstep (se 1 (by rfl) ⟨2113019, by rfl⟩ : syracuseStep 2817359 = 4226039) B4226039
theorem B4226471 : Blo 1877140 4226471 := bstep (se 1 (by rfl) ⟨3169853, by rfl⟩ : syracuseStep 4226471 = 6339707) B6339707
theorem B2817449 : Blo 1877140 2817449 := bstep (se 2 (by rfl) ⟨1056543, by rfl⟩ : syracuseStep 2817449 = 2113087) B2113087
theorem B3169705 : Blo 1877140 3169705 := bstep (se 2 (by rfl) ⟨1188639, by rfl⟩ : syracuseStep 3169705 = 2377279) B2377279
theorem B12844499 : Blo 1877140 12844499 := bstep (se 1 (by rfl) ⟨9633374, by rfl⟩ : syracuseStep 12844499 = 19266749) B19266749
theorem B2817599 : Blo 1877140 2817599 := bstep (se 1 (by rfl) ⟨2113199, by rfl⟩ : syracuseStep 2817599 = 4226399) B4226399
theorem B4226651 : Blo 1877140 4226651 := bstep (se 1 (by rfl) ⟨3169988, by rfl⟩ : syracuseStep 4226651 = 6339977) B6339977
theorem B2817863 : Blo 1877140 2817863 := bstep (se 1 (by rfl) ⟨2113397, by rfl⟩ : syracuseStep 2817863 = 4226795) B4226795
theorem B3170171 : Blo 1877140 3170171 := bstep (se 1 (by rfl) ⟨2377628, by rfl⟩ : syracuseStep 3170171 = 4755257) B4755257
theorem B4226939 : Blo 1877140 4226939 := bstep (se 1 (by rfl) ⟨3170204, by rfl⟩ : syracuseStep 4226939 = 6340409) B6340409
theorem B2817947 : Blo 1877140 2817947 := bstep (se 1 (by rfl) ⟨2113460, by rfl⟩ : syracuseStep 2817947 = 4226921) B4226921
theorem B4227263 : Blo 1877140 4227263 := bstep (se 1 (by rfl) ⟨3170447, by rfl⟩ : syracuseStep 4227263 = 6340895) B6340895
theorem B2818283 : Blo 1877140 2818283 := bstep (se 1 (by rfl) ⟨2113712, by rfl⟩ : syracuseStep 2818283 = 4227425) B4227425
theorem B4636921 : Blo 1877140 4636921 := bstep (se 2 (by rfl) ⟨1738845, by rfl⟩ : syracuseStep 4636921 = 3477691) B3477691
theorem B2818343 : Blo 1877140 2818343 := bstep (se 1 (by rfl) ⟨2113757, by rfl⟩ : syracuseStep 2818343 = 4227515) B4227515
theorem B2375983 : Blo 1877140 2375983 := bstep (se 1 (by rfl) ⟨1781987, by rfl⟩ : syracuseStep 2375983 = 3563975) B3563975
theorem B3563831 : Blo 1877140 3563831 := bstep (se 1 (by rfl) ⟨2672873, by rfl⟩ : syracuseStep 3563831 = 5345747) B5345747
theorem B8134967 : Blo 1877140 8134967 := bstep (se 1 (by rfl) ⟨6101225, by rfl⟩ : syracuseStep 8134967 = 12202451) B12202451
theorem B4751743 : Blo 1877140 4751743 := bstep (se 1 (by rfl) ⟨3563807, by rfl⟩ : syracuseStep 4751743 = 7127615) B7127615
theorem B5349881 : Blo 1877140 5349881 := bstep (se 2 (by rfl) ⟨2006205, by rfl⟩ : syracuseStep 5349881 = 4012411) B4012411
theorem B9511505 : Blo 1877140 9511505 := bstep (se 2 (by rfl) ⟨3566814, by rfl⟩ : syracuseStep 9511505 = 7133629) B7133629
theorem B4227695 : Blo 1877140 4227695 := bstep (se 1 (by rfl) ⟨3170771, by rfl⟩ : syracuseStep 4227695 = 6341543) B6341543
theorem B32105159 : Blo 1877140 32105159 := bstep (se 1 (by rfl) ⟨24078869, by rfl⟩ : syracuseStep 32105159 = 48157739) B48157739
theorem B3171035 : Blo 1877140 3171035 := bstep (se 1 (by rfl) ⟨2378276, by rfl⟩ : syracuseStep 3171035 = 4756553) B4756553
theorem B24060827 : Blo 1877140 24060827 := bstep (se 1 (by rfl) ⟨18045620, by rfl⟩ : syracuseStep 24060827 = 36091241) B36091241
theorem B4285487 : Blo 1877140 4285487 := bstep (se 1 (by rfl) ⟨3214115, by rfl⟩ : syracuseStep 4285487 = 6428231) B6428231
theorem B14451817 : Blo 1877140 14451817 := bstep (se 2 (by rfl) ⟨5419431, by rfl⟩ : syracuseStep 14451817 = 10838863) B10838863
theorem B1877159 : Blo 1877140 1877159 := bstep (se 1 (by rfl) ⟨1407869, by rfl⟩ : syracuseStep 1877159 = 2815739) B2815739
theorem B1877183 : Blo 1877140 1877183 := bstep (se 1 (by rfl) ⟨1407887, by rfl⟩ : syracuseStep 1877183 = 2815775) B2815775
theorem B7128283 : Blo 1877140 7128283 := bstep (se 1 (by rfl) ⟨5346212, by rfl⟩ : syracuseStep 7128283 = 10692425) B10692425
theorem B34251997 : Blo 1877140 34251997 := bstep (se 3 (by rfl) ⟨6422249, by rfl⟩ : syracuseStep 34251997 = 12844499) B12844499
theorem B1877215 : Blo 1877140 1877215 := bstep (se 1 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 1877215 = 2815823) B2815823
theorem B6341867 : Blo 1877140 6341867 := bstep (se 1 (by rfl) ⟨4756400, by rfl⟩ : syracuseStep 6341867 = 9512801) B9512801
theorem B4752665 : Blo 1877140 4752665 := bstep (se 2 (by rfl) ⟨1782249, by rfl⟩ : syracuseStep 4752665 = 3564499) B3564499
theorem B1877295 : Blo 1877140 1877295 := bstep (se 1 (by rfl) ⟨1407971, by rfl⟩ : syracuseStep 1877295 = 2815943) B2815943
theorem B3384823 : Blo 1877140 3384823 := bstep (se 1 (by rfl) ⟨2538617, by rfl⟩ : syracuseStep 3384823 = 5077235) B5077235
theorem B1877531 : Blo 1877140 1877531 := bstep (se 1 (by rfl) ⟨1408148, by rfl⟩ : syracuseStep 1877531 = 2816297) B2816297
theorem B1877535 : Blo 1877140 1877535 := bstep (se 1 (by rfl) ⟨1408151, by rfl⟩ : syracuseStep 1877535 = 2816303) B2816303
theorem B3565129 : Blo 1877140 3565129 := bstep (se 2 (by rfl) ⟨1336923, by rfl⟩ : syracuseStep 3565129 = 2673847) B2673847
theorem B7227001 : Blo 1877140 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B1877695 : Blo 1877140 1877695 := bstep (se 1 (by rfl) ⟨1408271, by rfl⟩ : syracuseStep 1877695 = 2816543) B2816543
theorem B36095705 : Blo 1877140 36095705 := bstep (se 2 (by rfl) ⟨13535889, by rfl⟩ : syracuseStep 36095705 = 27071779) B27071779
theorem B121866065 : Blo 1877140 121866065 := bstep (se 2 (by rfl) ⟨45699774, by rfl⟩ : syracuseStep 121866065 = 91399549) B91399549
theorem B1877951 : Blo 1877140 1877951 := bstep (se 1 (by rfl) ⟨1408463, by rfl⟩ : syracuseStep 1877951 = 2816927) B2816927
theorem B1877983 : Blo 1877140 1877983 := bstep (se 1 (by rfl) ⟨1408487, by rfl⟩ : syracuseStep 1877983 = 2816975) B2816975
theorem B1878043 : Blo 1877140 1878043 := bstep (se 1 (by rfl) ⟨1408532, by rfl⟩ : syracuseStep 1878043 = 2817065) B2817065
theorem B1878047 : Blo 1877140 1878047 := bstep (se 1 (by rfl) ⟨1408535, by rfl⟩ : syracuseStep 1878047 = 2817071) B2817071
theorem B1878063 : Blo 1877140 1878063 := bstep (se 1 (by rfl) ⟨1408547, by rfl⟩ : syracuseStep 1878063 = 2817095) B2817095
theorem B3565615 : Blo 1877140 3565615 := bstep (se 1 (by rfl) ⟨2674211, by rfl⟩ : syracuseStep 3565615 = 5348423) B5348423
theorem B6015131 : Blo 1877140 6015131 := bstep (se 1 (by rfl) ⟨4511348, by rfl⟩ : syracuseStep 6015131 = 9022697) B9022697
theorem B15231185 : Blo 1877140 15231185 := bstep (se 2 (by rfl) ⟨5711694, by rfl⟩ : syracuseStep 15231185 = 11423389) B11423389
theorem B1878239 : Blo 1877140 1878239 := bstep (se 1 (by rfl) ⟨1408679, by rfl⟩ : syracuseStep 1878239 = 2817359) B2817359
theorem B3213535 : Blo 1877140 3213535 := bstep (se 1 (by rfl) ⟨2410151, by rfl⟩ : syracuseStep 3213535 = 4820303) B4820303
theorem B1878299 : Blo 1877140 1878299 := bstep (se 1 (by rfl) ⟨1408724, by rfl⟩ : syracuseStep 1878299 = 2817449) B2817449
theorem B1878399 : Blo 1877140 1878399 := bstep (se 1 (by rfl) ⟨1408799, by rfl⟩ : syracuseStep 1878399 = 2817599) B2817599
theorem B1878575 : Blo 1877140 1878575 := bstep (se 1 (by rfl) ⟨1408931, by rfl⟩ : syracuseStep 1878575 = 2817863) B2817863
theorem B1878631 : Blo 1877140 1878631 := bstep (se 1 (by rfl) ⟨1408973, by rfl⟩ : syracuseStep 1878631 = 2817947) B2817947
theorem B18057923 : Blo 1877140 18057923 := bstep (se 1 (by rfl) ⟨13543442, by rfl⟩ : syracuseStep 18057923 = 27086885) B27086885
theorem B4754335 : Blo 1877140 4754335 := bstep (se 1 (by rfl) ⟨3565751, by rfl⟩ : syracuseStep 4754335 = 7131503) B7131503
theorem B1879007 : Blo 1877140 1879007 := bstep (se 1 (by rfl) ⟨1409255, by rfl⟩ : syracuseStep 1879007 = 2818511) B2818511
theorem B1879035 : Blo 1877140 1879035 := bstep (se 1 (by rfl) ⟨1409276, by rfl⟩ : syracuseStep 1879035 = 2818553) B2818553
theorem B10701881 : Blo 1877140 10701881 := bstep (se 2 (by rfl) ⟨4013205, by rfl⟩ : syracuseStep 10701881 = 8026411) B8026411
theorem B1879103 : Blo 1877140 1879103 := bstep (se 1 (by rfl) ⟨1409327, by rfl⟩ : syracuseStep 1879103 = 2818655) B2818655
theorem B3566663 : Blo 1877140 3566663 := bstep (se 1 (by rfl) ⟨2674997, by rfl⟩ : syracuseStep 3566663 = 5349995) B5349995
theorem B12037385 : Blo 1877140 12037385 := bstep (se 2 (by rfl) ⟨4514019, by rfl⟩ : syracuseStep 12037385 = 9028039) B9028039
theorem B6336143 : Blo 1877140 6336143 := bstep (se 1 (by rfl) ⟨4752107, by rfl⟩ : syracuseStep 6336143 = 9504215) B9504215
theorem B10694339 : Blo 1877140 10694339 := bstep (se 1 (by rfl) ⟨8020754, by rfl⟩ : syracuseStep 10694339 = 16041509) B16041509
theorem B2674559 : Blo 1877140 2674559 := bstep (se 1 (by rfl) ⟨2005919, by rfl⟩ : syracuseStep 2674559 = 4011839) B4011839
theorem B12029903 : Blo 1877140 12029903 := bstep (se 1 (by rfl) ⟨9022427, by rfl⟩ : syracuseStep 12029903 = 18044855) B18044855
theorem B4755743 : Blo 1877140 4755743 := bstep (se 1 (by rfl) ⟨3566807, by rfl⟩ : syracuseStep 4755743 = 7133615) B7133615
theorem B7131473 : Blo 1877140 7131473 := bstep (se 2 (by rfl) ⟨2674302, by rfl⟩ : syracuseStep 7131473 = 5348605) B5348605
theorem B9269747 : Blo 1877140 9269747 := bstep (se 1 (by rfl) ⟨6952310, by rfl⟩ : syracuseStep 9269747 = 13904621) B13904621
theorem B4223753 : Blo 1877140 4223753 := bstep (se 2 (by rfl) ⟨1583907, by rfl⟩ : syracuseStep 4223753 = 3167815) B3167815
theorem B4223807 : Blo 1877140 4223807 := bstep (se 1 (by rfl) ⟨3167855, by rfl⟩ : syracuseStep 4223807 = 6335711) B6335711
theorem B4223951 : Blo 1877140 4223951 := bstep (se 1 (by rfl) ⟨3167963, by rfl⟩ : syracuseStep 4223951 = 6335927) B6335927
theorem B4224041 : Blo 1877140 4224041 := bstep (se 2 (by rfl) ⟨1584015, by rfl⟩ : syracuseStep 4224041 = 3168031) B3168031
theorem B41718833 : Blo 1877140 41718833 := bstep (se 2 (by rfl) ⟨15644562, by rfl⟩ : syracuseStep 41718833 = 31289125) B31289125
theorem B4011113 : Blo 1877140 4011113 := bstep (se 2 (by rfl) ⟨1504167, by rfl⟩ : syracuseStep 4011113 = 3008335) B3008335
theorem B9024641 : Blo 1877140 9024641 := bstep (se 2 (by rfl) ⟨3384240, by rfl⟩ : syracuseStep 9024641 = 6768481) B6768481
theorem B26047763 : Blo 1877140 26047763 := bstep (se 1 (by rfl) ⟨19535822, by rfl⟩ : syracuseStep 26047763 = 39071645) B39071645
theorem B4224329 : Blo 1877140 4224329 := bstep (se 2 (by rfl) ⟨1584123, by rfl⟩ : syracuseStep 4224329 = 3168247) B3168247
theorem B2856431 : Blo 1877140 2856431 := bstep (se 1 (by rfl) ⟨2142323, by rfl⟩ : syracuseStep 2856431 = 4284647) B4284647
theorem B15062537 : Blo 1877140 15062537 := bstep (se 2 (by rfl) ⟨5648451, by rfl⟩ : syracuseStep 15062537 = 11296903) B11296903
theorem B9025195 : Blo 1877140 9025195 := bstep (se 1 (by rfl) ⟨6768896, by rfl⟩ : syracuseStep 9025195 = 13537793) B13537793
theorem B108295865 : Blo 1877140 108295865 := bstep (se 2 (by rfl) ⟨40610949, by rfl⟩ : syracuseStep 108295865 = 81221899) B81221899
theorem B2815721 : Blo 1877140 2815721 := bstep (se 2 (by rfl) ⟨1055895, by rfl⟩ : syracuseStep 2815721 = 2111791) B2111791
theorem B2815727 : Blo 1877140 2815727 := bstep (se 1 (by rfl) ⟨2111795, by rfl⟩ : syracuseStep 2815727 = 4223591) B4223591
theorem B9025271 : Blo 1877140 9025271 := bstep (se 1 (by rfl) ⟨6768953, by rfl⟩ : syracuseStep 9025271 = 13537907) B13537907
theorem B5347079 : Blo 1877140 5347079 := bstep (se 1 (by rfl) ⟨4010309, by rfl⟩ : syracuseStep 5347079 = 8020619) B8020619
theorem B22837049 : Blo 1877140 22837049 := bstep (se 2 (by rfl) ⟨8563893, by rfl⟩ : syracuseStep 22837049 = 17127787) B17127787
theorem B6018887 : Blo 1877140 6018887 := bstep (se 1 (by rfl) ⟨4514165, by rfl⟩ : syracuseStep 6018887 = 9028331) B9028331
theorem B10696799 : Blo 1877140 10696799 := bstep (se 1 (by rfl) ⟨8022599, by rfl⟩ : syracuseStep 10696799 = 16045199) B16045199
theorem B2816183 : Blo 1877140 2816183 := bstep (se 1 (by rfl) ⟨2112137, by rfl⟩ : syracuseStep 2816183 = 4224275) B4224275
theorem B73177283 : Blo 1877140 73177283 := bstep (se 1 (by rfl) ⟨54882962, by rfl⟩ : syracuseStep 73177283 = 109765925) B109765925
theorem B2816231 : Blo 1877140 2816231 := bstep (se 1 (by rfl) ⟨2112173, by rfl⟩ : syracuseStep 2816231 = 4224347) B4224347
theorem B7133417 : Blo 1877140 7133417 := bstep (se 2 (by rfl) ⟨2675031, by rfl⟩ : syracuseStep 7133417 = 5350063) B5350063
theorem B7133447 : Blo 1877140 7133447 := bstep (se 1 (by rfl) ⟨5350085, by rfl⟩ : syracuseStep 7133447 = 10700171) B10700171
theorem B4225319 : Blo 1877140 4225319 := bstep (se 1 (by rfl) ⟨3168989, by rfl⟩ : syracuseStep 4225319 = 6337979) B6337979
theorem B2816603 : Blo 1877140 2816603 := bstep (se 1 (by rfl) ⟨2112452, by rfl⟩ : syracuseStep 2816603 = 4224905) B4224905
theorem B4225679 : Blo 1877140 4225679 := bstep (se 1 (by rfl) ⟨3169259, by rfl⟩ : syracuseStep 4225679 = 6338519) B6338519
theorem B4225769 : Blo 1877140 4225769 := bstep (se 2 (by rfl) ⟨1584663, by rfl⟩ : syracuseStep 4225769 = 3169327) B3169327
theorem B2816747 : Blo 1877140 2816747 := bstep (se 1 (by rfl) ⟨2112560, by rfl⟩ : syracuseStep 2816747 = 4225121) B4225121
theorem B2816777 : Blo 1877140 2816777 := bstep (se 2 (by rfl) ⟨1056291, by rfl⟩ : syracuseStep 2816777 = 2112583) B2112583
theorem B2112367 : Blo 1877140 2112367 := bstep (se 1 (by rfl) ⟨1584275, by rfl⟩ : syracuseStep 2112367 = 3168551) B3168551
theorem B4226003 : Blo 1877140 4226003 := bstep (se 1 (by rfl) ⟨3169502, by rfl⟩ : syracuseStep 4226003 = 6339005) B6339005
theorem B4226273 : Blo 1877140 4226273 := bstep (se 2 (by rfl) ⟨1584852, by rfl⟩ : syracuseStep 4226273 = 3169705) B3169705
theorem B6339815 : Blo 1877140 6339815 := bstep (se 1 (by rfl) ⟨4754861, by rfl⟩ : syracuseStep 6339815 = 9509723) B9509723
theorem B12033467 : Blo 1877140 12033467 := bstep (se 1 (by rfl) ⟨9025100, by rfl⟩ : syracuseStep 12033467 = 18050201) B18050201
theorem B2006479 : Blo 1877140 2006479 := bstep (se 1 (by rfl) ⟨1504859, by rfl⟩ : syracuseStep 2006479 = 3009719) B3009719
theorem B17137127 : Blo 1877140 17137127 := bstep (se 1 (by rfl) ⟨12852845, by rfl⟩ : syracuseStep 17137127 = 25705691) B25705691
theorem B4226579 : Blo 1877140 4226579 := bstep (se 1 (by rfl) ⟨3169934, by rfl⟩ : syracuseStep 4226579 = 6339869) B6339869
theorem B21388859 : Blo 1877140 21388859 := bstep (se 1 (by rfl) ⟨16041644, by rfl⟩ : syracuseStep 21388859 = 32083289) B32083289
theorem B2817647 : Blo 1877140 2817647 := bstep (se 1 (by rfl) ⟨2113235, by rfl⟩ : syracuseStep 2817647 = 4226471) B4226471
theorem B2711161 : Blo 1877140 2711161 := bstep (se 2 (by rfl) ⟨1016685, by rfl⟩ : syracuseStep 2711161 = 2033371) B2033371
theorem B2817767 : Blo 1877140 2817767 := bstep (se 1 (by rfl) ⟨2113325, by rfl⟩ : syracuseStep 2817767 = 4226651) B4226651
theorem B2113447 : Blo 1877140 2113447 := bstep (se 1 (by rfl) ⟨1585085, by rfl⟩ : syracuseStep 2113447 = 3170171) B3170171
theorem B2817959 : Blo 1877140 2817959 := bstep (se 1 (by rfl) ⟨2113469, by rfl⟩ : syracuseStep 2817959 = 4226939) B4226939
theorem B9510857 : Blo 1877140 9510857 := bstep (se 2 (by rfl) ⟨3566571, by rfl⟩ : syracuseStep 9510857 = 7133143) B7133143
theorem B20586473 : Blo 1877140 20586473 := bstep (se 2 (by rfl) ⟨7719927, by rfl⟩ : syracuseStep 20586473 = 15439855) B15439855
theorem B11427965 : Blo 1877140 11427965 := bstep (se 3 (by rfl) ⟨2142743, by rfl⟩ : syracuseStep 11427965 = 4285487) B4285487
theorem B2818175 : Blo 1877140 2818175 := bstep (se 1 (by rfl) ⟨2113631, by rfl⟩ : syracuseStep 2818175 = 4227263) B4227263
theorem B3170495 : Blo 1877140 3170495 := bstep (se 1 (by rfl) ⟨2377871, by rfl⟩ : syracuseStep 3170495 = 4755743) B4755743
theorem B2375887 : Blo 1877140 2375887 := bstep (se 1 (by rfl) ⟨1781915, by rfl⟩ : syracuseStep 2375887 = 3563831) B3563831
theorem B5423311 : Blo 1877140 5423311 := bstep (se 1 (by rfl) ⟨4067483, by rfl⟩ : syracuseStep 5423311 = 8134967) B8134967
theorem B4284713 : Blo 1877140 4284713 := bstep (se 2 (by rfl) ⟨1606767, by rfl⟩ : syracuseStep 4284713 = 3213535) B3213535
theorem B6341003 : Blo 1877140 6341003 := bstep (se 1 (by rfl) ⟨4755752, by rfl⟩ : syracuseStep 6341003 = 9511505) B9511505
theorem B2818463 : Blo 1877140 2818463 := bstep (se 1 (by rfl) ⟨2113847, by rfl⟩ : syracuseStep 2818463 = 4227695) B4227695
theorem B2114023 : Blo 1877140 2114023 := bstep (se 1 (by rfl) ⟨1585517, by rfl⟩ : syracuseStep 2114023 = 3171035) B3171035
theorem B16040551 : Blo 1877140 16040551 := bstep (se 1 (by rfl) ⟨12030413, by rfl⟩ : syracuseStep 16040551 = 24060827) B24060827
theorem B38544005 : Blo 1877140 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B27812555 : Blo 1877140 27812555 := bstep (se 1 (by rfl) ⟨20859416, by rfl⟩ : syracuseStep 27812555 = 41718833) B41718833
theorem B4227911 : Blo 1877140 4227911 := bstep (se 1 (by rfl) ⟨3170933, by rfl⟩ : syracuseStep 4227911 = 6341867) B6341867
theorem B72197243 : Blo 1877140 72197243 := bstep (se 1 (by rfl) ⟨54147932, by rfl⟩ : syracuseStep 72197243 = 108295865) B108295865
theorem B1877147 : Blo 1877140 1877147 := bstep (se 1 (by rfl) ⟨1407860, by rfl⟩ : syracuseStep 1877147 = 2815721) B2815721
theorem B1877151 : Blo 1877140 1877151 := bstep (se 1 (by rfl) ⟨1407863, by rfl⟩ : syracuseStep 1877151 = 2815727) B2815727
theorem B3564719 : Blo 1877140 3564719 := bstep (se 1 (by rfl) ⟨2673539, by rfl⟩ : syracuseStep 3564719 = 5347079) B5347079
theorem B1877455 : Blo 1877140 1877455 := bstep (se 1 (by rfl) ⟨1408091, by rfl⟩ : syracuseStep 1877455 = 2816183) B2816183
theorem B48784855 : Blo 1877140 48784855 := bstep (se 1 (by rfl) ⟨36588641, by rfl⟩ : syracuseStep 48784855 = 73177283) B73177283
theorem B19269089 : Blo 1877140 19269089 := bstep (se 2 (by rfl) ⟨7225908, by rfl⟩ : syracuseStep 19269089 = 14451817) B14451817
theorem B1877487 : Blo 1877140 1877487 := bstep (se 1 (by rfl) ⟨1408115, by rfl⟩ : syracuseStep 1877487 = 2816231) B2816231
theorem B9504377 : Blo 1877140 9504377 := bstep (se 2 (by rfl) ⟨3564141, by rfl⟩ : syracuseStep 9504377 = 7128283) B7128283
theorem B1877735 : Blo 1877140 1877735 := bstep (se 1 (by rfl) ⟨1408301, by rfl⟩ : syracuseStep 1877735 = 2816603) B2816603
theorem B1877831 : Blo 1877140 1877831 := bstep (se 1 (by rfl) ⟨1408373, by rfl⟩ : syracuseStep 1877831 = 2816747) B2816747
theorem B1877851 : Blo 1877140 1877851 := bstep (se 1 (by rfl) ⟨1408388, by rfl⟩ : syracuseStep 1877851 = 2816777) B2816777
theorem B2377775 : Blo 1877140 2377775 := bstep (se 1 (by rfl) ⟨1783331, by rfl⟩ : syracuseStep 2377775 = 3566663) B3566663
theorem B4753505 : Blo 1877140 4753505 := bstep (se 2 (by rfl) ⟨1782564, by rfl⟩ : syracuseStep 4753505 = 3565129) B3565129
theorem B3614881 : Blo 1877140 3614881 := bstep (se 2 (by rfl) ⟨1355580, by rfl⟩ : syracuseStep 3614881 = 2711161) B2711161
theorem B8022311 : Blo 1877140 8022311 := bstep (se 1 (by rfl) ⟨6016733, by rfl⟩ : syracuseStep 8022311 = 12033467) B12033467
theorem B1878431 : Blo 1877140 1878431 := bstep (se 1 (by rfl) ⟨1408823, by rfl⟩ : syracuseStep 1878431 = 2817647) B2817647
theorem B7129559 : Blo 1877140 7129559 := bstep (se 1 (by rfl) ⟨5347169, by rfl⟩ : syracuseStep 7129559 = 10694339) B10694339
theorem B1878511 : Blo 1877140 1878511 := bstep (se 1 (by rfl) ⟨1408883, by rfl⟩ : syracuseStep 1878511 = 2817767) B2817767
theorem B1878639 : Blo 1877140 1878639 := bstep (se 1 (by rfl) ⟨1408979, by rfl⟩ : syracuseStep 1878639 = 2817959) B2817959
theorem B13724315 : Blo 1877140 13724315 := bstep (se 1 (by rfl) ⟨10293236, by rfl⟩ : syracuseStep 13724315 = 20586473) B20586473
theorem B4754153 : Blo 1877140 4754153 := bstep (se 2 (by rfl) ⟨1782807, by rfl⟩ : syracuseStep 4754153 = 3565615) B3565615
theorem B1878855 : Blo 1877140 1878855 := bstep (se 1 (by rfl) ⟨1409141, by rfl⟩ : syracuseStep 1878855 = 2818283) B2818283
theorem B1878895 : Blo 1877140 1878895 := bstep (se 1 (by rfl) ⟨1409171, by rfl⟩ : syracuseStep 1878895 = 2818343) B2818343
theorem B4754315 : Blo 1877140 4754315 := bstep (se 1 (by rfl) ⟨3565736, by rfl⟩ : syracuseStep 4754315 = 7131473) B7131473
theorem B6179831 : Blo 1877140 6179831 := bstep (se 1 (by rfl) ⟨4634873, by rfl⟩ : syracuseStep 6179831 = 9269747) B9269747
theorem B3566587 : Blo 1877140 3566587 := bstep (se 1 (by rfl) ⟨2674940, by rfl⟩ : syracuseStep 3566587 = 5349881) B5349881
theorem B6335657 : Blo 1877140 6335657 := bstep (se 2 (by rfl) ⟨2375871, by rfl⟩ : syracuseStep 6335657 = 4751743) B4751743
theorem B2674075 : Blo 1877140 2674075 := bstep (se 1 (by rfl) ⟨2005556, by rfl⟩ : syracuseStep 2674075 = 4011113) B4011113
theorem B6016427 : Blo 1877140 6016427 := bstep (se 1 (by rfl) ⟨4512320, by rfl⟩ : syracuseStep 6016427 = 9024641) B9024641
theorem B24063803 : Blo 1877140 24063803 := bstep (se 1 (by rfl) ⟨18047852, by rfl⟩ : syracuseStep 24063803 = 36095705) B36095705
theorem B6016847 : Blo 1877140 6016847 := bstep (se 1 (by rfl) ⟨4512635, by rfl⟩ : syracuseStep 6016847 = 9025271) B9025271
theorem B15224699 : Blo 1877140 15224699 := bstep (se 1 (by rfl) ⟨11418524, by rfl⟩ : syracuseStep 15224699 = 22837049) B22837049
theorem B81244043 : Blo 1877140 81244043 := bstep (se 1 (by rfl) ⟨60933032, by rfl⟩ : syracuseStep 81244043 = 121866065) B121866065
theorem B45699005 : Blo 1877140 45699005 := bstep (se 3 (by rfl) ⟨8568563, by rfl⟩ : syracuseStep 45699005 = 17137127) B17137127
theorem B7131199 : Blo 1877140 7131199 := bstep (se 1 (by rfl) ⟨5348399, by rfl⟩ : syracuseStep 7131199 = 10696799) B10696799
theorem B4010087 : Blo 1877140 4010087 := bstep (se 1 (by rfl) ⟨3007565, by rfl⟩ : syracuseStep 4010087 = 6015131) B6015131
theorem B10154123 : Blo 1877140 10154123 := bstep (se 1 (by rfl) ⟨7615592, by rfl⟩ : syracuseStep 10154123 = 15231185) B15231185
theorem B4755611 : Blo 1877140 4755611 := bstep (se 1 (by rfl) ⟨3566708, by rfl⟩ : syracuseStep 4755611 = 7133417) B7133417
theorem B4755631 : Blo 1877140 4755631 := bstep (se 1 (by rfl) ⟨3566723, by rfl⟩ : syracuseStep 4755631 = 7133447) B7133447
theorem B12038615 : Blo 1877140 12038615 := bstep (se 1 (by rfl) ⟨9028961, by rfl⟩ : syracuseStep 12038615 = 18057923) B18057923
theorem B2675305 : Blo 1877140 2675305 := bstep (se 2 (by rfl) ⟨1003239, by rfl⟩ : syracuseStep 2675305 = 2006479) B2006479
theorem B8024923 : Blo 1877140 8024923 := bstep (se 1 (by rfl) ⟨6018692, by rfl⟩ : syracuseStep 8024923 = 12037385) B12037385
theorem B7132157 : Blo 1877140 7132157 := bstep (se 3 (by rfl) ⟨1337279, by rfl⟩ : syracuseStep 7132157 = 2674559) B2674559
theorem B14259239 : Blo 1877140 14259239 := bstep (se 1 (by rfl) ⟨10694429, by rfl⟩ : syracuseStep 14259239 = 21388859) B21388859
theorem B4224095 : Blo 1877140 4224095 := bstep (se 1 (by rfl) ⟨3168071, by rfl⟩ : syracuseStep 4224095 = 6336143) B6336143
theorem B6182561 : Blo 1877140 6182561 := bstep (se 2 (by rfl) ⟨2318460, by rfl⟩ : syracuseStep 6182561 = 4636921) B4636921
theorem B3167977 : Blo 1877140 3167977 := bstep (se 2 (by rfl) ⟨1187991, by rfl⟩ : syracuseStep 3167977 = 2375983) B2375983
theorem B21403439 : Blo 1877140 21403439 := bstep (se 1 (by rfl) ⟨16052579, by rfl⟩ : syracuseStep 21403439 = 32105159) B32105159
theorem B2815835 : Blo 1877140 2815835 := bstep (se 1 (by rfl) ⟨2111876, by rfl⟩ : syracuseStep 2815835 = 4223753) B4223753
theorem B2815871 : Blo 1877140 2815871 := bstep (se 1 (by rfl) ⟨2111903, by rfl⟩ : syracuseStep 2815871 = 4223807) B4223807
theorem B2815967 : Blo 1877140 2815967 := bstep (se 1 (by rfl) ⟨2111975, by rfl⟩ : syracuseStep 2815967 = 4223951) B4223951
theorem B2816027 : Blo 1877140 2816027 := bstep (se 1 (by rfl) ⟨2112020, by rfl⟩ : syracuseStep 2816027 = 4224041) B4224041
theorem B17365175 : Blo 1877140 17365175 := bstep (se 1 (by rfl) ⟨13023881, by rfl⟩ : syracuseStep 17365175 = 26047763) B26047763
theorem B3168443 : Blo 1877140 3168443 := bstep (se 1 (by rfl) ⟨2376332, by rfl⟩ : syracuseStep 3168443 = 4752665) B4752665
theorem B2816219 : Blo 1877140 2816219 := bstep (se 1 (by rfl) ⟨2112164, by rfl⟩ : syracuseStep 2816219 = 4224329) B4224329
theorem B10041691 : Blo 1877140 10041691 := bstep (se 1 (by rfl) ⟨7531268, by rfl⟩ : syracuseStep 10041691 = 15062537) B15062537
theorem B2816489 : Blo 1877140 2816489 := bstep (se 2 (by rfl) ⟨1056183, by rfl⟩ : syracuseStep 2816489 = 2112367) B2112367
theorem B6339113 : Blo 1877140 6339113 := bstep (se 2 (by rfl) ⟨2377167, by rfl⟩ : syracuseStep 6339113 = 4754335) B4754335
theorem B4012591 : Blo 1877140 4012591 := bstep (se 1 (by rfl) ⟨3009443, by rfl⟩ : syracuseStep 4012591 = 6018887) B6018887
theorem B7617149 : Blo 1877140 7617149 := bstep (se 3 (by rfl) ⟨1428215, by rfl⟩ : syracuseStep 7617149 = 2856431) B2856431
theorem B2816879 : Blo 1877140 2816879 := bstep (se 1 (by rfl) ⟨2112659, by rfl⟩ : syracuseStep 2816879 = 4225319) B4225319
theorem B45669329 : Blo 1877140 45669329 := bstep (se 2 (by rfl) ⟨17125998, by rfl⟩ : syracuseStep 45669329 = 34251997) B34251997
theorem B2817119 : Blo 1877140 2817119 := bstep (se 1 (by rfl) ⟨2112839, by rfl⟩ : syracuseStep 2817119 = 4225679) B4225679
theorem B2817179 : Blo 1877140 2817179 := bstep (se 1 (by rfl) ⟨2112884, by rfl⟩ : syracuseStep 2817179 = 4225769) B4225769
theorem B2817335 : Blo 1877140 2817335 := bstep (se 1 (by rfl) ⟨2113001, by rfl⟩ : syracuseStep 2817335 = 4226003) B4226003
theorem B4513097 : Blo 1877140 4513097 := bstep (se 2 (by rfl) ⟨1692411, by rfl⟩ : syracuseStep 4513097 = 3384823) B3384823
theorem B7134587 : Blo 1877140 7134587 := bstep (se 1 (by rfl) ⟨5350940, by rfl⟩ : syracuseStep 7134587 = 10701881) B10701881
theorem B2817515 : Blo 1877140 2817515 := bstep (se 1 (by rfl) ⟨2113136, by rfl⟩ : syracuseStep 2817515 = 4226273) B4226273
theorem B4226543 : Blo 1877140 4226543 := bstep (se 1 (by rfl) ⟨3169907, by rfl⟩ : syracuseStep 4226543 = 6339815) B6339815
theorem B12033593 : Blo 1877140 12033593 := bstep (se 2 (by rfl) ⟨4512597, by rfl⟩ : syracuseStep 12033593 = 9025195) B9025195
theorem B2817719 : Blo 1877140 2817719 := bstep (se 1 (by rfl) ⟨2113289, by rfl⟩ : syracuseStep 2817719 = 4226579) B4226579
theorem B2817929 : Blo 1877140 2817929 := bstep (se 2 (by rfl) ⟨1056723, by rfl⟩ : syracuseStep 2817929 = 2113447) B2113447
theorem B6340571 : Blo 1877140 6340571 := bstep (se 1 (by rfl) ⟨4755428, by rfl⟩ : syracuseStep 6340571 = 9510857) B9510857
theorem B8019935 : Blo 1877140 8019935 := bstep (se 1 (by rfl) ⟨6014951, by rfl⟩ : syracuseStep 8019935 = 12029903) B12029903
theorem B7618643 : Blo 1877140 7618643 := bstep (se 1 (by rfl) ⟨5713982, by rfl⟩ : syracuseStep 7618643 = 11427965) B11427965
theorem B3170407 : Blo 1877140 3170407 := bstep (se 1 (by rfl) ⟨2377805, by rfl⟩ : syracuseStep 3170407 = 4755611) B4755611
theorem B6340733 : Blo 1877140 6340733 := bstep (se 3 (by rfl) ⟨1188887, by rfl⟩ : syracuseStep 6340733 = 2377775) B2377775
theorem B2113663 : Blo 1877140 2113663 := bstep (se 1 (by rfl) ⟨1585247, by rfl⟩ : syracuseStep 2113663 = 3170495) B3170495
theorem B6340841 : Blo 1877140 6340841 := bstep (se 2 (by rfl) ⟨2377815, by rfl⟩ : syracuseStep 6340841 = 4755631) B4755631
theorem B4227335 : Blo 1877140 4227335 := bstep (se 1 (by rfl) ⟨3170501, by rfl⟩ : syracuseStep 4227335 = 6341003) B6341003
theorem B2818607 : Blo 1877140 2818607 := bstep (se 1 (by rfl) ⟨2113955, by rfl⟩ : syracuseStep 2818607 = 4227911) B4227911
theorem B2818697 : Blo 1877140 2818697 := bstep (se 2 (by rfl) ⟨1057011, by rfl⟩ : syracuseStep 2818697 = 2114023) B2114023
theorem B5350121 : Blo 1877140 5350121 := bstep (se 2 (by rfl) ⟨2006295, by rfl⟩ : syracuseStep 5350121 = 4012591) B4012591
theorem B2376479 : Blo 1877140 2376479 := bstep (se 1 (by rfl) ⟨1782359, by rfl⟩ : syracuseStep 2376479 = 3564719) B3564719
theorem B12034925 : Blo 1877140 12034925 := bstep (se 3 (by rfl) ⟨2256548, by rfl⟩ : syracuseStep 12034925 = 4513097) B4513097
theorem B12846059 : Blo 1877140 12846059 := bstep (se 1 (by rfl) ⟨9634544, by rfl⟩ : syracuseStep 12846059 = 19269089) B19269089
theorem B4121707 : Blo 1877140 4121707 := bstep (se 1 (by rfl) ⟨3091280, by rfl⟩ : syracuseStep 4121707 = 6182561) B6182561
theorem B10699897 : Blo 1877140 10699897 := bstep (se 2 (by rfl) ⟨4012461, by rfl⟩ : syracuseStep 10699897 = 8024923) B8024923
theorem B1877223 : Blo 1877140 1877223 := bstep (se 1 (by rfl) ⟨1407917, by rfl⟩ : syracuseStep 1877223 = 2815835) B2815835
theorem B1877247 : Blo 1877140 1877247 := bstep (se 1 (by rfl) ⟨1407935, by rfl⟩ : syracuseStep 1877247 = 2815871) B2815871
theorem B1877311 : Blo 1877140 1877311 := bstep (se 1 (by rfl) ⟨1407983, by rfl⟩ : syracuseStep 1877311 = 2815967) B2815967
theorem B1877351 : Blo 1877140 1877351 := bstep (se 1 (by rfl) ⟨1408013, by rfl⟩ : syracuseStep 1877351 = 2816027) B2816027
theorem B11576783 : Blo 1877140 11576783 := bstep (se 1 (by rfl) ⟨8682587, by rfl⟩ : syracuseStep 11576783 = 17365175) B17365175
theorem B1877479 : Blo 1877140 1877479 := bstep (se 1 (by rfl) ⟨1408109, by rfl⟩ : syracuseStep 1877479 = 2816219) B2816219
theorem B4753039 : Blo 1877140 4753039 := bstep (se 1 (by rfl) ⟨3564779, by rfl⟩ : syracuseStep 4753039 = 7129559) B7129559
theorem B1877659 : Blo 1877140 1877659 := bstep (se 1 (by rfl) ⟨1408244, by rfl⟩ : syracuseStep 1877659 = 2816489) B2816489
theorem B3565433 : Blo 1877140 3565433 := bstep (se 2 (by rfl) ⟨1337037, by rfl⟩ : syracuseStep 3565433 = 2674075) B2674075
theorem B1877919 : Blo 1877140 1877919 := bstep (se 1 (by rfl) ⟨1408439, by rfl⟩ : syracuseStep 1877919 = 2816879) B2816879
theorem B65046473 : Blo 1877140 65046473 := bstep (se 2 (by rfl) ⟨24392427, by rfl⟩ : syracuseStep 65046473 = 48784855) B48784855
theorem B1878079 : Blo 1877140 1878079 := bstep (se 1 (by rfl) ⟨1408559, by rfl⟩ : syracuseStep 1878079 = 2817119) B2817119
theorem B1878119 : Blo 1877140 1878119 := bstep (se 1 (by rfl) ⟨1408589, by rfl⟩ : syracuseStep 1878119 = 2817179) B2817179
theorem B1878223 : Blo 1877140 1878223 := bstep (se 1 (by rfl) ⟨1408667, by rfl⟩ : syracuseStep 1878223 = 2817335) B2817335
theorem B1878343 : Blo 1877140 1878343 := bstep (se 1 (by rfl) ⟨1408757, by rfl⟩ : syracuseStep 1878343 = 2817515) B2817515
theorem B8022395 : Blo 1877140 8022395 := bstep (se 1 (by rfl) ⟨6016796, by rfl⟩ : syracuseStep 8022395 = 12033593) B12033593
theorem B1878479 : Blo 1877140 1878479 := bstep (se 1 (by rfl) ⟨1408859, by rfl⟩ : syracuseStep 1878479 = 2817719) B2817719
theorem B16042535 : Blo 1877140 16042535 := bstep (se 1 (by rfl) ⟨12031901, by rfl⟩ : syracuseStep 16042535 = 24063803) B24063803
theorem B1878619 : Blo 1877140 1878619 := bstep (se 1 (by rfl) ⟨1408964, by rfl⟩ : syracuseStep 1878619 = 2817929) B2817929
theorem B1878783 : Blo 1877140 1878783 := bstep (se 1 (by rfl) ⟨1409087, by rfl⟩ : syracuseStep 1878783 = 2818175) B2818175
theorem B6769415 : Blo 1877140 6769415 := bstep (se 1 (by rfl) ⟨5077061, by rfl⟩ : syracuseStep 6769415 = 10154123) B10154123
theorem B4819841 : Blo 1877140 4819841 := bstep (se 2 (by rfl) ⟨1807440, by rfl⟩ : syracuseStep 4819841 = 3614881) B3614881
theorem B10693565 : Blo 1877140 10693565 := bstep (se 3 (by rfl) ⟨2005043, by rfl⟩ : syracuseStep 10693565 = 4010087) B4010087
theorem B1878975 : Blo 1877140 1878975 := bstep (se 1 (by rfl) ⟨1409231, by rfl⟩ : syracuseStep 1878975 = 2818463) B2818463
theorem B13388921 : Blo 1877140 13388921 := bstep (se 2 (by rfl) ⟨5020845, by rfl⟩ : syracuseStep 13388921 = 10041691) B10041691
theorem B18541703 : Blo 1877140 18541703 := bstep (se 1 (by rfl) ⟨13906277, by rfl⟩ : syracuseStep 18541703 = 27812555) B27812555
theorem B4754771 : Blo 1877140 4754771 := bstep (se 1 (by rfl) ⟨3566078, by rfl⟩ : syracuseStep 4754771 = 7132157) B7132157
theorem B9506159 : Blo 1877140 9506159 := bstep (se 1 (by rfl) ⟨7129619, by rfl⟩ : syracuseStep 9506159 = 14259239) B14259239
theorem B48131495 : Blo 1877140 48131495 := bstep (se 1 (by rfl) ⟨36098621, by rfl⟩ : syracuseStep 48131495 = 72197243) B72197243
theorem B3567073 : Blo 1877140 3567073 := bstep (se 2 (by rfl) ⟨1337652, by rfl⟩ : syracuseStep 3567073 = 2675305) B2675305
theorem B6336251 : Blo 1877140 6336251 := bstep (se 1 (by rfl) ⟨4752188, by rfl⟩ : syracuseStep 6336251 = 9504377) B9504377
theorem B4755449 : Blo 1877140 4755449 := bstep (se 2 (by rfl) ⟨1783293, by rfl⟩ : syracuseStep 4755449 = 3566587) B3566587
theorem B30446219 : Blo 1877140 30446219 := bstep (se 1 (by rfl) ⟨22834664, by rfl⟩ : syracuseStep 30446219 = 45669329) B45669329
theorem B4223771 : Blo 1877140 4223771 := bstep (se 1 (by rfl) ⟨3167828, by rfl⟩ : syracuseStep 4223771 = 6335657) B6335657
theorem B16044925 : Blo 1877140 16044925 := bstep (se 3 (by rfl) ⟨3008423, by rfl⟩ : syracuseStep 16044925 = 6016847) B6016847
theorem B4756391 : Blo 1877140 4756391 := bstep (se 1 (by rfl) ⟨3567293, by rfl⟩ : syracuseStep 4756391 = 7134587) B7134587
theorem B4010951 : Blo 1877140 4010951 := bstep (se 1 (by rfl) ⟨3008213, by rfl⟩ : syracuseStep 4010951 = 6016427) B6016427
theorem B4223969 : Blo 1877140 4223969 := bstep (se 2 (by rfl) ⟨1583988, by rfl⟩ : syracuseStep 4223969 = 3167977) B3167977
theorem B54162695 : Blo 1877140 54162695 := bstep (se 1 (by rfl) ⟨40622021, by rfl⟩ : syracuseStep 54162695 = 81244043) B81244043
theorem B5346623 : Blo 1877140 5346623 := bstep (se 1 (by rfl) ⟨4009967, by rfl⟩ : syracuseStep 5346623 = 8019935) B8019935
theorem B9508265 : Blo 1877140 9508265 := bstep (se 2 (by rfl) ⟨3565599, by rfl⟩ : syracuseStep 9508265 = 7131199) B7131199
theorem B2856475 : Blo 1877140 2856475 := bstep (se 1 (by rfl) ⟨2142356, by rfl⟩ : syracuseStep 2856475 = 4284713) B4284713
theorem B3167849 : Blo 1877140 3167849 := bstep (se 2 (by rfl) ⟨1187943, by rfl⟩ : syracuseStep 3167849 = 2375887) B2375887
theorem B7231081 : Blo 1877140 7231081 := bstep (se 2 (by rfl) ⟨2711655, by rfl⟩ : syracuseStep 7231081 = 5423311) B5423311
theorem B8025743 : Blo 1877140 8025743 := bstep (se 1 (by rfl) ⟨6019307, by rfl⟩ : syracuseStep 8025743 = 12038615) B12038615
theorem B25696003 : Blo 1877140 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B2816063 : Blo 1877140 2816063 := bstep (se 1 (by rfl) ⟨2112047, by rfl⟩ : syracuseStep 2816063 = 4224095) B4224095
theorem B21387401 : Blo 1877140 21387401 := bstep (se 2 (by rfl) ⟨8020275, by rfl⟩ : syracuseStep 21387401 = 16040551) B16040551
theorem B14268959 : Blo 1877140 14268959 := bstep (se 1 (by rfl) ⟨10701719, by rfl⟩ : syracuseStep 14268959 = 21403439) B21403439
theorem B3169003 : Blo 1877140 3169003 := bstep (se 1 (by rfl) ⟨2376752, by rfl⟩ : syracuseStep 3169003 = 4753505) B4753505
theorem B2112295 : Blo 1877140 2112295 := bstep (se 1 (by rfl) ⟨1584221, by rfl⟩ : syracuseStep 2112295 = 3168443) B3168443
theorem B5348207 : Blo 1877140 5348207 := bstep (se 1 (by rfl) ⟨4011155, by rfl⟩ : syracuseStep 5348207 = 8022311) B8022311
theorem B4226075 : Blo 1877140 4226075 := bstep (se 1 (by rfl) ⟨3169556, by rfl⟩ : syracuseStep 4226075 = 6339113) B6339113
theorem B5078099 : Blo 1877140 5078099 := bstep (se 1 (by rfl) ⟨3808574, by rfl⟩ : syracuseStep 5078099 = 7617149) B7617149
theorem B9149543 : Blo 1877140 9149543 := bstep (se 1 (by rfl) ⟨6862157, by rfl⟩ : syracuseStep 9149543 = 13724315) B13724315
theorem B3169435 : Blo 1877140 3169435 := bstep (se 1 (by rfl) ⟨2377076, by rfl⟩ : syracuseStep 3169435 = 4754153) B4754153
theorem B3169543 : Blo 1877140 3169543 := bstep (se 1 (by rfl) ⟨2377157, by rfl⟩ : syracuseStep 3169543 = 4754315) B4754315
theorem B4119887 : Blo 1877140 4119887 := bstep (se 1 (by rfl) ⟨3089915, by rfl⟩ : syracuseStep 4119887 = 6179831) B6179831
theorem B2817695 : Blo 1877140 2817695 := bstep (se 1 (by rfl) ⟨2113271, by rfl⟩ : syracuseStep 2817695 = 4226543) B4226543
theorem B10149799 : Blo 1877140 10149799 := bstep (se 1 (by rfl) ⟨7612349, by rfl⟩ : syracuseStep 10149799 = 15224699) B15224699
theorem B30466003 : Blo 1877140 30466003 := bstep (se 1 (by rfl) ⟨22849502, by rfl⟩ : syracuseStep 30466003 = 45699005) B45699005
theorem B4227047 : Blo 1877140 4227047 := bstep (se 1 (by rfl) ⟨3170285, by rfl⟩ : syracuseStep 4227047 = 6340571) B6340571
theorem B5079095 : Blo 1877140 5079095 := bstep (se 1 (by rfl) ⟨3809321, by rfl⟩ : syracuseStep 5079095 = 7618643) B7618643
theorem B4227155 : Blo 1877140 4227155 := bstep (se 1 (by rfl) ⟨3170366, by rfl⟩ : syracuseStep 4227155 = 6340733) B6340733
theorem B4227209 : Blo 1877140 4227209 := bstep (se 2 (by rfl) ⟨1585203, by rfl⟩ : syracuseStep 4227209 = 3170407) B3170407
theorem B4227227 : Blo 1877140 4227227 := bstep (se 1 (by rfl) ⟨3170420, by rfl⟩ : syracuseStep 4227227 = 6340841) B6340841
theorem B2818217 : Blo 1877140 2818217 := bstep (se 2 (by rfl) ⟨1056831, by rfl⟩ : syracuseStep 2818217 = 2113663) B2113663
theorem B2818223 : Blo 1877140 2818223 := bstep (se 1 (by rfl) ⟨2113667, by rfl⟩ : syracuseStep 2818223 = 4227335) B4227335
theorem B13541597 : Blo 1877140 13541597 := bstep (se 3 (by rfl) ⟨2539049, by rfl⟩ : syracuseStep 13541597 = 5078099) B5078099
theorem B3170927 : Blo 1877140 3170927 := bstep (se 1 (by rfl) ⟨2378195, by rfl⟩ : syracuseStep 3170927 = 4756391) B4756391
theorem B3170299 : Blo 1877140 3170299 := bstep (se 1 (by rfl) ⟨2377724, by rfl⟩ : syracuseStep 3170299 = 4755449) B4755449
theorem B3564415 : Blo 1877140 3564415 := bstep (se 1 (by rfl) ⟨2673311, by rfl⟩ : syracuseStep 3564415 = 5346623) B5346623
theorem B7717855 : Blo 1877140 7717855 := bstep (se 1 (by rfl) ⟨5788391, by rfl⟩ : syracuseStep 7717855 = 11576783) B11576783
theorem B2376955 : Blo 1877140 2376955 := bstep (se 1 (by rfl) ⟨1782716, by rfl⟩ : syracuseStep 2376955 = 3565433) B3565433
theorem B1877375 : Blo 1877140 1877375 := bstep (se 1 (by rfl) ⟨1408031, by rfl⟩ : syracuseStep 1877375 = 2816063) B2816063
theorem B9512639 : Blo 1877140 9512639 := bstep (se 1 (by rfl) ⟨7134479, by rfl⟩ : syracuseStep 9512639 = 14268959) B14268959
theorem B3565471 : Blo 1877140 3565471 := bstep (se 1 (by rfl) ⟨2674103, by rfl⟩ : syracuseStep 3565471 = 5348207) B5348207
theorem B3213227 : Blo 1877140 3213227 := bstep (se 1 (by rfl) ⟨2409920, by rfl⟩ : syracuseStep 3213227 = 4819841) B4819841
theorem B7129043 : Blo 1877140 7129043 := bstep (se 1 (by rfl) ⟨5346782, by rfl⟩ : syracuseStep 7129043 = 10693565) B10693565
theorem B2746591 : Blo 1877140 2746591 := bstep (se 1 (by rfl) ⟨2059943, by rfl⟩ : syracuseStep 2746591 = 4119887) B4119887
theorem B34261337 : Blo 1877140 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B1878463 : Blo 1877140 1878463 := bstep (se 1 (by rfl) ⟨1408847, by rfl⟩ : syracuseStep 1878463 = 2817695) B2817695
theorem B1879071 : Blo 1877140 1879071 := bstep (se 1 (by rfl) ⟨1409303, by rfl⟩ : syracuseStep 1879071 = 2818607) B2818607
theorem B1879131 : Blo 1877140 1879131 := bstep (se 1 (by rfl) ⟨1409348, by rfl⟩ : syracuseStep 1879131 = 2818697) B2818697
theorem B3566747 : Blo 1877140 3566747 := bstep (se 1 (by rfl) ⟨2675060, by rfl⟩ : syracuseStep 3566747 = 5350121) B5350121
theorem B8023283 : Blo 1877140 8023283 := bstep (se 1 (by rfl) ⟨6017462, by rfl⟩ : syracuseStep 8023283 = 12034925) B12034925
theorem B2673967 : Blo 1877140 2673967 := bstep (se 1 (by rfl) ⟨2005475, by rfl⟩ : syracuseStep 2673967 = 4010951) B4010951
theorem B8564039 : Blo 1877140 8564039 := bstep (se 1 (by rfl) ⟨6423029, by rfl⟩ : syracuseStep 8564039 = 12846059) B12846059
theorem B21393233 : Blo 1877140 21393233 := bstep (se 2 (by rfl) ⟨8022462, by rfl⟩ : syracuseStep 21393233 = 16044925) B16044925
theorem B43364315 : Blo 1877140 43364315 := bstep (se 1 (by rfl) ⟨32523236, by rfl⟩ : syracuseStep 43364315 = 65046473) B65046473
theorem B14258267 : Blo 1877140 14258267 := bstep (se 1 (by rfl) ⟨10693700, by rfl⟩ : syracuseStep 14258267 = 21387401) B21387401
theorem B14266529 : Blo 1877140 14266529 := bstep (se 2 (by rfl) ⟨5349948, by rfl⟩ : syracuseStep 14266529 = 10699897) B10699897
theorem B10695023 : Blo 1877140 10695023 := bstep (se 1 (by rfl) ⟨8021267, by rfl⟩ : syracuseStep 10695023 = 16042535) B16042535
theorem B21401981 : Blo 1877140 21401981 := bstep (se 3 (by rfl) ⟨4012871, by rfl⟩ : syracuseStep 21401981 = 8025743) B8025743
theorem B4756097 : Blo 1877140 4756097 := bstep (se 2 (by rfl) ⟨1783536, by rfl⟩ : syracuseStep 4756097 = 3567073) B3567073
theorem B6099695 : Blo 1877140 6099695 := bstep (se 1 (by rfl) ⟨4574771, by rfl⟩ : syracuseStep 6099695 = 9149543) B9149543
theorem B8925947 : Blo 1877140 8925947 := bstep (se 1 (by rfl) ⟨6694460, by rfl⟩ : syracuseStep 8925947 = 13388921) B13388921
theorem B6337277 : Blo 1877140 6337277 := bstep (se 3 (by rfl) ⟨1188239, by rfl⟩ : syracuseStep 6337277 = 2376479) B2376479
theorem B6337385 : Blo 1877140 6337385 := bstep (se 2 (by rfl) ⟨2376519, by rfl⟩ : syracuseStep 6337385 = 4753039) B4753039
theorem B6337439 : Blo 1877140 6337439 := bstep (se 1 (by rfl) ⟨4753079, by rfl⟩ : syracuseStep 6337439 = 9506159) B9506159
theorem B4224167 : Blo 1877140 4224167 := bstep (se 1 (by rfl) ⟨3168125, by rfl⟩ : syracuseStep 4224167 = 6336251) B6336251
theorem B40621337 : Blo 1877140 40621337 := bstep (se 2 (by rfl) ⟨15233001, by rfl⟩ : syracuseStep 40621337 = 30466003) B30466003
theorem B20297479 : Blo 1877140 20297479 := bstep (se 1 (by rfl) ⟨15223109, by rfl⟩ : syracuseStep 20297479 = 30446219) B30446219
theorem B2815847 : Blo 1877140 2815847 := bstep (se 1 (by rfl) ⟨2111885, by rfl⟩ : syracuseStep 2815847 = 4223771) B4223771
theorem B2815979 : Blo 1877140 2815979 := bstep (se 1 (by rfl) ⟨2111984, by rfl⟩ : syracuseStep 2815979 = 4223969) B4223969
theorem B36108463 : Blo 1877140 36108463 := bstep (se 1 (by rfl) ⟨27081347, by rfl⟩ : syracuseStep 36108463 = 54162695) B54162695
theorem B6338843 : Blo 1877140 6338843 := bstep (se 1 (by rfl) ⟨4754132, by rfl⟩ : syracuseStep 6338843 = 9508265) B9508265
theorem B4225337 : Blo 1877140 4225337 := bstep (se 2 (by rfl) ⟨1584501, by rfl⟩ : syracuseStep 4225337 = 3169003) B3169003
theorem B2816393 : Blo 1877140 2816393 := bstep (se 2 (by rfl) ⟨1056147, by rfl⟩ : syracuseStep 2816393 = 2112295) B2112295
theorem B2111899 : Blo 1877140 2111899 := bstep (se 1 (by rfl) ⟨1583924, by rfl⟩ : syracuseStep 2111899 = 3167849) B3167849
theorem B5495609 : Blo 1877140 5495609 := bstep (se 2 (by rfl) ⟨2060853, by rfl⟩ : syracuseStep 5495609 = 4121707) B4121707
theorem B4225913 : Blo 1877140 4225913 := bstep (se 2 (by rfl) ⟨1584717, by rfl⟩ : syracuseStep 4225913 = 3169435) B3169435
theorem B5348263 : Blo 1877140 5348263 := bstep (se 1 (by rfl) ⟨4011197, by rfl⟩ : syracuseStep 5348263 = 8022395) B8022395
theorem B4226057 : Blo 1877140 4226057 := bstep (se 2 (by rfl) ⟨1584771, by rfl⟩ : syracuseStep 4226057 = 3169543) B3169543
theorem B4512943 : Blo 1877140 4512943 := bstep (se 1 (by rfl) ⟨3384707, by rfl⟩ : syracuseStep 4512943 = 6769415) B6769415
theorem B2817383 : Blo 1877140 2817383 := bstep (se 1 (by rfl) ⟨2113037, by rfl⟩ : syracuseStep 2817383 = 4226075) B4226075
theorem B3808633 : Blo 1877140 3808633 := bstep (se 2 (by rfl) ⟨1428237, by rfl⟩ : syracuseStep 3808633 = 2856475) B2856475
theorem B12361135 : Blo 1877140 12361135 := bstep (se 1 (by rfl) ⟨9270851, by rfl⟩ : syracuseStep 12361135 = 18541703) B18541703
theorem B9641441 : Blo 1877140 9641441 := bstep (se 2 (by rfl) ⟨3615540, by rfl⟩ : syracuseStep 9641441 = 7231081) B7231081
theorem B3169847 : Blo 1877140 3169847 := bstep (se 1 (by rfl) ⟨2377385, by rfl⟩ : syracuseStep 3169847 = 4754771) B4754771
theorem B32087663 : Blo 1877140 32087663 := bstep (se 1 (by rfl) ⟨24065747, by rfl⟩ : syracuseStep 32087663 = 48131495) B48131495
theorem B13533065 : Blo 1877140 13533065 := bstep (se 2 (by rfl) ⟨5074899, by rfl⟩ : syracuseStep 13533065 = 10149799) B10149799
theorem B2818031 : Blo 1877140 2818031 := bstep (se 1 (by rfl) ⟨2113523, by rfl⟩ : syracuseStep 2818031 = 4227047) B4227047
theorem B2818103 : Blo 1877140 2818103 := bstep (se 1 (by rfl) ⟨2113577, by rfl⟩ : syracuseStep 2818103 = 4227155) B4227155
theorem B2818139 : Blo 1877140 2818139 := bstep (se 1 (by rfl) ⟨2113604, by rfl⟩ : syracuseStep 2818139 = 4227209) B4227209
theorem B2818151 : Blo 1877140 2818151 := bstep (se 1 (by rfl) ⟨2113613, by rfl⟩ : syracuseStep 2818151 = 4227227) B4227227
theorem B9511019 : Blo 1877140 9511019 := bstep (se 1 (by rfl) ⟨7133264, by rfl⟩ : syracuseStep 9511019 = 14266529) B14266529
theorem B9027731 : Blo 1877140 9027731 := bstep (se 1 (by rfl) ⟨6770798, by rfl⟩ : syracuseStep 9027731 = 13541597) B13541597
theorem B48144617 : Blo 1877140 48144617 := bstep (se 2 (by rfl) ⟨18054231, by rfl⟩ : syracuseStep 48144617 = 36108463) B36108463
theorem B2113951 : Blo 1877140 2113951 := bstep (se 1 (by rfl) ⟨1585463, by rfl⟩ : syracuseStep 2113951 = 3170927) B3170927
theorem B3170731 : Blo 1877140 3170731 := bstep (se 1 (by rfl) ⟨2378048, by rfl⟩ : syracuseStep 3170731 = 4756097) B4756097
theorem B6341759 : Blo 1877140 6341759 := bstep (se 1 (by rfl) ⟨4756319, by rfl⟩ : syracuseStep 6341759 = 9512639) B9512639
theorem B14648485 : Blo 1877140 14648485 := bstep (se 4 (by rfl) ⟨1373295, by rfl⟩ : syracuseStep 14648485 = 2746591) B2746591
theorem B4752553 : Blo 1877140 4752553 := bstep (se 2 (by rfl) ⟨1782207, by rfl⟩ : syracuseStep 4752553 = 3564415) B3564415
theorem B1877231 : Blo 1877140 1877231 := bstep (se 1 (by rfl) ⟨1407923, by rfl⟩ : syracuseStep 1877231 = 2815847) B2815847
theorem B10290473 : Blo 1877140 10290473 := bstep (se 2 (by rfl) ⟨3858927, by rfl⟩ : syracuseStep 10290473 = 7717855) B7717855
theorem B4752695 : Blo 1877140 4752695 := bstep (se 1 (by rfl) ⟨3564521, by rfl⟩ : syracuseStep 4752695 = 7129043) B7129043
theorem B1877319 : Blo 1877140 1877319 := bstep (se 1 (by rfl) ⟨1407989, by rfl⟩ : syracuseStep 1877319 = 2815979) B2815979
theorem B1877595 : Blo 1877140 1877595 := bstep (se 1 (by rfl) ⟨1408196, by rfl⟩ : syracuseStep 1877595 = 2816393) B2816393
theorem B3565289 : Blo 1877140 3565289 := bstep (se 2 (by rfl) ⟨1336983, by rfl⟩ : syracuseStep 3565289 = 2673967) B2673967
theorem B3663739 : Blo 1877140 3663739 := bstep (se 1 (by rfl) ⟨2747804, by rfl⟩ : syracuseStep 3663739 = 5495609) B5495609
theorem B2377831 : Blo 1877140 2377831 := bstep (se 1 (by rfl) ⟨1783373, by rfl⟩ : syracuseStep 2377831 = 3566747) B3566747
theorem B1878255 : Blo 1877140 1878255 := bstep (se 1 (by rfl) ⟨1408691, by rfl⟩ : syracuseStep 1878255 = 2817383) B2817383
theorem B21391775 : Blo 1877140 21391775 := bstep (se 1 (by rfl) ⟨16043831, by rfl⟩ : syracuseStep 21391775 = 32087663) B32087663
theorem B4753961 : Blo 1877140 4753961 := bstep (se 2 (by rfl) ⟨1782735, by rfl⟩ : syracuseStep 4753961 = 3565471) B3565471
theorem B9022043 : Blo 1877140 9022043 := bstep (se 1 (by rfl) ⟨6766532, by rfl⟩ : syracuseStep 9022043 = 13533065) B13533065
theorem B1878687 : Blo 1877140 1878687 := bstep (se 1 (by rfl) ⟨1409015, by rfl⟩ : syracuseStep 1878687 = 2818031) B2818031
theorem B3386063 : Blo 1877140 3386063 := bstep (se 1 (by rfl) ⟨2539547, by rfl⟩ : syracuseStep 3386063 = 5079095) B5079095
theorem B9505511 : Blo 1877140 9505511 := bstep (se 1 (by rfl) ⟨7129133, by rfl⟩ : syracuseStep 9505511 = 14258267) B14258267
theorem B1878811 : Blo 1877140 1878811 := bstep (se 1 (by rfl) ⟨1409108, by rfl⟩ : syracuseStep 1878811 = 2818217) B2818217
theorem B1878815 : Blo 1877140 1878815 := bstep (se 1 (by rfl) ⟨1409111, by rfl⟩ : syracuseStep 1878815 = 2818223) B2818223
theorem B7130015 : Blo 1877140 7130015 := bstep (se 1 (by rfl) ⟨5347511, by rfl⟩ : syracuseStep 7130015 = 10695023) B10695023
theorem B4066463 : Blo 1877140 4066463 := bstep (se 1 (by rfl) ⟨3049847, by rfl⟩ : syracuseStep 4066463 = 6099695) B6099695
theorem B5950631 : Blo 1877140 5950631 := bstep (se 1 (by rfl) ⟨4462973, by rfl⟩ : syracuseStep 5950631 = 8925947) B8925947
theorem B7131017 : Blo 1877140 7131017 := bstep (se 2 (by rfl) ⟨2674131, by rfl⟩ : syracuseStep 7131017 = 5348263) B5348263
theorem B25710509 : Blo 1877140 25710509 := bstep (se 3 (by rfl) ⟨4820720, by rfl⟩ : syracuseStep 25710509 = 9641441) B9641441
theorem B6017257 : Blo 1877140 6017257 := bstep (se 2 (by rfl) ⟨2256471, by rfl⟩ : syracuseStep 6017257 = 4512943) B4512943
theorem B27063305 : Blo 1877140 27063305 := bstep (se 2 (by rfl) ⟨10148739, by rfl⟩ : syracuseStep 27063305 = 20297479) B20297479
theorem B14267987 : Blo 1877140 14267987 := bstep (se 1 (by rfl) ⟨10700990, by rfl⟩ : syracuseStep 14267987 = 21401981) B21401981
theorem B4224851 : Blo 1877140 4224851 := bstep (se 1 (by rfl) ⟨3168638, by rfl⟩ : syracuseStep 4224851 = 6337277) B6337277
theorem B2815865 : Blo 1877140 2815865 := bstep (se 2 (by rfl) ⟨1055949, by rfl⟩ : syracuseStep 2815865 = 2111899) B2111899
theorem B4224923 : Blo 1877140 4224923 := bstep (se 1 (by rfl) ⟨3168692, by rfl⟩ : syracuseStep 4224923 = 6337385) B6337385
theorem B4224959 : Blo 1877140 4224959 := bstep (se 1 (by rfl) ⟨3168719, by rfl⟩ : syracuseStep 4224959 = 6337439) B6337439
theorem B2816111 : Blo 1877140 2816111 := bstep (se 1 (by rfl) ⟨2112083, by rfl⟩ : syracuseStep 2816111 = 4224167) B4224167
theorem B27080891 : Blo 1877140 27080891 := bstep (se 1 (by rfl) ⟨20310668, by rfl⟩ : syracuseStep 27080891 = 40621337) B40621337
theorem B91363565 : Blo 1877140 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B4225895 : Blo 1877140 4225895 := bstep (se 1 (by rfl) ⟨3169421, by rfl⟩ : syracuseStep 4225895 = 6338843) B6338843
theorem B2816891 : Blo 1877140 2816891 := bstep (se 1 (by rfl) ⟨2112668, by rfl⟩ : syracuseStep 2816891 = 4225337) B4225337
theorem B3169273 : Blo 1877140 3169273 := bstep (se 2 (by rfl) ⟨1188477, by rfl⟩ : syracuseStep 3169273 = 2376955) B2376955
theorem B5078177 : Blo 1877140 5078177 := bstep (se 2 (by rfl) ⟨1904316, by rfl⟩ : syracuseStep 5078177 = 3808633) B3808633
theorem B16481513 : Blo 1877140 16481513 := bstep (se 2 (by rfl) ⟨6180567, by rfl⟩ : syracuseStep 16481513 = 12361135) B12361135
theorem B2817275 : Blo 1877140 2817275 := bstep (se 1 (by rfl) ⟨2112956, by rfl⟩ : syracuseStep 2817275 = 4225913) B4225913
theorem B2817371 : Blo 1877140 2817371 := bstep (se 1 (by rfl) ⟨2113028, by rfl⟩ : syracuseStep 2817371 = 4226057) B4226057
theorem B5348855 : Blo 1877140 5348855 := bstep (se 1 (by rfl) ⟨4011641, by rfl⟩ : syracuseStep 5348855 = 8023283) B8023283
theorem B5709359 : Blo 1877140 5709359 := bstep (se 1 (by rfl) ⟨4282019, by rfl⟩ : syracuseStep 5709359 = 8564039) B8564039
theorem B2113231 : Blo 1877140 2113231 := bstep (se 1 (by rfl) ⟨1584923, by rfl⟩ : syracuseStep 2113231 = 3169847) B3169847
theorem B8568605 : Blo 1877140 8568605 := bstep (se 3 (by rfl) ⟨1606613, by rfl⟩ : syracuseStep 8568605 = 3213227) B3213227
theorem B14262155 : Blo 1877140 14262155 := bstep (se 1 (by rfl) ⟨10696616, by rfl⟩ : syracuseStep 14262155 = 21393233) B21393233
theorem B28909543 : Blo 1877140 28909543 := bstep (se 1 (by rfl) ⟨21682157, by rfl⟩ : syracuseStep 28909543 = 43364315) B43364315
theorem B4227065 : Blo 1877140 4227065 := bstep (se 2 (by rfl) ⟨1585149, by rfl⟩ : syracuseStep 4227065 = 3170299) B3170299
theorem B6340679 : Blo 1877140 6340679 := bstep (se 1 (by rfl) ⟨4755509, by rfl⟩ : syracuseStep 6340679 = 9511019) B9511019
theorem B3170441 : Blo 1877140 3170441 := bstep (se 2 (by rfl) ⟨1188915, by rfl⟩ : syracuseStep 3170441 = 2377831) B2377831
theorem B32096411 : Blo 1877140 32096411 := bstep (se 1 (by rfl) ⟨24072308, by rfl⟩ : syracuseStep 32096411 = 48144617) B48144617
theorem B15868349 : Blo 1877140 15868349 := bstep (se 3 (by rfl) ⟨2975315, by rfl⟩ : syracuseStep 15868349 = 5950631) B5950631
theorem B2818601 : Blo 1877140 2818601 := bstep (se 2 (by rfl) ⟨1056975, by rfl⟩ : syracuseStep 2818601 = 2113951) B2113951
theorem B4227641 : Blo 1877140 4227641 := bstep (se 2 (by rfl) ⟨1585365, by rfl⟩ : syracuseStep 4227641 = 3170731) B3170731
theorem B43950701 : Blo 1877140 43950701 := bstep (se 3 (by rfl) ⟨8240756, by rfl⟩ : syracuseStep 43950701 = 16481513) B16481513
theorem B4227839 : Blo 1877140 4227839 := bstep (se 1 (by rfl) ⟨3170879, by rfl⟩ : syracuseStep 4227839 = 6341759) B6341759
theorem B9511991 : Blo 1877140 9511991 := bstep (se 1 (by rfl) ⟨7133993, by rfl⟩ : syracuseStep 9511991 = 14267987) B14267987
theorem B2376859 : Blo 1877140 2376859 := bstep (se 1 (by rfl) ⟨1782644, by rfl⟩ : syracuseStep 2376859 = 3565289) B3565289
theorem B1877243 : Blo 1877140 1877243 := bstep (se 1 (by rfl) ⟨1407932, by rfl⟩ : syracuseStep 1877243 = 2815865) B2815865
theorem B14263613 : Blo 1877140 14263613 := bstep (se 3 (by rfl) ⟨2674427, by rfl⟩ : syracuseStep 14263613 = 5348855) B5348855
theorem B1877407 : Blo 1877140 1877407 := bstep (se 1 (by rfl) ⟨1408055, by rfl⟩ : syracuseStep 1877407 = 2816111) B2816111
theorem B60909043 : Blo 1877140 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B19531313 : Blo 1877140 19531313 := bstep (se 2 (by rfl) ⟨7324242, by rfl⟩ : syracuseStep 19531313 = 14648485) B14648485
theorem B6014695 : Blo 1877140 6014695 := bstep (se 1 (by rfl) ⟨4511021, by rfl⟩ : syracuseStep 6014695 = 9022043) B9022043
theorem B9029501 : Blo 1877140 9029501 := bstep (se 3 (by rfl) ⟨1693031, by rfl⟩ : syracuseStep 9029501 = 3386063) B3386063
theorem B1877927 : Blo 1877140 1877927 := bstep (se 1 (by rfl) ⟨1408445, by rfl⟩ : syracuseStep 1877927 = 2816891) B2816891
theorem B4753343 : Blo 1877140 4753343 := bstep (se 1 (by rfl) ⟨3565007, by rfl⟩ : syracuseStep 4753343 = 7130015) B7130015
theorem B3385451 : Blo 1877140 3385451 := bstep (se 1 (by rfl) ⟨2539088, by rfl⟩ : syracuseStep 3385451 = 5078177) B5078177
theorem B1878183 : Blo 1877140 1878183 := bstep (se 1 (by rfl) ⟨1408637, by rfl⟩ : syracuseStep 1878183 = 2817275) B2817275
theorem B1878247 : Blo 1877140 1878247 := bstep (se 1 (by rfl) ⟨1408685, by rfl⟩ : syracuseStep 1878247 = 2817371) B2817371
theorem B4884985 : Blo 1877140 4884985 := bstep (se 2 (by rfl) ⟨1831869, by rfl⟩ : syracuseStep 4884985 = 3663739) B3663739
theorem B5712403 : Blo 1877140 5712403 := bstep (se 1 (by rfl) ⟨4284302, by rfl⟩ : syracuseStep 5712403 = 8568605) B8568605
theorem B4754011 : Blo 1877140 4754011 := bstep (se 1 (by rfl) ⟨3565508, by rfl⟩ : syracuseStep 4754011 = 7131017) B7131017
theorem B17140339 : Blo 1877140 17140339 := bstep (se 1 (by rfl) ⟨12855254, by rfl⟩ : syracuseStep 17140339 = 25710509) B25710509
theorem B38546057 : Blo 1877140 38546057 := bstep (se 2 (by rfl) ⟨14454771, by rfl⟩ : syracuseStep 38546057 = 28909543) B28909543
theorem B1878735 : Blo 1877140 1878735 := bstep (se 1 (by rfl) ⟨1409051, by rfl⟩ : syracuseStep 1878735 = 2818103) B2818103
theorem B1878759 : Blo 1877140 1878759 := bstep (se 1 (by rfl) ⟨1409069, by rfl⟩ : syracuseStep 1878759 = 2818139) B2818139
theorem B1878767 : Blo 1877140 1878767 := bstep (se 1 (by rfl) ⟨1409075, by rfl⟩ : syracuseStep 1878767 = 2818151) B2818151
theorem B18042203 : Blo 1877140 18042203 := bstep (se 1 (by rfl) ⟨13531652, by rfl⟩ : syracuseStep 18042203 = 27063305) B27063305
theorem B6860315 : Blo 1877140 6860315 := bstep (se 1 (by rfl) ⟨5145236, by rfl⟩ : syracuseStep 6860315 = 10290473) B10290473
theorem B32092037 : Blo 1877140 32092037 := bstep (se 4 (by rfl) ⟨3008628, by rfl⟩ : syracuseStep 32092037 = 6017257) B6017257
theorem B6336737 : Blo 1877140 6336737 := bstep (se 2 (by rfl) ⟨2376276, by rfl⟩ : syracuseStep 6336737 = 4752553) B4752553
theorem B6337007 : Blo 1877140 6337007 := bstep (se 1 (by rfl) ⟨4752755, by rfl⟩ : syracuseStep 6337007 = 9505511) B9505511
theorem B3806239 : Blo 1877140 3806239 := bstep (se 1 (by rfl) ⟨2854679, by rfl⟩ : syracuseStep 3806239 = 5709359) B5709359
theorem B9508103 : Blo 1877140 9508103 := bstep (se 1 (by rfl) ⟨7131077, by rfl⟩ : syracuseStep 9508103 = 14262155) B14262155
theorem B24073949 : Blo 1877140 24073949 := bstep (se 3 (by rfl) ⟨4513865, by rfl⟩ : syracuseStep 24073949 = 9027731) B9027731
theorem B3168463 : Blo 1877140 3168463 := bstep (se 1 (by rfl) ⟨2376347, by rfl⟩ : syracuseStep 3168463 = 4752695) B4752695
theorem B2816567 : Blo 1877140 2816567 := bstep (se 1 (by rfl) ⟨2112425, by rfl⟩ : syracuseStep 2816567 = 4224851) B4224851
theorem B2816615 : Blo 1877140 2816615 := bstep (se 1 (by rfl) ⟨2112461, by rfl⟩ : syracuseStep 2816615 = 4224923) B4224923
theorem B2816639 : Blo 1877140 2816639 := bstep (se 1 (by rfl) ⟨2112479, by rfl⟩ : syracuseStep 2816639 = 4224959) B4224959
theorem B4225697 : Blo 1877140 4225697 := bstep (se 2 (by rfl) ⟨1584636, by rfl⟩ : syracuseStep 4225697 = 3169273) B3169273
theorem B18053927 : Blo 1877140 18053927 := bstep (se 1 (by rfl) ⟨13540445, by rfl⟩ : syracuseStep 18053927 = 27080891) B27080891
theorem B14261183 : Blo 1877140 14261183 := bstep (se 1 (by rfl) ⟨10695887, by rfl⟩ : syracuseStep 14261183 = 21391775) B21391775
theorem B3169307 : Blo 1877140 3169307 := bstep (se 1 (by rfl) ⟨2376980, by rfl⟩ : syracuseStep 3169307 = 4753961) B4753961
theorem B2817263 : Blo 1877140 2817263 := bstep (se 1 (by rfl) ⟨2112947, by rfl⟩ : syracuseStep 2817263 = 4225895) B4225895
theorem B2710975 : Blo 1877140 2710975 := bstep (se 1 (by rfl) ⟨2033231, by rfl⟩ : syracuseStep 2710975 = 4066463) B4066463
theorem B2817641 : Blo 1877140 2817641 := bstep (se 2 (by rfl) ⟨1056615, by rfl⟩ : syracuseStep 2817641 = 2113231) B2113231
theorem B2818043 : Blo 1877140 2818043 := bstep (se 1 (by rfl) ⟨2113532, by rfl⟩ : syracuseStep 2818043 = 4227065) B4227065
theorem B4227119 : Blo 1877140 4227119 := bstep (se 1 (by rfl) ⟨3170339, by rfl⟩ : syracuseStep 4227119 = 6340679) B6340679
theorem B2113627 : Blo 1877140 2113627 := bstep (se 1 (by rfl) ⟨1585220, by rfl⟩ : syracuseStep 2113627 = 3170441) B3170441
theorem B21397607 : Blo 1877140 21397607 := bstep (se 1 (by rfl) ⟨16048205, by rfl⟩ : syracuseStep 21397607 = 32096411) B32096411
theorem B2818427 : Blo 1877140 2818427 := bstep (se 1 (by rfl) ⟨2113820, by rfl⟩ : syracuseStep 2818427 = 4227641) B4227641
theorem B2818559 : Blo 1877140 2818559 := bstep (se 1 (by rfl) ⟨2113919, by rfl⟩ : syracuseStep 2818559 = 4227839) B4227839
theorem B6341327 : Blo 1877140 6341327 := bstep (se 1 (by rfl) ⟨4755995, by rfl⟩ : syracuseStep 6341327 = 9511991) B9511991
theorem B16049299 : Blo 1877140 16049299 := bstep (se 1 (by rfl) ⟨12036974, by rfl⟩ : syracuseStep 16049299 = 24073949) B24073949
theorem B1877711 : Blo 1877140 1877711 := bstep (se 1 (by rfl) ⟨1408283, by rfl⟩ : syracuseStep 1877711 = 2816567) B2816567
theorem B1877743 : Blo 1877140 1877743 := bstep (se 1 (by rfl) ⟨1408307, by rfl⟩ : syracuseStep 1877743 = 2816615) B2816615
theorem B1877759 : Blo 1877140 1877759 := bstep (se 1 (by rfl) ⟨1408319, by rfl⟩ : syracuseStep 1877759 = 2816639) B2816639
theorem B12035951 : Blo 1877140 12035951 := bstep (se 1 (by rfl) ⟨9026963, by rfl⟩ : syracuseStep 12035951 = 18053927) B18053927
theorem B3614633 : Blo 1877140 3614633 := bstep (se 2 (by rfl) ⟨1355487, by rfl⟩ : syracuseStep 3614633 = 2710975) B2710975
theorem B1878175 : Blo 1877140 1878175 := bstep (se 1 (by rfl) ⟨1408631, by rfl⟩ : syracuseStep 1878175 = 2817263) B2817263
theorem B12028135 : Blo 1877140 12028135 := bstep (se 1 (by rfl) ⟨9021101, by rfl⟩ : syracuseStep 12028135 = 18042203) B18042203
theorem B4573543 : Blo 1877140 4573543 := bstep (se 1 (by rfl) ⟨3430157, by rfl⟩ : syracuseStep 4573543 = 6860315) B6860315
theorem B1878427 : Blo 1877140 1878427 := bstep (se 1 (by rfl) ⟨1408820, by rfl⟩ : syracuseStep 1878427 = 2817641) B2817641
theorem B26053253 : Blo 1877140 26053253 := bstep (se 4 (by rfl) ⟨2442492, by rfl⟩ : syracuseStep 26053253 = 4884985) B4884985
theorem B1878695 : Blo 1877140 1878695 := bstep (se 1 (by rfl) ⟨1409021, by rfl⟩ : syracuseStep 1878695 = 2818043) B2818043
theorem B10578899 : Blo 1877140 10578899 := bstep (se 1 (by rfl) ⟨7934174, by rfl⟩ : syracuseStep 10578899 = 15868349) B15868349
theorem B1879067 : Blo 1877140 1879067 := bstep (se 1 (by rfl) ⟨1409300, by rfl⟩ : syracuseStep 1879067 = 2818601) B2818601
theorem B13020875 : Blo 1877140 13020875 := bstep (se 1 (by rfl) ⟨9765656, by rfl⟩ : syracuseStep 13020875 = 19531313) B19531313
theorem B5074985 : Blo 1877140 5074985 := bstep (se 2 (by rfl) ⟨1903119, by rfl⟩ : syracuseStep 5074985 = 3806239) B3806239
theorem B2256967 : Blo 1877140 2256967 := bstep (se 1 (by rfl) ⟨1692725, by rfl⟩ : syracuseStep 2256967 = 3385451) B3385451
theorem B9507455 : Blo 1877140 9507455 := bstep (se 1 (by rfl) ⟨7130591, by rfl⟩ : syracuseStep 9507455 = 14261183) B14261183
theorem B81212057 : Blo 1877140 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B21394691 : Blo 1877140 21394691 := bstep (se 1 (by rfl) ⟨16046018, by rfl⟩ : syracuseStep 21394691 = 32092037) B32092037
theorem B4224491 : Blo 1877140 4224491 := bstep (se 1 (by rfl) ⟨3168368, by rfl⟩ : syracuseStep 4224491 = 6336737) B6336737
theorem B4224617 : Blo 1877140 4224617 := bstep (se 2 (by rfl) ⟨1584231, by rfl⟩ : syracuseStep 4224617 = 3168463) B3168463
theorem B4224671 : Blo 1877140 4224671 := bstep (se 1 (by rfl) ⟨3168503, by rfl⟩ : syracuseStep 4224671 = 6337007) B6337007
theorem B29300467 : Blo 1877140 29300467 := bstep (se 1 (by rfl) ⟨21975350, by rfl⟩ : syracuseStep 29300467 = 43950701) B43950701
theorem B7616537 : Blo 1877140 7616537 := bstep (se 2 (by rfl) ⟨2856201, by rfl⟩ : syracuseStep 7616537 = 5712403) B5712403
theorem B6338681 : Blo 1877140 6338681 := bstep (se 2 (by rfl) ⟨2377005, by rfl⟩ : syracuseStep 6338681 = 4754011) B4754011
theorem B22853785 : Blo 1877140 22853785 := bstep (se 2 (by rfl) ⟨8570169, by rfl⟩ : syracuseStep 22853785 = 17140339) B17140339
theorem B6338735 : Blo 1877140 6338735 := bstep (se 1 (by rfl) ⟨4754051, by rfl⟩ : syracuseStep 6338735 = 9508103) B9508103
theorem B9509075 : Blo 1877140 9509075 := bstep (se 1 (by rfl) ⟨7131806, by rfl⟩ : syracuseStep 9509075 = 14263613) B14263613
theorem B6019667 : Blo 1877140 6019667 := bstep (se 1 (by rfl) ⟨4514750, by rfl⟩ : syracuseStep 6019667 = 9029501) B9029501
theorem B3168895 : Blo 1877140 3168895 := bstep (se 1 (by rfl) ⟨2376671, by rfl⟩ : syracuseStep 3168895 = 4753343) B4753343
theorem B3169145 : Blo 1877140 3169145 := bstep (se 2 (by rfl) ⟨1188429, by rfl⟩ : syracuseStep 3169145 = 2376859) B2376859
theorem B25697371 : Blo 1877140 25697371 := bstep (se 1 (by rfl) ⟨19273028, by rfl⟩ : syracuseStep 25697371 = 38546057) B38546057
theorem B2817131 : Blo 1877140 2817131 := bstep (se 1 (by rfl) ⟨2112848, by rfl⟩ : syracuseStep 2817131 = 4225697) B4225697
theorem B2112871 : Blo 1877140 2112871 := bstep (se 1 (by rfl) ⟨1584653, by rfl⟩ : syracuseStep 2112871 = 3169307) B3169307
theorem B8019593 : Blo 1877140 8019593 := bstep (se 2 (by rfl) ⟨3007347, by rfl⟩ : syracuseStep 8019593 = 6014695) B6014695
theorem B2818079 : Blo 1877140 2818079 := bstep (se 1 (by rfl) ⟨2113559, by rfl⟩ : syracuseStep 2818079 = 4227119) B4227119
theorem B13533293 : Blo 1877140 13533293 := bstep (se 3 (by rfl) ⟨2537492, by rfl⟩ : syracuseStep 13533293 = 5074985) B5074985
theorem B2818169 : Blo 1877140 2818169 := bstep (se 2 (by rfl) ⟨1056813, by rfl⟩ : syracuseStep 2818169 = 2113627) B2113627
theorem B54141371 : Blo 1877140 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B4227551 : Blo 1877140 4227551 := bstep (se 1 (by rfl) ⟨3170663, by rfl⟩ : syracuseStep 4227551 = 6341327) B6341327
theorem B14263127 : Blo 1877140 14263127 := bstep (se 1 (by rfl) ⟨10697345, by rfl⟩ : syracuseStep 14263127 = 21394691) B21394691
theorem B2409755 : Blo 1877140 2409755 := bstep (se 1 (by rfl) ⟨1807316, by rfl⟩ : syracuseStep 2409755 = 3614633) B3614633
theorem B21399065 : Blo 1877140 21399065 := bstep (se 2 (by rfl) ⟨8024649, by rfl⟩ : syracuseStep 21399065 = 16049299) B16049299
theorem B17368835 : Blo 1877140 17368835 := bstep (se 1 (by rfl) ⟨13026626, by rfl⟩ : syracuseStep 17368835 = 26053253) B26053253
theorem B1878087 : Blo 1877140 1878087 := bstep (se 1 (by rfl) ⟨1408565, by rfl⟩ : syracuseStep 1878087 = 2817131) B2817131
theorem B14265071 : Blo 1877140 14265071 := bstep (se 1 (by rfl) ⟨10698803, by rfl⟩ : syracuseStep 14265071 = 21397607) B21397607
theorem B1878951 : Blo 1877140 1878951 := bstep (se 1 (by rfl) ⟨1409213, by rfl⟩ : syracuseStep 1878951 = 2818427) B2818427
theorem B1879039 : Blo 1877140 1879039 := bstep (se 1 (by rfl) ⟨1409279, by rfl⟩ : syracuseStep 1879039 = 2818559) B2818559
theorem B12037157 : Blo 1877140 12037157 := bstep (se 4 (by rfl) ⟨1128483, by rfl⟩ : syracuseStep 12037157 = 2256967) B2256967
theorem B6098057 : Blo 1877140 6098057 := bstep (se 2 (by rfl) ⟨2286771, by rfl⟩ : syracuseStep 6098057 = 4573543) B4573543
theorem B8023967 : Blo 1877140 8023967 := bstep (se 1 (by rfl) ⟨6017975, by rfl⟩ : syracuseStep 8023967 = 12035951) B12035951
theorem B34263161 : Blo 1877140 34263161 := bstep (se 2 (by rfl) ⟨12848685, by rfl⟩ : syracuseStep 34263161 = 25697371) B25697371
theorem B5346395 : Blo 1877140 5346395 := bstep (se 1 (by rfl) ⟨4009796, by rfl⟩ : syracuseStep 5346395 = 8019593) B8019593
theorem B8680583 : Blo 1877140 8680583 := bstep (se 1 (by rfl) ⟨6510437, by rfl⟩ : syracuseStep 8680583 = 13020875) B13020875
theorem B30471713 : Blo 1877140 30471713 := bstep (se 2 (by rfl) ⟨11426892, by rfl⟩ : syracuseStep 30471713 = 22853785) B22853785
theorem B16037513 : Blo 1877140 16037513 := bstep (se 2 (by rfl) ⟨6014067, by rfl⟩ : syracuseStep 16037513 = 12028135) B12028135
theorem B6338303 : Blo 1877140 6338303 := bstep (se 1 (by rfl) ⟨4753727, by rfl⟩ : syracuseStep 6338303 = 9507455) B9507455
theorem B4225193 : Blo 1877140 4225193 := bstep (se 2 (by rfl) ⟨1584447, by rfl⟩ : syracuseStep 4225193 = 3168895) B3168895
theorem B2816327 : Blo 1877140 2816327 := bstep (se 1 (by rfl) ⟨2112245, by rfl⟩ : syracuseStep 2816327 = 4224491) B4224491
theorem B2816411 : Blo 1877140 2816411 := bstep (se 1 (by rfl) ⟨2112308, by rfl⟩ : syracuseStep 2816411 = 4224617) B4224617
theorem B2816447 : Blo 1877140 2816447 := bstep (se 1 (by rfl) ⟨2112335, by rfl⟩ : syracuseStep 2816447 = 4224671) B4224671
theorem B5077691 : Blo 1877140 5077691 := bstep (se 1 (by rfl) ⟨3808268, by rfl⟩ : syracuseStep 5077691 = 7616537) B7616537
theorem B4225787 : Blo 1877140 4225787 := bstep (se 1 (by rfl) ⟨3169340, by rfl⟩ : syracuseStep 4225787 = 6338681) B6338681
theorem B4225823 : Blo 1877140 4225823 := bstep (se 1 (by rfl) ⟨3169367, by rfl⟩ : syracuseStep 4225823 = 6338735) B6338735
theorem B6339383 : Blo 1877140 6339383 := bstep (se 1 (by rfl) ⟨4754537, by rfl⟩ : syracuseStep 6339383 = 9509075) B9509075
theorem B4013111 : Blo 1877140 4013111 := bstep (se 1 (by rfl) ⟨3009833, by rfl⟩ : syracuseStep 4013111 = 6019667) B6019667
theorem B2817161 : Blo 1877140 2817161 := bstep (se 2 (by rfl) ⟨1056435, by rfl⟩ : syracuseStep 2817161 = 2112871) B2112871
theorem B2112763 : Blo 1877140 2112763 := bstep (se 1 (by rfl) ⟨1584572, by rfl⟩ : syracuseStep 2112763 = 3169145) B3169145
theorem B7052599 : Blo 1877140 7052599 := bstep (se 1 (by rfl) ⟨5289449, by rfl⟩ : syracuseStep 7052599 = 10578899) B10578899
theorem B39067289 : Blo 1877140 39067289 := bstep (se 2 (by rfl) ⟨14650233, by rfl⟩ : syracuseStep 39067289 = 29300467) B29300467
theorem B36094247 : Blo 1877140 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B2818367 : Blo 1877140 2818367 := bstep (se 1 (by rfl) ⟨2113775, by rfl⟩ : syracuseStep 2818367 = 4227551) B4227551
theorem B3564263 : Blo 1877140 3564263 := bstep (se 1 (by rfl) ⟨2673197, by rfl⟩ : syracuseStep 3564263 = 5346395) B5346395
theorem B10691675 : Blo 1877140 10691675 := bstep (se 1 (by rfl) ⟨8018756, by rfl⟩ : syracuseStep 10691675 = 16037513) B16037513
theorem B1877551 : Blo 1877140 1877551 := bstep (se 1 (by rfl) ⟨1408163, by rfl⟩ : syracuseStep 1877551 = 2816327) B2816327
theorem B1877607 : Blo 1877140 1877607 := bstep (se 1 (by rfl) ⟨1408205, by rfl⟩ : syracuseStep 1877607 = 2816411) B2816411
theorem B1877631 : Blo 1877140 1877631 := bstep (se 1 (by rfl) ⟨1408223, by rfl⟩ : syracuseStep 1877631 = 2816447) B2816447
theorem B3385127 : Blo 1877140 3385127 := bstep (se 1 (by rfl) ⟨2538845, by rfl⟩ : syracuseStep 3385127 = 5077691) B5077691
theorem B4065371 : Blo 1877140 4065371 := bstep (se 1 (by rfl) ⟨3049028, by rfl⟩ : syracuseStep 4065371 = 6098057) B6098057
theorem B1878107 : Blo 1877140 1878107 := bstep (se 1 (by rfl) ⟨1408580, by rfl⟩ : syracuseStep 1878107 = 2817161) B2817161
theorem B26044859 : Blo 1877140 26044859 := bstep (se 1 (by rfl) ⟨19533644, by rfl⟩ : syracuseStep 26044859 = 39067289) B39067289
theorem B1878719 : Blo 1877140 1878719 := bstep (se 1 (by rfl) ⟨1409039, by rfl⟩ : syracuseStep 1878719 = 2818079) B2818079
theorem B9022195 : Blo 1877140 9022195 := bstep (se 1 (by rfl) ⟨6766646, by rfl⟩ : syracuseStep 9022195 = 13533293) B13533293
theorem B22842107 : Blo 1877140 22842107 := bstep (se 1 (by rfl) ⟨17131580, by rfl⟩ : syracuseStep 22842107 = 34263161) B34263161
theorem B1878779 : Blo 1877140 1878779 := bstep (se 1 (by rfl) ⟨1409084, by rfl⟩ : syracuseStep 1878779 = 2818169) B2818169
theorem B10701629 : Blo 1877140 10701629 := bstep (se 3 (by rfl) ⟨2006555, by rfl⟩ : syracuseStep 10701629 = 4013111) B4013111
theorem B14266043 : Blo 1877140 14266043 := bstep (se 1 (by rfl) ⟨10699532, by rfl⟩ : syracuseStep 14266043 = 21399065) B21399065
theorem B8024771 : Blo 1877140 8024771 := bstep (se 1 (by rfl) ⟨6018578, by rfl⟩ : syracuseStep 8024771 = 12037157) B12037157
theorem B185267573 : Blo 1877140 185267573 := bstep (se 5 (by rfl) ⟨8684417, by rfl⟩ : syracuseStep 185267573 = 17368835) B17368835
theorem B25704053 : Blo 1877140 25704053 := bstep (se 5 (by rfl) ⟨1204877, by rfl⟩ : syracuseStep 25704053 = 2409755) B2409755
theorem B23148221 : Blo 1877140 23148221 := bstep (se 3 (by rfl) ⟨4340291, by rfl⟩ : syracuseStep 23148221 = 8680583) B8680583
theorem B9508751 : Blo 1877140 9508751 := bstep (se 1 (by rfl) ⟨7131563, by rfl⟩ : syracuseStep 9508751 = 14263127) B14263127
theorem B20314475 : Blo 1877140 20314475 := bstep (se 1 (by rfl) ⟨15235856, by rfl⟩ : syracuseStep 20314475 = 30471713) B30471713
theorem B4225535 : Blo 1877140 4225535 := bstep (se 1 (by rfl) ⟨3169151, by rfl⟩ : syracuseStep 4225535 = 6338303) B6338303
theorem B2816795 : Blo 1877140 2816795 := bstep (se 1 (by rfl) ⟨2112596, by rfl⟩ : syracuseStep 2816795 = 4225193) B4225193
theorem B2817017 : Blo 1877140 2817017 := bstep (se 2 (by rfl) ⟨1056381, by rfl⟩ : syracuseStep 2817017 = 2112763) B2112763
theorem B9403465 : Blo 1877140 9403465 := bstep (se 2 (by rfl) ⟨3526299, by rfl⟩ : syracuseStep 9403465 = 7052599) B7052599
theorem B9510047 : Blo 1877140 9510047 := bstep (se 1 (by rfl) ⟨7132535, by rfl⟩ : syracuseStep 9510047 = 14265071) B14265071
theorem B2817191 : Blo 1877140 2817191 := bstep (se 1 (by rfl) ⟨2112893, by rfl⟩ : syracuseStep 2817191 = 4225787) B4225787
theorem B2817215 : Blo 1877140 2817215 := bstep (se 1 (by rfl) ⟨2112911, by rfl⟩ : syracuseStep 2817215 = 4225823) B4225823
theorem B4226255 : Blo 1877140 4226255 := bstep (se 1 (by rfl) ⟨3169691, by rfl⟩ : syracuseStep 4226255 = 6339383) B6339383
theorem B5349311 : Blo 1877140 5349311 := bstep (se 1 (by rfl) ⟨4011983, by rfl⟩ : syracuseStep 5349311 = 8023967) B8023967
theorem B5349847 : Blo 1877140 5349847 := bstep (se 1 (by rfl) ⟨4012385, by rfl⟩ : syracuseStep 5349847 = 8024771) B8024771
theorem B7127783 : Blo 1877140 7127783 := bstep (se 1 (by rfl) ⟨5345837, by rfl⟩ : syracuseStep 7127783 = 10691675) B10691675
theorem B123511715 : Blo 1877140 123511715 := bstep (se 1 (by rfl) ⟨92633786, by rfl⟩ : syracuseStep 123511715 = 185267573) B185267573
theorem B69452957 : Blo 1877140 69452957 := bstep (se 3 (by rfl) ⟨13022429, by rfl⟩ : syracuseStep 69452957 = 26044859) B26044859
theorem B13542983 : Blo 1877140 13542983 := bstep (se 1 (by rfl) ⟨10157237, by rfl⟩ : syracuseStep 13542983 = 20314475) B20314475
theorem B61728589 : Blo 1877140 61728589 := bstep (se 3 (by rfl) ⟨11574110, by rfl⟩ : syracuseStep 61728589 = 23148221) B23148221
theorem B1877863 : Blo 1877140 1877863 := bstep (se 1 (by rfl) ⟨1408397, by rfl⟩ : syracuseStep 1877863 = 2816795) B2816795
theorem B9504701 : Blo 1877140 9504701 := bstep (se 3 (by rfl) ⟨1782131, by rfl⟩ : syracuseStep 9504701 = 3564263) B3564263
theorem B1878011 : Blo 1877140 1878011 := bstep (se 1 (by rfl) ⟨1408508, by rfl⟩ : syracuseStep 1878011 = 2817017) B2817017
theorem B1878127 : Blo 1877140 1878127 := bstep (se 1 (by rfl) ⟨1408595, by rfl⟩ : syracuseStep 1878127 = 2817191) B2817191
theorem B1878143 : Blo 1877140 1878143 := bstep (se 1 (by rfl) ⟨1408607, by rfl⟩ : syracuseStep 1878143 = 2817215) B2817215
theorem B3566207 : Blo 1877140 3566207 := bstep (se 1 (by rfl) ⟨2674655, by rfl⟩ : syracuseStep 3566207 = 5349311) B5349311
theorem B24062831 : Blo 1877140 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B1878911 : Blo 1877140 1878911 := bstep (se 1 (by rfl) ⟨1409183, by rfl⟩ : syracuseStep 1878911 = 2818367) B2818367
theorem B43363957 : Blo 1877140 43363957 := bstep (se 5 (by rfl) ⟨2032685, by rfl⟩ : syracuseStep 43363957 = 4065371) B4065371
theorem B2256751 : Blo 1877140 2256751 := bstep (se 1 (by rfl) ⟨1692563, by rfl⟩ : syracuseStep 2256751 = 3385127) B3385127
theorem B12537953 : Blo 1877140 12537953 := bstep (se 2 (by rfl) ⟨4701732, by rfl⟩ : syracuseStep 12537953 = 9403465) B9403465
theorem B17136035 : Blo 1877140 17136035 := bstep (se 1 (by rfl) ⟨12852026, by rfl⟩ : syracuseStep 17136035 = 25704053) B25704053
theorem B6339167 : Blo 1877140 6339167 := bstep (se 1 (by rfl) ⟨4754375, by rfl⟩ : syracuseStep 6339167 = 9508751) B9508751
theorem B48118373 : Blo 1877140 48118373 := bstep (se 4 (by rfl) ⟨4511097, by rfl⟩ : syracuseStep 48118373 = 9022195) B9022195
theorem B2817023 : Blo 1877140 2817023 := bstep (se 1 (by rfl) ⟨2112767, by rfl⟩ : syracuseStep 2817023 = 4225535) B4225535
theorem B15228071 : Blo 1877140 15228071 := bstep (se 1 (by rfl) ⟨11421053, by rfl⟩ : syracuseStep 15228071 = 22842107) B22842107
theorem B7134419 : Blo 1877140 7134419 := bstep (se 1 (by rfl) ⟨5350814, by rfl⟩ : syracuseStep 7134419 = 10701629) B10701629
theorem B6340031 : Blo 1877140 6340031 := bstep (se 1 (by rfl) ⟨4755023, by rfl⟩ : syracuseStep 6340031 = 9510047) B9510047
theorem B2817503 : Blo 1877140 2817503 := bstep (se 1 (by rfl) ⟨2113127, by rfl⟩ : syracuseStep 2817503 = 4226255) B4226255
theorem B9510695 : Blo 1877140 9510695 := bstep (se 1 (by rfl) ⟨7133021, by rfl⟩ : syracuseStep 9510695 = 14266043) B14266043
theorem B4751855 : Blo 1877140 4751855 := bstep (se 1 (by rfl) ⟨3563891, by rfl⟩ : syracuseStep 4751855 = 7127783) B7127783
theorem B46301971 : Blo 1877140 46301971 := bstep (se 1 (by rfl) ⟨34726478, by rfl⟩ : syracuseStep 46301971 = 69452957) B69452957
theorem B9028655 : Blo 1877140 9028655 := bstep (se 1 (by rfl) ⟨6771491, by rfl⟩ : syracuseStep 9028655 = 13542983) B13542983
theorem B16041887 : Blo 1877140 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B1878015 : Blo 1877140 1878015 := bstep (se 1 (by rfl) ⟨1408511, by rfl⟩ : syracuseStep 1878015 = 2817023) B2817023
theorem B10152047 : Blo 1877140 10152047 := bstep (se 1 (by rfl) ⟨7614035, by rfl⟩ : syracuseStep 10152047 = 15228071) B15228071
theorem B1878335 : Blo 1877140 1878335 := bstep (se 1 (by rfl) ⟨1408751, by rfl⟩ : syracuseStep 1878335 = 2817503) B2817503
theorem B3009001 : Blo 1877140 3009001 := bstep (se 2 (by rfl) ⟨1128375, by rfl⟩ : syracuseStep 3009001 = 2256751) B2256751
theorem B8358635 : Blo 1877140 8358635 := bstep (se 1 (by rfl) ⟨6268976, by rfl⟩ : syracuseStep 8358635 = 12537953) B12537953
theorem B82341143 : Blo 1877140 82341143 := bstep (se 1 (by rfl) ⟨61755857, by rfl⟩ : syracuseStep 82341143 = 123511715) B123511715
theorem B6336467 : Blo 1877140 6336467 := bstep (se 1 (by rfl) ⟨4752350, by rfl⟩ : syracuseStep 6336467 = 9504701) B9504701
theorem B11424023 : Blo 1877140 11424023 := bstep (se 1 (by rfl) ⟨8568017, by rfl⟩ : syracuseStep 11424023 = 17136035) B17136035
theorem B4756279 : Blo 1877140 4756279 := bstep (se 1 (by rfl) ⟨3567209, by rfl⟩ : syracuseStep 4756279 = 7134419) B7134419
theorem B7133129 : Blo 1877140 7133129 := bstep (se 2 (by rfl) ⟨2674923, by rfl⟩ : syracuseStep 7133129 = 5349847) B5349847
theorem B9509885 : Blo 1877140 9509885 := bstep (se 3 (by rfl) ⟨1783103, by rfl⟩ : syracuseStep 9509885 = 3566207) B3566207
theorem B4226111 : Blo 1877140 4226111 := bstep (se 1 (by rfl) ⟨3169583, by rfl⟩ : syracuseStep 4226111 = 6339167) B6339167
theorem B32078915 : Blo 1877140 32078915 := bstep (se 1 (by rfl) ⟨24059186, by rfl⟩ : syracuseStep 32078915 = 48118373) B48118373
theorem B57818609 : Blo 1877140 57818609 := bstep (se 2 (by rfl) ⟨21681978, by rfl⟩ : syracuseStep 57818609 = 43363957) B43363957
theorem B4226687 : Blo 1877140 4226687 := bstep (se 1 (by rfl) ⟨3170015, by rfl⟩ : syracuseStep 4226687 = 6340031) B6340031
theorem B82304785 : Blo 1877140 82304785 := bstep (se 2 (by rfl) ⟨30864294, by rfl⟩ : syracuseStep 82304785 = 61728589) B61728589
theorem B6340463 : Blo 1877140 6340463 := bstep (se 1 (by rfl) ⟨4755347, by rfl⟩ : syracuseStep 6340463 = 9510695) B9510695
theorem B61735961 : Blo 1877140 61735961 := bstep (se 2 (by rfl) ⟨23150985, by rfl⟩ : syracuseStep 61735961 = 46301971) B46301971
theorem B6341705 : Blo 1877140 6341705 := bstep (se 2 (by rfl) ⟨2378139, by rfl⟩ : syracuseStep 6341705 = 4756279) B4756279
theorem B6768031 : Blo 1877140 6768031 := bstep (se 1 (by rfl) ⟨5076023, by rfl⟩ : syracuseStep 6768031 = 10152047) B10152047
theorem B5572423 : Blo 1877140 5572423 := bstep (se 1 (by rfl) ⟨4179317, by rfl⟩ : syracuseStep 5572423 = 8358635) B8358635
theorem B38545739 : Blo 1877140 38545739 := bstep (se 1 (by rfl) ⟨28909304, by rfl⟩ : syracuseStep 38545739 = 57818609) B57818609
theorem B10694591 : Blo 1877140 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B4755419 : Blo 1877140 4755419 := bstep (se 1 (by rfl) ⟨3566564, by rfl⟩ : syracuseStep 4755419 = 7133129) B7133129
theorem B21385943 : Blo 1877140 21385943 := bstep (se 1 (by rfl) ⟨16039457, by rfl⟩ : syracuseStep 21385943 = 32078915) B32078915
theorem B4224311 : Blo 1877140 4224311 := bstep (se 1 (by rfl) ⟨3168233, by rfl⟩ : syracuseStep 4224311 = 6336467) B6336467
theorem B7616015 : Blo 1877140 7616015 := bstep (se 1 (by rfl) ⟨5712011, by rfl⟩ : syracuseStep 7616015 = 11424023) B11424023
theorem B3167903 : Blo 1877140 3167903 := bstep (se 1 (by rfl) ⟨2375927, by rfl⟩ : syracuseStep 3167903 = 4751855) B4751855
theorem B4012001 : Blo 1877140 4012001 := bstep (se 2 (by rfl) ⟨1504500, by rfl⟩ : syracuseStep 4012001 = 3009001) B3009001
theorem B6019103 : Blo 1877140 6019103 := bstep (se 1 (by rfl) ⟨4514327, by rfl⟩ : syracuseStep 6019103 = 9028655) B9028655
theorem B6339923 : Blo 1877140 6339923 := bstep (se 1 (by rfl) ⟨4754942, by rfl⟩ : syracuseStep 6339923 = 9509885) B9509885
theorem B2817407 : Blo 1877140 2817407 := bstep (se 1 (by rfl) ⟨2113055, by rfl⟩ : syracuseStep 2817407 = 4226111) B4226111
theorem B54894095 : Blo 1877140 54894095 := bstep (se 1 (by rfl) ⟨41170571, by rfl⟩ : syracuseStep 54894095 = 82341143) B82341143
theorem B109739713 : Blo 1877140 109739713 := bstep (se 2 (by rfl) ⟨41152392, by rfl⟩ : syracuseStep 109739713 = 82304785) B82304785
theorem B2817791 : Blo 1877140 2817791 := bstep (se 1 (by rfl) ⟨2113343, by rfl⟩ : syracuseStep 2817791 = 4226687) B4226687
theorem B4226975 : Blo 1877140 4226975 := bstep (se 1 (by rfl) ⟨3170231, by rfl⟩ : syracuseStep 4226975 = 6340463) B6340463
theorem B41157307 : Blo 1877140 41157307 := bstep (se 1 (by rfl) ⟨30867980, by rfl⟩ : syracuseStep 41157307 = 61735961) B61735961
theorem B4227803 : Blo 1877140 4227803 := bstep (se 1 (by rfl) ⟨3170852, by rfl⟩ : syracuseStep 4227803 = 6341705) B6341705
theorem B1878271 : Blo 1877140 1878271 := bstep (se 1 (by rfl) ⟨1408703, by rfl⟩ : syracuseStep 1878271 = 2817407) B2817407
theorem B146319617 : Blo 1877140 146319617 := bstep (se 2 (by rfl) ⟨54869856, by rfl⟩ : syracuseStep 146319617 = 109739713) B109739713
theorem B36596063 : Blo 1877140 36596063 := bstep (se 1 (by rfl) ⟨27447047, by rfl⟩ : syracuseStep 36596063 = 54894095) B54894095
theorem B1878527 : Blo 1877140 1878527 := bstep (se 1 (by rfl) ⟨1408895, by rfl⟩ : syracuseStep 1878527 = 2817791) B2817791
theorem B7129727 : Blo 1877140 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B14257295 : Blo 1877140 14257295 := bstep (se 1 (by rfl) ⟨10692971, by rfl⟩ : syracuseStep 14257295 = 21385943) B21385943
theorem B2674667 : Blo 1877140 2674667 := bstep (se 1 (by rfl) ⟨2006000, by rfl⟩ : syracuseStep 2674667 = 4012001) B4012001
theorem B9024041 : Blo 1877140 9024041 := bstep (se 2 (by rfl) ⟨3384015, by rfl⟩ : syracuseStep 9024041 = 6768031) B6768031
theorem B2816207 : Blo 1877140 2816207 := bstep (se 1 (by rfl) ⟨2112155, by rfl⟩ : syracuseStep 2816207 = 4224311) B4224311
theorem B5077343 : Blo 1877140 5077343 := bstep (se 1 (by rfl) ⟨3808007, by rfl⟩ : syracuseStep 5077343 = 7616015) B7616015
theorem B2111935 : Blo 1877140 2111935 := bstep (se 1 (by rfl) ⟨1583951, by rfl⟩ : syracuseStep 2111935 = 3167903) B3167903
theorem B4012735 : Blo 1877140 4012735 := bstep (se 1 (by rfl) ⟨3009551, by rfl⟩ : syracuseStep 4012735 = 6019103) B6019103
theorem B25697159 : Blo 1877140 25697159 := bstep (se 1 (by rfl) ⟨19272869, by rfl⟩ : syracuseStep 25697159 = 38545739) B38545739
theorem B4226615 : Blo 1877140 4226615 := bstep (se 1 (by rfl) ⟨3169961, by rfl⟩ : syracuseStep 4226615 = 6339923) B6339923
theorem B7429897 : Blo 1877140 7429897 := bstep (se 2 (by rfl) ⟨2786211, by rfl⟩ : syracuseStep 7429897 = 5572423) B5572423
theorem B2817983 : Blo 1877140 2817983 := bstep (se 1 (by rfl) ⟨2113487, by rfl⟩ : syracuseStep 2817983 = 4226975) B4226975
theorem B3170279 : Blo 1877140 3170279 := bstep (se 1 (by rfl) ⟨2377709, by rfl⟩ : syracuseStep 3170279 = 4755419) B4755419
theorem B2818535 : Blo 1877140 2818535 := bstep (se 1 (by rfl) ⟨2113901, by rfl⟩ : syracuseStep 2818535 = 4227803) B4227803
theorem B5350313 : Blo 1877140 5350313 := bstep (se 2 (by rfl) ⟨2006367, by rfl⟩ : syracuseStep 5350313 = 4012735) B4012735
theorem B1877471 : Blo 1877140 1877471 := bstep (se 1 (by rfl) ⟨1408103, by rfl⟩ : syracuseStep 1877471 = 2816207) B2816207
theorem B24397375 : Blo 1877140 24397375 := bstep (se 1 (by rfl) ⟨18298031, by rfl⟩ : syracuseStep 24397375 = 36596063) B36596063
theorem B4753151 : Blo 1877140 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B17131439 : Blo 1877140 17131439 := bstep (se 1 (by rfl) ⟨12848579, by rfl⟩ : syracuseStep 17131439 = 25697159) B25697159
theorem B9504863 : Blo 1877140 9504863 := bstep (se 1 (by rfl) ⟨7128647, by rfl⟩ : syracuseStep 9504863 = 14257295) B14257295
theorem B9906529 : Blo 1877140 9906529 := bstep (se 2 (by rfl) ⟨3714948, by rfl⟩ : syracuseStep 9906529 = 7429897) B7429897
theorem B1878655 : Blo 1877140 1878655 := bstep (se 1 (by rfl) ⟨1408991, by rfl⟩ : syracuseStep 1878655 = 2817983) B2817983
theorem B6016027 : Blo 1877140 6016027 := bstep (se 1 (by rfl) ⟨4512020, by rfl⟩ : syracuseStep 6016027 = 9024041) B9024041
theorem B97546411 : Blo 1877140 97546411 := bstep (se 1 (by rfl) ⟨73159808, by rfl⟩ : syracuseStep 97546411 = 146319617) B146319617
theorem B7132445 : Blo 1877140 7132445 := bstep (se 3 (by rfl) ⟨1337333, by rfl⟩ : syracuseStep 7132445 = 2674667) B2674667
theorem B2815913 : Blo 1877140 2815913 := bstep (se 2 (by rfl) ⟨1055967, by rfl⟩ : syracuseStep 2815913 = 2111935) B2111935
theorem B54876409 : Blo 1877140 54876409 := bstep (se 2 (by rfl) ⟨20578653, by rfl⟩ : syracuseStep 54876409 = 41157307) B41157307
theorem B13539581 : Blo 1877140 13539581 := bstep (se 3 (by rfl) ⟨2538671, by rfl⟩ : syracuseStep 13539581 = 5077343) B5077343
theorem B2817743 : Blo 1877140 2817743 := bstep (se 1 (by rfl) ⟨2113307, by rfl⟩ : syracuseStep 2817743 = 4226615) B4226615
theorem B2113519 : Blo 1877140 2113519 := bstep (se 1 (by rfl) ⟨1585139, by rfl⟩ : syracuseStep 2113519 = 3170279) B3170279
theorem B1877275 : Blo 1877140 1877275 := bstep (se 1 (by rfl) ⟨1407956, by rfl⟩ : syracuseStep 1877275 = 2815913) B2815913
theorem B11420959 : Blo 1877140 11420959 := bstep (se 1 (by rfl) ⟨8565719, by rfl⟩ : syracuseStep 11420959 = 17131439) B17131439
theorem B8021369 : Blo 1877140 8021369 := bstep (se 2 (by rfl) ⟨3008013, by rfl⟩ : syracuseStep 8021369 = 6016027) B6016027
theorem B1878495 : Blo 1877140 1878495 := bstep (se 1 (by rfl) ⟨1408871, by rfl⟩ : syracuseStep 1878495 = 2817743) B2817743
theorem B1879023 : Blo 1877140 1879023 := bstep (se 1 (by rfl) ⟨1409267, by rfl⟩ : syracuseStep 1879023 = 2818535) B2818535
theorem B13208705 : Blo 1877140 13208705 := bstep (se 2 (by rfl) ⟨4953264, by rfl⟩ : syracuseStep 13208705 = 9906529) B9906529
theorem B4754963 : Blo 1877140 4754963 := bstep (se 1 (by rfl) ⟨3566222, by rfl⟩ : syracuseStep 4754963 = 7132445) B7132445
theorem B6336575 : Blo 1877140 6336575 := bstep (se 1 (by rfl) ⟨4752431, by rfl⟩ : syracuseStep 6336575 = 9504863) B9504863
theorem B14267501 : Blo 1877140 14267501 := bstep (se 3 (by rfl) ⟨2675156, by rfl⟩ : syracuseStep 14267501 = 5350313) B5350313
theorem B130061881 : Blo 1877140 130061881 := bstep (se 2 (by rfl) ⟨48773205, by rfl⟩ : syracuseStep 130061881 = 97546411) B97546411
theorem B3168767 : Blo 1877140 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B292674181 : Blo 1877140 292674181 := bstep (se 4 (by rfl) ⟨27438204, by rfl⟩ : syracuseStep 292674181 = 54876409) B54876409
theorem B9026387 : Blo 1877140 9026387 := bstep (se 1 (by rfl) ⟨6769790, by rfl⟩ : syracuseStep 9026387 = 13539581) B13539581
theorem B32529833 : Blo 1877140 32529833 := bstep (se 2 (by rfl) ⟨12198687, by rfl⟩ : syracuseStep 32529833 = 24397375) B24397375
theorem B2818025 : Blo 1877140 2818025 := bstep (se 2 (by rfl) ⟨1056759, by rfl⟩ : syracuseStep 2818025 = 2113519) B2113519
theorem B9511667 : Blo 1877140 9511667 := bstep (se 1 (by rfl) ⟨7133750, by rfl⟩ : syracuseStep 9511667 = 14267501) B14267501
theorem B21390317 : Blo 1877140 21390317 := bstep (se 3 (by rfl) ⟨4010684, by rfl⟩ : syracuseStep 21390317 = 8021369) B8021369
theorem B21686555 : Blo 1877140 21686555 := bstep (se 1 (by rfl) ⟨16264916, by rfl⟩ : syracuseStep 21686555 = 32529833) B32529833
theorem B1878683 : Blo 1877140 1878683 := bstep (se 1 (by rfl) ⟨1409012, by rfl⟩ : syracuseStep 1878683 = 2818025) B2818025
theorem B6017591 : Blo 1877140 6017591 := bstep (se 1 (by rfl) ⟨4513193, by rfl⟩ : syracuseStep 6017591 = 9026387) B9026387
theorem B4224383 : Blo 1877140 4224383 := bstep (se 1 (by rfl) ⟨3168287, by rfl⟩ : syracuseStep 4224383 = 6336575) B6336575
theorem B693663365 : Blo 1877140 693663365 := bstep (se 4 (by rfl) ⟨65030940, by rfl⟩ : syracuseStep 693663365 = 130061881) B130061881
theorem B390232241 : Blo 1877140 390232241 := bstep (se 2 (by rfl) ⟨146337090, by rfl⟩ : syracuseStep 390232241 = 292674181) B292674181
theorem B2112511 : Blo 1877140 2112511 := bstep (se 1 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 2112511 = 3168767) B3168767
theorem B15227945 : Blo 1877140 15227945 := bstep (se 2 (by rfl) ⟨5710479, by rfl⟩ : syracuseStep 15227945 = 11420959) B11420959
theorem B8805803 : Blo 1877140 8805803 := bstep (se 1 (by rfl) ⟨6604352, by rfl⟩ : syracuseStep 8805803 = 13208705) B13208705
theorem B3169975 : Blo 1877140 3169975 := bstep (se 1 (by rfl) ⟨2377481, by rfl⟩ : syracuseStep 3169975 = 4754963) B4754963
theorem B6341111 : Blo 1877140 6341111 := bstep (se 1 (by rfl) ⟨4755833, by rfl⟩ : syracuseStep 6341111 = 9511667) B9511667
theorem B260154827 : Blo 1877140 260154827 := bstep (se 1 (by rfl) ⟨195116120, by rfl⟩ : syracuseStep 260154827 = 390232241) B390232241
theorem B10151963 : Blo 1877140 10151963 := bstep (se 1 (by rfl) ⟨7613972, by rfl⟩ : syracuseStep 10151963 = 15227945) B15227945
theorem B462442243 : Blo 1877140 462442243 := bstep (se 1 (by rfl) ⟨346831682, by rfl⟩ : syracuseStep 462442243 = 693663365) B693663365
theorem B14260211 : Blo 1877140 14260211 := bstep (se 1 (by rfl) ⟨10695158, by rfl⟩ : syracuseStep 14260211 = 21390317) B21390317
theorem B2816255 : Blo 1877140 2816255 := bstep (se 1 (by rfl) ⟨2112191, by rfl⟩ : syracuseStep 2816255 = 4224383) B4224383
theorem B2816681 : Blo 1877140 2816681 := bstep (se 2 (by rfl) ⟨1056255, by rfl⟩ : syracuseStep 2816681 = 2112511) B2112511
theorem B16046909 : Blo 1877140 16046909 := bstep (se 3 (by rfl) ⟨3008795, by rfl⟩ : syracuseStep 16046909 = 6017591) B6017591
theorem B14457703 : Blo 1877140 14457703 := bstep (se 1 (by rfl) ⟨10843277, by rfl⟩ : syracuseStep 14457703 = 21686555) B21686555
theorem B93928565 : Blo 1877140 93928565 := bstep (se 5 (by rfl) ⟨4402901, by rfl⟩ : syracuseStep 93928565 = 8805803) B8805803
theorem B4226633 : Blo 1877140 4226633 := bstep (se 2 (by rfl) ⟨1584987, by rfl⟩ : syracuseStep 4226633 = 3169975) B3169975
theorem B4227407 : Blo 1877140 4227407 := bstep (se 1 (by rfl) ⟨3170555, by rfl⟩ : syracuseStep 4227407 = 6341111) B6341111
theorem B19276937 : Blo 1877140 19276937 := bstep (se 2 (by rfl) ⟨7228851, by rfl⟩ : syracuseStep 19276937 = 14457703) B14457703
theorem B6767975 : Blo 1877140 6767975 := bstep (se 1 (by rfl) ⟨5075981, by rfl⟩ : syracuseStep 6767975 = 10151963) B10151963
theorem B1877503 : Blo 1877140 1877503 := bstep (se 1 (by rfl) ⟨1408127, by rfl⟩ : syracuseStep 1877503 = 2816255) B2816255
theorem B1877787 : Blo 1877140 1877787 := bstep (se 1 (by rfl) ⟨1408340, by rfl⟩ : syracuseStep 1877787 = 2816681) B2816681
theorem B616589657 : Blo 1877140 616589657 := bstep (se 2 (by rfl) ⟨231221121, by rfl⟩ : syracuseStep 616589657 = 462442243) B462442243
theorem B173436551 : Blo 1877140 173436551 := bstep (se 1 (by rfl) ⟨130077413, by rfl⟩ : syracuseStep 173436551 = 260154827) B260154827
theorem B9506807 : Blo 1877140 9506807 := bstep (se 1 (by rfl) ⟨7130105, by rfl⟩ : syracuseStep 9506807 = 14260211) B14260211
theorem B10697939 : Blo 1877140 10697939 := bstep (se 1 (by rfl) ⟨8023454, by rfl⟩ : syracuseStep 10697939 = 16046909) B16046909
theorem B62619043 : Blo 1877140 62619043 := bstep (se 1 (by rfl) ⟨46964282, by rfl⟩ : syracuseStep 62619043 = 93928565) B93928565
theorem B2817755 : Blo 1877140 2817755 := bstep (se 1 (by rfl) ⟨2113316, by rfl⟩ : syracuseStep 2817755 = 4226633) B4226633
theorem B2818271 : Blo 1877140 2818271 := bstep (se 1 (by rfl) ⟨2113703, by rfl⟩ : syracuseStep 2818271 = 4227407) B4227407
theorem B411059771 : Blo 1877140 411059771 := bstep (se 1 (by rfl) ⟨308294828, by rfl⟩ : syracuseStep 411059771 = 616589657) B616589657
theorem B115624367 : Blo 1877140 115624367 := bstep (se 1 (by rfl) ⟨86718275, by rfl⟩ : syracuseStep 115624367 = 173436551) B173436551
theorem B1878503 : Blo 1877140 1878503 := bstep (se 1 (by rfl) ⟨1408877, by rfl⟩ : syracuseStep 1878503 = 2817755) B2817755
theorem B7131959 : Blo 1877140 7131959 := bstep (se 1 (by rfl) ⟨5348969, by rfl⟩ : syracuseStep 7131959 = 10697939) B10697939
theorem B6337871 : Blo 1877140 6337871 := bstep (se 1 (by rfl) ⟨4753403, by rfl⟩ : syracuseStep 6337871 = 9506807) B9506807
theorem B12851291 : Blo 1877140 12851291 := bstep (se 1 (by rfl) ⟨9638468, by rfl⟩ : syracuseStep 12851291 = 19276937) B19276937
theorem B4511983 : Blo 1877140 4511983 := bstep (se 1 (by rfl) ⟨3383987, by rfl⟩ : syracuseStep 4511983 = 6767975) B6767975
theorem B83492057 : Blo 1877140 83492057 := bstep (se 2 (by rfl) ⟨31309521, by rfl⟩ : syracuseStep 83492057 = 62619043) B62619043
theorem B274039847 : Blo 1877140 274039847 := bstep (se 1 (by rfl) ⟨205529885, by rfl⟩ : syracuseStep 274039847 = 411059771) B411059771
theorem B1878847 : Blo 1877140 1878847 := bstep (se 1 (by rfl) ⟨1409135, by rfl⟩ : syracuseStep 1878847 = 2818271) B2818271
theorem B6015977 : Blo 1877140 6015977 := bstep (se 2 (by rfl) ⟨2255991, by rfl⟩ : syracuseStep 6015977 = 4511983) B4511983
theorem B4754639 : Blo 1877140 4754639 := bstep (se 1 (by rfl) ⟨3565979, by rfl⟩ : syracuseStep 4754639 = 7131959) B7131959
theorem B222645485 : Blo 1877140 222645485 := bstep (se 3 (by rfl) ⟨41746028, by rfl⟩ : syracuseStep 222645485 = 83492057) B83492057
theorem B77082911 : Blo 1877140 77082911 := bstep (se 1 (by rfl) ⟨57812183, by rfl⟩ : syracuseStep 77082911 = 115624367) B115624367
theorem B4225247 : Blo 1877140 4225247 := bstep (se 1 (by rfl) ⟨3168935, by rfl⟩ : syracuseStep 4225247 = 6337871) B6337871
theorem B8567527 : Blo 1877140 8567527 := bstep (se 1 (by rfl) ⟨6425645, by rfl⟩ : syracuseStep 8567527 = 12851291) B12851291
theorem B51388607 : Blo 1877140 51388607 := bstep (se 1 (by rfl) ⟨38541455, by rfl⟩ : syracuseStep 51388607 = 77082911) B77082911
theorem B182693231 : Blo 1877140 182693231 := bstep (se 1 (by rfl) ⟨137019923, by rfl⟩ : syracuseStep 182693231 = 274039847) B274039847
theorem B11423369 : Blo 1877140 11423369 := bstep (se 2 (by rfl) ⟨4283763, by rfl⟩ : syracuseStep 11423369 = 8567527) B8567527
theorem B4010651 : Blo 1877140 4010651 := bstep (se 1 (by rfl) ⟨3007988, by rfl⟩ : syracuseStep 4010651 = 6015977) B6015977
theorem B2816831 : Blo 1877140 2816831 := bstep (se 1 (by rfl) ⟨2112623, by rfl⟩ : syracuseStep 2816831 = 4225247) B4225247
theorem B3169759 : Blo 1877140 3169759 := bstep (se 1 (by rfl) ⟨2377319, by rfl⟩ : syracuseStep 3169759 = 4754639) B4754639
theorem B148430323 : Blo 1877140 148430323 := bstep (se 1 (by rfl) ⟨111322742, by rfl⟩ : syracuseStep 148430323 = 222645485) B222645485
theorem B34259071 : Blo 1877140 34259071 := bstep (se 1 (by rfl) ⟨25694303, by rfl⟩ : syracuseStep 34259071 = 51388607) B51388607
theorem B1877887 : Blo 1877140 1877887 := bstep (se 1 (by rfl) ⟨1408415, by rfl⟩ : syracuseStep 1877887 = 2816831) B2816831
theorem B2673767 : Blo 1877140 2673767 := bstep (se 1 (by rfl) ⟨2005325, by rfl⟩ : syracuseStep 2673767 = 4010651) B4010651
theorem B197907097 : Blo 1877140 197907097 := bstep (se 2 (by rfl) ⟨74215161, by rfl⟩ : syracuseStep 197907097 = 148430323) B148430323
theorem B121795487 : Blo 1877140 121795487 := bstep (se 1 (by rfl) ⟨91346615, by rfl⟩ : syracuseStep 121795487 = 182693231) B182693231
theorem B7615579 : Blo 1877140 7615579 := bstep (se 1 (by rfl) ⟨5711684, by rfl⟩ : syracuseStep 7615579 = 11423369) B11423369
theorem B4226345 : Blo 1877140 4226345 := bstep (se 2 (by rfl) ⟨1584879, by rfl⟩ : syracuseStep 4226345 = 3169759) B3169759
theorem B45678761 : Blo 1877140 45678761 := bstep (se 2 (by rfl) ⟨17129535, by rfl⟩ : syracuseStep 45678761 = 34259071) B34259071
theorem B7130045 : Blo 1877140 7130045 := bstep (se 3 (by rfl) ⟨1336883, by rfl⟩ : syracuseStep 7130045 = 2673767) B2673767
theorem B263876129 : Blo 1877140 263876129 := bstep (se 2 (by rfl) ⟨98953548, by rfl⟩ : syracuseStep 263876129 = 197907097) B197907097
theorem B10154105 : Blo 1877140 10154105 := bstep (se 2 (by rfl) ⟨3807789, by rfl⟩ : syracuseStep 10154105 = 7615579) B7615579
theorem B81196991 : Blo 1877140 81196991 := bstep (se 1 (by rfl) ⟨60897743, by rfl⟩ : syracuseStep 81196991 = 121795487) B121795487
theorem B2817563 : Blo 1877140 2817563 := bstep (se 1 (by rfl) ⟨2113172, by rfl⟩ : syracuseStep 2817563 = 4226345) B4226345
theorem B4753363 : Blo 1877140 4753363 := bstep (se 1 (by rfl) ⟨3565022, by rfl⟩ : syracuseStep 4753363 = 7130045) B7130045
theorem B1878375 : Blo 1877140 1878375 := bstep (se 1 (by rfl) ⟨1408781, by rfl⟩ : syracuseStep 1878375 = 2817563) B2817563
theorem B175917419 : Blo 1877140 175917419 := bstep (se 1 (by rfl) ⟨131938064, by rfl⟩ : syracuseStep 175917419 = 263876129) B263876129
theorem B6769403 : Blo 1877140 6769403 := bstep (se 1 (by rfl) ⟨5077052, by rfl⟩ : syracuseStep 6769403 = 10154105) B10154105
theorem B30452507 : Blo 1877140 30452507 := bstep (se 1 (by rfl) ⟨22839380, by rfl⟩ : syracuseStep 30452507 = 45678761) B45678761
theorem B54131327 : Blo 1877140 54131327 := bstep (se 1 (by rfl) ⟨40598495, by rfl⟩ : syracuseStep 54131327 = 81196991) B81196991
theorem B117278279 : Blo 1877140 117278279 := bstep (se 1 (by rfl) ⟨87958709, by rfl⟩ : syracuseStep 117278279 = 175917419) B175917419
theorem B36087551 : Blo 1877140 36087551 := bstep (se 1 (by rfl) ⟨27065663, by rfl⟩ : syracuseStep 36087551 = 54131327) B54131327
theorem B20301671 : Blo 1877140 20301671 := bstep (se 1 (by rfl) ⟨15226253, by rfl⟩ : syracuseStep 20301671 = 30452507) B30452507
theorem B6337817 : Blo 1877140 6337817 := bstep (se 2 (by rfl) ⟨2376681, by rfl⟩ : syracuseStep 6337817 = 4753363) B4753363
theorem B4512935 : Blo 1877140 4512935 := bstep (se 1 (by rfl) ⟨3384701, by rfl⟩ : syracuseStep 4512935 = 6769403) B6769403
theorem B12034493 : Blo 1877140 12034493 := bstep (se 3 (by rfl) ⟨2256467, by rfl⟩ : syracuseStep 12034493 = 4512935) B4512935
theorem B78185519 : Blo 1877140 78185519 := bstep (se 1 (by rfl) ⟨58639139, by rfl⟩ : syracuseStep 78185519 = 117278279) B117278279
theorem B13534447 : Blo 1877140 13534447 := bstep (se 1 (by rfl) ⟨10150835, by rfl⟩ : syracuseStep 13534447 = 20301671) B20301671
theorem B4225211 : Blo 1877140 4225211 := bstep (se 1 (by rfl) ⟨3168908, by rfl⟩ : syracuseStep 4225211 = 6337817) B6337817
theorem B24058367 : Blo 1877140 24058367 := bstep (se 1 (by rfl) ⟨18043775, by rfl⟩ : syracuseStep 24058367 = 36087551) B36087551
theorem B8022995 : Blo 1877140 8022995 := bstep (se 1 (by rfl) ⟨6017246, by rfl⟩ : syracuseStep 8022995 = 12034493) B12034493
theorem B52123679 : Blo 1877140 52123679 := bstep (se 1 (by rfl) ⟨39092759, by rfl⟩ : syracuseStep 52123679 = 78185519) B78185519
theorem B2816807 : Blo 1877140 2816807 := bstep (se 1 (by rfl) ⟨2112605, by rfl⟩ : syracuseStep 2816807 = 4225211) B4225211
theorem B18045929 : Blo 1877140 18045929 := bstep (se 2 (by rfl) ⟨6767223, by rfl⟩ : syracuseStep 18045929 = 13534447) B13534447
theorem B16038911 : Blo 1877140 16038911 := bstep (se 1 (by rfl) ⟨12029183, by rfl⟩ : syracuseStep 16038911 = 24058367) B24058367
theorem B1877871 : Blo 1877140 1877871 := bstep (se 1 (by rfl) ⟨1408403, by rfl⟩ : syracuseStep 1877871 = 2816807) B2816807
theorem B10692607 : Blo 1877140 10692607 := bstep (se 1 (by rfl) ⟨8019455, by rfl⟩ : syracuseStep 10692607 = 16038911) B16038911
theorem B12030619 : Blo 1877140 12030619 := bstep (se 1 (by rfl) ⟨9022964, by rfl⟩ : syracuseStep 12030619 = 18045929) B18045929
theorem B34749119 : Blo 1877140 34749119 := bstep (se 1 (by rfl) ⟨26061839, by rfl⟩ : syracuseStep 34749119 = 52123679) B52123679
theorem B5348663 : Blo 1877140 5348663 := bstep (se 1 (by rfl) ⟨4011497, by rfl⟩ : syracuseStep 5348663 = 8022995) B8022995
theorem B16040825 : Blo 1877140 16040825 := bstep (se 2 (by rfl) ⟨6015309, by rfl⟩ : syracuseStep 16040825 = 12030619) B12030619
theorem B3565775 : Blo 1877140 3565775 := bstep (se 1 (by rfl) ⟨2674331, by rfl⟩ : syracuseStep 3565775 = 5348663) B5348663
theorem B14256809 : Blo 1877140 14256809 := bstep (se 2 (by rfl) ⟨5346303, by rfl⟩ : syracuseStep 14256809 = 10692607) B10692607
theorem B92664317 : Blo 1877140 92664317 := bstep (se 3 (by rfl) ⟨17374559, by rfl⟩ : syracuseStep 92664317 = 34749119) B34749119
theorem B61776211 : Blo 1877140 61776211 := bstep (se 1 (by rfl) ⟨46332158, by rfl⟩ : syracuseStep 61776211 = 92664317) B92664317
theorem B2377183 : Blo 1877140 2377183 := bstep (se 1 (by rfl) ⟨1782887, by rfl⟩ : syracuseStep 2377183 = 3565775) B3565775
theorem B9504539 : Blo 1877140 9504539 := bstep (se 1 (by rfl) ⟨7128404, by rfl⟩ : syracuseStep 9504539 = 14256809) B14256809
theorem B10693883 : Blo 1877140 10693883 := bstep (se 1 (by rfl) ⟨8020412, by rfl⟩ : syracuseStep 10693883 = 16040825) B16040825
theorem B7129255 : Blo 1877140 7129255 := bstep (se 1 (by rfl) ⟨5346941, by rfl⟩ : syracuseStep 7129255 = 10693883) B10693883
theorem B6336359 : Blo 1877140 6336359 := bstep (se 1 (by rfl) ⟨4752269, by rfl⟩ : syracuseStep 6336359 = 9504539) B9504539
theorem B82368281 : Blo 1877140 82368281 := bstep (se 2 (by rfl) ⟨30888105, by rfl⟩ : syracuseStep 82368281 = 61776211) B61776211
theorem B3169577 : Blo 1877140 3169577 := bstep (se 2 (by rfl) ⟨1188591, by rfl⟩ : syracuseStep 3169577 = 2377183) B2377183
theorem B54912187 : Blo 1877140 54912187 := bstep (se 1 (by rfl) ⟨41184140, by rfl⟩ : syracuseStep 54912187 = 82368281) B82368281
theorem B9505673 : Blo 1877140 9505673 := bstep (se 2 (by rfl) ⟨3564627, by rfl⟩ : syracuseStep 9505673 = 7129255) B7129255
theorem B4224239 : Blo 1877140 4224239 := bstep (se 1 (by rfl) ⟨3168179, by rfl⟩ : syracuseStep 4224239 = 6336359) B6336359
theorem B2113051 : Blo 1877140 2113051 := bstep (se 1 (by rfl) ⟨1584788, by rfl⟩ : syracuseStep 2113051 = 3169577) B3169577
theorem B292864997 : Blo 1877140 292864997 := bstep (se 4 (by rfl) ⟨27456093, by rfl⟩ : syracuseStep 292864997 = 54912187) B54912187
theorem B6337115 : Blo 1877140 6337115 := bstep (se 1 (by rfl) ⟨4752836, by rfl⟩ : syracuseStep 6337115 = 9505673) B9505673
theorem B2816159 : Blo 1877140 2816159 := bstep (se 1 (by rfl) ⟨2112119, by rfl⟩ : syracuseStep 2816159 = 4224239) B4224239
theorem B2817401 : Blo 1877140 2817401 := bstep (se 2 (by rfl) ⟨1056525, by rfl⟩ : syracuseStep 2817401 = 2113051) B2113051
theorem B1877439 : Blo 1877140 1877439 := bstep (se 1 (by rfl) ⟨1408079, by rfl⟩ : syracuseStep 1877439 = 2816159) B2816159
theorem B1878267 : Blo 1877140 1878267 := bstep (se 1 (by rfl) ⟨1408700, by rfl⟩ : syracuseStep 1878267 = 2817401) B2817401
theorem B195243331 : Blo 1877140 195243331 := bstep (se 1 (by rfl) ⟨146432498, by rfl⟩ : syracuseStep 195243331 = 292864997) B292864997
theorem B4224743 : Blo 1877140 4224743 := bstep (se 1 (by rfl) ⟨3168557, by rfl⟩ : syracuseStep 4224743 = 6337115) B6337115
theorem B2816495 : Blo 1877140 2816495 := bstep (se 1 (by rfl) ⟨2112371, by rfl⟩ : syracuseStep 2816495 = 4224743) B4224743
theorem B260324441 : Blo 1877140 260324441 := bstep (se 2 (by rfl) ⟨97621665, by rfl⟩ : syracuseStep 260324441 = 195243331) B195243331
theorem B1877663 : Blo 1877140 1877663 := bstep (se 1 (by rfl) ⟨1408247, by rfl⟩ : syracuseStep 1877663 = 2816495) B2816495
theorem B173549627 : Blo 1877140 173549627 := bstep (se 1 (by rfl) ⟨130162220, by rfl⟩ : syracuseStep 173549627 = 260324441) B260324441
theorem B115699751 : Blo 1877140 115699751 := bstep (se 1 (by rfl) ⟨86774813, by rfl⟩ : syracuseStep 115699751 = 173549627) B173549627
theorem B77133167 : Blo 1877140 77133167 := bstep (se 1 (by rfl) ⟨57849875, by rfl⟩ : syracuseStep 77133167 = 115699751) B115699751
theorem B51422111 : Blo 1877140 51422111 := bstep (se 1 (by rfl) ⟨38566583, by rfl⟩ : syracuseStep 51422111 = 77133167) B77133167
theorem B34281407 : Blo 1877140 34281407 := bstep (se 1 (by rfl) ⟨25711055, by rfl⟩ : syracuseStep 34281407 = 51422111) B51422111
theorem B22854271 : Blo 1877140 22854271 := bstep (se 1 (by rfl) ⟨17140703, by rfl⟩ : syracuseStep 22854271 = 34281407) B34281407
theorem B30472361 : Blo 1877140 30472361 := bstep (se 2 (by rfl) ⟨11427135, by rfl⟩ : syracuseStep 30472361 = 22854271) B22854271
theorem B20314907 : Blo 1877140 20314907 := bstep (se 1 (by rfl) ⟨15236180, by rfl⟩ : syracuseStep 20314907 = 30472361) B30472361
theorem B13543271 : Blo 1877140 13543271 := bstep (se 1 (by rfl) ⟨10157453, by rfl⟩ : syracuseStep 13543271 = 20314907) B20314907
theorem B9028847 : Blo 1877140 9028847 := bstep (se 1 (by rfl) ⟨6771635, by rfl⟩ : syracuseStep 9028847 = 13543271) B13543271
theorem B24076925 : Blo 1877140 24076925 := bstep (se 3 (by rfl) ⟨4514423, by rfl⟩ : syracuseStep 24076925 = 9028847) B9028847
theorem B16051283 : Blo 1877140 16051283 := bstep (se 1 (by rfl) ⟨12038462, by rfl⟩ : syracuseStep 16051283 = 24076925) B24076925
theorem B10700855 : Blo 1877140 10700855 := bstep (se 1 (by rfl) ⟨8025641, by rfl⟩ : syracuseStep 10700855 = 16051283) B16051283
theorem B7133903 : Blo 1877140 7133903 := bstep (se 1 (by rfl) ⟨5350427, by rfl⟩ : syracuseStep 7133903 = 10700855) B10700855
theorem B4755935 : Blo 1877140 4755935 := bstep (se 1 (by rfl) ⟨3566951, by rfl⟩ : syracuseStep 4755935 = 7133903) B7133903
theorem B3170623 : Blo 1877140 3170623 := bstep (se 1 (by rfl) ⟨2377967, by rfl⟩ : syracuseStep 3170623 = 4755935) B4755935
theorem B4227497 : Blo 1877140 4227497 := bstep (se 2 (by rfl) ⟨1585311, by rfl⟩ : syracuseStep 4227497 = 3170623) B3170623
theorem B2818331 : Blo 1877140 2818331 := bstep (se 1 (by rfl) ⟨2113748, by rfl⟩ : syracuseStep 2818331 = 4227497) B4227497
theorem B1878887 : Blo 1877140 1878887 := bstep (se 1 (by rfl) ⟨1409165, by rfl⟩ : syracuseStep 1878887 = 2818331) B2818331

theorem C0 (j : ℕ) (h1 : 469285 ≤ j) (h2 : j ≤ 469784) : Blo 1877140 (4 * j + 3) := by
  interval_cases j
  · exact B1877143
  · exact B1877147
  · exact B1877151
  · exact B1877155
  · exact B1877159
  · exact B1877163
  · exact B1877167
  · exact B1877171
  · exact B1877175
  · exact B1877179
  · exact B1877183
  · exact B1877187
  · exact B1877191
  · exact B1877195
  · exact B1877199
  · exact B1877203
  · exact B1877207
  · exact B1877211
  · exact B1877215
  · exact B1877219
  · exact B1877223
  · exact B1877227
  · exact B1877231
  · exact B1877235
  · exact B1877239
  · exact B1877243
  · exact B1877247
  · exact B1877251
  · exact B1877255
  · exact B1877259
  · exact B1877263
  · exact B1877267
  · exact B1877271
  · exact B1877275
  · exact B1877279
  · exact B1877283
  · exact B1877287
  · exact B1877291
  · exact B1877295
  · exact B1877299
  · exact B1877303
  · exact B1877307
  · exact B1877311
  · exact B1877315
  · exact B1877319
  · exact B1877323
  · exact B1877327
  · exact B1877331
  · exact B1877335
  · exact B1877339
  · exact B1877343
  · exact B1877347
  · exact B1877351
  · exact B1877355
  · exact B1877359
  · exact B1877363
  · exact B1877367
  · exact B1877371
  · exact B1877375
  · exact B1877379
  · exact B1877383
  · exact B1877387
  · exact B1877391
  · exact B1877395
  · exact B1877399
  · exact B1877403
  · exact B1877407
  · exact B1877411
  · exact B1877415
  · exact B1877419
  · exact B1877423
  · exact B1877427
  · exact B1877431
  · exact B1877435
  · exact B1877439
  · exact B1877443
  · exact B1877447
  · exact B1877451
  · exact B1877455
  · exact B1877459
  · exact B1877463
  · exact B1877467
  · exact B1877471
  · exact B1877475
  · exact B1877479
  · exact B1877483
  · exact B1877487
  · exact B1877491
  · exact B1877495
  · exact B1877499
  · exact B1877503
  · exact B1877507
  · exact B1877511
  · exact B1877515
  · exact B1877519
  · exact B1877523
  · exact B1877527
  · exact B1877531
  · exact B1877535
  · exact B1877539
  · exact B1877543
  · exact B1877547
  · exact B1877551
  · exact B1877555
  · exact B1877559
  · exact B1877563
  · exact B1877567
  · exact B1877571
  · exact B1877575
  · exact B1877579
  · exact B1877583
  · exact B1877587
  · exact B1877591
  · exact B1877595
  · exact B1877599
  · exact B1877603
  · exact B1877607
  · exact B1877611
  · exact B1877615
  · exact B1877619
  · exact B1877623
  · exact B1877627
  · exact B1877631
  · exact B1877635
  · exact B1877639
  · exact B1877643
  · exact B1877647
  · exact B1877651
  · exact B1877655
  · exact B1877659
  · exact B1877663
  · exact B1877667
  · exact B1877671
  · exact B1877675
  · exact B1877679
  · exact B1877683
  · exact B1877687
  · exact B1877691
  · exact B1877695
  · exact B1877699
  · exact B1877703
  · exact B1877707
  · exact B1877711
  · exact B1877715
  · exact B1877719
  · exact B1877723
  · exact B1877727
  · exact B1877731
  · exact B1877735
  · exact B1877739
  · exact B1877743
  · exact B1877747
  · exact B1877751
  · exact B1877755
  · exact B1877759
  · exact B1877763
  · exact B1877767
  · exact B1877771
  · exact B1877775
  · exact B1877779
  · exact B1877783
  · exact B1877787
  · exact B1877791
  · exact B1877795
  · exact B1877799
  · exact B1877803
  · exact B1877807
  · exact B1877811
  · exact B1877815
  · exact B1877819
  · exact B1877823
  · exact B1877827
  · exact B1877831
  · exact B1877835
  · exact B1877839
  · exact B1877843
  · exact B1877847
  · exact B1877851
  · exact B1877855
  · exact B1877859
  · exact B1877863
  · exact B1877867
  · exact B1877871
  · exact B1877875
  · exact B1877879
  · exact B1877883
  · exact B1877887
  · exact B1877891
  · exact B1877895
  · exact B1877899
  · exact B1877903
  · exact B1877907
  · exact B1877911
  · exact B1877915
  · exact B1877919
  · exact B1877923
  · exact B1877927
  · exact B1877931
  · exact B1877935
  · exact B1877939
  · exact B1877943
  · exact B1877947
  · exact B1877951
  · exact B1877955
  · exact B1877959
  · exact B1877963
  · exact B1877967
  · exact B1877971
  · exact B1877975
  · exact B1877979
  · exact B1877983
  · exact B1877987
  · exact B1877991
  · exact B1877995
  · exact B1877999
  · exact B1878003
  · exact B1878007
  · exact B1878011
  · exact B1878015
  · exact B1878019
  · exact B1878023
  · exact B1878027
  · exact B1878031
  · exact B1878035
  · exact B1878039
  · exact B1878043
  · exact B1878047
  · exact B1878051
  · exact B1878055
  · exact B1878059
  · exact B1878063
  · exact B1878067
  · exact B1878071
  · exact B1878075
  · exact B1878079
  · exact B1878083
  · exact B1878087
  · exact B1878091
  · exact B1878095
  · exact B1878099
  · exact B1878103
  · exact B1878107
  · exact B1878111
  · exact B1878115
  · exact B1878119
  · exact B1878123
  · exact B1878127
  · exact B1878131
  · exact B1878135
  · exact B1878139
  · exact B1878143
  · exact B1878147
  · exact B1878151
  · exact B1878155
  · exact B1878159
  · exact B1878163
  · exact B1878167
  · exact B1878171
  · exact B1878175
  · exact B1878179
  · exact B1878183
  · exact B1878187
  · exact B1878191
  · exact B1878195
  · exact B1878199
  · exact B1878203
  · exact B1878207
  · exact B1878211
  · exact B1878215
  · exact B1878219
  · exact B1878223
  · exact B1878227
  · exact B1878231
  · exact B1878235
  · exact B1878239
  · exact B1878243
  · exact B1878247
  · exact B1878251
  · exact B1878255
  · exact B1878259
  · exact B1878263
  · exact B1878267
  · exact B1878271
  · exact B1878275
  · exact B1878279
  · exact B1878283
  · exact B1878287
  · exact B1878291
  · exact B1878295
  · exact B1878299
  · exact B1878303
  · exact B1878307
  · exact B1878311
  · exact B1878315
  · exact B1878319
  · exact B1878323
  · exact B1878327
  · exact B1878331
  · exact B1878335
  · exact B1878339
  · exact B1878343
  · exact B1878347
  · exact B1878351
  · exact B1878355
  · exact B1878359
  · exact B1878363
  · exact B1878367
  · exact B1878371
  · exact B1878375
  · exact B1878379
  · exact B1878383
  · exact B1878387
  · exact B1878391
  · exact B1878395
  · exact B1878399
  · exact B1878403
  · exact B1878407
  · exact B1878411
  · exact B1878415
  · exact B1878419
  · exact B1878423
  · exact B1878427
  · exact B1878431
  · exact B1878435
  · exact B1878439
  · exact B1878443
  · exact B1878447
  · exact B1878451
  · exact B1878455
  · exact B1878459
  · exact B1878463
  · exact B1878467
  · exact B1878471
  · exact B1878475
  · exact B1878479
  · exact B1878483
  · exact B1878487
  · exact B1878491
  · exact B1878495
  · exact B1878499
  · exact B1878503
  · exact B1878507
  · exact B1878511
  · exact B1878515
  · exact B1878519
  · exact B1878523
  · exact B1878527
  · exact B1878531
  · exact B1878535
  · exact B1878539
  · exact B1878543
  · exact B1878547
  · exact B1878551
  · exact B1878555
  · exact B1878559
  · exact B1878563
  · exact B1878567
  · exact B1878571
  · exact B1878575
  · exact B1878579
  · exact B1878583
  · exact B1878587
  · exact B1878591
  · exact B1878595
  · exact B1878599
  · exact B1878603
  · exact B1878607
  · exact B1878611
  · exact B1878615
  · exact B1878619
  · exact B1878623
  · exact B1878627
  · exact B1878631
  · exact B1878635
  · exact B1878639
  · exact B1878643
  · exact B1878647
  · exact B1878651
  · exact B1878655
  · exact B1878659
  · exact B1878663
  · exact B1878667
  · exact B1878671
  · exact B1878675
  · exact B1878679
  · exact B1878683
  · exact B1878687
  · exact B1878691
  · exact B1878695
  · exact B1878699
  · exact B1878703
  · exact B1878707
  · exact B1878711
  · exact B1878715
  · exact B1878719
  · exact B1878723
  · exact B1878727
  · exact B1878731
  · exact B1878735
  · exact B1878739
  · exact B1878743
  · exact B1878747
  · exact B1878751
  · exact B1878755
  · exact B1878759
  · exact B1878763
  · exact B1878767
  · exact B1878771
  · exact B1878775
  · exact B1878779
  · exact B1878783
  · exact B1878787
  · exact B1878791
  · exact B1878795
  · exact B1878799
  · exact B1878803
  · exact B1878807
  · exact B1878811
  · exact B1878815
  · exact B1878819
  · exact B1878823
  · exact B1878827
  · exact B1878831
  · exact B1878835
  · exact B1878839
  · exact B1878843
  · exact B1878847
  · exact B1878851
  · exact B1878855
  · exact B1878859
  · exact B1878863
  · exact B1878867
  · exact B1878871
  · exact B1878875
  · exact B1878879
  · exact B1878883
  · exact B1878887
  · exact B1878891
  · exact B1878895
  · exact B1878899
  · exact B1878903
  · exact B1878907
  · exact B1878911
  · exact B1878915
  · exact B1878919
  · exact B1878923
  · exact B1878927
  · exact B1878931
  · exact B1878935
  · exact B1878939
  · exact B1878943
  · exact B1878947
  · exact B1878951
  · exact B1878955
  · exact B1878959
  · exact B1878963
  · exact B1878967
  · exact B1878971
  · exact B1878975
  · exact B1878979
  · exact B1878983
  · exact B1878987
  · exact B1878991
  · exact B1878995
  · exact B1878999
  · exact B1879003
  · exact B1879007
  · exact B1879011
  · exact B1879015
  · exact B1879019
  · exact B1879023
  · exact B1879027
  · exact B1879031
  · exact B1879035
  · exact B1879039
  · exact B1879043
  · exact B1879047
  · exact B1879051
  · exact B1879055
  · exact B1879059
  · exact B1879063
  · exact B1879067
  · exact B1879071
  · exact B1879075
  · exact B1879079
  · exact B1879083
  · exact B1879087
  · exact B1879091
  · exact B1879095
  · exact B1879099
  · exact B1879103
  · exact B1879107
  · exact B1879111
  · exact B1879115
  · exact B1879119
  · exact B1879123
  · exact B1879127
  · exact B1879131
  · exact B1879135
  · exact B1879139

theorem solution (m : ℕ) (hlo : 1877140 ≤ m) (hhi : m ≤ 1879140) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 469285 ≤ j := by omega
    have hj2 : j ≤ 469784 := by omega
    have hb : Blo 1877140 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
