-- Prove2me | solution 1 for syracuse_descends_range_1711056_1713056
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:27:49.506543+00:00
-- url     : https://prove2.me/submissions/dd369df8-c6a3-4a2d-ba56-2127e61ab6ee

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


theorem B3850253 : Blo 1711056 3850253 := bbase (se 3 (by rfl) ⟨721922, by rfl⟩ : syracuseStep 3850253 = 1443845) (by norm_num)
theorem B1925149 : Blo 1711056 1925149 := bbase (se 3 (by rfl) ⟨360965, by rfl⟩ : syracuseStep 1925149 = 721931) (by norm_num)
theorem B3293237 : Blo 1711056 3293237 := bbase (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) (by norm_num)
theorem B4333621 : Blo 1711056 4333621 := bbase (se 5 (by rfl) ⟨203138, by rfl⟩ : syracuseStep 4333621 = 406277) (by norm_num)
theorem B1925185 : Blo 1711056 1925185 := bbase (se 2 (by rfl) ⟨721944, by rfl⟩ : syracuseStep 1925185 = 1443889) (by norm_num)
theorem B3850325 : Blo 1711056 3850325 := bbase (se 8 (by rfl) ⟨22560, by rfl⟩ : syracuseStep 3850325 = 45121) (by norm_num)
theorem B5775461 : Blo 1711056 5775461 := bbase (se 4 (by rfl) ⟨541449, by rfl⟩ : syracuseStep 5775461 = 1082899) (by norm_num)
theorem B1925221 : Blo 1711056 1925221 := bbase (se 4 (by rfl) ⟨180489, by rfl⟩ : syracuseStep 1925221 = 360979) (by norm_num)
theorem B4874357 : Blo 1711056 4874357 := bbase (se 5 (by rfl) ⟨228485, by rfl⟩ : syracuseStep 4874357 = 456971) (by norm_num)
theorem B1925257 : Blo 1711056 1925257 := bbase (se 2 (by rfl) ⟨721971, by rfl⟩ : syracuseStep 1925257 = 1443943) (by norm_num)
theorem B3850397 : Blo 1711056 3850397 := bbase (se 3 (by rfl) ⟨721949, by rfl⟩ : syracuseStep 3850397 = 1443899) (by norm_num)
theorem B4333733 : Blo 1711056 4333733 := bbase (se 4 (by rfl) ⟨406287, by rfl⟩ : syracuseStep 4333733 = 812575) (by norm_num)
theorem B1925293 : Blo 1711056 1925293 := bbase (se 3 (by rfl) ⟨360992, by rfl⟩ : syracuseStep 1925293 = 721985) (by norm_num)
theorem B1925329 : Blo 1711056 1925329 := bbase (se 2 (by rfl) ⟨721998, by rfl⟩ : syracuseStep 1925329 = 1443997) (by norm_num)
theorem B3850469 : Blo 1711056 3850469 := bbase (se 4 (by rfl) ⟨360981, by rfl⟩ : syracuseStep 3850469 = 721963) (by norm_num)
theorem B1925365 : Blo 1711056 1925365 := bbase (se 5 (by rfl) ⟨90251, by rfl⟩ : syracuseStep 1925365 = 180503) (by norm_num)
theorem B1925401 : Blo 1711056 1925401 := bbase (se 2 (by rfl) ⟨722025, by rfl⟩ : syracuseStep 1925401 = 1444051) (by norm_num)
theorem B3850541 : Blo 1711056 3850541 := bbase (se 3 (by rfl) ⟨721976, by rfl⟩ : syracuseStep 3850541 = 1443953) (by norm_num)
theorem B1925437 : Blo 1711056 1925437 := bbase (se 3 (by rfl) ⟨361019, by rfl⟩ : syracuseStep 1925437 = 722039) (by norm_num)
theorem B1925473 : Blo 1711056 1925473 := bbase (se 2 (by rfl) ⟨722052, by rfl⟩ : syracuseStep 1925473 = 1444105) (by norm_num)
theorem B4333925 : Blo 1711056 4333925 := bbase (se 4 (by rfl) ⟨406305, by rfl⟩ : syracuseStep 4333925 = 812611) (by norm_num)
theorem B3850613 : Blo 1711056 3850613 := bbase (se 5 (by rfl) ⟨180497, by rfl⟩ : syracuseStep 3850613 = 360995) (by norm_num)
theorem B1925509 : Blo 1711056 1925509 := bbase (se 4 (by rfl) ⟨180516, by rfl⟩ : syracuseStep 1925509 = 361033) (by norm_num)
theorem B8225189 : Blo 1711056 8225189 := bbase (se 4 (by rfl) ⟨771111, by rfl⟩ : syracuseStep 8225189 = 1542223) (by norm_num)
theorem B1925545 : Blo 1711056 1925545 := bbase (se 2 (by rfl) ⟨722079, by rfl⟩ : syracuseStep 1925545 = 1444159) (by norm_num)
theorem B3850685 : Blo 1711056 3850685 := bbase (se 3 (by rfl) ⟨722003, by rfl⟩ : syracuseStep 3850685 = 1444007) (by norm_num)
theorem B1925581 : Blo 1711056 1925581 := bbase (se 3 (by rfl) ⟨361046, by rfl⟩ : syracuseStep 1925581 = 722093) (by norm_num)
theorem B1925617 : Blo 1711056 1925617 := bbase (se 2 (by rfl) ⟨722106, by rfl⟩ : syracuseStep 1925617 = 1444213) (by norm_num)
theorem B6496757 : Blo 1711056 6496757 := bbase (se 5 (by rfl) ⟨304535, by rfl⟩ : syracuseStep 6496757 = 609071) (by norm_num)
theorem B4112893 : Blo 1711056 4112893 := bbase (se 3 (by rfl) ⟨771167, by rfl⟩ : syracuseStep 4112893 = 1542335) (by norm_num)
theorem B3850757 : Blo 1711056 3850757 := bbase (se 4 (by rfl) ⟨361008, by rfl⟩ : syracuseStep 3850757 = 722017) (by norm_num)
theorem B5775893 : Blo 1711056 5775893 := bbase (se 6 (by rfl) ⟨135372, by rfl⟩ : syracuseStep 5775893 = 270745) (by norm_num)
theorem B1925653 : Blo 1711056 1925653 := bbase (se 6 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 1925653 = 90265) (by norm_num)
theorem B1925689 : Blo 1711056 1925689 := bbase (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) (by norm_num)
theorem B3850829 : Blo 1711056 3850829 := bbase (se 3 (by rfl) ⟨722030, by rfl⟩ : syracuseStep 3850829 = 1444061) (by norm_num)
theorem B1925725 : Blo 1711056 1925725 := bbase (se 3 (by rfl) ⟨361073, by rfl⟩ : syracuseStep 1925725 = 722147) (by norm_num)
theorem B1925761 : Blo 1711056 1925761 := bbase (se 2 (by rfl) ⟨722160, by rfl⟩ : syracuseStep 1925761 = 1444321) (by norm_num)
theorem B1827461 : Blo 1711056 1827461 := bbase (se 4 (by rfl) ⟨171324, by rfl⟩ : syracuseStep 1827461 = 342649) (by norm_num)
theorem B3850901 : Blo 1711056 3850901 := bbase (se 6 (by rfl) ⟨90255, by rfl⟩ : syracuseStep 3850901 = 180511) (by norm_num)
theorem B1925797 : Blo 1711056 1925797 := bbase (se 4 (by rfl) ⟨180543, by rfl⟩ : syracuseStep 1925797 = 361087) (by norm_num)
theorem B4334269 : Blo 1711056 4334269 := bbase (se 3 (by rfl) ⟨812675, by rfl⟩ : syracuseStep 4334269 = 1625351) (by norm_num)
theorem B1925833 : Blo 1711056 1925833 := bbase (se 2 (by rfl) ⟨722187, by rfl⟩ : syracuseStep 1925833 = 1444375) (by norm_num)
theorem B3850973 : Blo 1711056 3850973 := bbase (se 3 (by rfl) ⟨722057, by rfl⟩ : syracuseStep 3850973 = 1444115) (by norm_num)
theorem B4113125 : Blo 1711056 4113125 := bbase (se 4 (by rfl) ⟨385605, by rfl⟩ : syracuseStep 4113125 = 771211) (by norm_num)
theorem B1925869 : Blo 1711056 1925869 := bbase (se 3 (by rfl) ⟨361100, by rfl⟩ : syracuseStep 1925869 = 722201) (by norm_num)
theorem B2056961 : Blo 1711056 2056961 := bbase (se 2 (by rfl) ⟨771360, by rfl⟩ : syracuseStep 2056961 = 1542721) (by norm_num)
theorem B1925905 : Blo 1711056 1925905 := bbase (se 2 (by rfl) ⟨722214, by rfl⟩ : syracuseStep 1925905 = 1444429) (by norm_num)
theorem B4875029 : Blo 1711056 4875029 := bbase (se 6 (by rfl) ⟨114258, by rfl⟩ : syracuseStep 4875029 = 228517) (by norm_num)
theorem B3851045 : Blo 1711056 3851045 := bbase (se 4 (by rfl) ⟨361035, by rfl⟩ : syracuseStep 3851045 = 722071) (by norm_num)
theorem B4334381 : Blo 1711056 4334381 := bbase (se 3 (by rfl) ⟨812696, by rfl⟩ : syracuseStep 4334381 = 1625393) (by norm_num)
theorem B1925941 : Blo 1711056 1925941 := bbase (se 5 (by rfl) ⟨90278, by rfl⟩ : syracuseStep 1925941 = 180557) (by norm_num)
theorem B4391765 : Blo 1711056 4391765 := bbase (se 9 (by rfl) ⟨12866, by rfl⟩ : syracuseStep 4391765 = 25733) (by norm_num)
theorem B93725525 : Blo 1711056 93725525 := bbase (se 9 (by rfl) ⟨274586, by rfl⟩ : syracuseStep 93725525 = 549173) (by norm_num)
theorem B1925977 : Blo 1711056 1925977 := bbase (se 2 (by rfl) ⟨722241, by rfl⟩ : syracuseStep 1925977 = 1444483) (by norm_num)
theorem B3851117 : Blo 1711056 3851117 := bbase (se 3 (by rfl) ⟨722084, by rfl⟩ : syracuseStep 3851117 = 1444169) (by norm_num)
theorem B1926013 : Blo 1711056 1926013 := bbase (se 3 (by rfl) ⟨361127, by rfl⟩ : syracuseStep 1926013 = 722255) (by norm_num)
theorem B1926049 : Blo 1711056 1926049 := bbase (se 2 (by rfl) ⟨722268, by rfl⟩ : syracuseStep 1926049 = 1444537) (by norm_num)
theorem B3851189 : Blo 1711056 3851189 := bbase (se 5 (by rfl) ⟨180524, by rfl⟩ : syracuseStep 3851189 = 361049) (by norm_num)
theorem B7316405 : Blo 1711056 7316405 := bbase (se 5 (by rfl) ⟨342956, by rfl⟩ : syracuseStep 7316405 = 685913) (by norm_num)
theorem B5776325 : Blo 1711056 5776325 := bbase (se 4 (by rfl) ⟨541530, by rfl⟩ : syracuseStep 5776325 = 1083061) (by norm_num)
theorem B1926085 : Blo 1711056 1926085 := bbase (se 4 (by rfl) ⟨180570, by rfl⟩ : syracuseStep 1926085 = 361141) (by norm_num)
theorem B7914469 : Blo 1711056 7914469 := bbase (se 4 (by rfl) ⟨741981, by rfl⟩ : syracuseStep 7914469 = 1483963) (by norm_num)
theorem B8668133 : Blo 1711056 8668133 := bbase (se 4 (by rfl) ⟨812637, by rfl⟩ : syracuseStep 8668133 = 1625275) (by norm_num)
theorem B1926121 : Blo 1711056 1926121 := bbase (se 2 (by rfl) ⟨722295, by rfl⟩ : syracuseStep 1926121 = 1444591) (by norm_num)
theorem B4334573 : Blo 1711056 4334573 := bbase (se 3 (by rfl) ⟨812732, by rfl⟩ : syracuseStep 4334573 = 1625465) (by norm_num)
theorem B13173749 : Blo 1711056 13173749 := bbase (se 5 (by rfl) ⟨617519, by rfl⟩ : syracuseStep 13173749 = 1235039) (by norm_num)
theorem B3851261 : Blo 1711056 3851261 := bbase (se 3 (by rfl) ⟨722111, by rfl⟩ : syracuseStep 3851261 = 1444223) (by norm_num)
theorem B1926157 : Blo 1711056 1926157 := bbase (se 3 (by rfl) ⟨361154, by rfl⟩ : syracuseStep 1926157 = 722309) (by norm_num)
theorem B1926193 : Blo 1711056 1926193 := bbase (se 2 (by rfl) ⟨722322, by rfl⟩ : syracuseStep 1926193 = 1444645) (by norm_num)
theorem B1827905 : Blo 1711056 1827905 := bbase (se 2 (by rfl) ⟨685464, by rfl⟩ : syracuseStep 1827905 = 1370929) (by norm_num)
theorem B3851333 : Blo 1711056 3851333 := bbase (se 4 (by rfl) ⟨361062, by rfl⟩ : syracuseStep 3851333 = 722125) (by norm_num)
theorem B1926229 : Blo 1711056 1926229 := bbase (se 8 (by rfl) ⟨11286, by rfl⟩ : syracuseStep 1926229 = 22573) (by norm_num)
theorem B4113517 : Blo 1711056 4113517 := bbase (se 3 (by rfl) ⟨771284, by rfl⟩ : syracuseStep 4113517 = 1542569) (by norm_num)
theorem B1926265 : Blo 1711056 1926265 := bbase (se 2 (by rfl) ⟨722349, by rfl⟩ : syracuseStep 1926265 = 1444699) (by norm_num)
theorem B1827965 : Blo 1711056 1827965 := bbase (se 3 (by rfl) ⟨342743, by rfl⟩ : syracuseStep 1827965 = 685487) (by norm_num)
theorem B3851405 : Blo 1711056 3851405 := bbase (se 3 (by rfl) ⟨722138, by rfl⟩ : syracuseStep 3851405 = 1444277) (by norm_num)
theorem B1926301 : Blo 1711056 1926301 := bbase (se 3 (by rfl) ⟨361181, by rfl⟩ : syracuseStep 1926301 = 722363) (by norm_num)
theorem B8225957 : Blo 1711056 8225957 := bbase (se 4 (by rfl) ⟨771183, by rfl⟩ : syracuseStep 8225957 = 1542367) (by norm_num)
theorem B1926337 : Blo 1711056 1926337 := bbase (se 2 (by rfl) ⟨722376, by rfl⟩ : syracuseStep 1926337 = 1444753) (by norm_num)
theorem B4875461 : Blo 1711056 4875461 := bbase (se 4 (by rfl) ⟨457074, by rfl⟩ : syracuseStep 4875461 = 914149) (by norm_num)
theorem B3851477 : Blo 1711056 3851477 := bbase (se 7 (by rfl) ⟨45134, by rfl⟩ : syracuseStep 3851477 = 90269) (by norm_num)
theorem B1926373 : Blo 1711056 1926373 := bbase (se 4 (by rfl) ⟨180597, by rfl⟩ : syracuseStep 1926373 = 361195) (by norm_num)
theorem B1828093 : Blo 1711056 1828093 := bbase (se 3 (by rfl) ⟨342767, by rfl⟩ : syracuseStep 1828093 = 685535) (by norm_num)
theorem B1926409 : Blo 1711056 1926409 := bbase (se 2 (by rfl) ⟨722403, by rfl⟩ : syracuseStep 1926409 = 1444807) (by norm_num)
theorem B3851549 : Blo 1711056 3851549 := bbase (se 3 (by rfl) ⟨722165, by rfl⟩ : syracuseStep 3851549 = 1444331) (by norm_num)
theorem B1926445 : Blo 1711056 1926445 := bbase (se 3 (by rfl) ⟨361208, by rfl⟩ : syracuseStep 1926445 = 722417) (by norm_num)
theorem B5203253 : Blo 1711056 5203253 := bbase (se 5 (by rfl) ⟨243902, by rfl⟩ : syracuseStep 5203253 = 487805) (by norm_num)
theorem B3654973 : Blo 1711056 3654973 := bbase (se 3 (by rfl) ⟨685307, by rfl⟩ : syracuseStep 3654973 = 1370615) (by norm_num)
theorem B4334917 : Blo 1711056 4334917 := bbase (se 4 (by rfl) ⟨406398, by rfl⟩ : syracuseStep 4334917 = 812797) (by norm_num)
theorem B1926481 : Blo 1711056 1926481 := bbase (se 2 (by rfl) ⟨722430, by rfl⟩ : syracuseStep 1926481 = 1444861) (by norm_num)
theorem B6939989 : Blo 1711056 6939989 := bbase (se 12 (by rfl) ⟨2541, by rfl⟩ : syracuseStep 6939989 = 5083) (by norm_num)
theorem B3851621 : Blo 1711056 3851621 := bbase (se 4 (by rfl) ⟨361089, by rfl⟩ : syracuseStep 3851621 = 722179) (by norm_num)
theorem B5776757 : Blo 1711056 5776757 := bbase (se 5 (by rfl) ⟨270785, by rfl⟩ : syracuseStep 5776757 = 541571) (by norm_num)
theorem B1926517 : Blo 1711056 1926517 := bbase (se 5 (by rfl) ⟨90305, by rfl⟩ : syracuseStep 1926517 = 180611) (by norm_num)
theorem B19506581 : Blo 1711056 19506581 := bbase (se 6 (by rfl) ⟨457185, by rfl⟩ : syracuseStep 19506581 = 914371) (by norm_num)
theorem B1926553 : Blo 1711056 1926553 := bbase (se 2 (by rfl) ⟨722457, by rfl⟩ : syracuseStep 1926553 = 1444915) (by norm_num)
theorem B3851693 : Blo 1711056 3851693 := bbase (se 3 (by rfl) ⟨722192, by rfl⟩ : syracuseStep 3851693 = 1444385) (by norm_num)
theorem B4335029 : Blo 1711056 4335029 := bbase (se 5 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 4335029 = 406409) (by norm_num)
theorem B1926589 : Blo 1711056 1926589 := bbase (se 3 (by rfl) ⟨361235, by rfl⟩ : syracuseStep 1926589 = 722471) (by norm_num)
theorem B2057681 : Blo 1711056 2057681 := bbase (se 2 (by rfl) ⟨771630, by rfl⟩ : syracuseStep 2057681 = 1543261) (by norm_num)
theorem B1926625 : Blo 1711056 1926625 := bbase (se 2 (by rfl) ⟨722484, by rfl⟩ : syracuseStep 1926625 = 1444969) (by norm_num)
theorem B3851765 : Blo 1711056 3851765 := bbase (se 5 (by rfl) ⟨180551, by rfl⟩ : syracuseStep 3851765 = 361103) (by norm_num)
theorem B1926661 : Blo 1711056 1926661 := bbase (se 4 (by rfl) ⟨180624, by rfl⟩ : syracuseStep 1926661 = 361249) (by norm_num)
theorem B1926697 : Blo 1711056 1926697 := bbase (se 2 (by rfl) ⟨722511, by rfl⟩ : syracuseStep 1926697 = 1445023) (by norm_num)
theorem B3851837 : Blo 1711056 3851837 := bbase (se 3 (by rfl) ⟨722219, by rfl⟩ : syracuseStep 3851837 = 1444439) (by norm_num)
theorem B1926733 : Blo 1711056 1926733 := bbase (se 3 (by rfl) ⟨361262, by rfl⟩ : syracuseStep 1926733 = 722525) (by norm_num)
theorem B1926769 : Blo 1711056 1926769 := bbase (se 2 (by rfl) ⟨722538, by rfl⟩ : syracuseStep 1926769 = 1445077) (by norm_num)
theorem B4335221 : Blo 1711056 4335221 := bbase (se 5 (by rfl) ⟨203213, by rfl⟩ : syracuseStep 4335221 = 406427) (by norm_num)
theorem B3851909 : Blo 1711056 3851909 := bbase (se 4 (by rfl) ⟨361116, by rfl⟩ : syracuseStep 3851909 = 722233) (by norm_num)
theorem B6497941 : Blo 1711056 6497941 := bbase (se 6 (by rfl) ⟨152295, by rfl⟩ : syracuseStep 6497941 = 304591) (by norm_num)
theorem B1926805 : Blo 1711056 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B1828537 : Blo 1711056 1828537 := bbase (se 2 (by rfl) ⟨685701, by rfl⟩ : syracuseStep 1828537 = 1371403) (by norm_num)
theorem B1926841 : Blo 1711056 1926841 := bbase (se 2 (by rfl) ⟨722565, by rfl⟩ : syracuseStep 1926841 = 1445131) (by norm_num)
theorem B3851981 : Blo 1711056 3851981 := bbase (se 3 (by rfl) ⟨722246, by rfl⟩ : syracuseStep 3851981 = 1444493) (by norm_num)
theorem B1926877 : Blo 1711056 1926877 := bbase (se 3 (by rfl) ⟨361289, by rfl⟩ : syracuseStep 1926877 = 722579) (by norm_num)
theorem B1926913 : Blo 1711056 1926913 := bbase (se 2 (by rfl) ⟨722592, by rfl⟩ : syracuseStep 1926913 = 1445185) (by norm_num)
theorem B2057989 : Blo 1711056 2057989 := bbase (se 4 (by rfl) ⟨192936, by rfl⟩ : syracuseStep 2057989 = 385873) (by norm_num)
theorem B3852053 : Blo 1711056 3852053 := bbase (se 6 (by rfl) ⟨90282, by rfl⟩ : syracuseStep 3852053 = 180565) (by norm_num)
theorem B5777189 : Blo 1711056 5777189 := bbase (se 4 (by rfl) ⟨541611, by rfl⟩ : syracuseStep 5777189 = 1083223) (by norm_num)
theorem B1926949 : Blo 1711056 1926949 := bbase (se 4 (by rfl) ⟨180651, by rfl⟩ : syracuseStep 1926949 = 361303) (by norm_num)
theorem B3655469 : Blo 1711056 3655469 := bbase (se 3 (by rfl) ⟨685400, by rfl⟩ : syracuseStep 3655469 = 1370801) (by norm_num)
theorem B1828657 : Blo 1711056 1828657 := bbase (se 2 (by rfl) ⟨685746, by rfl⟩ : syracuseStep 1828657 = 1371493) (by norm_num)
theorem B1926985 : Blo 1711056 1926985 := bbase (se 2 (by rfl) ⟨722619, by rfl⟩ : syracuseStep 1926985 = 1445239) (by norm_num)
theorem B3852125 : Blo 1711056 3852125 := bbase (se 3 (by rfl) ⟨722273, by rfl⟩ : syracuseStep 3852125 = 1444547) (by norm_num)
theorem B1927021 : Blo 1711056 1927021 := bbase (se 3 (by rfl) ⟨361316, by rfl⟩ : syracuseStep 1927021 = 722633) (by norm_num)
theorem B1927057 : Blo 1711056 1927057 := bbase (se 2 (by rfl) ⟨722646, by rfl⟩ : syracuseStep 1927057 = 1445293) (by norm_num)
theorem B3852197 : Blo 1711056 3852197 := bbase (se 4 (by rfl) ⟨361143, by rfl⟩ : syracuseStep 3852197 = 722287) (by norm_num)
theorem B4876213 : Blo 1711056 4876213 := bbase (se 5 (by rfl) ⟨228572, by rfl⟩ : syracuseStep 4876213 = 457145) (by norm_num)
theorem B1927093 : Blo 1711056 1927093 := bbase (se 5 (by rfl) ⟨90332, by rfl⟩ : syracuseStep 1927093 = 180665) (by norm_num)
theorem B2197441 : Blo 1711056 2197441 := bbase (se 2 (by rfl) ⟨824040, by rfl⟩ : syracuseStep 2197441 = 1648081) (by norm_num)
theorem B6498245 : Blo 1711056 6498245 := bbase (se 4 (by rfl) ⟨609210, by rfl⟩ : syracuseStep 6498245 = 1218421) (by norm_num)
theorem B2779085 : Blo 1711056 2779085 := bbase (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) (by norm_num)
theorem B4335565 : Blo 1711056 4335565 := bbase (se 3 (by rfl) ⟨812918, by rfl⟩ : syracuseStep 4335565 = 1625837) (by norm_num)
theorem B1927129 : Blo 1711056 1927129 := bbase (se 2 (by rfl) ⟨722673, by rfl⟩ : syracuseStep 1927129 = 1445347) (by norm_num)
theorem B3852269 : Blo 1711056 3852269 := bbase (se 3 (by rfl) ⟨722300, by rfl⟩ : syracuseStep 3852269 = 1444601) (by norm_num)
theorem B1927165 : Blo 1711056 1927165 := bbase (se 3 (by rfl) ⟨361343, by rfl⟩ : syracuseStep 1927165 = 722687) (by norm_num)
theorem B7309349 : Blo 1711056 7309349 := bbase (se 4 (by rfl) ⟨685251, by rfl⟩ : syracuseStep 7309349 = 1370503) (by norm_num)
theorem B1828909 : Blo 1711056 1828909 := bbase (se 3 (by rfl) ⟨342920, by rfl⟩ : syracuseStep 1828909 = 685841) (by norm_num)
theorem B1828913 : Blo 1711056 1828913 := bbase (se 2 (by rfl) ⟨685842, by rfl⟩ : syracuseStep 1828913 = 1371685) (by norm_num)
theorem B3852341 : Blo 1711056 3852341 := bbase (se 5 (by rfl) ⟨180578, by rfl⟩ : syracuseStep 3852341 = 361157) (by norm_num)
theorem B4335677 : Blo 1711056 4335677 := bbase (se 3 (by rfl) ⟨812939, by rfl⟩ : syracuseStep 4335677 = 1625879) (by norm_num)
theorem B28543061 : Blo 1711056 28543061 := bbase (se 8 (by rfl) ⟨167244, by rfl⟩ : syracuseStep 28543061 = 334489) (by norm_num)
theorem B3852413 : Blo 1711056 3852413 := bbase (se 3 (by rfl) ⟨722327, by rfl⟩ : syracuseStep 3852413 = 1444655) (by norm_num)
theorem B1853585 : Blo 1711056 1853585 := bbase (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) (by norm_num)
theorem B4114613 : Blo 1711056 4114613 := bbase (se 5 (by rfl) ⟨192872, by rfl⟩ : syracuseStep 4114613 = 385745) (by norm_num)
theorem B3852485 : Blo 1711056 3852485 := bbase (se 4 (by rfl) ⟨361170, by rfl⟩ : syracuseStep 3852485 = 722341) (by norm_num)
theorem B5777621 : Blo 1711056 5777621 := bbase (se 7 (by rfl) ⟨67706, by rfl⟩ : syracuseStep 5777621 = 135413) (by norm_num)
theorem B12503285 : Blo 1711056 12503285 := bbase (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) (by norm_num)
theorem B5482741 : Blo 1711056 5482741 := bbase (se 5 (by rfl) ⟨257003, by rfl⟩ : syracuseStep 5482741 = 514007) (by norm_num)
theorem B8669429 : Blo 1711056 8669429 := bbase (se 5 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 8669429 = 812759) (by norm_num)
theorem B4335869 : Blo 1711056 4335869 := bbase (se 3 (by rfl) ⟨812975, by rfl⟩ : syracuseStep 4335869 = 1625951) (by norm_num)
theorem B3852557 : Blo 1711056 3852557 := bbase (se 3 (by rfl) ⟨722354, by rfl⟩ : syracuseStep 3852557 = 1444709) (by norm_num)
theorem B1878313 : Blo 1711056 1878313 := bbase (se 2 (by rfl) ⟨704367, by rfl⟩ : syracuseStep 1878313 = 1408735) (by norm_num)
theorem B3852629 : Blo 1711056 3852629 := bbase (se 10 (by rfl) ⟨5643, by rfl⟩ : syracuseStep 3852629 = 11287) (by norm_num)
theorem B3852701 : Blo 1711056 3852701 := bbase (se 3 (by rfl) ⟨722381, by rfl⟩ : syracuseStep 3852701 = 1444763) (by norm_num)
theorem B2566589 : Blo 1711056 2566589 := bbase (se 3 (by rfl) ⟨481235, by rfl⟩ : syracuseStep 2566589 = 962471) (by norm_num)
theorem B2566613 : Blo 1711056 2566613 := bbase (se 7 (by rfl) ⟨30077, by rfl⟩ : syracuseStep 2566613 = 60155) (by norm_num)
theorem B4114901 : Blo 1711056 4114901 := bbase (se 7 (by rfl) ⟨48221, by rfl⟩ : syracuseStep 4114901 = 96443) (by norm_num)
theorem B3852773 : Blo 1711056 3852773 := bbase (se 4 (by rfl) ⟨361197, by rfl⟩ : syracuseStep 3852773 = 722395) (by norm_num)
theorem B2566637 : Blo 1711056 2566637 := bbase (se 3 (by rfl) ⟨481244, by rfl⟩ : syracuseStep 2566637 = 962489) (by norm_num)
theorem B6941173 : Blo 1711056 6941173 := bbase (se 5 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 6941173 = 650735) (by norm_num)
theorem B2566661 : Blo 1711056 2566661 := bbase (se 4 (by rfl) ⟨240624, by rfl⟩ : syracuseStep 2566661 = 481249) (by norm_num)
theorem B2566685 : Blo 1711056 2566685 := bbase (se 3 (by rfl) ⟨481253, by rfl⟩ : syracuseStep 2566685 = 962507) (by norm_num)
theorem B3852845 : Blo 1711056 3852845 := bbase (se 3 (by rfl) ⟨722408, by rfl⟩ : syracuseStep 3852845 = 1444817) (by norm_num)
theorem B2566709 : Blo 1711056 2566709 := bbase (se 5 (by rfl) ⟨120314, by rfl⟩ : syracuseStep 2566709 = 240629) (by norm_num)
theorem B2566733 : Blo 1711056 2566733 := bbase (se 3 (by rfl) ⟨481262, by rfl⟩ : syracuseStep 2566733 = 962525) (by norm_num)
theorem B2566757 : Blo 1711056 2566757 := bbase (se 4 (by rfl) ⟨240633, by rfl⟩ : syracuseStep 2566757 = 481267) (by norm_num)
theorem B3852917 : Blo 1711056 3852917 := bbase (se 5 (by rfl) ⟨180605, by rfl⟩ : syracuseStep 3852917 = 361211) (by norm_num)
theorem B2566781 : Blo 1711056 2566781 := bbase (se 3 (by rfl) ⟨481271, by rfl⟩ : syracuseStep 2566781 = 962543) (by norm_num)
theorem B5778053 : Blo 1711056 5778053 := bbase (se 4 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 5778053 = 1083385) (by norm_num)
theorem B2566805 : Blo 1711056 2566805 := bbase (se 6 (by rfl) ⟨60159, by rfl⟩ : syracuseStep 2566805 = 120319) (by norm_num)
theorem B6941333 : Blo 1711056 6941333 := bbase (se 6 (by rfl) ⟨162687, by rfl⟩ : syracuseStep 6941333 = 325375) (by norm_num)
theorem B3656357 : Blo 1711056 3656357 := bbase (se 4 (by rfl) ⟨342783, by rfl⟩ : syracuseStep 3656357 = 685567) (by norm_num)
theorem B2566829 : Blo 1711056 2566829 := bbase (se 3 (by rfl) ⟨481280, by rfl⟩ : syracuseStep 2566829 = 962561) (by norm_num)
theorem B10963637 : Blo 1711056 10963637 := bbase (se 5 (by rfl) ⟨513920, by rfl⟩ : syracuseStep 10963637 = 1027841) (by norm_num)
theorem B3852989 : Blo 1711056 3852989 := bbase (se 3 (by rfl) ⟨722435, by rfl⟩ : syracuseStep 3852989 = 1444871) (by norm_num)
theorem B2566853 : Blo 1711056 2566853 := bbase (se 4 (by rfl) ⟨240642, by rfl⟩ : syracuseStep 2566853 = 481285) (by norm_num)
theorem B2566877 : Blo 1711056 2566877 := bbase (se 3 (by rfl) ⟨481289, by rfl⟩ : syracuseStep 2566877 = 962579) (by norm_num)
theorem B1925113 : Blo 1711056 1925113 := bbase (se 2 (by rfl) ⟨721917, by rfl⟩ : syracuseStep 1925113 = 1443835) (by norm_num)
theorem B2312941 : Blo 1711056 2312941 := bbase (se 3 (by rfl) ⟨433676, by rfl⟩ : syracuseStep 2312941 = 867353) (by norm_num)
theorem B2566901 : Blo 1711056 2566901 := bbase (se 5 (by rfl) ⟨120323, by rfl⟩ : syracuseStep 2566901 = 240647) (by norm_num)
theorem B3853061 : Blo 1711056 3853061 := bbase (se 4 (by rfl) ⟨361224, by rfl⟩ : syracuseStep 3853061 = 722449) (by norm_num)
theorem B2566925 : Blo 1711056 2566925 := bbase (se 3 (by rfl) ⟨481298, by rfl⟩ : syracuseStep 2566925 = 962597) (by norm_num)
theorem B3656477 : Blo 1711056 3656477 := bbase (se 3 (by rfl) ⟨685589, by rfl⟩ : syracuseStep 3656477 = 1371179) (by norm_num)
theorem B2566949 : Blo 1711056 2566949 := bbase (se 4 (by rfl) ⟨240651, by rfl⟩ : syracuseStep 2566949 = 481303) (by norm_num)
theorem B1878841 : Blo 1711056 1878841 := bbase (se 2 (by rfl) ⟨704565, by rfl⟩ : syracuseStep 1878841 = 1409131) (by norm_num)
theorem B2566973 : Blo 1711056 2566973 := bbase (se 3 (by rfl) ⟨481307, by rfl⟩ : syracuseStep 2566973 = 962615) (by norm_num)
theorem B3853133 : Blo 1711056 3853133 := bbase (se 3 (by rfl) ⟨722462, by rfl⟩ : syracuseStep 3853133 = 1444925) (by norm_num)
theorem B2566997 : Blo 1711056 2566997 := bbase (se 9 (by rfl) ⟨7520, by rfl⟩ : syracuseStep 2566997 = 15041) (by norm_num)
theorem B2567021 : Blo 1711056 2567021 := bbase (se 3 (by rfl) ⟨481316, by rfl⟩ : syracuseStep 2567021 = 962633) (by norm_num)
theorem B2567045 : Blo 1711056 2567045 := bbase (se 4 (by rfl) ⟨240660, by rfl⟩ : syracuseStep 2567045 = 481321) (by norm_num)
theorem B3853205 : Blo 1711056 3853205 := bbase (se 6 (by rfl) ⟨90309, by rfl⟩ : syracuseStep 3853205 = 180619) (by norm_num)
theorem B2567069 : Blo 1711056 2567069 := bbase (se 3 (by rfl) ⟨481325, by rfl⟩ : syracuseStep 2567069 = 962651) (by norm_num)
theorem B2567093 : Blo 1711056 2567093 := bbase (se 5 (by rfl) ⟨120332, by rfl⟩ : syracuseStep 2567093 = 240665) (by norm_num)
theorem B3296189 : Blo 1711056 3296189 := bbase (se 3 (by rfl) ⟨618035, by rfl⟩ : syracuseStep 3296189 = 1236071) (by norm_num)
theorem B2567117 : Blo 1711056 2567117 := bbase (se 3 (by rfl) ⟨481334, by rfl⟩ : syracuseStep 2567117 = 962669) (by norm_num)
theorem B2165717 : Blo 1711056 2165717 := bbase (se 7 (by rfl) ⟨25379, by rfl⟩ : syracuseStep 2165717 = 50759) (by norm_num)
theorem B3853277 : Blo 1711056 3853277 := bbase (se 3 (by rfl) ⟨722489, by rfl⟩ : syracuseStep 3853277 = 1444979) (by norm_num)
theorem B2567141 : Blo 1711056 2567141 := bbase (se 4 (by rfl) ⟨240669, by rfl⟩ : syracuseStep 2567141 = 481339) (by norm_num)
theorem B2567165 : Blo 1711056 2567165 := bbase (se 3 (by rfl) ⟨481343, by rfl⟩ : syracuseStep 2567165 = 962687) (by norm_num)
theorem B2165773 : Blo 1711056 2165773 := bbase (se 3 (by rfl) ⟨406082, by rfl⟩ : syracuseStep 2165773 = 812165) (by norm_num)
theorem B7310357 : Blo 1711056 7310357 := bbase (se 6 (by rfl) ⟨171336, by rfl⟩ : syracuseStep 7310357 = 342673) (by norm_num)
theorem B2567189 : Blo 1711056 2567189 := bbase (se 6 (by rfl) ⟨60168, by rfl⟩ : syracuseStep 2567189 = 120337) (by norm_num)
theorem B5557285 : Blo 1711056 5557285 := bbase (se 4 (by rfl) ⟨520995, by rfl⟩ : syracuseStep 5557285 = 1041991) (by norm_num)
theorem B3853349 : Blo 1711056 3853349 := bbase (se 4 (by rfl) ⟨361251, by rfl⟩ : syracuseStep 3853349 = 722503) (by norm_num)
theorem B2567213 : Blo 1711056 2567213 := bbase (se 3 (by rfl) ⟨481352, by rfl⟩ : syracuseStep 2567213 = 962705) (by norm_num)
theorem B5778485 : Blo 1711056 5778485 := bbase (se 5 (by rfl) ⟨270866, by rfl⟩ : syracuseStep 5778485 = 541733) (by norm_num)
theorem B2567237 : Blo 1711056 2567237 := bbase (se 4 (by rfl) ⟨240678, by rfl⟩ : syracuseStep 2567237 = 481357) (by norm_num)
theorem B3296333 : Blo 1711056 3296333 := bbase (se 3 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 3296333 = 1236125) (by norm_num)
theorem B2567261 : Blo 1711056 2567261 := bbase (se 3 (by rfl) ⟨481361, by rfl⟩ : syracuseStep 2567261 = 962723) (by norm_num)
theorem B2165869 : Blo 1711056 2165869 := bbase (se 3 (by rfl) ⟨406100, by rfl⟩ : syracuseStep 2165869 = 812201) (by norm_num)
theorem B3853421 : Blo 1711056 3853421 := bbase (se 3 (by rfl) ⟨722516, by rfl⟩ : syracuseStep 3853421 = 1445033) (by norm_num)
theorem B2567285 : Blo 1711056 2567285 := bbase (se 5 (by rfl) ⟨120341, by rfl⟩ : syracuseStep 2567285 = 240683) (by norm_num)
theorem B2567309 : Blo 1711056 2567309 := bbase (se 3 (by rfl) ⟨481370, by rfl⟩ : syracuseStep 2567309 = 962741) (by norm_num)
theorem B4942997 : Blo 1711056 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B2567333 : Blo 1711056 2567333 := bbase (se 4 (by rfl) ⟨240687, by rfl⟩ : syracuseStep 2567333 = 481375) (by norm_num)
theorem B3083437 : Blo 1711056 3083437 := bbase (se 3 (by rfl) ⟨578144, by rfl⟩ : syracuseStep 3083437 = 1156289) (by norm_num)
theorem B3853493 : Blo 1711056 3853493 := bbase (se 5 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 3853493 = 361265) (by norm_num)
theorem B2567357 : Blo 1711056 2567357 := bbase (se 3 (by rfl) ⟨481379, by rfl⟩ : syracuseStep 2567357 = 962759) (by norm_num)
theorem B2567381 : Blo 1711056 2567381 := bbase (se 7 (by rfl) ⟨30086, by rfl⟩ : syracuseStep 2567381 = 60173) (by norm_num)
theorem B2567405 : Blo 1711056 2567405 := bbase (se 3 (by rfl) ⟨481388, by rfl⟩ : syracuseStep 2567405 = 962777) (by norm_num)
theorem B3853565 : Blo 1711056 3853565 := bbase (se 3 (by rfl) ⟨722543, by rfl⟩ : syracuseStep 3853565 = 1445087) (by norm_num)
theorem B2567429 : Blo 1711056 2567429 := bbase (se 4 (by rfl) ⟨240696, by rfl⟩ : syracuseStep 2567429 = 481393) (by norm_num)
theorem B2166041 : Blo 1711056 2166041 := bbase (se 2 (by rfl) ⟨812265, by rfl⟩ : syracuseStep 2166041 = 1624531) (by norm_num)
theorem B2567453 : Blo 1711056 2567453 := bbase (se 3 (by rfl) ⟨481397, by rfl⟩ : syracuseStep 2567453 = 962795) (by norm_num)
theorem B2567477 : Blo 1711056 2567477 := bbase (se 5 (by rfl) ⟨120350, by rfl⟩ : syracuseStep 2567477 = 240701) (by norm_num)
theorem B2436421 : Blo 1711056 2436421 := bbase (se 4 (by rfl) ⟨228414, by rfl⟩ : syracuseStep 2436421 = 456829) (by norm_num)
theorem B3853637 : Blo 1711056 3853637 := bbase (se 4 (by rfl) ⟨361278, by rfl⟩ : syracuseStep 3853637 = 722557) (by norm_num)
theorem B2567501 : Blo 1711056 2567501 := bbase (se 3 (by rfl) ⟨481406, by rfl⟩ : syracuseStep 2567501 = 962813) (by norm_num)
theorem B2166097 : Blo 1711056 2166097 := bbase (se 2 (by rfl) ⟨812286, by rfl⟩ : syracuseStep 2166097 = 1624573) (by norm_num)
theorem B2567525 : Blo 1711056 2567525 := bbase (se 4 (by rfl) ⟨240705, by rfl⟩ : syracuseStep 2567525 = 481411) (by norm_num)
theorem B2567549 : Blo 1711056 2567549 := bbase (se 3 (by rfl) ⟨481415, by rfl⟩ : syracuseStep 2567549 = 962831) (by norm_num)
theorem B3083653 : Blo 1711056 3083653 := bbase (se 4 (by rfl) ⟨289092, by rfl⟩ : syracuseStep 3083653 = 578185) (by norm_num)
theorem B3853709 : Blo 1711056 3853709 := bbase (se 3 (by rfl) ⟨722570, by rfl⟩ : syracuseStep 3853709 = 1445141) (by norm_num)
theorem B2567573 : Blo 1711056 2567573 := bbase (se 6 (by rfl) ⟨60177, by rfl⟩ : syracuseStep 2567573 = 120355) (by norm_num)
theorem B3657109 : Blo 1711056 3657109 := bbase (se 6 (by rfl) ⟨85713, by rfl⟩ : syracuseStep 3657109 = 171427) (by norm_num)
theorem B2567597 : Blo 1711056 2567597 := bbase (se 3 (by rfl) ⟨481424, by rfl⟩ : syracuseStep 2567597 = 962849) (by norm_num)
theorem B2166193 : Blo 1711056 2166193 := bbase (se 2 (by rfl) ⟨812322, by rfl⟩ : syracuseStep 2166193 = 1624645) (by norm_num)
theorem B2567621 : Blo 1711056 2567621 := bbase (se 4 (by rfl) ⟨240714, by rfl⟩ : syracuseStep 2567621 = 481429) (by norm_num)
theorem B3853781 : Blo 1711056 3853781 := bbase (se 7 (by rfl) ⟨45161, by rfl⟩ : syracuseStep 3853781 = 90323) (by norm_num)
theorem B2567645 : Blo 1711056 2567645 := bbase (se 3 (by rfl) ⟨481433, by rfl⟩ : syracuseStep 2567645 = 962867) (by norm_num)
theorem B5778917 : Blo 1711056 5778917 := bbase (se 4 (by rfl) ⟨541773, by rfl⟩ : syracuseStep 5778917 = 1083547) (by norm_num)
theorem B2567669 : Blo 1711056 2567669 := bbase (se 5 (by rfl) ⟨120359, by rfl⟩ : syracuseStep 2567669 = 240719) (by norm_num)
theorem B8670725 : Blo 1711056 8670725 := bbase (se 4 (by rfl) ⟨812880, by rfl⟩ : syracuseStep 8670725 = 1625761) (by norm_num)
theorem B2567693 : Blo 1711056 2567693 := bbase (se 3 (by rfl) ⟨481442, by rfl⟩ : syracuseStep 2567693 = 962885) (by norm_num)
theorem B2436637 : Blo 1711056 2436637 := bbase (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) (by norm_num)
theorem B3853853 : Blo 1711056 3853853 := bbase (se 3 (by rfl) ⟨722597, by rfl⟩ : syracuseStep 3853853 = 1445195) (by norm_num)
theorem B2567717 : Blo 1711056 2567717 := bbase (se 4 (by rfl) ⟨240723, by rfl⟩ : syracuseStep 2567717 = 481447) (by norm_num)
theorem B2567741 : Blo 1711056 2567741 := bbase (se 3 (by rfl) ⟨481451, by rfl⟩ : syracuseStep 2567741 = 962903) (by norm_num)
theorem B2928197 : Blo 1711056 2928197 := bbase (se 4 (by rfl) ⟨274518, by rfl⟩ : syracuseStep 2928197 = 549037) (by norm_num)
theorem B2567765 : Blo 1711056 2567765 := bbase (se 8 (by rfl) ⟨15045, by rfl⟩ : syracuseStep 2567765 = 30091) (by norm_num)
theorem B2166365 : Blo 1711056 2166365 := bbase (se 3 (by rfl) ⟨406193, by rfl⟩ : syracuseStep 2166365 = 812387) (by norm_num)
theorem B3853925 : Blo 1711056 3853925 := bbase (se 4 (by rfl) ⟨361305, by rfl⟩ : syracuseStep 3853925 = 722611) (by norm_num)
theorem B2567789 : Blo 1711056 2567789 := bbase (se 3 (by rfl) ⟨481460, by rfl⟩ : syracuseStep 2567789 = 962921) (by norm_num)
theorem B2567813 : Blo 1711056 2567813 := bbase (se 4 (by rfl) ⟨240732, by rfl⟩ : syracuseStep 2567813 = 481465) (by norm_num)
theorem B2166421 : Blo 1711056 2166421 := bbase (se 6 (by rfl) ⟨50775, by rfl⟩ : syracuseStep 2166421 = 101551) (by norm_num)
theorem B2567837 : Blo 1711056 2567837 := bbase (se 3 (by rfl) ⟨481469, by rfl⟩ : syracuseStep 2567837 = 962939) (by norm_num)
theorem B3853997 : Blo 1711056 3853997 := bbase (se 3 (by rfl) ⟨722624, by rfl⟩ : syracuseStep 3853997 = 1445249) (by norm_num)
theorem B2567861 : Blo 1711056 2567861 := bbase (se 5 (by rfl) ⟨120368, by rfl⟩ : syracuseStep 2567861 = 240737) (by norm_num)
theorem B2567885 : Blo 1711056 2567885 := bbase (se 3 (by rfl) ⟨481478, by rfl⟩ : syracuseStep 2567885 = 962957) (by norm_num)
theorem B2567909 : Blo 1711056 2567909 := bbase (se 4 (by rfl) ⟨240741, by rfl⟩ : syracuseStep 2567909 = 481483) (by norm_num)
theorem B2166517 : Blo 1711056 2166517 := bbase (se 5 (by rfl) ⟨101555, by rfl⟩ : syracuseStep 2166517 = 203111) (by norm_num)
theorem B3854069 : Blo 1711056 3854069 := bbase (se 5 (by rfl) ⟨180659, by rfl⟩ : syracuseStep 3854069 = 361319) (by norm_num)
theorem B2567933 : Blo 1711056 2567933 := bbase (se 3 (by rfl) ⟨481487, by rfl⟩ : syracuseStep 2567933 = 962975) (by norm_num)
theorem B6942469 : Blo 1711056 6942469 := bbase (se 4 (by rfl) ⟨650856, by rfl⟩ : syracuseStep 6942469 = 1301713) (by norm_num)
theorem B9252629 : Blo 1711056 9252629 := bbase (se 6 (by rfl) ⟨216858, by rfl⟩ : syracuseStep 9252629 = 433717) (by norm_num)
theorem B2567957 : Blo 1711056 2567957 := bbase (se 6 (by rfl) ⟨60186, by rfl⟩ : syracuseStep 2567957 = 120373) (by norm_num)
theorem B2567981 : Blo 1711056 2567981 := bbase (se 3 (by rfl) ⟨481496, by rfl⟩ : syracuseStep 2567981 = 962993) (by norm_num)
theorem B3854141 : Blo 1711056 3854141 := bbase (se 3 (by rfl) ⟨722651, by rfl⟩ : syracuseStep 3854141 = 1445303) (by norm_num)
theorem B2568005 : Blo 1711056 2568005 := bbase (se 4 (by rfl) ⟨240750, by rfl⟩ : syracuseStep 2568005 = 481501) (by norm_num)
theorem B2887501 : Blo 1711056 2887501 := bbase (se 3 (by rfl) ⟨541406, by rfl⟩ : syracuseStep 2887501 = 1082813) (by norm_num)
theorem B2568029 : Blo 1711056 2568029 := bbase (se 3 (by rfl) ⟨481505, by rfl⟩ : syracuseStep 2568029 = 963011) (by norm_num)
theorem B2568053 : Blo 1711056 2568053 := bbase (se 5 (by rfl) ⟨120377, by rfl⟩ : syracuseStep 2568053 = 240755) (by norm_num)
theorem B3854213 : Blo 1711056 3854213 := bbase (se 4 (by rfl) ⟨361332, by rfl⟩ : syracuseStep 3854213 = 722665) (by norm_num)
theorem B2568077 : Blo 1711056 2568077 := bbase (se 3 (by rfl) ⟨481514, by rfl⟩ : syracuseStep 2568077 = 963029) (by norm_num)
theorem B2437013 : Blo 1711056 2437013 := bbase (se 6 (by rfl) ⟨57117, by rfl⟩ : syracuseStep 2437013 = 114235) (by norm_num)
theorem B5779349 : Blo 1711056 5779349 := bbase (se 6 (by rfl) ⟨135453, by rfl⟩ : syracuseStep 5779349 = 270907) (by norm_num)
theorem B2166689 : Blo 1711056 2166689 := bbase (se 2 (by rfl) ⟨812508, by rfl⟩ : syracuseStep 2166689 = 1625017) (by norm_num)
theorem B2887589 : Blo 1711056 2887589 := bbase (se 4 (by rfl) ⟨270711, by rfl⟩ : syracuseStep 2887589 = 541423) (by norm_num)
theorem B8662949 : Blo 1711056 8662949 := bbase (se 4 (by rfl) ⟨812151, by rfl⟩ : syracuseStep 8662949 = 1624303) (by norm_num)
theorem B2568101 : Blo 1711056 2568101 := bbase (se 4 (by rfl) ⟨240759, by rfl⟩ : syracuseStep 2568101 = 481519) (by norm_num)
theorem B2568125 : Blo 1711056 2568125 := bbase (se 3 (by rfl) ⟨481523, by rfl⟩ : syracuseStep 2568125 = 963047) (by norm_num)
theorem B3854285 : Blo 1711056 3854285 := bbase (se 3 (by rfl) ⟨722678, by rfl⟩ : syracuseStep 3854285 = 1445357) (by norm_num)
theorem B2568149 : Blo 1711056 2568149 := bbase (se 7 (by rfl) ⟨30095, by rfl⟩ : syracuseStep 2568149 = 60191) (by norm_num)
theorem B29257685 : Blo 1711056 29257685 := bbase (se 7 (by rfl) ⟨342863, by rfl⟩ : syracuseStep 29257685 = 685727) (by norm_num)
theorem B2166745 : Blo 1711056 2166745 := bbase (se 2 (by rfl) ⟨812529, by rfl⟩ : syracuseStep 2166745 = 1625059) (by norm_num)
theorem B3903461 : Blo 1711056 3903461 := bbase (se 4 (by rfl) ⟨365949, by rfl⟩ : syracuseStep 3903461 = 731899) (by norm_num)
theorem B2568173 : Blo 1711056 2568173 := bbase (se 3 (by rfl) ⟨481532, by rfl⟩ : syracuseStep 2568173 = 963065) (by norm_num)
theorem B6500357 : Blo 1711056 6500357 := bbase (se 4 (by rfl) ⟨609408, by rfl⟩ : syracuseStep 6500357 = 1218817) (by norm_num)
theorem B2568197 : Blo 1711056 2568197 := bbase (se 4 (by rfl) ⟨240768, by rfl⟩ : syracuseStep 2568197 = 481537) (by norm_num)
theorem B8335381 : Blo 1711056 8335381 := bbase (se 6 (by rfl) ⟨195360, by rfl⟩ : syracuseStep 8335381 = 390721) (by norm_num)
theorem B3706901 : Blo 1711056 3706901 := bbase (se 6 (by rfl) ⟨86880, by rfl⟩ : syracuseStep 3706901 = 173761) (by norm_num)
theorem B3854357 : Blo 1711056 3854357 := bbase (se 6 (by rfl) ⟨90336, by rfl⟩ : syracuseStep 3854357 = 180673) (by norm_num)
theorem B2568221 : Blo 1711056 2568221 := bbase (se 3 (by rfl) ⟨481541, by rfl⟩ : syracuseStep 2568221 = 963083) (by norm_num)
theorem B2887717 : Blo 1711056 2887717 := bbase (se 4 (by rfl) ⟨270723, by rfl⟩ : syracuseStep 2887717 = 541447) (by norm_num)
theorem B3903533 : Blo 1711056 3903533 := bbase (se 3 (by rfl) ⟨731912, by rfl⟩ : syracuseStep 3903533 = 1463825) (by norm_num)
theorem B2568245 : Blo 1711056 2568245 := bbase (se 5 (by rfl) ⟨120386, by rfl⟩ : syracuseStep 2568245 = 240773) (by norm_num)
theorem B2166841 : Blo 1711056 2166841 := bbase (se 2 (by rfl) ⟨812565, by rfl⟩ : syracuseStep 2166841 = 1625131) (by norm_num)
theorem B2568269 : Blo 1711056 2568269 := bbase (se 3 (by rfl) ⟨481550, by rfl⟩ : syracuseStep 2568269 = 963101) (by norm_num)
theorem B3518549 : Blo 1711056 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B27775061 : Blo 1711056 27775061 := bbase (se 8 (by rfl) ⟨162744, by rfl⟩ : syracuseStep 27775061 = 325489) (by norm_num)
theorem B2568293 : Blo 1711056 2568293 := bbase (se 4 (by rfl) ⟨240777, by rfl⟩ : syracuseStep 2568293 = 481555) (by norm_num)
theorem B1806445 : Blo 1711056 1806445 := bbase (se 3 (by rfl) ⟨338708, by rfl⟩ : syracuseStep 1806445 = 677417) (by norm_num)
theorem B2887805 : Blo 1711056 2887805 := bbase (se 3 (by rfl) ⟨541463, by rfl⟩ : syracuseStep 2887805 = 1082927) (by norm_num)
theorem B2568317 : Blo 1711056 2568317 := bbase (se 3 (by rfl) ⟨481559, by rfl⟩ : syracuseStep 2568317 = 963119) (by norm_num)
theorem B2568341 : Blo 1711056 2568341 := bbase (se 6 (by rfl) ⟨60195, by rfl⟩ : syracuseStep 2568341 = 120391) (by norm_num)
theorem B2568365 : Blo 1711056 2568365 := bbase (se 3 (by rfl) ⟨481568, by rfl⟩ : syracuseStep 2568365 = 963137) (by norm_num)
theorem B8335541 : Blo 1711056 8335541 := bbase (se 5 (by rfl) ⟨390728, by rfl⟩ : syracuseStep 8335541 = 781457) (by norm_num)
theorem B2568389 : Blo 1711056 2568389 := bbase (se 4 (by rfl) ⟨240786, by rfl⟩ : syracuseStep 2568389 = 481573) (by norm_num)
theorem B2568413 : Blo 1711056 2568413 := bbase (se 3 (by rfl) ⟨481577, by rfl⟩ : syracuseStep 2568413 = 963155) (by norm_num)
theorem B2167013 : Blo 1711056 2167013 := bbase (se 4 (by rfl) ⟨203157, by rfl⟩ : syracuseStep 2167013 = 406315) (by norm_num)
theorem B2568437 : Blo 1711056 2568437 := bbase (se 5 (by rfl) ⟨120395, by rfl⟩ : syracuseStep 2568437 = 240791) (by norm_num)
theorem B2887933 : Blo 1711056 2887933 := bbase (se 3 (by rfl) ⟨541487, by rfl⟩ : syracuseStep 2887933 = 1082975) (by norm_num)
theorem B2568461 : Blo 1711056 2568461 := bbase (se 3 (by rfl) ⟨481586, by rfl⟩ : syracuseStep 2568461 = 963173) (by norm_num)
theorem B3657997 : Blo 1711056 3657997 := bbase (se 3 (by rfl) ⟨685874, by rfl⟩ : syracuseStep 3657997 = 1371749) (by norm_num)
theorem B2167069 : Blo 1711056 2167069 := bbase (se 3 (by rfl) ⟨406325, by rfl⟩ : syracuseStep 2167069 = 812651) (by norm_num)
theorem B6500645 : Blo 1711056 6500645 := bbase (se 4 (by rfl) ⟨609435, by rfl⟩ : syracuseStep 6500645 = 1218871) (by norm_num)
theorem B2568485 : Blo 1711056 2568485 := bbase (se 4 (by rfl) ⟨240795, by rfl⟩ : syracuseStep 2568485 = 481591) (by norm_num)
theorem B2314541 : Blo 1711056 2314541 := bbase (se 3 (by rfl) ⟨433976, by rfl⟩ : syracuseStep 2314541 = 867953) (by norm_num)
theorem B2568509 : Blo 1711056 2568509 := bbase (se 3 (by rfl) ⟨481595, by rfl⟩ : syracuseStep 2568509 = 963191) (by norm_num)
theorem B5779781 : Blo 1711056 5779781 := bbase (se 4 (by rfl) ⟨541854, by rfl⟩ : syracuseStep 5779781 = 1083709) (by norm_num)
theorem B2888021 : Blo 1711056 2888021 := bbase (se 10 (by rfl) ⟨4230, by rfl⟩ : syracuseStep 2888021 = 8461) (by norm_num)
theorem B2568533 : Blo 1711056 2568533 := bbase (se 10 (by rfl) ⟨3762, by rfl⟩ : syracuseStep 2568533 = 7525) (by norm_num)
theorem B2568557 : Blo 1711056 2568557 := bbase (se 3 (by rfl) ⟨481604, by rfl⟩ : syracuseStep 2568557 = 963209) (by norm_num)
theorem B2167165 : Blo 1711056 2167165 := bbase (se 3 (by rfl) ⟨406343, by rfl⟩ : syracuseStep 2167165 = 812687) (by norm_num)
theorem B2568581 : Blo 1711056 2568581 := bbase (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) (by norm_num)
theorem B3658117 : Blo 1711056 3658117 := bbase (se 4 (by rfl) ⟨342948, by rfl⟩ : syracuseStep 3658117 = 685897) (by norm_num)
theorem B2568605 : Blo 1711056 2568605 := bbase (se 3 (by rfl) ⟨481613, by rfl⟩ : syracuseStep 2568605 = 963227) (by norm_num)
theorem B2568629 : Blo 1711056 2568629 := bbase (se 5 (by rfl) ⟨120404, by rfl⟩ : syracuseStep 2568629 = 240809) (by norm_num)
theorem B2568653 : Blo 1711056 2568653 := bbase (se 3 (by rfl) ⟨481622, by rfl⟩ : syracuseStep 2568653 = 963245) (by norm_num)
theorem B2888149 : Blo 1711056 2888149 := bbase (se 7 (by rfl) ⟨33845, by rfl⟩ : syracuseStep 2888149 = 67691) (by norm_num)
theorem B2568677 : Blo 1711056 2568677 := bbase (se 4 (by rfl) ⟨240813, by rfl⟩ : syracuseStep 2568677 = 481627) (by norm_num)
theorem B2568701 : Blo 1711056 2568701 := bbase (se 3 (by rfl) ⟨481631, by rfl⟩ : syracuseStep 2568701 = 963263) (by norm_num)
theorem B3084821 : Blo 1711056 3084821 := bbase (se 6 (by rfl) ⟨72300, by rfl⟩ : syracuseStep 3084821 = 144601) (by norm_num)
theorem B2568725 : Blo 1711056 2568725 := bbase (se 6 (by rfl) ⟨60204, by rfl⟩ : syracuseStep 2568725 = 120409) (by norm_num)
theorem B2167337 : Blo 1711056 2167337 := bbase (se 2 (by rfl) ⟨812751, by rfl⟩ : syracuseStep 2167337 = 1625503) (by norm_num)
theorem B2888237 : Blo 1711056 2888237 := bbase (se 3 (by rfl) ⟨541544, by rfl⟩ : syracuseStep 2888237 = 1083089) (by norm_num)
theorem B2568749 : Blo 1711056 2568749 := bbase (se 3 (by rfl) ⟨481640, by rfl⟩ : syracuseStep 2568749 = 963281) (by norm_num)
theorem B2568773 : Blo 1711056 2568773 := bbase (se 4 (by rfl) ⟨240822, by rfl⟩ : syracuseStep 2568773 = 481645) (by norm_num)
theorem B2568797 : Blo 1711056 2568797 := bbase (se 3 (by rfl) ⟨481649, by rfl⟩ : syracuseStep 2568797 = 963299) (by norm_num)
theorem B2167393 : Blo 1711056 2167393 := bbase (se 2 (by rfl) ⟨812772, by rfl⟩ : syracuseStep 2167393 = 1625545) (by norm_num)
theorem B2740853 : Blo 1711056 2740853 := bbase (se 5 (by rfl) ⟨128477, by rfl⟩ : syracuseStep 2740853 = 256955) (by norm_num)
theorem B2568821 : Blo 1711056 2568821 := bbase (se 5 (by rfl) ⟨120413, by rfl⟩ : syracuseStep 2568821 = 240827) (by norm_num)
theorem B3658373 : Blo 1711056 3658373 := bbase (se 4 (by rfl) ⟨342972, by rfl⟩ : syracuseStep 3658373 = 685945) (by norm_num)
theorem B2568845 : Blo 1711056 2568845 := bbase (se 3 (by rfl) ⟨481658, by rfl⟩ : syracuseStep 2568845 = 963317) (by norm_num)
theorem B12341909 : Blo 1711056 12341909 := bbase (se 6 (by rfl) ⟨289263, by rfl⟩ : syracuseStep 12341909 = 578527) (by norm_num)
theorem B2568869 : Blo 1711056 2568869 := bbase (se 4 (by rfl) ⟨240831, by rfl⟩ : syracuseStep 2568869 = 481663) (by norm_num)
theorem B2888365 : Blo 1711056 2888365 := bbase (se 3 (by rfl) ⟨541568, by rfl⟩ : syracuseStep 2888365 = 1083137) (by norm_num)
theorem B2568893 : Blo 1711056 2568893 := bbase (se 3 (by rfl) ⟨481667, by rfl⟩ : syracuseStep 2568893 = 963335) (by norm_num)
theorem B2167489 : Blo 1711056 2167489 := bbase (se 2 (by rfl) ⟨812808, by rfl⟩ : syracuseStep 2167489 = 1625617) (by norm_num)
theorem B2568917 : Blo 1711056 2568917 := bbase (se 7 (by rfl) ⟨30104, by rfl⟩ : syracuseStep 2568917 = 60209) (by norm_num)
theorem B2568941 : Blo 1711056 2568941 := bbase (se 3 (by rfl) ⟨481676, by rfl⟩ : syracuseStep 2568941 = 963353) (by norm_num)
theorem B5780213 : Blo 1711056 5780213 := bbase (se 5 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 5780213 = 541895) (by norm_num)
theorem B2888453 : Blo 1711056 2888453 := bbase (se 4 (by rfl) ⟨270792, by rfl⟩ : syracuseStep 2888453 = 541585) (by norm_num)
theorem B7312133 : Blo 1711056 7312133 := bbase (se 4 (by rfl) ⟨685512, by rfl⟩ : syracuseStep 7312133 = 1371025) (by norm_num)
theorem B2568965 : Blo 1711056 2568965 := bbase (se 4 (by rfl) ⟨240840, by rfl⟩ : syracuseStep 2568965 = 481681) (by norm_num)
theorem B21943061 : Blo 1711056 21943061 := bbase (se 6 (by rfl) ⟨514290, by rfl⟩ : syracuseStep 21943061 = 1028581) (by norm_num)
theorem B8672021 : Blo 1711056 8672021 := bbase (se 6 (by rfl) ⟨203250, by rfl⟩ : syracuseStep 8672021 = 406501) (by norm_num)
theorem B2568989 : Blo 1711056 2568989 := bbase (se 3 (by rfl) ⟨481685, by rfl⟩ : syracuseStep 2568989 = 963371) (by norm_num)
theorem B2569013 : Blo 1711056 2569013 := bbase (se 5 (by rfl) ⟨120422, by rfl⟩ : syracuseStep 2569013 = 240845) (by norm_num)
theorem B2569037 : Blo 1711056 2569037 := bbase (se 3 (by rfl) ⟨481694, by rfl⟩ : syracuseStep 2569037 = 963389) (by norm_num)
theorem B2569061 : Blo 1711056 2569061 := bbase (se 4 (by rfl) ⟨240849, by rfl⟩ : syracuseStep 2569061 = 481699) (by norm_num)
theorem B2167661 : Blo 1711056 2167661 := bbase (se 3 (by rfl) ⟨406436, by rfl⟩ : syracuseStep 2167661 = 812873) (by norm_num)
theorem B7811957 : Blo 1711056 7811957 := bbase (se 5 (by rfl) ⟨366185, by rfl⟩ : syracuseStep 7811957 = 732371) (by norm_num)
theorem B2569085 : Blo 1711056 2569085 := bbase (se 3 (by rfl) ⟨481703, by rfl⟩ : syracuseStep 2569085 = 963407) (by norm_num)
theorem B2888581 : Blo 1711056 2888581 := bbase (se 4 (by rfl) ⟨270804, by rfl⟩ : syracuseStep 2888581 = 541609) (by norm_num)
theorem B6943637 : Blo 1711056 6943637 := bbase (se 6 (by rfl) ⟨162741, by rfl⟩ : syracuseStep 6943637 = 325483) (by norm_num)
theorem B2569109 : Blo 1711056 2569109 := bbase (se 6 (by rfl) ⟨60213, by rfl⟩ : syracuseStep 2569109 = 120427) (by norm_num)
theorem B2167717 : Blo 1711056 2167717 := bbase (se 4 (by rfl) ⟨203223, by rfl⟩ : syracuseStep 2167717 = 406447) (by norm_num)
theorem B2569133 : Blo 1711056 2569133 := bbase (se 3 (by rfl) ⟨481712, by rfl⟩ : syracuseStep 2569133 = 963425) (by norm_num)
theorem B3470261 : Blo 1711056 3470261 := bbase (se 5 (by rfl) ⟨162668, by rfl⟩ : syracuseStep 3470261 = 325337) (by norm_num)
theorem B6173621 : Blo 1711056 6173621 := bbase (se 5 (by rfl) ⟨289388, by rfl⟩ : syracuseStep 6173621 = 578777) (by norm_num)
theorem B3249085 : Blo 1711056 3249085 := bbase (se 3 (by rfl) ⟨609203, by rfl⟩ : syracuseStep 3249085 = 1218407) (by norm_num)
theorem B2569157 : Blo 1711056 2569157 := bbase (se 4 (by rfl) ⟨240858, by rfl⟩ : syracuseStep 2569157 = 481717) (by norm_num)
theorem B18502613 : Blo 1711056 18502613 := bbase (se 7 (by rfl) ⟨216827, by rfl⟩ : syracuseStep 18502613 = 433655) (by norm_num)
theorem B2888669 : Blo 1711056 2888669 := bbase (se 3 (by rfl) ⟨541625, by rfl⟩ : syracuseStep 2888669 = 1083251) (by norm_num)
theorem B2569181 : Blo 1711056 2569181 := bbase (se 3 (by rfl) ⟨481721, by rfl⟩ : syracuseStep 2569181 = 963443) (by norm_num)
theorem B2569205 : Blo 1711056 2569205 := bbase (se 5 (by rfl) ⟨120431, by rfl⟩ : syracuseStep 2569205 = 240863) (by norm_num)
theorem B2167813 : Blo 1711056 2167813 := bbase (se 4 (by rfl) ⟨203232, by rfl⟩ : syracuseStep 2167813 = 406465) (by norm_num)
theorem B2569229 : Blo 1711056 2569229 := bbase (se 3 (by rfl) ⟨481730, by rfl⟩ : syracuseStep 2569229 = 963461) (by norm_num)
theorem B1758229 : Blo 1711056 1758229 := bbase (se 6 (by rfl) ⟨41208, by rfl⟩ : syracuseStep 1758229 = 82417) (by norm_num)
theorem B13005845 : Blo 1711056 13005845 := bbase (se 6 (by rfl) ⟨304824, by rfl⟩ : syracuseStep 13005845 = 609649) (by norm_num)
theorem B2569253 : Blo 1711056 2569253 := bbase (se 4 (by rfl) ⟨240867, by rfl⟩ : syracuseStep 2569253 = 481735) (by norm_num)
theorem B10417205 : Blo 1711056 10417205 := bbase (se 5 (by rfl) ⟨488306, by rfl⟩ : syracuseStep 10417205 = 976613) (by norm_num)
theorem B2569277 : Blo 1711056 2569277 := bbase (se 3 (by rfl) ⟨481739, by rfl⟩ : syracuseStep 2569277 = 963479) (by norm_num)
theorem B3249229 : Blo 1711056 3249229 := bbase (se 3 (by rfl) ⟨609230, by rfl⟩ : syracuseStep 3249229 = 1218461) (by norm_num)
theorem B2569301 : Blo 1711056 2569301 := bbase (se 8 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 2569301 = 30109) (by norm_num)
theorem B2888797 : Blo 1711056 2888797 := bbase (se 3 (by rfl) ⟨541649, by rfl⟩ : syracuseStep 2888797 = 1083299) (by norm_num)
theorem B2569325 : Blo 1711056 2569325 := bbase (se 3 (by rfl) ⟨481748, by rfl⟩ : syracuseStep 2569325 = 963497) (by norm_num)
theorem B2569349 : Blo 1711056 2569349 := bbase (se 4 (by rfl) ⟨240876, by rfl⟩ : syracuseStep 2569349 = 481753) (by norm_num)
theorem B2569373 : Blo 1711056 2569373 := bbase (se 3 (by rfl) ⟨481757, by rfl⟩ : syracuseStep 2569373 = 963515) (by norm_num)
theorem B2471077 : Blo 1711056 2471077 := bbase (se 4 (by rfl) ⟨231663, by rfl⟩ : syracuseStep 2471077 = 463327) (by norm_num)
theorem B5780645 : Blo 1711056 5780645 := bbase (se 4 (by rfl) ⟨541935, by rfl⟩ : syracuseStep 5780645 = 1083871) (by norm_num)
theorem B2167985 : Blo 1711056 2167985 := bbase (se 2 (by rfl) ⟨812994, by rfl⟩ : syracuseStep 2167985 = 1625989) (by norm_num)
theorem B8664245 : Blo 1711056 8664245 := bbase (se 5 (by rfl) ⟨406136, by rfl⟩ : syracuseStep 8664245 = 812273) (by norm_num)
theorem B2888885 : Blo 1711056 2888885 := bbase (se 5 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 2888885 = 270833) (by norm_num)
theorem B2569397 : Blo 1711056 2569397 := bbase (se 5 (by rfl) ⟨120440, by rfl⟩ : syracuseStep 2569397 = 240881) (by norm_num)
theorem B2569421 : Blo 1711056 2569421 := bbase (se 3 (by rfl) ⟨481766, by rfl⟩ : syracuseStep 2569421 = 963533) (by norm_num)
theorem B2569445 : Blo 1711056 2569445 := bbase (se 4 (by rfl) ⟨240885, by rfl⟩ : syracuseStep 2569445 = 481771) (by norm_num)
theorem B2168041 : Blo 1711056 2168041 := bbase (se 2 (by rfl) ⟨813015, by rfl⟩ : syracuseStep 2168041 = 1626031) (by norm_num)
theorem B3249389 : Blo 1711056 3249389 := bbase (se 3 (by rfl) ⟨609260, by rfl⟩ : syracuseStep 3249389 = 1218521) (by norm_num)
theorem B2569469 : Blo 1711056 2569469 := bbase (se 3 (by rfl) ⟨481775, by rfl⟩ : syracuseStep 2569469 = 963551) (by norm_num)
theorem B2569493 : Blo 1711056 2569493 := bbase (se 6 (by rfl) ⟨60222, by rfl⟩ : syracuseStep 2569493 = 120445) (by norm_num)
theorem B2929949 : Blo 1711056 2929949 := bbase (se 3 (by rfl) ⟨549365, by rfl⟩ : syracuseStep 2929949 = 1098731) (by norm_num)
theorem B2438437 : Blo 1711056 2438437 := bbase (se 4 (by rfl) ⟨228603, by rfl⟩ : syracuseStep 2438437 = 457207) (by norm_num)
theorem B2569517 : Blo 1711056 2569517 := bbase (se 3 (by rfl) ⟨481784, by rfl⟩ : syracuseStep 2569517 = 963569) (by norm_num)
theorem B2889013 : Blo 1711056 2889013 := bbase (se 5 (by rfl) ⟨135422, by rfl⟩ : syracuseStep 2889013 = 270845) (by norm_num)
theorem B2569541 : Blo 1711056 2569541 := bbase (se 4 (by rfl) ⟨240894, by rfl⟩ : syracuseStep 2569541 = 481789) (by norm_num)
theorem B2569565 : Blo 1711056 2569565 := bbase (se 3 (by rfl) ⟨481793, by rfl⟩ : syracuseStep 2569565 = 963587) (by norm_num)
theorem B3249533 : Blo 1711056 3249533 := bbase (se 3 (by rfl) ⟨609287, by rfl⟩ : syracuseStep 3249533 = 1218575) (by norm_num)
theorem B2889101 : Blo 1711056 2889101 := bbase (se 3 (by rfl) ⟨541706, by rfl⟩ : syracuseStep 2889101 = 1083413) (by norm_num)
theorem B2602405 : Blo 1711056 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B12998069 : Blo 1711056 12998069 := bbase (se 5 (by rfl) ⟨609284, by rfl⟩ : syracuseStep 12998069 = 1218569) (by norm_num)
theorem B3904957 : Blo 1711056 3904957 := bbase (se 3 (by rfl) ⟨732179, by rfl⟩ : syracuseStep 3904957 = 1464359) (by norm_num)
theorem B6501829 : Blo 1711056 6501829 := bbase (se 4 (by rfl) ⟨609546, by rfl⟩ : syracuseStep 6501829 = 1219093) (by norm_num)
theorem B3470845 : Blo 1711056 3470845 := bbase (se 3 (by rfl) ⟨650783, by rfl⟩ : syracuseStep 3470845 = 1301567) (by norm_num)
theorem B2889229 : Blo 1711056 2889229 := bbase (se 3 (by rfl) ⟨541730, by rfl⟩ : syracuseStep 2889229 = 1083461) (by norm_num)
theorem B2741845 : Blo 1711056 2741845 := bbase (se 8 (by rfl) ⟨16065, by rfl⟩ : syracuseStep 2741845 = 32131) (by norm_num)
theorem B5781077 : Blo 1711056 5781077 := bbase (se 8 (by rfl) ⟨33873, by rfl⟩ : syracuseStep 5781077 = 67747) (by norm_num)
theorem B2889317 : Blo 1711056 2889317 := bbase (se 4 (by rfl) ⟨270873, by rfl⟩ : syracuseStep 2889317 = 541747) (by norm_num)
theorem B4331141 : Blo 1711056 4331141 := bbase (se 4 (by rfl) ⟨406044, by rfl⟩ : syracuseStep 4331141 = 812089) (by norm_num)
theorem B3249821 : Blo 1711056 3249821 := bbase (se 3 (by rfl) ⟨609341, by rfl⟩ : syracuseStep 3249821 = 1218683) (by norm_num)
theorem B16676533 : Blo 1711056 16676533 := bbase (se 5 (by rfl) ⟨781712, by rfl⟩ : syracuseStep 16676533 = 1563425) (by norm_num)
theorem B2889445 : Blo 1711056 2889445 := bbase (se 4 (by rfl) ⟨270885, by rfl⟩ : syracuseStep 2889445 = 541771) (by norm_num)
theorem B6502133 : Blo 1711056 6502133 := bbase (se 5 (by rfl) ⟨304787, by rfl⟩ : syracuseStep 6502133 = 609575) (by norm_num)
theorem B3249973 : Blo 1711056 3249973 := bbase (se 5 (by rfl) ⟨152342, by rfl⟩ : syracuseStep 3249973 = 304685) (by norm_num)
theorem B2889533 : Blo 1711056 2889533 := bbase (se 3 (by rfl) ⟨541787, by rfl⟩ : syracuseStep 2889533 = 1083575) (by norm_num)
theorem B4331333 : Blo 1711056 4331333 := bbase (se 4 (by rfl) ⟨406062, by rfl⟩ : syracuseStep 4331333 = 812125) (by norm_num)
theorem B2439029 : Blo 1711056 2439029 := bbase (se 5 (by rfl) ⟨114329, by rfl⟩ : syracuseStep 2439029 = 228659) (by norm_num)
theorem B2889661 : Blo 1711056 2889661 := bbase (se 3 (by rfl) ⟨541811, by rfl⟩ : syracuseStep 2889661 = 1083623) (by norm_num)
theorem B6256597 : Blo 1711056 6256597 := bbase (se 7 (by rfl) ⟨73319, by rfl⟩ : syracuseStep 6256597 = 146639) (by norm_num)
theorem B9754613 : Blo 1711056 9754613 := bbase (se 5 (by rfl) ⟨457247, by rfl⟩ : syracuseStep 9754613 = 914495) (by norm_num)
theorem B5781509 : Blo 1711056 5781509 := bbase (se 4 (by rfl) ⟨542016, by rfl⟩ : syracuseStep 5781509 = 1084033) (by norm_num)
theorem B2742293 : Blo 1711056 2742293 := bbase (se 6 (by rfl) ⟨64272, by rfl⟩ : syracuseStep 2742293 = 128545) (by norm_num)
theorem B2889749 : Blo 1711056 2889749 := bbase (se 6 (by rfl) ⟨67728, by rfl⟩ : syracuseStep 2889749 = 135457) (by norm_num)
theorem B3905597 : Blo 1711056 3905597 := bbase (se 3 (by rfl) ⟨732299, by rfl⟩ : syracuseStep 3905597 = 1464599) (by norm_num)
theorem B3250277 : Blo 1711056 3250277 := bbase (se 4 (by rfl) ⟨304713, by rfl⟩ : syracuseStep 3250277 = 609427) (by norm_num)
theorem B3127405 : Blo 1711056 3127405 := bbase (se 3 (by rfl) ⟨586388, by rfl⟩ : syracuseStep 3127405 = 1172777) (by norm_num)
theorem B2889877 : Blo 1711056 2889877 := bbase (se 6 (by rfl) ⟨67731, by rfl⟩ : syracuseStep 2889877 = 135463) (by norm_num)
theorem B4331677 : Blo 1711056 4331677 := bbase (se 3 (by rfl) ⟨812189, by rfl⟩ : syracuseStep 4331677 = 1624379) (by norm_num)
theorem B2742493 : Blo 1711056 2742493 := bbase (se 3 (by rfl) ⟨514217, by rfl⟩ : syracuseStep 2742493 = 1028435) (by norm_num)
theorem B2889965 : Blo 1711056 2889965 := bbase (se 3 (by rfl) ⟨541868, by rfl⟩ : syracuseStep 2889965 = 1083737) (by norm_num)
theorem B4331789 : Blo 1711056 4331789 := bbase (se 3 (by rfl) ⟨812210, by rfl⟩ : syracuseStep 4331789 = 1624421) (by norm_num)
theorem B5486933 : Blo 1711056 5486933 := bbase (se 10 (by rfl) ⟨8037, by rfl⟩ : syracuseStep 5486933 = 16075) (by norm_num)
theorem B2890093 : Blo 1711056 2890093 := bbase (se 3 (by rfl) ⟨541892, by rfl⟩ : syracuseStep 2890093 = 1083785) (by norm_num)
theorem B8665541 : Blo 1711056 8665541 := bbase (se 4 (by rfl) ⟨812394, by rfl⟩ : syracuseStep 8665541 = 1624789) (by norm_num)
theorem B2890181 : Blo 1711056 2890181 := bbase (se 4 (by rfl) ⟨270954, by rfl⟩ : syracuseStep 2890181 = 541909) (by norm_num)
theorem B4331981 : Blo 1711056 4331981 := bbase (se 3 (by rfl) ⟨812246, by rfl⟩ : syracuseStep 4331981 = 1624493) (by norm_num)
theorem B2742749 : Blo 1711056 2742749 := bbase (se 3 (by rfl) ⟨514265, by rfl⟩ : syracuseStep 2742749 = 1028531) (by norm_num)
theorem B10975733 : Blo 1711056 10975733 := bbase (se 5 (by rfl) ⟨514487, by rfl⟩ : syracuseStep 10975733 = 1028975) (by norm_num)
theorem B2603573 : Blo 1711056 2603573 := bbase (se 5 (by rfl) ⟨122042, by rfl⟩ : syracuseStep 2603573 = 244085) (by norm_num)
theorem B4872773 : Blo 1711056 4872773 := bbase (se 4 (by rfl) ⟨456822, by rfl⟩ : syracuseStep 4872773 = 913645) (by norm_num)
theorem B2890309 : Blo 1711056 2890309 := bbase (se 4 (by rfl) ⟨270966, by rfl⟩ : syracuseStep 2890309 = 541933) (by norm_num)
theorem B3906125 : Blo 1711056 3906125 := bbase (se 3 (by rfl) ⟨732398, by rfl⟩ : syracuseStep 3906125 = 1464797) (by norm_num)
theorem B2890397 : Blo 1711056 2890397 := bbase (se 3 (by rfl) ⟨541949, by rfl⟩ : syracuseStep 2890397 = 1083899) (by norm_num)
theorem B5274341 : Blo 1711056 5274341 := bbase (se 4 (by rfl) ⟨494469, by rfl⟩ : syracuseStep 5274341 = 988939) (by norm_num)
theorem B2890525 : Blo 1711056 2890525 := bbase (se 3 (by rfl) ⟨541973, by rfl⟩ : syracuseStep 2890525 = 1083947) (by norm_num)
theorem B4332325 : Blo 1711056 4332325 := bbase (se 4 (by rfl) ⟨406155, by rfl⟩ : syracuseStep 4332325 = 812311) (by norm_num)
theorem B3251029 : Blo 1711056 3251029 := bbase (se 9 (by rfl) ⟨9524, by rfl⟩ : syracuseStep 3251029 = 19049) (by norm_num)
theorem B2890613 : Blo 1711056 2890613 := bbase (se 5 (by rfl) ⟨135497, by rfl⟩ : syracuseStep 2890613 = 270995) (by norm_num)
theorem B1735553 : Blo 1711056 1735553 := bbase (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) (by norm_num)
theorem B4168589 : Blo 1711056 4168589 := bbase (se 3 (by rfl) ⟨781610, by rfl⟩ : syracuseStep 4168589 = 1563221) (by norm_num)
theorem B4332437 : Blo 1711056 4332437 := bbase (se 6 (by rfl) ⟨101541, by rfl⟩ : syracuseStep 4332437 = 203083) (by norm_num)
theorem B1735601 : Blo 1711056 1735601 := bbase (se 2 (by rfl) ⟨650850, by rfl⟩ : syracuseStep 1735601 = 1301701) (by norm_num)
theorem B3251173 : Blo 1711056 3251173 := bbase (se 4 (by rfl) ⟨304797, by rfl⟩ : syracuseStep 3251173 = 609595) (by norm_num)
theorem B2890741 : Blo 1711056 2890741 := bbase (se 5 (by rfl) ⟨135503, by rfl⟩ : syracuseStep 2890741 = 271007) (by norm_num)
theorem B3128341 : Blo 1711056 3128341 := bbase (se 6 (by rfl) ⟨73320, by rfl⟩ : syracuseStep 3128341 = 146641) (by norm_num)
theorem B4627525 : Blo 1711056 4627525 := bbase (se 4 (by rfl) ⟨433830, by rfl⟩ : syracuseStep 4627525 = 867661) (by norm_num)
theorem B4332629 : Blo 1711056 4332629 := bbase (se 8 (by rfl) ⟨25386, by rfl⟩ : syracuseStep 4332629 = 50773) (by norm_num)
theorem B3251333 : Blo 1711056 3251333 := bbase (se 4 (by rfl) ⟨304812, by rfl⟩ : syracuseStep 3251333 = 609625) (by norm_num)
theorem B3472589 : Blo 1711056 3472589 := bbase (se 3 (by rfl) ⟨651110, by rfl⟩ : syracuseStep 3472589 = 1302221) (by norm_num)
theorem B3251477 : Blo 1711056 3251477 := bbase (se 6 (by rfl) ⟨76206, by rfl⟩ : syracuseStep 3251477 = 152413) (by norm_num)
theorem B8224037 : Blo 1711056 8224037 := bbase (se 4 (by rfl) ⟨771003, by rfl⟩ : syracuseStep 8224037 = 1542007) (by norm_num)
theorem B4332973 : Blo 1711056 4332973 := bbase (se 3 (by rfl) ⟨812432, by rfl⟩ : syracuseStep 4332973 = 1624865) (by norm_num)
theorem B4627925 : Blo 1711056 4627925 := bbase (se 7 (by rfl) ⟨54233, by rfl⟩ : syracuseStep 4627925 = 108467) (by norm_num)
theorem B1736165 : Blo 1711056 1736165 := bbase (se 4 (by rfl) ⟨162765, by rfl⟩ : syracuseStep 1736165 = 325531) (by norm_num)
theorem B2604557 : Blo 1711056 2604557 := bbase (se 3 (by rfl) ⟨488354, by rfl⟩ : syracuseStep 2604557 = 976709) (by norm_num)
theorem B4333085 : Blo 1711056 4333085 := bbase (se 3 (by rfl) ⟨812453, by rfl⟩ : syracuseStep 4333085 = 1624907) (by norm_num)
theorem B2055721 : Blo 1711056 2055721 := bbase (se 2 (by rfl) ⟨770895, by rfl⟩ : syracuseStep 2055721 = 1541791) (by norm_num)
theorem B5561909 : Blo 1711056 5561909 := bbase (se 5 (by rfl) ⟨260714, by rfl⟩ : syracuseStep 5561909 = 521429) (by norm_num)
theorem B3251765 : Blo 1711056 3251765 := bbase (se 5 (by rfl) ⟨152426, by rfl⟩ : syracuseStep 3251765 = 304853) (by norm_num)
theorem B2743877 : Blo 1711056 2743877 := bbase (se 4 (by rfl) ⟨257238, by rfl⟩ : syracuseStep 2743877 = 514477) (by norm_num)
theorem B4628053 : Blo 1711056 4628053 := bbase (se 8 (by rfl) ⟨27117, by rfl⟩ : syracuseStep 4628053 = 54235) (by norm_num)
theorem B3849893 : Blo 1711056 3849893 := bbase (se 4 (by rfl) ⟨360927, by rfl⟩ : syracuseStep 3849893 = 721855) (by norm_num)
theorem B5775029 : Blo 1711056 5775029 := bbase (se 5 (by rfl) ⟨270704, by rfl⟩ : syracuseStep 5775029 = 541409) (by norm_num)
theorem B3251917 : Blo 1711056 3251917 := bbase (se 3 (by rfl) ⟨609734, by rfl⟩ : syracuseStep 3251917 = 1219469) (by norm_num)
theorem B8666837 : Blo 1711056 8666837 := bbase (se 7 (by rfl) ⟨101564, by rfl⟩ : syracuseStep 8666837 = 203129) (by norm_num)
theorem B4333277 : Blo 1711056 4333277 := bbase (se 3 (by rfl) ⟨812489, by rfl⟩ : syracuseStep 4333277 = 1624979) (by norm_num)
theorem B3849965 : Blo 1711056 3849965 := bbase (se 3 (by rfl) ⟨721868, by rfl⟩ : syracuseStep 3849965 = 1443737) (by norm_num)
theorem B2055985 : Blo 1711056 2055985 := bbase (se 2 (by rfl) ⟨770994, by rfl⟩ : syracuseStep 2055985 = 1541989) (by norm_num)
theorem B3850037 : Blo 1711056 3850037 := bbase (se 5 (by rfl) ⟨180470, by rfl⟩ : syracuseStep 3850037 = 360941) (by norm_num)
theorem B6504245 : Blo 1711056 6504245 := bbase (se 5 (by rfl) ⟨304886, by rfl⟩ : syracuseStep 6504245 = 609773) (by norm_num)
theorem B8781637 : Blo 1711056 8781637 := bbase (se 4 (by rfl) ⟨823278, by rfl⟩ : syracuseStep 8781637 = 1646557) (by norm_num)
theorem B1924969 : Blo 1711056 1924969 := bbase (se 2 (by rfl) ⟨721863, by rfl⟩ : syracuseStep 1924969 = 1443727) (by norm_num)
theorem B3850109 : Blo 1711056 3850109 := bbase (se 3 (by rfl) ⟨721895, by rfl⟩ : syracuseStep 3850109 = 1443791) (by norm_num)
theorem B1925005 : Blo 1711056 1925005 := bbase (se 3 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 1925005 = 721877) (by norm_num)
theorem B2056105 : Blo 1711056 2056105 := bbase (se 2 (by rfl) ⟨771039, by rfl⟩ : syracuseStep 2056105 = 1542079) (by norm_num)
theorem B1925041 : Blo 1711056 1925041 := bbase (se 2 (by rfl) ⟨721890, by rfl⟩ : syracuseStep 1925041 = 1443781) (by norm_num)
theorem B3850181 : Blo 1711056 3850181 := bbase (se 4 (by rfl) ⟨360954, by rfl⟩ : syracuseStep 3850181 = 721909) (by norm_num)
theorem B1925077 : Blo 1711056 1925077 := bbase (se 7 (by rfl) ⟨22559, by rfl⟩ : syracuseStep 1925077 = 45119) (by norm_num)
theorem B4333571 : Blo 1711056 4333571 := bstep (se 1 (by rfl) ⟨3250178, by rfl⟩ : syracuseStep 4333571 = 6500357) B6500357
theorem B1712131 : Blo 1711056 1712131 := bstep (se 1 (by rfl) ⟨1284098, by rfl⟩ : syracuseStep 1712131 = 2568197) B2568197
theorem B1712147 : Blo 1711056 1712147 := bstep (se 1 (by rfl) ⟨1284110, by rfl⟩ : syracuseStep 1712147 = 2568221) B2568221
theorem B1712163 : Blo 1711056 1712163 := bstep (se 1 (by rfl) ⟨1284122, by rfl⟩ : syracuseStep 1712163 = 2568245) B2568245
theorem B3850289 : Blo 1711056 3850289 := bstep (se 2 (by rfl) ⟨1443858, by rfl⟩ : syracuseStep 3850289 = 2887717) B2887717
theorem B1712179 : Blo 1711056 1712179 := bstep (se 1 (by rfl) ⟨1284134, by rfl⟩ : syracuseStep 1712179 = 2568269) B2568269
theorem B3850307 : Blo 1711056 3850307 := bstep (se 1 (by rfl) ⟨2887730, by rfl⟩ : syracuseStep 3850307 = 5775461) B5775461
theorem B1712195 : Blo 1711056 1712195 := bstep (se 1 (by rfl) ⟨1284146, by rfl⟩ : syracuseStep 1712195 = 2568293) B2568293
theorem B1925203 : Blo 1711056 1925203 := bstep (se 1 (by rfl) ⟨1443902, by rfl⟩ : syracuseStep 1925203 = 2887805) B2887805
theorem B1712211 : Blo 1711056 1712211 := bstep (se 1 (by rfl) ⟨1284158, by rfl⟩ : syracuseStep 1712211 = 2568317) B2568317
theorem B1712227 : Blo 1711056 1712227 := bstep (se 1 (by rfl) ⟨1284170, by rfl⟩ : syracuseStep 1712227 = 2568341) B2568341
theorem B1712243 : Blo 1711056 1712243 := bstep (se 1 (by rfl) ⟨1284182, by rfl⟩ : syracuseStep 1712243 = 2568365) B2568365
theorem B1712259 : Blo 1711056 1712259 := bstep (se 1 (by rfl) ⟨1284194, by rfl⟩ : syracuseStep 1712259 = 2568389) B2568389
theorem B8781965 : Blo 1711056 8781965 := bstep (se 3 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 8781965 = 3293237) B3293237
theorem B27779213 : Blo 1711056 27779213 := bstep (se 3 (by rfl) ⟨5208602, by rfl⟩ : syracuseStep 27779213 = 10417205) B10417205
theorem B4169873 : Blo 1711056 4169873 := bstep (se 2 (by rfl) ⟨1563702, by rfl⟩ : syracuseStep 4169873 = 3127405) B3127405
theorem B1712275 : Blo 1711056 1712275 := bstep (se 1 (by rfl) ⟨1284206, by rfl⟩ : syracuseStep 1712275 = 2568413) B2568413
theorem B1712291 : Blo 1711056 1712291 := bstep (se 1 (by rfl) ⟨1284218, by rfl⟩ : syracuseStep 1712291 = 2568437) B2568437
theorem B4874413 : Blo 1711056 4874413 := bstep (se 3 (by rfl) ⟨913952, by rfl⟩ : syracuseStep 4874413 = 1827905) B1827905
theorem B1712307 : Blo 1711056 1712307 := bstep (se 1 (by rfl) ⟨1284230, by rfl⟩ : syracuseStep 1712307 = 2568461) B2568461
theorem B4333763 : Blo 1711056 4333763 := bstep (se 1 (by rfl) ⟨3250322, by rfl⟩ : syracuseStep 4333763 = 6500645) B6500645
theorem B1712323 : Blo 1711056 1712323 := bstep (se 1 (by rfl) ⟨1284242, by rfl⟩ : syracuseStep 1712323 = 2568485) B2568485
theorem B8790221 : Blo 1711056 8790221 := bstep (se 3 (by rfl) ⟨1648166, by rfl⟩ : syracuseStep 8790221 = 3296333) B3296333
theorem B5775569 : Blo 1711056 5775569 := bstep (se 2 (by rfl) ⟨2165838, by rfl⟩ : syracuseStep 5775569 = 4331677) B4331677
theorem B1712339 : Blo 1711056 1712339 := bstep (se 1 (by rfl) ⟨1284254, by rfl⟩ : syracuseStep 1712339 = 2568509) B2568509
theorem B1925347 : Blo 1711056 1925347 := bstep (se 1 (by rfl) ⟨1444010, by rfl⟩ : syracuseStep 1925347 = 2888021) B2888021
theorem B1712355 : Blo 1711056 1712355 := bstep (se 1 (by rfl) ⟨1284266, by rfl⟩ : syracuseStep 1712355 = 2568533) B2568533
theorem B1712371 : Blo 1711056 1712371 := bstep (se 1 (by rfl) ⟨1284278, by rfl⟩ : syracuseStep 1712371 = 2568557) B2568557
theorem B1712387 : Blo 1711056 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B1712403 : Blo 1711056 1712403 := bstep (se 1 (by rfl) ⟨1284302, by rfl⟩ : syracuseStep 1712403 = 2568605) B2568605
theorem B1712419 : Blo 1711056 1712419 := bstep (se 1 (by rfl) ⟨1284314, by rfl⟩ : syracuseStep 1712419 = 2568629) B2568629
theorem B1712435 : Blo 1711056 1712435 := bstep (se 1 (by rfl) ⟨1284326, by rfl⟩ : syracuseStep 1712435 = 2568653) B2568653
theorem B1712451 : Blo 1711056 1712451 := bstep (se 1 (by rfl) ⟨1284338, by rfl⟩ : syracuseStep 1712451 = 2568677) B2568677
theorem B4874573 : Blo 1711056 4874573 := bstep (se 3 (by rfl) ⟨913982, by rfl⟩ : syracuseStep 4874573 = 1827965) B1827965
theorem B3850577 : Blo 1711056 3850577 := bstep (se 2 (by rfl) ⟨1443966, by rfl⟩ : syracuseStep 3850577 = 2887933) B2887933
theorem B1712467 : Blo 1711056 1712467 := bstep (se 1 (by rfl) ⟨1284350, by rfl⟩ : syracuseStep 1712467 = 2568701) B2568701
theorem B3850595 : Blo 1711056 3850595 := bstep (se 1 (by rfl) ⟨2887946, by rfl⟩ : syracuseStep 3850595 = 5775893) B5775893
theorem B2056547 : Blo 1711056 2056547 := bstep (se 1 (by rfl) ⟨1542410, by rfl⟩ : syracuseStep 2056547 = 3084821) B3084821
theorem B1712483 : Blo 1711056 1712483 := bstep (se 1 (by rfl) ⟨1284362, by rfl⟩ : syracuseStep 1712483 = 2568725) B2568725
theorem B1925491 : Blo 1711056 1925491 := bstep (se 1 (by rfl) ⟨1444118, by rfl⟩ : syracuseStep 1925491 = 2888237) B2888237
theorem B1712499 : Blo 1711056 1712499 := bstep (se 1 (by rfl) ⟨1284374, by rfl⟩ : syracuseStep 1712499 = 2568749) B2568749
theorem B1712515 : Blo 1711056 1712515 := bstep (se 1 (by rfl) ⟨1284386, by rfl⟩ : syracuseStep 1712515 = 2568773) B2568773
theorem B1712531 : Blo 1711056 1712531 := bstep (se 1 (by rfl) ⟨1284398, by rfl⟩ : syracuseStep 1712531 = 2568797) B2568797
theorem B1827235 : Blo 1711056 1827235 := bstep (se 1 (by rfl) ⟨1370426, by rfl⟩ : syracuseStep 1827235 = 2740853) B2740853
theorem B1712547 : Blo 1711056 1712547 := bstep (se 1 (by rfl) ⟨1284410, by rfl⟩ : syracuseStep 1712547 = 2568821) B2568821
theorem B1712563 : Blo 1711056 1712563 := bstep (se 1 (by rfl) ⟨1284422, by rfl⟩ : syracuseStep 1712563 = 2568845) B2568845
theorem B1712579 : Blo 1711056 1712579 := bstep (se 1 (by rfl) ⟨1284434, by rfl⟩ : syracuseStep 1712579 = 2568869) B2568869
theorem B1712595 : Blo 1711056 1712595 := bstep (se 1 (by rfl) ⟨1284446, by rfl⟩ : syracuseStep 1712595 = 2568893) B2568893
theorem B1712611 : Blo 1711056 1712611 := bstep (se 1 (by rfl) ⟨1284458, by rfl⟩ : syracuseStep 1712611 = 2568917) B2568917
theorem B1712627 : Blo 1711056 1712627 := bstep (se 1 (by rfl) ⟨1284470, by rfl⟩ : syracuseStep 1712627 = 2568941) B2568941
theorem B1925635 : Blo 1711056 1925635 := bstep (se 1 (by rfl) ⟨1444226, by rfl⟩ : syracuseStep 1925635 = 2888453) B2888453
theorem B4874755 : Blo 1711056 4874755 := bstep (se 1 (by rfl) ⟨3656066, by rfl⟩ : syracuseStep 4874755 = 7312133) B7312133
theorem B1712643 : Blo 1711056 1712643 := bstep (se 1 (by rfl) ⟨1284482, by rfl⟩ : syracuseStep 1712643 = 2568965) B2568965
theorem B1712659 : Blo 1711056 1712659 := bstep (se 1 (by rfl) ⟨1284494, by rfl⟩ : syracuseStep 1712659 = 2568989) B2568989
theorem B1712675 : Blo 1711056 1712675 := bstep (se 1 (by rfl) ⟨1284506, by rfl⟩ : syracuseStep 1712675 = 2569013) B2569013
theorem B1712691 : Blo 1711056 1712691 := bstep (se 1 (by rfl) ⟨1284518, by rfl⟩ : syracuseStep 1712691 = 2569037) B2569037
theorem B1712707 : Blo 1711056 1712707 := bstep (se 1 (by rfl) ⟨1284530, by rfl⟩ : syracuseStep 1712707 = 2569061) B2569061
theorem B9634373 : Blo 1711056 9634373 := bstep (se 4 (by rfl) ⟨903222, by rfl⟩ : syracuseStep 9634373 = 1806445) B1806445
theorem B1712723 : Blo 1711056 1712723 := bstep (se 1 (by rfl) ⟨1284542, by rfl⟩ : syracuseStep 1712723 = 2569085) B2569085
theorem B4629091 : Blo 1711056 4629091 := bstep (se 1 (by rfl) ⟨3471818, by rfl⟩ : syracuseStep 4629091 = 6943637) B6943637
theorem B1712739 : Blo 1711056 1712739 := bstep (se 1 (by rfl) ⟨1284554, by rfl⟩ : syracuseStep 1712739 = 2569109) B2569109
theorem B3850865 : Blo 1711056 3850865 := bstep (se 2 (by rfl) ⟨1444074, by rfl⟩ : syracuseStep 3850865 = 2888149) B2888149
theorem B1712755 : Blo 1711056 1712755 := bstep (se 1 (by rfl) ⟨1284566, by rfl⟩ : syracuseStep 1712755 = 2569133) B2569133
theorem B3850883 : Blo 1711056 3850883 := bstep (se 1 (by rfl) ⟨2888162, by rfl⟩ : syracuseStep 3850883 = 5776325) B5776325
theorem B1712771 : Blo 1711056 1712771 := bstep (se 1 (by rfl) ⟨1284578, by rfl⟩ : syracuseStep 1712771 = 2569157) B2569157
theorem B1925779 : Blo 1711056 1925779 := bstep (se 1 (by rfl) ⟨1444334, by rfl⟩ : syracuseStep 1925779 = 2888669) B2888669
theorem B1712787 : Blo 1711056 1712787 := bstep (se 1 (by rfl) ⟨1284590, by rfl⟩ : syracuseStep 1712787 = 2569181) B2569181
theorem B8782499 : Blo 1711056 8782499 := bstep (se 1 (by rfl) ⟨6586874, by rfl⟩ : syracuseStep 8782499 = 13173749) B13173749
theorem B1712803 : Blo 1711056 1712803 := bstep (se 1 (by rfl) ⟨1284602, by rfl⟩ : syracuseStep 1712803 = 2569205) B2569205
theorem B1712819 : Blo 1711056 1712819 := bstep (se 1 (by rfl) ⟨1284614, by rfl⟩ : syracuseStep 1712819 = 2569229) B2569229
theorem B1712835 : Blo 1711056 1712835 := bstep (se 1 (by rfl) ⟨1284626, by rfl⟩ : syracuseStep 1712835 = 2569253) B2569253
theorem B1712851 : Blo 1711056 1712851 := bstep (se 1 (by rfl) ⟨1284638, by rfl⟩ : syracuseStep 1712851 = 2569277) B2569277
theorem B79086293 : Blo 1711056 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B1712867 : Blo 1711056 1712867 := bstep (se 1 (by rfl) ⟨1284650, by rfl⟩ : syracuseStep 1712867 = 2569301) B2569301
theorem B5776109 : Blo 1711056 5776109 := bstep (se 3 (by rfl) ⟨1083020, by rfl⟩ : syracuseStep 5776109 = 2166041) B2166041
theorem B1712883 : Blo 1711056 1712883 := bstep (se 1 (by rfl) ⟨1284662, by rfl⟩ : syracuseStep 1712883 = 2569325) B2569325
theorem B1712899 : Blo 1711056 1712899 := bstep (se 1 (by rfl) ⟨1284674, by rfl⟩ : syracuseStep 1712899 = 2569349) B2569349
theorem B1712915 : Blo 1711056 1712915 := bstep (se 1 (by rfl) ⟨1284686, by rfl⟩ : syracuseStep 1712915 = 2569373) B2569373
theorem B5776163 : Blo 1711056 5776163 := bstep (se 1 (by rfl) ⟨4332122, by rfl⟩ : syracuseStep 5776163 = 8664245) B8664245
theorem B1925923 : Blo 1711056 1925923 := bstep (se 1 (by rfl) ⟨1444442, by rfl⟩ : syracuseStep 1925923 = 2888885) B2888885
theorem B1712931 : Blo 1711056 1712931 := bstep (se 1 (by rfl) ⟨1284698, by rfl⟩ : syracuseStep 1712931 = 2569397) B2569397
theorem B1712947 : Blo 1711056 1712947 := bstep (se 1 (by rfl) ⟨1284710, by rfl⟩ : syracuseStep 1712947 = 2569421) B2569421
theorem B1712963 : Blo 1711056 1712963 := bstep (se 1 (by rfl) ⟨1284722, by rfl⟩ : syracuseStep 1712963 = 2569445) B2569445
theorem B1712979 : Blo 1711056 1712979 := bstep (se 1 (by rfl) ⟨1284734, by rfl⟩ : syracuseStep 1712979 = 2569469) B2569469
theorem B1712995 : Blo 1711056 1712995 := bstep (se 1 (by rfl) ⟨1284746, by rfl⟩ : syracuseStep 1712995 = 2569493) B2569493
theorem B1713011 : Blo 1711056 1713011 := bstep (se 1 (by rfl) ⟨1284758, by rfl⟩ : syracuseStep 1713011 = 2569517) B2569517
theorem B1713027 : Blo 1711056 1713027 := bstep (se 1 (by rfl) ⟨1284770, by rfl⟩ : syracuseStep 1713027 = 2569541) B2569541
theorem B3851153 : Blo 1711056 3851153 := bstep (se 2 (by rfl) ⟨1444182, by rfl⟩ : syracuseStep 3851153 = 2888365) B2888365
theorem B1713043 : Blo 1711056 1713043 := bstep (se 1 (by rfl) ⟨1284782, by rfl⟩ : syracuseStep 1713043 = 2569565) B2569565
theorem B3851171 : Blo 1711056 3851171 := bstep (se 1 (by rfl) ⟨2888378, by rfl⟩ : syracuseStep 3851171 = 5776757) B5776757
theorem B1926067 : Blo 1711056 1926067 := bstep (se 1 (by rfl) ⟨1444550, by rfl⟩ : syracuseStep 1926067 = 2889101) B2889101
theorem B88941509 : Blo 1711056 88941509 := bstep (se 4 (by rfl) ⟨8338266, by rfl⟩ : syracuseStep 88941509 = 16676533) B16676533
theorem B5776433 : Blo 1711056 5776433 := bstep (se 2 (by rfl) ⟨2166162, by rfl⟩ : syracuseStep 5776433 = 4332325) B4332325
theorem B1926211 : Blo 1711056 1926211 := bstep (se 1 (by rfl) ⟨1444658, by rfl⟩ : syracuseStep 1926211 = 2889317) B2889317
theorem B4334705 : Blo 1711056 4334705 := bstep (se 2 (by rfl) ⟨1625514, by rfl⟩ : syracuseStep 4334705 = 3251029) B3251029
theorem B4334755 : Blo 1711056 4334755 := bstep (se 1 (by rfl) ⟨3251066, by rfl⟩ : syracuseStep 4334755 = 6502133) B6502133
theorem B3851441 : Blo 1711056 3851441 := bstep (se 2 (by rfl) ⟨1444290, by rfl⟩ : syracuseStep 3851441 = 2888581) B2888581
theorem B3851459 : Blo 1711056 3851459 := bstep (se 1 (by rfl) ⟨2888594, by rfl⟩ : syracuseStep 3851459 = 5777189) B5777189
theorem B1926355 : Blo 1711056 1926355 := bstep (se 1 (by rfl) ⟨1444766, by rfl⟩ : syracuseStep 1926355 = 2889533) B2889533
theorem B4629773 : Blo 1711056 4629773 := bstep (se 3 (by rfl) ⟨868082, by rfl⟩ : syracuseStep 4629773 = 1736165) B1736165
theorem B10552625 : Blo 1711056 10552625 := bstep (se 2 (by rfl) ⟨3957234, by rfl⟩ : syracuseStep 10552625 = 7914469) B7914469
theorem B4334897 : Blo 1711056 4334897 := bstep (se 2 (by rfl) ⟨1625586, by rfl⟩ : syracuseStep 4334897 = 3251173) B3251173
theorem B1852723 : Blo 1711056 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B1926499 : Blo 1711056 1926499 := bstep (se 1 (by rfl) ⟨1444874, by rfl⟩ : syracuseStep 1926499 = 2889749) B2889749
theorem B4171121 : Blo 1711056 4171121 := bstep (se 2 (by rfl) ⟨1564170, by rfl⟩ : syracuseStep 4171121 = 3128341) B3128341
theorem B6170033 : Blo 1711056 6170033 := bstep (se 2 (by rfl) ⟨2313762, by rfl⟩ : syracuseStep 6170033 = 4627525) B4627525
theorem B3851729 : Blo 1711056 3851729 := bstep (se 2 (by rfl) ⟨1444398, by rfl⟩ : syracuseStep 3851729 = 2888797) B2888797
theorem B3851747 : Blo 1711056 3851747 := bstep (se 1 (by rfl) ⟨2888810, by rfl⟩ : syracuseStep 3851747 = 5777621) B5777621
theorem B1926643 : Blo 1711056 1926643 := bstep (se 1 (by rfl) ⟨1444982, by rfl⟩ : syracuseStep 1926643 = 2889965) B2889965
theorem B5776973 : Blo 1711056 5776973 := bstep (se 3 (by rfl) ⟨1083182, by rfl⟩ : syracuseStep 5776973 = 2166365) B2166365
theorem B5777027 : Blo 1711056 5777027 := bstep (se 1 (by rfl) ⟨4332770, by rfl⟩ : syracuseStep 5777027 = 8665541) B8665541
theorem B1926787 : Blo 1711056 1926787 := bstep (se 1 (by rfl) ⟨1445090, by rfl⟩ : syracuseStep 1926787 = 2890181) B2890181
theorem B10020485 : Blo 1711056 10020485 := bstep (se 4 (by rfl) ⟨939420, by rfl⟩ : syracuseStep 10020485 = 1878841) B1878841
theorem B1828499 : Blo 1711056 1828499 := bstep (se 1 (by rfl) ⟨1371374, by rfl⟩ : syracuseStep 1828499 = 2742749) B2742749
theorem B7317155 : Blo 1711056 7317155 := bstep (se 1 (by rfl) ⟨5487866, by rfl⟩ : syracuseStep 7317155 = 10975733) B10975733
theorem B3852017 : Blo 1711056 3852017 := bstep (se 2 (by rfl) ⟨1444506, by rfl⟩ : syracuseStep 3852017 = 2889013) B2889013
theorem B3852035 : Blo 1711056 3852035 := bstep (se 1 (by rfl) ⟨2889026, by rfl⟩ : syracuseStep 3852035 = 5778053) B5778053
theorem B1926931 : Blo 1711056 1926931 := bstep (se 1 (by rfl) ⟨1445198, by rfl⟩ : syracuseStep 1926931 = 2890397) B2890397
theorem B7309091 : Blo 1711056 7309091 := bstep (se 1 (by rfl) ⟨5481818, by rfl⟩ : syracuseStep 7309091 = 10963637) B10963637
theorem B3516227 : Blo 1711056 3516227 := bstep (se 1 (by rfl) ⟨2637170, by rfl⟩ : syracuseStep 3516227 = 5274341) B5274341
theorem B4876145 : Blo 1711056 4876145 := bstep (se 2 (by rfl) ⟨1828554, by rfl⟩ : syracuseStep 4876145 = 3657109) B3657109
theorem B5777297 : Blo 1711056 5777297 := bstep (se 2 (by rfl) ⟨2166486, by rfl⟩ : syracuseStep 5777297 = 4332973) B4332973
theorem B1927075 : Blo 1711056 1927075 := bstep (se 1 (by rfl) ⟨1445306, by rfl⟩ : syracuseStep 1927075 = 2890613) B2890613
theorem B8669105 : Blo 1711056 8669105 := bstep (se 2 (by rfl) ⟨3250914, by rfl⟩ : syracuseStep 8669105 = 6501829) B6501829
theorem B2197459 : Blo 1711056 2197459 := bstep (se 1 (by rfl) ⟨1648094, by rfl⟩ : syracuseStep 2197459 = 3296189) B3296189
theorem B3852305 : Blo 1711056 3852305 := bstep (se 2 (by rfl) ⟨1444614, by rfl⟩ : syracuseStep 3852305 = 2889229) B2889229
theorem B3852323 : Blo 1711056 3852323 := bstep (se 1 (by rfl) ⟨2889242, by rfl⟩ : syracuseStep 3852323 = 5778485) B5778485
theorem B3295331 : Blo 1711056 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B3655793 : Blo 1711056 3655793 := bstep (se 2 (by rfl) ⟨1370922, by rfl⟩ : syracuseStep 3655793 = 2741845) B2741845
theorem B6170737 : Blo 1711056 6170737 := bstep (se 2 (by rfl) ⟨2314026, by rfl⟩ : syracuseStep 6170737 = 4628053) B4628053
theorem B5482691 : Blo 1711056 5482691 := bstep (se 1 (by rfl) ⟨4112018, by rfl⟩ : syracuseStep 5482691 = 8224037) B8224037
theorem B4335889 : Blo 1711056 4335889 := bstep (se 2 (by rfl) ⟨1625958, by rfl⟩ : syracuseStep 4335889 = 3251917) B3251917
theorem B3852593 : Blo 1711056 3852593 := bstep (se 2 (by rfl) ⟨1444722, by rfl⟩ : syracuseStep 3852593 = 2889445) B2889445
theorem B3852611 : Blo 1711056 3852611 := bstep (se 1 (by rfl) ⟨2889458, by rfl⟩ : syracuseStep 3852611 = 5778917) B5778917
theorem B1952131 : Blo 1711056 1952131 := bstep (se 1 (by rfl) ⟨1464098, by rfl⟩ : syracuseStep 1952131 = 2928197) B2928197
theorem B1829251 : Blo 1711056 1829251 := bstep (se 1 (by rfl) ⟨1371938, by rfl⟩ : syracuseStep 1829251 = 2743877) B2743877
theorem B6498701 : Blo 1711056 6498701 := bstep (se 3 (by rfl) ⟨1218506, by rfl⟩ : syracuseStep 6498701 = 2437013) B2437013
theorem B5777837 : Blo 1711056 5777837 := bstep (se 3 (by rfl) ⟨1083344, by rfl⟩ : syracuseStep 5777837 = 2166689) B2166689
theorem B11708849 : Blo 1711056 11708849 := bstep (se 2 (by rfl) ⟨4390818, by rfl⟩ : syracuseStep 11708849 = 8781637) B8781637
theorem B2566595 : Blo 1711056 2566595 := bstep (se 1 (by rfl) ⟨1924946, by rfl⟩ : syracuseStep 2566595 = 3849893) B3849893
theorem B2566625 : Blo 1711056 2566625 := bstep (se 2 (by rfl) ⟨962484, by rfl⟩ : syracuseStep 2566625 = 1924969) B1924969
theorem B5777891 : Blo 1711056 5777891 := bstep (se 1 (by rfl) ⟨4333418, by rfl⟩ : syracuseStep 5777891 = 8666837) B8666837
theorem B2566643 : Blo 1711056 2566643 := bstep (se 1 (by rfl) ⟨1924982, by rfl⟩ : syracuseStep 2566643 = 3849965) B3849965
theorem B2566673 : Blo 1711056 2566673 := bstep (se 2 (by rfl) ⟨962502, by rfl⟩ : syracuseStep 2566673 = 1925005) B1925005
theorem B2566691 : Blo 1711056 2566691 := bstep (se 1 (by rfl) ⟨1925018, by rfl⟩ : syracuseStep 2566691 = 3850037) B3850037
theorem B4336163 : Blo 1711056 4336163 := bstep (se 1 (by rfl) ⟨3252122, by rfl⟩ : syracuseStep 4336163 = 6504245) B6504245
theorem B2566721 : Blo 1711056 2566721 := bstep (se 2 (by rfl) ⟨962520, by rfl⟩ : syracuseStep 2566721 = 1925041) B1925041
theorem B2566739 : Blo 1711056 2566739 := bstep (se 1 (by rfl) ⟨1925054, by rfl⟩ : syracuseStep 2566739 = 3850109) B3850109
theorem B3852881 : Blo 1711056 3852881 := bstep (se 2 (by rfl) ⟨1444830, by rfl⟩ : syracuseStep 3852881 = 2889661) B2889661
theorem B3852899 : Blo 1711056 3852899 := bstep (se 1 (by rfl) ⟨2889674, by rfl⟩ : syracuseStep 3852899 = 5779349) B5779349
theorem B2566769 : Blo 1711056 2566769 := bstep (se 2 (by rfl) ⟨962538, by rfl⟩ : syracuseStep 2566769 = 1925077) B1925077
theorem B8342129 : Blo 1711056 8342129 := bstep (se 2 (by rfl) ⟨3128298, by rfl⟩ : syracuseStep 8342129 = 6256597) B6256597
theorem B2566787 : Blo 1711056 2566787 := bstep (se 1 (by rfl) ⟨1925090, by rfl⟩ : syracuseStep 2566787 = 3850181) B3850181
theorem B2566817 : Blo 1711056 2566817 := bstep (se 2 (by rfl) ⟨962556, by rfl⟩ : syracuseStep 2566817 = 1925113) B1925113
theorem B2566835 : Blo 1711056 2566835 := bstep (se 1 (by rfl) ⟨1925126, by rfl⟩ : syracuseStep 2566835 = 3850253) B3850253
theorem B2566865 : Blo 1711056 2566865 := bstep (se 2 (by rfl) ⟨962574, by rfl⟩ : syracuseStep 2566865 = 1925149) B1925149
theorem B2566883 : Blo 1711056 2566883 := bstep (se 1 (by rfl) ⟨1925162, by rfl⟩ : syracuseStep 2566883 = 3850325) B3850325
theorem B2345699 : Blo 1711056 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B18516707 : Blo 1711056 18516707 := bstep (se 1 (by rfl) ⟨13887530, by rfl⟩ : syracuseStep 18516707 = 27775061) B27775061
theorem B5778161 : Blo 1711056 5778161 := bstep (se 2 (by rfl) ⟨2166810, by rfl⟩ : syracuseStep 5778161 = 4333621) B4333621
theorem B2566913 : Blo 1711056 2566913 := bstep (se 2 (by rfl) ⟨962592, by rfl⟩ : syracuseStep 2566913 = 1925185) B1925185
theorem B2566931 : Blo 1711056 2566931 := bstep (se 1 (by rfl) ⟨1925198, by rfl⟩ : syracuseStep 2566931 = 3850397) B3850397
theorem B5557027 : Blo 1711056 5557027 := bstep (se 1 (by rfl) ⟨4167770, by rfl⟩ : syracuseStep 5557027 = 8335541) B8335541
theorem B4877101 : Blo 1711056 4877101 := bstep (se 3 (by rfl) ⟨914456, by rfl⟩ : syracuseStep 4877101 = 1828913) B1828913
theorem B2566961 : Blo 1711056 2566961 := bstep (se 2 (by rfl) ⟨962610, by rfl⟩ : syracuseStep 2566961 = 1925221) B1925221
theorem B2566979 : Blo 1711056 2566979 := bstep (se 1 (by rfl) ⟨1925234, by rfl⟩ : syracuseStep 2566979 = 3850469) B3850469
theorem B2567009 : Blo 1711056 2567009 := bstep (se 2 (by rfl) ⟨962628, by rfl⟩ : syracuseStep 2567009 = 1925257) B1925257
theorem B3853169 : Blo 1711056 3853169 := bstep (se 2 (by rfl) ⟨1444938, by rfl⟩ : syracuseStep 3853169 = 2889877) B2889877
theorem B2567027 : Blo 1711056 2567027 := bstep (se 1 (by rfl) ⟨1925270, by rfl⟩ : syracuseStep 2567027 = 3850541) B3850541
theorem B3853187 : Blo 1711056 3853187 := bstep (se 1 (by rfl) ⟨2889890, by rfl⟩ : syracuseStep 3853187 = 5779781) B5779781
theorem B76114829 : Blo 1711056 76114829 := bstep (se 3 (by rfl) ⟨14271530, by rfl⟩ : syracuseStep 76114829 = 28543061) B28543061
theorem B2567057 : Blo 1711056 2567057 := bstep (se 2 (by rfl) ⟨962646, by rfl⟩ : syracuseStep 2567057 = 1925293) B1925293
theorem B2567075 : Blo 1711056 2567075 := bstep (se 1 (by rfl) ⟨1925306, by rfl⟩ : syracuseStep 2567075 = 3850613) B3850613
theorem B2567105 : Blo 1711056 2567105 := bstep (se 2 (by rfl) ⟨962664, by rfl⟩ : syracuseStep 2567105 = 1925329) B1925329
theorem B5483459 : Blo 1711056 5483459 := bstep (se 1 (by rfl) ⟨4112594, by rfl⟩ : syracuseStep 5483459 = 8225189) B8225189
theorem B3656657 : Blo 1711056 3656657 := bstep (se 2 (by rfl) ⟨1371246, by rfl⟩ : syracuseStep 3656657 = 2742493) B2742493
theorem B2567123 : Blo 1711056 2567123 := bstep (se 1 (by rfl) ⟨1925342, by rfl⟩ : syracuseStep 2567123 = 3850685) B3850685
theorem B7310321 : Blo 1711056 7310321 := bstep (se 2 (by rfl) ⟨2741370, by rfl⟩ : syracuseStep 7310321 = 5482741) B5482741
theorem B2567153 : Blo 1711056 2567153 := bstep (se 2 (by rfl) ⟨962682, by rfl⟩ : syracuseStep 2567153 = 1925365) B1925365
theorem B2567171 : Blo 1711056 2567171 := bstep (se 1 (by rfl) ⟨1925378, by rfl⟩ : syracuseStep 2567171 = 3850757) B3850757
theorem B4877329 : Blo 1711056 4877329 := bstep (se 2 (by rfl) ⟨1828998, by rfl⟩ : syracuseStep 4877329 = 3657997) B3657997
theorem B2567201 : Blo 1711056 2567201 := bstep (se 2 (by rfl) ⟨962700, by rfl⟩ : syracuseStep 2567201 = 1925401) B1925401
theorem B2567219 : Blo 1711056 2567219 := bstep (se 1 (by rfl) ⟨1925414, by rfl⟩ : syracuseStep 2567219 = 3850829) B3850829
theorem B2567249 : Blo 1711056 2567249 := bstep (se 2 (by rfl) ⟨962718, by rfl⟩ : syracuseStep 2567249 = 1925437) B1925437
theorem B2567267 : Blo 1711056 2567267 := bstep (se 1 (by rfl) ⟨1925450, by rfl⟩ : syracuseStep 2567267 = 3850901) B3850901
theorem B8227939 : Blo 1711056 8227939 := bstep (se 1 (by rfl) ⟨6170954, by rfl⟩ : syracuseStep 8227939 = 12341909) B12341909
theorem B2567297 : Blo 1711056 2567297 := bstep (se 2 (by rfl) ⟨962736, by rfl⟩ : syracuseStep 2567297 = 1925473) B1925473
theorem B3853457 : Blo 1711056 3853457 := bstep (se 2 (by rfl) ⟨1445046, by rfl⟩ : syracuseStep 3853457 = 2890093) B2890093
theorem B2567315 : Blo 1711056 2567315 := bstep (se 1 (by rfl) ⟨1925486, by rfl⟩ : syracuseStep 2567315 = 3850973) B3850973
theorem B3853475 : Blo 1711056 3853475 := bstep (se 1 (by rfl) ⟨2890106, by rfl⟩ : syracuseStep 3853475 = 5780213) B5780213
theorem B2567345 : Blo 1711056 2567345 := bstep (se 2 (by rfl) ⟨962754, by rfl⟩ : syracuseStep 2567345 = 1925509) B1925509
theorem B4877489 : Blo 1711056 4877489 := bstep (se 2 (by rfl) ⟨1829058, by rfl⟩ : syracuseStep 4877489 = 3658117) B3658117
theorem B2567363 : Blo 1711056 2567363 := bstep (se 1 (by rfl) ⟨1925522, by rfl⟩ : syracuseStep 2567363 = 3851045) B3851045
theorem B9260237 : Blo 1711056 9260237 := bstep (se 3 (by rfl) ⟨1736294, by rfl⟩ : syracuseStep 9260237 = 3472589) B3472589
theorem B2567393 : Blo 1711056 2567393 := bstep (se 2 (by rfl) ⟨962772, by rfl⟩ : syracuseStep 2567393 = 1925545) B1925545
theorem B2927843 : Blo 1711056 2927843 := bstep (se 1 (by rfl) ⟨2195882, by rfl⟩ : syracuseStep 2927843 = 4391765) B4391765
theorem B62483683 : Blo 1711056 62483683 := bstep (se 1 (by rfl) ⟨46862762, by rfl⟩ : syracuseStep 62483683 = 93725525) B93725525
theorem B2567411 : Blo 1711056 2567411 := bstep (se 1 (by rfl) ⟨1925558, by rfl⟩ : syracuseStep 2567411 = 3851117) B3851117
theorem B5778701 : Blo 1711056 5778701 := bstep (se 3 (by rfl) ⟨1083506, by rfl⟩ : syracuseStep 5778701 = 2167013) B2167013
theorem B2567441 : Blo 1711056 2567441 := bstep (se 2 (by rfl) ⟨962790, by rfl⟩ : syracuseStep 2567441 = 1925581) B1925581
theorem B2567459 : Blo 1711056 2567459 := bstep (se 1 (by rfl) ⟨1925594, by rfl⟩ : syracuseStep 2567459 = 3851189) B3851189
theorem B4877603 : Blo 1711056 4877603 := bstep (se 1 (by rfl) ⟨3658202, by rfl⟩ : syracuseStep 4877603 = 7316405) B7316405
theorem B4115747 : Blo 1711056 4115747 := bstep (se 1 (by rfl) ⟨3086810, by rfl⟩ : syracuseStep 4115747 = 6173621) B6173621
theorem B2567489 : Blo 1711056 2567489 := bstep (se 2 (by rfl) ⟨962808, by rfl⟩ : syracuseStep 2567489 = 1925617) B1925617
theorem B5778755 : Blo 1711056 5778755 := bstep (se 1 (by rfl) ⟨4334066, by rfl⟩ : syracuseStep 5778755 = 8668133) B8668133
theorem B5483857 : Blo 1711056 5483857 := bstep (se 2 (by rfl) ⟨2056446, by rfl⟩ : syracuseStep 5483857 = 4112893) B4112893
theorem B2567507 : Blo 1711056 2567507 := bstep (se 1 (by rfl) ⟨1925630, by rfl⟩ : syracuseStep 2567507 = 3851261) B3851261
theorem B8670563 : Blo 1711056 8670563 := bstep (se 1 (by rfl) ⟨6502922, by rfl⟩ : syracuseStep 8670563 = 13005845) B13005845
theorem B2567537 : Blo 1711056 2567537 := bstep (se 2 (by rfl) ⟨962826, by rfl⟩ : syracuseStep 2567537 = 1925653) B1925653
theorem B2567555 : Blo 1711056 2567555 := bstep (se 1 (by rfl) ⟨1925666, by rfl⟩ : syracuseStep 2567555 = 3851333) B3851333
theorem B2567585 : Blo 1711056 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B3853745 : Blo 1711056 3853745 := bstep (se 2 (by rfl) ⟨1445154, by rfl⟩ : syracuseStep 3853745 = 2890309) B2890309
theorem B2567603 : Blo 1711056 2567603 := bstep (se 1 (by rfl) ⟨1925702, by rfl⟩ : syracuseStep 2567603 = 3851405) B3851405
theorem B5483971 : Blo 1711056 5483971 := bstep (se 1 (by rfl) ⟨4112978, by rfl⟩ : syracuseStep 5483971 = 8225957) B8225957
theorem B3853763 : Blo 1711056 3853763 := bstep (se 1 (by rfl) ⟨2890322, by rfl⟩ : syracuseStep 3853763 = 5780645) B5780645
theorem B6172109 : Blo 1711056 6172109 := bstep (se 3 (by rfl) ⟨1157270, by rfl⟩ : syracuseStep 6172109 = 2314541) B2314541
theorem B2567633 : Blo 1711056 2567633 := bstep (se 2 (by rfl) ⟨962862, by rfl⟩ : syracuseStep 2567633 = 1925725) B1925725
theorem B2567651 : Blo 1711056 2567651 := bstep (se 1 (by rfl) ⟨1925738, by rfl⟩ : syracuseStep 2567651 = 3851477) B3851477
theorem B2166259 : Blo 1711056 2166259 := bstep (se 1 (by rfl) ⟨1624694, by rfl⟩ : syracuseStep 2166259 = 3249389) B3249389
theorem B2567681 : Blo 1711056 2567681 := bstep (se 2 (by rfl) ⟨962880, by rfl⟩ : syracuseStep 2567681 = 1925761) B1925761
theorem B2567699 : Blo 1711056 2567699 := bstep (se 1 (by rfl) ⟨1925774, by rfl⟩ : syracuseStep 2567699 = 3851549) B3851549
theorem B1953299 : Blo 1711056 1953299 := bstep (se 1 (by rfl) ⟨1464974, by rfl⟩ : syracuseStep 1953299 = 2929949) B2929949
theorem B3468835 : Blo 1711056 3468835 := bstep (se 1 (by rfl) ⟨2601626, by rfl⟩ : syracuseStep 3468835 = 5203253) B5203253
theorem B2567729 : Blo 1711056 2567729 := bstep (se 2 (by rfl) ⟨962898, by rfl⟩ : syracuseStep 2567729 = 1925797) B1925797
theorem B2567747 : Blo 1711056 2567747 := bstep (se 1 (by rfl) ⟨1925810, by rfl⟩ : syracuseStep 2567747 = 3851621) B3851621
theorem B5779025 : Blo 1711056 5779025 := bstep (se 2 (by rfl) ⟨2167134, by rfl⟩ : syracuseStep 5779025 = 4334269) B4334269
theorem B2166355 : Blo 1711056 2166355 := bstep (se 1 (by rfl) ⟨1624766, by rfl⟩ : syracuseStep 2166355 = 3249533) B3249533
theorem B2567777 : Blo 1711056 2567777 := bstep (se 2 (by rfl) ⟨962916, by rfl⟩ : syracuseStep 2567777 = 1925833) B1925833
theorem B13004387 : Blo 1711056 13004387 := bstep (se 1 (by rfl) ⟨9753290, by rfl⟩ : syracuseStep 13004387 = 19506581) B19506581
theorem B2567795 : Blo 1711056 2567795 := bstep (se 1 (by rfl) ⟨1925846, by rfl⟩ : syracuseStep 2567795 = 3851693) B3851693
theorem B9752197 : Blo 1711056 9752197 := bstep (se 4 (by rfl) ⟨914268, by rfl⟩ : syracuseStep 9752197 = 1828537) B1828537
theorem B3083921 : Blo 1711056 3083921 := bstep (se 2 (by rfl) ⟨1156470, by rfl⟩ : syracuseStep 3083921 = 2312941) B2312941
theorem B2567825 : Blo 1711056 2567825 := bstep (se 2 (by rfl) ⟨962934, by rfl⟩ : syracuseStep 2567825 = 1925869) B1925869
theorem B2567843 : Blo 1711056 2567843 := bstep (se 1 (by rfl) ⟨1925882, by rfl⟩ : syracuseStep 2567843 = 3851765) B3851765
theorem B2567873 : Blo 1711056 2567873 := bstep (se 2 (by rfl) ⟨962952, by rfl⟩ : syracuseStep 2567873 = 1925905) B1925905
theorem B3854033 : Blo 1711056 3854033 := bstep (se 2 (by rfl) ⟨1445262, by rfl⟩ : syracuseStep 3854033 = 2890525) B2890525
theorem B2567891 : Blo 1711056 2567891 := bstep (se 1 (by rfl) ⟨1925918, by rfl⟩ : syracuseStep 2567891 = 3851837) B3851837
theorem B3854051 : Blo 1711056 3854051 := bstep (se 1 (by rfl) ⟨2890538, by rfl⟩ : syracuseStep 3854051 = 5781077) B5781077
theorem B2567921 : Blo 1711056 2567921 := bstep (se 2 (by rfl) ⟨962970, by rfl⟩ : syracuseStep 2567921 = 1925941) B1925941
theorem B2887427 : Blo 1711056 2887427 := bstep (se 1 (by rfl) ⟨2165570, by rfl⟩ : syracuseStep 2887427 = 4331141) B4331141
theorem B2567939 : Blo 1711056 2567939 := bstep (se 1 (by rfl) ⟨1925954, by rfl⟩ : syracuseStep 2567939 = 3851909) B3851909
theorem B2567969 : Blo 1711056 2567969 := bstep (se 2 (by rfl) ⟨962988, by rfl⟩ : syracuseStep 2567969 = 1925977) B1925977
theorem B2567987 : Blo 1711056 2567987 := bstep (se 1 (by rfl) ⟨1925990, by rfl⟩ : syracuseStep 2567987 = 3851981) B3851981
theorem B2568017 : Blo 1711056 2568017 := bstep (se 2 (by rfl) ⟨963006, by rfl⟩ : syracuseStep 2568017 = 1926013) B1926013
theorem B2568035 : Blo 1711056 2568035 := bstep (se 1 (by rfl) ⟨1926026, by rfl⟩ : syracuseStep 2568035 = 3852053) B3852053
theorem B2436979 : Blo 1711056 2436979 := bstep (se 1 (by rfl) ⟨1827734, by rfl⟩ : syracuseStep 2436979 = 3655469) B3655469
theorem B2568065 : Blo 1711056 2568065 := bstep (se 2 (by rfl) ⟨963024, by rfl⟩ : syracuseStep 2568065 = 1926049) B1926049
theorem B2887555 : Blo 1711056 2887555 := bstep (se 1 (by rfl) ⟨2165666, by rfl⟩ : syracuseStep 2887555 = 4331333) B4331333
theorem B10973069 : Blo 1711056 10973069 := bstep (se 3 (by rfl) ⟨2057450, by rfl⟩ : syracuseStep 10973069 = 4114901) B4114901
theorem B2568083 : Blo 1711056 2568083 := bstep (se 1 (by rfl) ⟨1926062, by rfl⟩ : syracuseStep 2568083 = 3852125) B3852125
theorem B2568113 : Blo 1711056 2568113 := bstep (se 2 (by rfl) ⟨963042, by rfl⟩ : syracuseStep 2568113 = 1926085) B1926085
theorem B2568131 : Blo 1711056 2568131 := bstep (se 1 (by rfl) ⟨1926098, by rfl⟩ : syracuseStep 2568131 = 3852197) B3852197
theorem B2568161 : Blo 1711056 2568161 := bstep (se 2 (by rfl) ⟨963060, by rfl⟩ : syracuseStep 2568161 = 1926121) B1926121
theorem B3854321 : Blo 1711056 3854321 := bstep (se 2 (by rfl) ⟨1445370, by rfl⟩ : syracuseStep 3854321 = 2890741) B2890741
theorem B2568179 : Blo 1711056 2568179 := bstep (se 1 (by rfl) ⟨1926134, by rfl⟩ : syracuseStep 2568179 = 3852269) B3852269
theorem B3854339 : Blo 1711056 3854339 := bstep (se 1 (by rfl) ⟨2890754, by rfl⟩ : syracuseStep 3854339 = 5781509) B5781509
theorem B2887697 : Blo 1711056 2887697 := bstep (se 2 (by rfl) ⟨1082886, by rfl⟩ : syracuseStep 2887697 = 2165773) B2165773
theorem B2568209 : Blo 1711056 2568209 := bstep (se 2 (by rfl) ⟨963078, by rfl⟩ : syracuseStep 2568209 = 1926157) B1926157
theorem B2568227 : Blo 1711056 2568227 := bstep (se 1 (by rfl) ⟨1926170, by rfl⟩ : syracuseStep 2568227 = 3852341) B3852341
theorem B7409713 : Blo 1711056 7409713 := bstep (se 2 (by rfl) ⟨2778642, by rfl⟩ : syracuseStep 7409713 = 5557285) B5557285
theorem B2568257 : Blo 1711056 2568257 := bstep (se 2 (by rfl) ⟨963096, by rfl⟩ : syracuseStep 2568257 = 1926193) B1926193
theorem B2166851 : Blo 1711056 2166851 := bstep (se 1 (by rfl) ⟨1625138, by rfl⟩ : syracuseStep 2166851 = 3250277) B3250277
theorem B2568275 : Blo 1711056 2568275 := bstep (se 1 (by rfl) ⟨1926206, by rfl⟩ : syracuseStep 2568275 = 3852413) B3852413
theorem B5779565 : Blo 1711056 5779565 := bstep (se 3 (by rfl) ⟨1083668, by rfl⟩ : syracuseStep 5779565 = 2167337) B2167337
theorem B2568305 : Blo 1711056 2568305 := bstep (se 2 (by rfl) ⟨963114, by rfl⟩ : syracuseStep 2568305 = 1926229) B1926229
theorem B2568323 : Blo 1711056 2568323 := bstep (se 1 (by rfl) ⟨1926242, by rfl⟩ : syracuseStep 2568323 = 3852485) B3852485
theorem B8671373 : Blo 1711056 8671373 := bstep (se 3 (by rfl) ⟨1625882, by rfl⟩ : syracuseStep 8671373 = 3251765) B3251765
theorem B2887825 : Blo 1711056 2887825 := bstep (se 2 (by rfl) ⟨1082934, by rfl⟩ : syracuseStep 2887825 = 2165869) B2165869
theorem B5484689 : Blo 1711056 5484689 := bstep (se 2 (by rfl) ⟨2056758, by rfl⟩ : syracuseStep 5484689 = 4113517) B4113517
theorem B2568353 : Blo 1711056 2568353 := bstep (se 2 (by rfl) ⟨963132, by rfl⟩ : syracuseStep 2568353 = 1926265) B1926265
theorem B8335523 : Blo 1711056 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B5779619 : Blo 1711056 5779619 := bstep (se 1 (by rfl) ⟨4334714, by rfl⟩ : syracuseStep 5779619 = 8669429) B8669429
theorem B2887859 : Blo 1711056 2887859 := bstep (se 1 (by rfl) ⟨2165894, by rfl⟩ : syracuseStep 2887859 = 4331789) B4331789
theorem B2568371 : Blo 1711056 2568371 := bstep (se 1 (by rfl) ⟨1926278, by rfl⟩ : syracuseStep 2568371 = 3852557) B3852557
theorem B2568401 : Blo 1711056 2568401 := bstep (se 2 (by rfl) ⟨963150, by rfl⟩ : syracuseStep 2568401 = 1926301) B1926301
theorem B2568419 : Blo 1711056 2568419 := bstep (se 1 (by rfl) ⟨1926314, by rfl⟩ : syracuseStep 2568419 = 3852629) B3852629
theorem B3657955 : Blo 1711056 3657955 := bstep (se 1 (by rfl) ⟨2743466, by rfl⟩ : syracuseStep 3657955 = 5486933) B5486933
theorem B2568449 : Blo 1711056 2568449 := bstep (se 2 (by rfl) ⟨963168, by rfl⟩ : syracuseStep 2568449 = 1926337) B1926337
theorem B10965253 : Blo 1711056 10965253 := bstep (se 4 (by rfl) ⟨1027992, by rfl⟩ : syracuseStep 10965253 = 2055985) B2055985
theorem B2568467 : Blo 1711056 2568467 := bstep (se 1 (by rfl) ⟨1926350, by rfl⟩ : syracuseStep 2568467 = 3852701) B3852701
theorem B2568497 : Blo 1711056 2568497 := bstep (se 2 (by rfl) ⟨963186, by rfl⟩ : syracuseStep 2568497 = 1926373) B1926373
theorem B2887987 : Blo 1711056 2887987 := bstep (se 1 (by rfl) ⟨2165990, by rfl⟩ : syracuseStep 2887987 = 4331981) B4331981
theorem B2568515 : Blo 1711056 2568515 := bstep (se 1 (by rfl) ⟨1926386, by rfl⟩ : syracuseStep 2568515 = 3852773) B3852773
theorem B2437457 : Blo 1711056 2437457 := bstep (se 2 (by rfl) ⟨914046, by rfl⟩ : syracuseStep 2437457 = 1828093) B1828093
theorem B2568545 : Blo 1711056 2568545 := bstep (se 2 (by rfl) ⟨963204, by rfl⟩ : syracuseStep 2568545 = 1926409) B1926409
theorem B2568563 : Blo 1711056 2568563 := bstep (se 1 (by rfl) ⟨1926422, by rfl⟩ : syracuseStep 2568563 = 3852845) B3852845
theorem B3248515 : Blo 1711056 3248515 := bstep (se 1 (by rfl) ⟨2436386, by rfl⟩ : syracuseStep 3248515 = 4872773) B4872773
theorem B18510221 : Blo 1711056 18510221 := bstep (se 3 (by rfl) ⟨3470666, by rfl⟩ : syracuseStep 18510221 = 6941333) B6941333
theorem B2568593 : Blo 1711056 2568593 := bstep (se 2 (by rfl) ⟨963222, by rfl⟩ : syracuseStep 2568593 = 1926445) B1926445
theorem B2568611 : Blo 1711056 2568611 := bstep (se 1 (by rfl) ⟨1926458, by rfl⟩ : syracuseStep 2568611 = 3852917) B3852917
theorem B3248561 : Blo 1711056 3248561 := bstep (se 2 (by rfl) ⟨1218210, by rfl⟩ : syracuseStep 3248561 = 2436421) B2436421
theorem B5779889 : Blo 1711056 5779889 := bstep (se 2 (by rfl) ⟨2167458, by rfl⟩ : syracuseStep 5779889 = 4334917) B4334917
theorem B2888129 : Blo 1711056 2888129 := bstep (se 2 (by rfl) ⟨1083048, by rfl⟩ : syracuseStep 2888129 = 2166097) B2166097
theorem B2437571 : Blo 1711056 2437571 := bstep (se 1 (by rfl) ⟨1828178, by rfl⟩ : syracuseStep 2437571 = 3656357) B3656357
theorem B2568641 : Blo 1711056 2568641 := bstep (se 2 (by rfl) ⟨963240, by rfl⟩ : syracuseStep 2568641 = 1926481) B1926481
theorem B2568659 : Blo 1711056 2568659 := bstep (se 1 (by rfl) ⟨1926494, by rfl⟩ : syracuseStep 2568659 = 3852989) B3852989
theorem B2568689 : Blo 1711056 2568689 := bstep (se 2 (by rfl) ⟨963258, by rfl⟩ : syracuseStep 2568689 = 1926517) B1926517
theorem B2568707 : Blo 1711056 2568707 := bstep (se 1 (by rfl) ⟨1926530, by rfl⟩ : syracuseStep 2568707 = 3853061) B3853061
theorem B2437651 : Blo 1711056 2437651 := bstep (se 1 (by rfl) ⟨1828238, by rfl⟩ : syracuseStep 2437651 = 3656477) B3656477
theorem B2568737 : Blo 1711056 2568737 := bstep (se 2 (by rfl) ⟨963276, by rfl⟩ : syracuseStep 2568737 = 1926553) B1926553
theorem B3469873 : Blo 1711056 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B2568755 : Blo 1711056 2568755 := bstep (se 1 (by rfl) ⟨1926566, by rfl⟩ : syracuseStep 2568755 = 3853133) B3853133
theorem B2888257 : Blo 1711056 2888257 := bstep (se 2 (by rfl) ⟨1083096, by rfl⟩ : syracuseStep 2888257 = 2166193) B2166193
theorem B5206609 : Blo 1711056 5206609 := bstep (se 2 (by rfl) ⟨1952478, by rfl⟩ : syracuseStep 5206609 = 3904957) B3904957
theorem B2568785 : Blo 1711056 2568785 := bstep (se 2 (by rfl) ⟨963294, by rfl⟩ : syracuseStep 2568785 = 1926589) B1926589
theorem B2888291 : Blo 1711056 2888291 := bstep (se 1 (by rfl) ⟨2166218, by rfl⟩ : syracuseStep 2888291 = 4332437) B4332437
theorem B2568803 : Blo 1711056 2568803 := bstep (se 1 (by rfl) ⟨1926602, by rfl⟩ : syracuseStep 2568803 = 3853205) B3853205
theorem B2568833 : Blo 1711056 2568833 := bstep (se 2 (by rfl) ⟨963312, by rfl⟩ : syracuseStep 2568833 = 1926625) B1926625
theorem B2568851 : Blo 1711056 2568851 := bstep (se 1 (by rfl) ⟨1926638, by rfl⟩ : syracuseStep 2568851 = 3853277) B3853277
theorem B5485229 : Blo 1711056 5485229 := bstep (se 3 (by rfl) ⟨1028480, by rfl⟩ : syracuseStep 5485229 = 2056961) B2056961
theorem B2568881 : Blo 1711056 2568881 := bstep (se 2 (by rfl) ⟨963330, by rfl⟩ : syracuseStep 2568881 = 1926661) B1926661
theorem B2568899 : Blo 1711056 2568899 := bstep (se 1 (by rfl) ⟨1926674, by rfl⟩ : syracuseStep 2568899 = 3853349) B3853349
theorem B16446149 : Blo 1711056 16446149 := bstep (se 4 (by rfl) ⟨1541826, by rfl⟩ : syracuseStep 16446149 = 3083653) B3083653
theorem B3248849 : Blo 1711056 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B2740961 : Blo 1711056 2740961 := bstep (se 2 (by rfl) ⟨1027860, by rfl⟩ : syracuseStep 2740961 = 2055721) B2055721
theorem B2568929 : Blo 1711056 2568929 := bstep (se 2 (by rfl) ⟨963348, by rfl⟩ : syracuseStep 2568929 = 1926697) B1926697
theorem B2888419 : Blo 1711056 2888419 := bstep (se 1 (by rfl) ⟨2166314, by rfl⟩ : syracuseStep 2888419 = 4332629) B4332629
theorem B2568947 : Blo 1711056 2568947 := bstep (se 1 (by rfl) ⟨1926710, by rfl⟩ : syracuseStep 2568947 = 3853421) B3853421
theorem B2167555 : Blo 1711056 2167555 := bstep (se 1 (by rfl) ⟨1625666, by rfl⟩ : syracuseStep 2167555 = 3251333) B3251333
theorem B2568977 : Blo 1711056 2568977 := bstep (se 2 (by rfl) ⟨963366, by rfl⟩ : syracuseStep 2568977 = 1926733) B1926733
theorem B2568995 : Blo 1711056 2568995 := bstep (se 1 (by rfl) ⟨1926746, by rfl⟩ : syracuseStep 2568995 = 3853493) B3853493
theorem B2569025 : Blo 1711056 2569025 := bstep (se 2 (by rfl) ⟨963384, by rfl⟩ : syracuseStep 2569025 = 1926769) B1926769
theorem B2569043 : Blo 1711056 2569043 := bstep (se 1 (by rfl) ⟨1926782, by rfl⟩ : syracuseStep 2569043 = 3853565) B3853565
theorem B2167651 : Blo 1711056 2167651 := bstep (se 1 (by rfl) ⟨1625738, by rfl⟩ : syracuseStep 2167651 = 3251477) B3251477
theorem B8663921 : Blo 1711056 8663921 := bstep (se 2 (by rfl) ⟨3248970, by rfl⟩ : syracuseStep 8663921 = 6497941) B6497941
theorem B2888561 : Blo 1711056 2888561 := bstep (se 2 (by rfl) ⟨1083210, by rfl⟩ : syracuseStep 2888561 = 2166421) B2166421
theorem B2569073 : Blo 1711056 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B2569091 : Blo 1711056 2569091 := bstep (se 1 (by rfl) ⟨1926818, by rfl⟩ : syracuseStep 2569091 = 3853637) B3853637
theorem B2569121 : Blo 1711056 2569121 := bstep (se 2 (by rfl) ⟨963420, by rfl⟩ : syracuseStep 2569121 = 1926841) B1926841
theorem B2569139 : Blo 1711056 2569139 := bstep (se 1 (by rfl) ⟨1926854, by rfl⟩ : syracuseStep 2569139 = 3853709) B3853709
theorem B5780429 : Blo 1711056 5780429 := bstep (se 3 (by rfl) ⟨1083830, by rfl⟩ : syracuseStep 5780429 = 2167661) B2167661
theorem B2569169 : Blo 1711056 2569169 := bstep (se 2 (by rfl) ⟨963438, by rfl⟩ : syracuseStep 2569169 = 1926877) B1926877
theorem B3085283 : Blo 1711056 3085283 := bstep (se 1 (by rfl) ⟨2313962, by rfl⟩ : syracuseStep 3085283 = 4627925) B4627925
theorem B2569187 : Blo 1711056 2569187 := bstep (se 1 (by rfl) ⟨1926890, by rfl⟩ : syracuseStep 2569187 = 3853781) B3853781
theorem B2888689 : Blo 1711056 2888689 := bstep (se 2 (by rfl) ⟨1083258, by rfl⟩ : syracuseStep 2888689 = 2166517) B2166517
theorem B2569217 : Blo 1711056 2569217 := bstep (se 2 (by rfl) ⟨963456, by rfl⟩ : syracuseStep 2569217 = 1926913) B1926913
theorem B5780483 : Blo 1711056 5780483 := bstep (se 1 (by rfl) ⟨4335362, by rfl⟩ : syracuseStep 5780483 = 8670725) B8670725
theorem B11719685 : Blo 1711056 11719685 := bstep (se 4 (by rfl) ⟨1098720, by rfl⟩ : syracuseStep 11719685 = 2197441) B2197441
theorem B2888723 : Blo 1711056 2888723 := bstep (se 1 (by rfl) ⟨2166542, by rfl⟩ : syracuseStep 2888723 = 4333085) B4333085
theorem B2569235 : Blo 1711056 2569235 := bstep (se 1 (by rfl) ⟨1926926, by rfl⟩ : syracuseStep 2569235 = 3853853) B3853853
theorem B3707939 : Blo 1711056 3707939 := bstep (se 1 (by rfl) ⟨2780954, by rfl⟩ : syracuseStep 3707939 = 5561909) B5561909
theorem B2569265 : Blo 1711056 2569265 := bstep (se 2 (by rfl) ⟨963474, by rfl⟩ : syracuseStep 2569265 = 1926949) B1926949
theorem B2438209 : Blo 1711056 2438209 := bstep (se 2 (by rfl) ⟨914328, by rfl⟩ : syracuseStep 2438209 = 1828657) B1828657
theorem B2569283 : Blo 1711056 2569283 := bstep (se 1 (by rfl) ⟨1926962, by rfl⟩ : syracuseStep 2569283 = 3853925) B3853925
theorem B2569313 : Blo 1711056 2569313 := bstep (se 2 (by rfl) ⟨963492, by rfl⟩ : syracuseStep 2569313 = 1926985) B1926985
theorem B2569331 : Blo 1711056 2569331 := bstep (se 1 (by rfl) ⟨1926998, by rfl⟩ : syracuseStep 2569331 = 3853997) B3853997
theorem B9254029 : Blo 1711056 9254029 := bstep (se 3 (by rfl) ⟨1735130, by rfl⟩ : syracuseStep 9254029 = 3470261) B3470261
theorem B2569361 : Blo 1711056 2569361 := bstep (se 2 (by rfl) ⟨963510, by rfl⟩ : syracuseStep 2569361 = 1927021) B1927021
theorem B2888851 : Blo 1711056 2888851 := bstep (se 1 (by rfl) ⟨2166638, by rfl⟩ : syracuseStep 2888851 = 4333277) B4333277
theorem B2569379 : Blo 1711056 2569379 := bstep (se 1 (by rfl) ⟨1927034, by rfl⟩ : syracuseStep 2569379 = 3854069) B3854069
theorem B2569409 : Blo 1711056 2569409 := bstep (se 2 (by rfl) ⟨963528, by rfl⟩ : syracuseStep 2569409 = 1927057) B1927057
theorem B2569427 : Blo 1711056 2569427 := bstep (se 1 (by rfl) ⟨1927070, by rfl⟩ : syracuseStep 2569427 = 3854141) B3854141
theorem B2741473 : Blo 1711056 2741473 := bstep (se 2 (by rfl) ⟨1028052, by rfl⟩ : syracuseStep 2741473 = 2056105) B2056105
theorem B6501617 : Blo 1711056 6501617 := bstep (se 2 (by rfl) ⟨2438106, by rfl⟩ : syracuseStep 6501617 = 4876213) B4876213
theorem B2569457 : Blo 1711056 2569457 := bstep (se 2 (by rfl) ⟨963546, by rfl⟩ : syracuseStep 2569457 = 1927093) B1927093
theorem B2569475 : Blo 1711056 2569475 := bstep (se 1 (by rfl) ⟨1927106, by rfl⟩ : syracuseStep 2569475 = 3854213) B3854213
theorem B5780753 : Blo 1711056 5780753 := bstep (se 2 (by rfl) ⟨2167782, by rfl⟩ : syracuseStep 5780753 = 4335565) B4335565
theorem B2888993 : Blo 1711056 2888993 := bstep (se 2 (by rfl) ⟨1083372, by rfl⟩ : syracuseStep 2888993 = 2166745) B2166745
theorem B2569505 : Blo 1711056 2569505 := bstep (se 2 (by rfl) ⟨963564, by rfl⟩ : syracuseStep 2569505 = 1927129) B1927129
theorem B2569523 : Blo 1711056 2569523 := bstep (se 1 (by rfl) ⟨1927142, by rfl⟩ : syracuseStep 2569523 = 3854285) B3854285
theorem B2602307 : Blo 1711056 2602307 := bstep (se 1 (by rfl) ⟨1951730, by rfl⟩ : syracuseStep 2602307 = 3903461) B3903461
theorem B2569553 : Blo 1711056 2569553 := bstep (se 2 (by rfl) ⟨963582, by rfl⟩ : syracuseStep 2569553 = 1927165) B1927165
theorem B2471267 : Blo 1711056 2471267 := bstep (se 1 (by rfl) ⟨1853450, by rfl⟩ : syracuseStep 2471267 = 3706901) B3706901
theorem B2569571 : Blo 1711056 2569571 := bstep (se 1 (by rfl) ⟨1927178, by rfl⟩ : syracuseStep 2569571 = 3854357) B3854357
theorem B11113841 : Blo 1711056 11113841 := bstep (se 2 (by rfl) ⟨4167690, by rfl⟩ : syracuseStep 11113841 = 8335381) B8335381
theorem B2602355 : Blo 1711056 2602355 := bstep (se 1 (by rfl) ⟨1951766, by rfl⟩ : syracuseStep 2602355 = 3903533) B3903533
theorem B7312781 : Blo 1711056 7312781 := bstep (se 3 (by rfl) ⟨1371146, by rfl⟩ : syracuseStep 7312781 = 2742293) B2742293
theorem B2889121 : Blo 1711056 2889121 := bstep (se 2 (by rfl) ⟨1083420, by rfl⟩ : syracuseStep 2889121 = 2166841) B2166841
theorem B3249571 : Blo 1711056 3249571 := bstep (se 1 (by rfl) ⟨2437178, by rfl⟩ : syracuseStep 3249571 = 4874357) B4874357
theorem B2889155 : Blo 1711056 2889155 := bstep (se 1 (by rfl) ⟨2166866, by rfl⟩ : syracuseStep 2889155 = 4333733) B4333733
theorem B9377221 : Blo 1711056 9377221 := bstep (se 4 (by rfl) ⟨879114, by rfl⟩ : syracuseStep 9377221 = 1758229) B1758229
theorem B2889283 : Blo 1711056 2889283 := bstep (se 1 (by rfl) ⟨2166962, by rfl⟩ : syracuseStep 2889283 = 4333925) B4333925
theorem B9754181 : Blo 1711056 9754181 := bstep (se 4 (by rfl) ⟨914454, by rfl⟩ : syracuseStep 9754181 = 1828909) B1828909
theorem B4331171 : Blo 1711056 4331171 := bstep (se 1 (by rfl) ⟨3248378, by rfl⟩ : syracuseStep 4331171 = 6496757) B6496757
theorem B2889425 : Blo 1711056 2889425 := bstep (se 2 (by rfl) ⟨1083534, by rfl⟩ : syracuseStep 2889425 = 2167069) B2167069
theorem B2504417 : Blo 1711056 2504417 := bstep (se 2 (by rfl) ⟨939156, by rfl⟩ : syracuseStep 2504417 = 1878313) B1878313
theorem B2438915 : Blo 1711056 2438915 := bstep (se 1 (by rfl) ⟨1829186, by rfl⟩ : syracuseStep 2438915 = 3658373) B3658373
theorem B5781293 : Blo 1711056 5781293 := bstep (se 3 (by rfl) ⟨1083992, by rfl⟩ : syracuseStep 5781293 = 2167985) B2167985
theorem B2742083 : Blo 1711056 2742083 := bstep (se 1 (by rfl) ⟨2056562, by rfl⟩ : syracuseStep 2742083 = 4113125) B4113125
theorem B2889553 : Blo 1711056 2889553 := bstep (se 2 (by rfl) ⟨1083582, by rfl⟩ : syracuseStep 2889553 = 2167165) B2167165
theorem B3250019 : Blo 1711056 3250019 := bstep (se 1 (by rfl) ⟨2437514, by rfl⟩ : syracuseStep 3250019 = 4875029) B4875029
theorem B14628707 : Blo 1711056 14628707 := bstep (se 1 (by rfl) ⟨10971530, by rfl⟩ : syracuseStep 14628707 = 21943061) B21943061
theorem B5781347 : Blo 1711056 5781347 := bstep (se 1 (by rfl) ⟨4336010, by rfl⟩ : syracuseStep 5781347 = 8672021) B8672021
theorem B2889587 : Blo 1711056 2889587 := bstep (se 1 (by rfl) ⟨2167190, by rfl⟩ : syracuseStep 2889587 = 4334381) B4334381
theorem B5207971 : Blo 1711056 5207971 := bstep (se 1 (by rfl) ⟨3905978, by rfl⟩ : syracuseStep 5207971 = 7811957) B7811957
theorem B12335075 : Blo 1711056 12335075 := bstep (se 1 (by rfl) ⟨9251306, by rfl⟩ : syracuseStep 12335075 = 18502613) B18502613
theorem B9254897 : Blo 1711056 9254897 := bstep (se 2 (by rfl) ⟨3470586, by rfl⟩ : syracuseStep 9254897 = 6941173) B6941173
theorem B2889715 : Blo 1711056 2889715 := bstep (se 1 (by rfl) ⟨2167286, by rfl⟩ : syracuseStep 2889715 = 4334573) B4334573
theorem B2889857 : Blo 1711056 2889857 := bstep (se 2 (by rfl) ⟨1083696, by rfl⟩ : syracuseStep 2889857 = 2167393) B2167393
theorem B3250307 : Blo 1711056 3250307 := bstep (se 1 (by rfl) ⟨2437730, by rfl⟩ : syracuseStep 3250307 = 4875461) B4875461
theorem B13179077 : Blo 1711056 13179077 := bstep (se 4 (by rfl) ⟨1235538, by rfl⟩ : syracuseStep 13179077 = 2471077) B2471077
theorem B4626659 : Blo 1711056 4626659 := bstep (se 1 (by rfl) ⟨3469994, by rfl⟩ : syracuseStep 4626659 = 6939989) B6939989
theorem B2889985 : Blo 1711056 2889985 := bstep (se 2 (by rfl) ⟨1083744, by rfl⟩ : syracuseStep 2889985 = 2167489) B2167489
theorem B8665379 : Blo 1711056 8665379 := bstep (se 1 (by rfl) ⟨6499034, by rfl⟩ : syracuseStep 8665379 = 12998069) B12998069
theorem B2890019 : Blo 1711056 2890019 := bstep (se 1 (by rfl) ⟨2167514, by rfl⟩ : syracuseStep 2890019 = 4335029) B4335029
theorem B2890147 : Blo 1711056 2890147 := bstep (se 1 (by rfl) ⟨2167610, by rfl⟩ : syracuseStep 2890147 = 4335221) B4335221
theorem B5487149 : Blo 1711056 5487149 := bstep (se 3 (by rfl) ⟨1028840, by rfl⟩ : syracuseStep 5487149 = 2057681) B2057681
theorem B2890289 : Blo 1711056 2890289 := bstep (se 2 (by rfl) ⟨1083858, by rfl⟩ : syracuseStep 2890289 = 2167717) B2167717
theorem B4332113 : Blo 1711056 4332113 := bstep (se 2 (by rfl) ⟨1624542, by rfl⟩ : syracuseStep 4332113 = 3249085) B3249085
theorem B4332163 : Blo 1711056 4332163 := bstep (se 1 (by rfl) ⟨3249122, by rfl⟩ : syracuseStep 4332163 = 6498245) B6498245
theorem B6503075 : Blo 1711056 6503075 := bstep (se 1 (by rfl) ⟨4877306, by rfl⟩ : syracuseStep 6503075 = 9754613) B9754613
theorem B2890417 : Blo 1711056 2890417 := bstep (se 2 (by rfl) ⟨1083906, by rfl⟩ : syracuseStep 2890417 = 2167813) B2167813
theorem B4872899 : Blo 1711056 4872899 := bstep (se 1 (by rfl) ⟨3654674, by rfl⟩ : syracuseStep 4872899 = 7309349) B7309349
theorem B6945485 : Blo 1711056 6945485 := bstep (se 3 (by rfl) ⟨1302278, by rfl⟩ : syracuseStep 6945485 = 2604557) B2604557
theorem B2603731 : Blo 1711056 2603731 := bstep (se 1 (by rfl) ⟨1952798, by rfl⟩ : syracuseStep 2603731 = 3905597) B3905597
theorem B2890451 : Blo 1711056 2890451 := bstep (se 1 (by rfl) ⟨2167838, by rfl⟩ : syracuseStep 2890451 = 4335677) B4335677
theorem B4332305 : Blo 1711056 4332305 := bstep (se 2 (by rfl) ⟨1624614, by rfl⟩ : syracuseStep 4332305 = 3249229) B3249229
theorem B2743075 : Blo 1711056 2743075 := bstep (se 1 (by rfl) ⟨2057306, by rfl⟩ : syracuseStep 2743075 = 4114613) B4114613
theorem B2890579 : Blo 1711056 2890579 := bstep (se 1 (by rfl) ⟨2167934, by rfl⟩ : syracuseStep 2890579 = 4335869) B4335869
theorem B4111249 : Blo 1711056 4111249 := bstep (se 2 (by rfl) ⟨1541718, by rfl⟩ : syracuseStep 4111249 = 3083437) B3083437
theorem B1711059 : Blo 1711056 1711059 := bstep (se 1 (by rfl) ⟨1283294, by rfl⟩ : syracuseStep 1711059 = 2566589) B2566589
theorem B2890721 : Blo 1711056 2890721 := bstep (se 2 (by rfl) ⟨1084020, by rfl⟩ : syracuseStep 2890721 = 2168041) B2168041
theorem B1711075 : Blo 1711056 1711075 := bstep (se 1 (by rfl) ⟨1283306, by rfl⟩ : syracuseStep 1711075 = 2566613) B2566613
theorem B1711091 : Blo 1711056 1711091 := bstep (se 1 (by rfl) ⟨1283318, by rfl⟩ : syracuseStep 1711091 = 2566637) B2566637
theorem B1711107 : Blo 1711056 1711107 := bstep (se 1 (by rfl) ⟨1283330, by rfl⟩ : syracuseStep 1711107 = 2566661) B2566661
theorem B4873229 : Blo 1711056 4873229 := bstep (se 3 (by rfl) ⟨913730, by rfl⟩ : syracuseStep 4873229 = 1827461) B1827461
theorem B1711123 : Blo 1711056 1711123 := bstep (se 1 (by rfl) ⟨1283342, by rfl⟩ : syracuseStep 1711123 = 2566685) B2566685
theorem B1711139 : Blo 1711056 1711139 := bstep (se 1 (by rfl) ⟨1283354, by rfl⟩ : syracuseStep 1711139 = 2566709) B2566709
theorem B1735715 : Blo 1711056 1735715 := bstep (se 1 (by rfl) ⟨1301786, by rfl⟩ : syracuseStep 1735715 = 2603573) B2603573
theorem B3251249 : Blo 1711056 3251249 := bstep (se 2 (by rfl) ⟨1219218, by rfl⟩ : syracuseStep 3251249 = 2438437) B2438437
theorem B1711155 : Blo 1711056 1711155 := bstep (se 1 (by rfl) ⟨1283366, by rfl⟩ : syracuseStep 1711155 = 2566733) B2566733
theorem B2604083 : Blo 1711056 2604083 := bstep (se 1 (by rfl) ⟨1953062, by rfl⟩ : syracuseStep 2604083 = 3906125) B3906125
theorem B1711171 : Blo 1711056 1711171 := bstep (se 1 (by rfl) ⟨1283378, by rfl⟩ : syracuseStep 1711171 = 2566757) B2566757
theorem B8666189 : Blo 1711056 8666189 := bstep (se 3 (by rfl) ⟨1624910, by rfl⟩ : syracuseStep 8666189 = 3249821) B3249821
theorem B4873297 : Blo 1711056 4873297 := bstep (se 2 (by rfl) ⟨1827486, by rfl⟩ : syracuseStep 4873297 = 3654973) B3654973
theorem B1711187 : Blo 1711056 1711187 := bstep (se 1 (by rfl) ⟨1283390, by rfl⟩ : syracuseStep 1711187 = 2566781) B2566781
theorem B1711203 : Blo 1711056 1711203 := bstep (se 1 (by rfl) ⟨1283402, by rfl⟩ : syracuseStep 1711203 = 2566805) B2566805
theorem B1711219 : Blo 1711056 1711219 := bstep (se 1 (by rfl) ⟨1283414, by rfl⟩ : syracuseStep 1711219 = 2566829) B2566829
theorem B1711235 : Blo 1711056 1711235 := bstep (se 1 (by rfl) ⟨1283426, by rfl⟩ : syracuseStep 1711235 = 2566853) B2566853
theorem B1711251 : Blo 1711056 1711251 := bstep (se 1 (by rfl) ⟨1283438, by rfl⟩ : syracuseStep 1711251 = 2566877) B2566877
theorem B1711267 : Blo 1711056 1711267 := bstep (se 1 (by rfl) ⟨1283450, by rfl⟩ : syracuseStep 1711267 = 2566901) B2566901
theorem B1711283 : Blo 1711056 1711283 := bstep (se 1 (by rfl) ⟨1283462, by rfl⟩ : syracuseStep 1711283 = 2566925) B2566925
theorem B1711299 : Blo 1711056 1711299 := bstep (se 1 (by rfl) ⟨1283474, by rfl⟩ : syracuseStep 1711299 = 2566949) B2566949
theorem B1711315 : Blo 1711056 1711315 := bstep (se 1 (by rfl) ⟨1283486, by rfl⟩ : syracuseStep 1711315 = 2566973) B2566973
theorem B1711331 : Blo 1711056 1711331 := bstep (se 1 (by rfl) ⟨1283498, by rfl⟩ : syracuseStep 1711331 = 2566997) B2566997
theorem B1711347 : Blo 1711056 1711347 := bstep (se 1 (by rfl) ⟨1283510, by rfl⟩ : syracuseStep 1711347 = 2567021) B2567021
theorem B1711363 : Blo 1711056 1711363 := bstep (se 1 (by rfl) ⟨1283522, by rfl⟩ : syracuseStep 1711363 = 2567045) B2567045
theorem B1711379 : Blo 1711056 1711379 := bstep (se 1 (by rfl) ⟨1283534, by rfl⟩ : syracuseStep 1711379 = 2567069) B2567069
theorem B1711395 : Blo 1711056 1711395 := bstep (se 1 (by rfl) ⟨1283546, by rfl⟩ : syracuseStep 1711395 = 2567093) B2567093
theorem B1711411 : Blo 1711056 1711411 := bstep (se 1 (by rfl) ⟨1283558, by rfl⟩ : syracuseStep 1711411 = 2567117) B2567117
theorem B1711427 : Blo 1711056 1711427 := bstep (se 1 (by rfl) ⟨1283570, by rfl⟩ : syracuseStep 1711427 = 2567141) B2567141
theorem B4627793 : Blo 1711056 4627793 := bstep (se 2 (by rfl) ⟨1735422, by rfl⟩ : syracuseStep 4627793 = 3470845) B3470845
theorem B1711443 : Blo 1711056 1711443 := bstep (se 1 (by rfl) ⟨1283582, by rfl⟩ : syracuseStep 1711443 = 2567165) B2567165
theorem B4873571 : Blo 1711056 4873571 := bstep (se 1 (by rfl) ⟨3655178, by rfl⟩ : syracuseStep 4873571 = 7310357) B7310357
theorem B1711459 : Blo 1711056 1711459 := bstep (se 1 (by rfl) ⟨1283594, by rfl⟩ : syracuseStep 1711459 = 2567189) B2567189
theorem B1711475 : Blo 1711056 1711475 := bstep (se 1 (by rfl) ⟨1283606, by rfl⟩ : syracuseStep 1711475 = 2567213) B2567213
theorem B1711491 : Blo 1711056 1711491 := bstep (se 1 (by rfl) ⟨1283618, by rfl⟩ : syracuseStep 1711491 = 2567237) B2567237
theorem B1711507 : Blo 1711056 1711507 := bstep (se 1 (by rfl) ⟨1283630, by rfl⟩ : syracuseStep 1711507 = 2567261) B2567261
theorem B1711523 : Blo 1711056 1711523 := bstep (se 1 (by rfl) ⟨1283642, by rfl⟩ : syracuseStep 1711523 = 2567285) B2567285
theorem B1711539 : Blo 1711056 1711539 := bstep (se 1 (by rfl) ⟨1283654, by rfl⟩ : syracuseStep 1711539 = 2567309) B2567309
theorem B1711555 : Blo 1711056 1711555 := bstep (se 1 (by rfl) ⟨1283666, by rfl⟩ : syracuseStep 1711555 = 2567333) B2567333
theorem B1711571 : Blo 1711056 1711571 := bstep (se 1 (by rfl) ⟨1283678, by rfl⟩ : syracuseStep 1711571 = 2567357) B2567357
theorem B1711587 : Blo 1711056 1711587 := bstep (se 1 (by rfl) ⟨1283690, by rfl⟩ : syracuseStep 1711587 = 2567381) B2567381
theorem B1711603 : Blo 1711056 1711603 := bstep (se 1 (by rfl) ⟨1283702, by rfl⟩ : syracuseStep 1711603 = 2567405) B2567405
theorem B1711619 : Blo 1711056 1711619 := bstep (se 1 (by rfl) ⟨1283714, by rfl⟩ : syracuseStep 1711619 = 2567429) B2567429
theorem B1711635 : Blo 1711056 1711635 := bstep (se 1 (by rfl) ⟨1283726, by rfl⟩ : syracuseStep 1711635 = 2567453) B2567453
theorem B1711651 : Blo 1711056 1711651 := bstep (se 1 (by rfl) ⟨1283738, by rfl⟩ : syracuseStep 1711651 = 2567477) B2567477
theorem B1711667 : Blo 1711056 1711667 := bstep (se 1 (by rfl) ⟨1283750, by rfl⟩ : syracuseStep 1711667 = 2567501) B2567501
theorem B1711683 : Blo 1711056 1711683 := bstep (se 1 (by rfl) ⟨1283762, by rfl⟩ : syracuseStep 1711683 = 2567525) B2567525
theorem B1711699 : Blo 1711056 1711699 := bstep (se 1 (by rfl) ⟨1283774, by rfl⟩ : syracuseStep 1711699 = 2567549) B2567549
theorem B1711715 : Blo 1711056 1711715 := bstep (se 1 (by rfl) ⟨1283786, by rfl⟩ : syracuseStep 1711715 = 2567573) B2567573
theorem B1711731 : Blo 1711056 1711731 := bstep (se 1 (by rfl) ⟨1283798, by rfl⟩ : syracuseStep 1711731 = 2567597) B2567597
theorem B1711747 : Blo 1711056 1711747 := bstep (se 1 (by rfl) ⟨1283810, by rfl⟩ : syracuseStep 1711747 = 2567621) B2567621
theorem B6504077 : Blo 1711056 6504077 := bstep (se 3 (by rfl) ⟨1219514, by rfl⟩ : syracuseStep 6504077 = 2439029) B2439029
theorem B1711763 : Blo 1711056 1711763 := bstep (se 1 (by rfl) ⟨1283822, by rfl⟩ : syracuseStep 1711763 = 2567645) B2567645
theorem B1711779 : Blo 1711056 1711779 := bstep (se 1 (by rfl) ⟨1283834, by rfl⟩ : syracuseStep 1711779 = 2567669) B2567669
theorem B4628141 : Blo 1711056 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B9256625 : Blo 1711056 9256625 := bstep (se 2 (by rfl) ⟨3471234, by rfl⟩ : syracuseStep 9256625 = 6942469) B6942469
theorem B2743985 : Blo 1711056 2743985 := bstep (se 2 (by rfl) ⟨1028994, by rfl⟩ : syracuseStep 2743985 = 2057989) B2057989
theorem B1711795 : Blo 1711056 1711795 := bstep (se 1 (by rfl) ⟨1283846, by rfl⟩ : syracuseStep 1711795 = 2567693) B2567693
theorem B1711811 : Blo 1711056 1711811 := bstep (se 1 (by rfl) ⟨1283858, by rfl⟩ : syracuseStep 1711811 = 2567717) B2567717
theorem B11116237 : Blo 1711056 11116237 := bstep (se 3 (by rfl) ⟨2084294, by rfl⟩ : syracuseStep 11116237 = 4168589) B4168589
theorem B1711827 : Blo 1711056 1711827 := bstep (se 1 (by rfl) ⟨1283870, by rfl⟩ : syracuseStep 1711827 = 2567741) B2567741
theorem B1711843 : Blo 1711056 1711843 := bstep (se 1 (by rfl) ⟨1283882, by rfl⟩ : syracuseStep 1711843 = 2567765) B2567765
theorem B4333297 : Blo 1711056 4333297 := bstep (se 2 (by rfl) ⟨1624986, by rfl⟩ : syracuseStep 4333297 = 3249973) B3249973
theorem B1711859 : Blo 1711056 1711859 := bstep (se 1 (by rfl) ⟨1283894, by rfl⟩ : syracuseStep 1711859 = 2567789) B2567789
theorem B1711875 : Blo 1711056 1711875 := bstep (se 1 (by rfl) ⟨1283906, by rfl⟩ : syracuseStep 1711875 = 2567813) B2567813
theorem B3850001 : Blo 1711056 3850001 := bstep (se 2 (by rfl) ⟨1443750, by rfl⟩ : syracuseStep 3850001 = 2887501) B2887501
theorem B1711891 : Blo 1711056 1711891 := bstep (se 1 (by rfl) ⟨1283918, by rfl⟩ : syracuseStep 1711891 = 2567837) B2567837
theorem B3850019 : Blo 1711056 3850019 := bstep (se 1 (by rfl) ⟨2887514, by rfl⟩ : syracuseStep 3850019 = 5775029) B5775029
theorem B1711907 : Blo 1711056 1711907 := bstep (se 1 (by rfl) ⟨1283930, by rfl⟩ : syracuseStep 1711907 = 2567861) B2567861
theorem B4628269 : Blo 1711056 4628269 := bstep (se 3 (by rfl) ⟨867800, by rfl⟩ : syracuseStep 4628269 = 1735601) B1735601
theorem B1711923 : Blo 1711056 1711923 := bstep (se 1 (by rfl) ⟨1283942, by rfl⟩ : syracuseStep 1711923 = 2567885) B2567885
theorem B1711939 : Blo 1711056 1711939 := bstep (se 1 (by rfl) ⟨1283954, by rfl⟩ : syracuseStep 1711939 = 2567909) B2567909
theorem B1711955 : Blo 1711056 1711955 := bstep (se 1 (by rfl) ⟨1283966, by rfl⟩ : syracuseStep 1711955 = 2567933) B2567933
theorem B6168419 : Blo 1711056 6168419 := bstep (se 1 (by rfl) ⟨4626314, by rfl⟩ : syracuseStep 6168419 = 9252629) B9252629
theorem B1711971 : Blo 1711056 1711971 := bstep (se 1 (by rfl) ⟨1283978, by rfl⟩ : syracuseStep 1711971 = 2567957) B2567957
theorem B1711987 : Blo 1711056 1711987 := bstep (se 1 (by rfl) ⟨1283990, by rfl⟩ : syracuseStep 1711987 = 2567981) B2567981
theorem B1712003 : Blo 1711056 1712003 := bstep (se 1 (by rfl) ⟨1284002, by rfl⟩ : syracuseStep 1712003 = 2568005) B2568005
theorem B5775245 : Blo 1711056 5775245 := bstep (se 3 (by rfl) ⟨1082858, by rfl⟩ : syracuseStep 5775245 = 2165717) B2165717
theorem B1712019 : Blo 1711056 1712019 := bstep (se 1 (by rfl) ⟨1284014, by rfl⟩ : syracuseStep 1712019 = 2568029) B2568029
theorem B1712035 : Blo 1711056 1712035 := bstep (se 1 (by rfl) ⟨1284026, by rfl⟩ : syracuseStep 1712035 = 2568053) B2568053
theorem B1712051 : Blo 1711056 1712051 := bstep (se 1 (by rfl) ⟨1284038, by rfl⟩ : syracuseStep 1712051 = 2568077) B2568077
theorem B1925059 : Blo 1711056 1925059 := bstep (se 1 (by rfl) ⟨1443794, by rfl⟩ : syracuseStep 1925059 = 2887589) B2887589
theorem B5775299 : Blo 1711056 5775299 := bstep (se 1 (by rfl) ⟨4331474, by rfl⟩ : syracuseStep 5775299 = 8662949) B8662949
theorem B1712067 : Blo 1711056 1712067 := bstep (se 1 (by rfl) ⟨1284050, by rfl⟩ : syracuseStep 1712067 = 2568101) B2568101
theorem B1712083 : Blo 1711056 1712083 := bstep (se 1 (by rfl) ⟨1284062, by rfl⟩ : syracuseStep 1712083 = 2568125) B2568125
theorem B1712099 : Blo 1711056 1712099 := bstep (se 1 (by rfl) ⟨1284074, by rfl⟩ : syracuseStep 1712099 = 2568149) B2568149
theorem B19505123 : Blo 1711056 19505123 := bstep (se 1 (by rfl) ⟨14628842, by rfl⟩ : syracuseStep 19505123 = 29257685) B29257685
theorem B1712115 : Blo 1711056 1712115 := bstep (se 1 (by rfl) ⟨1284086, by rfl⟩ : syracuseStep 1712115 = 2568173) B2568173
theorem B1925131 : Blo 1711056 1925131 := bstep (se 1 (by rfl) ⟨1443848, by rfl⟩ : syracuseStep 1925131 = 2887697) B2887697
theorem B1712139 : Blo 1711056 1712139 := bstep (se 1 (by rfl) ⟨1284104, by rfl⟩ : syracuseStep 1712139 = 2568209) B2568209
theorem B31252493 : Blo 1711056 31252493 := bstep (se 3 (by rfl) ⟨5859842, by rfl⟩ : syracuseStep 31252493 = 11719685) B11719685
theorem B1712151 : Blo 1711056 1712151 := bstep (se 1 (by rfl) ⟨1284113, by rfl⟩ : syracuseStep 1712151 = 2568227) B2568227
theorem B1712171 : Blo 1711056 1712171 := bstep (se 1 (by rfl) ⟨1284128, by rfl⟩ : syracuseStep 1712171 = 2568257) B2568257
theorem B1712183 : Blo 1711056 1712183 := bstep (se 1 (by rfl) ⟨1284137, by rfl⟩ : syracuseStep 1712183 = 2568275) B2568275
theorem B9879617 : Blo 1711056 9879617 := bstep (se 2 (by rfl) ⟨3704856, by rfl⟩ : syracuseStep 9879617 = 7409713) B7409713
theorem B1712203 : Blo 1711056 1712203 := bstep (se 1 (by rfl) ⟨1284152, by rfl⟩ : syracuseStep 1712203 = 2568305) B2568305
theorem B1712215 : Blo 1711056 1712215 := bstep (se 1 (by rfl) ⟨1284161, by rfl⟩ : syracuseStep 1712215 = 2568323) B2568323
theorem B4628573 : Blo 1711056 4628573 := bstep (se 3 (by rfl) ⟨867857, by rfl⟩ : syracuseStep 4628573 = 1735715) B1735715
theorem B9887837 : Blo 1711056 9887837 := bstep (se 3 (by rfl) ⟨1853969, by rfl⟩ : syracuseStep 9887837 = 3707939) B3707939
theorem B1712235 : Blo 1711056 1712235 := bstep (se 1 (by rfl) ⟨1284176, by rfl⟩ : syracuseStep 1712235 = 2568353) B2568353
theorem B1925239 : Blo 1711056 1925239 := bstep (se 1 (by rfl) ⟨1443929, by rfl⟩ : syracuseStep 1925239 = 2887859) B2887859
theorem B1712247 : Blo 1711056 1712247 := bstep (se 1 (by rfl) ⟨1284185, by rfl⟩ : syracuseStep 1712247 = 2568371) B2568371
theorem B3850379 : Blo 1711056 3850379 := bstep (se 1 (by rfl) ⟨2887784, by rfl⟩ : syracuseStep 3850379 = 5775569) B5775569
theorem B1712267 : Blo 1711056 1712267 := bstep (se 1 (by rfl) ⟨1284200, by rfl⟩ : syracuseStep 1712267 = 2568401) B2568401
theorem B1712279 : Blo 1711056 1712279 := bstep (se 1 (by rfl) ⟨1284209, by rfl⟩ : syracuseStep 1712279 = 2568419) B2568419
theorem B1712299 : Blo 1711056 1712299 := bstep (se 1 (by rfl) ⟨1284224, by rfl⟩ : syracuseStep 1712299 = 2568449) B2568449
theorem B1712311 : Blo 1711056 1712311 := bstep (se 1 (by rfl) ⟨1284233, by rfl⟩ : syracuseStep 1712311 = 2568467) B2568467
theorem B3850433 : Blo 1711056 3850433 := bstep (se 2 (by rfl) ⟨1443912, by rfl⟩ : syracuseStep 3850433 = 2887825) B2887825
theorem B1712331 : Blo 1711056 1712331 := bstep (se 1 (by rfl) ⟨1284248, by rfl⟩ : syracuseStep 1712331 = 2568497) B2568497
theorem B1712343 : Blo 1711056 1712343 := bstep (se 1 (by rfl) ⟨1284257, by rfl⟩ : syracuseStep 1712343 = 2568515) B2568515
theorem B1712363 : Blo 1711056 1712363 := bstep (se 1 (by rfl) ⟨1284272, by rfl⟩ : syracuseStep 1712363 = 2568545) B2568545
theorem B1712375 : Blo 1711056 1712375 := bstep (se 1 (by rfl) ⟨1284281, by rfl⟩ : syracuseStep 1712375 = 2568563) B2568563
theorem B1712395 : Blo 1711056 1712395 := bstep (se 1 (by rfl) ⟨1284296, by rfl⟩ : syracuseStep 1712395 = 2568593) B2568593
theorem B1712407 : Blo 1711056 1712407 := bstep (se 1 (by rfl) ⟨1284305, by rfl⟩ : syracuseStep 1712407 = 2568611) B2568611
theorem B1925419 : Blo 1711056 1925419 := bstep (se 1 (by rfl) ⟨1444064, by rfl⟩ : syracuseStep 1925419 = 2888129) B2888129
theorem B9748781 : Blo 1711056 9748781 := bstep (se 3 (by rfl) ⟨1827896, by rfl⟩ : syracuseStep 9748781 = 3655793) B3655793
theorem B1712427 : Blo 1711056 1712427 := bstep (se 1 (by rfl) ⟨1284320, by rfl⟩ : syracuseStep 1712427 = 2568641) B2568641
theorem B1712439 : Blo 1711056 1712439 := bstep (se 1 (by rfl) ⟨1284329, by rfl⟩ : syracuseStep 1712439 = 2568659) B2568659
theorem B1712459 : Blo 1711056 1712459 := bstep (se 1 (by rfl) ⟨1284344, by rfl⟩ : syracuseStep 1712459 = 2568689) B2568689
theorem B1712471 : Blo 1711056 1712471 := bstep (se 1 (by rfl) ⟨1284353, by rfl⟩ : syracuseStep 1712471 = 2568707) B2568707
theorem B8667485 : Blo 1711056 8667485 := bstep (se 3 (by rfl) ⟨1625153, by rfl⟩ : syracuseStep 8667485 = 3250307) B3250307
theorem B1712491 : Blo 1711056 1712491 := bstep (se 1 (by rfl) ⟨1284368, by rfl⟩ : syracuseStep 1712491 = 2568737) B2568737
theorem B1712503 : Blo 1711056 1712503 := bstep (se 1 (by rfl) ⟨1284377, by rfl⟩ : syracuseStep 1712503 = 2568755) B2568755
theorem B6422915 : Blo 1711056 6422915 := bstep (se 1 (by rfl) ⟨4817186, by rfl⟩ : syracuseStep 6422915 = 9634373) B9634373
theorem B1712523 : Blo 1711056 1712523 := bstep (se 1 (by rfl) ⟨1284392, by rfl⟩ : syracuseStep 1712523 = 2568785) B2568785
theorem B1925527 : Blo 1711056 1925527 := bstep (se 1 (by rfl) ⟨1444145, by rfl⟩ : syracuseStep 1925527 = 2888291) B2888291
theorem B1712535 : Blo 1711056 1712535 := bstep (se 1 (by rfl) ⟨1284401, by rfl⟩ : syracuseStep 1712535 = 2568803) B2568803
theorem B3850649 : Blo 1711056 3850649 := bstep (se 2 (by rfl) ⟨1443993, by rfl⟩ : syracuseStep 3850649 = 2887987) B2887987
theorem B1712555 : Blo 1711056 1712555 := bstep (se 1 (by rfl) ⟨1284416, by rfl⟩ : syracuseStep 1712555 = 2568833) B2568833
theorem B1712567 : Blo 1711056 1712567 := bstep (se 1 (by rfl) ⟨1284425, by rfl⟩ : syracuseStep 1712567 = 2568851) B2568851
theorem B1712587 : Blo 1711056 1712587 := bstep (se 1 (by rfl) ⟨1284440, by rfl⟩ : syracuseStep 1712587 = 2568881) B2568881
theorem B1712599 : Blo 1711056 1712599 := bstep (se 1 (by rfl) ⟨1284449, by rfl⟩ : syracuseStep 1712599 = 2568899) B2568899
theorem B52724195 : Blo 1711056 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B1827307 : Blo 1711056 1827307 := bstep (se 1 (by rfl) ⟨1370480, by rfl⟩ : syracuseStep 1827307 = 2740961) B2740961
theorem B1712619 : Blo 1711056 1712619 := bstep (se 1 (by rfl) ⟨1284464, by rfl⟩ : syracuseStep 1712619 = 2568929) B2568929
theorem B3850739 : Blo 1711056 3850739 := bstep (se 1 (by rfl) ⟨2888054, by rfl⟩ : syracuseStep 3850739 = 5776109) B5776109
theorem B1712631 : Blo 1711056 1712631 := bstep (se 1 (by rfl) ⟨1284473, by rfl⟩ : syracuseStep 1712631 = 2568947) B2568947
theorem B1712651 : Blo 1711056 1712651 := bstep (se 1 (by rfl) ⟨1284488, by rfl⟩ : syracuseStep 1712651 = 2568977) B2568977
theorem B3850775 : Blo 1711056 3850775 := bstep (se 1 (by rfl) ⟨2888081, by rfl⟩ : syracuseStep 3850775 = 5776163) B5776163
theorem B1712663 : Blo 1711056 1712663 := bstep (se 1 (by rfl) ⟨1284497, by rfl⟩ : syracuseStep 1712663 = 2568995) B2568995
theorem B1712683 : Blo 1711056 1712683 := bstep (se 1 (by rfl) ⟨1284512, by rfl⟩ : syracuseStep 1712683 = 2569025) B2569025
theorem B1712695 : Blo 1711056 1712695 := bstep (se 1 (by rfl) ⟨1284521, by rfl⟩ : syracuseStep 1712695 = 2569043) B2569043
theorem B5775947 : Blo 1711056 5775947 := bstep (se 1 (by rfl) ⟨4331960, by rfl⟩ : syracuseStep 5775947 = 8663921) B8663921
theorem B1925707 : Blo 1711056 1925707 := bstep (se 1 (by rfl) ⟨1444280, by rfl⟩ : syracuseStep 1925707 = 2888561) B2888561
theorem B1712715 : Blo 1711056 1712715 := bstep (se 1 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 1712715 = 2569073) B2569073
theorem B1712727 : Blo 1711056 1712727 := bstep (se 1 (by rfl) ⟨1284545, by rfl⟩ : syracuseStep 1712727 = 2569091) B2569091
theorem B12337757 : Blo 1711056 12337757 := bstep (se 3 (by rfl) ⟨2313329, by rfl⟩ : syracuseStep 12337757 = 4626659) B4626659
theorem B1712747 : Blo 1711056 1712747 := bstep (se 1 (by rfl) ⟨1284560, by rfl⟩ : syracuseStep 1712747 = 2569121) B2569121
theorem B1712759 : Blo 1711056 1712759 := bstep (se 1 (by rfl) ⟨1284569, by rfl⟩ : syracuseStep 1712759 = 2569139) B2569139
theorem B59294339 : Blo 1711056 59294339 := bstep (se 1 (by rfl) ⟨44470754, by rfl⟩ : syracuseStep 59294339 = 88941509) B88941509
theorem B1712779 : Blo 1711056 1712779 := bstep (se 1 (by rfl) ⟨1284584, by rfl⟩ : syracuseStep 1712779 = 2569169) B2569169
theorem B2056855 : Blo 1711056 2056855 := bstep (se 1 (by rfl) ⟨1542641, by rfl⟩ : syracuseStep 2056855 = 3085283) B3085283
theorem B1712791 : Blo 1711056 1712791 := bstep (se 1 (by rfl) ⟨1284593, by rfl⟩ : syracuseStep 1712791 = 2569187) B2569187
theorem B1712811 : Blo 1711056 1712811 := bstep (se 1 (by rfl) ⟨1284608, by rfl⟩ : syracuseStep 1712811 = 2569217) B2569217
theorem B1925815 : Blo 1711056 1925815 := bstep (se 1 (by rfl) ⟨1444361, by rfl⟩ : syracuseStep 1925815 = 2888723) B2888723
theorem B1712823 : Blo 1711056 1712823 := bstep (se 1 (by rfl) ⟨1284617, by rfl⟩ : syracuseStep 1712823 = 2569235) B2569235
theorem B3850955 : Blo 1711056 3850955 := bstep (se 1 (by rfl) ⟨2888216, by rfl⟩ : syracuseStep 3850955 = 5776433) B5776433
theorem B1712843 : Blo 1711056 1712843 := bstep (se 1 (by rfl) ⟨1284632, by rfl⟩ : syracuseStep 1712843 = 2569265) B2569265
theorem B1712855 : Blo 1711056 1712855 := bstep (se 1 (by rfl) ⟨1284641, by rfl⟩ : syracuseStep 1712855 = 2569283) B2569283
theorem B1712875 : Blo 1711056 1712875 := bstep (se 1 (by rfl) ⟨1284656, by rfl⟩ : syracuseStep 1712875 = 2569313) B2569313
theorem B1712887 : Blo 1711056 1712887 := bstep (se 1 (by rfl) ⟨1284665, by rfl⟩ : syracuseStep 1712887 = 2569331) B2569331
theorem B3851009 : Blo 1711056 3851009 := bstep (se 2 (by rfl) ⟨1444128, by rfl⟩ : syracuseStep 3851009 = 2888257) B2888257
theorem B1712907 : Blo 1711056 1712907 := bstep (se 1 (by rfl) ⟨1284680, by rfl⟩ : syracuseStep 1712907 = 2569361) B2569361
theorem B1712919 : Blo 1711056 1712919 := bstep (se 1 (by rfl) ⟨1284689, by rfl⟩ : syracuseStep 1712919 = 2569379) B2569379
theorem B1712939 : Blo 1711056 1712939 := bstep (se 1 (by rfl) ⟨1284704, by rfl⟩ : syracuseStep 1712939 = 2569409) B2569409
theorem B1712951 : Blo 1711056 1712951 := bstep (se 1 (by rfl) ⟨1284713, by rfl⟩ : syracuseStep 1712951 = 2569427) B2569427
theorem B4334411 : Blo 1711056 4334411 := bstep (se 1 (by rfl) ⟨3250808, by rfl⟩ : syracuseStep 4334411 = 6501617) B6501617
theorem B1712971 : Blo 1711056 1712971 := bstep (se 1 (by rfl) ⟨1284728, by rfl⟩ : syracuseStep 1712971 = 2569457) B2569457
theorem B1712983 : Blo 1711056 1712983 := bstep (se 1 (by rfl) ⟨1284737, by rfl⟩ : syracuseStep 1712983 = 2569475) B2569475
theorem B5776217 : Blo 1711056 5776217 := bstep (se 2 (by rfl) ⟨2166081, by rfl⟩ : syracuseStep 5776217 = 4332163) B4332163
theorem B6939485 : Blo 1711056 6939485 := bstep (se 3 (by rfl) ⟨1301153, by rfl⟩ : syracuseStep 6939485 = 2602307) B2602307
theorem B1925995 : Blo 1711056 1925995 := bstep (se 1 (by rfl) ⟨1444496, by rfl⟩ : syracuseStep 1925995 = 2888993) B2888993
theorem B1713003 : Blo 1711056 1713003 := bstep (se 1 (by rfl) ⟨1284752, by rfl⟩ : syracuseStep 1713003 = 2569505) B2569505
theorem B1713015 : Blo 1711056 1713015 := bstep (se 1 (by rfl) ⟨1284761, by rfl⟩ : syracuseStep 1713015 = 2569523) B2569523
theorem B1713035 : Blo 1711056 1713035 := bstep (se 1 (by rfl) ⟨1284776, by rfl⟩ : syracuseStep 1713035 = 2569553) B2569553
theorem B1713047 : Blo 1711056 1713047 := bstep (se 1 (by rfl) ⟨1284785, by rfl⟩ : syracuseStep 1713047 = 2569571) B2569571
theorem B4113355 : Blo 1711056 4113355 := bstep (se 1 (by rfl) ⟨3085016, by rfl⟩ : syracuseStep 4113355 = 6170033) B6170033
theorem B1926103 : Blo 1711056 1926103 := bstep (se 1 (by rfl) ⟨1444577, by rfl⟩ : syracuseStep 1926103 = 2889155) B2889155
theorem B3851225 : Blo 1711056 3851225 := bstep (se 2 (by rfl) ⟨1444209, by rfl⟩ : syracuseStep 3851225 = 2888419) B2888419
theorem B6939613 : Blo 1711056 6939613 := bstep (se 3 (by rfl) ⟨1301177, by rfl⟩ : syracuseStep 6939613 = 2602355) B2602355
theorem B3851315 : Blo 1711056 3851315 := bstep (se 1 (by rfl) ⟨2888486, by rfl⟩ : syracuseStep 3851315 = 5776973) B5776973
theorem B3851351 : Blo 1711056 3851351 := bstep (se 1 (by rfl) ⟨2888513, by rfl⟩ : syracuseStep 3851351 = 5777027) B5777027
theorem B1926283 : Blo 1711056 1926283 := bstep (se 1 (by rfl) ⟨1444712, by rfl⟩ : syracuseStep 1926283 = 2889425) B2889425
theorem B5481665 : Blo 1711056 5481665 := bstep (se 2 (by rfl) ⟨2055624, by rfl⟩ : syracuseStep 5481665 = 4111249) B4111249
theorem B2344151 : Blo 1711056 2344151 := bstep (se 1 (by rfl) ⟨1758113, by rfl⟩ : syracuseStep 2344151 = 3516227) B3516227
theorem B1828055 : Blo 1711056 1828055 := bstep (se 1 (by rfl) ⟨1371041, by rfl⟩ : syracuseStep 1828055 = 2742083) B2742083
theorem B1926391 : Blo 1711056 1926391 := bstep (se 1 (by rfl) ⟨1444793, by rfl⟩ : syracuseStep 1926391 = 2889587) B2889587
theorem B3851531 : Blo 1711056 3851531 := bstep (se 1 (by rfl) ⟨2888648, by rfl⟩ : syracuseStep 3851531 = 5777297) B5777297
theorem B3851585 : Blo 1711056 3851585 := bstep (se 2 (by rfl) ⟨1444344, by rfl⟩ : syracuseStep 3851585 = 2888689) B2888689
theorem B6169931 : Blo 1711056 6169931 := bstep (se 1 (by rfl) ⟨4627448, by rfl⟩ : syracuseStep 6169931 = 9254897) B9254897
theorem B2196887 : Blo 1711056 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B1926571 : Blo 1711056 1926571 := bstep (se 1 (by rfl) ⟨1444928, by rfl⟩ : syracuseStep 1926571 = 2889857) B2889857
theorem B6497729 : Blo 1711056 6497729 := bstep (se 2 (by rfl) ⟨2436648, by rfl⟩ : syracuseStep 6497729 = 4873297) B4873297
theorem B14632397 : Blo 1711056 14632397 := bstep (se 3 (by rfl) ⟨2743574, by rfl⟩ : syracuseStep 14632397 = 5487149) B5487149
theorem B3655127 : Blo 1711056 3655127 := bstep (se 1 (by rfl) ⟨2741345, by rfl⟩ : syracuseStep 3655127 = 5482691) B5482691
theorem B10970585 : Blo 1711056 10970585 := bstep (se 2 (by rfl) ⟨4113969, by rfl⟩ : syracuseStep 10970585 = 8227939) B8227939
theorem B12338705 : Blo 1711056 12338705 := bstep (se 2 (by rfl) ⟨4627014, by rfl⟩ : syracuseStep 12338705 = 9254029) B9254029
theorem B5776919 : Blo 1711056 5776919 := bstep (se 1 (by rfl) ⟨4332689, by rfl⟩ : syracuseStep 5776919 = 8665379) B8665379
theorem B1926679 : Blo 1711056 1926679 := bstep (se 1 (by rfl) ⟨1445009, by rfl⟩ : syracuseStep 1926679 = 2890019) B2890019
theorem B3851801 : Blo 1711056 3851801 := bstep (se 2 (by rfl) ⟨1444425, by rfl⟩ : syracuseStep 3851801 = 2888851) B2888851
theorem B24684101 : Blo 1711056 24684101 := bstep (se 4 (by rfl) ⟨2314134, by rfl⟩ : syracuseStep 24684101 = 4628269) B4628269
theorem B9881189 : Blo 1711056 9881189 := bstep (se 4 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 9881189 = 1852723) B1852723
theorem B3851891 : Blo 1711056 3851891 := bstep (se 1 (by rfl) ⟨2888918, by rfl⟩ : syracuseStep 3851891 = 5777837) B5777837
theorem B3655297 : Blo 1711056 3655297 := bstep (se 2 (by rfl) ⟨1370736, by rfl⟩ : syracuseStep 3655297 = 2741473) B2741473
theorem B3851927 : Blo 1711056 3851927 := bstep (se 1 (by rfl) ⟨2888945, by rfl⟩ : syracuseStep 3851927 = 5777891) B5777891
theorem B1926859 : Blo 1711056 1926859 := bstep (se 1 (by rfl) ⟨1445144, by rfl⟩ : syracuseStep 1926859 = 2890289) B2890289
theorem B4875997 : Blo 1711056 4875997 := bstep (se 3 (by rfl) ⟨914249, by rfl⟩ : syracuseStep 4875997 = 1828499) B1828499
theorem B4335383 : Blo 1711056 4335383 := bstep (se 1 (by rfl) ⟨3251537, by rfl⟩ : syracuseStep 4335383 = 6503075) B6503075
theorem B1926967 : Blo 1711056 1926967 := bstep (se 1 (by rfl) ⟨1445225, by rfl⟩ : syracuseStep 1926967 = 2890451) B2890451
theorem B3852107 : Blo 1711056 3852107 := bstep (se 1 (by rfl) ⟨2889080, by rfl⟩ : syracuseStep 3852107 = 5778161) B5778161
theorem B3852161 : Blo 1711056 3852161 := bstep (se 2 (by rfl) ⟨1444560, by rfl⟩ : syracuseStep 3852161 = 2889121) B2889121
theorem B6678445 : Blo 1711056 6678445 := bstep (se 3 (by rfl) ⟨1252208, by rfl⟩ : syracuseStep 6678445 = 2504417) B2504417
theorem B12502961 : Blo 1711056 12502961 := bstep (se 2 (by rfl) ⟨4688610, by rfl⟩ : syracuseStep 12502961 = 9377221) B9377221
theorem B50743219 : Blo 1711056 50743219 := bstep (se 1 (by rfl) ⟨38057414, by rfl⟩ : syracuseStep 50743219 = 76114829) B76114829
theorem B3655639 : Blo 1711056 3655639 := bstep (se 1 (by rfl) ⟨2741729, by rfl⟩ : syracuseStep 3655639 = 5483459) B5483459
theorem B1927147 : Blo 1711056 1927147 := bstep (se 1 (by rfl) ⟨1445360, by rfl⟩ : syracuseStep 1927147 = 2890721) B2890721
theorem B5777459 : Blo 1711056 5777459 := bstep (se 1 (by rfl) ⟨4333094, by rfl⟩ : syracuseStep 5777459 = 8666189) B8666189
theorem B3852377 : Blo 1711056 3852377 := bstep (se 2 (by rfl) ⟨1444641, by rfl⟩ : syracuseStep 3852377 = 2889283) B2889283
theorem B1951895 : Blo 1711056 1951895 := bstep (se 1 (by rfl) ⟨1463921, by rfl⟩ : syracuseStep 1951895 = 2927843) B2927843
theorem B13002929 : Blo 1711056 13002929 := bstep (se 2 (by rfl) ⟨4876098, by rfl⟩ : syracuseStep 13002929 = 9752197) B9752197
theorem B3852467 : Blo 1711056 3852467 := bstep (se 1 (by rfl) ⟨2889350, by rfl⟩ : syracuseStep 3852467 = 5778701) B5778701
theorem B3852503 : Blo 1711056 3852503 := bstep (se 1 (by rfl) ⟨2889377, by rfl⟩ : syracuseStep 3852503 = 5778755) B5778755
theorem B14821649 : Blo 1711056 14821649 := bstep (se 2 (by rfl) ⟨5558118, by rfl⟩ : syracuseStep 14821649 = 11116237) B11116237
theorem B4114739 : Blo 1711056 4114739 := bstep (se 1 (by rfl) ⟨3086054, by rfl⟩ : syracuseStep 4114739 = 6172109) B6172109
theorem B5777729 : Blo 1711056 5777729 := bstep (se 2 (by rfl) ⟨2166648, by rfl⟩ : syracuseStep 5777729 = 4333297) B4333297
theorem B3852683 : Blo 1711056 3852683 := bstep (se 1 (by rfl) ⟨2889512, by rfl⟩ : syracuseStep 3852683 = 5779025) B5779025
theorem B8669591 : Blo 1711056 8669591 := bstep (se 1 (by rfl) ⟨6502193, by rfl⟩ : syracuseStep 8669591 = 13004387) B13004387
theorem B4336051 : Blo 1711056 4336051 := bstep (se 1 (by rfl) ⟨3252038, by rfl⟩ : syracuseStep 4336051 = 6504077) B6504077
theorem B3852737 : Blo 1711056 3852737 := bstep (se 2 (by rfl) ⟨1444776, by rfl⟩ : syracuseStep 3852737 = 2889553) B2889553
theorem B6171083 : Blo 1711056 6171083 := bstep (se 1 (by rfl) ⟨4628312, by rfl⟩ : syracuseStep 6171083 = 9256625) B9256625
theorem B1829323 : Blo 1711056 1829323 := bstep (se 1 (by rfl) ⟨1371992, by rfl⟩ : syracuseStep 1829323 = 2743985) B2743985
theorem B2566667 : Blo 1711056 2566667 := bstep (se 1 (by rfl) ⟨1925000, by rfl⟩ : syracuseStep 2566667 = 3850001) B3850001
theorem B2566679 : Blo 1711056 2566679 := bstep (se 1 (by rfl) ⟨1925009, by rfl⟩ : syracuseStep 2566679 = 3850019) B3850019
theorem B2566745 : Blo 1711056 2566745 := bstep (se 2 (by rfl) ⟨962529, by rfl⟩ : syracuseStep 2566745 = 1925059) B1925059
theorem B13003415 : Blo 1711056 13003415 := bstep (se 1 (by rfl) ⟨9752561, by rfl⟩ : syracuseStep 13003415 = 19505123) B19505123
theorem B3852953 : Blo 1711056 3852953 := bstep (se 2 (by rfl) ⟨1444857, by rfl⟩ : syracuseStep 3852953 = 2889715) B2889715
theorem B2566859 : Blo 1711056 2566859 := bstep (se 1 (by rfl) ⟨1925144, by rfl⟩ : syracuseStep 2566859 = 3850289) B3850289
theorem B2566871 : Blo 1711056 2566871 := bstep (se 1 (by rfl) ⟨1925153, by rfl⟩ : syracuseStep 2566871 = 3850307) B3850307
theorem B3853043 : Blo 1711056 3853043 := bstep (se 1 (by rfl) ⟨2889782, by rfl⟩ : syracuseStep 3853043 = 5779565) B5779565
theorem B3656459 : Blo 1711056 3656459 := bstep (se 1 (by rfl) ⟨2742344, by rfl⟩ : syracuseStep 3656459 = 5484689) B5484689
theorem B2779915 : Blo 1711056 2779915 := bstep (se 1 (by rfl) ⟨2084936, by rfl⟩ : syracuseStep 2779915 = 4169873) B4169873
theorem B5557015 : Blo 1711056 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B2566937 : Blo 1711056 2566937 := bstep (se 2 (by rfl) ⟨962601, by rfl⟩ : syracuseStep 2566937 = 1925203) B1925203
theorem B3853079 : Blo 1711056 3853079 := bstep (se 1 (by rfl) ⟨2889809, by rfl⟩ : syracuseStep 3853079 = 5779619) B5779619
theorem B5860147 : Blo 1711056 5860147 := bstep (se 1 (by rfl) ⟨4395110, by rfl⟩ : syracuseStep 5860147 = 8790221) B8790221
theorem B8227649 : Blo 1711056 8227649 := bstep (se 2 (by rfl) ⟨3085368, by rfl⟩ : syracuseStep 8227649 = 6170737) B6170737
theorem B5778269 : Blo 1711056 5778269 := bstep (se 3 (by rfl) ⟨1083425, by rfl⟩ : syracuseStep 5778269 = 2166851) B2166851
theorem B2567051 : Blo 1711056 2567051 := bstep (se 1 (by rfl) ⟨1925288, by rfl⟩ : syracuseStep 2567051 = 3850577) B3850577
theorem B6499217 : Blo 1711056 6499217 := bstep (se 2 (by rfl) ⟨2437206, by rfl⟩ : syracuseStep 6499217 = 4874413) B4874413
theorem B2567063 : Blo 1711056 2567063 := bstep (se 1 (by rfl) ⟨1925297, by rfl⟩ : syracuseStep 2567063 = 3850595) B3850595
theorem B2165707 : Blo 1711056 2165707 := bstep (se 1 (by rfl) ⟨1624280, by rfl⟩ : syracuseStep 2165707 = 3248561) B3248561
theorem B3853259 : Blo 1711056 3853259 := bstep (se 1 (by rfl) ⟨2889944, by rfl⟩ : syracuseStep 3853259 = 5779889) B5779889
theorem B2567129 : Blo 1711056 2567129 := bstep (se 2 (by rfl) ⟨962673, by rfl⟩ : syracuseStep 2567129 = 1925347) B1925347
theorem B4877273 : Blo 1711056 4877273 := bstep (se 2 (by rfl) ⟨1828977, by rfl⟩ : syracuseStep 4877273 = 3657955) B3657955
theorem B3853313 : Blo 1711056 3853313 := bstep (se 2 (by rfl) ⟨1444992, by rfl⟩ : syracuseStep 3853313 = 2889985) B2889985
theorem B2567243 : Blo 1711056 2567243 := bstep (se 1 (by rfl) ⟨1925432, by rfl⟩ : syracuseStep 2567243 = 3850865) B3850865
theorem B2567255 : Blo 1711056 2567255 := bstep (se 1 (by rfl) ⟨1925441, by rfl⟩ : syracuseStep 2567255 = 3850883) B3850883
theorem B3656819 : Blo 1711056 3656819 := bstep (se 1 (by rfl) ⟨2742614, by rfl⟩ : syracuseStep 3656819 = 5485229) B5485229
theorem B10964099 : Blo 1711056 10964099 := bstep (se 1 (by rfl) ⟨8223074, by rfl⟩ : syracuseStep 10964099 = 16446149) B16446149
theorem B2567321 : Blo 1711056 2567321 := bstep (se 2 (by rfl) ⟨962745, by rfl⟩ : syracuseStep 2567321 = 1925491) B1925491
theorem B2436313 : Blo 1711056 2436313 := bstep (se 2 (by rfl) ⟨913617, by rfl⟩ : syracuseStep 2436313 = 1827235) B1827235
theorem B3853529 : Blo 1711056 3853529 := bstep (se 2 (by rfl) ⟨1445073, by rfl⟩ : syracuseStep 3853529 = 2890147) B2890147
theorem B2567435 : Blo 1711056 2567435 := bstep (se 1 (by rfl) ⟨1925576, by rfl⟩ : syracuseStep 2567435 = 3851153) B3851153
theorem B2567447 : Blo 1711056 2567447 := bstep (se 1 (by rfl) ⟨1925585, by rfl⟩ : syracuseStep 2567447 = 3851171) B3851171
theorem B3853619 : Blo 1711056 3853619 := bstep (se 1 (by rfl) ⟨2890214, by rfl⟩ : syracuseStep 3853619 = 5780429) B5780429
theorem B3853655 : Blo 1711056 3853655 := bstep (se 1 (by rfl) ⟨2890241, by rfl⟩ : syracuseStep 3853655 = 5780483) B5780483
theorem B2567513 : Blo 1711056 2567513 := bstep (se 2 (by rfl) ⟨962817, by rfl⟩ : syracuseStep 2567513 = 1925635) B1925635
theorem B6499673 : Blo 1711056 6499673 := bstep (se 2 (by rfl) ⟨2437377, by rfl⟩ : syracuseStep 6499673 = 4874755) B4874755
theorem B2567627 : Blo 1711056 2567627 := bstep (se 1 (by rfl) ⟨1925720, by rfl⟩ : syracuseStep 2567627 = 3851441) B3851441
theorem B2567639 : Blo 1711056 2567639 := bstep (se 1 (by rfl) ⟨1925729, by rfl⟩ : syracuseStep 2567639 = 3851459) B3851459
theorem B6172121 : Blo 1711056 6172121 := bstep (se 2 (by rfl) ⟨2314545, by rfl⟩ : syracuseStep 6172121 = 4629091) B4629091
theorem B3853835 : Blo 1711056 3853835 := bstep (se 1 (by rfl) ⟨2890376, by rfl⟩ : syracuseStep 3853835 = 5780753) B5780753
theorem B2567705 : Blo 1711056 2567705 := bstep (se 2 (by rfl) ⟨962889, by rfl⟩ : syracuseStep 2567705 = 1925779) B1925779
theorem B6499885 : Blo 1711056 6499885 := bstep (se 3 (by rfl) ⟨1218728, by rfl⟩ : syracuseStep 6499885 = 2437457) B2437457
theorem B12340781 : Blo 1711056 12340781 := bstep (se 3 (by rfl) ⟨2313896, by rfl⟩ : syracuseStep 12340781 = 4627793) B4627793
theorem B3853889 : Blo 1711056 3853889 := bstep (se 2 (by rfl) ⟨1445208, by rfl⟩ : syracuseStep 3853889 = 2890417) B2890417
theorem B2780747 : Blo 1711056 2780747 := bstep (se 1 (by rfl) ⟨2085560, by rfl⟩ : syracuseStep 2780747 = 4171121) B4171121
theorem B5484125 : Blo 1711056 5484125 := bstep (se 3 (by rfl) ⟨1028273, by rfl⟩ : syracuseStep 5484125 = 2056547) B2056547
theorem B6590045 : Blo 1711056 6590045 := bstep (se 3 (by rfl) ⟨1235633, by rfl⟩ : syracuseStep 6590045 = 2471267) B2471267
theorem B2567819 : Blo 1711056 2567819 := bstep (se 1 (by rfl) ⟨1925864, by rfl⟩ : syracuseStep 2567819 = 3851729) B3851729
theorem B2567831 : Blo 1711056 2567831 := bstep (se 1 (by rfl) ⟨1925873, by rfl⟩ : syracuseStep 2567831 = 3851747) B3851747
theorem B49360589 : Blo 1711056 49360589 := bstep (se 3 (by rfl) ⟨9255110, by rfl⟩ : syracuseStep 49360589 = 18510221) B18510221
theorem B19500749 : Blo 1711056 19500749 := bstep (se 3 (by rfl) ⟨3656390, by rfl⟩ : syracuseStep 19500749 = 7312781) B7312781
theorem B7409369 : Blo 1711056 7409369 := bstep (se 2 (by rfl) ⟨2778513, by rfl⟩ : syracuseStep 7409369 = 5557027) B5557027
theorem B2567897 : Blo 1711056 2567897 := bstep (se 2 (by rfl) ⟨962961, by rfl⟩ : syracuseStep 2567897 = 1925923) B1925923
theorem B6680323 : Blo 1711056 6680323 := bstep (se 1 (by rfl) ⟨5010242, by rfl⟩ : syracuseStep 6680323 = 10020485) B10020485
theorem B2887447 : Blo 1711056 2887447 := bstep (se 1 (by rfl) ⟨2165585, by rfl⟩ : syracuseStep 2887447 = 4331171) B4331171
theorem B3854105 : Blo 1711056 3854105 := bstep (se 2 (by rfl) ⟨1445289, by rfl⟩ : syracuseStep 3854105 = 2890579) B2890579
theorem B2568011 : Blo 1711056 2568011 := bstep (se 1 (by rfl) ⟨1926008, by rfl⟩ : syracuseStep 2568011 = 3852017) B3852017
theorem B2568023 : Blo 1711056 2568023 := bstep (se 1 (by rfl) ⟨1926017, by rfl⟩ : syracuseStep 2568023 = 3852035) B3852035
theorem B6500189 : Blo 1711056 6500189 := bstep (se 3 (by rfl) ⟨1218785, by rfl⟩ : syracuseStep 6500189 = 2437571) B2437571
theorem B3854195 : Blo 1711056 3854195 := bstep (se 1 (by rfl) ⟨2890646, by rfl⟩ : syracuseStep 3854195 = 5781293) B5781293
theorem B2166679 : Blo 1711056 2166679 := bstep (se 1 (by rfl) ⟨1625009, by rfl⟩ : syracuseStep 2166679 = 3250019) B3250019
theorem B9752471 : Blo 1711056 9752471 := bstep (se 1 (by rfl) ⟨7314353, by rfl⟩ : syracuseStep 9752471 = 14628707) B14628707
theorem B2568089 : Blo 1711056 2568089 := bstep (se 2 (by rfl) ⟨963033, by rfl⟩ : syracuseStep 2568089 = 1926067) B1926067
theorem B3854231 : Blo 1711056 3854231 := bstep (se 1 (by rfl) ⟨2890673, by rfl⟩ : syracuseStep 3854231 = 5781347) B5781347
theorem B5779403 : Blo 1711056 5779403 := bstep (se 1 (by rfl) ⟨4334552, by rfl⟩ : syracuseStep 5779403 = 8669105) B8669105
theorem B2568203 : Blo 1711056 2568203 := bstep (se 1 (by rfl) ⟨1926152, by rfl⟩ : syracuseStep 2568203 = 3852305) B3852305
theorem B2568215 : Blo 1711056 2568215 := bstep (se 1 (by rfl) ⟨1926161, by rfl⟩ : syracuseStep 2568215 = 3852323) B3852323
theorem B2568281 : Blo 1711056 2568281 := bstep (se 2 (by rfl) ⟨963105, by rfl⟩ : syracuseStep 2568281 = 1926211) B1926211
theorem B8786051 : Blo 1711056 8786051 := bstep (se 1 (by rfl) ⟨6589538, by rfl⟩ : syracuseStep 8786051 = 13179077) B13179077
theorem B2568395 : Blo 1711056 2568395 := bstep (se 1 (by rfl) ⟨1926296, by rfl⟩ : syracuseStep 2568395 = 3852593) B3852593
theorem B1712119 : Blo 1711056 1712119 := bstep (se 1 (by rfl) ⟨1284089, by rfl⟩ : syracuseStep 1712119 = 2568179) B2568179
theorem B2568407 : Blo 1711056 2568407 := bstep (se 1 (by rfl) ⟨1926305, by rfl⟩ : syracuseStep 2568407 = 3852611) B3852611
theorem B5779673 : Blo 1711056 5779673 := bstep (se 2 (by rfl) ⟨2167377, by rfl⟩ : syracuseStep 5779673 = 4334755) B4334755
theorem B2568473 : Blo 1711056 2568473 := bstep (se 2 (by rfl) ⟨963177, by rfl⟩ : syracuseStep 2568473 = 1926355) B1926355
theorem B22245677 : Blo 1711056 22245677 := bstep (se 3 (by rfl) ⟨4171064, by rfl⟩ : syracuseStep 22245677 = 8342129) B8342129
theorem B2888075 : Blo 1711056 2888075 := bstep (se 1 (by rfl) ⟨2166056, by rfl⟩ : syracuseStep 2888075 = 4332113) B4332113
theorem B2568587 : Blo 1711056 2568587 := bstep (se 1 (by rfl) ⟨1926440, by rfl⟩ : syracuseStep 2568587 = 3852881) B3852881
theorem B2568599 : Blo 1711056 2568599 := bstep (se 1 (by rfl) ⟨1926449, by rfl⟩ : syracuseStep 2568599 = 3852899) B3852899
theorem B7311809 : Blo 1711056 7311809 := bstep (se 2 (by rfl) ⟨2741928, by rfl⟩ : syracuseStep 7311809 = 5483857) B5483857
theorem B3248599 : Blo 1711056 3248599 := bstep (se 1 (by rfl) ⟨2436449, by rfl⟩ : syracuseStep 3248599 = 4872899) B4872899
theorem B2568665 : Blo 1711056 2568665 := bstep (se 2 (by rfl) ⟨963249, by rfl⟩ : syracuseStep 2568665 = 1926499) B1926499
theorem B2888203 : Blo 1711056 2888203 := bstep (se 1 (by rfl) ⟨2166152, by rfl⟩ : syracuseStep 2888203 = 4332305) B4332305
theorem B8663597 : Blo 1711056 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B2568779 : Blo 1711056 2568779 := bstep (se 1 (by rfl) ⟨1926584, by rfl⟩ : syracuseStep 2568779 = 3853169) B3853169
theorem B2568791 : Blo 1711056 2568791 := bstep (se 1 (by rfl) ⟨1926593, by rfl⟩ : syracuseStep 2568791 = 3853187) B3853187
theorem B7311961 : Blo 1711056 7311961 := bstep (se 2 (by rfl) ⟨2741985, by rfl⟩ : syracuseStep 7311961 = 5483971) B5483971
theorem B6255197 : Blo 1711056 6255197 := bstep (se 3 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 6255197 = 2345699) B2345699
theorem B2437771 : Blo 1711056 2437771 := bstep (se 1 (by rfl) ⟨1828328, by rfl⟩ : syracuseStep 2437771 = 3656657) B3656657
theorem B2888345 : Blo 1711056 2888345 := bstep (se 2 (by rfl) ⟨1083129, by rfl⟩ : syracuseStep 2888345 = 2166259) B2166259
theorem B2568857 : Blo 1711056 2568857 := bstep (se 2 (by rfl) ⟨963321, by rfl⟩ : syracuseStep 2568857 = 1926643) B1926643
theorem B3248819 : Blo 1711056 3248819 := bstep (se 1 (by rfl) ⟨2436614, by rfl⟩ : syracuseStep 3248819 = 4873229) B4873229
theorem B2167499 : Blo 1711056 2167499 := bstep (se 1 (by rfl) ⟨1625624, by rfl⟩ : syracuseStep 2167499 = 3251249) B3251249
theorem B4625113 : Blo 1711056 4625113 := bstep (se 2 (by rfl) ⟨1734417, by rfl⟩ : syracuseStep 4625113 = 3468835) B3468835
theorem B2568971 : Blo 1711056 2568971 := bstep (se 1 (by rfl) ⟨1926728, by rfl⟩ : syracuseStep 2568971 = 3853457) B3853457
theorem B2568983 : Blo 1711056 2568983 := bstep (se 1 (by rfl) ⟨1926737, by rfl⟩ : syracuseStep 2568983 = 3853475) B3853475
theorem B2888473 : Blo 1711056 2888473 := bstep (se 2 (by rfl) ⟨1083177, by rfl⟩ : syracuseStep 2888473 = 2166355) B2166355
theorem B6173491 : Blo 1711056 6173491 := bstep (se 1 (by rfl) ⟨4630118, by rfl⟩ : syracuseStep 6173491 = 9260237) B9260237
theorem B2569049 : Blo 1711056 2569049 := bstep (se 2 (by rfl) ⟨963393, by rfl⟩ : syracuseStep 2569049 = 1926787) B1926787
theorem B3249047 : Blo 1711056 3249047 := bstep (se 1 (by rfl) ⟨2436785, by rfl⟩ : syracuseStep 3249047 = 4873571) B4873571
theorem B5780375 : Blo 1711056 5780375 := bstep (se 1 (by rfl) ⟨4335281, by rfl⟩ : syracuseStep 5780375 = 8670563) B8670563
theorem B2569163 : Blo 1711056 2569163 := bstep (se 1 (by rfl) ⟨1926872, by rfl⟩ : syracuseStep 2569163 = 3853745) B3853745
theorem B2569175 : Blo 1711056 2569175 := bstep (se 1 (by rfl) ⟨1926881, by rfl⟩ : syracuseStep 2569175 = 3853763) B3853763
theorem B2569241 : Blo 1711056 2569241 := bstep (se 2 (by rfl) ⟨963465, by rfl⟩ : syracuseStep 2569241 = 1926931) B1926931
theorem B3085427 : Blo 1711056 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B2569355 : Blo 1711056 2569355 := bstep (se 1 (by rfl) ⟨1927016, by rfl⟩ : syracuseStep 2569355 = 3854033) B3854033
theorem B2569367 : Blo 1711056 2569367 := bstep (se 1 (by rfl) ⟨1927025, by rfl⟩ : syracuseStep 2569367 = 3854051) B3854051
theorem B3249305 : Blo 1711056 3249305 := bstep (se 2 (by rfl) ⟨1218489, by rfl⟩ : syracuseStep 3249305 = 2436979) B2436979
theorem B6943961 : Blo 1711056 6943961 := bstep (se 2 (by rfl) ⟨2603985, by rfl⟩ : syracuseStep 6943961 = 5207971) B5207971
theorem B2569433 : Blo 1711056 2569433 := bstep (se 2 (by rfl) ⟨963537, by rfl⟩ : syracuseStep 2569433 = 1927075) B1927075
theorem B2929945 : Blo 1711056 2929945 := bstep (se 2 (by rfl) ⟨1098729, by rfl⟩ : syracuseStep 2929945 = 2197459) B2197459
theorem B2569547 : Blo 1711056 2569547 := bstep (se 1 (by rfl) ⟨1927160, by rfl⟩ : syracuseStep 2569547 = 3854321) B3854321
theorem B2889047 : Blo 1711056 2889047 := bstep (se 1 (by rfl) ⟨2166785, by rfl⟩ : syracuseStep 2889047 = 4333571) B4333571
theorem B2569559 : Blo 1711056 2569559 := bstep (se 1 (by rfl) ⟨1927169, by rfl⟩ : syracuseStep 2569559 = 3854339) B3854339
theorem B5854643 : Blo 1711056 5854643 := bstep (se 1 (by rfl) ⟨4390982, by rfl⟩ : syracuseStep 5854643 = 8781965) B8781965
theorem B18519475 : Blo 1711056 18519475 := bstep (se 1 (by rfl) ⟨13889606, by rfl⟩ : syracuseStep 18519475 = 27779213) B27779213
theorem B5780915 : Blo 1711056 5780915 := bstep (se 1 (by rfl) ⟨4335686, by rfl⟩ : syracuseStep 5780915 = 8671373) B8671373
theorem B2889175 : Blo 1711056 2889175 := bstep (se 1 (by rfl) ⟨2166881, by rfl⟩ : syracuseStep 2889175 = 4333763) B4333763
theorem B6944221 : Blo 1711056 6944221 := bstep (se 3 (by rfl) ⟨1302041, by rfl⟩ : syracuseStep 6944221 = 2604083) B2604083
theorem B3249715 : Blo 1711056 3249715 := bstep (se 1 (by rfl) ⟨2437286, by rfl⟩ : syracuseStep 3249715 = 4874573) B4874573
theorem B166581845 : Blo 1711056 166581845 := bstep (se 8 (by rfl) ⟨976065, by rfl⟩ : syracuseStep 166581845 = 1952131) B1952131
theorem B14620337 : Blo 1711056 14620337 := bstep (se 2 (by rfl) ⟨5482626, by rfl⟩ : syracuseStep 14620337 = 10965253) B10965253
theorem B5781185 : Blo 1711056 5781185 := bstep (se 2 (by rfl) ⟨2167944, by rfl⟩ : syracuseStep 5781185 = 4335889) B4335889
theorem B27768581 : Blo 1711056 27768581 := bstep (se 4 (by rfl) ⟨2603304, by rfl⟩ : syracuseStep 27768581 = 5206609) B5206609
theorem B5854999 : Blo 1711056 5854999 := bstep (se 1 (by rfl) ⟨4391249, by rfl⟩ : syracuseStep 5854999 = 8782499) B8782499
theorem B4331353 : Blo 1711056 4331353 := bstep (se 2 (by rfl) ⟨1624257, by rfl⟩ : syracuseStep 4331353 = 3248515) B3248515
theorem B2439001 : Blo 1711056 2439001 := bstep (se 2 (by rfl) ⟨914625, by rfl⟩ : syracuseStep 2439001 = 1829251) B1829251
theorem B3250201 : Blo 1711056 3250201 := bstep (se 2 (by rfl) ⟨1218825, by rfl⟩ : syracuseStep 3250201 = 2437651) B2437651
theorem B4626497 : Blo 1711056 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B2889803 : Blo 1711056 2889803 := bstep (se 1 (by rfl) ⟨2167352, by rfl⟩ : syracuseStep 2889803 = 4334705) B4334705
theorem B3086515 : Blo 1711056 3086515 := bstep (se 1 (by rfl) ⟨2314886, by rfl⟩ : syracuseStep 3086515 = 4629773) B4629773
theorem B7035083 : Blo 1711056 7035083 := bstep (se 1 (by rfl) ⟨5276312, by rfl⟩ : syracuseStep 7035083 = 10552625) B10552625
theorem B2889931 : Blo 1711056 2889931 := bstep (se 1 (by rfl) ⟨2167448, by rfl⟩ : syracuseStep 2889931 = 4334897) B4334897
theorem B3471641 : Blo 1711056 3471641 := bstep (se 2 (by rfl) ⟨1301865, by rfl⟩ : syracuseStep 3471641 = 2603731) B2603731
theorem B29636909 : Blo 1711056 29636909 := bstep (se 3 (by rfl) ⟨5556920, by rfl⟩ : syracuseStep 29636909 = 11113841) B11113841
theorem B2890073 : Blo 1711056 2890073 := bstep (se 2 (by rfl) ⟨1083777, by rfl⟩ : syracuseStep 2890073 = 2167555) B2167555
theorem B6502787 : Blo 1711056 6502787 := bstep (se 1 (by rfl) ⟨4877090, by rfl⟩ : syracuseStep 6502787 = 9754181) B9754181
theorem B6502801 : Blo 1711056 6502801 := bstep (se 2 (by rfl) ⟨2438550, by rfl⟩ : syracuseStep 6502801 = 4877101) B4877101
theorem B2890201 : Blo 1711056 2890201 := bstep (se 2 (by rfl) ⟨1083825, by rfl⟩ : syracuseStep 2890201 = 2167651) B2167651
theorem B4872727 : Blo 1711056 4872727 := bstep (se 1 (by rfl) ⟨3654545, by rfl⟩ : syracuseStep 4872727 = 7309091) B7309091
theorem B3250763 : Blo 1711056 3250763 := bstep (se 1 (by rfl) ⟨2438072, by rfl⟩ : syracuseStep 3250763 = 4876145) B4876145
theorem B8223383 : Blo 1711056 8223383 := bstep (se 1 (by rfl) ⟨6167537, by rfl⟩ : syracuseStep 8223383 = 12335075) B12335075
theorem B6503105 : Blo 1711056 6503105 := bstep (se 2 (by rfl) ⟨2438664, by rfl⟩ : syracuseStep 6503105 = 4877329) B4877329
theorem B5208797 : Blo 1711056 5208797 := bstep (se 3 (by rfl) ⟨976649, by rfl⟩ : syracuseStep 5208797 = 1953299) B1953299
theorem B3250945 : Blo 1711056 3250945 := bstep (se 2 (by rfl) ⟨1219104, by rfl⟩ : syracuseStep 3250945 = 2438209) B2438209
theorem B14629733 : Blo 1711056 14629733 := bstep (se 4 (by rfl) ⟨1371537, by rfl⟩ : syracuseStep 14629733 = 2743075) B2743075
theorem B4332467 : Blo 1711056 4332467 := bstep (se 1 (by rfl) ⟨3249350, by rfl⟩ : syracuseStep 4332467 = 6498701) B6498701
theorem B7805899 : Blo 1711056 7805899 := bstep (se 1 (by rfl) ⟨5854424, by rfl⟩ : syracuseStep 7805899 = 11708849) B11708849
theorem B1711063 : Blo 1711056 1711063 := bstep (se 1 (by rfl) ⟨1283297, by rfl⟩ : syracuseStep 1711063 = 2566595) B2566595
theorem B83311577 : Blo 1711056 83311577 := bstep (se 2 (by rfl) ⟨31241841, by rfl⟩ : syracuseStep 83311577 = 62483683) B62483683
theorem B1711083 : Blo 1711056 1711083 := bstep (se 1 (by rfl) ⟨1283312, by rfl⟩ : syracuseStep 1711083 = 2566625) B2566625
theorem B1711095 : Blo 1711056 1711095 := bstep (se 1 (by rfl) ⟨1283321, by rfl⟩ : syracuseStep 1711095 = 2566643) B2566643
theorem B1711115 : Blo 1711056 1711115 := bstep (se 1 (by rfl) ⟨1283336, by rfl⟩ : syracuseStep 1711115 = 2566673) B2566673
theorem B1711127 : Blo 1711056 1711127 := bstep (se 1 (by rfl) ⟨1283345, by rfl⟩ : syracuseStep 1711127 = 2566691) B2566691
theorem B2890775 : Blo 1711056 2890775 := bstep (se 1 (by rfl) ⟨2168081, by rfl⟩ : syracuseStep 2890775 = 4336163) B4336163
theorem B1711147 : Blo 1711056 1711147 := bstep (se 1 (by rfl) ⟨1283360, by rfl⟩ : syracuseStep 1711147 = 2566721) B2566721
theorem B1711159 : Blo 1711056 1711159 := bstep (se 1 (by rfl) ⟨1283369, by rfl⟩ : syracuseStep 1711159 = 2566739) B2566739
theorem B1711179 : Blo 1711056 1711179 := bstep (se 1 (by rfl) ⟨1283384, by rfl⟩ : syracuseStep 1711179 = 2566769) B2566769
theorem B1711191 : Blo 1711056 1711191 := bstep (se 1 (by rfl) ⟨1283393, by rfl⟩ : syracuseStep 1711191 = 2566787) B2566787
theorem B19512413 : Blo 1711056 19512413 := bstep (se 3 (by rfl) ⟨3658577, by rfl⟩ : syracuseStep 19512413 = 7317155) B7317155
theorem B1711211 : Blo 1711056 1711211 := bstep (se 1 (by rfl) ⟨1283408, by rfl⟩ : syracuseStep 1711211 = 2566817) B2566817
theorem B1711223 : Blo 1711056 1711223 := bstep (se 1 (by rfl) ⟨1283417, by rfl⟩ : syracuseStep 1711223 = 2566835) B2566835
theorem B1711243 : Blo 1711056 1711243 := bstep (se 1 (by rfl) ⟨1283432, by rfl⟩ : syracuseStep 1711243 = 2566865) B2566865
theorem B1711255 : Blo 1711056 1711255 := bstep (se 1 (by rfl) ⟨1283441, by rfl⟩ : syracuseStep 1711255 = 2566883) B2566883
theorem B12344471 : Blo 1711056 12344471 := bstep (se 1 (by rfl) ⟨9258353, by rfl⟩ : syracuseStep 12344471 = 18516707) B18516707
theorem B1711275 : Blo 1711056 1711275 := bstep (se 1 (by rfl) ⟨1283456, by rfl⟩ : syracuseStep 1711275 = 2566913) B2566913
theorem B1711287 : Blo 1711056 1711287 := bstep (se 1 (by rfl) ⟨1283465, by rfl⟩ : syracuseStep 1711287 = 2566931) B2566931
theorem B1711307 : Blo 1711056 1711307 := bstep (se 1 (by rfl) ⟨1283480, by rfl⟩ : syracuseStep 1711307 = 2566961) B2566961
theorem B18521293 : Blo 1711056 18521293 := bstep (se 3 (by rfl) ⟨3472742, by rfl⟩ : syracuseStep 18521293 = 6945485) B6945485
theorem B1711319 : Blo 1711056 1711319 := bstep (se 1 (by rfl) ⟨1283489, by rfl⟩ : syracuseStep 1711319 = 2566979) B2566979
theorem B4332761 : Blo 1711056 4332761 := bstep (se 2 (by rfl) ⟨1624785, by rfl⟩ : syracuseStep 4332761 = 3249571) B3249571
theorem B1711339 : Blo 1711056 1711339 := bstep (se 1 (by rfl) ⟨1283504, by rfl⟩ : syracuseStep 1711339 = 2567009) B2567009
theorem B1711351 : Blo 1711056 1711351 := bstep (se 1 (by rfl) ⟨1283513, by rfl⟩ : syracuseStep 1711351 = 2567027) B2567027
theorem B1711371 : Blo 1711056 1711371 := bstep (se 1 (by rfl) ⟨1283528, by rfl⟩ : syracuseStep 1711371 = 2567057) B2567057
theorem B1711383 : Blo 1711056 1711383 := bstep (se 1 (by rfl) ⟨1283537, by rfl⟩ : syracuseStep 1711383 = 2567075) B2567075
theorem B1711403 : Blo 1711056 1711403 := bstep (se 1 (by rfl) ⟨1283552, by rfl⟩ : syracuseStep 1711403 = 2567105) B2567105
theorem B1711415 : Blo 1711056 1711415 := bstep (se 1 (by rfl) ⟨1283561, by rfl⟩ : syracuseStep 1711415 = 2567123) B2567123
theorem B4873547 : Blo 1711056 4873547 := bstep (se 1 (by rfl) ⟨3655160, by rfl⟩ : syracuseStep 4873547 = 7310321) B7310321
theorem B1711435 : Blo 1711056 1711435 := bstep (se 1 (by rfl) ⟨1283576, by rfl⟩ : syracuseStep 1711435 = 2567153) B2567153
theorem B1711447 : Blo 1711056 1711447 := bstep (se 1 (by rfl) ⟨1283585, by rfl⟩ : syracuseStep 1711447 = 2567171) B2567171
theorem B6503773 : Blo 1711056 6503773 := bstep (se 3 (by rfl) ⟨1219457, by rfl⟩ : syracuseStep 6503773 = 2438915) B2438915
theorem B1711467 : Blo 1711056 1711467 := bstep (se 1 (by rfl) ⟨1283600, by rfl⟩ : syracuseStep 1711467 = 2567201) B2567201
theorem B1711479 : Blo 1711056 1711479 := bstep (se 1 (by rfl) ⟨1283609, by rfl⟩ : syracuseStep 1711479 = 2567219) B2567219
theorem B1711499 : Blo 1711056 1711499 := bstep (se 1 (by rfl) ⟨1283624, by rfl⟩ : syracuseStep 1711499 = 2567249) B2567249
theorem B1711511 : Blo 1711056 1711511 := bstep (se 1 (by rfl) ⟨1283633, by rfl⟩ : syracuseStep 1711511 = 2567267) B2567267
theorem B1711531 : Blo 1711056 1711531 := bstep (se 1 (by rfl) ⟨1283648, by rfl⟩ : syracuseStep 1711531 = 2567297) B2567297
theorem B1711543 : Blo 1711056 1711543 := bstep (se 1 (by rfl) ⟨1283657, by rfl⟩ : syracuseStep 1711543 = 2567315) B2567315
theorem B1711563 : Blo 1711056 1711563 := bstep (se 1 (by rfl) ⟨1283672, by rfl⟩ : syracuseStep 1711563 = 2567345) B2567345
theorem B3251659 : Blo 1711056 3251659 := bstep (se 1 (by rfl) ⟨2438744, by rfl⟩ : syracuseStep 3251659 = 4877489) B4877489
theorem B1711575 : Blo 1711056 1711575 := bstep (se 1 (by rfl) ⟨1283681, by rfl⟩ : syracuseStep 1711575 = 2567363) B2567363
theorem B1711595 : Blo 1711056 1711595 := bstep (se 1 (by rfl) ⟨1283696, by rfl⟩ : syracuseStep 1711595 = 2567393) B2567393
theorem B1711607 : Blo 1711056 1711607 := bstep (se 1 (by rfl) ⟨1283705, by rfl⟩ : syracuseStep 1711607 = 2567411) B2567411
theorem B1711627 : Blo 1711056 1711627 := bstep (se 1 (by rfl) ⟨1283720, by rfl⟩ : syracuseStep 1711627 = 2567441) B2567441
theorem B1711639 : Blo 1711056 1711639 := bstep (se 1 (by rfl) ⟨1283729, by rfl⟩ : syracuseStep 1711639 = 2567459) B2567459
theorem B3251735 : Blo 1711056 3251735 := bstep (se 1 (by rfl) ⟨2438801, by rfl⟩ : syracuseStep 3251735 = 4877603) B4877603
theorem B2743831 : Blo 1711056 2743831 := bstep (se 1 (by rfl) ⟨2057873, by rfl⟩ : syracuseStep 2743831 = 4115747) B4115747
theorem B1711659 : Blo 1711056 1711659 := bstep (se 1 (by rfl) ⟨1283744, by rfl⟩ : syracuseStep 1711659 = 2567489) B2567489
theorem B1711671 : Blo 1711056 1711671 := bstep (se 1 (by rfl) ⟨1283753, by rfl⟩ : syracuseStep 1711671 = 2567507) B2567507
theorem B1711691 : Blo 1711056 1711691 := bstep (se 1 (by rfl) ⟨1283768, by rfl⟩ : syracuseStep 1711691 = 2567537) B2567537
theorem B1711703 : Blo 1711056 1711703 := bstep (se 1 (by rfl) ⟨1283777, by rfl⟩ : syracuseStep 1711703 = 2567555) B2567555
theorem B1711723 : Blo 1711056 1711723 := bstep (se 1 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 1711723 = 2567585) B2567585
theorem B1711735 : Blo 1711056 1711735 := bstep (se 1 (by rfl) ⟨1283801, by rfl⟩ : syracuseStep 1711735 = 2567603) B2567603
theorem B1711755 : Blo 1711056 1711755 := bstep (se 1 (by rfl) ⟨1283816, by rfl⟩ : syracuseStep 1711755 = 2567633) B2567633
theorem B1711767 : Blo 1711056 1711767 := bstep (se 1 (by rfl) ⟨1283825, by rfl⟩ : syracuseStep 1711767 = 2567651) B2567651
theorem B1711787 : Blo 1711056 1711787 := bstep (se 1 (by rfl) ⟨1283840, by rfl⟩ : syracuseStep 1711787 = 2567681) B2567681
theorem B1711799 : Blo 1711056 1711799 := bstep (se 1 (by rfl) ⟨1283849, by rfl⟩ : syracuseStep 1711799 = 2567699) B2567699
theorem B1711819 : Blo 1711056 1711819 := bstep (se 1 (by rfl) ⟨1283864, by rfl⟩ : syracuseStep 1711819 = 2567729) B2567729
theorem B1711831 : Blo 1711056 1711831 := bstep (se 1 (by rfl) ⟨1283873, by rfl⟩ : syracuseStep 1711831 = 2567747) B2567747
theorem B1711851 : Blo 1711056 1711851 := bstep (se 1 (by rfl) ⟨1283888, by rfl⟩ : syracuseStep 1711851 = 2567777) B2567777
theorem B1711863 : Blo 1711056 1711863 := bstep (se 1 (by rfl) ⟨1283897, by rfl⟩ : syracuseStep 1711863 = 2567795) B2567795
theorem B2055947 : Blo 1711056 2055947 := bstep (se 1 (by rfl) ⟨1541960, by rfl⟩ : syracuseStep 2055947 = 3083921) B3083921
theorem B1711883 : Blo 1711056 1711883 := bstep (se 1 (by rfl) ⟨1283912, by rfl⟩ : syracuseStep 1711883 = 2567825) B2567825
theorem B1711895 : Blo 1711056 1711895 := bstep (se 1 (by rfl) ⟨1283921, by rfl⟩ : syracuseStep 1711895 = 2567843) B2567843
theorem B1711915 : Blo 1711056 1711915 := bstep (se 1 (by rfl) ⟨1283936, by rfl⟩ : syracuseStep 1711915 = 2567873) B2567873
theorem B1711927 : Blo 1711056 1711927 := bstep (se 1 (by rfl) ⟨1283945, by rfl⟩ : syracuseStep 1711927 = 2567891) B2567891
theorem B1711947 : Blo 1711056 1711947 := bstep (se 1 (by rfl) ⟨1283960, by rfl⟩ : syracuseStep 1711947 = 2567921) B2567921
theorem B1924951 : Blo 1711056 1924951 := bstep (se 1 (by rfl) ⟨1443713, by rfl⟩ : syracuseStep 1924951 = 2887427) B2887427
theorem B3850073 : Blo 1711056 3850073 := bstep (se 2 (by rfl) ⟨1443777, by rfl⟩ : syracuseStep 3850073 = 2887555) B2887555
theorem B1711959 : Blo 1711056 1711959 := bstep (se 1 (by rfl) ⟨1283969, by rfl⟩ : syracuseStep 1711959 = 2567939) B2567939
theorem B1711979 : Blo 1711056 1711979 := bstep (se 1 (by rfl) ⟨1283984, by rfl⟩ : syracuseStep 1711979 = 2567969) B2567969
theorem B1711991 : Blo 1711056 1711991 := bstep (se 1 (by rfl) ⟨1283993, by rfl⟩ : syracuseStep 1711991 = 2567987) B2567987
theorem B1712011 : Blo 1711056 1712011 := bstep (se 1 (by rfl) ⟨1284008, by rfl⟩ : syracuseStep 1712011 = 2568017) B2568017
theorem B4112279 : Blo 1711056 4112279 := bstep (se 1 (by rfl) ⟨3084209, by rfl⟩ : syracuseStep 4112279 = 6168419) B6168419
theorem B1712023 : Blo 1711056 1712023 := bstep (se 1 (by rfl) ⟨1284017, by rfl⟩ : syracuseStep 1712023 = 2568035) B2568035
theorem B1712043 : Blo 1711056 1712043 := bstep (se 1 (by rfl) ⟨1284032, by rfl⟩ : syracuseStep 1712043 = 2568065) B2568065
theorem B3850163 : Blo 1711056 3850163 := bstep (se 1 (by rfl) ⟨2887622, by rfl⟩ : syracuseStep 3850163 = 5775245) B5775245
theorem B7315379 : Blo 1711056 7315379 := bstep (se 1 (by rfl) ⟨5486534, by rfl⟩ : syracuseStep 7315379 = 10973069) B10973069
theorem B1712055 : Blo 1711056 1712055 := bstep (se 1 (by rfl) ⟨1284041, by rfl⟩ : syracuseStep 1712055 = 2568083) B2568083
theorem B1712075 : Blo 1711056 1712075 := bstep (se 1 (by rfl) ⟨1284056, by rfl⟩ : syracuseStep 1712075 = 2568113) B2568113
theorem B3850199 : Blo 1711056 3850199 := bstep (se 1 (by rfl) ⟨2887649, by rfl⟩ : syracuseStep 3850199 = 5775299) B5775299
theorem B1712087 : Blo 1711056 1712087 := bstep (se 1 (by rfl) ⟨1284065, by rfl⟩ : syracuseStep 1712087 = 2568131) B2568131
theorem B1712107 : Blo 1711056 1712107 := bstep (se 1 (by rfl) ⟨1284080, by rfl⟩ : syracuseStep 1712107 = 2568161) B2568161
theorem B1712135 : Blo 1711056 1712135 := bstep (se 1 (by rfl) ⟨1284101, by rfl⟩ : syracuseStep 1712135 = 2568203) B2568203
theorem B1712143 : Blo 1711056 1712143 := bstep (se 1 (by rfl) ⟨1284107, by rfl⟩ : syracuseStep 1712143 = 2568215) B2568215
theorem B4333601 : Blo 1711056 4333601 := bstep (se 2 (by rfl) ⟨1625100, by rfl⟩ : syracuseStep 4333601 = 3250201) B3250201
theorem B1712187 : Blo 1711056 1712187 := bstep (se 1 (by rfl) ⟨1284140, by rfl⟩ : syracuseStep 1712187 = 2568281) B2568281
theorem B5857367 : Blo 1711056 5857367 := bstep (se 1 (by rfl) ⟨4393025, by rfl⟩ : syracuseStep 5857367 = 8786051) B8786051
theorem B1712263 : Blo 1711056 1712263 := bstep (se 1 (by rfl) ⟨1284197, by rfl⟩ : syracuseStep 1712263 = 2568395) B2568395
theorem B1712271 : Blo 1711056 1712271 := bstep (se 1 (by rfl) ⟨1284203, by rfl⟩ : syracuseStep 1712271 = 2568407) B2568407
theorem B26345645 : Blo 1711056 26345645 := bstep (se 3 (by rfl) ⟨4939808, by rfl⟩ : syracuseStep 26345645 = 9879617) B9879617
theorem B1712315 : Blo 1711056 1712315 := bstep (se 1 (by rfl) ⟨1284236, by rfl⟩ : syracuseStep 1712315 = 2568473) B2568473
theorem B1925383 : Blo 1711056 1925383 := bstep (se 1 (by rfl) ⟨1444037, by rfl⟩ : syracuseStep 1925383 = 2888075) B2888075
theorem B1712391 : Blo 1711056 1712391 := bstep (se 1 (by rfl) ⟨1284293, by rfl⟩ : syracuseStep 1712391 = 2568587) B2568587
theorem B1712399 : Blo 1711056 1712399 := bstep (se 1 (by rfl) ⟨1284299, by rfl⟩ : syracuseStep 1712399 = 2568599) B2568599
theorem B4874539 : Blo 1711056 4874539 := bstep (se 1 (by rfl) ⟨3655904, by rfl⟩ : syracuseStep 4874539 = 7311809) B7311809
theorem B1712443 : Blo 1711056 1712443 := bstep (se 1 (by rfl) ⟨1284332, by rfl⟩ : syracuseStep 1712443 = 2568665) B2568665
theorem B5775731 : Blo 1711056 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B3850631 : Blo 1711056 3850631 := bstep (se 1 (by rfl) ⟨2887973, by rfl⟩ : syracuseStep 3850631 = 5775947) B5775947
theorem B1712519 : Blo 1711056 1712519 := bstep (se 1 (by rfl) ⟨1284389, by rfl⟩ : syracuseStep 1712519 = 2568779) B2568779
theorem B1712527 : Blo 1711056 1712527 := bstep (se 1 (by rfl) ⟨1284395, by rfl⟩ : syracuseStep 1712527 = 2568791) B2568791
theorem B8225171 : Blo 1711056 8225171 := bstep (se 1 (by rfl) ⟨6168878, by rfl⟩ : syracuseStep 8225171 = 12337757) B12337757
theorem B4170131 : Blo 1711056 4170131 := bstep (se 1 (by rfl) ⟨3127598, by rfl⟩ : syracuseStep 4170131 = 6255197) B6255197
theorem B1925563 : Blo 1711056 1925563 := bstep (se 1 (by rfl) ⟨1444172, by rfl⟩ : syracuseStep 1925563 = 2888345) B2888345
theorem B1712571 : Blo 1711056 1712571 := bstep (se 1 (by rfl) ⟨1284428, by rfl⟩ : syracuseStep 1712571 = 2568857) B2568857
theorem B1712647 : Blo 1711056 1712647 := bstep (se 1 (by rfl) ⟨1284485, by rfl⟩ : syracuseStep 1712647 = 2568971) B2568971
theorem B1712655 : Blo 1711056 1712655 := bstep (se 1 (by rfl) ⟨1284491, by rfl⟩ : syracuseStep 1712655 = 2568983) B2568983
theorem B3850811 : Blo 1711056 3850811 := bstep (se 1 (by rfl) ⟨2888108, by rfl⟩ : syracuseStep 3850811 = 5776217) B5776217
theorem B1712699 : Blo 1711056 1712699 := bstep (se 1 (by rfl) ⟨1284524, by rfl⟩ : syracuseStep 1712699 = 2569049) B2569049
theorem B6251069 : Blo 1711056 6251069 := bstep (se 3 (by rfl) ⟨1172075, by rfl⟩ : syracuseStep 6251069 = 2344151) B2344151
theorem B4874813 : Blo 1711056 4874813 := bstep (se 3 (by rfl) ⟨914027, by rfl⟩ : syracuseStep 4874813 = 1828055) B1828055
theorem B1712775 : Blo 1711056 1712775 := bstep (se 1 (by rfl) ⟨1284581, by rfl⟩ : syracuseStep 1712775 = 2569163) B2569163
theorem B1712783 : Blo 1711056 1712783 := bstep (se 1 (by rfl) ⟨1284587, by rfl⟩ : syracuseStep 1712783 = 2569175) B2569175
theorem B3850937 : Blo 1711056 3850937 := bstep (se 2 (by rfl) ⟨1444101, by rfl⟩ : syracuseStep 3850937 = 2888203) B2888203
theorem B1712827 : Blo 1711056 1712827 := bstep (se 1 (by rfl) ⟨1284620, by rfl⟩ : syracuseStep 1712827 = 2569241) B2569241
theorem B6496969 : Blo 1711056 6496969 := bstep (se 2 (by rfl) ⟨2436363, by rfl⟩ : syracuseStep 6496969 = 4872727) B4872727
theorem B2056951 : Blo 1711056 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B1712903 : Blo 1711056 1712903 := bstep (se 1 (by rfl) ⟨1284677, by rfl⟩ : syracuseStep 1712903 = 2569355) B2569355
theorem B1712911 : Blo 1711056 1712911 := bstep (se 1 (by rfl) ⟨1284683, by rfl⟩ : syracuseStep 1712911 = 2569367) B2569367
theorem B9749281 : Blo 1711056 9749281 := bstep (se 2 (by rfl) ⟨3655980, by rfl⟩ : syracuseStep 9749281 = 7311961) B7311961
theorem B3654443 : Blo 1711056 3654443 := bstep (se 1 (by rfl) ⟨2740832, by rfl⟩ : syracuseStep 3654443 = 5481665) B5481665
theorem B4629307 : Blo 1711056 4629307 := bstep (se 1 (by rfl) ⟨3471980, by rfl⟩ : syracuseStep 4629307 = 6943961) B6943961
theorem B1712955 : Blo 1711056 1712955 := bstep (se 1 (by rfl) ⟨1284716, by rfl⟩ : syracuseStep 1712955 = 2569433) B2569433
theorem B4113287 : Blo 1711056 4113287 := bstep (se 1 (by rfl) ⟨3084965, by rfl⟩ : syracuseStep 4113287 = 6169931) B6169931
theorem B1713031 : Blo 1711056 1713031 := bstep (se 1 (by rfl) ⟨1284773, by rfl⟩ : syracuseStep 1713031 = 2569547) B2569547
theorem B1926031 : Blo 1711056 1926031 := bstep (se 1 (by rfl) ⟨1444523, by rfl⟩ : syracuseStep 1926031 = 2889047) B2889047
theorem B1713039 : Blo 1711056 1713039 := bstep (se 1 (by rfl) ⟨1284779, by rfl⟩ : syracuseStep 1713039 = 2569559) B2569559
theorem B4334593 : Blo 1711056 4334593 := bstep (se 2 (by rfl) ⟨1625472, by rfl⟩ : syracuseStep 4334593 = 3250945) B3250945
theorem B8225803 : Blo 1711056 8225803 := bstep (se 1 (by rfl) ⟨6169352, by rfl⟩ : syracuseStep 8225803 = 12338705) B12338705
theorem B3851279 : Blo 1711056 3851279 := bstep (se 1 (by rfl) ⟨2888459, by rfl⟩ : syracuseStep 3851279 = 5776919) B5776919
theorem B3851297 : Blo 1711056 3851297 := bstep (se 2 (by rfl) ⟨1444236, by rfl⟩ : syracuseStep 3851297 = 2888473) B2888473
theorem B6587459 : Blo 1711056 6587459 := bstep (se 1 (by rfl) ⟨4940594, by rfl⟩ : syracuseStep 6587459 = 9881189) B9881189
theorem B3851639 : Blo 1711056 3851639 := bstep (se 1 (by rfl) ⟨2888729, by rfl⟩ : syracuseStep 3851639 = 5777459) B5777459
theorem B1926535 : Blo 1711056 1926535 := bstep (se 1 (by rfl) ⟨1444901, by rfl⟩ : syracuseStep 1926535 = 2889803) B2889803
theorem B8668619 : Blo 1711056 8668619 := bstep (se 1 (by rfl) ⟨6501464, by rfl⟩ : syracuseStep 8668619 = 13002929) B13002929
theorem B9881099 : Blo 1711056 9881099 := bstep (se 1 (by rfl) ⟨7410824, by rfl⟩ : syracuseStep 9881099 = 14821649) B14821649
theorem B3851819 : Blo 1711056 3851819 := bstep (se 1 (by rfl) ⟨2888864, by rfl⟩ : syracuseStep 3851819 = 5777729) B5777729
theorem B1926715 : Blo 1711056 1926715 := bstep (se 1 (by rfl) ⟨1445036, by rfl⟩ : syracuseStep 1926715 = 2890073) B2890073
theorem B14624333 : Blo 1711056 14624333 := bstep (se 3 (by rfl) ⟨2742062, by rfl⟩ : syracuseStep 14624333 = 5484125) B5484125
theorem B4335191 : Blo 1711056 4335191 := bstep (se 1 (by rfl) ⟨3251393, by rfl⟩ : syracuseStep 4335191 = 6502787) B6502787
theorem B4114055 : Blo 1711056 4114055 := bstep (se 1 (by rfl) ⟨3085541, by rfl⟩ : syracuseStep 4114055 = 6171083) B6171083
theorem B5482255 : Blo 1711056 5482255 := bstep (se 1 (by rfl) ⟨4111691, by rfl⟩ : syracuseStep 5482255 = 8223383) B8223383
theorem B8668943 : Blo 1711056 8668943 := bstep (se 1 (by rfl) ⟨6501707, by rfl⟩ : syracuseStep 8668943 = 13003415) B13003415
theorem B4335403 : Blo 1711056 4335403 := bstep (se 1 (by rfl) ⟨3251552, by rfl⟩ : syracuseStep 4335403 = 6503105) B6503105
theorem B3852179 : Blo 1711056 3852179 := bstep (se 1 (by rfl) ⟨2889134, by rfl⟩ : syracuseStep 3852179 = 5778269) B5778269
theorem B24692633 : Blo 1711056 24692633 := bstep (se 2 (by rfl) ⟨9259737, by rfl⟩ : syracuseStep 24692633 = 18519475) B18519475
theorem B4335545 : Blo 1711056 4335545 := bstep (se 2 (by rfl) ⟨1625829, by rfl⟩ : syracuseStep 4335545 = 3251659) B3251659
theorem B3852233 : Blo 1711056 3852233 := bstep (se 2 (by rfl) ⟨1444587, by rfl⟩ : syracuseStep 3852233 = 2889175) B2889175
theorem B9258961 : Blo 1711056 9258961 := bstep (se 2 (by rfl) ⟨3472110, by rfl⟩ : syracuseStep 9258961 = 6944221) B6944221
theorem B1927183 : Blo 1711056 1927183 := bstep (se 1 (by rfl) ⟨1445387, by rfl⟩ : syracuseStep 1927183 = 2890775) B2890775
theorem B5482525 : Blo 1711056 5482525 := bstep (se 3 (by rfl) ⟨1027973, by rfl⟩ : syracuseStep 5482525 = 2055947) B2055947
theorem B9750557 : Blo 1711056 9750557 := bstep (se 3 (by rfl) ⟨1828229, by rfl⟩ : syracuseStep 9750557 = 3656459) B3656459
theorem B7309399 : Blo 1711056 7309399 := bstep (se 1 (by rfl) ⟨5482049, by rfl⟩ : syracuseStep 7309399 = 10964099) B10964099
theorem B4114747 : Blo 1711056 4114747 := bstep (se 1 (by rfl) ⟨3086060, by rfl⟩ : syracuseStep 4114747 = 6172121) B6172121
theorem B8907097 : Blo 1711056 8907097 := bstep (se 2 (by rfl) ⟨3340161, by rfl⟩ : syracuseStep 8907097 = 6680323) B6680323
theorem B8227187 : Blo 1711056 8227187 := bstep (se 1 (by rfl) ⟨6170390, by rfl⟩ : syracuseStep 8227187 = 12340781) B12340781
theorem B1853831 : Blo 1711056 1853831 := bstep (se 1 (by rfl) ⟨1390373, by rfl⟩ : syracuseStep 1853831 = 2780747) B2780747
theorem B4393363 : Blo 1711056 4393363 := bstep (se 1 (by rfl) ⟨3295022, by rfl⟩ : syracuseStep 4393363 = 6590045) B6590045
theorem B2566601 : Blo 1711056 2566601 := bstep (se 2 (by rfl) ⟨962475, by rfl⟩ : syracuseStep 2566601 = 1924951) B1924951
theorem B2566715 : Blo 1711056 2566715 := bstep (se 1 (by rfl) ⟨1925036, by rfl⟩ : syracuseStep 2566715 = 3850073) B3850073
theorem B2566775 : Blo 1711056 2566775 := bstep (se 1 (by rfl) ⟨1925081, by rfl⟩ : syracuseStep 2566775 = 3850163) B3850163
theorem B4876919 : Blo 1711056 4876919 := bstep (se 1 (by rfl) ⟨3657689, by rfl⟩ : syracuseStep 4876919 = 7315379) B7315379
theorem B3852935 : Blo 1711056 3852935 := bstep (se 1 (by rfl) ⟨2889701, by rfl⟩ : syracuseStep 3852935 = 5779403) B5779403
theorem B2566799 : Blo 1711056 2566799 := bstep (se 1 (by rfl) ⟨1925099, by rfl⟩ : syracuseStep 2566799 = 3850199) B3850199
theorem B20834995 : Blo 1711056 20834995 := bstep (se 1 (by rfl) ⟨15626246, by rfl⟩ : syracuseStep 20834995 = 31252493) B31252493
theorem B2566841 : Blo 1711056 2566841 := bstep (se 2 (by rfl) ⟨962565, by rfl⟩ : syracuseStep 2566841 = 1925131) B1925131
theorem B2566919 : Blo 1711056 2566919 := bstep (se 1 (by rfl) ⟨1925189, by rfl⟩ : syracuseStep 2566919 = 3850379) B3850379
theorem B2566955 : Blo 1711056 2566955 := bstep (se 1 (by rfl) ⟨1925216, by rfl⟩ : syracuseStep 2566955 = 3850433) B3850433
theorem B3853115 : Blo 1711056 3853115 := bstep (se 1 (by rfl) ⟨2889836, by rfl⟩ : syracuseStep 3853115 = 5779673) B5779673
theorem B2566985 : Blo 1711056 2566985 := bstep (se 2 (by rfl) ⟨962619, by rfl⟩ : syracuseStep 2566985 = 1925239) B1925239
theorem B6499187 : Blo 1711056 6499187 := bstep (se 1 (by rfl) ⟨4874390, by rfl⟩ : syracuseStep 6499187 = 9748781) B9748781
theorem B14830451 : Blo 1711056 14830451 := bstep (se 1 (by rfl) ⟨11122838, by rfl⟩ : syracuseStep 14830451 = 22245677) B22245677
theorem B5778323 : Blo 1711056 5778323 := bstep (se 1 (by rfl) ⟨4333742, by rfl⟩ : syracuseStep 5778323 = 8667485) B8667485
theorem B3853241 : Blo 1711056 3853241 := bstep (se 2 (by rfl) ⟨1444965, by rfl⟩ : syracuseStep 3853241 = 2889931) B2889931
theorem B2567099 : Blo 1711056 2567099 := bstep (se 1 (by rfl) ⟨1925324, by rfl⟩ : syracuseStep 2567099 = 3850649) B3850649
theorem B2567159 : Blo 1711056 2567159 := bstep (se 1 (by rfl) ⟨1925369, by rfl⟩ : syracuseStep 2567159 = 3850739) B3850739
theorem B2567183 : Blo 1711056 2567183 := bstep (se 1 (by rfl) ⟨1925387, by rfl⟩ : syracuseStep 2567183 = 3850775) B3850775
theorem B2567225 : Blo 1711056 2567225 := bstep (se 2 (by rfl) ⟨962709, by rfl⟩ : syracuseStep 2567225 = 1925419) B1925419
theorem B5205053 : Blo 1711056 5205053 := bstep (se 3 (by rfl) ⟨975947, by rfl⟩ : syracuseStep 5205053 = 1951895) B1951895
theorem B39529559 : Blo 1711056 39529559 := bstep (se 1 (by rfl) ⟨29647169, by rfl⟩ : syracuseStep 39529559 = 59294339) B59294339
theorem B2165879 : Blo 1711056 2165879 := bstep (se 1 (by rfl) ⟨1624409, by rfl⟩ : syracuseStep 2165879 = 3248819) B3248819
theorem B2567303 : Blo 1711056 2567303 := bstep (se 1 (by rfl) ⟨1925477, by rfl⟩ : syracuseStep 2567303 = 3850955) B3850955
theorem B2567339 : Blo 1711056 2567339 := bstep (se 1 (by rfl) ⟨1925504, by rfl⟩ : syracuseStep 2567339 = 3851009) B3851009
theorem B8670401 : Blo 1711056 8670401 := bstep (se 2 (by rfl) ⟨3251400, by rfl⟩ : syracuseStep 8670401 = 6502801) B6502801
theorem B2567369 : Blo 1711056 2567369 := bstep (se 2 (by rfl) ⟨962763, by rfl⟩ : syracuseStep 2567369 = 1925527) B1925527
theorem B2166031 : Blo 1711056 2166031 := bstep (se 1 (by rfl) ⟨1624523, by rfl⟩ : syracuseStep 2166031 = 3249047) B3249047
theorem B3853583 : Blo 1711056 3853583 := bstep (se 1 (by rfl) ⟨2890187, by rfl⟩ : syracuseStep 3853583 = 5780375) B5780375
theorem B3853601 : Blo 1711056 3853601 := bstep (se 2 (by rfl) ⟨1445100, by rfl⟩ : syracuseStep 3853601 = 2890201) B2890201
theorem B2436409 : Blo 1711056 2436409 := bstep (se 2 (by rfl) ⟨913653, by rfl⟩ : syracuseStep 2436409 = 1827307) B1827307
theorem B2567483 : Blo 1711056 2567483 := bstep (se 1 (by rfl) ⟨1925612, by rfl⟩ : syracuseStep 2567483 = 3851225) B3851225
theorem B2567543 : Blo 1711056 2567543 := bstep (se 1 (by rfl) ⟨1925657, by rfl⟩ : syracuseStep 2567543 = 3851315) B3851315
theorem B2567567 : Blo 1711056 2567567 := bstep (se 1 (by rfl) ⟨1925675, by rfl⟩ : syracuseStep 2567567 = 3851351) B3851351
theorem B2567609 : Blo 1711056 2567609 := bstep (se 2 (by rfl) ⟨962853, by rfl⟩ : syracuseStep 2567609 = 1925707) B1925707
theorem B2166203 : Blo 1711056 2166203 := bstep (se 1 (by rfl) ⟨1624652, by rfl⟩ : syracuseStep 2166203 = 3249305) B3249305
theorem B2567687 : Blo 1711056 2567687 := bstep (se 1 (by rfl) ⟨1925765, by rfl⟩ : syracuseStep 2567687 = 3851531) B3851531
theorem B12996125 : Blo 1711056 12996125 := bstep (se 3 (by rfl) ⟨2436773, by rfl⟩ : syracuseStep 12996125 = 4873547) B4873547
theorem B2567723 : Blo 1711056 2567723 := bstep (se 1 (by rfl) ⟨1925792, by rfl⟩ : syracuseStep 2567723 = 3851585) B3851585
theorem B2567753 : Blo 1711056 2567753 := bstep (se 2 (by rfl) ⟨962907, by rfl⟩ : syracuseStep 2567753 = 1925815) B1925815
theorem B16461413 : Blo 1711056 16461413 := bstep (se 4 (by rfl) ⟨1543257, by rfl⟩ : syracuseStep 16461413 = 3086515) B3086515
theorem B3903095 : Blo 1711056 3903095 := bstep (se 1 (by rfl) ⟨2927321, by rfl⟩ : syracuseStep 3903095 = 5854643) B5854643
theorem B3853943 : Blo 1711056 3853943 := bstep (se 1 (by rfl) ⟨2890457, by rfl⟩ : syracuseStep 3853943 = 5780915) B5780915
theorem B2436751 : Blo 1711056 2436751 := bstep (se 1 (by rfl) ⟨1827563, by rfl⟩ : syracuseStep 2436751 = 3655127) B3655127
theorem B3706553 : Blo 1711056 3706553 := bstep (se 2 (by rfl) ⟨1389957, by rfl⟩ : syracuseStep 3706553 = 2779915) B2779915
theorem B2567867 : Blo 1711056 2567867 := bstep (se 1 (by rfl) ⟨1925900, by rfl⟩ : syracuseStep 2567867 = 3851801) B3851801
theorem B111054563 : Blo 1711056 111054563 := bstep (se 1 (by rfl) ⟨83290922, by rfl⟩ : syracuseStep 111054563 = 166581845) B166581845
theorem B2567927 : Blo 1711056 2567927 := bstep (se 1 (by rfl) ⟨1925945, by rfl⟩ : syracuseStep 2567927 = 3851891) B3851891
theorem B2567951 : Blo 1711056 2567951 := bstep (se 1 (by rfl) ⟨1925963, by rfl⟩ : syracuseStep 2567951 = 3851927) B3851927
theorem B3854123 : Blo 1711056 3854123 := bstep (se 1 (by rfl) ⟨2890592, by rfl⟩ : syracuseStep 3854123 = 5781185) B5781185
theorem B2567993 : Blo 1711056 2567993 := bstep (se 2 (by rfl) ⟨962997, by rfl⟩ : syracuseStep 2567993 = 1925995) B1925995
theorem B2568071 : Blo 1711056 2568071 := bstep (se 1 (by rfl) ⟨1926053, by rfl⟩ : syracuseStep 2568071 = 3852107) B3852107
theorem B2568107 : Blo 1711056 2568107 := bstep (se 1 (by rfl) ⟨1926080, by rfl⟩ : syracuseStep 2568107 = 3852161) B3852161
theorem B2887609 : Blo 1711056 2887609 := bstep (se 2 (by rfl) ⟨1082853, by rfl⟩ : syracuseStep 2887609 = 2165707) B2165707
theorem B10407865 : Blo 1711056 10407865 := bstep (se 2 (by rfl) ⟨3902949, by rfl⟩ : syracuseStep 10407865 = 7805899) B7805899
theorem B5484473 : Blo 1711056 5484473 := bstep (se 2 (by rfl) ⟨2056677, by rfl⟩ : syracuseStep 5484473 = 4113355) B4113355
theorem B2568137 : Blo 1711056 2568137 := bstep (se 2 (by rfl) ⟨963051, by rfl⟩ : syracuseStep 2568137 = 1926103) B1926103
theorem B8335307 : Blo 1711056 8335307 := bstep (se 1 (by rfl) ⟨6251480, by rfl⟩ : syracuseStep 8335307 = 12502961) B12502961
theorem B3084331 : Blo 1711056 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B2568251 : Blo 1711056 2568251 := bstep (se 1 (by rfl) ⟨1926188, by rfl⟩ : syracuseStep 2568251 = 3852377) B3852377
theorem B2568311 : Blo 1711056 2568311 := bstep (se 1 (by rfl) ⟨1926233, by rfl⟩ : syracuseStep 2568311 = 3852467) B3852467
theorem B4690055 : Blo 1711056 4690055 := bstep (se 1 (by rfl) ⟨3517541, by rfl⟩ : syracuseStep 4690055 = 7035083) B7035083
theorem B2568335 : Blo 1711056 2568335 := bstep (se 1 (by rfl) ⟨1926251, by rfl⟩ : syracuseStep 2568335 = 3852503) B3852503
theorem B2568377 : Blo 1711056 2568377 := bstep (se 2 (by rfl) ⟨963141, by rfl⟩ : syracuseStep 2568377 = 1926283) B1926283
theorem B2314427 : Blo 1711056 2314427 := bstep (se 1 (by rfl) ⟨1735820, by rfl⟩ : syracuseStep 2314427 = 3471641) B3471641
theorem B23433461 : Blo 1711056 23433461 := bstep (se 5 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 23433461 = 2196887) B2196887
theorem B2568455 : Blo 1711056 2568455 := bstep (se 1 (by rfl) ⟨1926341, by rfl⟩ : syracuseStep 2568455 = 3852683) B3852683
theorem B5779727 : Blo 1711056 5779727 := bstep (se 1 (by rfl) ⟨4334795, by rfl⟩ : syracuseStep 5779727 = 8669591) B8669591
theorem B24695057 : Blo 1711056 24695057 := bstep (se 2 (by rfl) ⟨9260646, by rfl⟩ : syracuseStep 24695057 = 18521293) B18521293
theorem B3248417 : Blo 1711056 3248417 := bstep (se 2 (by rfl) ⟨1218156, by rfl⟩ : syracuseStep 3248417 = 2436313) B2436313
theorem B2568491 : Blo 1711056 2568491 := bstep (se 1 (by rfl) ⟨1926368, by rfl⟩ : syracuseStep 2568491 = 3852737) B3852737
theorem B2568521 : Blo 1711056 2568521 := bstep (se 2 (by rfl) ⟨963195, by rfl⟩ : syracuseStep 2568521 = 1926391) B1926391
theorem B2167175 : Blo 1711056 2167175 := bstep (se 1 (by rfl) ⟨1625381, by rfl⟩ : syracuseStep 2167175 = 3250763) B3250763
theorem B2568635 : Blo 1711056 2568635 := bstep (se 1 (by rfl) ⟨1926476, by rfl⟩ : syracuseStep 2568635 = 3852953) B3852953
theorem B8671697 : Blo 1711056 8671697 := bstep (se 2 (by rfl) ⟨3251886, by rfl⟩ : syracuseStep 8671697 = 6503773) B6503773
theorem B2568695 : Blo 1711056 2568695 := bstep (se 1 (by rfl) ⟨1926521, by rfl⟩ : syracuseStep 2568695 = 3853043) B3853043
theorem B2568719 : Blo 1711056 2568719 := bstep (se 1 (by rfl) ⟨1926539, by rfl⟩ : syracuseStep 2568719 = 3853079) B3853079
theorem B5779997 : Blo 1711056 5779997 := bstep (se 3 (by rfl) ⟨1083749, by rfl⟩ : syracuseStep 5779997 = 2167499) B2167499
theorem B5485099 : Blo 1711056 5485099 := bstep (se 1 (by rfl) ⟨4113824, by rfl⟩ : syracuseStep 5485099 = 8227649) B8227649
theorem B2568761 : Blo 1711056 2568761 := bstep (se 2 (by rfl) ⟨963285, by rfl⟩ : syracuseStep 2568761 = 1926571) B1926571
theorem B9753155 : Blo 1711056 9753155 := bstep (se 1 (by rfl) ⟨7314866, by rfl⟩ : syracuseStep 9753155 = 14629733) B14629733
theorem B13890125 : Blo 1711056 13890125 := bstep (se 3 (by rfl) ⟨2604398, by rfl⟩ : syracuseStep 13890125 = 5208797) B5208797
theorem B2888311 : Blo 1711056 2888311 := bstep (se 1 (by rfl) ⟨2166233, by rfl⟩ : syracuseStep 2888311 = 4332467) B4332467
theorem B2568839 : Blo 1711056 2568839 := bstep (se 1 (by rfl) ⟨1926629, by rfl⟩ : syracuseStep 2568839 = 3853259) B3853259
theorem B2568875 : Blo 1711056 2568875 := bstep (se 1 (by rfl) ⟨1926656, by rfl⟩ : syracuseStep 2568875 = 3853313) B3853313
theorem B2568905 : Blo 1711056 2568905 := bstep (se 2 (by rfl) ⟨963339, by rfl⟩ : syracuseStep 2568905 = 1926679) B1926679
theorem B3658441 : Blo 1711056 3658441 := bstep (se 2 (by rfl) ⟨1371915, by rfl⟩ : syracuseStep 3658441 = 2743831) B2743831
theorem B2437879 : Blo 1711056 2437879 := bstep (se 1 (by rfl) ⟨1828409, by rfl⟩ : syracuseStep 2437879 = 3656819) B3656819
theorem B8229647 : Blo 1711056 8229647 := bstep (se 1 (by rfl) ⟨6172235, by rfl⟩ : syracuseStep 8229647 = 12344471) B12344471
theorem B2888507 : Blo 1711056 2888507 := bstep (se 1 (by rfl) ⟨2166380, by rfl⟩ : syracuseStep 2888507 = 4332761) B4332761
theorem B2569019 : Blo 1711056 2569019 := bstep (se 1 (by rfl) ⟨1926764, by rfl⟩ : syracuseStep 2569019 = 3853529) B3853529
theorem B2569079 : Blo 1711056 2569079 := bstep (se 1 (by rfl) ⟨1926809, by rfl⟩ : syracuseStep 2569079 = 3853619) B3853619
theorem B2569103 : Blo 1711056 2569103 := bstep (se 1 (by rfl) ⟨1926827, by rfl⟩ : syracuseStep 2569103 = 3853655) B3853655
theorem B2569145 : Blo 1711056 2569145 := bstep (se 2 (by rfl) ⟨963429, by rfl⟩ : syracuseStep 2569145 = 1926859) B1926859
theorem B6501329 : Blo 1711056 6501329 := bstep (se 2 (by rfl) ⟨2437998, by rfl⟩ : syracuseStep 6501329 = 4875997) B4875997
theorem B2569223 : Blo 1711056 2569223 := bstep (se 1 (by rfl) ⟨1926917, by rfl⟩ : syracuseStep 2569223 = 3853835) B3853835
theorem B2167823 : Blo 1711056 2167823 := bstep (se 1 (by rfl) ⟨1625867, by rfl⟩ : syracuseStep 2167823 = 3251735) B3251735
theorem B2569259 : Blo 1711056 2569259 := bstep (se 1 (by rfl) ⟨1926944, by rfl⟩ : syracuseStep 2569259 = 3853889) B3853889
theorem B2569289 : Blo 1711056 2569289 := bstep (se 2 (by rfl) ⟨963483, by rfl⟩ : syracuseStep 2569289 = 1926967) B1926967
theorem B2569403 : Blo 1711056 2569403 := bstep (se 1 (by rfl) ⟨1927052, by rfl⟩ : syracuseStep 2569403 = 3854105) B3854105
theorem B2888905 : Blo 1711056 2888905 := bstep (se 2 (by rfl) ⟨1083339, by rfl⟩ : syracuseStep 2888905 = 2166679) B2166679
theorem B2569463 : Blo 1711056 2569463 := bstep (se 1 (by rfl) ⟨1927097, by rfl⟩ : syracuseStep 2569463 = 3854195) B3854195
theorem B2741519 : Blo 1711056 2741519 := bstep (se 1 (by rfl) ⟨2056139, by rfl⟩ : syracuseStep 2741519 = 4112279) B4112279
theorem B6501647 : Blo 1711056 6501647 := bstep (se 1 (by rfl) ⟨4876235, by rfl⟩ : syracuseStep 6501647 = 9752471) B9752471
theorem B2569487 : Blo 1711056 2569487 := bstep (se 1 (by rfl) ⟨1927115, by rfl⟩ : syracuseStep 2569487 = 3854231) B3854231
theorem B2569529 : Blo 1711056 2569529 := bstep (se 2 (by rfl) ⟨963573, by rfl⟩ : syracuseStep 2569529 = 1927147) B1927147
theorem B3085715 : Blo 1711056 3085715 := bstep (se 1 (by rfl) ⟨2314286, by rfl⟩ : syracuseStep 3085715 = 4628573) B4628573
theorem B4281943 : Blo 1711056 4281943 := bstep (se 1 (by rfl) ⟨3211457, by rfl⟩ : syracuseStep 4281943 = 6422915) B6422915
theorem B35149463 : Blo 1711056 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B2889607 : Blo 1711056 2889607 := bstep (se 1 (by rfl) ⟨2167205, by rfl⟩ : syracuseStep 2889607 = 4334411) B4334411
theorem B4626323 : Blo 1711056 4626323 := bstep (se 1 (by rfl) ⟨3469742, by rfl⟩ : syracuseStep 4626323 = 6939485) B6939485
theorem B5781401 : Blo 1711056 5781401 := bstep (se 2 (by rfl) ⟨2168025, by rfl⟩ : syracuseStep 5781401 = 4336051) B4336051
theorem B4331465 : Blo 1711056 4331465 := bstep (se 2 (by rfl) ⟨1624299, by rfl⟩ : syracuseStep 4331465 = 3248599) B3248599
theorem B19494917 : Blo 1711056 19494917 := bstep (se 4 (by rfl) ⟨1827648, by rfl⟩ : syracuseStep 19494917 = 3655297) B3655297
theorem B3250361 : Blo 1711056 3250361 := bstep (se 2 (by rfl) ⟨1218885, by rfl⟩ : syracuseStep 3250361 = 2437771) B2437771
theorem B2742473 : Blo 1711056 2742473 := bstep (se 2 (by rfl) ⟨1028427, by rfl⟩ : syracuseStep 2742473 = 2056855) B2056855
theorem B6166817 : Blo 1711056 6166817 := bstep (se 2 (by rfl) ⟨2312556, by rfl⟩ : syracuseStep 6166817 = 4625113) B4625113
theorem B4331819 : Blo 1711056 4331819 := bstep (se 1 (by rfl) ⟨3248864, by rfl⟩ : syracuseStep 4331819 = 6497729) B6497729
theorem B9754931 : Blo 1711056 9754931 := bstep (se 1 (by rfl) ⟨7316198, by rfl⟩ : syracuseStep 9754931 = 14632397) B14632397
theorem B105470261 : Blo 1711056 105470261 := bstep (se 5 (by rfl) ⟨4943918, by rfl⟩ : syracuseStep 105470261 = 9887837) B9887837
theorem B7313723 : Blo 1711056 7313723 := bstep (se 1 (by rfl) ⟨5485292, by rfl⟩ : syracuseStep 7313723 = 10970585) B10970585
theorem B16456067 : Blo 1711056 16456067 := bstep (se 1 (by rfl) ⟨12342050, by rfl⟩ : syracuseStep 16456067 = 24684101) B24684101
theorem B8231321 : Blo 1711056 8231321 := bstep (se 2 (by rfl) ⟨3086745, by rfl⟩ : syracuseStep 8231321 = 6173491) B6173491
theorem B7813529 : Blo 1711056 7813529 := bstep (se 2 (by rfl) ⟨2930073, by rfl⟩ : syracuseStep 7813529 = 5860147) B5860147
theorem B9746891 : Blo 1711056 9746891 := bstep (se 1 (by rfl) ⟨7310168, by rfl⟩ : syracuseStep 9746891 = 14620337) B14620337
theorem B18512387 : Blo 1711056 18512387 := bstep (se 1 (by rfl) ⟨13884290, by rfl⟩ : syracuseStep 18512387 = 27768581) B27768581
theorem B2890255 : Blo 1711056 2890255 := bstep (se 1 (by rfl) ⟨2167691, by rfl⟩ : syracuseStep 2890255 = 4335383) B4335383
theorem B29637413 : Blo 1711056 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B19757939 : Blo 1711056 19757939 := bstep (se 1 (by rfl) ⟨14818454, by rfl⟩ : syracuseStep 19757939 = 29636909) B29636909
theorem B2743159 : Blo 1711056 2743159 := bstep (se 1 (by rfl) ⟨2057369, by rfl⟩ : syracuseStep 2743159 = 4114739) B4114739
theorem B1711111 : Blo 1711056 1711111 := bstep (se 1 (by rfl) ⟨1283333, by rfl⟩ : syracuseStep 1711111 = 2566667) B2566667
theorem B1711119 : Blo 1711056 1711119 := bstep (se 1 (by rfl) ⟨1283339, by rfl⟩ : syracuseStep 1711119 = 2566679) B2566679
theorem B3906593 : Blo 1711056 3906593 := bstep (se 2 (by rfl) ⟨1464972, by rfl⟩ : syracuseStep 3906593 = 2929945) B2929945
theorem B1711163 : Blo 1711056 1711163 := bstep (se 1 (by rfl) ⟨1283372, by rfl⟩ : syracuseStep 1711163 = 2566745) B2566745
theorem B1711239 : Blo 1711056 1711239 := bstep (se 1 (by rfl) ⟨1283429, by rfl⟩ : syracuseStep 1711239 = 2566859) B2566859
theorem B1711247 : Blo 1711056 1711247 := bstep (se 1 (by rfl) ⟨1283435, by rfl⟩ : syracuseStep 1711247 = 2566871) B2566871
theorem B1711291 : Blo 1711056 1711291 := bstep (se 1 (by rfl) ⟨1283468, by rfl⟩ : syracuseStep 1711291 = 2566937) B2566937
theorem B1711367 : Blo 1711056 1711367 := bstep (se 1 (by rfl) ⟨1283525, by rfl⟩ : syracuseStep 1711367 = 2567051) B2567051
theorem B4332811 : Blo 1711056 4332811 := bstep (se 1 (by rfl) ⟨3249608, by rfl⟩ : syracuseStep 4332811 = 6499217) B6499217
theorem B1711375 : Blo 1711056 1711375 := bstep (se 1 (by rfl) ⟨1283531, by rfl⟩ : syracuseStep 1711375 = 2567063) B2567063
theorem B1711419 : Blo 1711056 1711419 := bstep (se 1 (by rfl) ⟨1283564, by rfl⟩ : syracuseStep 1711419 = 2567129) B2567129
theorem B55541051 : Blo 1711056 55541051 := bstep (se 1 (by rfl) ⟨41655788, by rfl⟩ : syracuseStep 55541051 = 83311577) B83311577
theorem B3251515 : Blo 1711056 3251515 := bstep (se 1 (by rfl) ⟨2438636, by rfl⟩ : syracuseStep 3251515 = 4877273) B4877273
theorem B1711495 : Blo 1711056 1711495 := bstep (se 1 (by rfl) ⟨1283621, by rfl⟩ : syracuseStep 1711495 = 2567243) B2567243
theorem B1711503 : Blo 1711056 1711503 := bstep (se 1 (by rfl) ⟨1283627, by rfl⟩ : syracuseStep 1711503 = 2567255) B2567255
theorem B8666513 : Blo 1711056 8666513 := bstep (se 2 (by rfl) ⟨3249942, by rfl⟩ : syracuseStep 8666513 = 6499885) B6499885
theorem B13008275 : Blo 1711056 13008275 := bstep (se 1 (by rfl) ⟨9756206, by rfl⟩ : syracuseStep 13008275 = 19512413) B19512413
theorem B4332953 : Blo 1711056 4332953 := bstep (se 2 (by rfl) ⟨1624857, by rfl⟩ : syracuseStep 4332953 = 3249715) B3249715
theorem B1711547 : Blo 1711056 1711547 := bstep (se 1 (by rfl) ⟨1283660, by rfl⟩ : syracuseStep 1711547 = 2567321) B2567321
theorem B1711623 : Blo 1711056 1711623 := bstep (se 1 (by rfl) ⟨1283717, by rfl⟩ : syracuseStep 1711623 = 2567435) B2567435
theorem B1711631 : Blo 1711056 1711631 := bstep (se 1 (by rfl) ⟨1283723, by rfl⟩ : syracuseStep 1711631 = 2567447) B2567447
theorem B1711675 : Blo 1711056 1711675 := bstep (se 1 (by rfl) ⟨1283756, by rfl⟩ : syracuseStep 1711675 = 2567513) B2567513
theorem B4333115 : Blo 1711056 4333115 := bstep (se 1 (by rfl) ⟨3249836, by rfl⟩ : syracuseStep 4333115 = 6499673) B6499673
theorem B1711751 : Blo 1711056 1711751 := bstep (se 1 (by rfl) ⟨1283813, by rfl⟩ : syracuseStep 1711751 = 2567627) B2567627
theorem B1711759 : Blo 1711056 1711759 := bstep (se 1 (by rfl) ⟨1283819, by rfl⟩ : syracuseStep 1711759 = 2567639) B2567639
theorem B1711803 : Blo 1711056 1711803 := bstep (se 1 (by rfl) ⟨1283852, by rfl⟩ : syracuseStep 1711803 = 2567705) B2567705
theorem B3849929 : Blo 1711056 3849929 := bstep (se 2 (by rfl) ⟨1443723, by rfl⟩ : syracuseStep 3849929 = 2887447) B2887447
theorem B7806665 : Blo 1711056 7806665 := bstep (se 2 (by rfl) ⟨2927499, by rfl⟩ : syracuseStep 7806665 = 5854999) B5854999
theorem B9756389 : Blo 1711056 9756389 := bstep (se 4 (by rfl) ⟨914661, by rfl⟩ : syracuseStep 9756389 = 1829323) B1829323
theorem B1711879 : Blo 1711056 1711879 := bstep (se 1 (by rfl) ⟨1283909, by rfl⟩ : syracuseStep 1711879 = 2567819) B2567819
theorem B1711887 : Blo 1711056 1711887 := bstep (se 1 (by rfl) ⟨1283915, by rfl⟩ : syracuseStep 1711887 = 2567831) B2567831
theorem B5775137 : Blo 1711056 5775137 := bstep (se 2 (by rfl) ⟨2165676, by rfl⟩ : syracuseStep 5775137 = 4331353) B4331353
theorem B3252001 : Blo 1711056 3252001 := bstep (se 2 (by rfl) ⟨1219500, by rfl⟩ : syracuseStep 3252001 = 2439001) B2439001
theorem B32907059 : Blo 1711056 32907059 := bstep (se 1 (by rfl) ⟨24680294, by rfl⟩ : syracuseStep 32907059 = 49360589) B49360589
theorem B13000499 : Blo 1711056 13000499 := bstep (se 1 (by rfl) ⟨9750374, by rfl⟩ : syracuseStep 13000499 = 19500749) B19500749
theorem B4939579 : Blo 1711056 4939579 := bstep (se 1 (by rfl) ⟨3704684, by rfl⟩ : syracuseStep 4939579 = 7409369) B7409369
theorem B1711931 : Blo 1711056 1711931 := bstep (se 1 (by rfl) ⟨1283948, by rfl⟩ : syracuseStep 1711931 = 2567897) B2567897
theorem B37011269 : Blo 1711056 37011269 := bstep (se 4 (by rfl) ⟨3469806, by rfl⟩ : syracuseStep 37011269 = 6939613) B6939613
theorem B1712007 : Blo 1711056 1712007 := bstep (se 1 (by rfl) ⟨1284005, by rfl⟩ : syracuseStep 1712007 = 2568011) B2568011
theorem B1712015 : Blo 1711056 1712015 := bstep (se 1 (by rfl) ⟨1284011, by rfl⟩ : syracuseStep 1712015 = 2568023) B2568023
theorem B8904593 : Blo 1711056 8904593 := bstep (se 2 (by rfl) ⟨3339222, by rfl⟩ : syracuseStep 8904593 = 6678445) B6678445
theorem B4333459 : Blo 1711056 4333459 := bstep (se 1 (by rfl) ⟨3250094, by rfl⟩ : syracuseStep 4333459 = 6500189) B6500189
theorem B67657625 : Blo 1711056 67657625 := bstep (se 2 (by rfl) ⟨25371609, by rfl⟩ : syracuseStep 67657625 = 50743219) B50743219
theorem B1712059 : Blo 1711056 1712059 := bstep (se 1 (by rfl) ⟨1284044, by rfl⟩ : syracuseStep 1712059 = 2568089) B2568089
theorem B4874185 : Blo 1711056 4874185 := bstep (se 2 (by rfl) ⟨1827819, by rfl⟩ : syracuseStep 4874185 = 3655639) B3655639
theorem B1712167 : Blo 1711056 1712167 := bstep (se 1 (by rfl) ⟨1284125, by rfl⟩ : syracuseStep 1712167 = 2568251) B2568251
theorem B4112441 : Blo 1711056 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B1712207 : Blo 1711056 1712207 := bstep (se 1 (by rfl) ⟨1284155, by rfl⟩ : syracuseStep 1712207 = 2568311) B2568311
theorem B1712223 : Blo 1711056 1712223 := bstep (se 1 (by rfl) ⟨1284167, by rfl⟩ : syracuseStep 1712223 = 2568335) B2568335
theorem B17563763 : Blo 1711056 17563763 := bstep (se 1 (by rfl) ⟨13172822, by rfl⟩ : syracuseStep 17563763 = 26345645) B26345645
theorem B1712251 : Blo 1711056 1712251 := bstep (se 1 (by rfl) ⟨1284188, by rfl⟩ : syracuseStep 1712251 = 2568377) B2568377
theorem B15622307 : Blo 1711056 15622307 := bstep (se 1 (by rfl) ⟨11716730, by rfl⟩ : syracuseStep 15622307 = 23433461) B23433461
theorem B1712303 : Blo 1711056 1712303 := bstep (se 1 (by rfl) ⟨1284227, by rfl⟩ : syracuseStep 1712303 = 2568455) B2568455
theorem B1712327 : Blo 1711056 1712327 := bstep (se 1 (by rfl) ⟨1284245, by rfl⟩ : syracuseStep 1712327 = 2568491) B2568491
theorem B1712347 : Blo 1711056 1712347 := bstep (se 1 (by rfl) ⟨1284260, by rfl⟩ : syracuseStep 1712347 = 2568521) B2568521
theorem B3850487 : Blo 1711056 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B1712423 : Blo 1711056 1712423 := bstep (se 1 (by rfl) ⟨1284317, by rfl⟩ : syracuseStep 1712423 = 2568635) B2568635
theorem B5775677 : Blo 1711056 5775677 := bstep (se 3 (by rfl) ⟨1082939, by rfl⟩ : syracuseStep 5775677 = 2165879) B2165879
theorem B1712463 : Blo 1711056 1712463 := bstep (se 1 (by rfl) ⟨1284347, by rfl⟩ : syracuseStep 1712463 = 2568695) B2568695
theorem B1712479 : Blo 1711056 1712479 := bstep (se 1 (by rfl) ⟨1284359, by rfl⟩ : syracuseStep 1712479 = 2568719) B2568719
theorem B1712507 : Blo 1711056 1712507 := bstep (se 1 (by rfl) ⟨1284380, by rfl⟩ : syracuseStep 1712507 = 2568761) B2568761
theorem B1712559 : Blo 1711056 1712559 := bstep (se 1 (by rfl) ⟨1284419, by rfl⟩ : syracuseStep 1712559 = 2568839) B2568839
theorem B1712583 : Blo 1711056 1712583 := bstep (se 1 (by rfl) ⟨1284437, by rfl⟩ : syracuseStep 1712583 = 2568875) B2568875
theorem B1712603 : Blo 1711056 1712603 := bstep (se 1 (by rfl) ⟨1284452, by rfl⟩ : syracuseStep 1712603 = 2568905) B2568905
theorem B5857817 : Blo 1711056 5857817 := bstep (se 2 (by rfl) ⟨2196681, by rfl⟩ : syracuseStep 5857817 = 4393363) B4393363
theorem B1925671 : Blo 1711056 1925671 := bstep (se 1 (by rfl) ⟨1444253, by rfl⟩ : syracuseStep 1925671 = 2888507) B2888507
theorem B1712679 : Blo 1711056 1712679 := bstep (se 1 (by rfl) ⟨1284509, by rfl⟩ : syracuseStep 1712679 = 2569019) B2569019
theorem B1712719 : Blo 1711056 1712719 := bstep (se 1 (by rfl) ⟨1284539, by rfl⟩ : syracuseStep 1712719 = 2569079) B2569079
theorem B1712735 : Blo 1711056 1712735 := bstep (se 1 (by rfl) ⟨1284551, by rfl⟩ : syracuseStep 1712735 = 2569103) B2569103
theorem B1712763 : Blo 1711056 1712763 := bstep (se 1 (by rfl) ⟨1284572, by rfl⟩ : syracuseStep 1712763 = 2569145) B2569145
theorem B4334219 : Blo 1711056 4334219 := bstep (se 1 (by rfl) ⟨3250664, by rfl⟩ : syracuseStep 4334219 = 6501329) B6501329
theorem B1712815 : Blo 1711056 1712815 := bstep (se 1 (by rfl) ⟨1284611, by rfl⟩ : syracuseStep 1712815 = 2569223) B2569223
theorem B1712839 : Blo 1711056 1712839 := bstep (se 1 (by rfl) ⟨1284629, by rfl⟩ : syracuseStep 1712839 = 2569259) B2569259
theorem B4391639 : Blo 1711056 4391639 := bstep (se 1 (by rfl) ⟨3293729, by rfl⟩ : syracuseStep 4391639 = 6587459) B6587459
theorem B1712859 : Blo 1711056 1712859 := bstep (se 1 (by rfl) ⟨1284644, by rfl⟩ : syracuseStep 1712859 = 2569289) B2569289
theorem B1712935 : Blo 1711056 1712935 := bstep (se 1 (by rfl) ⟨1284701, by rfl⟩ : syracuseStep 1712935 = 2569403) B2569403
theorem B3851081 : Blo 1711056 3851081 := bstep (se 2 (by rfl) ⟨1444155, by rfl⟩ : syracuseStep 3851081 = 2888311) B2888311
theorem B1712975 : Blo 1711056 1712975 := bstep (se 1 (by rfl) ⟨1284731, by rfl⟩ : syracuseStep 1712975 = 2569463) B2569463
theorem B1827679 : Blo 1711056 1827679 := bstep (se 1 (by rfl) ⟨1370759, by rfl⟩ : syracuseStep 1827679 = 2741519) B2741519
theorem B4334431 : Blo 1711056 4334431 := bstep (se 1 (by rfl) ⟨3250823, by rfl⟩ : syracuseStep 4334431 = 6501647) B6501647
theorem B1712991 : Blo 1711056 1712991 := bstep (se 1 (by rfl) ⟨1284743, by rfl⟩ : syracuseStep 1712991 = 2569487) B2569487
theorem B1713019 : Blo 1711056 1713019 := bstep (se 1 (by rfl) ⟨1284764, by rfl⟩ : syracuseStep 1713019 = 2569529) B2569529
theorem B27779993 : Blo 1711056 27779993 := bstep (se 2 (by rfl) ⟨10417497, by rfl⟩ : syracuseStep 27779993 = 20834995) B20834995
theorem B6587399 : Blo 1711056 6587399 := bstep (se 1 (by rfl) ⟨4940549, by rfl⟩ : syracuseStep 6587399 = 9881099) B9881099
theorem B9749555 : Blo 1711056 9749555 := bstep (se 1 (by rfl) ⟨7312166, by rfl⟩ : syracuseStep 9749555 = 14624333) B14624333
theorem B5776541 : Blo 1711056 5776541 := bstep (se 3 (by rfl) ⟨1083101, by rfl⟩ : syracuseStep 5776541 = 2166203) B2166203
theorem B1828315 : Blo 1711056 1828315 := bstep (se 1 (by rfl) ⟨1371236, by rfl⟩ : syracuseStep 1828315 = 2742473) B2742473
theorem B70313507 : Blo 1711056 70313507 := bstep (se 1 (by rfl) ⟨52735130, by rfl⟩ : syracuseStep 70313507 = 105470261) B105470261
theorem B4875815 : Blo 1711056 4875815 := bstep (se 1 (by rfl) ⟨3656861, by rfl⟩ : syracuseStep 4875815 = 7313723) B7313723
theorem B10970711 : Blo 1711056 10970711 := bstep (se 1 (by rfl) ⟨8228033, by rfl⟩ : syracuseStep 10970711 = 16456067) B16456067
theorem B3851873 : Blo 1711056 3851873 := bstep (se 2 (by rfl) ⟨1444452, by rfl⟩ : syracuseStep 3851873 = 2888905) B2888905
theorem B12994181 : Blo 1711056 12994181 := bstep (se 4 (by rfl) ⟨1218204, by rfl⟩ : syracuseStep 12994181 = 2436409) B2436409
theorem B6497927 : Blo 1711056 6497927 := bstep (se 1 (by rfl) ⟨4873445, by rfl⟩ : syracuseStep 6497927 = 9746891) B9746891
theorem B5777081 : Blo 1711056 5777081 := bstep (se 2 (by rfl) ⟨2166405, by rfl⟩ : syracuseStep 5777081 = 4332811) B4332811
theorem B4335353 : Blo 1711056 4335353 := bstep (se 2 (by rfl) ⟨1625757, by rfl⟩ : syracuseStep 4335353 = 3251515) B3251515
theorem B20817773 : Blo 1711056 20817773 := bstep (se 3 (by rfl) ⟨3903332, by rfl⟩ : syracuseStep 20817773 = 7806665) B7806665
theorem B3852215 : Blo 1711056 3852215 := bstep (se 1 (by rfl) ⟨2889161, by rfl⟩ : syracuseStep 3852215 = 5778323) B5778323
theorem B5777675 : Blo 1711056 5777675 := bstep (se 1 (by rfl) ⟨4333256, by rfl⟩ : syracuseStep 5777675 = 8666513) B8666513
theorem B7309673 : Blo 1711056 7309673 := bstep (se 2 (by rfl) ⟨2741127, by rfl⟩ : syracuseStep 7309673 = 5482255) B5482255
theorem B4336001 : Blo 1711056 4336001 := bstep (se 2 (by rfl) ⟨1626000, by rfl⟩ : syracuseStep 4336001 = 3252001) B3252001
theorem B2566619 : Blo 1711056 2566619 := bstep (se 1 (by rfl) ⟨1924964, by rfl⟩ : syracuseStep 2566619 = 3849929) B3849929
theorem B3852809 : Blo 1711056 3852809 := bstep (se 2 (by rfl) ⟨1444803, by rfl⟩ : syracuseStep 3852809 = 2889607) B2889607
theorem B5777945 : Blo 1711056 5777945 := bstep (se 2 (by rfl) ⟨2166729, by rfl⟩ : syracuseStep 5777945 = 4333459) B4333459
theorem B6498913 : Blo 1711056 6498913 := bstep (se 2 (by rfl) ⟨2437092, by rfl⟩ : syracuseStep 6498913 = 4874185) B4874185
theorem B3656315 : Blo 1711056 3656315 := bstep (se 1 (by rfl) ⟨2742236, by rfl⟩ : syracuseStep 3656315 = 5484473) B5484473
theorem B5556871 : Blo 1711056 5556871 := bstep (se 1 (by rfl) ⟨4167653, by rfl⟩ : syracuseStep 5556871 = 8335307) B8335307
theorem B7310033 : Blo 1711056 7310033 := bstep (se 2 (by rfl) ⟨2741262, by rfl⟩ : syracuseStep 7310033 = 5482525) B5482525
theorem B3853151 : Blo 1711056 3853151 := bstep (se 1 (by rfl) ⟨2889863, by rfl⟩ : syracuseStep 3853151 = 5779727) B5779727
theorem B2165611 : Blo 1711056 2165611 := bstep (se 1 (by rfl) ⟨1624208, by rfl⟩ : syracuseStep 2165611 = 3248417) B3248417
theorem B2567087 : Blo 1711056 2567087 := bstep (se 1 (by rfl) ⟨1925315, by rfl⟩ : syracuseStep 2567087 = 3850631) B3850631
theorem B5483447 : Blo 1711056 5483447 := bstep (se 1 (by rfl) ⟨4112585, by rfl⟩ : syracuseStep 5483447 = 8225171) B8225171
theorem B2780087 : Blo 1711056 2780087 := bstep (se 1 (by rfl) ⟨2085065, by rfl⟩ : syracuseStep 2780087 = 4170131) B4170131
theorem B2567177 : Blo 1711056 2567177 := bstep (se 2 (by rfl) ⟨962691, by rfl⟩ : syracuseStep 2567177 = 1925383) B1925383
theorem B3853331 : Blo 1711056 3853331 := bstep (se 1 (by rfl) ⟨2889998, by rfl⟩ : syracuseStep 3853331 = 5779997) B5779997
theorem B2567207 : Blo 1711056 2567207 := bstep (se 1 (by rfl) ⟨1925405, by rfl⟩ : syracuseStep 2567207 = 3850811) B3850811
theorem B9260083 : Blo 1711056 9260083 := bstep (se 1 (by rfl) ⟨6945062, by rfl⟩ : syracuseStep 9260083 = 13890125) B13890125
theorem B6499385 : Blo 1711056 6499385 := bstep (se 2 (by rfl) ⟨2437269, by rfl⟩ : syracuseStep 6499385 = 4874539) B4874539
theorem B2567291 : Blo 1711056 2567291 := bstep (se 1 (by rfl) ⟨1925468, by rfl⟩ : syracuseStep 2567291 = 3850937) B3850937
theorem B6171805 : Blo 1711056 6171805 := bstep (se 3 (by rfl) ⟨1157213, by rfl⟩ : syracuseStep 6171805 = 2314427) B2314427
theorem B2567417 : Blo 1711056 2567417 := bstep (se 2 (by rfl) ⟨962781, by rfl⟩ : syracuseStep 2567417 = 1925563) B1925563
theorem B2567519 : Blo 1711056 2567519 := bstep (se 1 (by rfl) ⟨1925639, by rfl⟩ : syracuseStep 2567519 = 3851279) B3851279
theorem B3853673 : Blo 1711056 3853673 := bstep (se 2 (by rfl) ⟨1445127, by rfl⟩ : syracuseStep 3853673 = 2890255) B2890255
theorem B2567531 : Blo 1711056 2567531 := bstep (se 1 (by rfl) ⟨1925648, by rfl⟩ : syracuseStep 2567531 = 3851297) B3851297
theorem B2567759 : Blo 1711056 2567759 := bstep (se 1 (by rfl) ⟨1925819, by rfl⟩ : syracuseStep 2567759 = 3851639) B3851639
theorem B8662625 : Blo 1711056 8662625 := bstep (se 2 (by rfl) ⟨3248484, by rfl⟩ : syracuseStep 8662625 = 6496969) B6496969
theorem B4877921 : Blo 1711056 4877921 := bstep (se 2 (by rfl) ⟨1829220, by rfl⟩ : syracuseStep 4877921 = 3658441) B3658441
theorem B5779079 : Blo 1711056 5779079 := bstep (se 1 (by rfl) ⟨4334309, by rfl⟩ : syracuseStep 5779079 = 8668619) B8668619
theorem B5779133 : Blo 1711056 5779133 := bstep (se 3 (by rfl) ⟨1083587, by rfl⟩ : syracuseStep 5779133 = 2167175) B2167175
theorem B4943549 : Blo 1711056 4943549 := bstep (se 3 (by rfl) ⟨926915, by rfl⟩ : syracuseStep 4943549 = 1853831) B1853831
theorem B2567879 : Blo 1711056 2567879 := bstep (se 1 (by rfl) ⟨1925909, by rfl⟩ : syracuseStep 2567879 = 3851819) B3851819
theorem B8228573 : Blo 1711056 8228573 := bstep (se 3 (by rfl) ⟨1542857, by rfl⟩ : syracuseStep 8228573 = 3085715) B3085715
theorem B21950189 : Blo 1711056 21950189 := bstep (se 3 (by rfl) ⟨4115660, by rfl⟩ : syracuseStep 21950189 = 8231321) B8231321
theorem B6172409 : Blo 1711056 6172409 := bstep (se 2 (by rfl) ⟨2314653, by rfl⟩ : syracuseStep 6172409 = 4629307) B4629307
theorem B23432975 : Blo 1711056 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B3657545 : Blo 1711056 3657545 := bstep (se 2 (by rfl) ⟨1371579, by rfl⟩ : syracuseStep 3657545 = 2743159) B2743159
theorem B5779295 : Blo 1711056 5779295 := bstep (se 1 (by rfl) ⟨4334471, by rfl⟩ : syracuseStep 5779295 = 8668943) B8668943
theorem B2568041 : Blo 1711056 2568041 := bstep (se 2 (by rfl) ⟨963015, by rfl⟩ : syracuseStep 2568041 = 1926031) B1926031
theorem B3084215 : Blo 1711056 3084215 := bstep (se 1 (by rfl) ⟨2313161, by rfl⟩ : syracuseStep 3084215 = 4626323) B4626323
theorem B2568119 : Blo 1711056 2568119 := bstep (se 1 (by rfl) ⟨1926089, by rfl⟩ : syracuseStep 2568119 = 3852179) B3852179
theorem B16461755 : Blo 1711056 16461755 := bstep (se 1 (by rfl) ⟨12346316, by rfl⟩ : syracuseStep 16461755 = 24692633) B24692633
theorem B3854267 : Blo 1711056 3854267 := bstep (se 1 (by rfl) ⟨2890700, by rfl⟩ : syracuseStep 3854267 = 5781401) B5781401
theorem B2887643 : Blo 1711056 2887643 := bstep (se 1 (by rfl) ⟨2165732, by rfl⟩ : syracuseStep 2887643 = 4331465) B4331465
theorem B2568155 : Blo 1711056 2568155 := bstep (se 1 (by rfl) ⟨1926116, by rfl⟩ : syracuseStep 2568155 = 3852233) B3852233
theorem B5779457 : Blo 1711056 5779457 := bstep (se 2 (by rfl) ⟨2167296, by rfl⟩ : syracuseStep 5779457 = 4334593) B4334593
theorem B12996611 : Blo 1711056 12996611 := bstep (se 1 (by rfl) ⟨9747458, by rfl⟩ : syracuseStep 12996611 = 19494917) B19494917
theorem B6500371 : Blo 1711056 6500371 := bstep (se 1 (by rfl) ⟨4875278, by rfl⟩ : syracuseStep 6500371 = 9750557) B9750557
theorem B2166907 : Blo 1711056 2166907 := bstep (se 1 (by rfl) ⟨1625180, by rfl⟩ : syracuseStep 2166907 = 3250361) B3250361
theorem B2887879 : Blo 1711056 2887879 := bstep (se 1 (by rfl) ⟨2165909, by rfl⟩ : syracuseStep 2887879 = 4331819) B4331819
theorem B5484791 : Blo 1711056 5484791 := bstep (se 1 (by rfl) ⟨4113593, by rfl⟩ : syracuseStep 5484791 = 8227187) B8227187
theorem B12341591 : Blo 1711056 12341591 := bstep (se 1 (by rfl) ⟨9256193, by rfl⟩ : syracuseStep 12341591 = 18512387) B18512387
theorem B2888041 : Blo 1711056 2888041 := bstep (se 2 (by rfl) ⟨1083015, by rfl⟩ : syracuseStep 2888041 = 2166031) B2166031
theorem B2568623 : Blo 1711056 2568623 := bstep (se 1 (by rfl) ⟨1926467, by rfl⟩ : syracuseStep 2568623 = 3852935) B3852935
theorem B9884141 : Blo 1711056 9884141 := bstep (se 3 (by rfl) ⟨1853276, by rfl⟩ : syracuseStep 9884141 = 3706553) B3706553
theorem B2568713 : Blo 1711056 2568713 := bstep (se 2 (by rfl) ⟨963267, by rfl⟩ : syracuseStep 2568713 = 1926535) B1926535
theorem B2568743 : Blo 1711056 2568743 := bstep (se 1 (by rfl) ⟨1926557, by rfl⟩ : syracuseStep 2568743 = 3853115) B3853115
theorem B2568827 : Blo 1711056 2568827 := bstep (se 1 (by rfl) ⟨1926620, by rfl⟩ : syracuseStep 2568827 = 3853241) B3853241
theorem B3470035 : Blo 1711056 3470035 := bstep (se 1 (by rfl) ⟨2602526, by rfl⟩ : syracuseStep 3470035 = 5205053) B5205053
theorem B2568953 : Blo 1711056 2568953 := bstep (se 2 (by rfl) ⟨963357, by rfl⟩ : syracuseStep 2568953 = 1926715) B1926715
theorem B9745181 : Blo 1711056 9745181 := bstep (se 3 (by rfl) ⟨1827221, by rfl⟩ : syracuseStep 9745181 = 3654443) B3654443
theorem B5780267 : Blo 1711056 5780267 := bstep (se 1 (by rfl) ⟨4335200, by rfl⟩ : syracuseStep 5780267 = 8670401) B8670401
theorem B2569055 : Blo 1711056 2569055 := bstep (se 1 (by rfl) ⟨1926791, by rfl⟩ : syracuseStep 2569055 = 3853583) B3853583
theorem B3249001 : Blo 1711056 3249001 := bstep (se 2 (by rfl) ⟨1218375, by rfl⟩ : syracuseStep 3249001 = 2436751) B2436751
theorem B2569067 : Blo 1711056 2569067 := bstep (se 1 (by rfl) ⟨1926800, by rfl⟩ : syracuseStep 2569067 = 3853601) B3853601
theorem B8672183 : Blo 1711056 8672183 := bstep (se 1 (by rfl) ⟨6504137, by rfl⟩ : syracuseStep 8672183 = 13008275) B13008275
theorem B2888635 : Blo 1711056 2888635 := bstep (se 1 (by rfl) ⟨2166476, by rfl⟩ : syracuseStep 2888635 = 4332953) B4332953
theorem B52687837 : Blo 1711056 52687837 := bstep (se 3 (by rfl) ⟨9878969, by rfl⟩ : syracuseStep 52687837 = 19757939) B19757939
theorem B8664083 : Blo 1711056 8664083 := bstep (se 1 (by rfl) ⟨6498062, by rfl⟩ : syracuseStep 8664083 = 12996125) B12996125
theorem B2888743 : Blo 1711056 2888743 := bstep (se 1 (by rfl) ⟨2166557, by rfl⟩ : syracuseStep 2888743 = 4333115) B4333115
theorem B23745581 : Blo 1711056 23745581 := bstep (se 3 (by rfl) ⟨4452296, by rfl⟩ : syracuseStep 23745581 = 8904593) B8904593
theorem B5780537 : Blo 1711056 5780537 := bstep (se 2 (by rfl) ⟨2167701, by rfl⟩ : syracuseStep 5780537 = 4335403) B4335403
theorem B10974275 : Blo 1711056 10974275 := bstep (se 1 (by rfl) ⟨8230706, by rfl⟩ : syracuseStep 10974275 = 16461413) B16461413
theorem B2602063 : Blo 1711056 2602063 := bstep (se 1 (by rfl) ⟨1951547, by rfl⟩ : syracuseStep 2602063 = 3903095) B3903095
theorem B2569295 : Blo 1711056 2569295 := bstep (se 1 (by rfl) ⟨1926971, by rfl⟩ : syracuseStep 2569295 = 3853943) B3853943
theorem B74036375 : Blo 1711056 74036375 := bstep (se 1 (by rfl) ⟨55527281, by rfl⟩ : syracuseStep 74036375 = 111054563) B111054563
theorem B2569415 : Blo 1711056 2569415 := bstep (se 1 (by rfl) ⟨1927061, by rfl⟩ : syracuseStep 2569415 = 3854123) B3854123
theorem B2569577 : Blo 1711056 2569577 := bstep (se 2 (by rfl) ⟨963591, by rfl⟩ : syracuseStep 2569577 = 1927183) B1927183
theorem B2889067 : Blo 1711056 2889067 := bstep (se 1 (by rfl) ⟨2166800, by rfl⟩ : syracuseStep 2889067 = 4333601) B4333601
theorem B5780861 : Blo 1711056 5780861 := bstep (se 3 (by rfl) ⟨1083911, by rfl⟩ : syracuseStep 5780861 = 2167823) B2167823
theorem B9745865 : Blo 1711056 9745865 := bstep (se 2 (by rfl) ⟨3654699, by rfl⟩ : syracuseStep 9745865 = 7309399) B7309399
theorem B16463371 : Blo 1711056 16463371 := bstep (se 1 (by rfl) ⟨12347528, by rfl⟩ : syracuseStep 16463371 = 24695057) B24695057
theorem B15619645 : Blo 1711056 15619645 := bstep (se 3 (by rfl) ⟨2928683, by rfl⟩ : syracuseStep 15619645 = 5857367) B5857367
theorem B5781131 : Blo 1711056 5781131 := bstep (se 1 (by rfl) ⟨4335848, by rfl⟩ : syracuseStep 5781131 = 8671697) B8671697
theorem B12506813 : Blo 1711056 12506813 := bstep (se 3 (by rfl) ⟨2345027, by rfl⟩ : syracuseStep 12506813 = 4690055) B4690055
theorem B4167379 : Blo 1711056 4167379 := bstep (se 1 (by rfl) ⟨3125534, by rfl⟩ : syracuseStep 4167379 = 6251069) B6251069
theorem B3249875 : Blo 1711056 3249875 := bstep (se 1 (by rfl) ⟨2437406, by rfl⟩ : syracuseStep 3249875 = 4874813) B4874813
theorem B6502103 : Blo 1711056 6502103 := bstep (se 1 (by rfl) ⟨4876577, by rfl⟩ : syracuseStep 6502103 = 9753155) B9753155
theorem B5486329 : Blo 1711056 5486329 := bstep (se 2 (by rfl) ⟨2057373, by rfl⟩ : syracuseStep 5486329 = 4114747) B4114747
theorem B11876129 : Blo 1711056 11876129 := bstep (se 2 (by rfl) ⟨4453548, by rfl⟩ : syracuseStep 11876129 = 8907097) B8907097
theorem B2742191 : Blo 1711056 2742191 := bstep (se 1 (by rfl) ⟨2056643, by rfl⟩ : syracuseStep 2742191 = 4113287) B4113287
theorem B7313465 : Blo 1711056 7313465 := bstep (se 2 (by rfl) ⟨2742549, by rfl⟩ : syracuseStep 7313465 = 5485099) B5485099
theorem B2742601 : Blo 1711056 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B3250505 : Blo 1711056 3250505 := bstep (se 2 (by rfl) ⟨1218939, by rfl⟩ : syracuseStep 3250505 = 2437879) B2437879
theorem B12999041 : Blo 1711056 12999041 := bstep (se 2 (by rfl) ⟨4874640, by rfl⟩ : syracuseStep 12999041 = 9749281) B9749281
theorem B2890127 : Blo 1711056 2890127 := bstep (se 1 (by rfl) ⟨2167595, by rfl⟩ : syracuseStep 2890127 = 4335191) B4335191
theorem B2742703 : Blo 1711056 2742703 := bstep (se 1 (by rfl) ⟨2057027, by rfl⟩ : syracuseStep 2742703 = 4114055) B4114055
theorem B2890363 : Blo 1711056 2890363 := bstep (se 1 (by rfl) ⟨2167772, by rfl⟩ : syracuseStep 2890363 = 4335545) B4335545
theorem B10967737 : Blo 1711056 10967737 := bstep (se 2 (by rfl) ⟨4112901, by rfl⟩ : syracuseStep 10967737 = 8225803) B8225803
theorem B4111211 : Blo 1711056 4111211 := bstep (se 1 (by rfl) ⟨3083408, by rfl⟩ : syracuseStep 4111211 = 6166817) B6166817
theorem B6503287 : Blo 1711056 6503287 := bstep (se 1 (by rfl) ⟨4877465, by rfl⟩ : syracuseStep 6503287 = 9754931) B9754931
theorem B5209019 : Blo 1711056 5209019 := bstep (se 1 (by rfl) ⟨3906764, by rfl⟩ : syracuseStep 5209019 = 7813529) B7813529
theorem B1711067 : Blo 1711056 1711067 := bstep (se 1 (by rfl) ⟨1283300, by rfl⟩ : syracuseStep 1711067 = 2566601) B2566601
theorem B1711143 : Blo 1711056 1711143 := bstep (se 1 (by rfl) ⟨1283357, by rfl⟩ : syracuseStep 1711143 = 2566715) B2566715
theorem B1711183 : Blo 1711056 1711183 := bstep (se 1 (by rfl) ⟨1283387, by rfl⟩ : syracuseStep 1711183 = 2566775) B2566775
theorem B3251279 : Blo 1711056 3251279 := bstep (se 1 (by rfl) ⟨2438459, by rfl⟩ : syracuseStep 3251279 = 4876919) B4876919
theorem B1711199 : Blo 1711056 1711199 := bstep (se 1 (by rfl) ⟨1283399, by rfl⟩ : syracuseStep 1711199 = 2566799) B2566799
theorem B1711227 : Blo 1711056 1711227 := bstep (se 1 (by rfl) ⟨1283420, by rfl⟩ : syracuseStep 1711227 = 2566841) B2566841
theorem B1711279 : Blo 1711056 1711279 := bstep (se 1 (by rfl) ⟨1283459, by rfl⟩ : syracuseStep 1711279 = 2566919) B2566919
theorem B19758275 : Blo 1711056 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B1711303 : Blo 1711056 1711303 := bstep (se 1 (by rfl) ⟨1283477, by rfl⟩ : syracuseStep 1711303 = 2566955) B2566955
theorem B1711323 : Blo 1711056 1711323 := bstep (se 1 (by rfl) ⟨1283492, by rfl⟩ : syracuseStep 1711323 = 2566985) B2566985
theorem B4332791 : Blo 1711056 4332791 := bstep (se 1 (by rfl) ⟨3249593, by rfl⟩ : syracuseStep 4332791 = 6499187) B6499187
theorem B9886967 : Blo 1711056 9886967 := bstep (se 1 (by rfl) ⟨7415225, by rfl⟩ : syracuseStep 9886967 = 14830451) B14830451
theorem B1711399 : Blo 1711056 1711399 := bstep (se 1 (by rfl) ⟨1283549, by rfl⟩ : syracuseStep 1711399 = 2567099) B2567099
theorem B1711439 : Blo 1711056 1711439 := bstep (se 1 (by rfl) ⟨1283579, by rfl⟩ : syracuseStep 1711439 = 2567159) B2567159
theorem B1711455 : Blo 1711056 1711455 := bstep (se 1 (by rfl) ⟨1283591, by rfl⟩ : syracuseStep 1711455 = 2567183) B2567183
theorem B2604395 : Blo 1711056 2604395 := bstep (se 1 (by rfl) ⟨1953296, by rfl⟩ : syracuseStep 2604395 = 3906593) B3906593
theorem B1711483 : Blo 1711056 1711483 := bstep (se 1 (by rfl) ⟨1283612, by rfl⟩ : syracuseStep 1711483 = 2567225) B2567225
theorem B21945725 : Blo 1711056 21945725 := bstep (se 3 (by rfl) ⟨4114823, by rfl⟩ : syracuseStep 21945725 = 8229647) B8229647
theorem B26353039 : Blo 1711056 26353039 := bstep (se 1 (by rfl) ⟨19764779, by rfl⟩ : syracuseStep 26353039 = 39529559) B39529559
theorem B1711535 : Blo 1711056 1711535 := bstep (se 1 (by rfl) ⟨1283651, by rfl⟩ : syracuseStep 1711535 = 2567303) B2567303
theorem B1711559 : Blo 1711056 1711559 := bstep (se 1 (by rfl) ⟨1283669, by rfl⟩ : syracuseStep 1711559 = 2567339) B2567339
theorem B5709257 : Blo 1711056 5709257 := bstep (se 2 (by rfl) ⟨2140971, by rfl⟩ : syracuseStep 5709257 = 4281943) B4281943
theorem B1711579 : Blo 1711056 1711579 := bstep (se 1 (by rfl) ⟨1283684, by rfl⟩ : syracuseStep 1711579 = 2567369) B2567369
theorem B1711655 : Blo 1711056 1711655 := bstep (se 1 (by rfl) ⟨1283741, by rfl⟩ : syracuseStep 1711655 = 2567483) B2567483
theorem B37027367 : Blo 1711056 37027367 := bstep (se 1 (by rfl) ⟨27770525, by rfl⟩ : syracuseStep 37027367 = 55541051) B55541051
theorem B1711695 : Blo 1711056 1711695 := bstep (se 1 (by rfl) ⟨1283771, by rfl⟩ : syracuseStep 1711695 = 2567543) B2567543
theorem B1711711 : Blo 1711056 1711711 := bstep (se 1 (by rfl) ⟨1283783, by rfl⟩ : syracuseStep 1711711 = 2567567) B2567567
theorem B1711739 : Blo 1711056 1711739 := bstep (se 1 (by rfl) ⟨1283804, by rfl⟩ : syracuseStep 1711739 = 2567609) B2567609
theorem B1711791 : Blo 1711056 1711791 := bstep (se 1 (by rfl) ⟨1283843, by rfl⟩ : syracuseStep 1711791 = 2567687) B2567687
theorem B1711815 : Blo 1711056 1711815 := bstep (se 1 (by rfl) ⟨1283861, by rfl⟩ : syracuseStep 1711815 = 2567723) B2567723
theorem B1711835 : Blo 1711056 1711835 := bstep (se 1 (by rfl) ⟨1283876, by rfl⟩ : syracuseStep 1711835 = 2567753) B2567753
theorem B6586105 : Blo 1711056 6586105 := bstep (se 2 (by rfl) ⟨2469789, by rfl⟩ : syracuseStep 6586105 = 4939579) B4939579
theorem B1711911 : Blo 1711056 1711911 := bstep (se 1 (by rfl) ⟨1283933, by rfl⟩ : syracuseStep 1711911 = 2567867) B2567867
theorem B6504259 : Blo 1711056 6504259 := bstep (se 1 (by rfl) ⟨4878194, by rfl⟩ : syracuseStep 6504259 = 9756389) B9756389
theorem B1711951 : Blo 1711056 1711951 := bstep (se 1 (by rfl) ⟨1283963, by rfl⟩ : syracuseStep 1711951 = 2567927) B2567927
theorem B1711967 : Blo 1711056 1711967 := bstep (se 1 (by rfl) ⟨1283975, by rfl⟩ : syracuseStep 1711967 = 2567951) B2567951
theorem B3850091 : Blo 1711056 3850091 := bstep (se 1 (by rfl) ⟨2887568, by rfl⟩ : syracuseStep 3850091 = 5775137) B5775137
theorem B21938039 : Blo 1711056 21938039 := bstep (se 1 (by rfl) ⟨16453529, by rfl⟩ : syracuseStep 21938039 = 32907059) B32907059
theorem B8666999 : Blo 1711056 8666999 := bstep (se 1 (by rfl) ⟨6500249, by rfl⟩ : syracuseStep 8666999 = 13000499) B13000499
theorem B1711995 : Blo 1711056 1711995 := bstep (se 1 (by rfl) ⟨1283996, by rfl⟩ : syracuseStep 1711995 = 2567993) B2567993
theorem B24674179 : Blo 1711056 24674179 := bstep (se 1 (by rfl) ⟨18505634, by rfl⟩ : syracuseStep 24674179 = 37011269) B37011269
theorem B3850145 : Blo 1711056 3850145 := bstep (se 2 (by rfl) ⟨1443804, by rfl⟩ : syracuseStep 3850145 = 2887609) B2887609
theorem B13877153 : Blo 1711056 13877153 := bstep (se 2 (by rfl) ⟨5203932, by rfl⟩ : syracuseStep 13877153 = 10407865) B10407865
theorem B1712047 : Blo 1711056 1712047 := bstep (se 1 (by rfl) ⟨1284035, by rfl⟩ : syracuseStep 1712047 = 2568071) B2568071
theorem B45105083 : Blo 1711056 45105083 := bstep (se 1 (by rfl) ⟨33828812, by rfl⟩ : syracuseStep 45105083 = 67657625) B67657625
theorem B12345281 : Blo 1711056 12345281 := bstep (se 2 (by rfl) ⟨4629480, by rfl⟩ : syracuseStep 12345281 = 9258961) B9258961
theorem B1712071 : Blo 1711056 1712071 := bstep (se 1 (by rfl) ⟨1284053, by rfl⟩ : syracuseStep 1712071 = 2568107) B2568107
theorem B1712091 : Blo 1711056 1712091 := bstep (se 1 (by rfl) ⟨1284068, by rfl⟩ : syracuseStep 1712091 = 2568137) B2568137
theorem B8667161 : Blo 1711056 8667161 := bstep (se 2 (by rfl) ⟨3250185, by rfl⟩ : syracuseStep 8667161 = 6500371) B6500371
theorem B3850451 : Blo 1711056 3850451 := bstep (se 1 (by rfl) ⟨2887838, by rfl⟩ : syracuseStep 3850451 = 5775677) B5775677
theorem B3850505 : Blo 1711056 3850505 := bstep (se 2 (by rfl) ⟨1443939, by rfl⟩ : syracuseStep 3850505 = 2887879) B2887879
theorem B1712415 : Blo 1711056 1712415 := bstep (se 1 (by rfl) ⟨1284311, by rfl⟩ : syracuseStep 1712415 = 2568623) B2568623
theorem B1712475 : Blo 1711056 1712475 := bstep (se 1 (by rfl) ⟨1284356, by rfl⟩ : syracuseStep 1712475 = 2568713) B2568713
theorem B1712495 : Blo 1711056 1712495 := bstep (se 1 (by rfl) ⟨1284371, by rfl⟩ : syracuseStep 1712495 = 2568743) B2568743
theorem B13877669 : Blo 1711056 13877669 := bstep (se 4 (by rfl) ⟨1301031, by rfl⟩ : syracuseStep 13877669 = 2602063) B2602063
theorem B1712551 : Blo 1711056 1712551 := bstep (se 1 (by rfl) ⟨1284413, by rfl⟩ : syracuseStep 1712551 = 2568827) B2568827
theorem B3850721 : Blo 1711056 3850721 := bstep (se 2 (by rfl) ⟨1444020, by rfl⟩ : syracuseStep 3850721 = 2888041) B2888041
theorem B1712635 : Blo 1711056 1712635 := bstep (se 1 (by rfl) ⟨1284476, by rfl⟩ : syracuseStep 1712635 = 2568953) B2568953
theorem B6496787 : Blo 1711056 6496787 := bstep (se 1 (by rfl) ⟨4872590, by rfl⟩ : syracuseStep 6496787 = 9745181) B9745181
theorem B1712703 : Blo 1711056 1712703 := bstep (se 1 (by rfl) ⟨1284527, by rfl⟩ : syracuseStep 1712703 = 2569055) B2569055
theorem B1712711 : Blo 1711056 1712711 := bstep (se 1 (by rfl) ⟨1284533, by rfl⟩ : syracuseStep 1712711 = 2569067) B2569067
theorem B4391599 : Blo 1711056 4391599 := bstep (se 1 (by rfl) ⟨3293699, by rfl⟩ : syracuseStep 4391599 = 6587399) B6587399
theorem B5776055 : Blo 1711056 5776055 := bstep (se 1 (by rfl) ⟨4332041, by rfl⟩ : syracuseStep 5776055 = 8664083) B8664083
theorem B7316183 : Blo 1711056 7316183 := bstep (se 1 (by rfl) ⟨5487137, by rfl⟩ : syracuseStep 7316183 = 10974275) B10974275
theorem B1712863 : Blo 1711056 1712863 := bstep (se 1 (by rfl) ⟨1284647, by rfl⟩ : syracuseStep 1712863 = 2569295) B2569295
theorem B49357583 : Blo 1711056 49357583 := bstep (se 1 (by rfl) ⟨37018187, by rfl⟩ : syracuseStep 49357583 = 74036375) B74036375
theorem B3851027 : Blo 1711056 3851027 := bstep (se 1 (by rfl) ⟨2888270, by rfl⟩ : syracuseStep 3851027 = 5776541) B5776541
theorem B1712943 : Blo 1711056 1712943 := bstep (se 1 (by rfl) ⟨1284707, by rfl⟩ : syracuseStep 1712943 = 2569415) B2569415
theorem B1713051 : Blo 1711056 1713051 := bstep (se 1 (by rfl) ⟨1284788, by rfl⟩ : syracuseStep 1713051 = 2569577) B2569577
theorem B14623649 : Blo 1711056 14623649 := bstep (se 2 (by rfl) ⟨5483868, by rfl⟩ : syracuseStep 14623649 = 10967737) B10967737
theorem B6497243 : Blo 1711056 6497243 := bstep (se 1 (by rfl) ⟨4872932, by rfl⟩ : syracuseStep 6497243 = 9745865) B9745865
theorem B46875671 : Blo 1711056 46875671 := bstep (se 1 (by rfl) ⟨35156753, by rfl⟩ : syracuseStep 46875671 = 70313507) B70313507
theorem B3851387 : Blo 1711056 3851387 := bstep (se 1 (by rfl) ⟨2888540, by rfl⟩ : syracuseStep 3851387 = 5777081) B5777081
theorem B4334735 : Blo 1711056 4334735 := bstep (se 1 (by rfl) ⟨3251051, by rfl⟩ : syracuseStep 4334735 = 6502103) B6502103
theorem B13878515 : Blo 1711056 13878515 := bstep (se 1 (by rfl) ⟨10408886, by rfl⟩ : syracuseStep 13878515 = 20817773) B20817773
theorem B3851513 : Blo 1711056 3851513 := bstep (se 2 (by rfl) ⟨1444317, by rfl⟩ : syracuseStep 3851513 = 2888635) B2888635
theorem B1828127 : Blo 1711056 1828127 := bstep (se 1 (by rfl) ⟨1371095, by rfl⟩ : syracuseStep 1828127 = 2742191) B2742191
theorem B4875643 : Blo 1711056 4875643 := bstep (se 1 (by rfl) ⟨3656732, by rfl⟩ : syracuseStep 4875643 = 7313465) B7313465
theorem B3851657 : Blo 1711056 3851657 := bstep (se 2 (by rfl) ⟨1444371, by rfl⟩ : syracuseStep 3851657 = 2888743) B2888743
theorem B12346777 : Blo 1711056 12346777 := bstep (se 2 (by rfl) ⟨4630041, by rfl⟩ : syracuseStep 12346777 = 9260083) B9260083
theorem B3851783 : Blo 1711056 3851783 := bstep (se 1 (by rfl) ⟨2888837, by rfl⟩ : syracuseStep 3851783 = 5777675) B5777675
theorem B1926751 : Blo 1711056 1926751 := bstep (se 1 (by rfl) ⟨1445063, by rfl⟩ : syracuseStep 1926751 = 2890127) B2890127
theorem B3851963 : Blo 1711056 3851963 := bstep (se 1 (by rfl) ⟨2888972, by rfl⟩ : syracuseStep 3851963 = 5777945) B5777945
theorem B3852089 : Blo 1711056 3852089 := bstep (se 2 (by rfl) ⟨1444533, by rfl⟩ : syracuseStep 3852089 = 2889067) B2889067
theorem B13182797 : Blo 1711056 13182797 := bstep (se 3 (by rfl) ⟨2471774, by rfl⟩ : syracuseStep 13182797 = 4943549) B4943549
theorem B35137385 : Blo 1711056 35137385 := bstep (se 2 (by rfl) ⟨13176519, by rfl⟩ : syracuseStep 35137385 = 26353039) B26353039
theorem B3655631 : Blo 1711056 3655631 := bstep (se 1 (by rfl) ⟨2741723, by rfl⟩ : syracuseStep 3655631 = 5483447) B5483447
theorem B16459757 : Blo 1711056 16459757 := bstep (se 3 (by rfl) ⟨3086204, by rfl⟩ : syracuseStep 16459757 = 6172409) B6172409
theorem B20826193 : Blo 1711056 20826193 := bstep (se 2 (by rfl) ⟨7809822, by rfl⟩ : syracuseStep 20826193 = 15619645) B15619645
theorem B5556505 : Blo 1711056 5556505 := bstep (se 2 (by rfl) ⟨2083689, by rfl⟩ : syracuseStep 5556505 = 4167379) B4167379
theorem B24684911 : Blo 1711056 24684911 := bstep (se 1 (by rfl) ⟨18513683, by rfl⟩ : syracuseStep 24684911 = 37027367) B37027367
theorem B3852719 : Blo 1711056 3852719 := bstep (se 1 (by rfl) ⟨2889539, by rfl⟩ : syracuseStep 3852719 = 5779079) B5779079
theorem B3852755 : Blo 1711056 3852755 := bstep (se 1 (by rfl) ⟨2889566, by rfl⟩ : syracuseStep 3852755 = 5779133) B5779133
theorem B9751013 : Blo 1711056 9751013 := bstep (se 4 (by rfl) ⟨914157, by rfl⟩ : syracuseStep 9751013 = 1828315) B1828315
theorem B14633459 : Blo 1711056 14633459 := bstep (se 1 (by rfl) ⟨10975094, by rfl⟩ : syracuseStep 14633459 = 21950189) B21950189
theorem B3852863 : Blo 1711056 3852863 := bstep (se 1 (by rfl) ⟨2889647, by rfl⟩ : syracuseStep 3852863 = 5779295) B5779295
theorem B2566727 : Blo 1711056 2566727 := bstep (se 1 (by rfl) ⟨1925045, by rfl⟩ : syracuseStep 2566727 = 3850091) B3850091
theorem B14625359 : Blo 1711056 14625359 := bstep (se 1 (by rfl) ⟨10969019, by rfl⟩ : syracuseStep 14625359 = 21938039) B21938039
theorem B5777999 : Blo 1711056 5777999 := bstep (se 1 (by rfl) ⟨4333499, by rfl⟩ : syracuseStep 5777999 = 8666999) B8666999
theorem B2566763 : Blo 1711056 2566763 := bstep (se 1 (by rfl) ⟨1925072, by rfl⟩ : syracuseStep 2566763 = 3850145) B3850145
theorem B9251435 : Blo 1711056 9251435 := bstep (se 1 (by rfl) ⟨6938576, by rfl⟩ : syracuseStep 9251435 = 13877153) B13877153
theorem B3852971 : Blo 1711056 3852971 := bstep (se 1 (by rfl) ⟨2889728, by rfl⟩ : syracuseStep 3852971 = 5779457) B5779457
theorem B10414871 : Blo 1711056 10414871 := bstep (se 1 (by rfl) ⟨7811153, by rfl⟩ : syracuseStep 10414871 = 15622307) B15622307
theorem B2566991 : Blo 1711056 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B8670077 : Blo 1711056 8670077 := bstep (se 3 (by rfl) ⟨1625639, by rfl⟩ : syracuseStep 8670077 = 3251279) B3251279
theorem B8227727 : Blo 1711056 8227727 := bstep (se 1 (by rfl) ⟨6170795, by rfl⟩ : syracuseStep 8227727 = 12341591) B12341591
theorem B46836701 : Blo 1711056 46836701 := bstep (se 3 (by rfl) ⟨8781881, by rfl⟩ : syracuseStep 46836701 = 17563763) B17563763
theorem B3656801 : Blo 1711056 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B2927759 : Blo 1711056 2927759 := bstep (se 1 (by rfl) ⟨2195819, by rfl⟩ : syracuseStep 2927759 = 4391639) B4391639
theorem B3853511 : Blo 1711056 3853511 := bstep (se 1 (by rfl) ⟨2890133, by rfl⟩ : syracuseStep 3853511 = 5780267) B5780267
theorem B2567387 : Blo 1711056 2567387 := bstep (se 1 (by rfl) ⟨1925540, by rfl⟩ : syracuseStep 2567387 = 3851081) B3851081
theorem B14626109 : Blo 1711056 14626109 := bstep (se 3 (by rfl) ⟨2742395, by rfl⟩ : syracuseStep 14626109 = 5484791) B5484791
theorem B15830387 : Blo 1711056 15830387 := bstep (se 1 (by rfl) ⟨11872790, by rfl⟩ : syracuseStep 15830387 = 23745581) B23745581
theorem B6499703 : Blo 1711056 6499703 := bstep (se 1 (by rfl) ⟨4874777, by rfl⟩ : syracuseStep 6499703 = 9749555) B9749555
theorem B3853691 : Blo 1711056 3853691 := bstep (se 1 (by rfl) ⟨2890268, by rfl⟩ : syracuseStep 3853691 = 5780537) B5780537
theorem B2567561 : Blo 1711056 2567561 := bstep (se 2 (by rfl) ⟨962835, by rfl⟩ : syracuseStep 2567561 = 1925671) B1925671
theorem B3853817 : Blo 1711056 3853817 := bstep (se 2 (by rfl) ⟨1445181, by rfl⟩ : syracuseStep 3853817 = 2890363) B2890363
theorem B7409161 : Blo 1711056 7409161 := bstep (se 2 (by rfl) ⟨2778435, by rfl⟩ : syracuseStep 7409161 = 5556871) B5556871
theorem B3853907 : Blo 1711056 3853907 := bstep (se 1 (by rfl) ⟨2890430, by rfl⟩ : syracuseStep 3853907 = 5780861) B5780861
theorem B2567915 : Blo 1711056 2567915 := bstep (se 1 (by rfl) ⟨1925936, by rfl⟩ : syracuseStep 2567915 = 3851873) B3851873
theorem B8662787 : Blo 1711056 8662787 := bstep (se 1 (by rfl) ⟨6497090, by rfl⟩ : syracuseStep 8662787 = 12994181) B12994181
theorem B3854087 : Blo 1711056 3854087 := bstep (se 1 (by rfl) ⟨2890565, by rfl⟩ : syracuseStep 3854087 = 5781131) B5781131
theorem B2436905 : Blo 1711056 2436905 := bstep (se 2 (by rfl) ⟨913839, by rfl⟩ : syracuseStep 2436905 = 1827679) B1827679
theorem B5779241 : Blo 1711056 5779241 := bstep (se 2 (by rfl) ⟨2167215, by rfl⟩ : syracuseStep 5779241 = 4334431) B4334431
theorem B2166583 : Blo 1711056 2166583 := bstep (se 1 (by rfl) ⟨1624937, by rfl⟩ : syracuseStep 2166583 = 3249875) B3249875
theorem B2887481 : Blo 1711056 2887481 := bstep (se 2 (by rfl) ⟨1082805, by rfl⟩ : syracuseStep 2887481 = 2165611) B2165611
theorem B8671049 : Blo 1711056 8671049 := bstep (se 2 (by rfl) ⟨3251643, by rfl⟩ : syracuseStep 8671049 = 6503287) B6503287
theorem B7917419 : Blo 1711056 7917419 := bstep (se 1 (by rfl) ⟨5938064, by rfl⟩ : syracuseStep 7917419 = 11876129) B11876129
theorem B2568143 : Blo 1711056 2568143 := bstep (se 1 (by rfl) ⟨1926107, by rfl⟩ : syracuseStep 2568143 = 3852215) B3852215
theorem B70250449 : Blo 1711056 70250449 := bstep (se 2 (by rfl) ⟨26343918, by rfl⟩ : syracuseStep 70250449 = 52687837) B52687837
theorem B8229073 : Blo 1711056 8229073 := bstep (se 2 (by rfl) ⟨3085902, by rfl⟩ : syracuseStep 8229073 = 6171805) B6171805
theorem B2167003 : Blo 1711056 2167003 := bstep (se 1 (by rfl) ⟨1625252, by rfl⟩ : syracuseStep 2167003 = 3250505) B3250505
theorem B2568539 : Blo 1711056 2568539 := bstep (se 1 (by rfl) ⟨1926404, by rfl⟩ : syracuseStep 2568539 = 3852809) B3852809
theorem B2437543 : Blo 1711056 2437543 := bstep (se 1 (by rfl) ⟨1828157, by rfl⟩ : syracuseStep 2437543 = 3656315) B3656315
theorem B2568767 : Blo 1711056 2568767 := bstep (se 1 (by rfl) ⟨1926575, by rfl⟩ : syracuseStep 2568767 = 3853151) B3853151
theorem B2740807 : Blo 1711056 2740807 := bstep (se 1 (by rfl) ⟨2055605, by rfl⟩ : syracuseStep 2740807 = 4111211) B4111211
theorem B2568887 : Blo 1711056 2568887 := bstep (se 1 (by rfl) ⟨1926665, by rfl⟩ : syracuseStep 2568887 = 3853331) B3853331
theorem B21951161 : Blo 1711056 21951161 := bstep (se 2 (by rfl) ⟨8231685, by rfl⟩ : syracuseStep 21951161 = 16463371) B16463371
theorem B2888527 : Blo 1711056 2888527 := bstep (se 1 (by rfl) ⟨2166395, by rfl⟩ : syracuseStep 2888527 = 4332791) B4332791
theorem B6591311 : Blo 1711056 6591311 := bstep (se 1 (by rfl) ⟨4943483, by rfl⟩ : syracuseStep 6591311 = 9886967) B9886967
theorem B2569115 : Blo 1711056 2569115 := bstep (se 1 (by rfl) ⟨1926836, by rfl⟩ : syracuseStep 2569115 = 3853673) B3853673
theorem B14627749 : Blo 1711056 14627749 := bstep (se 4 (by rfl) ⟨1371351, by rfl⟩ : syracuseStep 14627749 = 2742703) B2742703
theorem B3806171 : Blo 1711056 3806171 := bstep (se 1 (by rfl) ⟨2854628, by rfl⟩ : syracuseStep 3806171 = 5709257) B5709257
theorem B8672345 : Blo 1711056 8672345 := bstep (se 2 (by rfl) ⟨3252129, by rfl⟩ : syracuseStep 8672345 = 6504259) B6504259
theorem B5485715 : Blo 1711056 5485715 := bstep (se 1 (by rfl) ⟨4114286, by rfl⟩ : syracuseStep 5485715 = 8228573) B8228573
theorem B2438363 : Blo 1711056 2438363 := bstep (se 1 (by rfl) ⟨1828772, by rfl⟩ : syracuseStep 2438363 = 3657545) B3657545
theorem B10974503 : Blo 1711056 10974503 := bstep (se 1 (by rfl) ⟨8230877, by rfl⟩ : syracuseStep 10974503 = 16461755) B16461755
theorem B30070055 : Blo 1711056 30070055 := bstep (se 1 (by rfl) ⟨22552541, by rfl⟩ : syracuseStep 30070055 = 45105083) B45105083
theorem B2569511 : Blo 1711056 2569511 := bstep (se 1 (by rfl) ⟨1927133, by rfl⟩ : syracuseStep 2569511 = 3854267) B3854267
theorem B8230187 : Blo 1711056 8230187 := bstep (se 1 (by rfl) ⟨6172640, by rfl⟩ : syracuseStep 8230187 = 12345281) B12345281
theorem B8664407 : Blo 1711056 8664407 := bstep (se 1 (by rfl) ⟨6498305, by rfl⟩ : syracuseStep 8664407 = 12996611) B12996611
theorem B2741627 : Blo 1711056 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B2889209 : Blo 1711056 2889209 := bstep (se 2 (by rfl) ⟨1083453, by rfl⟩ : syracuseStep 2889209 = 2166907) B2166907
theorem B2889479 : Blo 1711056 2889479 := bstep (se 1 (by rfl) ⟨2167109, by rfl⟩ : syracuseStep 2889479 = 4334219) B4334219
theorem B18519995 : Blo 1711056 18519995 := bstep (se 1 (by rfl) ⟨13889996, by rfl⟩ : syracuseStep 18519995 = 27779993) B27779993
theorem B5781455 : Blo 1711056 5781455 := bstep (se 1 (by rfl) ⟨4336091, by rfl⟩ : syracuseStep 5781455 = 8672183) B8672183
theorem B8665217 : Blo 1711056 8665217 := bstep (se 2 (by rfl) ⟨3249456, by rfl⟩ : syracuseStep 8665217 = 6498913) B6498913
theorem B4626713 : Blo 1711056 4626713 := bstep (se 2 (by rfl) ⟨1735017, by rfl⟩ : syracuseStep 4626713 = 3470035) B3470035
theorem B3250543 : Blo 1711056 3250543 := bstep (se 1 (by rfl) ⟨2437907, by rfl⟩ : syracuseStep 3250543 = 4875815) B4875815
theorem B7313807 : Blo 1711056 7313807 := bstep (se 1 (by rfl) ⟨5485355, by rfl⟩ : syracuseStep 7313807 = 10970711) B10970711
theorem B4331951 : Blo 1711056 4331951 := bstep (se 1 (by rfl) ⟨3248963, by rfl⟩ : syracuseStep 4331951 = 6497927) B6497927
theorem B8337875 : Blo 1711056 8337875 := bstep (se 1 (by rfl) ⟨6253406, by rfl⟩ : syracuseStep 8337875 = 12506813) B12506813
theorem B4332001 : Blo 1711056 4332001 := bstep (se 2 (by rfl) ⟨1624500, by rfl⟩ : syracuseStep 4332001 = 3249001) B3249001
theorem B2890235 : Blo 1711056 2890235 := bstep (se 1 (by rfl) ⟨2167676, by rfl⟩ : syracuseStep 2890235 = 4335353) B4335353
theorem B15620845 : Blo 1711056 15620845 := bstep (se 3 (by rfl) ⟨2928908, by rfl⟩ : syracuseStep 15620845 = 5857817) B5857817
theorem B4873115 : Blo 1711056 4873115 := bstep (se 1 (by rfl) ⟨3654836, by rfl⟩ : syracuseStep 4873115 = 7309673) B7309673
theorem B8666027 : Blo 1711056 8666027 := bstep (se 1 (by rfl) ⟨6499520, by rfl⟩ : syracuseStep 8666027 = 12999041) B12999041
theorem B13007789 : Blo 1711056 13007789 := bstep (se 3 (by rfl) ⟨2438960, by rfl⟩ : syracuseStep 13007789 = 4877921) B4877921
theorem B2890667 : Blo 1711056 2890667 := bstep (se 1 (by rfl) ⟨2168000, by rfl⟩ : syracuseStep 2890667 = 4336001) B4336001
theorem B1711079 : Blo 1711056 1711079 := bstep (se 1 (by rfl) ⟨1283309, by rfl⟩ : syracuseStep 1711079 = 2566619) B2566619
theorem B4873355 : Blo 1711056 4873355 := bstep (se 1 (by rfl) ⟨3655016, by rfl⟩ : syracuseStep 4873355 = 7310033) B7310033
theorem B1711391 : Blo 1711056 1711391 := bstep (se 1 (by rfl) ⟨1283543, by rfl⟩ : syracuseStep 1711391 = 2567087) B2567087
theorem B3472679 : Blo 1711056 3472679 := bstep (se 1 (by rfl) ⟨2604509, by rfl⟩ : syracuseStep 3472679 = 5209019) B5209019
theorem B1711451 : Blo 1711056 1711451 := bstep (se 1 (by rfl) ⟨1283588, by rfl⟩ : syracuseStep 1711451 = 2567177) B2567177
theorem B1711471 : Blo 1711056 1711471 := bstep (se 1 (by rfl) ⟨1283603, by rfl⟩ : syracuseStep 1711471 = 2567207) B2567207
theorem B4332923 : Blo 1711056 4332923 := bstep (se 1 (by rfl) ⟨3249692, by rfl⟩ : syracuseStep 4332923 = 6499385) B6499385
theorem B1711527 : Blo 1711056 1711527 := bstep (se 1 (by rfl) ⟨1283645, by rfl⟩ : syracuseStep 1711527 = 2567291) B2567291
theorem B13172183 : Blo 1711056 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B1711611 : Blo 1711056 1711611 := bstep (se 1 (by rfl) ⟨1283708, by rfl⟩ : syracuseStep 1711611 = 2567417) B2567417
theorem B1711679 : Blo 1711056 1711679 := bstep (se 1 (by rfl) ⟨1283759, by rfl⟩ : syracuseStep 1711679 = 2567519) B2567519
theorem B1711687 : Blo 1711056 1711687 := bstep (se 1 (by rfl) ⟨1283765, by rfl⟩ : syracuseStep 1711687 = 2567531) B2567531
theorem B1736263 : Blo 1711056 1736263 := bstep (se 1 (by rfl) ⟨1302197, by rfl⟩ : syracuseStep 1736263 = 2604395) B2604395
theorem B14630483 : Blo 1711056 14630483 := bstep (se 1 (by rfl) ⟨10972862, by rfl⟩ : syracuseStep 14630483 = 21945725) B21945725
theorem B8781473 : Blo 1711056 8781473 := bstep (se 2 (by rfl) ⟨3293052, by rfl⟩ : syracuseStep 8781473 = 6586105) B6586105
theorem B7315105 : Blo 1711056 7315105 := bstep (se 2 (by rfl) ⟨2743164, by rfl⟩ : syracuseStep 7315105 = 5486329) B5486329
theorem B1711839 : Blo 1711056 1711839 := bstep (se 1 (by rfl) ⟨1283879, by rfl⟩ : syracuseStep 1711839 = 2567759) B2567759
theorem B5775083 : Blo 1711056 5775083 := bstep (se 1 (by rfl) ⟨4331312, by rfl⟩ : syracuseStep 5775083 = 8662625) B8662625
theorem B1711919 : Blo 1711056 1711919 := bstep (se 1 (by rfl) ⟨1283939, by rfl⟩ : syracuseStep 1711919 = 2567879) B2567879
theorem B105430837 : Blo 1711056 105430837 := bstep (se 5 (by rfl) ⟨4942070, by rfl⟩ : syracuseStep 105430837 = 9884141) B9884141
theorem B8224573 : Blo 1711056 8224573 := bstep (se 3 (by rfl) ⟨1542107, by rfl⟩ : syracuseStep 8224573 = 3084215) B3084215
theorem B7413565 : Blo 1711056 7413565 := bstep (se 3 (by rfl) ⟨1390043, by rfl⟩ : syracuseStep 7413565 = 2780087) B2780087
theorem B32898905 : Blo 1711056 32898905 := bstep (se 2 (by rfl) ⟨12337089, by rfl⟩ : syracuseStep 32898905 = 24674179) B24674179
theorem B15621983 : Blo 1711056 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B1712027 : Blo 1711056 1712027 := bstep (se 1 (by rfl) ⟨1284020, by rfl⟩ : syracuseStep 1712027 = 2568041) B2568041
theorem B1712079 : Blo 1711056 1712079 := bstep (se 1 (by rfl) ⟨1284059, by rfl⟩ : syracuseStep 1712079 = 2568119) B2568119
theorem B1925095 : Blo 1711056 1925095 := bstep (se 1 (by rfl) ⟨1443821, by rfl⟩ : syracuseStep 1925095 = 2887643) B2887643
theorem B1712103 : Blo 1711056 1712103 := bstep (se 1 (by rfl) ⟨1284077, by rfl⟩ : syracuseStep 1712103 = 2568155) B2568155
theorem B1712359 : Blo 1711056 1712359 := bstep (se 1 (by rfl) ⟨1284269, by rfl⟩ : syracuseStep 1712359 = 2568539) B2568539
theorem B7807357 : Blo 1711056 7807357 := bstep (se 3 (by rfl) ⟨1463879, by rfl⟩ : syracuseStep 7807357 = 2927759) B2927759
theorem B1712511 : Blo 1711056 1712511 := bstep (se 1 (by rfl) ⟨1284383, by rfl⟩ : syracuseStep 1712511 = 2568767) B2568767
theorem B3850703 : Blo 1711056 3850703 := bstep (se 1 (by rfl) ⟨2888027, by rfl⟩ : syracuseStep 3850703 = 5776055) B5776055
theorem B1712591 : Blo 1711056 1712591 := bstep (se 1 (by rfl) ⟨1284443, by rfl⟩ : syracuseStep 1712591 = 2568887) B2568887
theorem B4334057 : Blo 1711056 4334057 := bstep (se 2 (by rfl) ⟨1625271, by rfl⟩ : syracuseStep 4334057 = 3250543) B3250543
theorem B1712743 : Blo 1711056 1712743 := bstep (se 1 (by rfl) ⟨1284557, by rfl⟩ : syracuseStep 1712743 = 2569115) B2569115
theorem B9749099 : Blo 1711056 9749099 := bstep (se 1 (by rfl) ⟨7311824, by rfl⟩ : syracuseStep 9749099 = 14623649) B14623649
theorem B5776001 : Blo 1711056 5776001 := bstep (se 2 (by rfl) ⟨2166000, by rfl⟩ : syracuseStep 5776001 = 4332001) B4332001
theorem B4875005 : Blo 1711056 4875005 := bstep (se 3 (by rfl) ⟨914063, by rfl⟩ : syracuseStep 4875005 = 1828127) B1828127
theorem B3654409 : Blo 1711056 3654409 := bstep (se 2 (by rfl) ⟨1370403, by rfl⟩ : syracuseStep 3654409 = 2740807) B2740807
theorem B7316335 : Blo 1711056 7316335 := bstep (se 1 (by rfl) ⟨5487251, by rfl⟩ : syracuseStep 7316335 = 10974503) B10974503
theorem B20046703 : Blo 1711056 20046703 := bstep (se 1 (by rfl) ⟨15035027, by rfl⟩ : syracuseStep 20046703 = 30070055) B30070055
theorem B1713007 : Blo 1711056 1713007 := bstep (se 1 (by rfl) ⟨1284755, by rfl⟩ : syracuseStep 1713007 = 2569511) B2569511
theorem B5776271 : Blo 1711056 5776271 := bstep (se 1 (by rfl) ⟨4332203, by rfl⟩ : syracuseStep 5776271 = 8664407) B8664407
theorem B1926139 : Blo 1711056 1926139 := bstep (se 1 (by rfl) ⟨1444604, by rfl⟩ : syracuseStep 1926139 = 2889209) B2889209
theorem B3851369 : Blo 1711056 3851369 := bstep (se 2 (by rfl) ⟨1444263, by rfl⟩ : syracuseStep 3851369 = 2888527) B2888527
theorem B1926319 : Blo 1711056 1926319 := bstep (se 1 (by rfl) ⟨1444739, by rfl⟩ : syracuseStep 1926319 = 2889479) B2889479
theorem B22234333 : Blo 1711056 22234333 := bstep (se 3 (by rfl) ⟨4168937, by rfl⟩ : syracuseStep 22234333 = 8337875) B8337875
theorem B12346663 : Blo 1711056 12346663 := bstep (se 1 (by rfl) ⟨9259997, by rfl⟩ : syracuseStep 12346663 = 18519995) B18519995
theorem B5776811 : Blo 1711056 5776811 := bstep (se 1 (by rfl) ⟨4332608, by rfl⟩ : syracuseStep 5776811 = 8665217) B8665217
theorem B4875871 : Blo 1711056 4875871 := bstep (se 1 (by rfl) ⟨3656903, by rfl⟩ : syracuseStep 4875871 = 7313807) B7313807
theorem B1926823 : Blo 1711056 1926823 := bstep (se 1 (by rfl) ⟨1445117, by rfl⟩ : syracuseStep 1926823 = 2890235) B2890235
theorem B9750239 : Blo 1711056 9750239 := bstep (se 1 (by rfl) ⟨7312679, by rfl⟩ : syracuseStep 9750239 = 14625359) B14625359
theorem B3851999 : Blo 1711056 3851999 := bstep (se 1 (by rfl) ⟨2888999, by rfl⟩ : syracuseStep 3851999 = 5777999) B5777999
theorem B5777351 : Blo 1711056 5777351 := bstep (se 1 (by rfl) ⟨4333013, by rfl⟩ : syracuseStep 5777351 = 8666027) B8666027
theorem B1927111 : Blo 1711056 1927111 := bstep (se 1 (by rfl) ⟨1445333, by rfl⟩ : syracuseStep 1927111 = 2890667) B2890667
theorem B6498413 : Blo 1711056 6498413 := bstep (se 3 (by rfl) ⟨1218452, by rfl⟩ : syracuseStep 6498413 = 2436905) B2436905
theorem B9750739 : Blo 1711056 9750739 := bstep (se 1 (by rfl) ⟨7313054, by rfl⟩ : syracuseStep 9750739 = 14626109) B14626109
theorem B10553591 : Blo 1711056 10553591 := bstep (se 1 (by rfl) ⟨7915193, by rfl⟩ : syracuseStep 10553591 = 15830387) B15830387
theorem B3852827 : Blo 1711056 3852827 := bstep (se 1 (by rfl) ⟨2889620, by rfl⟩ : syracuseStep 3852827 = 5779241) B5779241
theorem B21932603 : Blo 1711056 21932603 := bstep (se 1 (by rfl) ⟨16449452, by rfl⟩ : syracuseStep 21932603 = 32898905) B32898905
theorem B10414655 : Blo 1711056 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B5278279 : Blo 1711056 5278279 := bstep (se 1 (by rfl) ⟨3958709, by rfl⟩ : syracuseStep 5278279 = 7917419) B7917419
theorem B2566793 : Blo 1711056 2566793 := bstep (se 2 (by rfl) ⟨962547, by rfl⟩ : syracuseStep 2566793 = 1925095) B1925095
theorem B5778107 : Blo 1711056 5778107 := bstep (se 1 (by rfl) ⟨4333580, by rfl⟩ : syracuseStep 5778107 = 8667161) B8667161
theorem B2566967 : Blo 1711056 2566967 := bstep (se 1 (by rfl) ⟨1925225, by rfl⟩ : syracuseStep 2566967 = 3850451) B3850451
theorem B2567003 : Blo 1711056 2567003 := bstep (se 1 (by rfl) ⟨1925252, by rfl⟩ : syracuseStep 2567003 = 3850505) B3850505
theorem B10972097 : Blo 1711056 10972097 := bstep (se 2 (by rfl) ⟨4114536, by rfl⟩ : syracuseStep 10972097 = 8229073) B8229073
theorem B2567147 : Blo 1711056 2567147 := bstep (se 1 (by rfl) ⟨1925360, by rfl⟩ : syracuseStep 2567147 = 3850721) B3850721
theorem B7408673 : Blo 1711056 7408673 := bstep (se 2 (by rfl) ⟨2778252, by rfl⟩ : syracuseStep 7408673 = 5556505) B5556505
theorem B14634107 : Blo 1711056 14634107 := bstep (se 1 (by rfl) ⟨10975580, by rfl⟩ : syracuseStep 14634107 = 21951161) B21951161
theorem B4877455 : Blo 1711056 4877455 := bstep (se 1 (by rfl) ⟨3658091, by rfl⟩ : syracuseStep 4877455 = 7316183) B7316183
theorem B2567351 : Blo 1711056 2567351 := bstep (se 1 (by rfl) ⟨1925513, by rfl⟩ : syracuseStep 2567351 = 3851027) B3851027
theorem B4394207 : Blo 1711056 4394207 := bstep (se 1 (by rfl) ⟨3295655, by rfl⟩ : syracuseStep 4394207 = 6591311) B6591311
theorem B2567591 : Blo 1711056 2567591 := bstep (se 1 (by rfl) ⟨1925693, by rfl⟩ : syracuseStep 2567591 = 3851387) B3851387
theorem B3657143 : Blo 1711056 3657143 := bstep (se 1 (by rfl) ⟨2742857, by rfl⟩ : syracuseStep 3657143 = 5485715) B5485715
theorem B9260477 : Blo 1711056 9260477 := bstep (se 3 (by rfl) ⟨1736339, by rfl⟩ : syracuseStep 9260477 = 3472679) B3472679
theorem B9252343 : Blo 1711056 9252343 := bstep (se 1 (by rfl) ⟨6939257, by rfl⟩ : syracuseStep 9252343 = 13878515) B13878515
theorem B2567675 : Blo 1711056 2567675 := bstep (se 1 (by rfl) ⟨1925756, by rfl⟩ : syracuseStep 2567675 = 3851513) B3851513
theorem B2567771 : Blo 1711056 2567771 := bstep (se 1 (by rfl) ⟨1925828, by rfl⟩ : syracuseStep 2567771 = 3851657) B3851657
theorem B20827793 : Blo 1711056 20827793 := bstep (se 2 (by rfl) ⟨7810422, by rfl⟩ : syracuseStep 20827793 = 15620845) B15620845
theorem B7311005 : Blo 1711056 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B2567855 : Blo 1711056 2567855 := bstep (se 1 (by rfl) ⟨1925891, by rfl⟩ : syracuseStep 2567855 = 3851783) B3851783
theorem B37007117 : Blo 1711056 37007117 := bstep (se 3 (by rfl) ⟨6938834, by rfl⟩ : syracuseStep 37007117 = 13877669) B13877669
theorem B2567975 : Blo 1711056 2567975 := bstep (se 1 (by rfl) ⟨1925981, by rfl⟩ : syracuseStep 2567975 = 3851963) B3851963
theorem B2568059 : Blo 1711056 2568059 := bstep (se 1 (by rfl) ⟨1926044, by rfl⟩ : syracuseStep 2568059 = 3852089) B3852089
theorem B23424923 : Blo 1711056 23424923 := bstep (se 1 (by rfl) ⟨17568692, by rfl⟩ : syracuseStep 23424923 = 35137385) B35137385
theorem B3854303 : Blo 1711056 3854303 := bstep (se 1 (by rfl) ⟨2890727, by rfl⟩ : syracuseStep 3854303 = 5781455) B5781455
theorem B10973171 : Blo 1711056 10973171 := bstep (se 1 (by rfl) ⟨8229878, by rfl⟩ : syracuseStep 10973171 = 16459757) B16459757
theorem B3084475 : Blo 1711056 3084475 := bstep (se 1 (by rfl) ⟨2313356, by rfl⟩ : syracuseStep 3084475 = 4626713) B4626713
theorem B2887967 : Blo 1711056 2887967 := bstep (se 1 (by rfl) ⟨2165975, by rfl⟩ : syracuseStep 2887967 = 4331951) B4331951
theorem B2568479 : Blo 1711056 2568479 := bstep (se 1 (by rfl) ⟨1926359, by rfl⟩ : syracuseStep 2568479 = 3852719) B3852719
theorem B2568503 : Blo 1711056 2568503 := bstep (se 1 (by rfl) ⟨1926377, by rfl⟩ : syracuseStep 2568503 = 3852755) B3852755
theorem B6500675 : Blo 1711056 6500675 := bstep (se 1 (by rfl) ⟨4875506, by rfl⟩ : syracuseStep 6500675 = 9751013) B9751013
theorem B2568575 : Blo 1711056 2568575 := bstep (se 1 (by rfl) ⟨1926431, by rfl⟩ : syracuseStep 2568575 = 3852863) B3852863
theorem B2568647 : Blo 1711056 2568647 := bstep (se 1 (by rfl) ⟨1926485, by rfl⟩ : syracuseStep 2568647 = 3852971) B3852971
theorem B6500857 : Blo 1711056 6500857 := bstep (se 2 (by rfl) ⟨2437821, by rfl⟩ : syracuseStep 6500857 = 4875643) B4875643
theorem B6943247 : Blo 1711056 6943247 := bstep (se 1 (by rfl) ⟨5207435, by rfl⟩ : syracuseStep 6943247 = 10414871) B10414871
theorem B16462369 : Blo 1711056 16462369 := bstep (se 2 (by rfl) ⟨6173388, by rfl⟩ : syracuseStep 16462369 = 12346777) B12346777
theorem B5780051 : Blo 1711056 5780051 := bstep (se 1 (by rfl) ⟨4335038, by rfl⟩ : syracuseStep 5780051 = 8670077) B8670077
theorem B5485151 : Blo 1711056 5485151 := bstep (se 1 (by rfl) ⟨4113863, by rfl⟩ : syracuseStep 5485151 = 8227727) B8227727
theorem B3248743 : Blo 1711056 3248743 := bstep (se 1 (by rfl) ⟨2436557, by rfl⟩ : syracuseStep 3248743 = 4873115) B4873115
theorem B8671859 : Blo 1711056 8671859 := bstep (se 1 (by rfl) ⟨6503894, by rfl⟩ : syracuseStep 8671859 = 13007789) B13007789
theorem B31224467 : Blo 1711056 31224467 := bstep (se 1 (by rfl) ⟨23418350, by rfl⟩ : syracuseStep 31224467 = 46836701) B46836701
theorem B2437867 : Blo 1711056 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B3248903 : Blo 1711056 3248903 := bstep (se 1 (by rfl) ⟨2436677, by rfl⟩ : syracuseStep 3248903 = 4873355) B4873355
theorem B2315017 : Blo 1711056 2315017 := bstep (se 2 (by rfl) ⟨868131, by rfl⟩ : syracuseStep 2315017 = 1736263) B1736263
theorem B2569001 : Blo 1711056 2569001 := bstep (se 2 (by rfl) ⟨963375, by rfl⟩ : syracuseStep 2569001 = 1926751) B1926751
theorem B2569007 : Blo 1711056 2569007 := bstep (se 1 (by rfl) ⟨1926755, by rfl⟩ : syracuseStep 2569007 = 3853511) B3853511
theorem B9753473 : Blo 1711056 9753473 := bstep (se 2 (by rfl) ⟨3657552, by rfl⟩ : syracuseStep 9753473 = 7315105) B7315105
theorem B2888615 : Blo 1711056 2888615 := bstep (se 1 (by rfl) ⟨2166461, by rfl⟩ : syracuseStep 2888615 = 4332923) B4332923
theorem B2569127 : Blo 1711056 2569127 := bstep (se 1 (by rfl) ⟨1926845, by rfl⟩ : syracuseStep 2569127 = 3853691) B3853691
theorem B2569211 : Blo 1711056 2569211 := bstep (se 1 (by rfl) ⟨1926908, by rfl⟩ : syracuseStep 2569211 = 3853817) B3853817
theorem B9753655 : Blo 1711056 9753655 := bstep (se 1 (by rfl) ⟨7315241, by rfl⟩ : syracuseStep 9753655 = 14630483) B14630483
theorem B2569271 : Blo 1711056 2569271 := bstep (se 1 (by rfl) ⟨1926953, by rfl⟩ : syracuseStep 2569271 = 3853907) B3853907
theorem B2888777 : Blo 1711056 2888777 := bstep (se 2 (by rfl) ⟨1083291, by rfl⟩ : syracuseStep 2888777 = 2166583) B2166583
theorem B10966097 : Blo 1711056 10966097 := bstep (se 2 (by rfl) ⟨4112286, by rfl⟩ : syracuseStep 10966097 = 8224573) B8224573
theorem B9884753 : Blo 1711056 9884753 := bstep (se 2 (by rfl) ⟨3706782, by rfl⟩ : syracuseStep 9884753 = 7413565) B7413565
theorem B5854315 : Blo 1711056 5854315 := bstep (se 1 (by rfl) ⟨4390736, by rfl⟩ : syracuseStep 5854315 = 8781473) B8781473
theorem B2569391 : Blo 1711056 2569391 := bstep (se 1 (by rfl) ⟨1927043, by rfl⟩ : syracuseStep 2569391 = 3854087) B3854087
theorem B5780699 : Blo 1711056 5780699 := bstep (se 1 (by rfl) ⟨4335524, by rfl⟩ : syracuseStep 5780699 = 8671049) B8671049
theorem B27768257 : Blo 1711056 27768257 := bstep (se 2 (by rfl) ⟨10413096, by rfl⟩ : syracuseStep 27768257 = 20826193) B20826193
theorem B2889337 : Blo 1711056 2889337 := bstep (se 2 (by rfl) ⟨1083501, by rfl⟩ : syracuseStep 2889337 = 2167003) B2167003
theorem B4331191 : Blo 1711056 4331191 := bstep (se 1 (by rfl) ⟨3248393, by rfl⟩ : syracuseStep 4331191 = 6496787) B6496787
theorem B32905055 : Blo 1711056 32905055 := bstep (se 1 (by rfl) ⟨24678791, by rfl⟩ : syracuseStep 32905055 = 49357583) B49357583
theorem B3250057 : Blo 1711056 3250057 := bstep (se 2 (by rfl) ⟨1218771, by rfl⟩ : syracuseStep 3250057 = 2437543) B2437543
theorem B6502301 : Blo 1711056 6502301 := bstep (se 3 (by rfl) ⟨1219181, by rfl⟩ : syracuseStep 6502301 = 2438363) B2438363
theorem B4331495 : Blo 1711056 4331495 := bstep (se 1 (by rfl) ⟨3248621, by rfl⟩ : syracuseStep 4331495 = 6497243) B6497243
theorem B2537447 : Blo 1711056 2537447 := bstep (se 1 (by rfl) ⟨1903085, by rfl⟩ : syracuseStep 2537447 = 3806171) B3806171
theorem B31250447 : Blo 1711056 31250447 := bstep (se 1 (by rfl) ⟨23437835, by rfl⟩ : syracuseStep 31250447 = 46875671) B46875671
theorem B5781563 : Blo 1711056 5781563 := bstep (se 1 (by rfl) ⟨4336172, by rfl⟩ : syracuseStep 5781563 = 8672345) B8672345
theorem B2889823 : Blo 1711056 2889823 := bstep (se 1 (by rfl) ⟨2167367, by rfl⟩ : syracuseStep 2889823 = 4334735) B4334735
theorem B5486791 : Blo 1711056 5486791 := bstep (se 1 (by rfl) ⟨4115093, by rfl⟩ : syracuseStep 5486791 = 8230187) B8230187
theorem B5855465 : Blo 1711056 5855465 := bstep (se 2 (by rfl) ⟨2195799, by rfl⟩ : syracuseStep 5855465 = 4391599) B4391599
theorem B19503665 : Blo 1711056 19503665 := bstep (se 2 (by rfl) ⟨7313874, by rfl⟩ : syracuseStep 19503665 = 14627749) B14627749
theorem B8788531 : Blo 1711056 8788531 := bstep (se 1 (by rfl) ⟨6591398, by rfl⟩ : syracuseStep 8788531 = 13182797) B13182797
theorem B16456607 : Blo 1711056 16456607 := bstep (se 1 (by rfl) ⟨12342455, by rfl⟩ : syracuseStep 16456607 = 24684911) B24684911
theorem B9755639 : Blo 1711056 9755639 := bstep (se 1 (by rfl) ⟨7316729, by rfl⟩ : syracuseStep 9755639 = 14633459) B14633459
theorem B1711151 : Blo 1711056 1711151 := bstep (se 1 (by rfl) ⟨1283363, by rfl⟩ : syracuseStep 1711151 = 2566727) B2566727
theorem B1711175 : Blo 1711056 1711175 := bstep (se 1 (by rfl) ⟨1283381, by rfl⟩ : syracuseStep 1711175 = 2566763) B2566763
theorem B6167623 : Blo 1711056 6167623 := bstep (se 1 (by rfl) ⟨4625717, by rfl⟩ : syracuseStep 6167623 = 9251435) B9251435
theorem B1711327 : Blo 1711056 1711327 := bstep (se 1 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 1711327 = 2566991) B2566991
theorem B9878881 : Blo 1711056 9878881 := bstep (se 2 (by rfl) ⟨3704580, by rfl⟩ : syracuseStep 9878881 = 7409161) B7409161
theorem B1711591 : Blo 1711056 1711591 := bstep (se 1 (by rfl) ⟨1283693, by rfl⟩ : syracuseStep 1711591 = 2567387) B2567387
theorem B4333135 : Blo 1711056 4333135 := bstep (se 1 (by rfl) ⟨3249851, by rfl⟩ : syracuseStep 4333135 = 6499703) B6499703
theorem B1711707 : Blo 1711056 1711707 := bstep (se 1 (by rfl) ⟨1283780, by rfl⟩ : syracuseStep 1711707 = 2567561) B2567561
theorem B8781455 : Blo 1711056 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B140574449 : Blo 1711056 140574449 := bstep (se 2 (by rfl) ⟨52715418, by rfl⟩ : syracuseStep 140574449 = 105430837) B105430837
theorem B3850055 : Blo 1711056 3850055 := bstep (se 1 (by rfl) ⟨2887541, by rfl⟩ : syracuseStep 3850055 = 5775083) B5775083
theorem B1711943 : Blo 1711056 1711943 := bstep (se 1 (by rfl) ⟨1283957, by rfl⟩ : syracuseStep 1711943 = 2567915) B2567915
theorem B5775191 : Blo 1711056 5775191 := bstep (se 1 (by rfl) ⟨4331393, by rfl⟩ : syracuseStep 5775191 = 8662787) B8662787
theorem B1924987 : Blo 1711056 1924987 := bstep (se 1 (by rfl) ⟨1443740, by rfl⟩ : syracuseStep 1924987 = 2887481) B2887481
theorem B9748349 : Blo 1711056 9748349 := bstep (se 3 (by rfl) ⟨1827815, by rfl⟩ : syracuseStep 9748349 = 3655631) B3655631
theorem B93667265 : Blo 1711056 93667265 := bstep (se 2 (by rfl) ⟨35125224, by rfl⟩ : syracuseStep 93667265 = 70250449) B70250449
theorem B1712095 : Blo 1711056 1712095 := bstep (se 1 (by rfl) ⟨1284071, by rfl⟩ : syracuseStep 1712095 = 2568143) B2568143
theorem B1925311 : Blo 1711056 1925311 := bstep (se 1 (by rfl) ⟨1443983, by rfl⟩ : syracuseStep 1925311 = 2887967) B2887967
theorem B1712319 : Blo 1711056 1712319 := bstep (se 1 (by rfl) ⟨1284239, by rfl⟩ : syracuseStep 1712319 = 2568479) B2568479
theorem B1712335 : Blo 1711056 1712335 := bstep (se 1 (by rfl) ⟨1284251, by rfl⟩ : syracuseStep 1712335 = 2568503) B2568503
theorem B4333783 : Blo 1711056 4333783 := bstep (se 1 (by rfl) ⟨3250337, by rfl⟩ : syracuseStep 4333783 = 6500675) B6500675
theorem B4112633 : Blo 1711056 4112633 := bstep (se 2 (by rfl) ⟨1542237, by rfl⟩ : syracuseStep 4112633 = 3084475) B3084475
theorem B1712383 : Blo 1711056 1712383 := bstep (se 1 (by rfl) ⟨1284287, by rfl⟩ : syracuseStep 1712383 = 2568575) B2568575
theorem B7315721 : Blo 1711056 7315721 := bstep (se 2 (by rfl) ⟨2743395, by rfl⟩ : syracuseStep 7315721 = 5486791) B5486791
theorem B13000985 : Blo 1711056 13000985 := bstep (se 2 (by rfl) ⟨4875369, by rfl⟩ : syracuseStep 13000985 = 9750739) B9750739
theorem B1712431 : Blo 1711056 1712431 := bstep (se 1 (by rfl) ⟨1284323, by rfl⟩ : syracuseStep 1712431 = 2568647) B2568647
theorem B4628831 : Blo 1711056 4628831 := bstep (se 1 (by rfl) ⟨3471623, by rfl⟩ : syracuseStep 4628831 = 6943247) B6943247
theorem B3850667 : Blo 1711056 3850667 := bstep (se 1 (by rfl) ⟨2888000, by rfl⟩ : syracuseStep 3850667 = 5776001) B5776001
theorem B20816311 : Blo 1711056 20816311 := bstep (se 1 (by rfl) ⟨15612233, by rfl⟩ : syracuseStep 20816311 = 31224467) B31224467
theorem B1712667 : Blo 1711056 1712667 := bstep (se 1 (by rfl) ⟨1284500, by rfl⟩ : syracuseStep 1712667 = 2569001) B2569001
theorem B1712671 : Blo 1711056 1712671 := bstep (se 1 (by rfl) ⟨1284503, by rfl⟩ : syracuseStep 1712671 = 2569007) B2569007
theorem B3850847 : Blo 1711056 3850847 := bstep (se 1 (by rfl) ⟨2888135, by rfl⟩ : syracuseStep 3850847 = 5776271) B5776271
theorem B1925743 : Blo 1711056 1925743 := bstep (se 1 (by rfl) ⟨1444307, by rfl⟩ : syracuseStep 1925743 = 2888615) B2888615
theorem B1712751 : Blo 1711056 1712751 := bstep (se 1 (by rfl) ⟨1284563, by rfl⟩ : syracuseStep 1712751 = 2569127) B2569127
theorem B8667809 : Blo 1711056 8667809 := bstep (se 2 (by rfl) ⟨3250428, by rfl⟩ : syracuseStep 8667809 = 6500857) B6500857
theorem B1712807 : Blo 1711056 1712807 := bstep (se 1 (by rfl) ⟨1284605, by rfl⟩ : syracuseStep 1712807 = 2569211) B2569211
theorem B1712847 : Blo 1711056 1712847 := bstep (se 1 (by rfl) ⟨1284635, by rfl⟩ : syracuseStep 1712847 = 2569271) B2569271
theorem B1925851 : Blo 1711056 1925851 := bstep (se 1 (by rfl) ⟨1444388, by rfl⟩ : syracuseStep 1925851 = 2888777) B2888777
theorem B7037705 : Blo 1711056 7037705 := bstep (se 2 (by rfl) ⟨2639139, by rfl⟩ : syracuseStep 7037705 = 5278279) B5278279
theorem B1712927 : Blo 1711056 1712927 := bstep (se 1 (by rfl) ⟨1284695, by rfl⟩ : syracuseStep 1712927 = 2569391) B2569391
theorem B3851207 : Blo 1711056 3851207 := bstep (se 1 (by rfl) ⟨2888405, by rfl⟩ : syracuseStep 3851207 = 5776811) B5776811
theorem B13001957 : Blo 1711056 13001957 := bstep (se 4 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 13001957 = 2437867) B2437867
theorem B4334867 : Blo 1711056 4334867 := bstep (se 1 (by rfl) ⟨3251150, by rfl⟩ : syracuseStep 4334867 = 6502301) B6502301
theorem B3851567 : Blo 1711056 3851567 := bstep (se 1 (by rfl) ⟨2888675, by rfl⟩ : syracuseStep 3851567 = 5777351) B5777351
theorem B20833631 : Blo 1711056 20833631 := bstep (se 1 (by rfl) ⟨15625223, by rfl⟩ : syracuseStep 20833631 = 31250447) B31250447
theorem B13002443 : Blo 1711056 13002443 := bstep (se 1 (by rfl) ⟨9751832, by rfl⟩ : syracuseStep 13002443 = 19503665) B19503665
theorem B3852071 : Blo 1711056 3852071 := bstep (se 1 (by rfl) ⟨2889053, by rfl⟩ : syracuseStep 3852071 = 5778107) B5778107
theorem B10971071 : Blo 1711056 10971071 := bstep (se 1 (by rfl) ⟨8228303, by rfl⟩ : syracuseStep 10971071 = 16456607) B16456607
theorem B5777513 : Blo 1711056 5777513 := bstep (se 2 (by rfl) ⟨2166567, by rfl⟩ : syracuseStep 5777513 = 4333135) B4333135
theorem B3852449 : Blo 1711056 3852449 := bstep (se 2 (by rfl) ⟨1444668, by rfl⟩ : syracuseStep 3852449 = 2889337) B2889337
theorem B62466461 : Blo 1711056 62466461 := bstep (se 3 (by rfl) ⟨11712461, by rfl⟩ : syracuseStep 62466461 = 23424923) B23424923
theorem B2566649 : Blo 1711056 2566649 := bstep (se 2 (by rfl) ⟨962493, by rfl⟩ : syracuseStep 2566649 = 1924987) B1924987
theorem B2566703 : Blo 1711056 2566703 := bstep (se 1 (by rfl) ⟨1925027, by rfl⟩ : syracuseStep 2566703 = 3850055) B3850055
theorem B6498899 : Blo 1711056 6498899 := bstep (se 1 (by rfl) ⟨4874174, by rfl⟩ : syracuseStep 6498899 = 9748349) B9748349
theorem B3853097 : Blo 1711056 3853097 := bstep (se 2 (by rfl) ⟨1444911, by rfl⟩ : syracuseStep 3853097 = 2889823) B2889823
theorem B2567135 : Blo 1711056 2567135 := bstep (se 1 (by rfl) ⟨1925351, by rfl⟩ : syracuseStep 2567135 = 3850703) B3850703
theorem B3853367 : Blo 1711056 3853367 := bstep (se 1 (by rfl) ⟨2890025, by rfl⟩ : syracuseStep 3853367 = 5780051) B5780051
theorem B3656767 : Blo 1711056 3656767 := bstep (se 1 (by rfl) ⟨2742575, by rfl⟩ : syracuseStep 3656767 = 5485151) B5485151
theorem B6499399 : Blo 1711056 6499399 := bstep (se 1 (by rfl) ⟨4874549, by rfl⟩ : syracuseStep 6499399 = 9749099) B9749099
theorem B2165935 : Blo 1711056 2165935 := bstep (se 1 (by rfl) ⟨1624451, by rfl⟩ : syracuseStep 2165935 = 3248903) B3248903
theorem B11717885 : Blo 1711056 11717885 := bstep (se 3 (by rfl) ⟨2197103, by rfl⟩ : syracuseStep 11717885 = 4394207) B4394207
theorem B28142909 : Blo 1711056 28142909 := bstep (se 3 (by rfl) ⟨5276795, by rfl⟩ : syracuseStep 28142909 = 10553591) B10553591
theorem B21949825 : Blo 1711056 21949825 := bstep (se 2 (by rfl) ⟨8231184, by rfl⟩ : syracuseStep 21949825 = 16462369) B16462369
theorem B7310731 : Blo 1711056 7310731 := bstep (se 1 (by rfl) ⟨5483048, by rfl⟩ : syracuseStep 7310731 = 10966097) B10966097
theorem B6589835 : Blo 1711056 6589835 := bstep (se 1 (by rfl) ⟨4942376, by rfl⟩ : syracuseStep 6589835 = 9884753) B9884753
theorem B11718041 : Blo 1711056 11718041 := bstep (se 2 (by rfl) ⟨4394265, by rfl⟩ : syracuseStep 11718041 = 8788531) B8788531
theorem B2567579 : Blo 1711056 2567579 := bstep (se 1 (by rfl) ⟨1925684, by rfl⟩ : syracuseStep 2567579 = 3851369) B3851369
theorem B3853799 : Blo 1711056 3853799 := bstep (se 1 (by rfl) ⟨2890349, by rfl⟩ : syracuseStep 3853799 = 5780699) B5780699
theorem B6500159 : Blo 1711056 6500159 := bstep (se 1 (by rfl) ⟨4875119, by rfl⟩ : syracuseStep 6500159 = 9750239) B9750239
theorem B2567999 : Blo 1711056 2567999 := bstep (se 1 (by rfl) ⟨1925999, by rfl⟩ : syracuseStep 2567999 = 3851999) B3851999
theorem B2887663 : Blo 1711056 2887663 := bstep (se 1 (by rfl) ⟨2165747, by rfl⟩ : syracuseStep 2887663 = 4331495) B4331495
theorem B2568185 : Blo 1711056 2568185 := bstep (se 2 (by rfl) ⟨963069, by rfl⟩ : syracuseStep 2568185 = 1926139) B1926139
theorem B3854375 : Blo 1711056 3854375 := bstep (se 1 (by rfl) ⟨2890781, by rfl⟩ : syracuseStep 3854375 = 5781563) B5781563
theorem B13004873 : Blo 1711056 13004873 := bstep (se 2 (by rfl) ⟨4876827, by rfl⟩ : syracuseStep 13004873 = 9753655) B9753655
theorem B3903643 : Blo 1711056 3903643 := bstep (se 1 (by rfl) ⟨2927732, by rfl⟩ : syracuseStep 3903643 = 5855465) B5855465
theorem B2568425 : Blo 1711056 2568425 := bstep (se 2 (by rfl) ⟨963159, by rfl⟩ : syracuseStep 2568425 = 1926319) B1926319
theorem B2568551 : Blo 1711056 2568551 := bstep (se 1 (by rfl) ⟨1926413, by rfl⟩ : syracuseStep 2568551 = 3852827) B3852827
theorem B6943103 : Blo 1711056 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B16462217 : Blo 1711056 16462217 := bstep (se 2 (by rfl) ⟨6173331, by rfl⟩ : syracuseStep 16462217 = 12346663) B12346663
theorem B6501161 : Blo 1711056 6501161 := bstep (se 2 (by rfl) ⟨2437935, by rfl⟩ : syracuseStep 6501161 = 4875871) B4875871
theorem B2569097 : Blo 1711056 2569097 := bstep (se 2 (by rfl) ⟨963411, by rfl⟩ : syracuseStep 2569097 = 1926823) B1926823
theorem B2438095 : Blo 1711056 2438095 := bstep (se 1 (by rfl) ⟨1828571, by rfl⟩ : syracuseStep 2438095 = 3657143) B3657143
theorem B6173651 : Blo 1711056 6173651 := bstep (se 1 (by rfl) ⟨4630238, by rfl⟩ : syracuseStep 6173651 = 9260477) B9260477
theorem B5854303 : Blo 1711056 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B24671411 : Blo 1711056 24671411 := bstep (se 1 (by rfl) ⟨18503558, by rfl⟩ : syracuseStep 24671411 = 37007117) B37007117
theorem B2569481 : Blo 1711056 2569481 := bstep (se 2 (by rfl) ⟨963555, by rfl⟩ : syracuseStep 2569481 = 1927111) B1927111
theorem B62444843 : Blo 1711056 62444843 := bstep (se 1 (by rfl) ⟨46833632, by rfl⟩ : syracuseStep 62444843 = 93667265) B93667265
theorem B2569535 : Blo 1711056 2569535 := bstep (se 1 (by rfl) ⟨1927151, by rfl⟩ : syracuseStep 2569535 = 3854303) B3854303
theorem B2889371 : Blo 1711056 2889371 := bstep (se 1 (by rfl) ⟨2167028, by rfl⟩ : syracuseStep 2889371 = 4334057) B4334057
theorem B5781239 : Blo 1711056 5781239 := bstep (se 1 (by rfl) ⟨4335929, by rfl⟩ : syracuseStep 5781239 = 8671859) B8671859
theorem B10409809 : Blo 1711056 10409809 := bstep (se 2 (by rfl) ⟨3903678, by rfl⟩ : syracuseStep 10409809 = 7807357) B7807357
theorem B6502315 : Blo 1711056 6502315 := bstep (se 1 (by rfl) ⟨4876736, by rfl⟩ : syracuseStep 6502315 = 9753473) B9753473
theorem B4331657 : Blo 1711056 4331657 := bstep (se 2 (by rfl) ⟨1624371, by rfl⟩ : syracuseStep 4331657 = 3248743) B3248743
theorem B18512171 : Blo 1711056 18512171 := bstep (se 1 (by rfl) ⟨13884128, by rfl⟩ : syracuseStep 18512171 = 27768257) B27768257
theorem B4872545 : Blo 1711056 4872545 := bstep (se 2 (by rfl) ⟨1827204, by rfl⟩ : syracuseStep 4872545 = 3654409) B3654409
theorem B3086689 : Blo 1711056 3086689 := bstep (se 2 (by rfl) ⟨1157508, by rfl⟩ : syracuseStep 3086689 = 2315017) B2315017
theorem B9755113 : Blo 1711056 9755113 := bstep (se 2 (by rfl) ⟨3658167, by rfl⟩ : syracuseStep 9755113 = 7316335) B7316335
theorem B26728937 : Blo 1711056 26728937 := bstep (se 2 (by rfl) ⟨10023351, by rfl⟩ : syracuseStep 26728937 = 20046703) B20046703
theorem B21936703 : Blo 1711056 21936703 := bstep (se 1 (by rfl) ⟨16452527, by rfl⟩ : syracuseStep 21936703 = 32905055) B32905055
theorem B4332275 : Blo 1711056 4332275 := bstep (se 1 (by rfl) ⟨3249206, by rfl⟩ : syracuseStep 4332275 = 6498413) B6498413
theorem B8223497 : Blo 1711056 8223497 := bstep (se 2 (by rfl) ⟨3083811, by rfl⟩ : syracuseStep 8223497 = 6167623) B6167623
theorem B7805753 : Blo 1711056 7805753 := bstep (se 2 (by rfl) ⟨2927157, by rfl⟩ : syracuseStep 7805753 = 5854315) B5854315
theorem B6503273 : Blo 1711056 6503273 := bstep (se 2 (by rfl) ⟨2438727, by rfl⟩ : syracuseStep 6503273 = 4877455) B4877455
theorem B29645777 : Blo 1711056 29645777 := bstep (se 2 (by rfl) ⟨11117166, by rfl⟩ : syracuseStep 29645777 = 22234333) B22234333
theorem B14621735 : Blo 1711056 14621735 := bstep (se 1 (by rfl) ⟨10966301, by rfl⟩ : syracuseStep 14621735 = 21932603) B21932603
theorem B1711195 : Blo 1711056 1711195 := bstep (se 1 (by rfl) ⟨1283396, by rfl⟩ : syracuseStep 1711195 = 2566793) B2566793
theorem B13171841 : Blo 1711056 13171841 := bstep (se 2 (by rfl) ⟨4939440, by rfl⟩ : syracuseStep 13171841 = 9878881) B9878881
theorem B1711311 : Blo 1711056 1711311 := bstep (se 1 (by rfl) ⟨1283483, by rfl⟩ : syracuseStep 1711311 = 2566967) B2566967
theorem B7315447 : Blo 1711056 7315447 := bstep (se 1 (by rfl) ⟨5486585, by rfl⟩ : syracuseStep 7315447 = 10973171) B10973171
theorem B1711335 : Blo 1711056 1711335 := bstep (se 1 (by rfl) ⟨1283501, by rfl⟩ : syracuseStep 1711335 = 2567003) B2567003
theorem B7314731 : Blo 1711056 7314731 := bstep (se 1 (by rfl) ⟨5486048, by rfl⟩ : syracuseStep 7314731 = 10972097) B10972097
theorem B1711431 : Blo 1711056 1711431 := bstep (se 1 (by rfl) ⟨1283573, by rfl⟩ : syracuseStep 1711431 = 2567147) B2567147
theorem B12336457 : Blo 1711056 12336457 := bstep (se 2 (by rfl) ⟨4626171, by rfl⟩ : syracuseStep 12336457 = 9252343) B9252343
theorem B13000013 : Blo 1711056 13000013 := bstep (se 3 (by rfl) ⟨2437502, by rfl⟩ : syracuseStep 13000013 = 4875005) B4875005
theorem B6503759 : Blo 1711056 6503759 := bstep (se 1 (by rfl) ⟨4877819, by rfl⟩ : syracuseStep 6503759 = 9755639) B9755639
theorem B4939115 : Blo 1711056 4939115 := bstep (se 1 (by rfl) ⟨3704336, by rfl⟩ : syracuseStep 4939115 = 7408673) B7408673
theorem B9756071 : Blo 1711056 9756071 := bstep (se 1 (by rfl) ⟨7317053, by rfl⟩ : syracuseStep 9756071 = 14634107) B14634107
theorem B1711567 : Blo 1711056 1711567 := bstep (se 1 (by rfl) ⟨1283675, by rfl⟩ : syracuseStep 1711567 = 2567351) B2567351
theorem B5774921 : Blo 1711056 5774921 := bstep (se 2 (by rfl) ⟨2165595, by rfl⟩ : syracuseStep 5774921 = 4331191) B4331191
theorem B1711727 : Blo 1711056 1711727 := bstep (se 1 (by rfl) ⟨1283795, by rfl⟩ : syracuseStep 1711727 = 2567591) B2567591
theorem B1711783 : Blo 1711056 1711783 := bstep (se 1 (by rfl) ⟨1283837, by rfl⟩ : syracuseStep 1711783 = 2567675) B2567675
theorem B1711847 : Blo 1711056 1711847 := bstep (se 1 (by rfl) ⟨1283885, by rfl⟩ : syracuseStep 1711847 = 2567771) B2567771
theorem B13885195 : Blo 1711056 13885195 := bstep (se 1 (by rfl) ⟨10413896, by rfl⟩ : syracuseStep 13885195 = 20827793) B20827793
theorem B4874003 : Blo 1711056 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B1711903 : Blo 1711056 1711903 := bstep (se 1 (by rfl) ⟨1283927, by rfl⟩ : syracuseStep 1711903 = 2567855) B2567855
theorem B93716299 : Blo 1711056 93716299 := bstep (se 1 (by rfl) ⟨70287224, by rfl⟩ : syracuseStep 93716299 = 140574449) B140574449
theorem B4333409 : Blo 1711056 4333409 := bstep (se 2 (by rfl) ⟨1625028, by rfl⟩ : syracuseStep 4333409 = 3250057) B3250057
theorem B1711983 : Blo 1711056 1711983 := bstep (se 1 (by rfl) ⟨1283987, by rfl⟩ : syracuseStep 1711983 = 2567975) B2567975
theorem B3850127 : Blo 1711056 3850127 := bstep (se 1 (by rfl) ⟨2887595, by rfl⟩ : syracuseStep 3850127 = 5775191) B5775191
theorem B1712039 : Blo 1711056 1712039 := bstep (se 1 (by rfl) ⟨1284029, by rfl⟩ : syracuseStep 1712039 = 2568059) B2568059
theorem B6766525 : Blo 1711056 6766525 := bstep (se 3 (by rfl) ⟨1268723, by rfl⟩ : syracuseStep 6766525 = 2537447) B2537447
theorem B1712283 : Blo 1711056 1712283 := bstep (se 1 (by rfl) ⟨1284212, by rfl⟩ : syracuseStep 1712283 = 2568425) B2568425
theorem B8667323 : Blo 1711056 8667323 := bstep (se 1 (by rfl) ⟨6500492, by rfl⟩ : syracuseStep 8667323 = 13000985) B13000985
theorem B1712367 : Blo 1711056 1712367 := bstep (se 1 (by rfl) ⟨1284275, by rfl⟩ : syracuseStep 1712367 = 2568551) B2568551
theorem B4628735 : Blo 1711056 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B4334107 : Blo 1711056 4334107 := bstep (se 1 (by rfl) ⟨3250580, by rfl⟩ : syracuseStep 4334107 = 6501161) B6501161
theorem B27755081 : Blo 1711056 27755081 := bstep (se 2 (by rfl) ⟨10408155, by rfl⟩ : syracuseStep 27755081 = 20816311) B20816311
theorem B1712731 : Blo 1711056 1712731 := bstep (se 1 (by rfl) ⟨1284548, by rfl⟩ : syracuseStep 1712731 = 2569097) B2569097
theorem B8667971 : Blo 1711056 8667971 := bstep (se 1 (by rfl) ⟨6500978, by rfl⟩ : syracuseStep 8667971 = 13001957) B13001957
theorem B1712987 : Blo 1711056 1712987 := bstep (se 1 (by rfl) ⟨1284740, by rfl⟩ : syracuseStep 1712987 = 2569481) B2569481
theorem B1713023 : Blo 1711056 1713023 := bstep (se 1 (by rfl) ⟨1284767, by rfl⟩ : syracuseStep 1713023 = 2569535) B2569535
theorem B1926247 : Blo 1711056 1926247 := bstep (se 1 (by rfl) ⟨1444685, by rfl⟩ : syracuseStep 1926247 = 2889371) B2889371
theorem B8668295 : Blo 1711056 8668295 := bstep (se 1 (by rfl) ⟨6501221, by rfl⟩ : syracuseStep 8668295 = 13002443) B13002443
theorem B3851675 : Blo 1711056 3851675 := bstep (se 1 (by rfl) ⟨2888756, by rfl⟩ : syracuseStep 3851675 = 5777513) B5777513
theorem B4875689 : Blo 1711056 4875689 := bstep (se 2 (by rfl) ⟨1828383, by rfl⟩ : syracuseStep 4875689 = 3656767) B3656767
theorem B17819291 : Blo 1711056 17819291 := bstep (se 1 (by rfl) ⟨13364468, by rfl⟩ : syracuseStep 17819291 = 26728937) B26728937
theorem B5482331 : Blo 1711056 5482331 := bstep (se 1 (by rfl) ⟨4111748, by rfl⟩ : syracuseStep 5482331 = 8223497) B8223497
theorem B5203835 : Blo 1711056 5203835 := bstep (se 1 (by rfl) ⟨3902876, by rfl⟩ : syracuseStep 5203835 = 7805753) B7805753
theorem B4335515 : Blo 1711056 4335515 := bstep (se 1 (by rfl) ⟨3251636, by rfl⟩ : syracuseStep 4335515 = 6503273) B6503273
theorem B4876487 : Blo 1711056 4876487 := bstep (se 1 (by rfl) ⟨3657365, by rfl⟩ : syracuseStep 4876487 = 7314731) B7314731
theorem B18761939 : Blo 1711056 18761939 := bstep (se 1 (by rfl) ⟨14071454, by rfl⟩ : syracuseStep 18761939 = 28142909) B28142909
theorem B4335839 : Blo 1711056 4335839 := bstep (se 1 (by rfl) ⟨3251879, by rfl⟩ : syracuseStep 4335839 = 6503759) B6503759
theorem B4393223 : Blo 1711056 4393223 := bstep (se 1 (by rfl) ⟨3294917, by rfl⟩ : syracuseStep 4393223 = 6589835) B6589835
theorem B124955065 : Blo 1711056 124955065 := bstep (se 2 (by rfl) ⟨46858149, by rfl⟩ : syracuseStep 124955065 = 93716299) B93716299
theorem B13879745 : Blo 1711056 13879745 := bstep (se 2 (by rfl) ⟨5204904, by rfl⟩ : syracuseStep 13879745 = 10409809) B10409809
theorem B8669753 : Blo 1711056 8669753 := bstep (se 2 (by rfl) ⟨3251157, by rfl⟩ : syracuseStep 8669753 = 6502315) B6502315
theorem B9022033 : Blo 1711056 9022033 := bstep (se 2 (by rfl) ⟨3383262, by rfl⟩ : syracuseStep 9022033 = 6766525) B6766525
theorem B2566751 : Blo 1711056 2566751 := bstep (se 1 (by rfl) ⟨1925063, by rfl⟩ : syracuseStep 2566751 = 3850127) B3850127
theorem B8669915 : Blo 1711056 8669915 := bstep (se 1 (by rfl) ⟨6502436, by rfl⟩ : syracuseStep 8669915 = 13004873) B13004873
theorem B4877147 : Blo 1711056 4877147 := bstep (se 1 (by rfl) ⟨3657860, by rfl⟩ : syracuseStep 4877147 = 7315721) B7315721
theorem B2567081 : Blo 1711056 2567081 := bstep (se 2 (by rfl) ⟨962655, by rfl⟩ : syracuseStep 2567081 = 1925311) B1925311
theorem B2567111 : Blo 1711056 2567111 := bstep (se 1 (by rfl) ⟨1925333, by rfl⟩ : syracuseStep 2567111 = 3850667) B3850667
theorem B5778377 : Blo 1711056 5778377 := bstep (se 2 (by rfl) ⟨2166891, by rfl⟩ : syracuseStep 5778377 = 4333783) B4333783
theorem B2567231 : Blo 1711056 2567231 := bstep (se 1 (by rfl) ⟨1925423, by rfl⟩ : syracuseStep 2567231 = 3850847) B3850847
theorem B5778539 : Blo 1711056 5778539 := bstep (se 1 (by rfl) ⟨4333904, by rfl⟩ : syracuseStep 5778539 = 8667809) B8667809
theorem B4115585 : Blo 1711056 4115585 := bstep (se 2 (by rfl) ⟨1543344, by rfl⟩ : syracuseStep 4115585 = 3086689) B3086689
theorem B2567471 : Blo 1711056 2567471 := bstep (se 1 (by rfl) ⟨1925603, by rfl⟩ : syracuseStep 2567471 = 3851207) B3851207
theorem B4115767 : Blo 1711056 4115767 := bstep (se 1 (by rfl) ⟨3086825, by rfl⟩ : syracuseStep 4115767 = 6173651) B6173651
theorem B29248937 : Blo 1711056 29248937 := bstep (se 2 (by rfl) ⟨10968351, by rfl⟩ : syracuseStep 29248937 = 21936703) B21936703
theorem B20819429 : Blo 1711056 20819429 := bstep (se 4 (by rfl) ⟨1951821, by rfl⟩ : syracuseStep 20819429 = 3903643) B3903643
theorem B2567657 : Blo 1711056 2567657 := bstep (se 2 (by rfl) ⟨962871, by rfl⟩ : syracuseStep 2567657 = 1925743) B1925743
theorem B2567711 : Blo 1711056 2567711 := bstep (se 1 (by rfl) ⟨1925783, by rfl⟩ : syracuseStep 2567711 = 3851567) B3851567
theorem B13889087 : Blo 1711056 13889087 := bstep (se 1 (by rfl) ⟨10416815, by rfl⟩ : syracuseStep 13889087 = 20833631) B20833631
theorem B2567801 : Blo 1711056 2567801 := bstep (se 2 (by rfl) ⟨962925, by rfl⟩ : syracuseStep 2567801 = 1925851) B1925851
theorem B31248109 : Blo 1711056 31248109 := bstep (se 3 (by rfl) ⟨5859020, by rfl⟩ : syracuseStep 31248109 = 11718041) B11718041
theorem B3854159 : Blo 1711056 3854159 := bstep (se 1 (by rfl) ⟨2890619, by rfl⟩ : syracuseStep 3854159 = 5781239) B5781239
theorem B2568047 : Blo 1711056 2568047 := bstep (se 1 (by rfl) ⟨1926035, by rfl⟩ : syracuseStep 2568047 = 3852071) B3852071
theorem B2887771 : Blo 1711056 2887771 := bstep (se 1 (by rfl) ⟨2165828, by rfl⟩ : syracuseStep 2887771 = 4331657) B4331657
theorem B2568299 : Blo 1711056 2568299 := bstep (se 1 (by rfl) ⟨1926224, by rfl⟩ : syracuseStep 2568299 = 3852449) B3852449
theorem B12341447 : Blo 1711056 12341447 := bstep (se 1 (by rfl) ⟨9256085, by rfl⟩ : syracuseStep 12341447 = 18512171) B18512171
theorem B1712123 : Blo 1711056 1712123 := bstep (se 1 (by rfl) ⟨1284092, by rfl⟩ : syracuseStep 1712123 = 2568185) B2568185
theorem B2887913 : Blo 1711056 2887913 := bstep (se 2 (by rfl) ⟨1082967, by rfl⟩ : syracuseStep 2887913 = 2165935) B2165935
theorem B3248363 : Blo 1711056 3248363 := bstep (se 1 (by rfl) ⟨2436272, by rfl⟩ : syracuseStep 3248363 = 4872545) B4872545
theorem B41644307 : Blo 1711056 41644307 := bstep (se 1 (by rfl) ⟨31233230, by rfl⟩ : syracuseStep 41644307 = 62466461) B62466461
theorem B2888183 : Blo 1711056 2888183 := bstep (se 1 (by rfl) ⟨2166137, by rfl⟩ : syracuseStep 2888183 = 4332275) B4332275
theorem B29266433 : Blo 1711056 29266433 := bstep (se 2 (by rfl) ⟨10974912, by rfl⟩ : syracuseStep 29266433 = 21949825) B21949825
theorem B2568731 : Blo 1711056 2568731 := bstep (se 1 (by rfl) ⟨1926548, by rfl⟩ : syracuseStep 2568731 = 3853097) B3853097
theorem B19763851 : Blo 1711056 19763851 := bstep (se 1 (by rfl) ⟨14822888, by rfl⟩ : syracuseStep 19763851 = 29645777) B29645777
theorem B2568911 : Blo 1711056 2568911 := bstep (se 1 (by rfl) ⟨1926683, by rfl⟩ : syracuseStep 2568911 = 3853367) B3853367
theorem B7811923 : Blo 1711056 7811923 := bstep (se 1 (by rfl) ⟨5858942, by rfl⟩ : syracuseStep 7811923 = 11717885) B11717885
theorem B2569199 : Blo 1711056 2569199 := bstep (se 1 (by rfl) ⟨1926899, by rfl⟩ : syracuseStep 2569199 = 3853799) B3853799
theorem B3249335 : Blo 1711056 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B2888939 : Blo 1711056 2888939 := bstep (se 1 (by rfl) ⟨2166704, by rfl⟩ : syracuseStep 2888939 = 4333409) B4333409
theorem B9753929 : Blo 1711056 9753929 := bstep (se 2 (by rfl) ⟨3657723, by rfl⟩ : syracuseStep 9753929 = 7315447) B7315447
theorem B2569583 : Blo 1711056 2569583 := bstep (se 1 (by rfl) ⟨1927187, by rfl⟩ : syracuseStep 2569583 = 3854375) B3854375
theorem B10974811 : Blo 1711056 10974811 := bstep (se 1 (by rfl) ⟨8231108, by rfl⟩ : syracuseStep 10974811 = 16462217) B16462217
theorem B4691803 : Blo 1711056 4691803 := bstep (se 1 (by rfl) ⟨3518852, by rfl⟩ : syracuseStep 4691803 = 7037705) B7037705
theorem B13006817 : Blo 1711056 13006817 := bstep (se 2 (by rfl) ⟨4877556, by rfl⟩ : syracuseStep 13006817 = 9755113) B9755113
theorem B10967021 : Blo 1711056 10967021 := bstep (se 3 (by rfl) ⟨2056316, by rfl⟩ : syracuseStep 10967021 = 4112633) B4112633
theorem B16447607 : Blo 1711056 16447607 := bstep (se 1 (by rfl) ⟨12335705, by rfl⟩ : syracuseStep 16447607 = 24671411) B24671411
theorem B2889911 : Blo 1711056 2889911 := bstep (se 1 (by rfl) ⟨2167433, by rfl⟩ : syracuseStep 2889911 = 4334867) B4334867
theorem B41629895 : Blo 1711056 41629895 := bstep (se 1 (by rfl) ⟨31222421, by rfl⟩ : syracuseStep 41629895 = 62444843) B62444843
theorem B12343549 : Blo 1711056 12343549 := bstep (se 3 (by rfl) ⟨2314415, by rfl⟩ : syracuseStep 12343549 = 4628831) B4628831
theorem B13170973 : Blo 1711056 13170973 := bstep (se 3 (by rfl) ⟨2469557, by rfl⟩ : syracuseStep 13170973 = 4939115) B4939115
theorem B3250793 : Blo 1711056 3250793 := bstep (se 2 (by rfl) ⟨1219047, by rfl⟩ : syracuseStep 3250793 = 2438095) B2438095
theorem B7314047 : Blo 1711056 7314047 := bstep (se 1 (by rfl) ⟨5485535, by rfl⟩ : syracuseStep 7314047 = 10971071) B10971071
theorem B8665865 : Blo 1711056 8665865 := bstep (se 2 (by rfl) ⟨3249699, by rfl⟩ : syracuseStep 8665865 = 6499399) B6499399
theorem B7805737 : Blo 1711056 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B1711099 : Blo 1711056 1711099 := bstep (se 1 (by rfl) ⟨1283324, by rfl⟩ : syracuseStep 1711099 = 2566649) B2566649
theorem B1711135 : Blo 1711056 1711135 := bstep (se 1 (by rfl) ⟨1283351, by rfl⟩ : syracuseStep 1711135 = 2566703) B2566703
theorem B4332599 : Blo 1711056 4332599 := bstep (se 1 (by rfl) ⟨3249449, by rfl⟩ : syracuseStep 4332599 = 6498899) B6498899
theorem B16448609 : Blo 1711056 16448609 := bstep (se 2 (by rfl) ⟨6168228, by rfl⟩ : syracuseStep 16448609 = 12336457) B12336457
theorem B9747641 : Blo 1711056 9747641 := bstep (se 2 (by rfl) ⟨3655365, by rfl⟩ : syracuseStep 9747641 = 7310731) B7310731
theorem B1711423 : Blo 1711056 1711423 := bstep (se 1 (by rfl) ⟨1283567, by rfl⟩ : syracuseStep 1711423 = 2567135) B2567135
theorem B9747823 : Blo 1711056 9747823 := bstep (se 1 (by rfl) ⟨7310867, by rfl⟩ : syracuseStep 9747823 = 14621735) B14621735
theorem B8781227 : Blo 1711056 8781227 := bstep (se 1 (by rfl) ⟨6585920, by rfl⟩ : syracuseStep 8781227 = 13171841) B13171841
theorem B8666675 : Blo 1711056 8666675 := bstep (se 1 (by rfl) ⟨6500006, by rfl⟩ : syracuseStep 8666675 = 13000013) B13000013
theorem B1711719 : Blo 1711056 1711719 := bstep (se 1 (by rfl) ⟨1283789, by rfl⟩ : syracuseStep 1711719 = 2567579) B2567579
theorem B6504047 : Blo 1711056 6504047 := bstep (se 1 (by rfl) ⟨4878035, by rfl⟩ : syracuseStep 6504047 = 9756071) B9756071
theorem B18513593 : Blo 1711056 18513593 := bstep (se 2 (by rfl) ⟨6942597, by rfl⟩ : syracuseStep 18513593 = 13885195) B13885195
theorem B3849947 : Blo 1711056 3849947 := bstep (se 1 (by rfl) ⟨2887460, by rfl⟩ : syracuseStep 3849947 = 5774921) B5774921
theorem B4333439 : Blo 1711056 4333439 := bstep (se 1 (by rfl) ⟨3250079, by rfl⟩ : syracuseStep 4333439 = 6500159) B6500159
theorem B1711999 : Blo 1711056 1711999 := bstep (se 1 (by rfl) ⟨1283999, by rfl⟩ : syracuseStep 1711999 = 2567999) B2567999
theorem B3850217 : Blo 1711056 3850217 := bstep (se 2 (by rfl) ⟨1443831, by rfl⟩ : syracuseStep 3850217 = 2887663) B2887663
theorem B1712199 : Blo 1711056 1712199 := bstep (se 1 (by rfl) ⟨1284149, by rfl⟩ : syracuseStep 1712199 = 2568299) B2568299
theorem B3850361 : Blo 1711056 3850361 := bstep (se 2 (by rfl) ⟨1443885, by rfl⟩ : syracuseStep 3850361 = 2887771) B2887771
theorem B1925275 : Blo 1711056 1925275 := bstep (se 1 (by rfl) ⟨1443956, by rfl⟩ : syracuseStep 1925275 = 2887913) B2887913
theorem B27762871 : Blo 1711056 27762871 := bstep (se 1 (by rfl) ⟨20822153, by rfl⟩ : syracuseStep 27762871 = 41644307) B41644307
theorem B1925455 : Blo 1711056 1925455 := bstep (se 1 (by rfl) ⟨1444091, by rfl⟩ : syracuseStep 1925455 = 2888183) B2888183
theorem B16458065 : Blo 1711056 16458065 := bstep (se 2 (by rfl) ⟨6171774, by rfl⟩ : syracuseStep 16458065 = 12343549) B12343549
theorem B1712487 : Blo 1711056 1712487 := bstep (se 1 (by rfl) ⟨1284365, by rfl⟩ : syracuseStep 1712487 = 2568731) B2568731
theorem B1712607 : Blo 1711056 1712607 := bstep (se 1 (by rfl) ⟨1284455, by rfl⟩ : syracuseStep 1712607 = 2568911) B2568911
theorem B1712799 : Blo 1711056 1712799 := bstep (se 1 (by rfl) ⟨1284599, by rfl⟩ : syracuseStep 1712799 = 2569199) B2569199
theorem B1925959 : Blo 1711056 1925959 := bstep (se 1 (by rfl) ⟨1444469, by rfl⟩ : syracuseStep 1925959 = 2888939) B2888939
theorem B1713055 : Blo 1711056 1713055 := bstep (se 1 (by rfl) ⟨1284791, by rfl⟩ : syracuseStep 1713055 = 2569583) B2569583
theorem B11879527 : Blo 1711056 11879527 := bstep (se 1 (by rfl) ⟨8909645, by rfl⟩ : syracuseStep 11879527 = 17819291) B17819291
theorem B3654887 : Blo 1711056 3654887 := bstep (se 1 (by rfl) ⟨2741165, by rfl⟩ : syracuseStep 3654887 = 5482331) B5482331
theorem B1926607 : Blo 1711056 1926607 := bstep (se 1 (by rfl) ⟨1444955, by rfl⟩ : syracuseStep 1926607 = 2889911) B2889911
theorem B8668781 : Blo 1711056 8668781 := bstep (se 3 (by rfl) ⟨1625396, by rfl⟩ : syracuseStep 8668781 = 3250793) B3250793
theorem B4876031 : Blo 1711056 4876031 := bstep (se 1 (by rfl) ⟨3657023, by rfl⟩ : syracuseStep 4876031 = 7314047) B7314047
theorem B5777243 : Blo 1711056 5777243 := bstep (se 1 (by rfl) ⟨4332932, by rfl⟩ : syracuseStep 5777243 = 8665865) B8665865
theorem B3852251 : Blo 1711056 3852251 := bstep (se 1 (by rfl) ⟨2889188, by rfl⟩ : syracuseStep 3852251 = 5778377) B5778377
theorem B3852359 : Blo 1711056 3852359 := bstep (se 1 (by rfl) ⟨2889269, by rfl⟩ : syracuseStep 3852359 = 5778539) B5778539
theorem B14633081 : Blo 1711056 14633081 := bstep (se 2 (by rfl) ⟨5487405, by rfl⟩ : syracuseStep 14633081 = 10974811) B10974811
theorem B6498427 : Blo 1711056 6498427 := bstep (se 1 (by rfl) ⟨4873820, by rfl⟩ : syracuseStep 6498427 = 9747641) B9747641
theorem B19499291 : Blo 1711056 19499291 := bstep (se 1 (by rfl) ⟨14624468, by rfl⟩ : syracuseStep 19499291 = 29248937) B29248937
theorem B13879619 : Blo 1711056 13879619 := bstep (se 1 (by rfl) ⟨10409714, by rfl⟩ : syracuseStep 13879619 = 20819429) B20819429
theorem B5777783 : Blo 1711056 5777783 := bstep (se 1 (by rfl) ⟨4333337, by rfl⟩ : syracuseStep 5777783 = 8666675) B8666675
theorem B9259391 : Blo 1711056 9259391 := bstep (se 1 (by rfl) ⟨6944543, by rfl⟩ : syracuseStep 9259391 = 13889087) B13889087
theorem B4336031 : Blo 1711056 4336031 := bstep (se 1 (by rfl) ⟨3252023, by rfl⟩ : syracuseStep 4336031 = 6504047) B6504047
theorem B2566631 : Blo 1711056 2566631 := bstep (se 1 (by rfl) ⟨1924973, by rfl⟩ : syracuseStep 2566631 = 3849947) B3849947
theorem B2566811 : Blo 1711056 2566811 := bstep (se 1 (by rfl) ⟨1925108, by rfl⟩ : syracuseStep 2566811 = 3850217) B3850217
theorem B5778215 : Blo 1711056 5778215 := bstep (se 1 (by rfl) ⟨4333661, by rfl⟩ : syracuseStep 5778215 = 8667323) B8667323
theorem B8227631 : Blo 1711056 8227631 := bstep (se 1 (by rfl) ⟨6170723, by rfl⟩ : syracuseStep 8227631 = 12341447) B12341447
theorem B5778647 : Blo 1711056 5778647 := bstep (se 1 (by rfl) ⟨4333985, by rfl⟩ : syracuseStep 5778647 = 8667971) B8667971
theorem B8662301 : Blo 1711056 8662301 := bstep (se 3 (by rfl) ⟨1624181, by rfl⟩ : syracuseStep 8662301 = 3248363) B3248363
theorem B5778809 : Blo 1711056 5778809 := bstep (se 2 (by rfl) ⟨2167053, by rfl⟩ : syracuseStep 5778809 = 4334107) B4334107
theorem B5778863 : Blo 1711056 5778863 := bstep (se 1 (by rfl) ⟨4334147, by rfl⟩ : syracuseStep 5778863 = 8668295) B8668295
theorem B2567783 : Blo 1711056 2567783 := bstep (se 1 (by rfl) ⟨1925837, by rfl⟩ : syracuseStep 2567783 = 3851675) B3851675
theorem B10407649 : Blo 1711056 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B10415897 : Blo 1711056 10415897 := bstep (se 2 (by rfl) ⟨3905961, by rfl⟩ : syracuseStep 10415897 = 7811923) B7811923
theorem B3469223 : Blo 1711056 3469223 := bstep (se 1 (by rfl) ⟨2601917, by rfl⟩ : syracuseStep 3469223 = 5203835) B5203835
theorem B8671211 : Blo 1711056 8671211 := bstep (se 1 (by rfl) ⟨6503408, by rfl⟩ : syracuseStep 8671211 = 13006817) B13006817
theorem B7311347 : Blo 1711056 7311347 := bstep (se 1 (by rfl) ⟨5483510, by rfl⟩ : syracuseStep 7311347 = 10967021) B10967021
theorem B10965071 : Blo 1711056 10965071 := bstep (se 1 (by rfl) ⟨8223803, by rfl⟩ : syracuseStep 10965071 = 16447607) B16447607
theorem B2568329 : Blo 1711056 2568329 := bstep (se 2 (by rfl) ⟨963123, by rfl⟩ : syracuseStep 2568329 = 1926247) B1926247
theorem B2928815 : Blo 1711056 2928815 := bstep (se 1 (by rfl) ⟨2196611, by rfl⟩ : syracuseStep 2928815 = 4393223) B4393223
theorem B9253163 : Blo 1711056 9253163 := bstep (se 1 (by rfl) ⟨6939872, by rfl⟩ : syracuseStep 9253163 = 13879745) B13879745
theorem B5779835 : Blo 1711056 5779835 := bstep (se 1 (by rfl) ⟨4334876, by rfl⟩ : syracuseStep 5779835 = 8669753) B8669753
theorem B5779943 : Blo 1711056 5779943 := bstep (se 1 (by rfl) ⟨4334957, by rfl⟩ : syracuseStep 5779943 = 8669915) B8669915
theorem B12997097 : Blo 1711056 12997097 := bstep (se 2 (by rfl) ⟨4873911, by rfl⟩ : syracuseStep 12997097 = 9747823) B9747823
theorem B2888399 : Blo 1711056 2888399 := bstep (se 1 (by rfl) ⟨2166299, by rfl⟩ : syracuseStep 2888399 = 4332599) B4332599
theorem B10965739 : Blo 1711056 10965739 := bstep (se 1 (by rfl) ⟨8224304, by rfl⟩ : syracuseStep 10965739 = 16448609) B16448609
theorem B5854151 : Blo 1711056 5854151 := bstep (se 1 (by rfl) ⟨4390613, by rfl⟩ : syracuseStep 5854151 = 8781227) B8781227
theorem B6255737 : Blo 1711056 6255737 := bstep (se 2 (by rfl) ⟨2345901, by rfl⟩ : syracuseStep 6255737 = 4691803) B4691803
theorem B12342395 : Blo 1711056 12342395 := bstep (se 1 (by rfl) ⟨9256796, by rfl⟩ : syracuseStep 12342395 = 18513593) B18513593
theorem B2569439 : Blo 1711056 2569439 := bstep (se 1 (by rfl) ⟨1927079, by rfl⟩ : syracuseStep 2569439 = 3854159) B3854159
theorem B2888959 : Blo 1711056 2888959 := bstep (se 1 (by rfl) ⟨2166719, by rfl⟩ : syracuseStep 2888959 = 4333439) B4333439
theorem B3085823 : Blo 1711056 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B19510955 : Blo 1711056 19510955 := bstep (se 1 (by rfl) ⟨14633216, by rfl⟩ : syracuseStep 19510955 = 29266433) B29266433
theorem B17561297 : Blo 1711056 17561297 := bstep (se 2 (by rfl) ⟨6585486, by rfl⟩ : syracuseStep 17561297 = 13170973) B13170973
theorem B18503387 : Blo 1711056 18503387 := bstep (se 1 (by rfl) ⟨13877540, by rfl⟩ : syracuseStep 18503387 = 27755081) B27755081
theorem B48117509 : Blo 1711056 48117509 := bstep (se 4 (by rfl) ⟨4511016, by rfl⟩ : syracuseStep 48117509 = 9022033) B9022033
theorem B8664893 : Blo 1711056 8664893 := bstep (se 3 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 8664893 = 3249335) B3249335
theorem B166606753 : Blo 1711056 166606753 := bstep (se 2 (by rfl) ⟨62477532, by rfl⟩ : syracuseStep 166606753 = 124955065) B124955065
theorem B26351801 : Blo 1711056 26351801 := bstep (se 2 (by rfl) ⟨9881925, by rfl⟩ : syracuseStep 26351801 = 19763851) B19763851
theorem B6502619 : Blo 1711056 6502619 := bstep (se 1 (by rfl) ⟨4876964, by rfl⟩ : syracuseStep 6502619 = 9753929) B9753929
theorem B3250459 : Blo 1711056 3250459 := bstep (se 1 (by rfl) ⟨2437844, by rfl⟩ : syracuseStep 3250459 = 4875689) B4875689
theorem B2890343 : Blo 1711056 2890343 := bstep (se 1 (by rfl) ⟨2167757, by rfl⟩ : syracuseStep 2890343 = 4335515) B4335515
theorem B27753263 : Blo 1711056 27753263 := bstep (se 1 (by rfl) ⟨20814947, by rfl⟩ : syracuseStep 27753263 = 41629895) B41629895
theorem B3250991 : Blo 1711056 3250991 := bstep (se 1 (by rfl) ⟨2438243, by rfl⟩ : syracuseStep 3250991 = 4876487) B4876487
theorem B12507959 : Blo 1711056 12507959 := bstep (se 1 (by rfl) ⟨9380969, by rfl⟩ : syracuseStep 12507959 = 18761939) B18761939
theorem B2890559 : Blo 1711056 2890559 := bstep (se 1 (by rfl) ⟨2167919, by rfl⟩ : syracuseStep 2890559 = 4335839) B4335839
theorem B1711167 : Blo 1711056 1711167 := bstep (se 1 (by rfl) ⟨1283375, by rfl⟩ : syracuseStep 1711167 = 2566751) B2566751
theorem B5487689 : Blo 1711056 5487689 := bstep (se 2 (by rfl) ⟨2057883, by rfl⟩ : syracuseStep 5487689 = 4115767) B4115767
theorem B3251431 : Blo 1711056 3251431 := bstep (se 1 (by rfl) ⟨2438573, by rfl⟩ : syracuseStep 3251431 = 4877147) B4877147
theorem B1711387 : Blo 1711056 1711387 := bstep (se 1 (by rfl) ⟨1283540, by rfl⟩ : syracuseStep 1711387 = 2567081) B2567081
theorem B1711407 : Blo 1711056 1711407 := bstep (se 1 (by rfl) ⟨1283555, by rfl⟩ : syracuseStep 1711407 = 2567111) B2567111
theorem B1711487 : Blo 1711056 1711487 := bstep (se 1 (by rfl) ⟨1283615, by rfl⟩ : syracuseStep 1711487 = 2567231) B2567231
theorem B2743723 : Blo 1711056 2743723 := bstep (se 1 (by rfl) ⟨2057792, by rfl⟩ : syracuseStep 2743723 = 4115585) B4115585
theorem B1711647 : Blo 1711056 1711647 := bstep (se 1 (by rfl) ⟨1283735, by rfl⟩ : syracuseStep 1711647 = 2567471) B2567471
theorem B41664145 : Blo 1711056 41664145 := bstep (se 2 (by rfl) ⟨15624054, by rfl⟩ : syracuseStep 41664145 = 31248109) B31248109
theorem B1711771 : Blo 1711056 1711771 := bstep (se 1 (by rfl) ⟨1283828, by rfl⟩ : syracuseStep 1711771 = 2567657) B2567657
theorem B1711807 : Blo 1711056 1711807 := bstep (se 1 (by rfl) ⟨1283855, by rfl⟩ : syracuseStep 1711807 = 2567711) B2567711
theorem B1711867 : Blo 1711056 1711867 := bstep (se 1 (by rfl) ⟨1283900, by rfl⟩ : syracuseStep 1711867 = 2567801) B2567801
theorem B1712031 : Blo 1711056 1712031 := bstep (se 1 (by rfl) ⟨1284023, by rfl⟩ : syracuseStep 1712031 = 2568047) B2568047
theorem B1712219 : Blo 1711056 1712219 := bstep (se 1 (by rfl) ⟨1284164, by rfl⟩ : syracuseStep 1712219 = 2568329) B2568329
theorem B4333945 : Blo 1711056 4333945 := bstep (se 2 (by rfl) ⟨1625229, by rfl⟩ : syracuseStep 4333945 = 3250459) B3250459
theorem B1925599 : Blo 1711056 1925599 := bstep (se 1 (by rfl) ⟨1444199, by rfl⟩ : syracuseStep 1925599 = 2888399) B2888399
theorem B4170491 : Blo 1711056 4170491 := bstep (se 1 (by rfl) ⟨3127868, by rfl⟩ : syracuseStep 4170491 = 6255737) B6255737
theorem B24675101 : Blo 1711056 24675101 := bstep (se 3 (by rfl) ⟨4626581, by rfl⟩ : syracuseStep 24675101 = 9253163) B9253163
theorem B1712959 : Blo 1711056 1712959 := bstep (se 1 (by rfl) ⟨1284719, by rfl⟩ : syracuseStep 1712959 = 2569439) B2569439
theorem B24691709 : Blo 1711056 24691709 := bstep (se 3 (by rfl) ⟨4629695, by rfl⟩ : syracuseStep 24691709 = 9259391) B9259391
theorem B5776595 : Blo 1711056 5776595 := bstep (se 1 (by rfl) ⟨4332446, by rfl⟩ : syracuseStep 5776595 = 8664893) B8664893
theorem B3851495 : Blo 1711056 3851495 := bstep (se 1 (by rfl) ⟨2888621, by rfl⟩ : syracuseStep 3851495 = 5777243) B5777243
theorem B4335079 : Blo 1711056 4335079 := bstep (se 1 (by rfl) ⟨3251309, by rfl⟩ : syracuseStep 4335079 = 6502619) B6502619
theorem B3851855 : Blo 1711056 3851855 := bstep (se 1 (by rfl) ⟨2888891, by rfl⟩ : syracuseStep 3851855 = 5777783) B5777783
theorem B4335241 : Blo 1711056 4335241 := bstep (se 2 (by rfl) ⟨1625715, by rfl⟩ : syracuseStep 4335241 = 3251431) B3251431
theorem B3851945 : Blo 1711056 3851945 := bstep (se 2 (by rfl) ⟨1444479, by rfl⟩ : syracuseStep 3851945 = 2888959) B2888959
theorem B1926895 : Blo 1711056 1926895 := bstep (se 1 (by rfl) ⟨1445171, by rfl⟩ : syracuseStep 1926895 = 2890343) B2890343
theorem B3852143 : Blo 1711056 3852143 := bstep (se 1 (by rfl) ⟨2889107, by rfl⟩ : syracuseStep 3852143 = 5778215) B5778215
theorem B1927039 : Blo 1711056 1927039 := bstep (se 1 (by rfl) ⟨1445279, by rfl⟩ : syracuseStep 1927039 = 2890559) B2890559
theorem B3852431 : Blo 1711056 3852431 := bstep (se 1 (by rfl) ⟨2889323, by rfl⟩ : syracuseStep 3852431 = 5778647) B5778647
theorem B55552193 : Blo 1711056 55552193 := bstep (se 2 (by rfl) ⟨20832072, by rfl⟩ : syracuseStep 55552193 = 41664145) B41664145
theorem B3852539 : Blo 1711056 3852539 := bstep (se 1 (by rfl) ⟨2889404, by rfl⟩ : syracuseStep 3852539 = 5778809) B5778809
theorem B3852575 : Blo 1711056 3852575 := bstep (se 1 (by rfl) ⟨2889431, by rfl⟩ : syracuseStep 3852575 = 5778863) B5778863
theorem B9251261 : Blo 1711056 9251261 := bstep (se 3 (by rfl) ⟨1734611, by rfl⟩ : syracuseStep 9251261 = 3469223) B3469223
theorem B2566907 : Blo 1711056 2566907 := bstep (se 1 (by rfl) ⟨1925180, by rfl⟩ : syracuseStep 2566907 = 3850361) B3850361
theorem B1952543 : Blo 1711056 1952543 := bstep (se 1 (by rfl) ⟨1464407, by rfl⟩ : syracuseStep 1952543 = 2928815) B2928815
theorem B2567033 : Blo 1711056 2567033 := bstep (se 2 (by rfl) ⟨962637, by rfl⟩ : syracuseStep 2567033 = 1925275) B1925275
theorem B29240189 : Blo 1711056 29240189 := bstep (se 3 (by rfl) ⟨5482535, by rfl⟩ : syracuseStep 29240189 = 10965071) B10965071
theorem B10972043 : Blo 1711056 10972043 := bstep (se 1 (by rfl) ⟨8229032, by rfl⟩ : syracuseStep 10972043 = 16458065) B16458065
theorem B3853223 : Blo 1711056 3853223 := bstep (se 1 (by rfl) ⟨2889917, by rfl⟩ : syracuseStep 3853223 = 5779835) B5779835
theorem B3853295 : Blo 1711056 3853295 := bstep (se 1 (by rfl) ⟨2889971, by rfl⟩ : syracuseStep 3853295 = 5779943) B5779943
theorem B2567273 : Blo 1711056 2567273 := bstep (se 2 (by rfl) ⟨962727, by rfl⟩ : syracuseStep 2567273 = 1925455) B1925455
theorem B5779187 : Blo 1711056 5779187 := bstep (se 1 (by rfl) ⟨4334390, by rfl⟩ : syracuseStep 5779187 = 8668781) B8668781
theorem B2567945 : Blo 1711056 2567945 := bstep (se 2 (by rfl) ⟨962979, by rfl⟩ : syracuseStep 2567945 = 1925959) B1925959
theorem B2568167 : Blo 1711056 2568167 := bstep (se 1 (by rfl) ⟨1926125, by rfl⟩ : syracuseStep 2568167 = 3852251) B3852251
theorem B8228861 : Blo 1711056 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B2568239 : Blo 1711056 2568239 := bstep (se 1 (by rfl) ⟨1926179, by rfl⟩ : syracuseStep 2568239 = 3852359) B3852359
theorem B17567867 : Blo 1711056 17567867 := bstep (se 1 (by rfl) ⟨13175900, by rfl⟩ : syracuseStep 17567867 = 26351801) B26351801
theorem B15839369 : Blo 1711056 15839369 := bstep (se 2 (by rfl) ⟨5939763, by rfl⟩ : syracuseStep 15839369 = 11879527) B11879527
theorem B9253079 : Blo 1711056 9253079 := bstep (se 1 (by rfl) ⟨6939809, by rfl⟩ : syracuseStep 9253079 = 13879619) B13879619
theorem B18502175 : Blo 1711056 18502175 := bstep (se 1 (by rfl) ⟨13876631, by rfl⟩ : syracuseStep 18502175 = 27753263) B27753263
theorem B5485087 : Blo 1711056 5485087 := bstep (se 1 (by rfl) ⟨4113815, by rfl⟩ : syracuseStep 5485087 = 8227631) B8227631
theorem B2167327 : Blo 1711056 2167327 := bstep (se 1 (by rfl) ⟨1625495, by rfl⟩ : syracuseStep 2167327 = 3250991) B3250991
theorem B46830125 : Blo 1711056 46830125 := bstep (se 3 (by rfl) ⟨8780648, by rfl⟩ : syracuseStep 46830125 = 17561297) B17561297
theorem B3658297 : Blo 1711056 3658297 := bstep (se 2 (by rfl) ⟨1371861, by rfl⟩ : syracuseStep 3658297 = 2743723) B2743723
theorem B2568809 : Blo 1711056 2568809 := bstep (se 2 (by rfl) ⟨963303, by rfl⟩ : syracuseStep 2568809 = 1926607) B1926607
theorem B3658459 : Blo 1711056 3658459 := bstep (se 1 (by rfl) ⟨2743844, by rfl⟩ : syracuseStep 3658459 = 5487689) B5487689
theorem B6943931 : Blo 1711056 6943931 := bstep (se 1 (by rfl) ⟨5207948, by rfl⟩ : syracuseStep 6943931 = 10415897) B10415897
theorem B15611069 : Blo 1711056 15611069 := bstep (se 3 (by rfl) ⟨2927075, by rfl⟩ : syracuseStep 15611069 = 5854151) B5854151
theorem B5780807 : Blo 1711056 5780807 := bstep (se 1 (by rfl) ⟨4335605, by rfl⟩ : syracuseStep 5780807 = 8671211) B8671211
theorem B8664569 : Blo 1711056 8664569 := bstep (se 2 (by rfl) ⟨3249213, by rfl⟩ : syracuseStep 8664569 = 6498427) B6498427
theorem B37017161 : Blo 1711056 37017161 := bstep (se 2 (by rfl) ⟨13881435, by rfl⟩ : syracuseStep 37017161 = 27762871) B27762871
theorem B8664731 : Blo 1711056 8664731 := bstep (se 1 (by rfl) ⟨6498548, by rfl⟩ : syracuseStep 8664731 = 12997097) B12997097
theorem B32913053 : Blo 1711056 32913053 := bstep (se 3 (by rfl) ⟨6171197, by rfl⟩ : syracuseStep 32913053 = 12342395) B12342395
theorem B9746365 : Blo 1711056 9746365 := bstep (se 3 (by rfl) ⟨1827443, by rfl⟩ : syracuseStep 9746365 = 3654887) B3654887
theorem B14620985 : Blo 1711056 14620985 := bstep (se 2 (by rfl) ⟨5482869, by rfl⟩ : syracuseStep 14620985 = 10965739) B10965739
theorem B13007303 : Blo 1711056 13007303 := bstep (se 1 (by rfl) ⟨9755477, by rfl⟩ : syracuseStep 13007303 = 19510955) B19510955
theorem B12335591 : Blo 1711056 12335591 := bstep (se 1 (by rfl) ⟨9251693, by rfl⟩ : syracuseStep 12335591 = 18503387) B18503387
theorem B3250687 : Blo 1711056 3250687 := bstep (se 1 (by rfl) ⟨2438015, by rfl⟩ : syracuseStep 3250687 = 4876031) B4876031
theorem B32078339 : Blo 1711056 32078339 := bstep (se 1 (by rfl) ⟨24058754, by rfl⟩ : syracuseStep 32078339 = 48117509) B48117509
theorem B9755387 : Blo 1711056 9755387 := bstep (se 1 (by rfl) ⟨7316540, by rfl⟩ : syracuseStep 9755387 = 14633081) B14633081
theorem B12999527 : Blo 1711056 12999527 := bstep (se 1 (by rfl) ⟨9749645, by rfl⟩ : syracuseStep 12999527 = 19499291) B19499291
theorem B2890687 : Blo 1711056 2890687 := bstep (se 1 (by rfl) ⟨2168015, by rfl⟩ : syracuseStep 2890687 = 4336031) B4336031
theorem B1711087 : Blo 1711056 1711087 := bstep (se 1 (by rfl) ⟨1283315, by rfl⟩ : syracuseStep 1711087 = 2566631) B2566631
theorem B1711207 : Blo 1711056 1711207 := bstep (se 1 (by rfl) ⟨1283405, by rfl⟩ : syracuseStep 1711207 = 2566811) B2566811
theorem B8338639 : Blo 1711056 8338639 := bstep (se 1 (by rfl) ⟨6253979, by rfl⟩ : syracuseStep 8338639 = 12507959) B12507959
theorem B5774867 : Blo 1711056 5774867 := bstep (se 1 (by rfl) ⟨4331150, by rfl⟩ : syracuseStep 5774867 = 8662301) B8662301
theorem B13876865 : Blo 1711056 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B1711855 : Blo 1711056 1711855 := bstep (se 1 (by rfl) ⟨1283891, by rfl⟩ : syracuseStep 1711855 = 2567783) B2567783
theorem B222142337 : Blo 1711056 222142337 := bstep (se 2 (by rfl) ⟨83303376, by rfl⟩ : syracuseStep 222142337 = 166606753) B166606753
theorem B4874231 : Blo 1711056 4874231 := bstep (se 1 (by rfl) ⟨3655673, by rfl⟩ : syracuseStep 4874231 = 7311347) B7311347
theorem B1712159 : Blo 1711056 1712159 := bstep (se 1 (by rfl) ⟨1284119, by rfl⟩ : syracuseStep 1712159 = 2568239) B2568239
theorem B10559579 : Blo 1711056 10559579 := bstep (se 1 (by rfl) ⟨7919684, by rfl⟩ : syracuseStep 10559579 = 15839369) B15839369
theorem B6168719 : Blo 1711056 6168719 := bstep (se 1 (by rfl) ⟨4626539, by rfl⟩ : syracuseStep 6168719 = 9253079) B9253079
theorem B31220083 : Blo 1711056 31220083 := bstep (se 1 (by rfl) ⟨23415062, by rfl⟩ : syracuseStep 31220083 = 46830125) B46830125
theorem B1712539 : Blo 1711056 1712539 := bstep (se 1 (by rfl) ⟨1284404, by rfl⟩ : syracuseStep 1712539 = 2568809) B2568809
theorem B16450067 : Blo 1711056 16450067 := bstep (se 1 (by rfl) ⟨12337550, by rfl⟩ : syracuseStep 16450067 = 24675101) B24675101
theorem B4334249 : Blo 1711056 4334249 := bstep (se 2 (by rfl) ⟨1625343, by rfl⟩ : syracuseStep 4334249 = 3250687) B3250687
theorem B4629287 : Blo 1711056 4629287 := bstep (se 1 (by rfl) ⟨3471965, by rfl⟩ : syracuseStep 4629287 = 6943931) B6943931
theorem B3851063 : Blo 1711056 3851063 := bstep (se 1 (by rfl) ⟨2888297, by rfl⟩ : syracuseStep 3851063 = 5776595) B5776595
theorem B5776379 : Blo 1711056 5776379 := bstep (se 1 (by rfl) ⟨4332284, by rfl⟩ : syracuseStep 5776379 = 8664569) B8664569
theorem B5776487 : Blo 1711056 5776487 := bstep (se 1 (by rfl) ⟨4332365, by rfl⟩ : syracuseStep 5776487 = 8664731) B8664731
theorem B11118185 : Blo 1711056 11118185 := bstep (se 2 (by rfl) ⟨4169319, by rfl⟩ : syracuseStep 11118185 = 8338639) B8338639
theorem B9251243 : Blo 1711056 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B3852791 : Blo 1711056 3852791 := bstep (se 1 (by rfl) ⟨2889593, by rfl⟩ : syracuseStep 3852791 = 5779187) B5779187
theorem B12995153 : Blo 1711056 12995153 := bstep (se 2 (by rfl) ⟨4873182, by rfl⟩ : syracuseStep 12995153 = 9746365) B9746365
theorem B5778593 : Blo 1711056 5778593 := bstep (se 2 (by rfl) ⟨2166972, by rfl⟩ : syracuseStep 5778593 = 4333945) B4333945
theorem B2780327 : Blo 1711056 2780327 := bstep (se 1 (by rfl) ⟨2085245, by rfl⟩ : syracuseStep 2780327 = 4170491) B4170491
theorem B2567465 : Blo 1711056 2567465 := bstep (se 2 (by rfl) ⟨962799, by rfl⟩ : syracuseStep 2567465 = 1925599) B1925599
theorem B16461139 : Blo 1711056 16461139 := bstep (se 1 (by rfl) ⟨12345854, by rfl⟩ : syracuseStep 16461139 = 24691709) B24691709
theorem B4877729 : Blo 1711056 4877729 := bstep (se 2 (by rfl) ⟨1829148, by rfl⟩ : syracuseStep 4877729 = 3658297) B3658297
theorem B10407379 : Blo 1711056 10407379 := bstep (se 1 (by rfl) ⟨7805534, by rfl⟩ : syracuseStep 10407379 = 15611069) B15611069
theorem B2567663 : Blo 1711056 2567663 := bstep (se 1 (by rfl) ⟨1925747, by rfl⟩ : syracuseStep 2567663 = 3851495) B3851495
theorem B3853871 : Blo 1711056 3853871 := bstep (se 1 (by rfl) ⟨2890403, by rfl⟩ : syracuseStep 3853871 = 5780807) B5780807
theorem B4877945 : Blo 1711056 4877945 := bstep (se 2 (by rfl) ⟨1829229, by rfl⟩ : syracuseStep 4877945 = 3658459) B3658459
theorem B24678107 : Blo 1711056 24678107 := bstep (se 1 (by rfl) ⟨18508580, by rfl⟩ : syracuseStep 24678107 = 37017161) B37017161
theorem B2567903 : Blo 1711056 2567903 := bstep (se 1 (by rfl) ⟨1925927, by rfl⟩ : syracuseStep 2567903 = 3851855) B3851855
theorem B21942035 : Blo 1711056 21942035 := bstep (se 1 (by rfl) ⟨16456526, by rfl⟩ : syracuseStep 21942035 = 32913053) B32913053
theorem B2567963 : Blo 1711056 2567963 := bstep (se 1 (by rfl) ⟨1925972, by rfl⟩ : syracuseStep 2567963 = 3851945) B3851945
theorem B2568095 : Blo 1711056 2568095 := bstep (se 1 (by rfl) ⟨1926071, by rfl⟩ : syracuseStep 2568095 = 3852143) B3852143
theorem B3854249 : Blo 1711056 3854249 := bstep (se 2 (by rfl) ⟨1445343, by rfl⟩ : syracuseStep 3854249 = 2890687) B2890687
theorem B32894909 : Blo 1711056 32894909 := bstep (se 3 (by rfl) ⟨6167795, by rfl⟩ : syracuseStep 32894909 = 12335591) B12335591
theorem B2568287 : Blo 1711056 2568287 := bstep (se 1 (by rfl) ⟨1926215, by rfl⟩ : syracuseStep 2568287 = 3852431) B3852431
theorem B2568359 : Blo 1711056 2568359 := bstep (se 1 (by rfl) ⟨1926269, by rfl⟩ : syracuseStep 2568359 = 3852539) B3852539
theorem B2568383 : Blo 1711056 2568383 := bstep (se 1 (by rfl) ⟨1926287, by rfl⟩ : syracuseStep 2568383 = 3852575) B3852575
theorem B8671535 : Blo 1711056 8671535 := bstep (se 1 (by rfl) ⟨6503651, by rfl⟩ : syracuseStep 8671535 = 13007303) B13007303
theorem B21385559 : Blo 1711056 21385559 := bstep (se 1 (by rfl) ⟨16039169, by rfl⟩ : syracuseStep 21385559 = 32078339) B32078339
theorem B19493459 : Blo 1711056 19493459 := bstep (se 1 (by rfl) ⟨14620094, by rfl⟩ : syracuseStep 19493459 = 29240189) B29240189
theorem B2568815 : Blo 1711056 2568815 := bstep (se 1 (by rfl) ⟨1926611, by rfl⟩ : syracuseStep 2568815 = 3853223) B3853223
theorem B5780105 : Blo 1711056 5780105 := bstep (se 2 (by rfl) ⟨2167539, by rfl⟩ : syracuseStep 5780105 = 4335079) B4335079
theorem B2568863 : Blo 1711056 2568863 := bstep (se 1 (by rfl) ⟨1926647, by rfl⟩ : syracuseStep 2568863 = 3853295) B3853295
theorem B5206781 : Blo 1711056 5206781 := bstep (se 3 (by rfl) ⟨976271, by rfl⟩ : syracuseStep 5206781 = 1952543) B1952543
theorem B5780321 : Blo 1711056 5780321 := bstep (se 2 (by rfl) ⟨2167620, by rfl⟩ : syracuseStep 5780321 = 4335241) B4335241
theorem B2569193 : Blo 1711056 2569193 := bstep (se 2 (by rfl) ⟨963447, by rfl⟩ : syracuseStep 2569193 = 1926895) B1926895
theorem B2569385 : Blo 1711056 2569385 := bstep (se 2 (by rfl) ⟨963519, by rfl⟩ : syracuseStep 2569385 = 1927039) B1927039
theorem B3249487 : Blo 1711056 3249487 := bstep (se 1 (by rfl) ⟨2437115, by rfl⟩ : syracuseStep 3249487 = 4874231) B4874231
theorem B5485907 : Blo 1711056 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B46847645 : Blo 1711056 46847645 := bstep (se 3 (by rfl) ⟨8783933, by rfl⟩ : syracuseStep 46847645 = 17567867) B17567867
theorem B12334783 : Blo 1711056 12334783 := bstep (se 1 (by rfl) ⟨9251087, by rfl⟩ : syracuseStep 12334783 = 18502175) B18502175
theorem B7313449 : Blo 1711056 7313449 := bstep (se 2 (by rfl) ⟨2742543, by rfl⟩ : syracuseStep 7313449 = 5485087) B5485087
theorem B2889769 : Blo 1711056 2889769 := bstep (se 2 (by rfl) ⟨1083663, by rfl⟩ : syracuseStep 2889769 = 2167327) B2167327
theorem B37034795 : Blo 1711056 37034795 := bstep (se 1 (by rfl) ⟨27776096, by rfl⟩ : syracuseStep 37034795 = 55552193) B55552193
theorem B9747323 : Blo 1711056 9747323 := bstep (se 1 (by rfl) ⟨7310492, by rfl⟩ : syracuseStep 9747323 = 14620985) B14620985
theorem B6167507 : Blo 1711056 6167507 := bstep (se 1 (by rfl) ⟨4625630, by rfl⟩ : syracuseStep 6167507 = 9251261) B9251261
theorem B1711271 : Blo 1711056 1711271 := bstep (se 1 (by rfl) ⟨1283453, by rfl⟩ : syracuseStep 1711271 = 2566907) B2566907
theorem B6503591 : Blo 1711056 6503591 := bstep (se 1 (by rfl) ⟨4877693, by rfl⟩ : syracuseStep 6503591 = 9755387) B9755387
theorem B8666351 : Blo 1711056 8666351 := bstep (se 1 (by rfl) ⟨6499763, by rfl⟩ : syracuseStep 8666351 = 12999527) B12999527
theorem B1711355 : Blo 1711056 1711355 := bstep (se 1 (by rfl) ⟨1283516, by rfl⟩ : syracuseStep 1711355 = 2567033) B2567033
theorem B7314695 : Blo 1711056 7314695 := bstep (se 1 (by rfl) ⟨5486021, by rfl⟩ : syracuseStep 7314695 = 10972043) B10972043
theorem B1711515 : Blo 1711056 1711515 := bstep (se 1 (by rfl) ⟨1283636, by rfl⟩ : syracuseStep 1711515 = 2567273) B2567273
theorem B3849911 : Blo 1711056 3849911 := bstep (se 1 (by rfl) ⟨2887433, by rfl⟩ : syracuseStep 3849911 = 5774867) B5774867
theorem B1711963 : Blo 1711056 1711963 := bstep (se 1 (by rfl) ⟨1283972, by rfl⟩ : syracuseStep 1711963 = 2567945) B2567945
theorem B148094891 : Blo 1711056 148094891 := bstep (se 1 (by rfl) ⟨111071168, by rfl⟩ : syracuseStep 148094891 = 222142337) B222142337
theorem B1712111 : Blo 1711056 1712111 := bstep (se 1 (by rfl) ⟨1284083, by rfl⟩ : syracuseStep 1712111 = 2568167) B2568167
theorem B1712191 : Blo 1711056 1712191 := bstep (se 1 (by rfl) ⟨1284143, by rfl⟩ : syracuseStep 1712191 = 2568287) B2568287
theorem B4112479 : Blo 1711056 4112479 := bstep (se 1 (by rfl) ⟨3084359, by rfl⟩ : syracuseStep 4112479 = 6168719) B6168719
theorem B1712239 : Blo 1711056 1712239 := bstep (se 1 (by rfl) ⟨1284179, by rfl⟩ : syracuseStep 1712239 = 2568359) B2568359
theorem B1712255 : Blo 1711056 1712255 := bstep (se 1 (by rfl) ⟨1284191, by rfl⟩ : syracuseStep 1712255 = 2568383) B2568383
theorem B1712543 : Blo 1711056 1712543 := bstep (se 1 (by rfl) ⟨1284407, by rfl⟩ : syracuseStep 1712543 = 2568815) B2568815
theorem B1712575 : Blo 1711056 1712575 := bstep (se 1 (by rfl) ⟨1284431, by rfl⟩ : syracuseStep 1712575 = 2568863) B2568863
theorem B1712795 : Blo 1711056 1712795 := bstep (se 1 (by rfl) ⟨1284596, by rfl⟩ : syracuseStep 1712795 = 2569193) B2569193
theorem B3850919 : Blo 1711056 3850919 := bstep (se 1 (by rfl) ⟨2888189, by rfl⟩ : syracuseStep 3850919 = 5776379) B5776379
theorem B3850991 : Blo 1711056 3850991 := bstep (se 1 (by rfl) ⟨2888243, by rfl⟩ : syracuseStep 3850991 = 5776487) B5776487
theorem B1712923 : Blo 1711056 1712923 := bstep (se 1 (by rfl) ⟨1284692, by rfl⟩ : syracuseStep 1712923 = 2569385) B2569385
theorem B21948185 : Blo 1711056 21948185 := bstep (se 2 (by rfl) ⟨8230569, by rfl⟩ : syracuseStep 21948185 = 16461139) B16461139
theorem B6498215 : Blo 1711056 6498215 := bstep (se 1 (by rfl) ⟨4873661, by rfl⟩ : syracuseStep 6498215 = 9747323) B9747323
theorem B3852395 : Blo 1711056 3852395 := bstep (se 1 (by rfl) ⟨2889296, by rfl⟩ : syracuseStep 3852395 = 5778593) B5778593
theorem B1853551 : Blo 1711056 1853551 := bstep (se 1 (by rfl) ⟨1390163, by rfl⟩ : syracuseStep 1853551 = 2780327) B2780327
theorem B4335727 : Blo 1711056 4335727 := bstep (se 1 (by rfl) ⟨3251795, by rfl⟩ : syracuseStep 4335727 = 6503591) B6503591
theorem B5777567 : Blo 1711056 5777567 := bstep (se 1 (by rfl) ⟨4333175, by rfl⟩ : syracuseStep 5777567 = 8666351) B8666351
theorem B4876463 : Blo 1711056 4876463 := bstep (se 1 (by rfl) ⟨3657347, by rfl⟩ : syracuseStep 4876463 = 7314695) B7314695
theorem B2566607 : Blo 1711056 2566607 := bstep (se 1 (by rfl) ⟨1924955, by rfl⟩ : syracuseStep 2566607 = 3849911) B3849911
theorem B16452071 : Blo 1711056 16452071 := bstep (se 1 (by rfl) ⟨12339053, by rfl⟩ : syracuseStep 16452071 = 24678107) B24678107
theorem B9751265 : Blo 1711056 9751265 := bstep (se 2 (by rfl) ⟨3656724, by rfl⟩ : syracuseStep 9751265 = 7313449) B7313449
theorem B3853025 : Blo 1711056 3853025 := bstep (se 2 (by rfl) ⟨1444884, by rfl⟩ : syracuseStep 3853025 = 2889769) B2889769
theorem B28158877 : Blo 1711056 28158877 := bstep (se 3 (by rfl) ⟨5279789, by rfl⟩ : syracuseStep 28158877 = 10559579) B10559579
theorem B12995639 : Blo 1711056 12995639 := bstep (se 1 (by rfl) ⟨9746729, by rfl⟩ : syracuseStep 12995639 = 19493459) B19493459
theorem B3853403 : Blo 1711056 3853403 := bstep (se 1 (by rfl) ⟨2890052, by rfl⟩ : syracuseStep 3853403 = 5780105) B5780105
theorem B2567375 : Blo 1711056 2567375 := bstep (se 1 (by rfl) ⟨1925531, by rfl⟩ : syracuseStep 2567375 = 3851063) B3851063
theorem B3853547 : Blo 1711056 3853547 := bstep (se 1 (by rfl) ⟨2890160, by rfl⟩ : syracuseStep 3853547 = 5780321) B5780321
theorem B57028157 : Blo 1711056 57028157 := bstep (se 3 (by rfl) ⟨10692779, by rfl⟩ : syracuseStep 57028157 = 21385559) B21385559
theorem B31231763 : Blo 1711056 31231763 := bstep (se 1 (by rfl) ⟨23423822, by rfl⟩ : syracuseStep 31231763 = 46847645) B46847645
theorem B2568527 : Blo 1711056 2568527 := bstep (se 1 (by rfl) ⟨1926395, by rfl⟩ : syracuseStep 2568527 = 3852791) B3852791
theorem B8663435 : Blo 1711056 8663435 := bstep (se 1 (by rfl) ⟨6497576, by rfl⟩ : syracuseStep 8663435 = 12995153) B12995153
theorem B166507109 : Blo 1711056 166507109 := bstep (se 4 (by rfl) ⟨15610041, by rfl⟩ : syracuseStep 166507109 = 31220083) B31220083
theorem B16446377 : Blo 1711056 16446377 := bstep (se 2 (by rfl) ⟨6167391, by rfl⟩ : syracuseStep 16446377 = 12334783) B12334783
theorem B2569247 : Blo 1711056 2569247 := bstep (se 1 (by rfl) ⟨1926935, by rfl⟩ : syracuseStep 2569247 = 3853871) B3853871
theorem B14628023 : Blo 1711056 14628023 := bstep (se 1 (by rfl) ⟨10971017, by rfl⟩ : syracuseStep 14628023 = 21942035) B21942035
theorem B16446685 : Blo 1711056 16446685 := bstep (se 3 (by rfl) ⟨3083753, by rfl⟩ : syracuseStep 16446685 = 6167507) B6167507
theorem B2569499 : Blo 1711056 2569499 := bstep (se 1 (by rfl) ⟨1927124, by rfl⟩ : syracuseStep 2569499 = 3854249) B3854249
theorem B5781023 : Blo 1711056 5781023 := bstep (se 1 (by rfl) ⟨4335767, by rfl⟩ : syracuseStep 5781023 = 8671535) B8671535
theorem B2889499 : Blo 1711056 2889499 := bstep (se 1 (by rfl) ⟨2167124, by rfl⟩ : syracuseStep 2889499 = 4334249) B4334249
theorem B3471187 : Blo 1711056 3471187 := bstep (se 1 (by rfl) ⟨2603390, by rfl⟩ : syracuseStep 3471187 = 5206781) B5206781
theorem B3086191 : Blo 1711056 3086191 := bstep (se 1 (by rfl) ⟨2314643, by rfl⟩ : syracuseStep 3086191 = 4629287) B4629287
theorem B14629085 : Blo 1711056 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B7412123 : Blo 1711056 7412123 := bstep (se 1 (by rfl) ⟨5559092, by rfl⟩ : syracuseStep 7412123 = 11118185) B11118185
theorem B43866845 : Blo 1711056 43866845 := bstep (se 3 (by rfl) ⟨8225033, by rfl⟩ : syracuseStep 43866845 = 16450067) B16450067
theorem B6167495 : Blo 1711056 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B4332649 : Blo 1711056 4332649 := bstep (se 2 (by rfl) ⟨1624743, by rfl⟩ : syracuseStep 4332649 = 3249487) B3249487
theorem B24689863 : Blo 1711056 24689863 := bstep (se 1 (by rfl) ⟨18517397, by rfl⟩ : syracuseStep 24689863 = 37034795) B37034795
theorem B13876505 : Blo 1711056 13876505 := bstep (se 2 (by rfl) ⟨5203689, by rfl⟩ : syracuseStep 13876505 = 10407379) B10407379
theorem B1711643 : Blo 1711056 1711643 := bstep (se 1 (by rfl) ⟨1283732, by rfl⟩ : syracuseStep 1711643 = 2567465) B2567465
theorem B3251819 : Blo 1711056 3251819 := bstep (se 1 (by rfl) ⟨2438864, by rfl⟩ : syracuseStep 3251819 = 4877729) B4877729
theorem B1711775 : Blo 1711056 1711775 := bstep (se 1 (by rfl) ⟨1283831, by rfl⟩ : syracuseStep 1711775 = 2567663) B2567663
theorem B3251963 : Blo 1711056 3251963 := bstep (se 1 (by rfl) ⟨2438972, by rfl⟩ : syracuseStep 3251963 = 4877945) B4877945
theorem B1711935 : Blo 1711056 1711935 := bstep (se 1 (by rfl) ⟨1283951, by rfl⟩ : syracuseStep 1711935 = 2567903) B2567903
theorem B1711975 : Blo 1711056 1711975 := bstep (se 1 (by rfl) ⟨1283981, by rfl⟩ : syracuseStep 1711975 = 2567963) B2567963
theorem B1712063 : Blo 1711056 1712063 := bstep (se 1 (by rfl) ⟨1284047, by rfl⟩ : syracuseStep 1712063 = 2568095) B2568095
theorem B98729927 : Blo 1711056 98729927 := bstep (se 1 (by rfl) ⟨74047445, by rfl⟩ : syracuseStep 98729927 = 148094891) B148094891
theorem B21929939 : Blo 1711056 21929939 := bstep (se 1 (by rfl) ⟨16447454, by rfl⟩ : syracuseStep 21929939 = 32894909) B32894909
theorem B1712351 : Blo 1711056 1712351 := bstep (se 1 (by rfl) ⟨1284263, by rfl⟩ : syracuseStep 1712351 = 2568527) B2568527
theorem B5775623 : Blo 1711056 5775623 := bstep (se 1 (by rfl) ⟨4331717, by rfl⟩ : syracuseStep 5775623 = 8663435) B8663435
theorem B1712831 : Blo 1711056 1712831 := bstep (se 1 (by rfl) ⟨1284623, by rfl⟩ : syracuseStep 1712831 = 2569247) B2569247
theorem B1712999 : Blo 1711056 1712999 := bstep (se 1 (by rfl) ⟨1284749, by rfl⟩ : syracuseStep 1712999 = 2569499) B2569499
theorem B14632123 : Blo 1711056 14632123 := bstep (se 1 (by rfl) ⟨10974092, by rfl⟩ : syracuseStep 14632123 = 21948185) B21948185
theorem B37545169 : Blo 1711056 37545169 := bstep (se 2 (by rfl) ⟨14079438, by rfl⟩ : syracuseStep 37545169 = 28158877) B28158877
theorem B3851711 : Blo 1711056 3851711 := bstep (se 1 (by rfl) ⟨2888783, by rfl⟩ : syracuseStep 3851711 = 5777567) B5777567
theorem B5776865 : Blo 1711056 5776865 := bstep (se 2 (by rfl) ⟨2166324, by rfl⟩ : syracuseStep 5776865 = 4332649) B4332649
theorem B4941415 : Blo 1711056 4941415 := bstep (se 1 (by rfl) ⟨3706061, by rfl⟩ : syracuseStep 4941415 = 7412123) B7412123
theorem B9251003 : Blo 1711056 9251003 := bstep (se 1 (by rfl) ⟨6938252, by rfl⟩ : syracuseStep 9251003 = 13876505) B13876505
theorem B3852665 : Blo 1711056 3852665 := bstep (se 2 (by rfl) ⟨1444749, by rfl⟩ : syracuseStep 3852665 = 2889499) B2889499
theorem B4114921 : Blo 1711056 4114921 := bstep (se 2 (by rfl) ⟨1543095, by rfl⟩ : syracuseStep 4114921 = 3086191) B3086191
theorem B5483305 : Blo 1711056 5483305 := bstep (se 2 (by rfl) ⟨2056239, by rfl⟩ : syracuseStep 5483305 = 4112479) B4112479
theorem B111004739 : Blo 1711056 111004739 := bstep (se 1 (by rfl) ⟨83253554, by rfl⟩ : syracuseStep 111004739 = 166507109) B166507109
theorem B2567279 : Blo 1711056 2567279 := bstep (se 1 (by rfl) ⟨1925459, by rfl⟩ : syracuseStep 2567279 = 3850919) B3850919
theorem B13003901 : Blo 1711056 13003901 := bstep (se 3 (by rfl) ⟨2438231, by rfl⟩ : syracuseStep 13003901 = 4876463) B4876463
theorem B2567327 : Blo 1711056 2567327 := bstep (se 1 (by rfl) ⟨1925495, by rfl⟩ : syracuseStep 2567327 = 3850991) B3850991
theorem B10964251 : Blo 1711056 10964251 := bstep (se 1 (by rfl) ⟨8223188, by rfl⟩ : syracuseStep 10964251 = 16446377) B16446377
theorem B9752015 : Blo 1711056 9752015 := bstep (se 1 (by rfl) ⟨7314011, by rfl⟩ : syracuseStep 9752015 = 14628023) B14628023
theorem B3854015 : Blo 1711056 3854015 := bstep (se 1 (by rfl) ⟨2890511, by rfl⟩ : syracuseStep 3854015 = 5781023) B5781023
theorem B2568263 : Blo 1711056 2568263 := bstep (se 1 (by rfl) ⟨1926197, by rfl⟩ : syracuseStep 2568263 = 3852395) B3852395
theorem B9752723 : Blo 1711056 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B32919817 : Blo 1711056 32919817 := bstep (se 2 (by rfl) ⟨12344931, by rfl⟩ : syracuseStep 32919817 = 24689863) B24689863
theorem B6500843 : Blo 1711056 6500843 := bstep (se 1 (by rfl) ⟨4875632, by rfl⟩ : syracuseStep 6500843 = 9751265) B9751265
theorem B2568683 : Blo 1711056 2568683 := bstep (se 1 (by rfl) ⟨1926512, by rfl⟩ : syracuseStep 2568683 = 3853025) B3853025
theorem B8663759 : Blo 1711056 8663759 := bstep (se 1 (by rfl) ⟨6497819, by rfl⟩ : syracuseStep 8663759 = 12995639) B12995639
theorem B2568935 : Blo 1711056 2568935 := bstep (se 1 (by rfl) ⟨1926701, by rfl⟩ : syracuseStep 2568935 = 3853403) B3853403
theorem B2569031 : Blo 1711056 2569031 := bstep (se 1 (by rfl) ⟨1926773, by rfl⟩ : syracuseStep 2569031 = 3853547) B3853547
theorem B2167879 : Blo 1711056 2167879 := bstep (se 1 (by rfl) ⟨1625909, by rfl⟩ : syracuseStep 2167879 = 3251819) B3251819
theorem B2167975 : Blo 1711056 2167975 := bstep (se 1 (by rfl) ⟨1625981, by rfl⟩ : syracuseStep 2167975 = 3251963) B3251963
theorem B20821175 : Blo 1711056 20821175 := bstep (se 1 (by rfl) ⟨15615881, by rfl⟩ : syracuseStep 20821175 = 31231763) B31231763
theorem B65819951 : Blo 1711056 65819951 := bstep (se 1 (by rfl) ⟨49364963, by rfl⟩ : syracuseStep 65819951 = 98729927) B98729927
theorem B14619959 : Blo 1711056 14619959 := bstep (se 1 (by rfl) ⟨10964969, by rfl⟩ : syracuseStep 14619959 = 21929939) B21929939
theorem B2471401 : Blo 1711056 2471401 := bstep (se 2 (by rfl) ⟨926775, by rfl⟩ : syracuseStep 2471401 = 1853551) B1853551
theorem B5780969 : Blo 1711056 5780969 := bstep (se 2 (by rfl) ⟨2167863, by rfl⟩ : syracuseStep 5780969 = 4335727) B4335727
theorem B4332143 : Blo 1711056 4332143 := bstep (se 1 (by rfl) ⟨3249107, by rfl⟩ : syracuseStep 4332143 = 6498215) B6498215
theorem B21928913 : Blo 1711056 21928913 := bstep (se 2 (by rfl) ⟨8223342, by rfl⟩ : syracuseStep 21928913 = 16446685) B16446685
theorem B1711071 : Blo 1711056 1711071 := bstep (se 1 (by rfl) ⟨1283303, by rfl⟩ : syracuseStep 1711071 = 2566607) B2566607
theorem B10968047 : Blo 1711056 10968047 := bstep (se 1 (by rfl) ⟨8226035, by rfl⟩ : syracuseStep 10968047 = 16452071) B16452071
theorem B29244563 : Blo 1711056 29244563 := bstep (se 1 (by rfl) ⟨21933422, by rfl⟩ : syracuseStep 29244563 = 43866845) B43866845
theorem B4111663 : Blo 1711056 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B1711583 : Blo 1711056 1711583 := bstep (se 1 (by rfl) ⟨1283687, by rfl⟩ : syracuseStep 1711583 = 2567375) B2567375
theorem B38018771 : Blo 1711056 38018771 := bstep (se 1 (by rfl) ⟨28514078, by rfl⟩ : syracuseStep 38018771 = 57028157) B57028157
theorem B4628249 : Blo 1711056 4628249 := bstep (se 2 (by rfl) ⟨1735593, by rfl⟩ : syracuseStep 4628249 = 3471187) B3471187
theorem B1712175 : Blo 1711056 1712175 := bstep (se 1 (by rfl) ⟨1284131, by rfl⟩ : syracuseStep 1712175 = 2568263) B2568263
theorem B3850415 : Blo 1711056 3850415 := bstep (se 1 (by rfl) ⟨2887811, by rfl⟩ : syracuseStep 3850415 = 5775623) B5775623
theorem B4333895 : Blo 1711056 4333895 := bstep (se 1 (by rfl) ⟨3250421, by rfl⟩ : syracuseStep 4333895 = 6500843) B6500843
theorem B1712455 : Blo 1711056 1712455 := bstep (se 1 (by rfl) ⟨1284341, by rfl⟩ : syracuseStep 1712455 = 2568683) B2568683
theorem B43893089 : Blo 1711056 43893089 := bstep (se 2 (by rfl) ⟨16459908, by rfl⟩ : syracuseStep 43893089 = 32919817) B32919817
theorem B5775839 : Blo 1711056 5775839 := bstep (se 1 (by rfl) ⟨4331879, by rfl⟩ : syracuseStep 5775839 = 8663759) B8663759
theorem B1712623 : Blo 1711056 1712623 := bstep (se 1 (by rfl) ⟨1284467, by rfl⟩ : syracuseStep 1712623 = 2568935) B2568935
theorem B1712687 : Blo 1711056 1712687 := bstep (se 1 (by rfl) ⟨1284515, by rfl⟩ : syracuseStep 1712687 = 2569031) B2569031
theorem B3851243 : Blo 1711056 3851243 := bstep (se 1 (by rfl) ⟨2888432, by rfl⟩ : syracuseStep 3851243 = 5776865) B5776865
theorem B5482217 : Blo 1711056 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B8669267 : Blo 1711056 8669267 := bstep (se 1 (by rfl) ⟨6501950, by rfl⟩ : syracuseStep 8669267 = 13003901) B13003901
theorem B6588553 : Blo 1711056 6588553 := bstep (se 2 (by rfl) ⟨2470707, by rfl⟩ : syracuseStep 6588553 = 4941415) B4941415
theorem B13880783 : Blo 1711056 13880783 := bstep (se 1 (by rfl) ⟨10410587, by rfl⟩ : syracuseStep 13880783 = 20821175) B20821175
theorem B43879967 : Blo 1711056 43879967 := bstep (se 1 (by rfl) ⟨32909975, by rfl⟩ : syracuseStep 43879967 = 65819951) B65819951
theorem B2567807 : Blo 1711056 2567807 := bstep (se 1 (by rfl) ⟨1925855, by rfl⟩ : syracuseStep 2567807 = 3851711) B3851711
theorem B3853979 : Blo 1711056 3853979 := bstep (se 1 (by rfl) ⟨2890484, by rfl⟩ : syracuseStep 3853979 = 5780969) B5780969
theorem B7311073 : Blo 1711056 7311073 := bstep (se 2 (by rfl) ⟨2741652, by rfl⟩ : syracuseStep 7311073 = 5483305) B5483305
theorem B19509497 : Blo 1711056 19509497 := bstep (se 2 (by rfl) ⟨7316061, by rfl⟩ : syracuseStep 19509497 = 14632123) B14632123
theorem B2568443 : Blo 1711056 2568443 := bstep (se 1 (by rfl) ⟨1926332, by rfl⟩ : syracuseStep 2568443 = 3852665) B3852665
theorem B14619001 : Blo 1711056 14619001 := bstep (se 2 (by rfl) ⟨5482125, by rfl⟩ : syracuseStep 14619001 = 10964251) B10964251
theorem B2888095 : Blo 1711056 2888095 := bstep (se 1 (by rfl) ⟨2166071, by rfl⟩ : syracuseStep 2888095 = 4332143) B4332143
theorem B14619275 : Blo 1711056 14619275 := bstep (se 1 (by rfl) ⟨10964456, by rfl⟩ : syracuseStep 14619275 = 21928913) B21928913
theorem B7312031 : Blo 1711056 7312031 := bstep (se 1 (by rfl) ⟨5484023, by rfl⟩ : syracuseStep 7312031 = 10968047) B10968047
theorem B74003159 : Blo 1711056 74003159 := bstep (se 1 (by rfl) ⟨55502369, by rfl⟩ : syracuseStep 74003159 = 111004739) B111004739
theorem B6501343 : Blo 1711056 6501343 := bstep (se 1 (by rfl) ⟨4876007, by rfl⟩ : syracuseStep 6501343 = 9752015) B9752015
theorem B2569343 : Blo 1711056 2569343 := bstep (se 1 (by rfl) ⟨1927007, by rfl⟩ : syracuseStep 2569343 = 3854015) B3854015
theorem B3085499 : Blo 1711056 3085499 := bstep (se 1 (by rfl) ⟨2314124, by rfl⟩ : syracuseStep 3085499 = 4628249) B4628249
theorem B6501815 : Blo 1711056 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B5486561 : Blo 1711056 5486561 := bstep (se 2 (by rfl) ⟨2057460, by rfl⟩ : syracuseStep 5486561 = 4114921) B4114921
theorem B9746639 : Blo 1711056 9746639 := bstep (se 1 (by rfl) ⟨7309979, by rfl⟩ : syracuseStep 9746639 = 14619959) B14619959
theorem B2890505 : Blo 1711056 2890505 := bstep (se 2 (by rfl) ⟨1083939, by rfl⟩ : syracuseStep 2890505 = 2167879) B2167879
theorem B6167335 : Blo 1711056 6167335 := bstep (se 1 (by rfl) ⟨4625501, by rfl⟩ : syracuseStep 6167335 = 9251003) B9251003
theorem B2890633 : Blo 1711056 2890633 := bstep (se 2 (by rfl) ⟨1083987, by rfl⟩ : syracuseStep 2890633 = 2167975) B2167975
theorem B50060225 : Blo 1711056 50060225 := bstep (se 2 (by rfl) ⟨18772584, by rfl⟩ : syracuseStep 50060225 = 37545169) B37545169
theorem B1711519 : Blo 1711056 1711519 := bstep (se 1 (by rfl) ⟨1283639, by rfl⟩ : syracuseStep 1711519 = 2567279) B2567279
theorem B19496375 : Blo 1711056 19496375 := bstep (se 1 (by rfl) ⟨14622281, by rfl⟩ : syracuseStep 19496375 = 29244563) B29244563
theorem B1711551 : Blo 1711056 1711551 := bstep (se 1 (by rfl) ⟨1283663, by rfl⟩ : syracuseStep 1711551 = 2567327) B2567327
theorem B25345847 : Blo 1711056 25345847 := bstep (se 1 (by rfl) ⟨19009385, by rfl⟩ : syracuseStep 25345847 = 38018771) B38018771
theorem B13180805 : Blo 1711056 13180805 := bstep (se 4 (by rfl) ⟨1235700, by rfl⟩ : syracuseStep 13180805 = 2471401) B2471401
theorem B1712295 : Blo 1711056 1712295 := bstep (se 1 (by rfl) ⟨1284221, by rfl⟩ : syracuseStep 1712295 = 2568443) B2568443
theorem B29262059 : Blo 1711056 29262059 := bstep (se 1 (by rfl) ⟨21946544, by rfl⟩ : syracuseStep 29262059 = 43893089) B43893089
theorem B3850559 : Blo 1711056 3850559 := bstep (se 1 (by rfl) ⟨2887919, by rfl⟩ : syracuseStep 3850559 = 5775839) B5775839
theorem B4874687 : Blo 1711056 4874687 := bstep (se 1 (by rfl) ⟨3656015, by rfl⟩ : syracuseStep 4874687 = 7312031) B7312031
theorem B3850793 : Blo 1711056 3850793 := bstep (se 2 (by rfl) ⟨1444047, by rfl⟩ : syracuseStep 3850793 = 2888095) B2888095
theorem B1712895 : Blo 1711056 1712895 := bstep (se 1 (by rfl) ⟨1284671, by rfl⟩ : syracuseStep 1712895 = 2569343) B2569343
theorem B2056999 : Blo 1711056 2056999 := bstep (se 1 (by rfl) ⟨1542749, by rfl⟩ : syracuseStep 2056999 = 3085499) B3085499
theorem B4334543 : Blo 1711056 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B3654811 : Blo 1711056 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B8668457 : Blo 1711056 8668457 := bstep (se 2 (by rfl) ⟨3250671, by rfl⟩ : syracuseStep 8668457 = 6501343) B6501343
theorem B6497759 : Blo 1711056 6497759 := bstep (se 1 (by rfl) ⟨4873319, by rfl⟩ : syracuseStep 6497759 = 9746639) B9746639
theorem B1927003 : Blo 1711056 1927003 := bstep (se 1 (by rfl) ⟨1445252, by rfl⟩ : syracuseStep 1927003 = 2890505) B2890505
theorem B2566943 : Blo 1711056 2566943 := bstep (se 1 (by rfl) ⟨1925207, by rfl⟩ : syracuseStep 2566943 = 3850415) B3850415
theorem B8784737 : Blo 1711056 8784737 := bstep (se 2 (by rfl) ⟨3294276, by rfl⟩ : syracuseStep 8784737 = 6588553) B6588553
theorem B49335439 : Blo 1711056 49335439 := bstep (se 1 (by rfl) ⟨37001579, by rfl⟩ : syracuseStep 49335439 = 74003159) B74003159
theorem B19492001 : Blo 1711056 19492001 := bstep (se 2 (by rfl) ⟨7309500, by rfl⟩ : syracuseStep 19492001 = 14619001) B14619001
theorem B2567495 : Blo 1711056 2567495 := bstep (se 1 (by rfl) ⟨1925621, by rfl⟩ : syracuseStep 2567495 = 3851243) B3851243
theorem B3854177 : Blo 1711056 3854177 := bstep (se 2 (by rfl) ⟨1445316, by rfl⟩ : syracuseStep 3854177 = 2890633) B2890633
theorem B3657707 : Blo 1711056 3657707 := bstep (se 1 (by rfl) ⟨2743280, by rfl⟩ : syracuseStep 3657707 = 5486561) B5486561
theorem B5779511 : Blo 1711056 5779511 := bstep (se 1 (by rfl) ⟨4334633, by rfl⟩ : syracuseStep 5779511 = 8669267) B8669267
theorem B12997583 : Blo 1711056 12997583 := bstep (se 1 (by rfl) ⟨9748187, by rfl⟩ : syracuseStep 12997583 = 19496375) B19496375
theorem B9253855 : Blo 1711056 9253855 := bstep (se 1 (by rfl) ⟨6940391, by rfl⟩ : syracuseStep 9253855 = 13880783) B13880783
theorem B2569319 : Blo 1711056 2569319 := bstep (se 1 (by rfl) ⟨1926989, by rfl⟩ : syracuseStep 2569319 = 3853979) B3853979
theorem B133493933 : Blo 1711056 133493933 := bstep (se 3 (by rfl) ⟨25030112, by rfl⟩ : syracuseStep 133493933 = 50060225) B50060225
theorem B16897231 : Blo 1711056 16897231 := bstep (se 1 (by rfl) ⟨12672923, by rfl⟩ : syracuseStep 16897231 = 25345847) B25345847
theorem B8787203 : Blo 1711056 8787203 := bstep (se 1 (by rfl) ⟨6590402, by rfl⟩ : syracuseStep 8787203 = 13180805) B13180805
theorem B13006331 : Blo 1711056 13006331 := bstep (se 1 (by rfl) ⟨9754748, by rfl⟩ : syracuseStep 13006331 = 19509497) B19509497
theorem B2889263 : Blo 1711056 2889263 := bstep (se 1 (by rfl) ⟨2166947, by rfl⟩ : syracuseStep 2889263 = 4333895) B4333895
theorem B9746183 : Blo 1711056 9746183 := bstep (se 1 (by rfl) ⟨7309637, by rfl⟩ : syracuseStep 9746183 = 14619275) B14619275
theorem B8223113 : Blo 1711056 8223113 := bstep (se 2 (by rfl) ⟨3083667, by rfl⟩ : syracuseStep 8223113 = 6167335) B6167335
theorem B9748097 : Blo 1711056 9748097 := bstep (se 2 (by rfl) ⟨3655536, by rfl⟩ : syracuseStep 9748097 = 7311073) B7311073
theorem B29253311 : Blo 1711056 29253311 := bstep (se 1 (by rfl) ⟨21939983, by rfl⟩ : syracuseStep 29253311 = 43879967) B43879967
theorem B1711871 : Blo 1711056 1711871 := bstep (se 1 (by rfl) ⟨1283903, by rfl⟩ : syracuseStep 1711871 = 2567807) B2567807
theorem B355983821 : Blo 1711056 355983821 := bstep (se 3 (by rfl) ⟨66746966, by rfl⟩ : syracuseStep 355983821 = 133493933) B133493933
theorem B1712879 : Blo 1711056 1712879 := bstep (se 1 (by rfl) ⟨1284659, by rfl⟩ : syracuseStep 1712879 = 2569319) B2569319
theorem B5858135 : Blo 1711056 5858135 := bstep (se 1 (by rfl) ⟨4393601, by rfl⟩ : syracuseStep 5858135 = 8787203) B8787203
theorem B1926175 : Blo 1711056 1926175 := bstep (se 1 (by rfl) ⟨1444631, by rfl⟩ : syracuseStep 1926175 = 2889263) B2889263
theorem B6497455 : Blo 1711056 6497455 := bstep (se 1 (by rfl) ⟨4873091, by rfl⟩ : syracuseStep 6497455 = 9746183) B9746183
theorem B5482075 : Blo 1711056 5482075 := bstep (se 1 (by rfl) ⟨4111556, by rfl⟩ : syracuseStep 5482075 = 8223113) B8223113
theorem B12994667 : Blo 1711056 12994667 := bstep (se 1 (by rfl) ⟨9746000, by rfl⟩ : syracuseStep 12994667 = 19492001) B19492001
theorem B6498731 : Blo 1711056 6498731 := bstep (se 1 (by rfl) ⟨4874048, by rfl⟩ : syracuseStep 6498731 = 9748097) B9748097
theorem B3853007 : Blo 1711056 3853007 := bstep (se 1 (by rfl) ⟨2889755, by rfl⟩ : syracuseStep 3853007 = 5779511) B5779511
theorem B19508039 : Blo 1711056 19508039 := bstep (se 1 (by rfl) ⟨14631029, by rfl⟩ : syracuseStep 19508039 = 29262059) B29262059
theorem B2567039 : Blo 1711056 2567039 := bstep (se 1 (by rfl) ⟨1925279, by rfl⟩ : syracuseStep 2567039 = 3850559) B3850559
theorem B2567195 : Blo 1711056 2567195 := bstep (se 1 (by rfl) ⟨1925396, by rfl⟩ : syracuseStep 2567195 = 3850793) B3850793
theorem B5778971 : Blo 1711056 5778971 := bstep (se 1 (by rfl) ⟨4334228, by rfl⟩ : syracuseStep 5778971 = 8668457) B8668457
theorem B8670887 : Blo 1711056 8670887 := bstep (se 1 (by rfl) ⟨6503165, by rfl⟩ : syracuseStep 8670887 = 13006331) B13006331
theorem B2569337 : Blo 1711056 2569337 := bstep (se 2 (by rfl) ⟨963501, by rfl⟩ : syracuseStep 2569337 = 1927003) B1927003
theorem B19502207 : Blo 1711056 19502207 := bstep (se 1 (by rfl) ⟨14626655, by rfl⟩ : syracuseStep 19502207 = 29253311) B29253311
theorem B49353893 : Blo 1711056 49353893 := bstep (se 4 (by rfl) ⟨4626927, by rfl⟩ : syracuseStep 49353893 = 9253855) B9253855
theorem B2569451 : Blo 1711056 2569451 := bstep (se 1 (by rfl) ⟨1927088, by rfl⟩ : syracuseStep 2569451 = 3854177) B3854177
theorem B2438471 : Blo 1711056 2438471 := bstep (se 1 (by rfl) ⟨1828853, by rfl⟩ : syracuseStep 2438471 = 3657707) B3657707
theorem B3249791 : Blo 1711056 3249791 := bstep (se 1 (by rfl) ⟨2437343, by rfl⟩ : syracuseStep 3249791 = 4874687) B4874687
theorem B8665055 : Blo 1711056 8665055 := bstep (se 1 (by rfl) ⟨6498791, by rfl⟩ : syracuseStep 8665055 = 12997583) B12997583
theorem B2889695 : Blo 1711056 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B4331839 : Blo 1711056 4331839 := bstep (se 1 (by rfl) ⟨3248879, by rfl⟩ : syracuseStep 4331839 = 6497759) B6497759
theorem B2742665 : Blo 1711056 2742665 := bstep (se 2 (by rfl) ⟨1028499, by rfl⟩ : syracuseStep 2742665 = 2056999) B2056999
theorem B90118565 : Blo 1711056 90118565 := bstep (se 4 (by rfl) ⟨8448615, by rfl⟩ : syracuseStep 90118565 = 16897231) B16897231
theorem B65780585 : Blo 1711056 65780585 := bstep (se 2 (by rfl) ⟨24667719, by rfl⟩ : syracuseStep 65780585 = 49335439) B49335439
theorem B4873081 : Blo 1711056 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B1711295 : Blo 1711056 1711295 := bstep (se 1 (by rfl) ⟨1283471, by rfl⟩ : syracuseStep 1711295 = 2566943) B2566943
theorem B5856491 : Blo 1711056 5856491 := bstep (se 1 (by rfl) ⟨4392368, by rfl⟩ : syracuseStep 5856491 = 8784737) B8784737
theorem B1711663 : Blo 1711056 1711663 := bstep (se 1 (by rfl) ⟨1283747, by rfl⟩ : syracuseStep 1711663 = 2567495) B2567495
theorem B237322547 : Blo 1711056 237322547 := bstep (se 1 (by rfl) ⟨177991910, by rfl⟩ : syracuseStep 237322547 = 355983821) B355983821
theorem B5775785 : Blo 1711056 5775785 := bstep (se 2 (by rfl) ⟨2165919, by rfl⟩ : syracuseStep 5775785 = 4331839) B4331839
theorem B1712891 : Blo 1711056 1712891 := bstep (se 1 (by rfl) ⟨1284668, by rfl⟩ : syracuseStep 1712891 = 2569337) B2569337
theorem B13001471 : Blo 1711056 13001471 := bstep (se 1 (by rfl) ⟨9751103, by rfl⟩ : syracuseStep 13001471 = 19502207) B19502207
theorem B1712967 : Blo 1711056 1712967 := bstep (se 1 (by rfl) ⟨1284725, by rfl⟩ : syracuseStep 1712967 = 2569451) B2569451
theorem B6497441 : Blo 1711056 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B5776703 : Blo 1711056 5776703 := bstep (se 1 (by rfl) ⟨4332527, by rfl⟩ : syracuseStep 5776703 = 8665055) B8665055
theorem B1926463 : Blo 1711056 1926463 := bstep (se 1 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 1926463 = 2889695) B2889695
theorem B43853723 : Blo 1711056 43853723 := bstep (se 1 (by rfl) ⟨32890292, by rfl⟩ : syracuseStep 43853723 = 65780585) B65780585
theorem B7309433 : Blo 1711056 7309433 := bstep (se 2 (by rfl) ⟨2741037, by rfl⟩ : syracuseStep 7309433 = 5482075) B5482075
theorem B3852647 : Blo 1711056 3852647 := bstep (se 1 (by rfl) ⟨2889485, by rfl⟩ : syracuseStep 3852647 = 5778971) B5778971
theorem B32902595 : Blo 1711056 32902595 := bstep (se 1 (by rfl) ⟨24676946, by rfl⟩ : syracuseStep 32902595 = 49353893) B49353893
theorem B2166527 : Blo 1711056 2166527 := bstep (se 1 (by rfl) ⟨1624895, by rfl⟩ : syracuseStep 2166527 = 3249791) B3249791
theorem B2568233 : Blo 1711056 2568233 := bstep (se 2 (by rfl) ⟨963087, by rfl⟩ : syracuseStep 2568233 = 1926175) B1926175
theorem B8663111 : Blo 1711056 8663111 := bstep (se 1 (by rfl) ⟨6497333, by rfl⟩ : syracuseStep 8663111 = 12994667) B12994667
theorem B8663273 : Blo 1711056 8663273 := bstep (se 2 (by rfl) ⟨3248727, by rfl⟩ : syracuseStep 8663273 = 6497455) B6497455
theorem B2568671 : Blo 1711056 2568671 := bstep (se 1 (by rfl) ⟨1926503, by rfl⟩ : syracuseStep 2568671 = 3853007) B3853007
theorem B13005359 : Blo 1711056 13005359 := bstep (se 1 (by rfl) ⟨9754019, by rfl⟩ : syracuseStep 13005359 = 19508039) B19508039
theorem B3904327 : Blo 1711056 3904327 := bstep (se 1 (by rfl) ⟨2928245, by rfl⟩ : syracuseStep 3904327 = 5856491) B5856491
theorem B5780591 : Blo 1711056 5780591 := bstep (se 1 (by rfl) ⟨4335443, by rfl⟩ : syracuseStep 5780591 = 8670887) B8670887
theorem B3905423 : Blo 1711056 3905423 := bstep (se 1 (by rfl) ⟨2929067, by rfl⟩ : syracuseStep 3905423 = 5858135) B5858135
theorem B6502589 : Blo 1711056 6502589 := bstep (se 3 (by rfl) ⟨1219235, by rfl⟩ : syracuseStep 6502589 = 2438471) B2438471
theorem B7313773 : Blo 1711056 7313773 := bstep (se 3 (by rfl) ⟨1371332, by rfl⟩ : syracuseStep 7313773 = 2742665) B2742665
theorem B60079043 : Blo 1711056 60079043 := bstep (se 1 (by rfl) ⟨45059282, by rfl⟩ : syracuseStep 60079043 = 90118565) B90118565
theorem B4332487 : Blo 1711056 4332487 := bstep (se 1 (by rfl) ⟨3249365, by rfl⟩ : syracuseStep 4332487 = 6498731) B6498731
theorem B1711359 : Blo 1711056 1711359 := bstep (se 1 (by rfl) ⟨1283519, by rfl⟩ : syracuseStep 1711359 = 2567039) B2567039
theorem B1711463 : Blo 1711056 1711463 := bstep (se 1 (by rfl) ⟨1283597, by rfl⟩ : syracuseStep 1711463 = 2567195) B2567195
theorem B1712155 : Blo 1711056 1712155 := bstep (se 1 (by rfl) ⟨1284116, by rfl⟩ : syracuseStep 1712155 = 2568233) B2568233
theorem B5775407 : Blo 1711056 5775407 := bstep (se 1 (by rfl) ⟨4331555, by rfl⟩ : syracuseStep 5775407 = 8663111) B8663111
theorem B5775515 : Blo 1711056 5775515 := bstep (se 1 (by rfl) ⟨4331636, by rfl⟩ : syracuseStep 5775515 = 8663273) B8663273
theorem B3850523 : Blo 1711056 3850523 := bstep (se 1 (by rfl) ⟨2887892, by rfl⟩ : syracuseStep 3850523 = 5775785) B5775785
theorem B1712447 : Blo 1711056 1712447 := bstep (se 1 (by rfl) ⟨1284335, by rfl⟩ : syracuseStep 1712447 = 2568671) B2568671
theorem B8667647 : Blo 1711056 8667647 := bstep (se 1 (by rfl) ⟨6500735, by rfl⟩ : syracuseStep 8667647 = 13001471) B13001471
theorem B3851135 : Blo 1711056 3851135 := bstep (se 1 (by rfl) ⟨2888351, by rfl⟩ : syracuseStep 3851135 = 5776703) B5776703
theorem B5776649 : Blo 1711056 5776649 := bstep (se 2 (by rfl) ⟨2166243, by rfl⟩ : syracuseStep 5776649 = 4332487) B4332487
theorem B4335059 : Blo 1711056 4335059 := bstep (se 1 (by rfl) ⟨3251294, by rfl⟩ : syracuseStep 4335059 = 6502589) B6502589
theorem B5777405 : Blo 1711056 5777405 := bstep (se 3 (by rfl) ⟨1083263, by rfl⟩ : syracuseStep 5777405 = 2166527) B2166527
theorem B158215031 : Blo 1711056 158215031 := bstep (se 1 (by rfl) ⟨118661273, by rfl⟩ : syracuseStep 158215031 = 237322547) B237322547
theorem B8670239 : Blo 1711056 8670239 := bstep (se 1 (by rfl) ⟨6502679, by rfl⟩ : syracuseStep 8670239 = 13005359) B13005359
theorem B9751697 : Blo 1711056 9751697 := bstep (se 2 (by rfl) ⟨3656886, by rfl⟩ : syracuseStep 9751697 = 7313773) B7313773
theorem B3853727 : Blo 1711056 3853727 := bstep (se 1 (by rfl) ⟨2890295, by rfl⟩ : syracuseStep 3853727 = 5780591) B5780591
theorem B2568431 : Blo 1711056 2568431 := bstep (se 1 (by rfl) ⟨1926323, by rfl⟩ : syracuseStep 2568431 = 3852647) B3852647
theorem B2568617 : Blo 1711056 2568617 := bstep (se 2 (by rfl) ⟨963231, by rfl⟩ : syracuseStep 2568617 = 1926463) B1926463
theorem B21935063 : Blo 1711056 21935063 := bstep (se 1 (by rfl) ⟨16451297, by rfl⟩ : syracuseStep 21935063 = 32902595) B32902595
theorem B4331627 : Blo 1711056 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B2603615 : Blo 1711056 2603615 := bstep (se 1 (by rfl) ⟨1952711, by rfl⟩ : syracuseStep 2603615 = 3905423) B3905423
theorem B29235815 : Blo 1711056 29235815 := bstep (se 1 (by rfl) ⟨21926861, by rfl⟩ : syracuseStep 29235815 = 43853723) B43853723
theorem B4872955 : Blo 1711056 4872955 := bstep (se 1 (by rfl) ⟨3654716, by rfl⟩ : syracuseStep 4872955 = 7309433) B7309433
theorem B20823077 : Blo 1711056 20823077 := bstep (se 4 (by rfl) ⟨1952163, by rfl⟩ : syracuseStep 20823077 = 3904327) B3904327
theorem B160210781 : Blo 1711056 160210781 := bstep (se 3 (by rfl) ⟨30039521, by rfl⟩ : syracuseStep 160210781 = 60079043) B60079043
theorem B3850271 : Blo 1711056 3850271 := bstep (se 1 (by rfl) ⟨2887703, by rfl⟩ : syracuseStep 3850271 = 5775407) B5775407
theorem B3850343 : Blo 1711056 3850343 := bstep (se 1 (by rfl) ⟨2887757, by rfl⟩ : syracuseStep 3850343 = 5775515) B5775515
theorem B1712287 : Blo 1711056 1712287 := bstep (se 1 (by rfl) ⟨1284215, by rfl⟩ : syracuseStep 1712287 = 2568431) B2568431
theorem B1712411 : Blo 1711056 1712411 := bstep (se 1 (by rfl) ⟨1284308, by rfl⟩ : syracuseStep 1712411 = 2568617) B2568617
theorem B14623375 : Blo 1711056 14623375 := bstep (se 1 (by rfl) ⟨10967531, by rfl⟩ : syracuseStep 14623375 = 21935063) B21935063
theorem B3851099 : Blo 1711056 3851099 := bstep (se 1 (by rfl) ⟨2888324, by rfl⟩ : syracuseStep 3851099 = 5776649) B5776649
theorem B27771893 : Blo 1711056 27771893 := bstep (se 5 (by rfl) ⟨1301807, by rfl⟩ : syracuseStep 27771893 = 2603615) B2603615
theorem B6497273 : Blo 1711056 6497273 := bstep (se 2 (by rfl) ⟨2436477, by rfl⟩ : syracuseStep 6497273 = 4872955) B4872955
theorem B3851603 : Blo 1711056 3851603 := bstep (se 1 (by rfl) ⟨2888702, by rfl⟩ : syracuseStep 3851603 = 5777405) B5777405
theorem B19490543 : Blo 1711056 19490543 := bstep (se 1 (by rfl) ⟨14617907, by rfl⟩ : syracuseStep 19490543 = 29235815) B29235815
theorem B2567015 : Blo 1711056 2567015 := bstep (se 1 (by rfl) ⟨1925261, by rfl⟩ : syracuseStep 2567015 = 3850523) B3850523
theorem B5778431 : Blo 1711056 5778431 := bstep (se 1 (by rfl) ⟨4333823, by rfl⟩ : syracuseStep 5778431 = 8667647) B8667647
theorem B2567423 : Blo 1711056 2567423 := bstep (se 1 (by rfl) ⟨1925567, by rfl⟩ : syracuseStep 2567423 = 3851135) B3851135
theorem B2887751 : Blo 1711056 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B105476687 : Blo 1711056 105476687 := bstep (se 1 (by rfl) ⟨79107515, by rfl⟩ : syracuseStep 105476687 = 158215031) B158215031
theorem B5780159 : Blo 1711056 5780159 := bstep (se 1 (by rfl) ⟨4335119, by rfl⟩ : syracuseStep 5780159 = 8670239) B8670239
theorem B13882051 : Blo 1711056 13882051 := bstep (se 1 (by rfl) ⟨10411538, by rfl⟩ : syracuseStep 13882051 = 20823077) B20823077
theorem B6501131 : Blo 1711056 6501131 := bstep (se 1 (by rfl) ⟨4875848, by rfl⟩ : syracuseStep 6501131 = 9751697) B9751697
theorem B2569151 : Blo 1711056 2569151 := bstep (se 1 (by rfl) ⟨1926863, by rfl⟩ : syracuseStep 2569151 = 3853727) B3853727
theorem B2890039 : Blo 1711056 2890039 := bstep (se 1 (by rfl) ⟨2167529, by rfl⟩ : syracuseStep 2890039 = 4335059) B4335059
theorem B106807187 : Blo 1711056 106807187 := bstep (se 1 (by rfl) ⟨80105390, by rfl⟩ : syracuseStep 106807187 = 160210781) B160210781
theorem B1925167 : Blo 1711056 1925167 := bstep (se 1 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 1925167 = 2887751) B2887751
theorem B4334087 : Blo 1711056 4334087 := bstep (se 1 (by rfl) ⟨3250565, by rfl⟩ : syracuseStep 4334087 = 6501131) B6501131
theorem B1712767 : Blo 1711056 1712767 := bstep (se 1 (by rfl) ⟨1284575, by rfl⟩ : syracuseStep 1712767 = 2569151) B2569151
theorem B18514595 : Blo 1711056 18514595 := bstep (se 1 (by rfl) ⟨13885946, by rfl⟩ : syracuseStep 18514595 = 27771893) B27771893
theorem B19497833 : Blo 1711056 19497833 := bstep (se 2 (by rfl) ⟨7311687, by rfl⟩ : syracuseStep 19497833 = 14623375) B14623375
theorem B12993695 : Blo 1711056 12993695 := bstep (se 1 (by rfl) ⟨9745271, by rfl⟩ : syracuseStep 12993695 = 19490543) B19490543
theorem B3852287 : Blo 1711056 3852287 := bstep (se 1 (by rfl) ⟨2889215, by rfl⟩ : syracuseStep 3852287 = 5778431) B5778431
theorem B2566847 : Blo 1711056 2566847 := bstep (se 1 (by rfl) ⟨1925135, by rfl⟩ : syracuseStep 2566847 = 3850271) B3850271
theorem B2566895 : Blo 1711056 2566895 := bstep (se 1 (by rfl) ⟨1925171, by rfl⟩ : syracuseStep 2566895 = 3850343) B3850343
theorem B3853385 : Blo 1711056 3853385 := bstep (se 2 (by rfl) ⟨1445019, by rfl⟩ : syracuseStep 3853385 = 2890039) B2890039
theorem B3853439 : Blo 1711056 3853439 := bstep (se 1 (by rfl) ⟨2890079, by rfl⟩ : syracuseStep 3853439 = 5780159) B5780159
theorem B2567399 : Blo 1711056 2567399 := bstep (se 1 (by rfl) ⟨1925549, by rfl⟩ : syracuseStep 2567399 = 3851099) B3851099
theorem B2567735 : Blo 1711056 2567735 := bstep (se 1 (by rfl) ⟨1925801, by rfl⟩ : syracuseStep 2567735 = 3851603) B3851603
theorem B18509401 : Blo 1711056 18509401 := bstep (se 2 (by rfl) ⟨6941025, by rfl⟩ : syracuseStep 18509401 = 13882051) B13882051
theorem B70317791 : Blo 1711056 70317791 := bstep (se 1 (by rfl) ⟨52738343, by rfl⟩ : syracuseStep 70317791 = 105476687) B105476687
theorem B4331515 : Blo 1711056 4331515 := bstep (se 1 (by rfl) ⟨3248636, by rfl⟩ : syracuseStep 4331515 = 6497273) B6497273
theorem B1711343 : Blo 1711056 1711343 := bstep (se 1 (by rfl) ⟨1283507, by rfl⟩ : syracuseStep 1711343 = 2567015) B2567015
theorem B1711615 : Blo 1711056 1711615 := bstep (se 1 (by rfl) ⟨1283711, by rfl⟩ : syracuseStep 1711615 = 2567423) B2567423
theorem B71204791 : Blo 1711056 71204791 := bstep (se 1 (by rfl) ⟨53403593, by rfl⟩ : syracuseStep 71204791 = 106807187) B106807187
theorem B94939721 : Blo 1711056 94939721 := bstep (se 2 (by rfl) ⟨35602395, by rfl⟩ : syracuseStep 94939721 = 71204791) B71204791
theorem B2566889 : Blo 1711056 2566889 := bstep (se 2 (by rfl) ⟨962583, by rfl⟩ : syracuseStep 2566889 = 1925167) B1925167
theorem B8662463 : Blo 1711056 8662463 := bstep (se 1 (by rfl) ⟨6496847, by rfl⟩ : syracuseStep 8662463 = 12993695) B12993695
theorem B46878527 : Blo 1711056 46878527 := bstep (se 1 (by rfl) ⟨35158895, by rfl⟩ : syracuseStep 46878527 = 70317791) B70317791
theorem B2568191 : Blo 1711056 2568191 := bstep (se 1 (by rfl) ⟨1926143, by rfl⟩ : syracuseStep 2568191 = 3852287) B3852287
theorem B2568923 : Blo 1711056 2568923 := bstep (se 1 (by rfl) ⟨1926692, by rfl⟩ : syracuseStep 2568923 = 3853385) B3853385
theorem B2568959 : Blo 1711056 2568959 := bstep (se 1 (by rfl) ⟨1926719, by rfl⟩ : syracuseStep 2568959 = 3853439) B3853439
theorem B24679201 : Blo 1711056 24679201 := bstep (se 2 (by rfl) ⟨9254700, by rfl⟩ : syracuseStep 24679201 = 18509401) B18509401
theorem B2889391 : Blo 1711056 2889391 := bstep (se 1 (by rfl) ⟨2167043, by rfl⟩ : syracuseStep 2889391 = 4334087) B4334087
theorem B12343063 : Blo 1711056 12343063 := bstep (se 1 (by rfl) ⟨9257297, by rfl⟩ : syracuseStep 12343063 = 18514595) B18514595
theorem B12998555 : Blo 1711056 12998555 := bstep (se 1 (by rfl) ⟨9748916, by rfl⟩ : syracuseStep 12998555 = 19497833) B19497833
theorem B1711231 : Blo 1711056 1711231 := bstep (se 1 (by rfl) ⟨1283423, by rfl⟩ : syracuseStep 1711231 = 2566847) B2566847
theorem B1711263 : Blo 1711056 1711263 := bstep (se 1 (by rfl) ⟨1283447, by rfl⟩ : syracuseStep 1711263 = 2566895) B2566895
theorem B1711599 : Blo 1711056 1711599 := bstep (se 1 (by rfl) ⟨1283699, by rfl⟩ : syracuseStep 1711599 = 2567399) B2567399
theorem B1711823 : Blo 1711056 1711823 := bstep (se 1 (by rfl) ⟨1283867, by rfl⟩ : syracuseStep 1711823 = 2567735) B2567735
theorem B5775353 : Blo 1711056 5775353 := bstep (se 2 (by rfl) ⟨2165757, by rfl⟩ : syracuseStep 5775353 = 4331515) B4331515
theorem B1712615 : Blo 1711056 1712615 := bstep (se 1 (by rfl) ⟨1284461, by rfl⟩ : syracuseStep 1712615 = 2568923) B2568923
theorem B1712639 : Blo 1711056 1712639 := bstep (se 1 (by rfl) ⟨1284479, by rfl⟩ : syracuseStep 1712639 = 2568959) B2568959
theorem B63293147 : Blo 1711056 63293147 := bstep (se 1 (by rfl) ⟨47469860, by rfl⟩ : syracuseStep 63293147 = 94939721) B94939721
theorem B3852521 : Blo 1711056 3852521 := bstep (se 2 (by rfl) ⟨1444695, by rfl⟩ : syracuseStep 3852521 = 2889391) B2889391
theorem B32905601 : Blo 1711056 32905601 := bstep (se 2 (by rfl) ⟨12339600, by rfl⟩ : syracuseStep 32905601 = 24679201) B24679201
theorem B8665703 : Blo 1711056 8665703 := bstep (se 1 (by rfl) ⟨6499277, by rfl⟩ : syracuseStep 8665703 = 12998555) B12998555
theorem B1711259 : Blo 1711056 1711259 := bstep (se 1 (by rfl) ⟨1283444, by rfl⟩ : syracuseStep 1711259 = 2566889) B2566889
theorem B5774975 : Blo 1711056 5774975 := bstep (se 1 (by rfl) ⟨4331231, by rfl⟩ : syracuseStep 5774975 = 8662463) B8662463
theorem B16457417 : Blo 1711056 16457417 := bstep (se 2 (by rfl) ⟨6171531, by rfl⟩ : syracuseStep 16457417 = 12343063) B12343063
theorem B31252351 : Blo 1711056 31252351 := bstep (se 1 (by rfl) ⟨23439263, by rfl⟩ : syracuseStep 31252351 = 46878527) B46878527
theorem B3850235 : Blo 1711056 3850235 := bstep (se 1 (by rfl) ⟨2887676, by rfl⟩ : syracuseStep 3850235 = 5775353) B5775353
theorem B1712127 : Blo 1711056 1712127 := bstep (se 1 (by rfl) ⟨1284095, by rfl⟩ : syracuseStep 1712127 = 2568191) B2568191
theorem B5777135 : Blo 1711056 5777135 := bstep (se 1 (by rfl) ⟨4332851, by rfl⟩ : syracuseStep 5777135 = 8665703) B8665703
theorem B10971611 : Blo 1711056 10971611 := bstep (se 1 (by rfl) ⟨8228708, by rfl⟩ : syracuseStep 10971611 = 16457417) B16457417
theorem B2566823 : Blo 1711056 2566823 := bstep (se 1 (by rfl) ⟨1925117, by rfl⟩ : syracuseStep 2566823 = 3850235) B3850235
theorem B2568347 : Blo 1711056 2568347 := bstep (se 1 (by rfl) ⟨1926260, by rfl⟩ : syracuseStep 2568347 = 3852521) B3852521
theorem B41669801 : Blo 1711056 41669801 := bstep (se 2 (by rfl) ⟨15626175, by rfl⟩ : syracuseStep 41669801 = 31252351) B31252351
theorem B42195431 : Blo 1711056 42195431 := bstep (se 1 (by rfl) ⟨31646573, by rfl⟩ : syracuseStep 42195431 = 63293147) B63293147
theorem B21937067 : Blo 1711056 21937067 := bstep (se 1 (by rfl) ⟨16452800, by rfl⟩ : syracuseStep 21937067 = 32905601) B32905601
theorem B3849983 : Blo 1711056 3849983 := bstep (se 1 (by rfl) ⟨2887487, by rfl⟩ : syracuseStep 3849983 = 5774975) B5774975
theorem B1712231 : Blo 1711056 1712231 := bstep (se 1 (by rfl) ⟨1284173, by rfl⟩ : syracuseStep 1712231 = 2568347) B2568347
theorem B27779867 : Blo 1711056 27779867 := bstep (se 1 (by rfl) ⟨20834900, by rfl⟩ : syracuseStep 27779867 = 41669801) B41669801
theorem B3851423 : Blo 1711056 3851423 := bstep (se 1 (by rfl) ⟨2888567, by rfl⟩ : syracuseStep 3851423 = 5777135) B5777135
theorem B14624711 : Blo 1711056 14624711 := bstep (se 1 (by rfl) ⟨10968533, by rfl⟩ : syracuseStep 14624711 = 21937067) B21937067
theorem B2566655 : Blo 1711056 2566655 := bstep (se 1 (by rfl) ⟨1924991, by rfl⟩ : syracuseStep 2566655 = 3849983) B3849983
theorem B112521149 : Blo 1711056 112521149 := bstep (se 3 (by rfl) ⟨21097715, by rfl⟩ : syracuseStep 112521149 = 42195431) B42195431
theorem B7314407 : Blo 1711056 7314407 := bstep (se 1 (by rfl) ⟨5485805, by rfl⟩ : syracuseStep 7314407 = 10971611) B10971611
theorem B1711215 : Blo 1711056 1711215 := bstep (se 1 (by rfl) ⟨1283411, by rfl⟩ : syracuseStep 1711215 = 2566823) B2566823
theorem B9749807 : Blo 1711056 9749807 := bstep (se 1 (by rfl) ⟨7312355, by rfl⟩ : syracuseStep 9749807 = 14624711) B14624711
theorem B4876271 : Blo 1711056 4876271 := bstep (se 1 (by rfl) ⟨3657203, by rfl⟩ : syracuseStep 4876271 = 7314407) B7314407
theorem B2567615 : Blo 1711056 2567615 := bstep (se 1 (by rfl) ⟨1925711, by rfl⟩ : syracuseStep 2567615 = 3851423) B3851423
theorem B18519911 : Blo 1711056 18519911 := bstep (se 1 (by rfl) ⟨13889933, by rfl⟩ : syracuseStep 18519911 = 27779867) B27779867
theorem B1711103 : Blo 1711056 1711103 := bstep (se 1 (by rfl) ⟨1283327, by rfl⟩ : syracuseStep 1711103 = 2566655) B2566655
theorem B75014099 : Blo 1711056 75014099 := bstep (se 1 (by rfl) ⟨56260574, by rfl⟩ : syracuseStep 75014099 = 112521149) B112521149
theorem B12346607 : Blo 1711056 12346607 := bstep (se 1 (by rfl) ⟨9259955, by rfl⟩ : syracuseStep 12346607 = 18519911) B18519911
theorem B6499871 : Blo 1711056 6499871 := bstep (se 1 (by rfl) ⟨4874903, by rfl⟩ : syracuseStep 6499871 = 9749807) B9749807
theorem B50009399 : Blo 1711056 50009399 := bstep (se 1 (by rfl) ⟨37507049, by rfl⟩ : syracuseStep 50009399 = 75014099) B75014099
theorem B3250847 : Blo 1711056 3250847 := bstep (se 1 (by rfl) ⟨2438135, by rfl⟩ : syracuseStep 3250847 = 4876271) B4876271
theorem B1711743 : Blo 1711056 1711743 := bstep (se 1 (by rfl) ⟨1283807, by rfl⟩ : syracuseStep 1711743 = 2567615) B2567615
theorem B2167231 : Blo 1711056 2167231 := bstep (se 1 (by rfl) ⟨1625423, by rfl⟩ : syracuseStep 2167231 = 3250847) B3250847
theorem B8231071 : Blo 1711056 8231071 := bstep (se 1 (by rfl) ⟨6173303, by rfl⟩ : syracuseStep 8231071 = 12346607) B12346607
theorem B33339599 : Blo 1711056 33339599 := bstep (se 1 (by rfl) ⟨25004699, by rfl⟩ : syracuseStep 33339599 = 50009399) B50009399
theorem B4333247 : Blo 1711056 4333247 := bstep (se 1 (by rfl) ⟨3249935, by rfl⟩ : syracuseStep 4333247 = 6499871) B6499871
theorem B22226399 : Blo 1711056 22226399 := bstep (se 1 (by rfl) ⟨16669799, by rfl⟩ : syracuseStep 22226399 = 33339599) B33339599
theorem B2888831 : Blo 1711056 2888831 := bstep (se 1 (by rfl) ⟨2166623, by rfl⟩ : syracuseStep 2888831 = 4333247) B4333247
theorem B10974761 : Blo 1711056 10974761 := bstep (se 2 (by rfl) ⟨4115535, by rfl⟩ : syracuseStep 10974761 = 8231071) B8231071
theorem B2889641 : Blo 1711056 2889641 := bstep (se 2 (by rfl) ⟨1083615, by rfl⟩ : syracuseStep 2889641 = 2167231) B2167231
theorem B1925887 : Blo 1711056 1925887 := bstep (se 1 (by rfl) ⟨1444415, by rfl⟩ : syracuseStep 1925887 = 2888831) B2888831
theorem B7316507 : Blo 1711056 7316507 := bstep (se 1 (by rfl) ⟨5487380, by rfl⟩ : syracuseStep 7316507 = 10974761) B10974761
theorem B1926427 : Blo 1711056 1926427 := bstep (se 1 (by rfl) ⟨1444820, by rfl⟩ : syracuseStep 1926427 = 2889641) B2889641
theorem B14817599 : Blo 1711056 14817599 := bstep (se 1 (by rfl) ⟨11113199, by rfl⟩ : syracuseStep 14817599 = 22226399) B22226399
theorem B4877671 : Blo 1711056 4877671 := bstep (se 1 (by rfl) ⟨3658253, by rfl⟩ : syracuseStep 4877671 = 7316507) B7316507
theorem B2567849 : Blo 1711056 2567849 := bstep (se 2 (by rfl) ⟨962943, by rfl⟩ : syracuseStep 2567849 = 1925887) B1925887
theorem B2568569 : Blo 1711056 2568569 := bstep (se 2 (by rfl) ⟨963213, by rfl⟩ : syracuseStep 2568569 = 1926427) B1926427
theorem B9878399 : Blo 1711056 9878399 := bstep (se 1 (by rfl) ⟨7408799, by rfl⟩ : syracuseStep 9878399 = 14817599) B14817599
theorem B1712379 : Blo 1711056 1712379 := bstep (se 1 (by rfl) ⟨1284284, by rfl⟩ : syracuseStep 1712379 = 2568569) B2568569
theorem B6503561 : Blo 1711056 6503561 := bstep (se 2 (by rfl) ⟨2438835, by rfl⟩ : syracuseStep 6503561 = 4877671) B4877671
theorem B6585599 : Blo 1711056 6585599 := bstep (se 1 (by rfl) ⟨4939199, by rfl⟩ : syracuseStep 6585599 = 9878399) B9878399
theorem B1711899 : Blo 1711056 1711899 := bstep (se 1 (by rfl) ⟨1283924, by rfl⟩ : syracuseStep 1711899 = 2567849) B2567849
theorem B4335707 : Blo 1711056 4335707 := bstep (se 1 (by rfl) ⟨3251780, by rfl⟩ : syracuseStep 4335707 = 6503561) B6503561
theorem B4390399 : Blo 1711056 4390399 := bstep (se 1 (by rfl) ⟨3292799, by rfl⟩ : syracuseStep 4390399 = 6585599) B6585599
theorem B5853865 : Blo 1711056 5853865 := bstep (se 2 (by rfl) ⟨2195199, by rfl⟩ : syracuseStep 5853865 = 4390399) B4390399
theorem B2890471 : Blo 1711056 2890471 := bstep (se 1 (by rfl) ⟨2167853, by rfl⟩ : syracuseStep 2890471 = 4335707) B4335707
theorem B3853961 : Blo 1711056 3853961 := bstep (se 2 (by rfl) ⟨1445235, by rfl⟩ : syracuseStep 3853961 = 2890471) B2890471
theorem B7805153 : Blo 1711056 7805153 := bstep (se 2 (by rfl) ⟨2926932, by rfl⟩ : syracuseStep 7805153 = 5853865) B5853865
theorem B5203435 : Blo 1711056 5203435 := bstep (se 1 (by rfl) ⟨3902576, by rfl⟩ : syracuseStep 5203435 = 7805153) B7805153
theorem B2569307 : Blo 1711056 2569307 := bstep (se 1 (by rfl) ⟨1926980, by rfl⟩ : syracuseStep 2569307 = 3853961) B3853961
theorem B1712871 : Blo 1711056 1712871 := bstep (se 1 (by rfl) ⟨1284653, by rfl⟩ : syracuseStep 1712871 = 2569307) B2569307
theorem B6937913 : Blo 1711056 6937913 := bstep (se 2 (by rfl) ⟨2601717, by rfl⟩ : syracuseStep 6937913 = 5203435) B5203435
theorem B4625275 : Blo 1711056 4625275 := bstep (se 1 (by rfl) ⟨3468956, by rfl⟩ : syracuseStep 4625275 = 6937913) B6937913
theorem B6167033 : Blo 1711056 6167033 := bstep (se 2 (by rfl) ⟨2312637, by rfl⟩ : syracuseStep 6167033 = 4625275) B4625275
theorem B4111355 : Blo 1711056 4111355 := bstep (se 1 (by rfl) ⟨3083516, by rfl⟩ : syracuseStep 4111355 = 6167033) B6167033
theorem B10963613 : Blo 1711056 10963613 := bstep (se 3 (by rfl) ⟨2055677, by rfl⟩ : syracuseStep 10963613 = 4111355) B4111355
theorem B7309075 : Blo 1711056 7309075 := bstep (se 1 (by rfl) ⟨5481806, by rfl⟩ : syracuseStep 7309075 = 10963613) B10963613
theorem B9745433 : Blo 1711056 9745433 := bstep (se 2 (by rfl) ⟨3654537, by rfl⟩ : syracuseStep 9745433 = 7309075) B7309075
theorem B6496955 : Blo 1711056 6496955 := bstep (se 1 (by rfl) ⟨4872716, by rfl⟩ : syracuseStep 6496955 = 9745433) B9745433
theorem B4331303 : Blo 1711056 4331303 := bstep (se 1 (by rfl) ⟨3248477, by rfl⟩ : syracuseStep 4331303 = 6496955) B6496955
theorem B2887535 : Blo 1711056 2887535 := bstep (se 1 (by rfl) ⟨2165651, by rfl⟩ : syracuseStep 2887535 = 4331303) B4331303
theorem B1925023 : Blo 1711056 1925023 := bstep (se 1 (by rfl) ⟨1443767, by rfl⟩ : syracuseStep 1925023 = 2887535) B2887535
theorem B2566697 : Blo 1711056 2566697 := bstep (se 2 (by rfl) ⟨962511, by rfl⟩ : syracuseStep 2566697 = 1925023) B1925023
theorem B1711131 : Blo 1711056 1711131 := bstep (se 1 (by rfl) ⟨1283348, by rfl⟩ : syracuseStep 1711131 = 2566697) B2566697

theorem C0 (j : ℕ) (h1 : 427764 ≤ j) (h2 : j ≤ 428263) : Blo 1711056 (4 * j + 3) := by
  interval_cases j
  · exact B1711059
  · exact B1711063
  · exact B1711067
  · exact B1711071
  · exact B1711075
  · exact B1711079
  · exact B1711083
  · exact B1711087
  · exact B1711091
  · exact B1711095
  · exact B1711099
  · exact B1711103
  · exact B1711107
  · exact B1711111
  · exact B1711115
  · exact B1711119
  · exact B1711123
  · exact B1711127
  · exact B1711131
  · exact B1711135
  · exact B1711139
  · exact B1711143
  · exact B1711147
  · exact B1711151
  · exact B1711155
  · exact B1711159
  · exact B1711163
  · exact B1711167
  · exact B1711171
  · exact B1711175
  · exact B1711179
  · exact B1711183
  · exact B1711187
  · exact B1711191
  · exact B1711195
  · exact B1711199
  · exact B1711203
  · exact B1711207
  · exact B1711211
  · exact B1711215
  · exact B1711219
  · exact B1711223
  · exact B1711227
  · exact B1711231
  · exact B1711235
  · exact B1711239
  · exact B1711243
  · exact B1711247
  · exact B1711251
  · exact B1711255
  · exact B1711259
  · exact B1711263
  · exact B1711267
  · exact B1711271
  · exact B1711275
  · exact B1711279
  · exact B1711283
  · exact B1711287
  · exact B1711291
  · exact B1711295
  · exact B1711299
  · exact B1711303
  · exact B1711307
  · exact B1711311
  · exact B1711315
  · exact B1711319
  · exact B1711323
  · exact B1711327
  · exact B1711331
  · exact B1711335
  · exact B1711339
  · exact B1711343
  · exact B1711347
  · exact B1711351
  · exact B1711355
  · exact B1711359
  · exact B1711363
  · exact B1711367
  · exact B1711371
  · exact B1711375
  · exact B1711379
  · exact B1711383
  · exact B1711387
  · exact B1711391
  · exact B1711395
  · exact B1711399
  · exact B1711403
  · exact B1711407
  · exact B1711411
  · exact B1711415
  · exact B1711419
  · exact B1711423
  · exact B1711427
  · exact B1711431
  · exact B1711435
  · exact B1711439
  · exact B1711443
  · exact B1711447
  · exact B1711451
  · exact B1711455
  · exact B1711459
  · exact B1711463
  · exact B1711467
  · exact B1711471
  · exact B1711475
  · exact B1711479
  · exact B1711483
  · exact B1711487
  · exact B1711491
  · exact B1711495
  · exact B1711499
  · exact B1711503
  · exact B1711507
  · exact B1711511
  · exact B1711515
  · exact B1711519
  · exact B1711523
  · exact B1711527
  · exact B1711531
  · exact B1711535
  · exact B1711539
  · exact B1711543
  · exact B1711547
  · exact B1711551
  · exact B1711555
  · exact B1711559
  · exact B1711563
  · exact B1711567
  · exact B1711571
  · exact B1711575
  · exact B1711579
  · exact B1711583
  · exact B1711587
  · exact B1711591
  · exact B1711595
  · exact B1711599
  · exact B1711603
  · exact B1711607
  · exact B1711611
  · exact B1711615
  · exact B1711619
  · exact B1711623
  · exact B1711627
  · exact B1711631
  · exact B1711635
  · exact B1711639
  · exact B1711643
  · exact B1711647
  · exact B1711651
  · exact B1711655
  · exact B1711659
  · exact B1711663
  · exact B1711667
  · exact B1711671
  · exact B1711675
  · exact B1711679
  · exact B1711683
  · exact B1711687
  · exact B1711691
  · exact B1711695
  · exact B1711699
  · exact B1711703
  · exact B1711707
  · exact B1711711
  · exact B1711715
  · exact B1711719
  · exact B1711723
  · exact B1711727
  · exact B1711731
  · exact B1711735
  · exact B1711739
  · exact B1711743
  · exact B1711747
  · exact B1711751
  · exact B1711755
  · exact B1711759
  · exact B1711763
  · exact B1711767
  · exact B1711771
  · exact B1711775
  · exact B1711779
  · exact B1711783
  · exact B1711787
  · exact B1711791
  · exact B1711795
  · exact B1711799
  · exact B1711803
  · exact B1711807
  · exact B1711811
  · exact B1711815
  · exact B1711819
  · exact B1711823
  · exact B1711827
  · exact B1711831
  · exact B1711835
  · exact B1711839
  · exact B1711843
  · exact B1711847
  · exact B1711851
  · exact B1711855
  · exact B1711859
  · exact B1711863
  · exact B1711867
  · exact B1711871
  · exact B1711875
  · exact B1711879
  · exact B1711883
  · exact B1711887
  · exact B1711891
  · exact B1711895
  · exact B1711899
  · exact B1711903
  · exact B1711907
  · exact B1711911
  · exact B1711915
  · exact B1711919
  · exact B1711923
  · exact B1711927
  · exact B1711931
  · exact B1711935
  · exact B1711939
  · exact B1711943
  · exact B1711947
  · exact B1711951
  · exact B1711955
  · exact B1711959
  · exact B1711963
  · exact B1711967
  · exact B1711971
  · exact B1711975
  · exact B1711979
  · exact B1711983
  · exact B1711987
  · exact B1711991
  · exact B1711995
  · exact B1711999
  · exact B1712003
  · exact B1712007
  · exact B1712011
  · exact B1712015
  · exact B1712019
  · exact B1712023
  · exact B1712027
  · exact B1712031
  · exact B1712035
  · exact B1712039
  · exact B1712043
  · exact B1712047
  · exact B1712051
  · exact B1712055
  · exact B1712059
  · exact B1712063
  · exact B1712067
  · exact B1712071
  · exact B1712075
  · exact B1712079
  · exact B1712083
  · exact B1712087
  · exact B1712091
  · exact B1712095
  · exact B1712099
  · exact B1712103
  · exact B1712107
  · exact B1712111
  · exact B1712115
  · exact B1712119
  · exact B1712123
  · exact B1712127
  · exact B1712131
  · exact B1712135
  · exact B1712139
  · exact B1712143
  · exact B1712147
  · exact B1712151
  · exact B1712155
  · exact B1712159
  · exact B1712163
  · exact B1712167
  · exact B1712171
  · exact B1712175
  · exact B1712179
  · exact B1712183
  · exact B1712187
  · exact B1712191
  · exact B1712195
  · exact B1712199
  · exact B1712203
  · exact B1712207
  · exact B1712211
  · exact B1712215
  · exact B1712219
  · exact B1712223
  · exact B1712227
  · exact B1712231
  · exact B1712235
  · exact B1712239
  · exact B1712243
  · exact B1712247
  · exact B1712251
  · exact B1712255
  · exact B1712259
  · exact B1712263
  · exact B1712267
  · exact B1712271
  · exact B1712275
  · exact B1712279
  · exact B1712283
  · exact B1712287
  · exact B1712291
  · exact B1712295
  · exact B1712299
  · exact B1712303
  · exact B1712307
  · exact B1712311
  · exact B1712315
  · exact B1712319
  · exact B1712323
  · exact B1712327
  · exact B1712331
  · exact B1712335
  · exact B1712339
  · exact B1712343
  · exact B1712347
  · exact B1712351
  · exact B1712355
  · exact B1712359
  · exact B1712363
  · exact B1712367
  · exact B1712371
  · exact B1712375
  · exact B1712379
  · exact B1712383
  · exact B1712387
  · exact B1712391
  · exact B1712395
  · exact B1712399
  · exact B1712403
  · exact B1712407
  · exact B1712411
  · exact B1712415
  · exact B1712419
  · exact B1712423
  · exact B1712427
  · exact B1712431
  · exact B1712435
  · exact B1712439
  · exact B1712443
  · exact B1712447
  · exact B1712451
  · exact B1712455
  · exact B1712459
  · exact B1712463
  · exact B1712467
  · exact B1712471
  · exact B1712475
  · exact B1712479
  · exact B1712483
  · exact B1712487
  · exact B1712491
  · exact B1712495
  · exact B1712499
  · exact B1712503
  · exact B1712507
  · exact B1712511
  · exact B1712515
  · exact B1712519
  · exact B1712523
  · exact B1712527
  · exact B1712531
  · exact B1712535
  · exact B1712539
  · exact B1712543
  · exact B1712547
  · exact B1712551
  · exact B1712555
  · exact B1712559
  · exact B1712563
  · exact B1712567
  · exact B1712571
  · exact B1712575
  · exact B1712579
  · exact B1712583
  · exact B1712587
  · exact B1712591
  · exact B1712595
  · exact B1712599
  · exact B1712603
  · exact B1712607
  · exact B1712611
  · exact B1712615
  · exact B1712619
  · exact B1712623
  · exact B1712627
  · exact B1712631
  · exact B1712635
  · exact B1712639
  · exact B1712643
  · exact B1712647
  · exact B1712651
  · exact B1712655
  · exact B1712659
  · exact B1712663
  · exact B1712667
  · exact B1712671
  · exact B1712675
  · exact B1712679
  · exact B1712683
  · exact B1712687
  · exact B1712691
  · exact B1712695
  · exact B1712699
  · exact B1712703
  · exact B1712707
  · exact B1712711
  · exact B1712715
  · exact B1712719
  · exact B1712723
  · exact B1712727
  · exact B1712731
  · exact B1712735
  · exact B1712739
  · exact B1712743
  · exact B1712747
  · exact B1712751
  · exact B1712755
  · exact B1712759
  · exact B1712763
  · exact B1712767
  · exact B1712771
  · exact B1712775
  · exact B1712779
  · exact B1712783
  · exact B1712787
  · exact B1712791
  · exact B1712795
  · exact B1712799
  · exact B1712803
  · exact B1712807
  · exact B1712811
  · exact B1712815
  · exact B1712819
  · exact B1712823
  · exact B1712827
  · exact B1712831
  · exact B1712835
  · exact B1712839
  · exact B1712843
  · exact B1712847
  · exact B1712851
  · exact B1712855
  · exact B1712859
  · exact B1712863
  · exact B1712867
  · exact B1712871
  · exact B1712875
  · exact B1712879
  · exact B1712883
  · exact B1712887
  · exact B1712891
  · exact B1712895
  · exact B1712899
  · exact B1712903
  · exact B1712907
  · exact B1712911
  · exact B1712915
  · exact B1712919
  · exact B1712923
  · exact B1712927
  · exact B1712931
  · exact B1712935
  · exact B1712939
  · exact B1712943
  · exact B1712947
  · exact B1712951
  · exact B1712955
  · exact B1712959
  · exact B1712963
  · exact B1712967
  · exact B1712971
  · exact B1712975
  · exact B1712979
  · exact B1712983
  · exact B1712987
  · exact B1712991
  · exact B1712995
  · exact B1712999
  · exact B1713003
  · exact B1713007
  · exact B1713011
  · exact B1713015
  · exact B1713019
  · exact B1713023
  · exact B1713027
  · exact B1713031
  · exact B1713035
  · exact B1713039
  · exact B1713043
  · exact B1713047
  · exact B1713051
  · exact B1713055

theorem solution (m : ℕ) (hlo : 1711056 ≤ m) (hhi : m ≤ 1713056) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 427764 ≤ j := by omega
    have hj2 : j ≤ 428263 := by omega
    have hb : Blo 1711056 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
