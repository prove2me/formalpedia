-- Prove2me | solution 1 for syracuse_descends_range_1048611_1052611
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:25.960489+00:00
-- url     : https://prove2.me/submissions/42c681d2-47a6-48e8-9aca-10a84c804772

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


theorem B1179697 : Blo 1048611 1179697 := bbase (se 2 (by rfl) ⟨442386, by rfl⟩ : syracuseStep 1179697 = 884773) (by norm_num)
theorem B1572917 : Blo 1048611 1572917 := bbase (se 5 (by rfl) ⟨73730, by rfl⟩ : syracuseStep 1572917 = 147461) (by norm_num)
theorem B1572941 : Blo 1048611 1572941 := bbase (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) (by norm_num)
theorem B1179733 : Blo 1048611 1179733 := bbase (se 8 (by rfl) ⟨6912, by rfl⟩ : syracuseStep 1179733 = 13825) (by norm_num)
theorem B2654309 : Blo 1048611 2654309 := bbase (se 4 (by rfl) ⟨248841, by rfl⟩ : syracuseStep 2654309 = 497683) (by norm_num)
theorem B1769573 : Blo 1048611 1769573 := bbase (se 4 (by rfl) ⟨165897, by rfl⟩ : syracuseStep 1769573 = 331795) (by norm_num)
theorem B1572965 : Blo 1048611 1572965 := bbase (se 4 (by rfl) ⟨147465, by rfl⟩ : syracuseStep 1572965 = 294931) (by norm_num)
theorem B1441901 : Blo 1048611 1441901 := bbase (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) (by norm_num)
theorem B1179769 : Blo 1048611 1179769 := bbase (se 2 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 1179769 = 884827) (by norm_num)
theorem B2359421 : Blo 1048611 2359421 := bbase (se 3 (by rfl) ⟨442391, by rfl⟩ : syracuseStep 2359421 = 884783) (by norm_num)
theorem B1572989 : Blo 1048611 1572989 := bbase (se 3 (by rfl) ⟨294935, by rfl⟩ : syracuseStep 1572989 = 589871) (by norm_num)
theorem B1573013 : Blo 1048611 1573013 := bbase (se 6 (by rfl) ⟨36867, by rfl⟩ : syracuseStep 1573013 = 73735) (by norm_num)
theorem B1179805 : Blo 1048611 1179805 := bbase (se 3 (by rfl) ⟨221213, by rfl⟩ : syracuseStep 1179805 = 442427) (by norm_num)
theorem B1573037 : Blo 1048611 1573037 := bbase (se 3 (by rfl) ⟨294944, by rfl⟩ : syracuseStep 1573037 = 589889) (by norm_num)
theorem B1179841 : Blo 1048611 1179841 := bbase (se 2 (by rfl) ⟨442440, by rfl⟩ : syracuseStep 1179841 = 884881) (by norm_num)
theorem B2359493 : Blo 1048611 2359493 := bbase (se 4 (by rfl) ⟨221202, by rfl⟩ : syracuseStep 2359493 = 442405) (by norm_num)
theorem B1573061 : Blo 1048611 1573061 := bbase (se 4 (by rfl) ⟨147474, by rfl⟩ : syracuseStep 1573061 = 294949) (by norm_num)
theorem B1573085 : Blo 1048611 1573085 := bbase (se 3 (by rfl) ⟨294953, by rfl⟩ : syracuseStep 1573085 = 589907) (by norm_num)
theorem B1769701 : Blo 1048611 1769701 := bbase (se 4 (by rfl) ⟨165909, by rfl⟩ : syracuseStep 1769701 = 331819) (by norm_num)
theorem B1179877 : Blo 1048611 1179877 := bbase (se 4 (by rfl) ⟨110613, by rfl⟩ : syracuseStep 1179877 = 221227) (by norm_num)
theorem B1573109 : Blo 1048611 1573109 := bbase (se 5 (by rfl) ⟨73739, by rfl⟩ : syracuseStep 1573109 = 147479) (by norm_num)
theorem B1179913 : Blo 1048611 1179913 := bbase (se 2 (by rfl) ⟨442467, by rfl⟩ : syracuseStep 1179913 = 884935) (by norm_num)
theorem B2359565 : Blo 1048611 2359565 := bbase (se 3 (by rfl) ⟨442418, by rfl⟩ : syracuseStep 2359565 = 884837) (by norm_num)
theorem B1573133 : Blo 1048611 1573133 := bbase (se 3 (by rfl) ⟨294962, by rfl⟩ : syracuseStep 1573133 = 589925) (by norm_num)
theorem B1573157 : Blo 1048611 1573157 := bbase (se 4 (by rfl) ⟨147483, by rfl⟩ : syracuseStep 1573157 = 294967) (by norm_num)
theorem B1179949 : Blo 1048611 1179949 := bbase (se 3 (by rfl) ⟨221240, by rfl⟩ : syracuseStep 1179949 = 442481) (by norm_num)
theorem B1769789 : Blo 1048611 1769789 := bbase (se 3 (by rfl) ⟨331835, by rfl⟩ : syracuseStep 1769789 = 663671) (by norm_num)
theorem B1573181 : Blo 1048611 1573181 := bbase (se 3 (by rfl) ⟨294971, by rfl⟩ : syracuseStep 1573181 = 589943) (by norm_num)
theorem B1179985 : Blo 1048611 1179985 := bbase (se 2 (by rfl) ⟨442494, by rfl⟩ : syracuseStep 1179985 = 884989) (by norm_num)
theorem B2359637 : Blo 1048611 2359637 := bbase (se 10 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 2359637 = 6913) (by norm_num)
theorem B1573205 : Blo 1048611 1573205 := bbase (se 10 (by rfl) ⟨2304, by rfl⟩ : syracuseStep 1573205 = 4609) (by norm_num)
theorem B1573229 : Blo 1048611 1573229 := bbase (se 3 (by rfl) ⟨294980, by rfl⟩ : syracuseStep 1573229 = 589961) (by norm_num)
theorem B1180021 : Blo 1048611 1180021 := bbase (se 5 (by rfl) ⟨55313, by rfl⟩ : syracuseStep 1180021 = 110627) (by norm_num)
theorem B1212797 : Blo 1048611 1212797 := bbase (se 3 (by rfl) ⟨227399, by rfl⟩ : syracuseStep 1212797 = 454799) (by norm_num)
theorem B1573253 : Blo 1048611 1573253 := bbase (se 4 (by rfl) ⟨147492, by rfl⟩ : syracuseStep 1573253 = 294985) (by norm_num)
theorem B1180057 : Blo 1048611 1180057 := bbase (se 2 (by rfl) ⟨442521, by rfl⟩ : syracuseStep 1180057 = 885043) (by norm_num)
theorem B2359709 : Blo 1048611 2359709 := bbase (se 3 (by rfl) ⟨442445, by rfl⟩ : syracuseStep 2359709 = 884891) (by norm_num)
theorem B1573277 : Blo 1048611 1573277 := bbase (se 3 (by rfl) ⟨294989, by rfl⟩ : syracuseStep 1573277 = 589979) (by norm_num)
theorem B1573301 : Blo 1048611 1573301 := bbase (se 5 (by rfl) ⟨73748, by rfl⟩ : syracuseStep 1573301 = 147497) (by norm_num)
theorem B2654653 : Blo 1048611 2654653 := bbase (se 3 (by rfl) ⟨497747, by rfl⟩ : syracuseStep 2654653 = 995495) (by norm_num)
theorem B1769917 : Blo 1048611 1769917 := bbase (se 3 (by rfl) ⟨331859, by rfl⟩ : syracuseStep 1769917 = 663719) (by norm_num)
theorem B1180093 : Blo 1048611 1180093 := bbase (se 3 (by rfl) ⟨221267, by rfl⟩ : syracuseStep 1180093 = 442535) (by norm_num)
theorem B1573325 : Blo 1048611 1573325 := bbase (se 3 (by rfl) ⟨294998, by rfl⟩ : syracuseStep 1573325 = 589997) (by norm_num)
theorem B1180129 : Blo 1048611 1180129 := bbase (se 2 (by rfl) ⟨442548, by rfl⟩ : syracuseStep 1180129 = 885097) (by norm_num)
theorem B5308901 : Blo 1048611 5308901 := bbase (se 4 (by rfl) ⟨497709, by rfl⟩ : syracuseStep 5308901 = 995419) (by norm_num)
theorem B3539429 : Blo 1048611 3539429 := bbase (se 4 (by rfl) ⟨331821, by rfl⟩ : syracuseStep 3539429 = 663643) (by norm_num)
theorem B2359781 : Blo 1048611 2359781 := bbase (se 4 (by rfl) ⟨221229, by rfl⟩ : syracuseStep 2359781 = 442459) (by norm_num)
theorem B1573349 : Blo 1048611 1573349 := bbase (se 4 (by rfl) ⟨147501, by rfl⟩ : syracuseStep 1573349 = 295003) (by norm_num)
theorem B1573373 : Blo 1048611 1573373 := bbase (se 3 (by rfl) ⟨295007, by rfl⟩ : syracuseStep 1573373 = 590015) (by norm_num)
theorem B1180165 : Blo 1048611 1180165 := bbase (se 4 (by rfl) ⟨110640, by rfl⟩ : syracuseStep 1180165 = 221281) (by norm_num)
theorem B1770005 : Blo 1048611 1770005 := bbase (se 6 (by rfl) ⟨41484, by rfl⟩ : syracuseStep 1770005 = 82969) (by norm_num)
theorem B1573397 : Blo 1048611 1573397 := bbase (se 6 (by rfl) ⟨36876, by rfl⟩ : syracuseStep 1573397 = 73753) (by norm_num)
theorem B1180201 : Blo 1048611 1180201 := bbase (se 2 (by rfl) ⟨442575, by rfl⟩ : syracuseStep 1180201 = 885151) (by norm_num)
theorem B2654765 : Blo 1048611 2654765 := bbase (se 3 (by rfl) ⟨497768, by rfl⟩ : syracuseStep 2654765 = 995537) (by norm_num)
theorem B2359853 : Blo 1048611 2359853 := bbase (se 3 (by rfl) ⟨442472, by rfl⟩ : syracuseStep 2359853 = 884945) (by norm_num)
theorem B1573421 : Blo 1048611 1573421 := bbase (se 3 (by rfl) ⟨295016, by rfl⟩ : syracuseStep 1573421 = 590033) (by norm_num)
theorem B1573445 : Blo 1048611 1573445 := bbase (se 4 (by rfl) ⟨147510, by rfl⟩ : syracuseStep 1573445 = 295021) (by norm_num)
theorem B1180237 : Blo 1048611 1180237 := bbase (se 3 (by rfl) ⟨221294, by rfl⟩ : syracuseStep 1180237 = 442589) (by norm_num)
theorem B1573469 : Blo 1048611 1573469 := bbase (se 3 (by rfl) ⟨295025, by rfl⟩ : syracuseStep 1573469 = 590051) (by norm_num)
theorem B1180273 : Blo 1048611 1180273 := bbase (se 2 (by rfl) ⟨442602, by rfl⟩ : syracuseStep 1180273 = 885205) (by norm_num)
theorem B2359925 : Blo 1048611 2359925 := bbase (se 5 (by rfl) ⟨110621, by rfl⟩ : syracuseStep 2359925 = 221243) (by norm_num)
theorem B1573493 : Blo 1048611 1573493 := bbase (se 5 (by rfl) ⟨73757, by rfl⟩ : syracuseStep 1573493 = 147515) (by norm_num)
theorem B1573517 : Blo 1048611 1573517 := bbase (se 3 (by rfl) ⟨295034, by rfl⟩ : syracuseStep 1573517 = 590069) (by norm_num)
theorem B1770133 : Blo 1048611 1770133 := bbase (se 6 (by rfl) ⟨41487, by rfl⟩ : syracuseStep 1770133 = 82975) (by norm_num)
theorem B1180309 : Blo 1048611 1180309 := bbase (se 6 (by rfl) ⟨27663, by rfl⟩ : syracuseStep 1180309 = 55327) (by norm_num)
theorem B1573541 : Blo 1048611 1573541 := bbase (se 4 (by rfl) ⟨147519, by rfl⟩ : syracuseStep 1573541 = 295039) (by norm_num)
theorem B1180345 : Blo 1048611 1180345 := bbase (se 2 (by rfl) ⟨442629, by rfl⟩ : syracuseStep 1180345 = 885259) (by norm_num)
theorem B2359997 : Blo 1048611 2359997 := bbase (se 3 (by rfl) ⟨442499, by rfl⟩ : syracuseStep 2359997 = 884999) (by norm_num)
theorem B1573565 : Blo 1048611 1573565 := bbase (se 3 (by rfl) ⟨295043, by rfl⟩ : syracuseStep 1573565 = 590087) (by norm_num)
theorem B1573589 : Blo 1048611 1573589 := bbase (se 7 (by rfl) ⟨18440, by rfl⟩ : syracuseStep 1573589 = 36881) (by norm_num)
theorem B1180381 : Blo 1048611 1180381 := bbase (se 3 (by rfl) ⟨221321, by rfl⟩ : syracuseStep 1180381 = 442643) (by norm_num)
theorem B2654957 : Blo 1048611 2654957 := bbase (se 3 (by rfl) ⟨497804, by rfl⟩ : syracuseStep 2654957 = 995609) (by norm_num)
theorem B1770221 : Blo 1048611 1770221 := bbase (se 3 (by rfl) ⟨331916, by rfl⟩ : syracuseStep 1770221 = 663833) (by norm_num)
theorem B1573613 : Blo 1048611 1573613 := bbase (se 3 (by rfl) ⟨295052, by rfl⟩ : syracuseStep 1573613 = 590105) (by norm_num)
theorem B1180417 : Blo 1048611 1180417 := bbase (se 2 (by rfl) ⟨442656, by rfl⟩ : syracuseStep 1180417 = 885313) (by norm_num)
theorem B2360069 : Blo 1048611 2360069 := bbase (se 4 (by rfl) ⟨221256, by rfl⟩ : syracuseStep 2360069 = 442513) (by norm_num)
theorem B1573637 : Blo 1048611 1573637 := bbase (se 4 (by rfl) ⟨147528, by rfl⟩ : syracuseStep 1573637 = 295057) (by norm_num)
theorem B1573661 : Blo 1048611 1573661 := bbase (se 3 (by rfl) ⟨295061, by rfl⟩ : syracuseStep 1573661 = 590123) (by norm_num)
theorem B1180453 : Blo 1048611 1180453 := bbase (se 4 (by rfl) ⟨110667, by rfl⟩ : syracuseStep 1180453 = 221335) (by norm_num)
theorem B1573685 : Blo 1048611 1573685 := bbase (se 5 (by rfl) ⟨73766, by rfl⟩ : syracuseStep 1573685 = 147533) (by norm_num)
theorem B1180489 : Blo 1048611 1180489 := bbase (se 2 (by rfl) ⟨442683, by rfl⟩ : syracuseStep 1180489 = 885367) (by norm_num)
theorem B2360141 : Blo 1048611 2360141 := bbase (se 3 (by rfl) ⟨442526, by rfl⟩ : syracuseStep 2360141 = 885053) (by norm_num)
theorem B1573709 : Blo 1048611 1573709 := bbase (se 3 (by rfl) ⟨295070, by rfl⟩ : syracuseStep 1573709 = 590141) (by norm_num)
theorem B1573733 : Blo 1048611 1573733 := bbase (se 4 (by rfl) ⟨147537, by rfl⟩ : syracuseStep 1573733 = 295075) (by norm_num)
theorem B1770349 : Blo 1048611 1770349 := bbase (se 3 (by rfl) ⟨331940, by rfl⟩ : syracuseStep 1770349 = 663881) (by norm_num)
theorem B1180525 : Blo 1048611 1180525 := bbase (se 3 (by rfl) ⟨221348, by rfl⟩ : syracuseStep 1180525 = 442697) (by norm_num)
theorem B1573757 : Blo 1048611 1573757 := bbase (se 3 (by rfl) ⟨295079, by rfl⟩ : syracuseStep 1573757 = 590159) (by norm_num)
theorem B4490117 : Blo 1048611 4490117 := bbase (se 4 (by rfl) ⟨420948, by rfl⟩ : syracuseStep 4490117 = 841897) (by norm_num)
theorem B1180561 : Blo 1048611 1180561 := bbase (se 2 (by rfl) ⟨442710, by rfl⟩ : syracuseStep 1180561 = 885421) (by norm_num)
theorem B3539861 : Blo 1048611 3539861 := bbase (se 6 (by rfl) ⟨82965, by rfl⟩ : syracuseStep 3539861 = 165931) (by norm_num)
theorem B2360213 : Blo 1048611 2360213 := bbase (se 6 (by rfl) ⟨55317, by rfl⟩ : syracuseStep 2360213 = 110635) (by norm_num)
theorem B1573781 : Blo 1048611 1573781 := bbase (se 6 (by rfl) ⟨36885, by rfl⟩ : syracuseStep 1573781 = 73771) (by norm_num)
theorem B1573805 : Blo 1048611 1573805 := bbase (se 3 (by rfl) ⟨295088, by rfl⟩ : syracuseStep 1573805 = 590177) (by norm_num)
theorem B1180597 : Blo 1048611 1180597 := bbase (se 5 (by rfl) ⟨55340, by rfl⟩ : syracuseStep 1180597 = 110681) (by norm_num)
theorem B1770437 : Blo 1048611 1770437 := bbase (se 4 (by rfl) ⟨165978, by rfl⟩ : syracuseStep 1770437 = 331957) (by norm_num)
theorem B1573829 : Blo 1048611 1573829 := bbase (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) (by norm_num)
theorem B1180633 : Blo 1048611 1180633 := bbase (se 2 (by rfl) ⟨442737, by rfl⟩ : syracuseStep 1180633 = 885475) (by norm_num)
theorem B2360285 : Blo 1048611 2360285 := bbase (se 3 (by rfl) ⟨442553, by rfl⟩ : syracuseStep 2360285 = 885107) (by norm_num)
theorem B1573853 : Blo 1048611 1573853 := bbase (se 3 (by rfl) ⟨295097, by rfl⟩ : syracuseStep 1573853 = 590195) (by norm_num)
theorem B1573877 : Blo 1048611 1573877 := bbase (se 5 (by rfl) ⟨73775, by rfl⟩ : syracuseStep 1573877 = 147551) (by norm_num)
theorem B2556917 : Blo 1048611 2556917 := bbase (se 5 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 2556917 = 239711) (by norm_num)
theorem B1180669 : Blo 1048611 1180669 := bbase (se 3 (by rfl) ⟨221375, by rfl⟩ : syracuseStep 1180669 = 442751) (by norm_num)
theorem B1573901 : Blo 1048611 1573901 := bbase (se 3 (by rfl) ⟨295106, by rfl⟩ : syracuseStep 1573901 = 590213) (by norm_num)
theorem B1180705 : Blo 1048611 1180705 := bbase (se 2 (by rfl) ⟨442764, by rfl⟩ : syracuseStep 1180705 = 885529) (by norm_num)
theorem B2360357 : Blo 1048611 2360357 := bbase (se 4 (by rfl) ⟨221283, by rfl⟩ : syracuseStep 2360357 = 442567) (by norm_num)
theorem B1573925 : Blo 1048611 1573925 := bbase (se 4 (by rfl) ⟨147555, by rfl⟩ : syracuseStep 1573925 = 295111) (by norm_num)
theorem B1573949 : Blo 1048611 1573949 := bbase (se 3 (by rfl) ⟨295115, by rfl⟩ : syracuseStep 1573949 = 590231) (by norm_num)
theorem B2655301 : Blo 1048611 2655301 := bbase (se 4 (by rfl) ⟨248934, by rfl⟩ : syracuseStep 2655301 = 497869) (by norm_num)
theorem B1770565 : Blo 1048611 1770565 := bbase (se 4 (by rfl) ⟨165990, by rfl⟩ : syracuseStep 1770565 = 331981) (by norm_num)
theorem B1180741 : Blo 1048611 1180741 := bbase (se 4 (by rfl) ⟨110694, by rfl⟩ : syracuseStep 1180741 = 221389) (by norm_num)
theorem B1573973 : Blo 1048611 1573973 := bbase (se 8 (by rfl) ⟨9222, by rfl⟩ : syracuseStep 1573973 = 18445) (by norm_num)
theorem B1180777 : Blo 1048611 1180777 := bbase (se 2 (by rfl) ⟨442791, by rfl⟩ : syracuseStep 1180777 = 885583) (by norm_num)
theorem B2360429 : Blo 1048611 2360429 := bbase (se 3 (by rfl) ⟨442580, by rfl⟩ : syracuseStep 2360429 = 885161) (by norm_num)
theorem B1573997 : Blo 1048611 1573997 := bbase (se 3 (by rfl) ⟨295124, by rfl⟩ : syracuseStep 1573997 = 590249) (by norm_num)
theorem B1574021 : Blo 1048611 1574021 := bbase (se 4 (by rfl) ⟨147564, by rfl⟩ : syracuseStep 1574021 = 295129) (by norm_num)
theorem B1180813 : Blo 1048611 1180813 := bbase (se 3 (by rfl) ⟨221402, by rfl⟩ : syracuseStep 1180813 = 442805) (by norm_num)
theorem B1770653 : Blo 1048611 1770653 := bbase (se 3 (by rfl) ⟨331997, by rfl⟩ : syracuseStep 1770653 = 663995) (by norm_num)
theorem B1574045 : Blo 1048611 1574045 := bbase (se 3 (by rfl) ⟨295133, by rfl⟩ : syracuseStep 1574045 = 590267) (by norm_num)
theorem B1180849 : Blo 1048611 1180849 := bbase (se 2 (by rfl) ⟨442818, by rfl⟩ : syracuseStep 1180849 = 885637) (by norm_num)
theorem B2655413 : Blo 1048611 2655413 := bbase (se 5 (by rfl) ⟨124472, by rfl⟩ : syracuseStep 2655413 = 248945) (by norm_num)
theorem B2360501 : Blo 1048611 2360501 := bbase (se 5 (by rfl) ⟨110648, by rfl⟩ : syracuseStep 2360501 = 221297) (by norm_num)
theorem B1574069 : Blo 1048611 1574069 := bbase (se 5 (by rfl) ⟨73784, by rfl⟩ : syracuseStep 1574069 = 147569) (by norm_num)
theorem B1574093 : Blo 1048611 1574093 := bbase (se 3 (by rfl) ⟨295142, by rfl⟩ : syracuseStep 1574093 = 590285) (by norm_num)
theorem B1180885 : Blo 1048611 1180885 := bbase (se 7 (by rfl) ⟨13838, by rfl⟩ : syracuseStep 1180885 = 27677) (by norm_num)
theorem B1574117 : Blo 1048611 1574117 := bbase (se 4 (by rfl) ⟨147573, by rfl⟩ : syracuseStep 1574117 = 295147) (by norm_num)
theorem B1180921 : Blo 1048611 1180921 := bbase (se 2 (by rfl) ⟨442845, by rfl⟩ : syracuseStep 1180921 = 885691) (by norm_num)
theorem B2360573 : Blo 1048611 2360573 := bbase (se 3 (by rfl) ⟨442607, by rfl⟩ : syracuseStep 2360573 = 885215) (by norm_num)
theorem B1574141 : Blo 1048611 1574141 := bbase (se 3 (by rfl) ⟨295151, by rfl⟩ : syracuseStep 1574141 = 590303) (by norm_num)
theorem B1574165 : Blo 1048611 1574165 := bbase (se 6 (by rfl) ⟨36894, by rfl⟩ : syracuseStep 1574165 = 73789) (by norm_num)
theorem B1770781 : Blo 1048611 1770781 := bbase (se 3 (by rfl) ⟨332021, by rfl⟩ : syracuseStep 1770781 = 664043) (by norm_num)
theorem B1180957 : Blo 1048611 1180957 := bbase (se 3 (by rfl) ⟨221429, by rfl⟩ : syracuseStep 1180957 = 442859) (by norm_num)
theorem B1574189 : Blo 1048611 1574189 := bbase (se 3 (by rfl) ⟨295160, by rfl⟩ : syracuseStep 1574189 = 590321) (by norm_num)
theorem B1180993 : Blo 1048611 1180993 := bbase (se 2 (by rfl) ⟨442872, by rfl⟩ : syracuseStep 1180993 = 885745) (by norm_num)
theorem B3540293 : Blo 1048611 3540293 := bbase (se 4 (by rfl) ⟨331902, by rfl⟩ : syracuseStep 3540293 = 663805) (by norm_num)
theorem B2360645 : Blo 1048611 2360645 := bbase (se 4 (by rfl) ⟨221310, by rfl⟩ : syracuseStep 2360645 = 442621) (by norm_num)
theorem B1574213 : Blo 1048611 1574213 := bbase (se 4 (by rfl) ⟨147582, by rfl⟩ : syracuseStep 1574213 = 295165) (by norm_num)
theorem B1574237 : Blo 1048611 1574237 := bbase (se 3 (by rfl) ⟨295169, by rfl⟩ : syracuseStep 1574237 = 590339) (by norm_num)
theorem B1181029 : Blo 1048611 1181029 := bbase (se 4 (by rfl) ⟨110721, by rfl⟩ : syracuseStep 1181029 = 221443) (by norm_num)
theorem B2655605 : Blo 1048611 2655605 := bbase (se 5 (by rfl) ⟨124481, by rfl⟩ : syracuseStep 2655605 = 248963) (by norm_num)
theorem B1770869 : Blo 1048611 1770869 := bbase (se 5 (by rfl) ⟨83009, by rfl⟩ : syracuseStep 1770869 = 166019) (by norm_num)
theorem B1574261 : Blo 1048611 1574261 := bbase (se 5 (by rfl) ⟨73793, by rfl⟩ : syracuseStep 1574261 = 147587) (by norm_num)
theorem B1181065 : Blo 1048611 1181065 := bbase (se 2 (by rfl) ⟨442899, by rfl⟩ : syracuseStep 1181065 = 885799) (by norm_num)
theorem B2360717 : Blo 1048611 2360717 := bbase (se 3 (by rfl) ⟨442634, by rfl⟩ : syracuseStep 2360717 = 885269) (by norm_num)
theorem B1574285 : Blo 1048611 1574285 := bbase (se 3 (by rfl) ⟨295178, by rfl⟩ : syracuseStep 1574285 = 590357) (by norm_num)
theorem B1574309 : Blo 1048611 1574309 := bbase (se 4 (by rfl) ⟨147591, by rfl⟩ : syracuseStep 1574309 = 295183) (by norm_num)
theorem B1181101 : Blo 1048611 1181101 := bbase (se 3 (by rfl) ⟨221456, by rfl⟩ : syracuseStep 1181101 = 442913) (by norm_num)
theorem B1574333 : Blo 1048611 1574333 := bbase (se 3 (by rfl) ⟨295187, by rfl⟩ : syracuseStep 1574333 = 590375) (by norm_num)
theorem B1181137 : Blo 1048611 1181137 := bbase (se 2 (by rfl) ⟨442926, by rfl⟩ : syracuseStep 1181137 = 885853) (by norm_num)
theorem B2360789 : Blo 1048611 2360789 := bbase (se 7 (by rfl) ⟨27665, by rfl⟩ : syracuseStep 2360789 = 55331) (by norm_num)
theorem B1574357 : Blo 1048611 1574357 := bbase (se 7 (by rfl) ⟨18449, by rfl⟩ : syracuseStep 1574357 = 36899) (by norm_num)
theorem B1574381 : Blo 1048611 1574381 := bbase (se 3 (by rfl) ⟨295196, by rfl⟩ : syracuseStep 1574381 = 590393) (by norm_num)
theorem B1770997 : Blo 1048611 1770997 := bbase (se 5 (by rfl) ⟨83015, by rfl⟩ : syracuseStep 1770997 = 166031) (by norm_num)
theorem B1181173 : Blo 1048611 1181173 := bbase (se 5 (by rfl) ⟨55367, by rfl⟩ : syracuseStep 1181173 = 110735) (by norm_num)
theorem B1574405 : Blo 1048611 1574405 := bbase (se 4 (by rfl) ⟨147600, by rfl⟩ : syracuseStep 1574405 = 295201) (by norm_num)
theorem B1181209 : Blo 1048611 1181209 := bbase (se 2 (by rfl) ⟨442953, by rfl⟩ : syracuseStep 1181209 = 885907) (by norm_num)
theorem B2360861 : Blo 1048611 2360861 := bbase (se 3 (by rfl) ⟨442661, by rfl⟩ : syracuseStep 2360861 = 885323) (by norm_num)
theorem B1574429 : Blo 1048611 1574429 := bbase (se 3 (by rfl) ⟨295205, by rfl⟩ : syracuseStep 1574429 = 590411) (by norm_num)
theorem B1574453 : Blo 1048611 1574453 := bbase (se 5 (by rfl) ⟨73802, by rfl⟩ : syracuseStep 1574453 = 147605) (by norm_num)
theorem B1181245 : Blo 1048611 1181245 := bbase (se 3 (by rfl) ⟨221483, by rfl⟩ : syracuseStep 1181245 = 442967) (by norm_num)
theorem B1771085 : Blo 1048611 1771085 := bbase (se 3 (by rfl) ⟨332078, by rfl⟩ : syracuseStep 1771085 = 664157) (by norm_num)
theorem B1574477 : Blo 1048611 1574477 := bbase (se 3 (by rfl) ⟨295214, by rfl⟩ : syracuseStep 1574477 = 590429) (by norm_num)
theorem B8619605 : Blo 1048611 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B1181281 : Blo 1048611 1181281 := bbase (se 2 (by rfl) ⟨442980, by rfl⟩ : syracuseStep 1181281 = 885961) (by norm_num)
theorem B2360933 : Blo 1048611 2360933 := bbase (se 4 (by rfl) ⟨221337, by rfl⟩ : syracuseStep 2360933 = 442675) (by norm_num)
theorem B1574501 : Blo 1048611 1574501 := bbase (se 4 (by rfl) ⟨147609, by rfl⟩ : syracuseStep 1574501 = 295219) (by norm_num)
theorem B1574525 : Blo 1048611 1574525 := bbase (se 3 (by rfl) ⟨295223, by rfl⟩ : syracuseStep 1574525 = 590447) (by norm_num)
theorem B1181317 : Blo 1048611 1181317 := bbase (se 4 (by rfl) ⟨110748, by rfl⟩ : syracuseStep 1181317 = 221497) (by norm_num)
theorem B2393749 : Blo 1048611 2393749 := bbase (se 6 (by rfl) ⟨56103, by rfl⟩ : syracuseStep 2393749 = 112207) (by norm_num)
theorem B1574549 : Blo 1048611 1574549 := bbase (se 6 (by rfl) ⟨36903, by rfl⟩ : syracuseStep 1574549 = 73807) (by norm_num)
theorem B1181353 : Blo 1048611 1181353 := bbase (se 2 (by rfl) ⟨443007, by rfl⟩ : syracuseStep 1181353 = 886015) (by norm_num)
theorem B2361005 : Blo 1048611 2361005 := bbase (se 3 (by rfl) ⟨442688, by rfl⟩ : syracuseStep 2361005 = 885377) (by norm_num)
theorem B1574573 : Blo 1048611 1574573 := bbase (se 3 (by rfl) ⟨295232, by rfl⟩ : syracuseStep 1574573 = 590465) (by norm_num)
theorem B1574597 : Blo 1048611 1574597 := bbase (se 4 (by rfl) ⟨147618, by rfl⟩ : syracuseStep 1574597 = 295237) (by norm_num)
theorem B2655949 : Blo 1048611 2655949 := bbase (se 3 (by rfl) ⟨497990, by rfl⟩ : syracuseStep 2655949 = 995981) (by norm_num)
theorem B1771213 : Blo 1048611 1771213 := bbase (se 3 (by rfl) ⟨332102, by rfl⟩ : syracuseStep 1771213 = 664205) (by norm_num)
theorem B1181389 : Blo 1048611 1181389 := bbase (se 3 (by rfl) ⟨221510, by rfl⟩ : syracuseStep 1181389 = 443021) (by norm_num)
theorem B1574621 : Blo 1048611 1574621 := bbase (se 3 (by rfl) ⟨295241, by rfl⟩ : syracuseStep 1574621 = 590483) (by norm_num)
theorem B2131685 : Blo 1048611 2131685 := bbase (se 4 (by rfl) ⟨199845, by rfl⟩ : syracuseStep 2131685 = 399691) (by norm_num)
theorem B1181425 : Blo 1048611 1181425 := bbase (se 2 (by rfl) ⟨443034, by rfl⟩ : syracuseStep 1181425 = 886069) (by norm_num)
theorem B5310197 : Blo 1048611 5310197 := bbase (se 5 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 5310197 = 497831) (by norm_num)
theorem B3540725 : Blo 1048611 3540725 := bbase (se 5 (by rfl) ⟨165971, by rfl⟩ : syracuseStep 3540725 = 331943) (by norm_num)
theorem B2361077 : Blo 1048611 2361077 := bbase (se 5 (by rfl) ⟨110675, by rfl⟩ : syracuseStep 2361077 = 221351) (by norm_num)
theorem B1574645 : Blo 1048611 1574645 := bbase (se 5 (by rfl) ⟨73811, by rfl⟩ : syracuseStep 1574645 = 147623) (by norm_num)
theorem B7571189 : Blo 1048611 7571189 := bbase (se 5 (by rfl) ⟨354899, by rfl⟩ : syracuseStep 7571189 = 709799) (by norm_num)
theorem B1574669 : Blo 1048611 1574669 := bbase (se 3 (by rfl) ⟨295250, by rfl⟩ : syracuseStep 1574669 = 590501) (by norm_num)
theorem B1181461 : Blo 1048611 1181461 := bbase (se 6 (by rfl) ⟨27690, by rfl⟩ : syracuseStep 1181461 = 55381) (by norm_num)
theorem B1771301 : Blo 1048611 1771301 := bbase (se 4 (by rfl) ⟨166059, by rfl⟩ : syracuseStep 1771301 = 332119) (by norm_num)
theorem B1574693 : Blo 1048611 1574693 := bbase (se 4 (by rfl) ⟨147627, by rfl⟩ : syracuseStep 1574693 = 295255) (by norm_num)
theorem B1181497 : Blo 1048611 1181497 := bbase (se 2 (by rfl) ⟨443061, by rfl⟩ : syracuseStep 1181497 = 886123) (by norm_num)
theorem B2656061 : Blo 1048611 2656061 := bbase (se 3 (by rfl) ⟨498011, by rfl⟩ : syracuseStep 2656061 = 996023) (by norm_num)
theorem B2361149 : Blo 1048611 2361149 := bbase (se 3 (by rfl) ⟨442715, by rfl⟩ : syracuseStep 2361149 = 885431) (by norm_num)
theorem B1574717 : Blo 1048611 1574717 := bbase (se 3 (by rfl) ⟨295259, by rfl⟩ : syracuseStep 1574717 = 590519) (by norm_num)
theorem B1574741 : Blo 1048611 1574741 := bbase (se 9 (by rfl) ⟨4613, by rfl⟩ : syracuseStep 1574741 = 9227) (by norm_num)
theorem B1181533 : Blo 1048611 1181533 := bbase (se 3 (by rfl) ⟨221537, by rfl⟩ : syracuseStep 1181533 = 443075) (by norm_num)
theorem B1574765 : Blo 1048611 1574765 := bbase (se 3 (by rfl) ⟨295268, by rfl⟩ : syracuseStep 1574765 = 590537) (by norm_num)
theorem B4786037 : Blo 1048611 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B1181569 : Blo 1048611 1181569 := bbase (se 2 (by rfl) ⟨443088, by rfl⟩ : syracuseStep 1181569 = 886177) (by norm_num)
theorem B2361221 : Blo 1048611 2361221 := bbase (se 4 (by rfl) ⟨221364, by rfl⟩ : syracuseStep 2361221 = 442729) (by norm_num)
theorem B1574789 : Blo 1048611 1574789 := bbase (se 4 (by rfl) ⟨147636, by rfl⟩ : syracuseStep 1574789 = 295273) (by norm_num)
theorem B1574813 : Blo 1048611 1574813 := bbase (se 3 (by rfl) ⟨295277, by rfl⟩ : syracuseStep 1574813 = 590555) (by norm_num)
theorem B1771429 : Blo 1048611 1771429 := bbase (se 4 (by rfl) ⟨166071, by rfl⟩ : syracuseStep 1771429 = 332143) (by norm_num)
theorem B1181605 : Blo 1048611 1181605 := bbase (se 4 (by rfl) ⟨110775, by rfl⟩ : syracuseStep 1181605 = 221551) (by norm_num)
theorem B1574837 : Blo 1048611 1574837 := bbase (se 5 (by rfl) ⟨73820, by rfl⟩ : syracuseStep 1574837 = 147641) (by norm_num)
theorem B1181641 : Blo 1048611 1181641 := bbase (se 2 (by rfl) ⟨443115, by rfl⟩ : syracuseStep 1181641 = 886231) (by norm_num)
theorem B2361293 : Blo 1048611 2361293 := bbase (se 3 (by rfl) ⟨442742, by rfl⟩ : syracuseStep 2361293 = 885485) (by norm_num)
theorem B1574861 : Blo 1048611 1574861 := bbase (se 3 (by rfl) ⟨295286, by rfl⟩ : syracuseStep 1574861 = 590573) (by norm_num)
theorem B1574885 : Blo 1048611 1574885 := bbase (se 4 (by rfl) ⟨147645, by rfl⟩ : syracuseStep 1574885 = 295291) (by norm_num)
theorem B1181677 : Blo 1048611 1181677 := bbase (se 3 (by rfl) ⟨221564, by rfl⟩ : syracuseStep 1181677 = 443129) (by norm_num)
theorem B2656253 : Blo 1048611 2656253 := bbase (se 3 (by rfl) ⟨498047, by rfl⟩ : syracuseStep 2656253 = 996095) (by norm_num)
theorem B1771517 : Blo 1048611 1771517 := bbase (se 3 (by rfl) ⟨332159, by rfl⟩ : syracuseStep 1771517 = 664319) (by norm_num)
theorem B1574909 : Blo 1048611 1574909 := bbase (se 3 (by rfl) ⟨295295, by rfl⟩ : syracuseStep 1574909 = 590591) (by norm_num)
theorem B1181713 : Blo 1048611 1181713 := bbase (se 2 (by rfl) ⟨443142, by rfl⟩ : syracuseStep 1181713 = 886285) (by norm_num)
theorem B2361365 : Blo 1048611 2361365 := bbase (se 6 (by rfl) ⟨55344, by rfl⟩ : syracuseStep 2361365 = 110689) (by norm_num)
theorem B1574933 : Blo 1048611 1574933 := bbase (se 6 (by rfl) ⟨36912, by rfl⟩ : syracuseStep 1574933 = 73825) (by norm_num)
theorem B4556837 : Blo 1048611 4556837 := bbase (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) (by norm_num)
theorem B1574957 : Blo 1048611 1574957 := bbase (se 3 (by rfl) ⟨295304, by rfl⟩ : syracuseStep 1574957 = 590609) (by norm_num)
theorem B1181749 : Blo 1048611 1181749 := bbase (se 5 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 1181749 = 110789) (by norm_num)
theorem B1574981 : Blo 1048611 1574981 := bbase (se 4 (by rfl) ⟨147654, by rfl⟩ : syracuseStep 1574981 = 295309) (by norm_num)
theorem B1181785 : Blo 1048611 1181785 := bbase (se 2 (by rfl) ⟨443169, by rfl⟩ : syracuseStep 1181785 = 886339) (by norm_num)
theorem B2361437 : Blo 1048611 2361437 := bbase (se 3 (by rfl) ⟨442769, by rfl⟩ : syracuseStep 2361437 = 885539) (by norm_num)
theorem B1575005 : Blo 1048611 1575005 := bbase (se 3 (by rfl) ⟨295313, by rfl⟩ : syracuseStep 1575005 = 590627) (by norm_num)
theorem B1575029 : Blo 1048611 1575029 := bbase (se 5 (by rfl) ⟨73829, by rfl⟩ : syracuseStep 1575029 = 147659) (by norm_num)
theorem B1771645 : Blo 1048611 1771645 := bbase (se 3 (by rfl) ⟨332183, by rfl⟩ : syracuseStep 1771645 = 664367) (by norm_num)
theorem B1181821 : Blo 1048611 1181821 := bbase (se 3 (by rfl) ⟨221591, by rfl⟩ : syracuseStep 1181821 = 443183) (by norm_num)
theorem B1575053 : Blo 1048611 1575053 := bbase (se 3 (by rfl) ⟨295322, by rfl⟩ : syracuseStep 1575053 = 590645) (by norm_num)
theorem B1181857 : Blo 1048611 1181857 := bbase (se 2 (by rfl) ⟨443196, by rfl⟩ : syracuseStep 1181857 = 886393) (by norm_num)
theorem B3541157 : Blo 1048611 3541157 := bbase (se 4 (by rfl) ⟨331983, by rfl⟩ : syracuseStep 3541157 = 663967) (by norm_num)
theorem B2361509 : Blo 1048611 2361509 := bbase (se 4 (by rfl) ⟨221391, by rfl⟩ : syracuseStep 2361509 = 442783) (by norm_num)
theorem B1575077 : Blo 1048611 1575077 := bbase (se 4 (by rfl) ⟨147663, by rfl⟩ : syracuseStep 1575077 = 295327) (by norm_num)
theorem B1575101 : Blo 1048611 1575101 := bbase (se 3 (by rfl) ⟨295331, by rfl⟩ : syracuseStep 1575101 = 590663) (by norm_num)
theorem B1181893 : Blo 1048611 1181893 := bbase (se 4 (by rfl) ⟨110802, by rfl⟩ : syracuseStep 1181893 = 221605) (by norm_num)
theorem B1771733 : Blo 1048611 1771733 := bbase (se 7 (by rfl) ⟨20762, by rfl⟩ : syracuseStep 1771733 = 41525) (by norm_num)
theorem B1575125 : Blo 1048611 1575125 := bbase (se 7 (by rfl) ⟨18458, by rfl⟩ : syracuseStep 1575125 = 36917) (by norm_num)
theorem B1181929 : Blo 1048611 1181929 := bbase (se 2 (by rfl) ⟨443223, by rfl⟩ : syracuseStep 1181929 = 886447) (by norm_num)
theorem B2361581 : Blo 1048611 2361581 := bbase (se 3 (by rfl) ⟨442796, by rfl⟩ : syracuseStep 2361581 = 885593) (by norm_num)
theorem B1575149 : Blo 1048611 1575149 := bbase (se 3 (by rfl) ⟨295340, by rfl⟩ : syracuseStep 1575149 = 590681) (by norm_num)
theorem B1575173 : Blo 1048611 1575173 := bbase (se 4 (by rfl) ⟨147672, by rfl⟩ : syracuseStep 1575173 = 295345) (by norm_num)
theorem B1181965 : Blo 1048611 1181965 := bbase (se 3 (by rfl) ⟨221618, by rfl⟩ : syracuseStep 1181965 = 443237) (by norm_num)
theorem B1575197 : Blo 1048611 1575197 := bbase (se 3 (by rfl) ⟨295349, by rfl⟩ : syracuseStep 1575197 = 590699) (by norm_num)
theorem B1182001 : Blo 1048611 1182001 := bbase (se 2 (by rfl) ⟨443250, by rfl⟩ : syracuseStep 1182001 = 886501) (by norm_num)
theorem B2361653 : Blo 1048611 2361653 := bbase (se 5 (by rfl) ⟨110702, by rfl⟩ : syracuseStep 2361653 = 221405) (by norm_num)
theorem B1575221 : Blo 1048611 1575221 := bbase (se 5 (by rfl) ⟨73838, by rfl⟩ : syracuseStep 1575221 = 147677) (by norm_num)
theorem B1575245 : Blo 1048611 1575245 := bbase (se 3 (by rfl) ⟨295358, by rfl⟩ : syracuseStep 1575245 = 590717) (by norm_num)
theorem B2656597 : Blo 1048611 2656597 := bbase (se 10 (by rfl) ⟨3891, by rfl⟩ : syracuseStep 2656597 = 7783) (by norm_num)
theorem B1771861 : Blo 1048611 1771861 := bbase (se 10 (by rfl) ⟨2595, by rfl⟩ : syracuseStep 1771861 = 5191) (by norm_num)
theorem B1182037 : Blo 1048611 1182037 := bbase (se 10 (by rfl) ⟨1731, by rfl⟩ : syracuseStep 1182037 = 3463) (by norm_num)
theorem B1575269 : Blo 1048611 1575269 := bbase (se 4 (by rfl) ⟨147681, by rfl⟩ : syracuseStep 1575269 = 295363) (by norm_num)
theorem B1182073 : Blo 1048611 1182073 := bbase (se 2 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 1182073 = 886555) (by norm_num)
theorem B2361725 : Blo 1048611 2361725 := bbase (se 3 (by rfl) ⟨442823, by rfl⟩ : syracuseStep 2361725 = 885647) (by norm_num)
theorem B1575293 : Blo 1048611 1575293 := bbase (se 3 (by rfl) ⟨295367, by rfl⟩ : syracuseStep 1575293 = 590735) (by norm_num)
theorem B1575317 : Blo 1048611 1575317 := bbase (se 6 (by rfl) ⟨36921, by rfl⟩ : syracuseStep 1575317 = 73843) (by norm_num)
theorem B1182109 : Blo 1048611 1182109 := bbase (se 3 (by rfl) ⟨221645, by rfl⟩ : syracuseStep 1182109 = 443291) (by norm_num)
theorem B1771949 : Blo 1048611 1771949 := bbase (se 3 (by rfl) ⟨332240, by rfl⟩ : syracuseStep 1771949 = 664481) (by norm_num)
theorem B1575341 : Blo 1048611 1575341 := bbase (se 3 (by rfl) ⟨295376, by rfl⟩ : syracuseStep 1575341 = 590753) (by norm_num)
theorem B1182145 : Blo 1048611 1182145 := bbase (se 2 (by rfl) ⟨443304, by rfl⟩ : syracuseStep 1182145 = 886609) (by norm_num)
theorem B2656709 : Blo 1048611 2656709 := bbase (se 4 (by rfl) ⟨249066, by rfl⟩ : syracuseStep 2656709 = 498133) (by norm_num)
theorem B2361797 : Blo 1048611 2361797 := bbase (se 4 (by rfl) ⟨221418, by rfl⟩ : syracuseStep 2361797 = 442837) (by norm_num)
theorem B1575365 : Blo 1048611 1575365 := bbase (se 4 (by rfl) ⟨147690, by rfl⟩ : syracuseStep 1575365 = 295381) (by norm_num)
theorem B1575389 : Blo 1048611 1575389 := bbase (se 3 (by rfl) ⟨295385, by rfl⟩ : syracuseStep 1575389 = 590771) (by norm_num)
theorem B1182181 : Blo 1048611 1182181 := bbase (se 4 (by rfl) ⟨110829, by rfl⟩ : syracuseStep 1182181 = 221659) (by norm_num)
theorem B1575413 : Blo 1048611 1575413 := bbase (se 5 (by rfl) ⟨73847, by rfl⟩ : syracuseStep 1575413 = 147695) (by norm_num)
theorem B1182217 : Blo 1048611 1182217 := bbase (se 2 (by rfl) ⟨443331, by rfl⟩ : syracuseStep 1182217 = 886663) (by norm_num)
theorem B2361869 : Blo 1048611 2361869 := bbase (se 3 (by rfl) ⟨442850, by rfl⟩ : syracuseStep 2361869 = 885701) (by norm_num)
theorem B1575437 : Blo 1048611 1575437 := bbase (se 3 (by rfl) ⟨295394, by rfl⟩ : syracuseStep 1575437 = 590789) (by norm_num)
theorem B1575461 : Blo 1048611 1575461 := bbase (se 4 (by rfl) ⟨147699, by rfl⟩ : syracuseStep 1575461 = 295399) (by norm_num)
theorem B1772077 : Blo 1048611 1772077 := bbase (se 3 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 1772077 = 664529) (by norm_num)
theorem B1182253 : Blo 1048611 1182253 := bbase (se 3 (by rfl) ⟨221672, by rfl⟩ : syracuseStep 1182253 = 443345) (by norm_num)
theorem B1575485 : Blo 1048611 1575485 := bbase (se 3 (by rfl) ⟨295403, by rfl⟩ : syracuseStep 1575485 = 590807) (by norm_num)
theorem B1182289 : Blo 1048611 1182289 := bbase (se 2 (by rfl) ⟨443358, by rfl⟩ : syracuseStep 1182289 = 886717) (by norm_num)
theorem B3541589 : Blo 1048611 3541589 := bbase (se 8 (by rfl) ⟨20751, by rfl⟩ : syracuseStep 3541589 = 41503) (by norm_num)
theorem B2361941 : Blo 1048611 2361941 := bbase (se 8 (by rfl) ⟨13839, by rfl⟩ : syracuseStep 2361941 = 27679) (by norm_num)
theorem B1575509 : Blo 1048611 1575509 := bbase (se 8 (by rfl) ⟨9231, by rfl⟩ : syracuseStep 1575509 = 18463) (by norm_num)
theorem B1575533 : Blo 1048611 1575533 := bbase (se 3 (by rfl) ⟨295412, by rfl⟩ : syracuseStep 1575533 = 590825) (by norm_num)
theorem B1182325 : Blo 1048611 1182325 := bbase (se 5 (by rfl) ⟨55421, by rfl⟩ : syracuseStep 1182325 = 110843) (by norm_num)
theorem B2656901 : Blo 1048611 2656901 := bbase (se 4 (by rfl) ⟨249084, by rfl⟩ : syracuseStep 2656901 = 498169) (by norm_num)
theorem B1772165 : Blo 1048611 1772165 := bbase (se 4 (by rfl) ⟨166140, by rfl⟩ : syracuseStep 1772165 = 332281) (by norm_num)
theorem B1575557 : Blo 1048611 1575557 := bbase (se 4 (by rfl) ⟨147708, by rfl⟩ : syracuseStep 1575557 = 295417) (by norm_num)
theorem B2525845 : Blo 1048611 2525845 := bbase (se 6 (by rfl) ⟨59199, by rfl⟩ : syracuseStep 2525845 = 118399) (by norm_num)
theorem B1182361 : Blo 1048611 1182361 := bbase (se 2 (by rfl) ⟨443385, by rfl⟩ : syracuseStep 1182361 = 886771) (by norm_num)
theorem B2362013 : Blo 1048611 2362013 := bbase (se 3 (by rfl) ⟨442877, by rfl⟩ : syracuseStep 2362013 = 885755) (by norm_num)
theorem B1575581 : Blo 1048611 1575581 := bbase (se 3 (by rfl) ⟨295421, by rfl⟩ : syracuseStep 1575581 = 590843) (by norm_num)
theorem B1575605 : Blo 1048611 1575605 := bbase (se 5 (by rfl) ⟨73856, by rfl⟩ : syracuseStep 1575605 = 147713) (by norm_num)
theorem B1346233 : Blo 1048611 1346233 := bbase (se 2 (by rfl) ⟨504837, by rfl⟩ : syracuseStep 1346233 = 1009675) (by norm_num)
theorem B1182397 : Blo 1048611 1182397 := bbase (se 3 (by rfl) ⟨221699, by rfl⟩ : syracuseStep 1182397 = 443399) (by norm_num)
theorem B1575629 : Blo 1048611 1575629 := bbase (se 3 (by rfl) ⟨295430, by rfl⟩ : syracuseStep 1575629 = 590861) (by norm_num)
theorem B1182433 : Blo 1048611 1182433 := bbase (se 2 (by rfl) ⟨443412, by rfl⟩ : syracuseStep 1182433 = 886825) (by norm_num)
theorem B2362085 : Blo 1048611 2362085 := bbase (se 4 (by rfl) ⟨221445, by rfl⟩ : syracuseStep 2362085 = 442891) (by norm_num)
theorem B1575653 : Blo 1048611 1575653 := bbase (se 4 (by rfl) ⟨147717, by rfl⟩ : syracuseStep 1575653 = 295435) (by norm_num)
theorem B1575677 : Blo 1048611 1575677 := bbase (se 3 (by rfl) ⟨295439, by rfl⟩ : syracuseStep 1575677 = 590879) (by norm_num)
theorem B1772293 : Blo 1048611 1772293 := bbase (se 4 (by rfl) ⟨166152, by rfl⟩ : syracuseStep 1772293 = 332305) (by norm_num)
theorem B1182469 : Blo 1048611 1182469 := bbase (se 4 (by rfl) ⟨110856, by rfl⟩ : syracuseStep 1182469 = 221713) (by norm_num)
theorem B1575701 : Blo 1048611 1575701 := bbase (se 6 (by rfl) ⟨36930, by rfl⟩ : syracuseStep 1575701 = 73861) (by norm_num)
theorem B2394917 : Blo 1048611 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B1182505 : Blo 1048611 1182505 := bbase (se 2 (by rfl) ⟨443439, by rfl⟩ : syracuseStep 1182505 = 886879) (by norm_num)
theorem B2362157 : Blo 1048611 2362157 := bbase (se 3 (by rfl) ⟨442904, by rfl⟩ : syracuseStep 2362157 = 885809) (by norm_num)
theorem B1575725 : Blo 1048611 1575725 := bbase (se 3 (by rfl) ⟨295448, by rfl⟩ : syracuseStep 1575725 = 590897) (by norm_num)
theorem B1575749 : Blo 1048611 1575749 := bbase (se 4 (by rfl) ⟨147726, by rfl⟩ : syracuseStep 1575749 = 295453) (by norm_num)
theorem B1182541 : Blo 1048611 1182541 := bbase (se 3 (by rfl) ⟨221726, by rfl⟩ : syracuseStep 1182541 = 443453) (by norm_num)
theorem B1772381 : Blo 1048611 1772381 := bbase (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) (by norm_num)
theorem B1575773 : Blo 1048611 1575773 := bbase (se 3 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 1575773 = 590915) (by norm_num)
theorem B1182577 : Blo 1048611 1182577 := bbase (se 2 (by rfl) ⟨443466, by rfl⟩ : syracuseStep 1182577 = 886933) (by norm_num)
theorem B2362229 : Blo 1048611 2362229 := bbase (se 5 (by rfl) ⟨110729, by rfl⟩ : syracuseStep 2362229 = 221459) (by norm_num)
theorem B1575797 : Blo 1048611 1575797 := bbase (se 5 (by rfl) ⟨73865, by rfl⟩ : syracuseStep 1575797 = 147731) (by norm_num)
theorem B1575821 : Blo 1048611 1575821 := bbase (se 3 (by rfl) ⟨295466, by rfl⟩ : syracuseStep 1575821 = 590933) (by norm_num)
theorem B1182613 : Blo 1048611 1182613 := bbase (se 6 (by rfl) ⟨27717, by rfl⟩ : syracuseStep 1182613 = 55435) (by norm_num)
theorem B1575845 : Blo 1048611 1575845 := bbase (se 4 (by rfl) ⟨147735, by rfl⟩ : syracuseStep 1575845 = 295471) (by norm_num)
theorem B1182649 : Blo 1048611 1182649 := bbase (se 2 (by rfl) ⟨443493, by rfl⟩ : syracuseStep 1182649 = 886987) (by norm_num)
theorem B2362301 : Blo 1048611 2362301 := bbase (se 3 (by rfl) ⟨442931, by rfl⟩ : syracuseStep 2362301 = 885863) (by norm_num)
theorem B1575869 : Blo 1048611 1575869 := bbase (se 3 (by rfl) ⟨295475, by rfl⟩ : syracuseStep 1575869 = 590951) (by norm_num)
theorem B1575893 : Blo 1048611 1575893 := bbase (se 7 (by rfl) ⟨18467, by rfl⟩ : syracuseStep 1575893 = 36935) (by norm_num)
theorem B2657245 : Blo 1048611 2657245 := bbase (se 3 (by rfl) ⟨498233, by rfl⟩ : syracuseStep 2657245 = 996467) (by norm_num)
theorem B1772509 : Blo 1048611 1772509 := bbase (se 3 (by rfl) ⟨332345, by rfl⟩ : syracuseStep 1772509 = 664691) (by norm_num)
theorem B1182685 : Blo 1048611 1182685 := bbase (se 3 (by rfl) ⟨221753, by rfl⟩ : syracuseStep 1182685 = 443507) (by norm_num)
theorem B1575917 : Blo 1048611 1575917 := bbase (se 3 (by rfl) ⟨295484, by rfl⟩ : syracuseStep 1575917 = 590969) (by norm_num)
theorem B1182721 : Blo 1048611 1182721 := bbase (se 2 (by rfl) ⟨443520, by rfl⟩ : syracuseStep 1182721 = 887041) (by norm_num)
theorem B5311493 : Blo 1048611 5311493 := bbase (se 4 (by rfl) ⟨497952, by rfl⟩ : syracuseStep 5311493 = 995905) (by norm_num)
theorem B3542021 : Blo 1048611 3542021 := bbase (se 4 (by rfl) ⟨332064, by rfl⟩ : syracuseStep 3542021 = 664129) (by norm_num)
theorem B2362373 : Blo 1048611 2362373 := bbase (se 4 (by rfl) ⟨221472, by rfl⟩ : syracuseStep 2362373 = 442945) (by norm_num)
theorem B1575941 : Blo 1048611 1575941 := bbase (se 4 (by rfl) ⟨147744, by rfl⟩ : syracuseStep 1575941 = 295489) (by norm_num)
theorem B1575965 : Blo 1048611 1575965 := bbase (se 3 (by rfl) ⟨295493, by rfl⟩ : syracuseStep 1575965 = 590987) (by norm_num)
theorem B1182757 : Blo 1048611 1182757 := bbase (se 4 (by rfl) ⟨110883, by rfl⟩ : syracuseStep 1182757 = 221767) (by norm_num)
theorem B1772597 : Blo 1048611 1772597 := bbase (se 5 (by rfl) ⟨83090, by rfl⟩ : syracuseStep 1772597 = 166181) (by norm_num)
theorem B1575989 : Blo 1048611 1575989 := bbase (se 5 (by rfl) ⟨73874, by rfl⟩ : syracuseStep 1575989 = 147749) (by norm_num)
theorem B1182793 : Blo 1048611 1182793 := bbase (se 2 (by rfl) ⟨443547, by rfl⟩ : syracuseStep 1182793 = 887095) (by norm_num)
theorem B2657357 : Blo 1048611 2657357 := bbase (se 3 (by rfl) ⟨498254, by rfl⟩ : syracuseStep 2657357 = 996509) (by norm_num)
theorem B2362445 : Blo 1048611 2362445 := bbase (se 3 (by rfl) ⟨442958, by rfl⟩ : syracuseStep 2362445 = 885917) (by norm_num)
theorem B1576013 : Blo 1048611 1576013 := bbase (se 3 (by rfl) ⟨295502, by rfl⟩ : syracuseStep 1576013 = 591005) (by norm_num)
theorem B1576037 : Blo 1048611 1576037 := bbase (se 4 (by rfl) ⟨147753, by rfl⟩ : syracuseStep 1576037 = 295507) (by norm_num)
theorem B1182829 : Blo 1048611 1182829 := bbase (se 3 (by rfl) ⟨221780, by rfl⟩ : syracuseStep 1182829 = 443561) (by norm_num)
theorem B1576061 : Blo 1048611 1576061 := bbase (se 3 (by rfl) ⟨295511, by rfl⟩ : syracuseStep 1576061 = 591023) (by norm_num)
theorem B1182865 : Blo 1048611 1182865 := bbase (se 2 (by rfl) ⟨443574, by rfl⟩ : syracuseStep 1182865 = 887149) (by norm_num)
theorem B2362517 : Blo 1048611 2362517 := bbase (se 6 (by rfl) ⟨55371, by rfl⟩ : syracuseStep 2362517 = 110743) (by norm_num)
theorem B1576085 : Blo 1048611 1576085 := bbase (se 6 (by rfl) ⟨36939, by rfl⟩ : syracuseStep 1576085 = 73879) (by norm_num)
theorem B2526365 : Blo 1048611 2526365 := bbase (se 3 (by rfl) ⟨473693, by rfl⟩ : syracuseStep 2526365 = 947387) (by norm_num)
theorem B1576109 : Blo 1048611 1576109 := bbase (se 3 (by rfl) ⟨295520, by rfl⟩ : syracuseStep 1576109 = 591041) (by norm_num)
theorem B1772725 : Blo 1048611 1772725 := bbase (se 5 (by rfl) ⟨83096, by rfl⟩ : syracuseStep 1772725 = 166193) (by norm_num)
theorem B1182901 : Blo 1048611 1182901 := bbase (se 5 (by rfl) ⟨55448, by rfl⟩ : syracuseStep 1182901 = 110897) (by norm_num)
theorem B1576133 : Blo 1048611 1576133 := bbase (se 4 (by rfl) ⟨147762, by rfl⟩ : syracuseStep 1576133 = 295525) (by norm_num)
theorem B1182937 : Blo 1048611 1182937 := bbase (se 2 (by rfl) ⟨443601, by rfl⟩ : syracuseStep 1182937 = 887203) (by norm_num)
theorem B2362589 : Blo 1048611 2362589 := bbase (se 3 (by rfl) ⟨442985, by rfl⟩ : syracuseStep 2362589 = 885971) (by norm_num)
theorem B1576157 : Blo 1048611 1576157 := bbase (se 3 (by rfl) ⟨295529, by rfl⟩ : syracuseStep 1576157 = 591059) (by norm_num)
theorem B1576181 : Blo 1048611 1576181 := bbase (se 5 (by rfl) ⟨73883, by rfl⟩ : syracuseStep 1576181 = 147767) (by norm_num)
theorem B2526461 : Blo 1048611 2526461 := bbase (se 3 (by rfl) ⟨473711, by rfl⟩ : syracuseStep 2526461 = 947423) (by norm_num)
theorem B1182973 : Blo 1048611 1182973 := bbase (se 3 (by rfl) ⟨221807, by rfl⟩ : syracuseStep 1182973 = 443615) (by norm_num)
theorem B2657549 : Blo 1048611 2657549 := bbase (se 3 (by rfl) ⟨498290, by rfl⟩ : syracuseStep 2657549 = 996581) (by norm_num)
theorem B1772813 : Blo 1048611 1772813 := bbase (se 3 (by rfl) ⟨332402, by rfl⟩ : syracuseStep 1772813 = 664805) (by norm_num)
theorem B1576205 : Blo 1048611 1576205 := bbase (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) (by norm_num)
theorem B1183009 : Blo 1048611 1183009 := bbase (se 2 (by rfl) ⟨443628, by rfl⟩ : syracuseStep 1183009 = 887257) (by norm_num)
theorem B2362661 : Blo 1048611 2362661 := bbase (se 4 (by rfl) ⟨221499, by rfl⟩ : syracuseStep 2362661 = 442999) (by norm_num)
theorem B1576229 : Blo 1048611 1576229 := bbase (se 4 (by rfl) ⟨147771, by rfl⟩ : syracuseStep 1576229 = 295543) (by norm_num)
theorem B1576253 : Blo 1048611 1576253 := bbase (se 3 (by rfl) ⟨295547, by rfl⟩ : syracuseStep 1576253 = 591095) (by norm_num)
theorem B1183045 : Blo 1048611 1183045 := bbase (se 4 (by rfl) ⟨110910, by rfl⟩ : syracuseStep 1183045 = 221821) (by norm_num)
theorem B1576277 : Blo 1048611 1576277 := bbase (se 11 (by rfl) ⟨1154, by rfl⟩ : syracuseStep 1576277 = 2309) (by norm_num)
theorem B1183081 : Blo 1048611 1183081 := bbase (se 2 (by rfl) ⟨443655, by rfl⟩ : syracuseStep 1183081 = 887311) (by norm_num)
theorem B2362733 : Blo 1048611 2362733 := bbase (se 3 (by rfl) ⟨443012, by rfl⟩ : syracuseStep 2362733 = 886025) (by norm_num)
theorem B1576301 : Blo 1048611 1576301 := bbase (se 3 (by rfl) ⟨295556, by rfl⟩ : syracuseStep 1576301 = 591113) (by norm_num)
theorem B2133373 : Blo 1048611 2133373 := bbase (se 3 (by rfl) ⟨400007, by rfl⟩ : syracuseStep 2133373 = 800015) (by norm_num)
theorem B1576325 : Blo 1048611 1576325 := bbase (se 4 (by rfl) ⟨147780, by rfl⟩ : syracuseStep 1576325 = 295561) (by norm_num)
theorem B1772941 : Blo 1048611 1772941 := bbase (se 3 (by rfl) ⟨332426, by rfl⟩ : syracuseStep 1772941 = 664853) (by norm_num)
theorem B1183117 : Blo 1048611 1183117 := bbase (se 3 (by rfl) ⟨221834, by rfl⟩ : syracuseStep 1183117 = 443669) (by norm_num)
theorem B1576349 : Blo 1048611 1576349 := bbase (se 3 (by rfl) ⟨295565, by rfl⟩ : syracuseStep 1576349 = 591131) (by norm_num)
theorem B1183153 : Blo 1048611 1183153 := bbase (se 2 (by rfl) ⟨443682, by rfl⟩ : syracuseStep 1183153 = 887365) (by norm_num)
theorem B3542453 : Blo 1048611 3542453 := bbase (se 5 (by rfl) ⟨166052, by rfl⟩ : syracuseStep 3542453 = 332105) (by norm_num)
theorem B2362805 : Blo 1048611 2362805 := bbase (se 5 (by rfl) ⟨110756, by rfl⟩ : syracuseStep 2362805 = 221513) (by norm_num)
theorem B1576373 : Blo 1048611 1576373 := bbase (se 5 (by rfl) ⟨73892, by rfl⟩ : syracuseStep 1576373 = 147785) (by norm_num)
theorem B1347017 : Blo 1048611 1347017 := bbase (se 2 (by rfl) ⟨505131, by rfl⟩ : syracuseStep 1347017 = 1010263) (by norm_num)
theorem B1576397 : Blo 1048611 1576397 := bbase (se 3 (by rfl) ⟨295574, by rfl⟩ : syracuseStep 1576397 = 591149) (by norm_num)
theorem B1183189 : Blo 1048611 1183189 := bbase (se 7 (by rfl) ⟨13865, by rfl⟩ : syracuseStep 1183189 = 27731) (by norm_num)
theorem B1773029 : Blo 1048611 1773029 := bbase (se 4 (by rfl) ⟨166221, by rfl⟩ : syracuseStep 1773029 = 332443) (by norm_num)
theorem B1576421 : Blo 1048611 1576421 := bbase (se 4 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 1576421 = 295579) (by norm_num)
theorem B1183225 : Blo 1048611 1183225 := bbase (se 2 (by rfl) ⟨443709, by rfl⟩ : syracuseStep 1183225 = 887419) (by norm_num)
theorem B2362877 : Blo 1048611 2362877 := bbase (se 3 (by rfl) ⟨443039, by rfl⟩ : syracuseStep 2362877 = 886079) (by norm_num)
theorem B1576445 : Blo 1048611 1576445 := bbase (se 3 (by rfl) ⟨295583, by rfl⟩ : syracuseStep 1576445 = 591167) (by norm_num)
theorem B7573013 : Blo 1048611 7573013 := bbase (se 6 (by rfl) ⟨177492, by rfl⟩ : syracuseStep 7573013 = 354985) (by norm_num)
theorem B1576469 : Blo 1048611 1576469 := bbase (se 6 (by rfl) ⟨36948, by rfl⟩ : syracuseStep 1576469 = 73897) (by norm_num)
theorem B1183261 : Blo 1048611 1183261 := bbase (se 3 (by rfl) ⟨221861, by rfl⟩ : syracuseStep 1183261 = 443723) (by norm_num)
theorem B1576493 : Blo 1048611 1576493 := bbase (se 3 (by rfl) ⟨295592, by rfl⟩ : syracuseStep 1576493 = 591185) (by norm_num)
theorem B1347121 : Blo 1048611 1347121 := bbase (se 2 (by rfl) ⟨505170, by rfl⟩ : syracuseStep 1347121 = 1010341) (by norm_num)
theorem B1183297 : Blo 1048611 1183297 := bbase (se 2 (by rfl) ⟨443736, by rfl⟩ : syracuseStep 1183297 = 887473) (by norm_num)
theorem B2362949 : Blo 1048611 2362949 := bbase (se 4 (by rfl) ⟨221526, by rfl⟩ : syracuseStep 2362949 = 443053) (by norm_num)
theorem B1576517 : Blo 1048611 1576517 := bbase (se 4 (by rfl) ⟨147798, by rfl⟩ : syracuseStep 1576517 = 295597) (by norm_num)
theorem B1576541 : Blo 1048611 1576541 := bbase (se 3 (by rfl) ⟨295601, by rfl⟩ : syracuseStep 1576541 = 591203) (by norm_num)
theorem B2657893 : Blo 1048611 2657893 := bbase (se 4 (by rfl) ⟨249177, by rfl⟩ : syracuseStep 2657893 = 498355) (by norm_num)
theorem B1773157 : Blo 1048611 1773157 := bbase (se 4 (by rfl) ⟨166233, by rfl⟩ : syracuseStep 1773157 = 332467) (by norm_num)
theorem B1183333 : Blo 1048611 1183333 := bbase (se 4 (by rfl) ⟨110937, by rfl⟩ : syracuseStep 1183333 = 221875) (by norm_num)
theorem B1576565 : Blo 1048611 1576565 := bbase (se 5 (by rfl) ⟨73901, by rfl⟩ : syracuseStep 1576565 = 147803) (by norm_num)
theorem B1183369 : Blo 1048611 1183369 := bbase (se 2 (by rfl) ⟨443763, by rfl⟩ : syracuseStep 1183369 = 887527) (by norm_num)
theorem B2363021 : Blo 1048611 2363021 := bbase (se 3 (by rfl) ⟨443066, by rfl⟩ : syracuseStep 2363021 = 886133) (by norm_num)
theorem B1576589 : Blo 1048611 1576589 := bbase (se 3 (by rfl) ⟨295610, by rfl⟩ : syracuseStep 1576589 = 591221) (by norm_num)
theorem B1576613 : Blo 1048611 1576613 := bbase (se 4 (by rfl) ⟨147807, by rfl⟩ : syracuseStep 1576613 = 295615) (by norm_num)
theorem B1183405 : Blo 1048611 1183405 := bbase (se 3 (by rfl) ⟨221888, by rfl⟩ : syracuseStep 1183405 = 443777) (by norm_num)
theorem B1773245 : Blo 1048611 1773245 := bbase (se 3 (by rfl) ⟨332483, by rfl⟩ : syracuseStep 1773245 = 664967) (by norm_num)
theorem B1576637 : Blo 1048611 1576637 := bbase (se 3 (by rfl) ⟨295619, by rfl⟩ : syracuseStep 1576637 = 591239) (by norm_num)
theorem B1183441 : Blo 1048611 1183441 := bbase (se 2 (by rfl) ⟨443790, by rfl⟩ : syracuseStep 1183441 = 887581) (by norm_num)
theorem B2658005 : Blo 1048611 2658005 := bbase (se 7 (by rfl) ⟨31148, by rfl⟩ : syracuseStep 2658005 = 62297) (by norm_num)
theorem B2363093 : Blo 1048611 2363093 := bbase (se 7 (by rfl) ⟨27692, by rfl⟩ : syracuseStep 2363093 = 55385) (by norm_num)
theorem B1576661 : Blo 1048611 1576661 := bbase (se 7 (by rfl) ⟨18476, by rfl⟩ : syracuseStep 1576661 = 36953) (by norm_num)
theorem B1576685 : Blo 1048611 1576685 := bbase (se 3 (by rfl) ⟨295628, by rfl⟩ : syracuseStep 1576685 = 591257) (by norm_num)
theorem B1183477 : Blo 1048611 1183477 := bbase (se 5 (by rfl) ⟨55475, by rfl⟩ : syracuseStep 1183477 = 110951) (by norm_num)
theorem B1576709 : Blo 1048611 1576709 := bbase (se 4 (by rfl) ⟨147816, by rfl⟩ : syracuseStep 1576709 = 295633) (by norm_num)
theorem B1183513 : Blo 1048611 1183513 := bbase (se 2 (by rfl) ⟨443817, by rfl⟩ : syracuseStep 1183513 = 887635) (by norm_num)
theorem B2363165 : Blo 1048611 2363165 := bbase (se 3 (by rfl) ⟨443093, by rfl⟩ : syracuseStep 2363165 = 886187) (by norm_num)
theorem B1576733 : Blo 1048611 1576733 := bbase (se 3 (by rfl) ⟨295637, by rfl⟩ : syracuseStep 1576733 = 591275) (by norm_num)
theorem B1576757 : Blo 1048611 1576757 := bbase (se 5 (by rfl) ⟨73910, by rfl⟩ : syracuseStep 1576757 = 147821) (by norm_num)
theorem B1773373 : Blo 1048611 1773373 := bbase (se 3 (by rfl) ⟨332507, by rfl⟩ : syracuseStep 1773373 = 665015) (by norm_num)
theorem B1183549 : Blo 1048611 1183549 := bbase (se 3 (by rfl) ⟨221915, by rfl⟩ : syracuseStep 1183549 = 443831) (by norm_num)
theorem B1576781 : Blo 1048611 1576781 := bbase (se 3 (by rfl) ⟨295646, by rfl⟩ : syracuseStep 1576781 = 591293) (by norm_num)
theorem B1183585 : Blo 1048611 1183585 := bbase (se 2 (by rfl) ⟨443844, by rfl⟩ : syracuseStep 1183585 = 887689) (by norm_num)
theorem B3542885 : Blo 1048611 3542885 := bbase (se 4 (by rfl) ⟨332145, by rfl⟩ : syracuseStep 3542885 = 664291) (by norm_num)
theorem B2363237 : Blo 1048611 2363237 := bbase (se 4 (by rfl) ⟨221553, by rfl⟩ : syracuseStep 2363237 = 443107) (by norm_num)
theorem B1576805 : Blo 1048611 1576805 := bbase (se 4 (by rfl) ⟨147825, by rfl⟩ : syracuseStep 1576805 = 295651) (by norm_num)
theorem B1576829 : Blo 1048611 1576829 := bbase (se 3 (by rfl) ⟨295655, by rfl⟩ : syracuseStep 1576829 = 591311) (by norm_num)
theorem B1183621 : Blo 1048611 1183621 := bbase (se 4 (by rfl) ⟨110964, by rfl⟩ : syracuseStep 1183621 = 221929) (by norm_num)
theorem B2658197 : Blo 1048611 2658197 := bbase (se 6 (by rfl) ⟨62301, by rfl⟩ : syracuseStep 2658197 = 124603) (by norm_num)
theorem B1773461 : Blo 1048611 1773461 := bbase (se 6 (by rfl) ⟨41565, by rfl⟩ : syracuseStep 1773461 = 83131) (by norm_num)
theorem B1576853 : Blo 1048611 1576853 := bbase (se 6 (by rfl) ⟨36957, by rfl⟩ : syracuseStep 1576853 = 73915) (by norm_num)
theorem B1183657 : Blo 1048611 1183657 := bbase (se 2 (by rfl) ⟨443871, by rfl⟩ : syracuseStep 1183657 = 887743) (by norm_num)
theorem B2363309 : Blo 1048611 2363309 := bbase (se 3 (by rfl) ⟨443120, by rfl⟩ : syracuseStep 2363309 = 886241) (by norm_num)
theorem B1576877 : Blo 1048611 1576877 := bbase (se 3 (by rfl) ⟨295664, by rfl⟩ : syracuseStep 1576877 = 591329) (by norm_num)
theorem B1576901 : Blo 1048611 1576901 := bbase (se 4 (by rfl) ⟨147834, by rfl⟩ : syracuseStep 1576901 = 295669) (by norm_num)
theorem B1183693 : Blo 1048611 1183693 := bbase (se 3 (by rfl) ⟨221942, by rfl⟩ : syracuseStep 1183693 = 443885) (by norm_num)
theorem B1576925 : Blo 1048611 1576925 := bbase (se 3 (by rfl) ⟨295673, by rfl⟩ : syracuseStep 1576925 = 591347) (by norm_num)
theorem B1183729 : Blo 1048611 1183729 := bbase (se 2 (by rfl) ⟨443898, by rfl⟩ : syracuseStep 1183729 = 887797) (by norm_num)
theorem B2363381 : Blo 1048611 2363381 := bbase (se 5 (by rfl) ⟨110783, by rfl⟩ : syracuseStep 2363381 = 221567) (by norm_num)
theorem B1576949 : Blo 1048611 1576949 := bbase (se 5 (by rfl) ⟨73919, by rfl⟩ : syracuseStep 1576949 = 147839) (by norm_num)
theorem B1576973 : Blo 1048611 1576973 := bbase (se 3 (by rfl) ⟨295682, by rfl⟩ : syracuseStep 1576973 = 591365) (by norm_num)
theorem B6066197 : Blo 1048611 6066197 := bbase (se 6 (by rfl) ⟨142176, by rfl⟩ : syracuseStep 6066197 = 284353) (by norm_num)
theorem B1773589 : Blo 1048611 1773589 := bbase (se 6 (by rfl) ⟨41568, by rfl⟩ : syracuseStep 1773589 = 83137) (by norm_num)
theorem B1183765 : Blo 1048611 1183765 := bbase (se 6 (by rfl) ⟨27744, by rfl⟩ : syracuseStep 1183765 = 55489) (by norm_num)
theorem B1576997 : Blo 1048611 1576997 := bbase (se 4 (by rfl) ⟨147843, by rfl⟩ : syracuseStep 1576997 = 295687) (by norm_num)
theorem B5050421 : Blo 1048611 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B1183801 : Blo 1048611 1183801 := bbase (se 2 (by rfl) ⟨443925, by rfl⟩ : syracuseStep 1183801 = 887851) (by norm_num)
theorem B2363453 : Blo 1048611 2363453 := bbase (se 3 (by rfl) ⟨443147, by rfl⟩ : syracuseStep 2363453 = 886295) (by norm_num)
theorem B1577021 : Blo 1048611 1577021 := bbase (se 3 (by rfl) ⟨295691, by rfl⟩ : syracuseStep 1577021 = 591383) (by norm_num)
theorem B1577045 : Blo 1048611 1577045 := bbase (se 8 (by rfl) ⟨9240, by rfl⟩ : syracuseStep 1577045 = 18481) (by norm_num)
theorem B1183837 : Blo 1048611 1183837 := bbase (se 3 (by rfl) ⟨221969, by rfl⟩ : syracuseStep 1183837 = 443939) (by norm_num)
theorem B1773677 : Blo 1048611 1773677 := bbase (se 3 (by rfl) ⟨332564, by rfl⟩ : syracuseStep 1773677 = 665129) (by norm_num)
theorem B1577069 : Blo 1048611 1577069 := bbase (se 3 (by rfl) ⟨295700, by rfl⟩ : syracuseStep 1577069 = 591401) (by norm_num)
theorem B1183873 : Blo 1048611 1183873 := bbase (se 2 (by rfl) ⟨443952, by rfl⟩ : syracuseStep 1183873 = 887905) (by norm_num)
theorem B2363525 : Blo 1048611 2363525 := bbase (se 4 (by rfl) ⟨221580, by rfl⟩ : syracuseStep 2363525 = 443161) (by norm_num)
theorem B1577093 : Blo 1048611 1577093 := bbase (se 4 (by rfl) ⟨147852, by rfl⟩ : syracuseStep 1577093 = 295705) (by norm_num)
theorem B1577117 : Blo 1048611 1577117 := bbase (se 3 (by rfl) ⟨295709, by rfl⟩ : syracuseStep 1577117 = 591419) (by norm_num)
theorem B1183909 : Blo 1048611 1183909 := bbase (se 4 (by rfl) ⟨110991, by rfl⟩ : syracuseStep 1183909 = 221983) (by norm_num)
theorem B2691245 : Blo 1048611 2691245 := bbase (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) (by norm_num)
theorem B1577141 : Blo 1048611 1577141 := bbase (se 5 (by rfl) ⟨73928, by rfl⟩ : syracuseStep 1577141 = 147857) (by norm_num)
theorem B1183945 : Blo 1048611 1183945 := bbase (se 2 (by rfl) ⟨443979, by rfl⟩ : syracuseStep 1183945 = 887959) (by norm_num)
theorem B2363597 : Blo 1048611 2363597 := bbase (se 3 (by rfl) ⟨443174, by rfl⟩ : syracuseStep 2363597 = 886349) (by norm_num)
theorem B1577165 : Blo 1048611 1577165 := bbase (se 3 (by rfl) ⟨295718, by rfl⟩ : syracuseStep 1577165 = 591437) (by norm_num)
theorem B1577189 : Blo 1048611 1577189 := bbase (se 4 (by rfl) ⟨147861, by rfl⟩ : syracuseStep 1577189 = 295723) (by norm_num)
theorem B2658541 : Blo 1048611 2658541 := bbase (se 3 (by rfl) ⟨498476, by rfl⟩ : syracuseStep 2658541 = 996953) (by norm_num)
theorem B1773805 : Blo 1048611 1773805 := bbase (se 3 (by rfl) ⟨332588, by rfl⟩ : syracuseStep 1773805 = 665177) (by norm_num)
theorem B1183981 : Blo 1048611 1183981 := bbase (se 3 (by rfl) ⟨221996, by rfl⟩ : syracuseStep 1183981 = 443993) (by norm_num)
theorem B1577213 : Blo 1048611 1577213 := bbase (se 3 (by rfl) ⟨295727, by rfl⟩ : syracuseStep 1577213 = 591455) (by norm_num)
theorem B1184017 : Blo 1048611 1184017 := bbase (se 2 (by rfl) ⟨444006, by rfl⟩ : syracuseStep 1184017 = 888013) (by norm_num)
theorem B7966997 : Blo 1048611 7966997 := bbase (se 6 (by rfl) ⟨186726, by rfl⟩ : syracuseStep 7966997 = 373453) (by norm_num)
theorem B5312789 : Blo 1048611 5312789 := bbase (se 6 (by rfl) ⟨124518, by rfl⟩ : syracuseStep 5312789 = 249037) (by norm_num)
theorem B3543317 : Blo 1048611 3543317 := bbase (se 6 (by rfl) ⟨83046, by rfl⟩ : syracuseStep 3543317 = 166093) (by norm_num)
theorem B2363669 : Blo 1048611 2363669 := bbase (se 6 (by rfl) ⟨55398, by rfl⟩ : syracuseStep 2363669 = 110797) (by norm_num)
theorem B1577237 : Blo 1048611 1577237 := bbase (se 6 (by rfl) ⟨36966, by rfl⟩ : syracuseStep 1577237 = 73933) (by norm_num)
theorem B1577261 : Blo 1048611 1577261 := bbase (se 3 (by rfl) ⟨295736, by rfl⟩ : syracuseStep 1577261 = 591473) (by norm_num)
theorem B1184053 : Blo 1048611 1184053 := bbase (se 5 (by rfl) ⟨55502, by rfl⟩ : syracuseStep 1184053 = 111005) (by norm_num)
theorem B1773893 : Blo 1048611 1773893 := bbase (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) (by norm_num)
theorem B1577285 : Blo 1048611 1577285 := bbase (se 4 (by rfl) ⟨147870, by rfl⟩ : syracuseStep 1577285 = 295741) (by norm_num)
theorem B1184089 : Blo 1048611 1184089 := bbase (se 2 (by rfl) ⟨444033, by rfl⟩ : syracuseStep 1184089 = 888067) (by norm_num)
theorem B2658653 : Blo 1048611 2658653 := bbase (se 3 (by rfl) ⟨498497, by rfl⟩ : syracuseStep 2658653 = 996995) (by norm_num)
theorem B2363741 : Blo 1048611 2363741 := bbase (se 3 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 2363741 = 886403) (by norm_num)
theorem B1577309 : Blo 1048611 1577309 := bbase (se 3 (by rfl) ⟨295745, by rfl⟩ : syracuseStep 1577309 = 591491) (by norm_num)
theorem B1577333 : Blo 1048611 1577333 := bbase (se 5 (by rfl) ⟨73937, by rfl⟩ : syracuseStep 1577333 = 147875) (by norm_num)
theorem B1184125 : Blo 1048611 1184125 := bbase (se 3 (by rfl) ⟨222023, by rfl⟩ : syracuseStep 1184125 = 444047) (by norm_num)
theorem B1577357 : Blo 1048611 1577357 := bbase (se 3 (by rfl) ⟨295754, by rfl⟩ : syracuseStep 1577357 = 591509) (by norm_num)
theorem B1184161 : Blo 1048611 1184161 := bbase (se 2 (by rfl) ⟨444060, by rfl⟩ : syracuseStep 1184161 = 888121) (by norm_num)
theorem B2363813 : Blo 1048611 2363813 := bbase (se 4 (by rfl) ⟨221607, by rfl⟩ : syracuseStep 2363813 = 443215) (by norm_num)
theorem B1577381 : Blo 1048611 1577381 := bbase (se 4 (by rfl) ⟨147879, by rfl⟩ : syracuseStep 1577381 = 295759) (by norm_num)
theorem B1577405 : Blo 1048611 1577405 := bbase (se 3 (by rfl) ⟨295763, by rfl⟩ : syracuseStep 1577405 = 591527) (by norm_num)
theorem B1774021 : Blo 1048611 1774021 := bbase (se 4 (by rfl) ⟨166314, by rfl⟩ : syracuseStep 1774021 = 332629) (by norm_num)
theorem B1577429 : Blo 1048611 1577429 := bbase (se 7 (by rfl) ⟨18485, by rfl⟩ : syracuseStep 1577429 = 36971) (by norm_num)
theorem B2429405 : Blo 1048611 2429405 := bbase (se 3 (by rfl) ⟨455513, by rfl⟩ : syracuseStep 2429405 = 911027) (by norm_num)
theorem B2363885 : Blo 1048611 2363885 := bbase (se 3 (by rfl) ⟨443228, by rfl⟩ : syracuseStep 2363885 = 886457) (by norm_num)
theorem B1577453 : Blo 1048611 1577453 := bbase (se 3 (by rfl) ⟨295772, by rfl⟩ : syracuseStep 1577453 = 591545) (by norm_num)
theorem B2560501 : Blo 1048611 2560501 := bbase (se 5 (by rfl) ⟨120023, by rfl⟩ : syracuseStep 2560501 = 240047) (by norm_num)
theorem B1577477 : Blo 1048611 1577477 := bbase (se 4 (by rfl) ⟨147888, by rfl⟩ : syracuseStep 1577477 = 295777) (by norm_num)
theorem B2658845 : Blo 1048611 2658845 := bbase (se 3 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 2658845 = 997067) (by norm_num)
theorem B1774109 : Blo 1048611 1774109 := bbase (se 3 (by rfl) ⟨332645, by rfl⟩ : syracuseStep 1774109 = 665291) (by norm_num)
theorem B1577501 : Blo 1048611 1577501 := bbase (se 3 (by rfl) ⟨295781, by rfl⟩ : syracuseStep 1577501 = 591563) (by norm_num)
theorem B2363957 : Blo 1048611 2363957 := bbase (se 5 (by rfl) ⟨110810, by rfl⟩ : syracuseStep 2363957 = 221621) (by norm_num)
theorem B1577525 : Blo 1048611 1577525 := bbase (se 5 (by rfl) ⟨73946, by rfl⟩ : syracuseStep 1577525 = 147893) (by norm_num)
theorem B2527805 : Blo 1048611 2527805 := bbase (se 3 (by rfl) ⟨473963, by rfl⟩ : syracuseStep 2527805 = 947927) (by norm_num)
theorem B1577549 : Blo 1048611 1577549 := bbase (se 3 (by rfl) ⟨295790, by rfl⟩ : syracuseStep 1577549 = 591581) (by norm_num)
theorem B1577573 : Blo 1048611 1577573 := bbase (se 4 (by rfl) ⟨147897, by rfl⟩ : syracuseStep 1577573 = 295795) (by norm_num)
theorem B2364029 : Blo 1048611 2364029 := bbase (se 3 (by rfl) ⟨443255, by rfl⟩ : syracuseStep 2364029 = 886511) (by norm_num)
theorem B1577597 : Blo 1048611 1577597 := bbase (se 3 (by rfl) ⟨295799, by rfl⟩ : syracuseStep 1577597 = 591599) (by norm_num)
theorem B2986645 : Blo 1048611 2986645 := bbase (se 6 (by rfl) ⟨69999, by rfl⟩ : syracuseStep 2986645 = 139999) (by norm_num)
theorem B1577621 : Blo 1048611 1577621 := bbase (se 6 (by rfl) ⟨36975, by rfl⟩ : syracuseStep 1577621 = 73951) (by norm_num)
theorem B1774237 : Blo 1048611 1774237 := bbase (se 3 (by rfl) ⟨332669, by rfl⟩ : syracuseStep 1774237 = 665339) (by norm_num)
theorem B1577645 : Blo 1048611 1577645 := bbase (se 3 (by rfl) ⟨295808, by rfl⟩ : syracuseStep 1577645 = 591617) (by norm_num)
theorem B3543749 : Blo 1048611 3543749 := bbase (se 4 (by rfl) ⟨332226, by rfl⟩ : syracuseStep 3543749 = 664453) (by norm_num)
theorem B2364101 : Blo 1048611 2364101 := bbase (se 4 (by rfl) ⟨221634, by rfl⟩ : syracuseStep 2364101 = 443269) (by norm_num)
theorem B1577669 : Blo 1048611 1577669 := bbase (se 4 (by rfl) ⟨147906, by rfl⟩ : syracuseStep 1577669 = 295813) (by norm_num)
theorem B1577693 : Blo 1048611 1577693 := bbase (se 3 (by rfl) ⟨295817, by rfl⟩ : syracuseStep 1577693 = 591635) (by norm_num)
theorem B1774325 : Blo 1048611 1774325 := bbase (se 5 (by rfl) ⟨83171, by rfl⟩ : syracuseStep 1774325 = 166343) (by norm_num)
theorem B1577717 : Blo 1048611 1577717 := bbase (se 5 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 1577717 = 147911) (by norm_num)
theorem B2364173 : Blo 1048611 2364173 := bbase (se 3 (by rfl) ⟨443282, by rfl⟩ : syracuseStep 2364173 = 886565) (by norm_num)
theorem B1577741 : Blo 1048611 1577741 := bbase (se 3 (by rfl) ⟨295826, by rfl⟩ : syracuseStep 1577741 = 591653) (by norm_num)
theorem B1348373 : Blo 1048611 1348373 := bbase (se 6 (by rfl) ⟨31602, by rfl⟩ : syracuseStep 1348373 = 63205) (by norm_num)
theorem B1577765 : Blo 1048611 1577765 := bbase (se 4 (by rfl) ⟨147915, by rfl⟩ : syracuseStep 1577765 = 295831) (by norm_num)
theorem B1577789 : Blo 1048611 1577789 := bbase (se 3 (by rfl) ⟨295835, by rfl⟩ : syracuseStep 1577789 = 591671) (by norm_num)
theorem B4494149 : Blo 1048611 4494149 := bbase (se 4 (by rfl) ⟨421326, by rfl⟩ : syracuseStep 4494149 = 842653) (by norm_num)
theorem B9835349 : Blo 1048611 9835349 := bbase (se 9 (by rfl) ⟨28814, by rfl⟩ : syracuseStep 9835349 = 57629) (by norm_num)
theorem B2364245 : Blo 1048611 2364245 := bbase (se 9 (by rfl) ⟨6926, by rfl⟩ : syracuseStep 2364245 = 13853) (by norm_num)
theorem B1577813 : Blo 1048611 1577813 := bbase (se 9 (by rfl) ⟨4622, by rfl⟩ : syracuseStep 1577813 = 9245) (by norm_num)
theorem B1577837 : Blo 1048611 1577837 := bbase (se 3 (by rfl) ⟨295844, by rfl⟩ : syracuseStep 1577837 = 591689) (by norm_num)
theorem B2659189 : Blo 1048611 2659189 := bbase (se 5 (by rfl) ⟨124649, by rfl⟩ : syracuseStep 2659189 = 249299) (by norm_num)
theorem B1774453 : Blo 1048611 1774453 := bbase (se 5 (by rfl) ⟨83177, by rfl⟩ : syracuseStep 1774453 = 166355) (by norm_num)
theorem B1577861 : Blo 1048611 1577861 := bbase (se 4 (by rfl) ⟨147924, by rfl⟩ : syracuseStep 1577861 = 295849) (by norm_num)
theorem B2364317 : Blo 1048611 2364317 := bbase (se 3 (by rfl) ⟨443309, by rfl⟩ : syracuseStep 2364317 = 886619) (by norm_num)
theorem B1577885 : Blo 1048611 1577885 := bbase (se 3 (by rfl) ⟨295853, by rfl⟩ : syracuseStep 1577885 = 591707) (by norm_num)
theorem B1577909 : Blo 1048611 1577909 := bbase (se 5 (by rfl) ⟨73964, by rfl⟩ : syracuseStep 1577909 = 147929) (by norm_num)
theorem B1774541 : Blo 1048611 1774541 := bbase (se 3 (by rfl) ⟨332726, by rfl⟩ : syracuseStep 1774541 = 665453) (by norm_num)
theorem B1577933 : Blo 1048611 1577933 := bbase (se 3 (by rfl) ⟨295862, by rfl⟩ : syracuseStep 1577933 = 591725) (by norm_num)
theorem B2659301 : Blo 1048611 2659301 := bbase (se 4 (by rfl) ⟨249309, by rfl⟩ : syracuseStep 2659301 = 498619) (by norm_num)
theorem B2364389 : Blo 1048611 2364389 := bbase (se 4 (by rfl) ⟨221661, by rfl⟩ : syracuseStep 2364389 = 443323) (by norm_num)
theorem B1577957 : Blo 1048611 1577957 := bbase (se 4 (by rfl) ⟨147933, by rfl⟩ : syracuseStep 1577957 = 295867) (by norm_num)
theorem B1577981 : Blo 1048611 1577981 := bbase (se 3 (by rfl) ⟨295871, by rfl⟩ : syracuseStep 1577981 = 591743) (by norm_num)
theorem B1578005 : Blo 1048611 1578005 := bbase (se 6 (by rfl) ⟨36984, by rfl⟩ : syracuseStep 1578005 = 73969) (by norm_num)
theorem B2364461 : Blo 1048611 2364461 := bbase (se 3 (by rfl) ⟨443336, by rfl⟩ : syracuseStep 2364461 = 886673) (by norm_num)
theorem B1578029 : Blo 1048611 1578029 := bbase (se 3 (by rfl) ⟨295880, by rfl⟩ : syracuseStep 1578029 = 591761) (by norm_num)
theorem B1578053 : Blo 1048611 1578053 := bbase (se 4 (by rfl) ⟨147942, by rfl⟩ : syracuseStep 1578053 = 295885) (by norm_num)
theorem B1774669 : Blo 1048611 1774669 := bbase (se 3 (by rfl) ⟨332750, by rfl⟩ : syracuseStep 1774669 = 665501) (by norm_num)
theorem B1578077 : Blo 1048611 1578077 := bbase (se 3 (by rfl) ⟨295889, by rfl⟩ : syracuseStep 1578077 = 591779) (by norm_num)
theorem B3544181 : Blo 1048611 3544181 := bbase (se 5 (by rfl) ⟨166133, by rfl⟩ : syracuseStep 3544181 = 332267) (by norm_num)
theorem B2364533 : Blo 1048611 2364533 := bbase (se 5 (by rfl) ⟨110837, by rfl⟩ : syracuseStep 2364533 = 221675) (by norm_num)
theorem B1578101 : Blo 1048611 1578101 := bbase (se 5 (by rfl) ⟨73973, by rfl⟩ : syracuseStep 1578101 = 147947) (by norm_num)
theorem B1578125 : Blo 1048611 1578125 := bbase (se 3 (by rfl) ⟨295898, by rfl⟩ : syracuseStep 1578125 = 591797) (by norm_num)
theorem B2659493 : Blo 1048611 2659493 := bbase (se 4 (by rfl) ⟨249327, by rfl⟩ : syracuseStep 2659493 = 498655) (by norm_num)
theorem B1774757 : Blo 1048611 1774757 := bbase (se 4 (by rfl) ⟨166383, by rfl⟩ : syracuseStep 1774757 = 332767) (by norm_num)
theorem B1578149 : Blo 1048611 1578149 := bbase (se 4 (by rfl) ⟨147951, by rfl⟩ : syracuseStep 1578149 = 295903) (by norm_num)
theorem B2364605 : Blo 1048611 2364605 := bbase (se 3 (by rfl) ⟨443363, by rfl⟩ : syracuseStep 2364605 = 886727) (by norm_num)
theorem B1578173 : Blo 1048611 1578173 := bbase (se 3 (by rfl) ⟨295907, by rfl⟩ : syracuseStep 1578173 = 591815) (by norm_num)
theorem B1578197 : Blo 1048611 1578197 := bbase (se 7 (by rfl) ⟨18494, by rfl⟩ : syracuseStep 1578197 = 36989) (by norm_num)
theorem B1578221 : Blo 1048611 1578221 := bbase (se 3 (by rfl) ⟨295916, by rfl⟩ : syracuseStep 1578221 = 591833) (by norm_num)
theorem B2364677 : Blo 1048611 2364677 := bbase (se 4 (by rfl) ⟨221688, by rfl⟩ : syracuseStep 2364677 = 443377) (by norm_num)
theorem B1578245 : Blo 1048611 1578245 := bbase (se 4 (by rfl) ⟨147960, by rfl⟩ : syracuseStep 1578245 = 295921) (by norm_num)
theorem B1578269 : Blo 1048611 1578269 := bbase (se 3 (by rfl) ⟨295925, by rfl⟩ : syracuseStep 1578269 = 591851) (by norm_num)
theorem B1774885 : Blo 1048611 1774885 := bbase (se 4 (by rfl) ⟨166395, by rfl⟩ : syracuseStep 1774885 = 332791) (by norm_num)
theorem B1578293 : Blo 1048611 1578293 := bbase (se 5 (by rfl) ⟨73982, by rfl⟩ : syracuseStep 1578293 = 147965) (by norm_num)
theorem B2364749 : Blo 1048611 2364749 := bbase (se 3 (by rfl) ⟨443390, by rfl⟩ : syracuseStep 2364749 = 886781) (by norm_num)
theorem B1578317 : Blo 1048611 1578317 := bbase (se 3 (by rfl) ⟨295934, by rfl⟩ : syracuseStep 1578317 = 591869) (by norm_num)
theorem B1578341 : Blo 1048611 1578341 := bbase (se 4 (by rfl) ⟨147969, by rfl⟩ : syracuseStep 1578341 = 295939) (by norm_num)
theorem B5051765 : Blo 1048611 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B1774973 : Blo 1048611 1774973 := bbase (se 3 (by rfl) ⟨332807, by rfl⟩ : syracuseStep 1774973 = 665615) (by norm_num)
theorem B1578365 : Blo 1048611 1578365 := bbase (se 3 (by rfl) ⟨295943, by rfl⟩ : syracuseStep 1578365 = 591887) (by norm_num)
theorem B2364821 : Blo 1048611 2364821 := bbase (se 6 (by rfl) ⟨55425, by rfl⟩ : syracuseStep 2364821 = 110851) (by norm_num)
theorem B1578389 : Blo 1048611 1578389 := bbase (se 6 (by rfl) ⟨36993, by rfl⟩ : syracuseStep 1578389 = 73987) (by norm_num)
theorem B1578413 : Blo 1048611 1578413 := bbase (se 3 (by rfl) ⟨295952, by rfl⟩ : syracuseStep 1578413 = 591905) (by norm_num)
theorem B1578437 : Blo 1048611 1578437 := bbase (se 4 (by rfl) ⟨147978, by rfl⟩ : syracuseStep 1578437 = 295957) (by norm_num)
theorem B2364893 : Blo 1048611 2364893 := bbase (se 3 (by rfl) ⟨443417, by rfl⟩ : syracuseStep 2364893 = 886835) (by norm_num)
theorem B1578461 : Blo 1048611 1578461 := bbase (se 3 (by rfl) ⟨295961, by rfl⟩ : syracuseStep 1578461 = 591923) (by norm_num)
theorem B1578485 : Blo 1048611 1578485 := bbase (se 5 (by rfl) ⟨73991, by rfl⟩ : syracuseStep 1578485 = 147983) (by norm_num)
theorem B2659837 : Blo 1048611 2659837 := bbase (se 3 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 2659837 = 997439) (by norm_num)
theorem B1775101 : Blo 1048611 1775101 := bbase (se 3 (by rfl) ⟨332831, by rfl⟩ : syracuseStep 1775101 = 665663) (by norm_num)
theorem B1578509 : Blo 1048611 1578509 := bbase (se 3 (by rfl) ⟨295970, by rfl⟩ : syracuseStep 1578509 = 591941) (by norm_num)
theorem B5314085 : Blo 1048611 5314085 := bbase (se 4 (by rfl) ⟨498195, by rfl⟩ : syracuseStep 5314085 = 996391) (by norm_num)
theorem B3544613 : Blo 1048611 3544613 := bbase (se 4 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 3544613 = 664615) (by norm_num)
theorem B2364965 : Blo 1048611 2364965 := bbase (se 4 (by rfl) ⟨221715, by rfl⟩ : syracuseStep 2364965 = 443431) (by norm_num)
theorem B1578533 : Blo 1048611 1578533 := bbase (se 4 (by rfl) ⟨147987, by rfl⟩ : syracuseStep 1578533 = 295975) (by norm_num)
theorem B1578557 : Blo 1048611 1578557 := bbase (se 3 (by rfl) ⟨295979, by rfl⟩ : syracuseStep 1578557 = 591959) (by norm_num)
theorem B1775189 : Blo 1048611 1775189 := bbase (se 8 (by rfl) ⟨10401, by rfl⟩ : syracuseStep 1775189 = 20803) (by norm_num)
theorem B1578581 : Blo 1048611 1578581 := bbase (se 8 (by rfl) ⟨9249, by rfl⟩ : syracuseStep 1578581 = 18499) (by norm_num)
theorem B2659949 : Blo 1048611 2659949 := bbase (se 3 (by rfl) ⟨498740, by rfl⟩ : syracuseStep 2659949 = 997481) (by norm_num)
theorem B2365037 : Blo 1048611 2365037 := bbase (se 3 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 2365037 = 886889) (by norm_num)
theorem B1578605 : Blo 1048611 1578605 := bbase (se 3 (by rfl) ⟨295988, by rfl⟩ : syracuseStep 1578605 = 591977) (by norm_num)
theorem B1578629 : Blo 1048611 1578629 := bbase (se 4 (by rfl) ⟨147996, by rfl⟩ : syracuseStep 1578629 = 295993) (by norm_num)
theorem B1578653 : Blo 1048611 1578653 := bbase (se 3 (by rfl) ⟨295997, by rfl⟩ : syracuseStep 1578653 = 591995) (by norm_num)
theorem B2365109 : Blo 1048611 2365109 := bbase (se 5 (by rfl) ⟨110864, by rfl⟩ : syracuseStep 2365109 = 221729) (by norm_num)
theorem B1578677 : Blo 1048611 1578677 := bbase (se 5 (by rfl) ⟨74000, by rfl⟩ : syracuseStep 1578677 = 148001) (by norm_num)
theorem B1119949 : Blo 1048611 1119949 := bbase (se 3 (by rfl) ⟨209990, by rfl⟩ : syracuseStep 1119949 = 419981) (by norm_num)
theorem B1578701 : Blo 1048611 1578701 := bbase (se 3 (by rfl) ⟨296006, by rfl⟩ : syracuseStep 1578701 = 592013) (by norm_num)
theorem B1775317 : Blo 1048611 1775317 := bbase (se 7 (by rfl) ⟨20804, by rfl⟩ : syracuseStep 1775317 = 41609) (by norm_num)
theorem B1578725 : Blo 1048611 1578725 := bbase (se 4 (by rfl) ⟨148005, by rfl⟩ : syracuseStep 1578725 = 296011) (by norm_num)
theorem B1349357 : Blo 1048611 1349357 := bbase (se 3 (by rfl) ⟨253004, by rfl⟩ : syracuseStep 1349357 = 506009) (by norm_num)
theorem B2365181 : Blo 1048611 2365181 := bbase (se 3 (by rfl) ⟨443471, by rfl⟩ : syracuseStep 2365181 = 886943) (by norm_num)
theorem B1578749 : Blo 1048611 1578749 := bbase (se 3 (by rfl) ⟨296015, by rfl⟩ : syracuseStep 1578749 = 592031) (by norm_num)
theorem B2692885 : Blo 1048611 2692885 := bbase (se 6 (by rfl) ⟨63114, by rfl⟩ : syracuseStep 2692885 = 126229) (by norm_num)
theorem B1578773 : Blo 1048611 1578773 := bbase (se 6 (by rfl) ⟨37002, by rfl⟩ : syracuseStep 1578773 = 74005) (by norm_num)
theorem B2660141 : Blo 1048611 2660141 := bbase (se 3 (by rfl) ⟨498776, by rfl⟩ : syracuseStep 2660141 = 997553) (by norm_num)
theorem B1775405 : Blo 1048611 1775405 := bbase (se 3 (by rfl) ⟨332888, by rfl⟩ : syracuseStep 1775405 = 665777) (by norm_num)
theorem B1578797 : Blo 1048611 1578797 := bbase (se 3 (by rfl) ⟨296024, by rfl⟩ : syracuseStep 1578797 = 592049) (by norm_num)
theorem B5674805 : Blo 1048611 5674805 := bbase (se 5 (by rfl) ⟨266006, by rfl⟩ : syracuseStep 5674805 = 532013) (by norm_num)
theorem B1120069 : Blo 1048611 1120069 := bbase (se 4 (by rfl) ⟨105006, by rfl⟩ : syracuseStep 1120069 = 210013) (by norm_num)
theorem B2365253 : Blo 1048611 2365253 := bbase (se 4 (by rfl) ⟨221742, by rfl⟩ : syracuseStep 2365253 = 443485) (by norm_num)
theorem B1578821 : Blo 1048611 1578821 := bbase (se 4 (by rfl) ⟨148014, by rfl⟩ : syracuseStep 1578821 = 296029) (by norm_num)
theorem B1578845 : Blo 1048611 1578845 := bbase (se 3 (by rfl) ⟨296033, by rfl⟩ : syracuseStep 1578845 = 592067) (by norm_num)
theorem B1578869 : Blo 1048611 1578869 := bbase (se 5 (by rfl) ⟨74009, by rfl⟩ : syracuseStep 1578869 = 148019) (by norm_num)
theorem B2365325 : Blo 1048611 2365325 := bbase (se 3 (by rfl) ⟨443498, by rfl⟩ : syracuseStep 2365325 = 886997) (by norm_num)
theorem B1578893 : Blo 1048611 1578893 := bbase (se 3 (by rfl) ⟨296042, by rfl⟩ : syracuseStep 1578893 = 592085) (by norm_num)
theorem B1578917 : Blo 1048611 1578917 := bbase (se 4 (by rfl) ⟨148023, by rfl⟩ : syracuseStep 1578917 = 296047) (by norm_num)
theorem B1775533 : Blo 1048611 1775533 := bbase (se 3 (by rfl) ⟨332912, by rfl⟩ : syracuseStep 1775533 = 665825) (by norm_num)
theorem B3545045 : Blo 1048611 3545045 := bbase (se 7 (by rfl) ⟨41543, by rfl⟩ : syracuseStep 3545045 = 83087) (by norm_num)
theorem B2365397 : Blo 1048611 2365397 := bbase (se 7 (by rfl) ⟨27719, by rfl⟩ : syracuseStep 2365397 = 55439) (by norm_num)
theorem B1775621 : Blo 1048611 1775621 := bbase (se 4 (by rfl) ⟨166464, by rfl⟩ : syracuseStep 1775621 = 332929) (by norm_num)
theorem B2365469 : Blo 1048611 2365469 := bbase (se 3 (by rfl) ⟨443525, by rfl⟩ : syracuseStep 2365469 = 887051) (by norm_num)
theorem B2922533 : Blo 1048611 2922533 := bbase (se 4 (by rfl) ⟨273987, by rfl⟩ : syracuseStep 2922533 = 547975) (by norm_num)
theorem B1120321 : Blo 1048611 1120321 := bbase (se 2 (by rfl) ⟨420120, by rfl⟩ : syracuseStep 1120321 = 840241) (by norm_num)
theorem B1120325 : Blo 1048611 1120325 := bbase (se 4 (by rfl) ⟨105030, by rfl⟩ : syracuseStep 1120325 = 210061) (by norm_num)
theorem B2365541 : Blo 1048611 2365541 := bbase (se 4 (by rfl) ⟨221769, by rfl⟩ : syracuseStep 2365541 = 443539) (by norm_num)
theorem B2660485 : Blo 1048611 2660485 := bbase (se 4 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 2660485 = 498841) (by norm_num)
theorem B1775749 : Blo 1048611 1775749 := bbase (se 4 (by rfl) ⟨166476, by rfl⟩ : syracuseStep 1775749 = 332953) (by norm_num)
theorem B2365613 : Blo 1048611 2365613 := bbase (se 3 (by rfl) ⟨443552, by rfl⟩ : syracuseStep 2365613 = 887105) (by norm_num)
theorem B1775837 : Blo 1048611 1775837 := bbase (se 3 (by rfl) ⟨332969, by rfl⟩ : syracuseStep 1775837 = 665939) (by norm_num)
theorem B2660597 : Blo 1048611 2660597 := bbase (se 5 (by rfl) ⟨124715, by rfl⟩ : syracuseStep 2660597 = 249431) (by norm_num)
theorem B2365685 : Blo 1048611 2365685 := bbase (se 5 (by rfl) ⟨110891, by rfl⟩ : syracuseStep 2365685 = 221783) (by norm_num)
theorem B2365757 : Blo 1048611 2365757 := bbase (se 3 (by rfl) ⟨443579, by rfl⟩ : syracuseStep 2365757 = 887159) (by norm_num)
theorem B1775965 : Blo 1048611 1775965 := bbase (se 3 (by rfl) ⟨332993, by rfl⟩ : syracuseStep 1775965 = 665987) (by norm_num)
theorem B1513837 : Blo 1048611 1513837 := bbase (se 3 (by rfl) ⟨283844, by rfl⟩ : syracuseStep 1513837 = 567689) (by norm_num)
theorem B3545477 : Blo 1048611 3545477 := bbase (se 4 (by rfl) ⟨332388, by rfl⟩ : syracuseStep 3545477 = 664777) (by norm_num)
theorem B2365829 : Blo 1048611 2365829 := bbase (se 4 (by rfl) ⟨221796, by rfl⟩ : syracuseStep 2365829 = 443593) (by norm_num)
theorem B2660789 : Blo 1048611 2660789 := bbase (se 5 (by rfl) ⟨124724, by rfl⟩ : syracuseStep 2660789 = 249449) (by norm_num)
theorem B1776053 : Blo 1048611 1776053 := bbase (se 5 (by rfl) ⟨83252, by rfl⟩ : syracuseStep 1776053 = 166505) (by norm_num)
theorem B2365901 : Blo 1048611 2365901 := bbase (se 3 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 2365901 = 887213) (by norm_num)
theorem B2365973 : Blo 1048611 2365973 := bbase (se 6 (by rfl) ⟨55452, by rfl⟩ : syracuseStep 2365973 = 110905) (by norm_num)
theorem B4495925 : Blo 1048611 4495925 := bbase (se 5 (by rfl) ⟨210746, by rfl⟩ : syracuseStep 4495925 = 421493) (by norm_num)
theorem B1776181 : Blo 1048611 1776181 := bbase (se 5 (by rfl) ⟨83258, by rfl⟩ : syracuseStep 1776181 = 166517) (by norm_num)
theorem B2366045 : Blo 1048611 2366045 := bbase (se 3 (by rfl) ⟨443633, by rfl⟩ : syracuseStep 2366045 = 887267) (by norm_num)
theorem B1120889 : Blo 1048611 1120889 := bbase (se 2 (by rfl) ⟨420333, by rfl⟩ : syracuseStep 1120889 = 840667) (by norm_num)
theorem B1776269 : Blo 1048611 1776269 := bbase (se 3 (by rfl) ⟨333050, by rfl⟩ : syracuseStep 1776269 = 666101) (by norm_num)
theorem B2366117 : Blo 1048611 2366117 := bbase (se 4 (by rfl) ⟨221823, by rfl⟩ : syracuseStep 2366117 = 443647) (by norm_num)
theorem B2366189 : Blo 1048611 2366189 := bbase (se 3 (by rfl) ⟨443660, by rfl⟩ : syracuseStep 2366189 = 887321) (by norm_num)
theorem B2661133 : Blo 1048611 2661133 := bbase (se 3 (by rfl) ⟨498962, by rfl⟩ : syracuseStep 2661133 = 997925) (by norm_num)
theorem B1121077 : Blo 1048611 1121077 := bbase (se 5 (by rfl) ⟨52550, by rfl⟩ : syracuseStep 1121077 = 105101) (by norm_num)
theorem B5315381 : Blo 1048611 5315381 := bbase (se 5 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 5315381 = 498317) (by norm_num)
theorem B3545909 : Blo 1048611 3545909 := bbase (se 5 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 3545909 = 332429) (by norm_num)
theorem B2366261 : Blo 1048611 2366261 := bbase (se 5 (by rfl) ⟨110918, by rfl⟩ : syracuseStep 2366261 = 221837) (by norm_num)
theorem B2661245 : Blo 1048611 2661245 := bbase (se 3 (by rfl) ⟨498983, by rfl⟩ : syracuseStep 2661245 = 997967) (by norm_num)
theorem B2366333 : Blo 1048611 2366333 := bbase (se 3 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 2366333 = 887375) (by norm_num)
theorem B2399141 : Blo 1048611 2399141 := bbase (se 4 (by rfl) ⟨224919, by rfl⟩ : syracuseStep 2399141 = 449839) (by norm_num)
theorem B2366405 : Blo 1048611 2366405 := bbase (se 4 (by rfl) ⟨221850, by rfl⟩ : syracuseStep 2366405 = 443701) (by norm_num)
theorem B2366477 : Blo 1048611 2366477 := bbase (se 3 (by rfl) ⟨443714, by rfl⟩ : syracuseStep 2366477 = 887429) (by norm_num)
theorem B2661437 : Blo 1048611 2661437 := bbase (se 3 (by rfl) ⟨499019, by rfl⟩ : syracuseStep 2661437 = 998039) (by norm_num)
theorem B2366549 : Blo 1048611 2366549 := bbase (se 8 (by rfl) ⟨13866, by rfl⟩ : syracuseStep 2366549 = 27733) (by norm_num)
theorem B2366621 : Blo 1048611 2366621 := bbase (se 3 (by rfl) ⟨443741, by rfl⟩ : syracuseStep 2366621 = 887483) (by norm_num)
theorem B3546341 : Blo 1048611 3546341 := bbase (se 4 (by rfl) ⟨332469, by rfl⟩ : syracuseStep 3546341 = 664939) (by norm_num)
theorem B2366693 : Blo 1048611 2366693 := bbase (se 4 (by rfl) ⟨221877, by rfl⟩ : syracuseStep 2366693 = 443755) (by norm_num)
theorem B2366765 : Blo 1048611 2366765 := bbase (se 3 (by rfl) ⟨443768, by rfl⟩ : syracuseStep 2366765 = 887537) (by norm_num)
theorem B5053765 : Blo 1048611 5053765 := bbase (se 4 (by rfl) ⟨473790, by rfl⟩ : syracuseStep 5053765 = 947581) (by norm_num)
theorem B2366837 : Blo 1048611 2366837 := bbase (se 5 (by rfl) ⟨110945, by rfl⟩ : syracuseStep 2366837 = 221891) (by norm_num)
theorem B2661781 : Blo 1048611 2661781 := bbase (se 6 (by rfl) ⟨62385, by rfl⟩ : syracuseStep 2661781 = 124771) (by norm_num)
theorem B2989493 : Blo 1048611 2989493 := bbase (se 5 (by rfl) ⟨140132, by rfl⟩ : syracuseStep 2989493 = 280265) (by norm_num)
theorem B2366909 : Blo 1048611 2366909 := bbase (se 3 (by rfl) ⟨443795, by rfl⟩ : syracuseStep 2366909 = 887591) (by norm_num)
theorem B2661893 : Blo 1048611 2661893 := bbase (se 4 (by rfl) ⟨249552, by rfl⟩ : syracuseStep 2661893 = 499105) (by norm_num)
theorem B2366981 : Blo 1048611 2366981 := bbase (se 4 (by rfl) ⟨221904, by rfl⟩ : syracuseStep 2366981 = 443809) (by norm_num)
theorem B2367053 : Blo 1048611 2367053 := bbase (se 3 (by rfl) ⟨443822, by rfl⟩ : syracuseStep 2367053 = 887645) (by norm_num)
theorem B1121897 : Blo 1048611 1121897 := bbase (se 2 (by rfl) ⟨420711, by rfl⟩ : syracuseStep 1121897 = 841423) (by norm_num)
theorem B3546773 : Blo 1048611 3546773 := bbase (se 6 (by rfl) ⟨83127, by rfl⟩ : syracuseStep 3546773 = 166255) (by norm_num)
theorem B2367125 : Blo 1048611 2367125 := bbase (se 6 (by rfl) ⟨55479, by rfl⟩ : syracuseStep 2367125 = 110959) (by norm_num)
theorem B2662085 : Blo 1048611 2662085 := bbase (se 4 (by rfl) ⟨249570, by rfl⟩ : syracuseStep 2662085 = 499141) (by norm_num)
theorem B2367197 : Blo 1048611 2367197 := bbase (se 3 (by rfl) ⟨443849, by rfl⟩ : syracuseStep 2367197 = 887699) (by norm_num)
theorem B2367269 : Blo 1048611 2367269 := bbase (se 4 (by rfl) ⟨221931, by rfl⟩ : syracuseStep 2367269 = 443863) (by norm_num)
theorem B2367341 : Blo 1048611 2367341 := bbase (se 3 (by rfl) ⟨443876, by rfl⟩ : syracuseStep 2367341 = 887753) (by norm_num)
theorem B2367413 : Blo 1048611 2367413 := bbase (se 5 (by rfl) ⟨110972, by rfl⟩ : syracuseStep 2367413 = 221945) (by norm_num)
theorem B2367485 : Blo 1048611 2367485 := bbase (se 3 (by rfl) ⟨443903, by rfl⟩ : syracuseStep 2367485 = 887807) (by norm_num)
theorem B2662429 : Blo 1048611 2662429 := bbase (se 3 (by rfl) ⟨499205, by rfl⟩ : syracuseStep 2662429 = 998411) (by norm_num)
theorem B1122341 : Blo 1048611 1122341 := bbase (se 4 (by rfl) ⟨105219, by rfl⟩ : syracuseStep 1122341 = 210439) (by norm_num)
theorem B5316677 : Blo 1048611 5316677 := bbase (se 4 (by rfl) ⟨498438, by rfl⟩ : syracuseStep 5316677 = 996877) (by norm_num)
theorem B3547205 : Blo 1048611 3547205 := bbase (se 4 (by rfl) ⟨332550, by rfl⟩ : syracuseStep 3547205 = 665101) (by norm_num)
theorem B2367557 : Blo 1048611 2367557 := bbase (se 4 (by rfl) ⟨221958, by rfl⟩ : syracuseStep 2367557 = 443917) (by norm_num)
theorem B2662541 : Blo 1048611 2662541 := bbase (se 3 (by rfl) ⟨499226, by rfl⟩ : syracuseStep 2662541 = 998453) (by norm_num)
theorem B2367629 : Blo 1048611 2367629 := bbase (se 3 (by rfl) ⟨443930, by rfl⟩ : syracuseStep 2367629 = 887861) (by norm_num)
theorem B2695349 : Blo 1048611 2695349 := bbase (se 5 (by rfl) ⟨126344, by rfl⟩ : syracuseStep 2695349 = 252689) (by norm_num)
theorem B6725845 : Blo 1048611 6725845 := bbase (se 7 (by rfl) ⟨78818, by rfl⟩ : syracuseStep 6725845 = 157637) (by norm_num)
theorem B2367701 : Blo 1048611 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B1417501 : Blo 1048611 1417501 := bbase (se 3 (by rfl) ⟨265781, by rfl⟩ : syracuseStep 1417501 = 531563) (by norm_num)
theorem B1122589 : Blo 1048611 1122589 := bbase (se 3 (by rfl) ⟨210485, by rfl⟩ : syracuseStep 1122589 = 420971) (by norm_num)
theorem B2367773 : Blo 1048611 2367773 := bbase (se 3 (by rfl) ⟨443957, by rfl⟩ : syracuseStep 2367773 = 887915) (by norm_num)
theorem B2662733 : Blo 1048611 2662733 := bbase (se 3 (by rfl) ⟨499262, by rfl⟩ : syracuseStep 2662733 = 998525) (by norm_num)
theorem B2367845 : Blo 1048611 2367845 := bbase (se 4 (by rfl) ⟨221985, by rfl⟩ : syracuseStep 2367845 = 443971) (by norm_num)
theorem B2367917 : Blo 1048611 2367917 := bbase (se 3 (by rfl) ⟨443984, by rfl⟩ : syracuseStep 2367917 = 887969) (by norm_num)
theorem B1679821 : Blo 1048611 1679821 := bbase (se 3 (by rfl) ⟨314966, by rfl⟩ : syracuseStep 1679821 = 629933) (by norm_num)
theorem B1515989 : Blo 1048611 1515989 := bbase (se 7 (by rfl) ⟨17765, by rfl⟩ : syracuseStep 1515989 = 35531) (by norm_num)
theorem B3547637 : Blo 1048611 3547637 := bbase (se 5 (by rfl) ⟨166295, by rfl⟩ : syracuseStep 3547637 = 332591) (by norm_num)
theorem B2367989 : Blo 1048611 2367989 := bbase (se 5 (by rfl) ⟨110999, by rfl⟩ : syracuseStep 2367989 = 221999) (by norm_num)
theorem B2368061 : Blo 1048611 2368061 := bbase (se 3 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 2368061 = 888023) (by norm_num)
theorem B2990677 : Blo 1048611 2990677 := bbase (se 8 (by rfl) ⟨17523, by rfl⟩ : syracuseStep 2990677 = 35047) (by norm_num)
theorem B1417837 : Blo 1048611 1417837 := bbase (se 3 (by rfl) ⟨265844, by rfl⟩ : syracuseStep 1417837 = 531689) (by norm_num)
theorem B2368133 : Blo 1048611 2368133 := bbase (se 4 (by rfl) ⟨222012, by rfl⟩ : syracuseStep 2368133 = 444025) (by norm_num)
theorem B2663077 : Blo 1048611 2663077 := bbase (se 4 (by rfl) ⟨249663, by rfl⟩ : syracuseStep 2663077 = 499327) (by norm_num)
theorem B1123021 : Blo 1048611 1123021 := bbase (se 3 (by rfl) ⟨210566, by rfl⟩ : syracuseStep 1123021 = 421133) (by norm_num)
theorem B2368205 : Blo 1048611 2368205 := bbase (se 3 (by rfl) ⟨444038, by rfl⟩ : syracuseStep 2368205 = 888077) (by norm_num)
theorem B30646997 : Blo 1048611 30646997 := bbase (se 7 (by rfl) ⟨359144, by rfl⟩ : syracuseStep 30646997 = 718289) (by norm_num)
theorem B2990837 : Blo 1048611 2990837 := bbase (se 5 (by rfl) ⟨140195, by rfl⟩ : syracuseStep 2990837 = 280391) (by norm_num)
theorem B1123093 : Blo 1048611 1123093 := bbase (se 6 (by rfl) ⟨26322, by rfl⟩ : syracuseStep 1123093 = 52645) (by norm_num)
theorem B2663189 : Blo 1048611 2663189 := bbase (se 6 (by rfl) ⟨62418, by rfl⟩ : syracuseStep 2663189 = 124837) (by norm_num)
theorem B2368277 : Blo 1048611 2368277 := bbase (se 6 (by rfl) ⟨55506, by rfl⟩ : syracuseStep 2368277 = 111013) (by norm_num)
theorem B2368349 : Blo 1048611 2368349 := bbase (se 3 (by rfl) ⟨444065, by rfl⟩ : syracuseStep 2368349 = 888131) (by norm_num)
theorem B1680277 : Blo 1048611 1680277 := bbase (se 6 (by rfl) ⟨39381, by rfl⟩ : syracuseStep 1680277 = 78763) (by norm_num)
theorem B3548069 : Blo 1048611 3548069 := bbase (se 4 (by rfl) ⟨332631, by rfl⟩ : syracuseStep 3548069 = 665263) (by norm_num)
theorem B10101685 : Blo 1048611 10101685 := bbase (se 5 (by rfl) ⟨473516, by rfl⟩ : syracuseStep 10101685 = 947033) (by norm_num)
theorem B2663381 : Blo 1048611 2663381 := bbase (se 7 (by rfl) ⟨31211, by rfl⟩ : syracuseStep 2663381 = 62423) (by norm_num)
theorem B2991077 : Blo 1048611 2991077 := bbase (se 4 (by rfl) ⟨280413, by rfl⟩ : syracuseStep 2991077 = 560827) (by norm_num)
theorem B1123465 : Blo 1048611 1123465 := bbase (se 2 (by rfl) ⟨421299, by rfl⟩ : syracuseStep 1123465 = 842599) (by norm_num)
theorem B2991269 : Blo 1048611 2991269 := bbase (se 4 (by rfl) ⟨280431, by rfl⟩ : syracuseStep 2991269 = 560863) (by norm_num)
theorem B2663725 : Blo 1048611 2663725 := bbase (se 3 (by rfl) ⟨499448, by rfl⟩ : syracuseStep 2663725 = 998897) (by norm_num)
theorem B5317973 : Blo 1048611 5317973 := bbase (se 12 (by rfl) ⟨1947, by rfl⟩ : syracuseStep 5317973 = 3895) (by norm_num)
theorem B3548501 : Blo 1048611 3548501 := bbase (se 12 (by rfl) ⟨1299, by rfl⟩ : syracuseStep 3548501 = 2599) (by norm_num)
theorem B2663837 : Blo 1048611 2663837 := bbase (se 3 (by rfl) ⟨499469, by rfl⟩ : syracuseStep 2663837 = 998939) (by norm_num)
theorem B1123841 : Blo 1048611 1123841 := bbase (se 2 (by rfl) ⟨421440, by rfl⟩ : syracuseStep 1123841 = 842881) (by norm_num)
theorem B1680949 : Blo 1048611 1680949 := bbase (se 5 (by rfl) ⟨78794, by rfl⟩ : syracuseStep 1680949 = 157589) (by norm_num)
theorem B1123913 : Blo 1048611 1123913 := bbase (se 2 (by rfl) ⟨421467, by rfl⟩ : syracuseStep 1123913 = 842935) (by norm_num)
theorem B2664029 : Blo 1048611 2664029 := bbase (se 3 (by rfl) ⟨499505, by rfl⟩ : syracuseStep 2664029 = 999011) (by norm_num)
theorem B7677589 : Blo 1048611 7677589 := bbase (se 6 (by rfl) ⟨179943, by rfl⟩ : syracuseStep 7677589 = 359887) (by norm_num)
theorem B3548933 : Blo 1048611 3548933 := bbase (se 4 (by rfl) ⟨332712, by rfl⟩ : syracuseStep 3548933 = 665425) (by norm_num)
theorem B2664373 : Blo 1048611 2664373 := bbase (se 5 (by rfl) ⟨124892, by rfl⟩ : syracuseStep 2664373 = 249785) (by norm_num)
theorem B1419221 : Blo 1048611 1419221 := bbase (se 7 (by rfl) ⟨16631, by rfl⟩ : syracuseStep 1419221 = 33263) (by norm_num)
theorem B1681373 : Blo 1048611 1681373 := bbase (se 3 (by rfl) ⟨315257, by rfl⟩ : syracuseStep 1681373 = 630515) (by norm_num)
theorem B2992261 : Blo 1048611 2992261 := bbase (se 4 (by rfl) ⟨280524, by rfl⟩ : syracuseStep 2992261 = 561049) (by norm_num)
theorem B3549365 : Blo 1048611 3549365 := bbase (se 5 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 3549365 = 332753) (by norm_num)
theorem B3188965 : Blo 1048611 3188965 := bbase (se 4 (by rfl) ⟨298965, by rfl⟩ : syracuseStep 3188965 = 597931) (by norm_num)
theorem B1681661 : Blo 1048611 1681661 := bbase (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) (by norm_num)
theorem B3189125 : Blo 1048611 3189125 := bbase (se 4 (by rfl) ⟨298980, by rfl⟩ : syracuseStep 3189125 = 597961) (by norm_num)
theorem B5319269 : Blo 1048611 5319269 := bbase (se 4 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 5319269 = 997363) (by norm_num)
theorem B3549797 : Blo 1048611 3549797 := bbase (se 4 (by rfl) ⟨332793, by rfl⟩ : syracuseStep 3549797 = 665587) (by norm_num)
theorem B3550229 : Blo 1048611 3550229 := bbase (se 6 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 3550229 = 166417) (by norm_num)
theorem B1682461 : Blo 1048611 1682461 := bbase (se 3 (by rfl) ⟨315461, by rfl⟩ : syracuseStep 1682461 = 630923) (by norm_num)
theorem B5680277 : Blo 1048611 5680277 := bbase (se 6 (by rfl) ⟨133131, by rfl⟩ : syracuseStep 5680277 = 266263) (by norm_num)
theorem B2993365 : Blo 1048611 2993365 := bbase (se 7 (by rfl) ⟨35078, by rfl⟩ : syracuseStep 2993365 = 70157) (by norm_num)
theorem B1420573 : Blo 1048611 1420573 := bbase (se 3 (by rfl) ⟨266357, by rfl⟩ : syracuseStep 1420573 = 532715) (by norm_num)
theorem B5680469 : Blo 1048611 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B5975477 : Blo 1048611 5975477 := bbase (se 5 (by rfl) ⟨280100, by rfl⟩ : syracuseStep 5975477 = 560201) (by norm_num)
theorem B2239933 : Blo 1048611 2239933 := bbase (se 3 (by rfl) ⟨419987, by rfl⟩ : syracuseStep 2239933 = 839975) (by norm_num)
theorem B3550661 : Blo 1048611 3550661 := bbase (se 4 (by rfl) ⟨332874, by rfl⟩ : syracuseStep 3550661 = 665749) (by norm_num)
theorem B1683013 : Blo 1048611 1683013 := bbase (se 4 (by rfl) ⟨157782, by rfl⟩ : syracuseStep 1683013 = 315565) (by norm_num)
theorem B1617509 : Blo 1048611 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B12136085 : Blo 1048611 12136085 := bbase (se 6 (by rfl) ⟨284439, by rfl⟩ : syracuseStep 12136085 = 568879) (by norm_num)
theorem B10104533 : Blo 1048611 10104533 := bbase (se 7 (by rfl) ⟨118412, by rfl⟩ : syracuseStep 10104533 = 236825) (by norm_num)
theorem B1421069 : Blo 1048611 1421069 := bbase (se 3 (by rfl) ⟨266450, by rfl⟩ : syracuseStep 1421069 = 532901) (by norm_num)
theorem B1683269 : Blo 1048611 1683269 := bbase (se 4 (by rfl) ⟨157806, by rfl⟩ : syracuseStep 1683269 = 315613) (by norm_num)
theorem B7974773 : Blo 1048611 7974773 := bbase (se 5 (by rfl) ⟨373817, by rfl⟩ : syracuseStep 7974773 = 747635) (by norm_num)
theorem B5320565 : Blo 1048611 5320565 := bbase (se 5 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 5320565 = 498803) (by norm_num)
theorem B3551093 : Blo 1048611 3551093 := bbase (se 5 (by rfl) ⟨166457, by rfl⟩ : syracuseStep 3551093 = 332915) (by norm_num)
theorem B5386261 : Blo 1048611 5386261 := bbase (se 6 (by rfl) ⟨126240, by rfl⟩ : syracuseStep 5386261 = 252481) (by norm_num)
theorem B1421501 : Blo 1048611 1421501 := bbase (se 3 (by rfl) ⟨266531, by rfl⟩ : syracuseStep 1421501 = 533063) (by norm_num)
theorem B2699453 : Blo 1048611 2699453 := bbase (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) (by norm_num)
theorem B3551525 : Blo 1048611 3551525 := bbase (se 4 (by rfl) ⟨332955, by rfl⟩ : syracuseStep 3551525 = 665911) (by norm_num)
theorem B2240821 : Blo 1048611 2240821 := bbase (se 5 (by rfl) ⟨105038, by rfl⟩ : syracuseStep 2240821 = 210077) (by norm_num)
theorem B2240941 : Blo 1048611 2240941 := bbase (se 3 (by rfl) ⟨420176, by rfl⟩ : syracuseStep 2240941 = 840353) (by norm_num)
theorem B2699741 : Blo 1048611 2699741 := bbase (se 3 (by rfl) ⟨506201, by rfl⟩ : syracuseStep 2699741 = 1012403) (by norm_num)
theorem B1683973 : Blo 1048611 1683973 := bbase (se 4 (by rfl) ⟨157872, by rfl⟩ : syracuseStep 1683973 = 315745) (by norm_num)
theorem B7582261 : Blo 1048611 7582261 := bbase (se 5 (by rfl) ⟨355418, by rfl⟩ : syracuseStep 7582261 = 710837) (by norm_num)
theorem B17052245 : Blo 1048611 17052245 := bbase (se 8 (by rfl) ⟨99915, by rfl⟩ : syracuseStep 17052245 = 199831) (by norm_num)
theorem B2241197 : Blo 1048611 2241197 := bbase (se 3 (by rfl) ⟨420224, by rfl⟩ : syracuseStep 2241197 = 840449) (by norm_num)
theorem B2994869 : Blo 1048611 2994869 := bbase (se 5 (by rfl) ⟨140384, by rfl⟩ : syracuseStep 2994869 = 280769) (by norm_num)
theorem B3551957 : Blo 1048611 3551957 := bbase (se 7 (by rfl) ⟨41624, by rfl⟩ : syracuseStep 3551957 = 83249) (by norm_num)
theorem B2274149 : Blo 1048611 2274149 := bbase (se 4 (by rfl) ⟨213201, by rfl⟩ : syracuseStep 2274149 = 426403) (by norm_num)
theorem B1684397 : Blo 1048611 1684397 := bbase (se 3 (by rfl) ⟨315824, by rfl⟩ : syracuseStep 1684397 = 631649) (by norm_num)
theorem B5321861 : Blo 1048611 5321861 := bbase (se 4 (by rfl) ⟨498924, by rfl⟩ : syracuseStep 5321861 = 997849) (by norm_num)
theorem B3552389 : Blo 1048611 3552389 := bbase (se 4 (by rfl) ⟨333036, by rfl⟩ : syracuseStep 3552389 = 666073) (by norm_num)
theorem B1684685 : Blo 1048611 1684685 := bbase (se 3 (by rfl) ⟨315878, by rfl⟩ : syracuseStep 1684685 = 631757) (by norm_num)
theorem B1684909 : Blo 1048611 1684909 := bbase (se 3 (by rfl) ⟨315920, by rfl⟩ : syracuseStep 1684909 = 631841) (by norm_num)
theorem B2242085 : Blo 1048611 2242085 := bbase (se 4 (by rfl) ⟨210195, by rfl⟩ : syracuseStep 2242085 = 420391) (by norm_num)
theorem B8763125 : Blo 1048611 8763125 := bbase (se 5 (by rfl) ⟨410771, by rfl⟩ : syracuseStep 8763125 = 821543) (by norm_num)
theorem B2242325 : Blo 1048611 2242325 := bbase (se 6 (by rfl) ⟨52554, by rfl⟩ : syracuseStep 2242325 = 105109) (by norm_num)
theorem B8534069 : Blo 1048611 8534069 := bbase (se 5 (by rfl) ⟨400034, by rfl⟩ : syracuseStep 8534069 = 800069) (by norm_num)
theorem B2996453 : Blo 1048611 2996453 := bbase (se 4 (by rfl) ⟨280917, by rfl⟩ : syracuseStep 2996453 = 561835) (by norm_num)
theorem B2242829 : Blo 1048611 2242829 := bbase (se 3 (by rfl) ⟨420530, by rfl⟩ : syracuseStep 2242829 = 841061) (by norm_num)
theorem B2242837 : Blo 1048611 2242837 := bbase (se 6 (by rfl) ⟨52566, by rfl⟩ : syracuseStep 2242837 = 105133) (by norm_num)
theorem B5323157 : Blo 1048611 5323157 := bbase (se 6 (by rfl) ⟨124761, by rfl⟩ : syracuseStep 5323157 = 249523) (by norm_num)
theorem B1686037 : Blo 1048611 1686037 := bbase (se 6 (by rfl) ⟨39516, by rfl⟩ : syracuseStep 1686037 = 79033) (by norm_num)
theorem B2079325 : Blo 1048611 2079325 := bbase (se 3 (by rfl) ⟨389873, by rfl⟩ : syracuseStep 2079325 = 779747) (by norm_num)
theorem B1260145 : Blo 1048611 1260145 := bbase (se 2 (by rfl) ⟨472554, by rfl⟩ : syracuseStep 1260145 = 945109) (by norm_num)
theorem B1260289 : Blo 1048611 1260289 := bbase (se 2 (by rfl) ⟨472608, by rfl⟩ : syracuseStep 1260289 = 945217) (by norm_num)
theorem B2997125 : Blo 1048611 2997125 := bbase (se 4 (by rfl) ⟨280980, by rfl⟩ : syracuseStep 2997125 = 561961) (by norm_num)
theorem B1063949 : Blo 1048611 1063949 := bbase (se 3 (by rfl) ⟨199490, by rfl⟩ : syracuseStep 1063949 = 398981) (by norm_num)
theorem B12795029 : Blo 1048611 12795029 := bbase (se 6 (by rfl) ⟨299883, by rfl⟩ : syracuseStep 12795029 = 599767) (by norm_num)
theorem B1621181 : Blo 1048611 1621181 := bbase (se 3 (by rfl) ⟨303971, by rfl⟩ : syracuseStep 1621181 = 607943) (by norm_num)
theorem B9583829 : Blo 1048611 9583829 := bbase (se 7 (by rfl) ⟨112310, by rfl⟩ : syracuseStep 9583829 = 224621) (by norm_num)
theorem B2243965 : Blo 1048611 2243965 := bbase (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) (by norm_num)
theorem B6733205 : Blo 1048611 6733205 := bbase (se 6 (by rfl) ⟨157809, by rfl⟩ : syracuseStep 6733205 = 315619) (by norm_num)
theorem B1064545 : Blo 1048611 1064545 := bbase (se 2 (by rfl) ⟨399204, by rfl⟩ : syracuseStep 1064545 = 798409) (by norm_num)
theorem B1064569 : Blo 1048611 1064569 := bbase (se 2 (by rfl) ⟨399213, by rfl⟩ : syracuseStep 1064569 = 798427) (by norm_num)
theorem B5324453 : Blo 1048611 5324453 := bbase (se 4 (by rfl) ⟨499167, by rfl⟩ : syracuseStep 5324453 = 998335) (by norm_num)
theorem B24592085 : Blo 1048611 24592085 := bbase (se 7 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 24592085 = 576377) (by norm_num)
theorem B2244341 : Blo 1048611 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B1261337 : Blo 1048611 1261337 := bbase (se 2 (by rfl) ⟨473001, by rfl⟩ : syracuseStep 1261337 = 946003) (by norm_num)
theorem B1064773 : Blo 1048611 1064773 := bbase (se 4 (by rfl) ⟨99822, by rfl⟩ : syracuseStep 1064773 = 199645) (by norm_num)
theorem B2768933 : Blo 1048611 2768933 := bbase (se 4 (by rfl) ⟨259587, by rfl⟩ : syracuseStep 2768933 = 519175) (by norm_num)
theorem B1327205 : Blo 1048611 1327205 := bbase (se 4 (by rfl) ⟨124425, by rfl⟩ : syracuseStep 1327205 = 248851) (by norm_num)
theorem B1261669 : Blo 1048611 1261669 := bbase (se 4 (by rfl) ⟨118281, by rfl⟩ : syracuseStep 1261669 = 236563) (by norm_num)
theorem B1327261 : Blo 1048611 1327261 := bbase (se 3 (by rfl) ⟨248861, by rfl⟩ : syracuseStep 1327261 = 497723) (by norm_num)
theorem B1327357 : Blo 1048611 1327357 := bbase (se 3 (by rfl) ⟨248879, by rfl⟩ : syracuseStep 1327357 = 497759) (by norm_num)
theorem B7389461 : Blo 1048611 7389461 := bbase (se 6 (by rfl) ⟨173190, by rfl⟩ : syracuseStep 7389461 = 346381) (by norm_num)
theorem B1818949 : Blo 1048611 1818949 := bbase (se 4 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 1818949 = 341053) (by norm_num)
theorem B13648213 : Blo 1048611 13648213 := bbase (se 10 (by rfl) ⟨19992, by rfl⟩ : syracuseStep 13648213 = 39985) (by norm_num)
theorem B1327529 : Blo 1048611 1327529 := bbase (se 2 (by rfl) ⟨497823, by rfl⟩ : syracuseStep 1327529 = 995647) (by norm_num)
theorem B1327585 : Blo 1048611 1327585 := bbase (se 2 (by rfl) ⟨497844, by rfl⟩ : syracuseStep 1327585 = 995689) (by norm_num)
theorem B3785237 : Blo 1048611 3785237 := bbase (se 6 (by rfl) ⟨88716, by rfl⟩ : syracuseStep 3785237 = 177433) (by norm_num)
theorem B1327681 : Blo 1048611 1327681 := bbase (se 2 (by rfl) ⟨497880, by rfl⟩ : syracuseStep 1327681 = 995761) (by norm_num)
theorem B3883589 : Blo 1048611 3883589 := bbase (se 4 (by rfl) ⟨364086, by rfl⟩ : syracuseStep 3883589 = 728173) (by norm_num)
theorem B1327853 : Blo 1048611 1327853 := bbase (se 3 (by rfl) ⟨248972, by rfl⟩ : syracuseStep 1327853 = 497945) (by norm_num)
theorem B1065737 : Blo 1048611 1065737 := bbase (se 2 (by rfl) ⟨399651, by rfl⟩ : syracuseStep 1065737 = 799303) (by norm_num)
theorem B1327909 : Blo 1048611 1327909 := bbase (se 4 (by rfl) ⟨124491, by rfl⟩ : syracuseStep 1327909 = 248983) (by norm_num)
theorem B1196893 : Blo 1048611 1196893 := bbase (se 3 (by rfl) ⟨224417, by rfl⟩ : syracuseStep 1196893 = 448835) (by norm_num)
theorem B1328005 : Blo 1048611 1328005 := bbase (se 4 (by rfl) ⟨124500, by rfl⟩ : syracuseStep 1328005 = 249001) (by norm_num)
theorem B5325749 : Blo 1048611 5325749 := bbase (se 5 (by rfl) ⟨249644, by rfl⟩ : syracuseStep 5325749 = 499289) (by norm_num)
theorem B1262557 : Blo 1048611 1262557 := bbase (se 3 (by rfl) ⟨236729, by rfl⟩ : syracuseStep 1262557 = 473459) (by norm_num)
theorem B1066025 : Blo 1048611 1066025 := bbase (se 2 (by rfl) ⟨399759, by rfl⟩ : syracuseStep 1066025 = 799519) (by norm_num)
theorem B1328177 : Blo 1048611 1328177 := bbase (se 2 (by rfl) ⟨498066, by rfl⟩ : syracuseStep 1328177 = 996133) (by norm_num)
theorem B3982405 : Blo 1048611 3982405 := bbase (se 4 (by rfl) ⟨373350, by rfl⟩ : syracuseStep 3982405 = 746701) (by norm_num)
theorem B1328233 : Blo 1048611 1328233 := bbase (se 2 (by rfl) ⟨498087, by rfl⟩ : syracuseStep 1328233 = 996175) (by norm_num)
theorem B1328329 : Blo 1048611 1328329 := bbase (se 2 (by rfl) ⟨498123, by rfl⟩ : syracuseStep 1328329 = 996247) (by norm_num)
theorem B1066321 : Blo 1048611 1066321 := bbase (se 2 (by rfl) ⟨399870, by rfl⟩ : syracuseStep 1066321 = 799741) (by norm_num)
theorem B2245981 : Blo 1048611 2245981 := bbase (se 3 (by rfl) ⟨421121, by rfl⟩ : syracuseStep 2245981 = 842243) (by norm_num)
theorem B1197421 : Blo 1048611 1197421 := bbase (se 3 (by rfl) ⟨224516, by rfl⟩ : syracuseStep 1197421 = 449033) (by norm_num)
theorem B3982709 : Blo 1048611 3982709 := bbase (se 5 (by rfl) ⟨186689, by rfl⟩ : syracuseStep 3982709 = 373379) (by norm_num)
theorem B1328501 : Blo 1048611 1328501 := bbase (se 5 (by rfl) ⟨62273, by rfl⟩ : syracuseStep 1328501 = 124547) (by norm_num)
theorem B1328557 : Blo 1048611 1328557 := bbase (se 3 (by rfl) ⟨249104, by rfl⟩ : syracuseStep 1328557 = 498209) (by norm_num)
theorem B15123925 : Blo 1048611 15123925 := bbase (se 7 (by rfl) ⟨177233, by rfl⟩ : syracuseStep 15123925 = 354467) (by norm_num)
theorem B1328653 : Blo 1048611 1328653 := bbase (se 3 (by rfl) ⟨249122, by rfl⟩ : syracuseStep 1328653 = 498245) (by norm_num)
theorem B1197677 : Blo 1048611 1197677 := bbase (se 3 (by rfl) ⟨224564, by rfl⟩ : syracuseStep 1197677 = 449129) (by norm_num)
theorem B1328825 : Blo 1048611 1328825 := bbase (se 2 (by rfl) ⟨498309, by rfl⟩ : syracuseStep 1328825 = 996619) (by norm_num)
theorem B1328881 : Blo 1048611 1328881 := bbase (se 2 (by rfl) ⟨498330, by rfl⟩ : syracuseStep 1328881 = 996661) (by norm_num)
theorem B3032821 : Blo 1048611 3032821 := bbase (se 5 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 3032821 = 284327) (by norm_num)
theorem B3360565 : Blo 1048611 3360565 := bbase (se 5 (by rfl) ⟨157526, by rfl⟩ : syracuseStep 3360565 = 315053) (by norm_num)
theorem B1328977 : Blo 1048611 1328977 := bbase (se 2 (by rfl) ⟨498366, by rfl⟩ : syracuseStep 1328977 = 996733) (by norm_num)
theorem B1066889 : Blo 1048611 1066889 := bbase (se 2 (by rfl) ⟨400083, by rfl⟩ : syracuseStep 1066889 = 800167) (by norm_num)
theorem B1066937 : Blo 1048611 1066937 := bbase (se 2 (by rfl) ⟨400101, by rfl⟩ : syracuseStep 1066937 = 800203) (by norm_num)
theorem B2836421 : Blo 1048611 2836421 := bbase (se 4 (by rfl) ⟨265914, by rfl⟩ : syracuseStep 2836421 = 531829) (by norm_num)
theorem B1263605 : Blo 1048611 1263605 := bbase (se 5 (by rfl) ⟨59231, by rfl⟩ : syracuseStep 1263605 = 118463) (by norm_num)
theorem B1329149 : Blo 1048611 1329149 := bbase (se 3 (by rfl) ⟨249215, by rfl⟩ : syracuseStep 1329149 = 498431) (by norm_num)
theorem B1329205 : Blo 1048611 1329205 := bbase (se 5 (by rfl) ⟨62306, by rfl⟩ : syracuseStep 1329205 = 124613) (by norm_num)
theorem B1329301 : Blo 1048611 1329301 := bbase (se 6 (by rfl) ⟨31155, by rfl⟩ : syracuseStep 1329301 = 62311) (by norm_num)
theorem B5327045 : Blo 1048611 5327045 := bbase (se 4 (by rfl) ⟨499410, by rfl⟩ : syracuseStep 5327045 = 998821) (by norm_num)
theorem B2246869 : Blo 1048611 2246869 := bbase (se 7 (by rfl) ⟨26330, by rfl⟩ : syracuseStep 2246869 = 52661) (by norm_num)
theorem B1329473 : Blo 1048611 1329473 := bbase (se 2 (by rfl) ⟨498552, by rfl⟩ : syracuseStep 1329473 = 997105) (by norm_num)
theorem B1263961 : Blo 1048611 1263961 := bbase (se 2 (by rfl) ⟨473985, by rfl⟩ : syracuseStep 1263961 = 947971) (by norm_num)
theorem B1329529 : Blo 1048611 1329529 := bbase (se 2 (by rfl) ⟨498573, by rfl⟩ : syracuseStep 1329529 = 997147) (by norm_num)
theorem B4049365 : Blo 1048611 4049365 := bbase (se 7 (by rfl) ⟨47453, by rfl⟩ : syracuseStep 4049365 = 94907) (by norm_num)
theorem B1329625 : Blo 1048611 1329625 := bbase (se 2 (by rfl) ⟨498609, by rfl⟩ : syracuseStep 1329625 = 997219) (by norm_num)
theorem B6736405 : Blo 1048611 6736405 := bbase (se 6 (by rfl) ⟨157884, by rfl⟩ : syracuseStep 6736405 = 315769) (by norm_num)
theorem B1264153 : Blo 1048611 1264153 := bbase (se 2 (by rfl) ⟨474057, by rfl⟩ : syracuseStep 1264153 = 948115) (by norm_num)
theorem B1329797 : Blo 1048611 1329797 := bbase (se 4 (by rfl) ⟨124668, by rfl⟩ : syracuseStep 1329797 = 249337) (by norm_num)
theorem B1493653 : Blo 1048611 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B1264297 : Blo 1048611 1264297 := bbase (se 2 (by rfl) ⟨474111, by rfl⟩ : syracuseStep 1264297 = 948223) (by norm_num)
theorem B1329853 : Blo 1048611 1329853 := bbase (se 3 (by rfl) ⟨249347, by rfl⟩ : syracuseStep 1329853 = 498695) (by norm_num)
theorem B2247365 : Blo 1048611 2247365 := bbase (se 4 (by rfl) ⟨210690, by rfl⟩ : syracuseStep 2247365 = 421381) (by norm_num)
theorem B1329949 : Blo 1048611 1329949 := bbase (se 3 (by rfl) ⟨249365, by rfl⟩ : syracuseStep 1329949 = 498731) (by norm_num)
theorem B2018125 : Blo 1048611 2018125 := bbase (se 3 (by rfl) ⟨378398, by rfl⟩ : syracuseStep 2018125 = 756797) (by norm_num)
theorem B1330121 : Blo 1048611 1330121 := bbase (se 2 (by rfl) ⟨498795, by rfl⟩ : syracuseStep 1330121 = 997591) (by norm_num)
theorem B1330177 : Blo 1048611 1330177 := bbase (se 2 (by rfl) ⟨498816, by rfl⟩ : syracuseStep 1330177 = 997633) (by norm_num)
theorem B1199173 : Blo 1048611 1199173 := bbase (se 4 (by rfl) ⟨112422, by rfl⟩ : syracuseStep 1199173 = 224845) (by norm_num)
theorem B1330273 : Blo 1048611 1330273 := bbase (se 2 (by rfl) ⟨498852, by rfl⟩ : syracuseStep 1330273 = 997705) (by norm_num)
theorem B3361925 : Blo 1048611 3361925 := bbase (se 4 (by rfl) ⟨315180, by rfl⟩ : syracuseStep 3361925 = 630361) (by norm_num)
theorem B1494245 : Blo 1048611 1494245 := bbase (se 4 (by rfl) ⟨140085, by rfl⟩ : syracuseStep 1494245 = 280171) (by norm_num)
theorem B3788005 : Blo 1048611 3788005 := bbase (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) (by norm_num)
theorem B2837749 : Blo 1048611 2837749 := bbase (se 5 (by rfl) ⟨133019, by rfl⟩ : syracuseStep 2837749 = 266039) (by norm_num)
theorem B1330445 : Blo 1048611 1330445 := bbase (se 3 (by rfl) ⟨249458, by rfl⟩ : syracuseStep 1330445 = 498917) (by norm_num)
theorem B1494325 : Blo 1048611 1494325 := bbase (se 5 (by rfl) ⟨70046, by rfl⟩ : syracuseStep 1494325 = 140093) (by norm_num)
theorem B5983541 : Blo 1048611 5983541 := bbase (se 5 (by rfl) ⟨280478, by rfl⟩ : syracuseStep 5983541 = 560957) (by norm_num)
theorem B1330501 : Blo 1048611 1330501 := bbase (se 4 (by rfl) ⟨124734, by rfl⟩ : syracuseStep 1330501 = 249469) (by norm_num)
theorem B1330597 : Blo 1048611 1330597 := bbase (se 4 (by rfl) ⟨124743, by rfl⟩ : syracuseStep 1330597 = 249487) (by norm_num)
theorem B1494445 : Blo 1048611 1494445 := bbase (se 3 (by rfl) ⟨280208, by rfl⟩ : syracuseStep 1494445 = 560417) (by norm_num)
theorem B3984821 : Blo 1048611 3984821 := bbase (se 5 (by rfl) ⟨186788, by rfl⟩ : syracuseStep 3984821 = 373577) (by norm_num)
theorem B5393861 : Blo 1048611 5393861 := bbase (se 4 (by rfl) ⟨505674, by rfl⟩ : syracuseStep 5393861 = 1011349) (by norm_num)
theorem B3034565 : Blo 1048611 3034565 := bbase (se 4 (by rfl) ⟨284490, by rfl⟩ : syracuseStep 3034565 = 568981) (by norm_num)
theorem B7982549 : Blo 1048611 7982549 := bbase (se 7 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 7982549 = 187091) (by norm_num)
theorem B5328341 : Blo 1048611 5328341 := bbase (se 7 (by rfl) ⟨62441, by rfl⟩ : syracuseStep 5328341 = 124883) (by norm_num)
theorem B1199621 : Blo 1048611 1199621 := bbase (se 4 (by rfl) ⟨112464, by rfl⟩ : syracuseStep 1199621 = 224929) (by norm_num)
theorem B1494541 : Blo 1048611 1494541 := bbase (se 3 (by rfl) ⟨280226, by rfl⟩ : syracuseStep 1494541 = 560453) (by norm_num)
theorem B4312597 : Blo 1048611 4312597 := bbase (se 6 (by rfl) ⟨101076, by rfl⟩ : syracuseStep 4312597 = 202153) (by norm_num)
theorem B1330769 : Blo 1048611 1330769 := bbase (se 2 (by rfl) ⟨499038, by rfl⟩ : syracuseStep 1330769 = 998077) (by norm_num)
theorem B1330825 : Blo 1048611 1330825 := bbase (se 2 (by rfl) ⟨499059, by rfl⟩ : syracuseStep 1330825 = 998119) (by norm_num)
theorem B3985109 : Blo 1048611 3985109 := bbase (se 7 (by rfl) ⟨46700, by rfl⟩ : syracuseStep 3985109 = 93401) (by norm_num)
theorem B2838245 : Blo 1048611 2838245 := bbase (se 4 (by rfl) ⟨266085, by rfl⟩ : syracuseStep 2838245 = 532171) (by norm_num)
theorem B1330921 : Blo 1048611 1330921 := bbase (se 2 (by rfl) ⟨499095, by rfl⟩ : syracuseStep 1330921 = 998191) (by norm_num)
theorem B1331093 : Blo 1048611 1331093 := bbase (se 6 (by rfl) ⟨31197, by rfl⟩ : syracuseStep 1331093 = 62395) (by norm_num)
theorem B8081333 : Blo 1048611 8081333 := bbase (se 5 (by rfl) ⟨378812, by rfl⟩ : syracuseStep 8081333 = 757625) (by norm_num)
theorem B1331149 : Blo 1048611 1331149 := bbase (se 3 (by rfl) ⟨249590, by rfl⟩ : syracuseStep 1331149 = 499181) (by norm_num)
theorem B1495037 : Blo 1048611 1495037 := bbase (se 3 (by rfl) ⟨280319, by rfl⟩ : syracuseStep 1495037 = 560639) (by norm_num)
theorem B1331245 : Blo 1048611 1331245 := bbase (se 3 (by rfl) ⟨249608, by rfl⟩ : syracuseStep 1331245 = 499217) (by norm_num)
theorem B2019541 : Blo 1048611 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B1331417 : Blo 1048611 1331417 := bbase (se 2 (by rfl) ⟨499281, by rfl⟩ : syracuseStep 1331417 = 998563) (by norm_num)
theorem B1331473 : Blo 1048611 1331473 := bbase (se 2 (by rfl) ⟨499302, by rfl⟩ : syracuseStep 1331473 = 998605) (by norm_num)
theorem B11948309 : Blo 1048611 11948309 := bbase (se 6 (by rfl) ⟨280038, by rfl⟩ : syracuseStep 11948309 = 560077) (by norm_num)
theorem B1331569 : Blo 1048611 1331569 := bbase (se 2 (by rfl) ⟨499338, by rfl⟩ : syracuseStep 1331569 = 998677) (by norm_num)
theorem B5984725 : Blo 1048611 5984725 := bbase (se 7 (by rfl) ⟨70133, by rfl⟩ : syracuseStep 5984725 = 140267) (by norm_num)
theorem B1331741 : Blo 1048611 1331741 := bbase (se 3 (by rfl) ⟨249701, by rfl⟩ : syracuseStep 1331741 = 499403) (by norm_num)
theorem B1495589 : Blo 1048611 1495589 := bbase (se 4 (by rfl) ⟨140211, by rfl⟩ : syracuseStep 1495589 = 280423) (by norm_num)
theorem B3330629 : Blo 1048611 3330629 := bbase (se 4 (by rfl) ⟨312246, by rfl⟩ : syracuseStep 3330629 = 624493) (by norm_num)
theorem B1331797 : Blo 1048611 1331797 := bbase (se 8 (by rfl) ⟨7803, by rfl⟩ : syracuseStep 1331797 = 15607) (by norm_num)
theorem B1331893 : Blo 1048611 1331893 := bbase (se 5 (by rfl) ⟨62432, by rfl⟩ : syracuseStep 1331893 = 124865) (by norm_num)
theorem B1332065 : Blo 1048611 1332065 := bbase (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) (by norm_num)
theorem B3986293 : Blo 1048611 3986293 := bbase (se 5 (by rfl) ⟨186857, by rfl⟩ : syracuseStep 3986293 = 373715) (by norm_num)
theorem B1332121 : Blo 1048611 1332121 := bbase (se 2 (by rfl) ⟨499545, by rfl⟩ : syracuseStep 1332121 = 999091) (by norm_num)
theorem B1365017 : Blo 1048611 1365017 := bbase (se 2 (by rfl) ⟨511881, by rfl⟩ : syracuseStep 1365017 = 1023763) (by norm_num)
theorem B1135745 : Blo 1048611 1135745 := bbase (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) (by norm_num)
theorem B3986597 : Blo 1048611 3986597 := bbase (se 4 (by rfl) ⟨373743, by rfl⟩ : syracuseStep 3986597 = 747487) (by norm_num)
theorem B1496341 : Blo 1048611 1496341 := bbase (se 6 (by rfl) ⟨35070, by rfl⟩ : syracuseStep 1496341 = 70141) (by norm_num)
theorem B1168849 : Blo 1048611 1168849 := bbase (se 2 (by rfl) ⟨438318, by rfl⟩ : syracuseStep 1168849 = 876637) (by norm_num)
theorem B18175445 : Blo 1048611 18175445 := bbase (se 7 (by rfl) ⟨212993, by rfl⟩ : syracuseStep 18175445 = 425987) (by norm_num)
theorem B3593909 : Blo 1048611 3593909 := bbase (se 5 (by rfl) ⟨168464, by rfl⟩ : syracuseStep 3593909 = 336929) (by norm_num)
theorem B3790613 : Blo 1048611 3790613 := bbase (se 6 (by rfl) ⟨88842, by rfl⟩ : syracuseStep 3790613 = 177685) (by norm_num)
theorem B2840453 : Blo 1048611 2840453 := bbase (se 4 (by rfl) ⟨266292, by rfl⟩ : syracuseStep 2840453 = 532585) (by norm_num)
theorem B1136521 : Blo 1048611 1136521 := bbase (se 2 (by rfl) ⟨426195, by rfl⟩ : syracuseStep 1136521 = 852391) (by norm_num)
theorem B1497133 : Blo 1048611 1497133 := bbase (se 3 (by rfl) ⟨280712, by rfl⟩ : syracuseStep 1497133 = 561425) (by norm_num)
theorem B3790901 : Blo 1048611 3790901 := bbase (se 5 (by rfl) ⟨177698, by rfl⟩ : syracuseStep 3790901 = 355397) (by norm_num)
theorem B1824925 : Blo 1048611 1824925 := bbase (se 3 (by rfl) ⟨342173, by rfl⟩ : syracuseStep 1824925 = 684347) (by norm_num)
theorem B1497469 : Blo 1048611 1497469 := bbase (se 3 (by rfl) ⟨280775, by rfl⟩ : syracuseStep 1497469 = 561551) (by norm_num)
theorem B5986709 : Blo 1048611 5986709 := bbase (se 6 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 5986709 = 280627) (by norm_num)
theorem B3365333 : Blo 1048611 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B1497685 : Blo 1048611 1497685 := bbase (se 8 (by rfl) ⟨8775, by rfl⟩ : syracuseStep 1497685 = 17551) (by norm_num)
theorem B1498061 : Blo 1048611 1498061 := bbase (se 3 (by rfl) ⟨280886, by rfl⟩ : syracuseStep 1498061 = 561773) (by norm_num)
theorem B3792053 : Blo 1048611 3792053 := bbase (se 5 (by rfl) ⟨177752, by rfl⟩ : syracuseStep 3792053 = 355505) (by norm_num)
theorem B3988709 : Blo 1048611 3988709 := bbase (se 4 (by rfl) ⟨373941, by rfl⟩ : syracuseStep 3988709 = 747883) (by norm_num)
theorem B3988997 : Blo 1048611 3988997 := bbase (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) (by norm_num)
theorem B1597013 : Blo 1048611 1597013 := bbase (se 8 (by rfl) ⟨9357, by rfl⟩ : syracuseStep 1597013 = 18715) (by norm_num)
theorem B3366613 : Blo 1048611 3366613 := bbase (se 7 (by rfl) ⟨39452, by rfl⟩ : syracuseStep 3366613 = 78905) (by norm_num)
theorem B1793773 : Blo 1048611 1793773 := bbase (se 3 (by rfl) ⟨336332, by rfl⟩ : syracuseStep 1793773 = 672665) (by norm_num)
theorem B1368029 : Blo 1048611 1368029 := bbase (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) (by norm_num)
theorem B6742453 : Blo 1048611 6742453 := bbase (se 5 (by rfl) ⟨316052, by rfl⟩ : syracuseStep 6742453 = 632105) (by norm_num)
theorem B5988917 : Blo 1048611 5988917 := bbase (se 5 (by rfl) ⟨280730, by rfl⟩ : syracuseStep 5988917 = 561461) (by norm_num)
theorem B2843221 : Blo 1048611 2843221 := bbase (se 8 (by rfl) ⟨16659, by rfl⟩ : syracuseStep 2843221 = 33319) (by norm_num)
theorem B2024029 : Blo 1048611 2024029 := bbase (se 3 (by rfl) ⟨379505, by rfl⟩ : syracuseStep 2024029 = 759011) (by norm_num)
theorem B1892965 : Blo 1048611 1892965 := bbase (se 4 (by rfl) ⟨177465, by rfl⟩ : syracuseStep 1892965 = 354931) (by norm_num)
theorem B1991317 : Blo 1048611 1991317 := bbase (se 6 (by rfl) ⟨46671, by rfl⟩ : syracuseStep 1991317 = 93343) (by norm_num)
theorem B3990181 : Blo 1048611 3990181 := bbase (se 4 (by rfl) ⟨374079, by rfl⟩ : syracuseStep 3990181 = 748159) (by norm_num)
theorem B10085077 : Blo 1048611 10085077 := bbase (se 7 (by rfl) ⟨118184, by rfl⟩ : syracuseStep 10085077 = 236369) (by norm_num)
theorem B1991461 : Blo 1048611 1991461 := bbase (se 4 (by rfl) ⟨186699, by rfl⟩ : syracuseStep 1991461 = 373399) (by norm_num)
theorem B1794901 : Blo 1048611 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B1991621 : Blo 1048611 1991621 := bbase (se 4 (by rfl) ⟨186714, by rfl⟩ : syracuseStep 1991621 = 373429) (by norm_num)
theorem B3990485 : Blo 1048611 3990485 := bbase (se 7 (by rfl) ⟨46763, by rfl⟩ : syracuseStep 3990485 = 93527) (by norm_num)
theorem B4482053 : Blo 1048611 4482053 := bbase (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) (by norm_num)
theorem B3367973 : Blo 1048611 3367973 := bbase (se 4 (by rfl) ⟨315747, by rfl⟩ : syracuseStep 3367973 = 631495) (by norm_num)
theorem B1991765 : Blo 1048611 1991765 := bbase (se 8 (by rfl) ⟨11670, by rfl⟩ : syracuseStep 1991765 = 23341) (by norm_num)
theorem B1893461 : Blo 1048611 1893461 := bbase (se 8 (by rfl) ⟨11094, by rfl⟩ : syracuseStep 1893461 = 22189) (by norm_num)
theorem B3368101 : Blo 1048611 3368101 := bbase (se 4 (by rfl) ⟨315759, by rfl⟩ : syracuseStep 3368101 = 631519) (by norm_num)
theorem B1992053 : Blo 1048611 1992053 := bbase (se 5 (by rfl) ⟨93377, by rfl⟩ : syracuseStep 1992053 = 186755) (by norm_num)
theorem B3368357 : Blo 1048611 3368357 := bbase (se 4 (by rfl) ⟨315783, by rfl⟩ : syracuseStep 3368357 = 631567) (by norm_num)
theorem B5400037 : Blo 1048611 5400037 := bbase (se 4 (by rfl) ⟨506253, by rfl⟩ : syracuseStep 5400037 = 1012507) (by norm_num)
theorem B1992205 : Blo 1048611 1992205 := bbase (se 3 (by rfl) ⟨373538, by rfl⟩ : syracuseStep 1992205 = 747077) (by norm_num)
theorem B1992509 : Blo 1048611 1992509 := bbase (se 3 (by rfl) ⟨373595, by rfl⟩ : syracuseStep 1992509 = 747191) (by norm_num)
theorem B2877365 : Blo 1048611 2877365 := bbase (se 5 (by rfl) ⟨134876, by rfl⟩ : syracuseStep 2877365 = 269753) (by norm_num)
theorem B1894349 : Blo 1048611 1894349 := bbase (se 3 (by rfl) ⟨355190, by rfl⟩ : syracuseStep 1894349 = 710381) (by norm_num)
theorem B2844821 : Blo 1048611 2844821 := bbase (se 6 (by rfl) ⟨66675, by rfl⟩ : syracuseStep 2844821 = 133351) (by norm_num)
theorem B1894637 : Blo 1048611 1894637 := bbase (se 3 (by rfl) ⟨355244, by rfl⟩ : syracuseStep 1894637 = 710489) (by norm_num)
theorem B1993261 : Blo 1048611 1993261 := bbase (se 3 (by rfl) ⟨373736, by rfl⟩ : syracuseStep 1993261 = 747473) (by norm_num)
theorem B1993405 : Blo 1048611 1993405 := bbase (se 3 (by rfl) ⟨373763, by rfl⟩ : syracuseStep 1993405 = 747527) (by norm_num)
theorem B4483829 : Blo 1048611 4483829 := bbase (se 5 (by rfl) ⟨210179, by rfl⟩ : syracuseStep 4483829 = 420359) (by norm_num)
theorem B1993565 : Blo 1048611 1993565 := bbase (se 3 (by rfl) ⟨373793, by rfl⟩ : syracuseStep 1993565 = 747587) (by norm_num)
theorem B4484069 : Blo 1048611 4484069 := bbase (se 4 (by rfl) ⟨420381, by rfl⟩ : syracuseStep 4484069 = 840763) (by norm_num)
theorem B1993709 : Blo 1048611 1993709 := bbase (se 3 (by rfl) ⟨373820, by rfl⟩ : syracuseStep 1993709 = 747641) (by norm_num)
theorem B3992597 : Blo 1048611 3992597 := bbase (se 6 (by rfl) ⟨93576, by rfl⟩ : syracuseStep 3992597 = 187153) (by norm_num)
theorem B7990325 : Blo 1048611 7990325 := bbase (se 5 (by rfl) ⟨374546, by rfl⟩ : syracuseStep 7990325 = 749093) (by norm_num)
theorem B4090981 : Blo 1048611 4090981 := bbase (se 4 (by rfl) ⟨383529, by rfl⟩ : syracuseStep 4090981 = 767059) (by norm_num)
theorem B1895653 : Blo 1048611 1895653 := bbase (se 4 (by rfl) ⟨177717, by rfl⟩ : syracuseStep 1895653 = 355435) (by norm_num)
theorem B1993997 : Blo 1048611 1993997 := bbase (se 3 (by rfl) ⟨373874, by rfl⟩ : syracuseStep 1993997 = 747749) (by norm_num)
theorem B3992885 : Blo 1048611 3992885 := bbase (se 5 (by rfl) ⟨187166, by rfl⟩ : syracuseStep 3992885 = 374333) (by norm_num)
theorem B5041541 : Blo 1048611 5041541 := bbase (se 4 (by rfl) ⟨472644, by rfl⟩ : syracuseStep 5041541 = 945289) (by norm_num)
theorem B1994149 : Blo 1048611 1994149 := bbase (se 4 (by rfl) ⟨186951, by rfl⟩ : syracuseStep 1994149 = 373903) (by norm_num)
theorem B1896085 : Blo 1048611 1896085 := bbase (se 6 (by rfl) ⟨44439, by rfl⟩ : syracuseStep 1896085 = 88879) (by norm_num)
theorem B1994453 : Blo 1048611 1994453 := bbase (se 7 (by rfl) ⟨23372, by rfl⟩ : syracuseStep 1994453 = 46745) (by norm_num)
theorem B3370805 : Blo 1048611 3370805 := bbase (se 5 (by rfl) ⟨158006, by rfl⟩ : syracuseStep 3370805 = 316013) (by norm_num)
theorem B1896373 : Blo 1048611 1896373 := bbase (se 5 (by rfl) ⟨88892, by rfl⟩ : syracuseStep 1896373 = 177785) (by norm_num)
theorem B17920277 : Blo 1048611 17920277 := bbase (se 6 (by rfl) ⟨420006, by rfl⟩ : syracuseStep 17920277 = 840013) (by norm_num)
theorem B7565653 : Blo 1048611 7565653 := bbase (se 10 (by rfl) ⟨11082, by rfl⟩ : syracuseStep 7565653 = 22165) (by norm_num)
theorem B1995205 : Blo 1048611 1995205 := bbase (se 4 (by rfl) ⟨187050, by rfl⟩ : syracuseStep 1995205 = 374101) (by norm_num)
theorem B3994069 : Blo 1048611 3994069 := bbase (se 7 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 3994069 = 93611) (by norm_num)
theorem B2126341 : Blo 1048611 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B8974901 : Blo 1048611 8974901 := bbase (se 5 (by rfl) ⟨420698, by rfl⟩ : syracuseStep 8974901 = 841397) (by norm_num)
theorem B1995349 : Blo 1048611 1995349 := bbase (se 8 (by rfl) ⟨11691, by rfl⟩ : syracuseStep 1995349 = 23383) (by norm_num)
theorem B1995509 : Blo 1048611 1995509 := bbase (se 5 (by rfl) ⟨93539, by rfl⟩ : syracuseStep 1995509 = 187079) (by norm_num)
theorem B3994373 : Blo 1048611 3994373 := bbase (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) (by norm_num)
theorem B1995653 : Blo 1048611 1995653 := bbase (se 4 (by rfl) ⟨187092, by rfl⟩ : syracuseStep 1995653 = 374185) (by norm_num)
theorem B3372149 : Blo 1048611 3372149 := bbase (se 5 (by rfl) ⟨158069, by rfl⟩ : syracuseStep 3372149 = 316139) (by norm_num)
theorem B1995941 : Blo 1048611 1995941 := bbase (se 4 (by rfl) ⟨187119, by rfl⟩ : syracuseStep 1995941 = 374239) (by norm_num)
theorem B4256981 : Blo 1048611 4256981 := bbase (se 7 (by rfl) ⟨49886, by rfl⟩ : syracuseStep 4256981 = 99773) (by norm_num)
theorem B4486357 : Blo 1048611 4486357 := bbase (se 7 (by rfl) ⟨52574, by rfl⟩ : syracuseStep 4486357 = 105149) (by norm_num)
theorem B1996093 : Blo 1048611 1996093 := bbase (se 3 (by rfl) ⟨374267, by rfl⟩ : syracuseStep 1996093 = 748535) (by norm_num)
theorem B2160029 : Blo 1048611 2160029 := bbase (se 3 (by rfl) ⟨405005, by rfl⟩ : syracuseStep 2160029 = 810011) (by norm_num)
theorem B1996397 : Blo 1048611 1996397 := bbase (se 3 (by rfl) ⟨374324, by rfl⟩ : syracuseStep 1996397 = 748649) (by norm_num)
theorem B2520877 : Blo 1048611 2520877 := bbase (se 3 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 2520877 = 945329) (by norm_num)
theorem B1800101 : Blo 1048611 1800101 := bbase (se 4 (by rfl) ⟨168759, by rfl⟩ : syracuseStep 1800101 = 337519) (by norm_num)
theorem B1997149 : Blo 1048611 1997149 := bbase (se 3 (by rfl) ⟨374465, by rfl⟩ : syracuseStep 1997149 = 748931) (by norm_num)
theorem B2521493 : Blo 1048611 2521493 := bbase (se 6 (by rfl) ⟨59097, by rfl⟩ : syracuseStep 2521493 = 118195) (by norm_num)
theorem B1997293 : Blo 1048611 1997293 := bbase (se 3 (by rfl) ⟨374492, by rfl⟩ : syracuseStep 1997293 = 748985) (by norm_num)
theorem B1997453 : Blo 1048611 1997453 := bbase (se 3 (by rfl) ⟨374522, by rfl⟩ : syracuseStep 1997453 = 749045) (by norm_num)
theorem B4487845 : Blo 1048611 4487845 := bbase (se 4 (by rfl) ⟨420735, by rfl⟩ : syracuseStep 4487845 = 841471) (by norm_num)
theorem B4487861 : Blo 1048611 4487861 := bbase (se 5 (by rfl) ⟨210368, by rfl⟩ : syracuseStep 4487861 = 420737) (by norm_num)
theorem B1997597 : Blo 1048611 1997597 := bbase (se 3 (by rfl) ⟨374549, by rfl⟩ : syracuseStep 1997597 = 749099) (by norm_num)
theorem B3996485 : Blo 1048611 3996485 := bbase (se 4 (by rfl) ⟨374670, by rfl⟩ : syracuseStep 3996485 = 749341) (by norm_num)
theorem B1997885 : Blo 1048611 1997885 := bbase (se 3 (by rfl) ⟨374603, by rfl⟩ : syracuseStep 1997885 = 749207) (by norm_num)
theorem B1080409 : Blo 1048611 1080409 := bbase (se 2 (by rfl) ⟨405153, by rfl⟩ : syracuseStep 1080409 = 810307) (by norm_num)
theorem B2522261 : Blo 1048611 2522261 := bbase (se 6 (by rfl) ⟨59115, by rfl⟩ : syracuseStep 2522261 = 118231) (by norm_num)
theorem B2522269 : Blo 1048611 2522269 := bbase (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) (by norm_num)
theorem B1998037 : Blo 1048611 1998037 := bbase (se 7 (by rfl) ⟨23414, by rfl⟩ : syracuseStep 1998037 = 46829) (by norm_num)
theorem B1703261 : Blo 1048611 1703261 := bbase (se 3 (by rfl) ⟨319361, by rfl⟩ : syracuseStep 1703261 = 638723) (by norm_num)
theorem B8977877 : Blo 1048611 8977877 := bbase (se 7 (by rfl) ⟨105209, by rfl⟩ : syracuseStep 8977877 = 210419) (by norm_num)
theorem B9567989 : Blo 1048611 9567989 := bbase (se 5 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 9567989 = 896999) (by norm_num)
theorem B4849397 : Blo 1048611 4849397 := bbase (se 5 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 4849397 = 454631) (by norm_num)
theorem B1638301 : Blo 1048611 1638301 := bbase (se 3 (by rfl) ⟨307181, by rfl⟩ : syracuseStep 1638301 = 614363) (by norm_num)
theorem B2523077 : Blo 1048611 2523077 := bbase (se 4 (by rfl) ⟨236538, by rfl⟩ : syracuseStep 2523077 = 473077) (by norm_num)
theorem B5046229 : Blo 1048611 5046229 := bbase (se 7 (by rfl) ⟨59135, by rfl⟩ : syracuseStep 5046229 = 118271) (by norm_num)
theorem B3243989 : Blo 1048611 3243989 := bbase (se 7 (by rfl) ⟨38015, by rfl⟩ : syracuseStep 3243989 = 76031) (by norm_num)
theorem B1048611 : Blo 1048611 1048611 := bstep (se 1 (by rfl) ⟨786458, by rfl⟩ : syracuseStep 1048611 = 1572917) B1572917
theorem B1048627 : Blo 1048611 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B1572929 : Blo 1048611 1572929 := bstep (se 2 (by rfl) ⟨589848, by rfl⟩ : syracuseStep 1572929 = 1179697) B1179697
theorem B1769539 : Blo 1048611 1769539 := bstep (se 1 (by rfl) ⟨1327154, by rfl⟩ : syracuseStep 1769539 = 2654309) B2654309
theorem B1179715 : Blo 1048611 1179715 := bstep (se 1 (by rfl) ⟨884786, by rfl⟩ : syracuseStep 1179715 = 1769573) B1769573
theorem B1048643 : Blo 1048611 1048643 := bstep (se 1 (by rfl) ⟨786482, by rfl⟩ : syracuseStep 1048643 = 1572965) B1572965
theorem B1572947 : Blo 1048611 1572947 := bstep (se 1 (by rfl) ⟨1179710, by rfl⟩ : syracuseStep 1572947 = 2359421) B2359421
theorem B1048659 : Blo 1048611 1048659 := bstep (se 1 (by rfl) ⟨786494, by rfl⟩ : syracuseStep 1048659 = 1572989) B1572989
theorem B1048675 : Blo 1048611 1048675 := bstep (se 1 (by rfl) ⟨786506, by rfl⟩ : syracuseStep 1048675 = 1573013) B1573013
theorem B1572977 : Blo 1048611 1572977 := bstep (se 2 (by rfl) ⟨589866, by rfl⟩ : syracuseStep 1572977 = 1179733) B1179733
theorem B1048691 : Blo 1048611 1048691 := bstep (se 1 (by rfl) ⟨786518, by rfl⟩ : syracuseStep 1048691 = 1573037) B1573037
theorem B1572995 : Blo 1048611 1572995 := bstep (se 1 (by rfl) ⟨1179746, by rfl⟩ : syracuseStep 1572995 = 2359493) B2359493
theorem B1048707 : Blo 1048611 1048707 := bstep (se 1 (by rfl) ⟨786530, by rfl⟩ : syracuseStep 1048707 = 1573061) B1573061
theorem B1048723 : Blo 1048611 1048723 := bstep (se 1 (by rfl) ⟨786542, by rfl⟩ : syracuseStep 1048723 = 1573085) B1573085
theorem B1573025 : Blo 1048611 1573025 := bstep (se 2 (by rfl) ⟨589884, by rfl⟩ : syracuseStep 1573025 = 1179769) B1179769
theorem B1048739 : Blo 1048611 1048739 := bstep (se 1 (by rfl) ⟨786554, by rfl⟩ : syracuseStep 1048739 = 1573109) B1573109
theorem B1573043 : Blo 1048611 1573043 := bstep (se 1 (by rfl) ⟨1179782, by rfl⟩ : syracuseStep 1573043 = 2359565) B2359565
theorem B1048755 : Blo 1048611 1048755 := bstep (se 1 (by rfl) ⟨786566, by rfl⟩ : syracuseStep 1048755 = 1573133) B1573133
theorem B1048771 : Blo 1048611 1048771 := bstep (se 1 (by rfl) ⟨786578, by rfl⟩ : syracuseStep 1048771 = 1573157) B1573157
theorem B1769681 : Blo 1048611 1769681 := bstep (se 2 (by rfl) ⟨663630, by rfl⟩ : syracuseStep 1769681 = 1327261) B1327261
theorem B1573073 : Blo 1048611 1573073 := bstep (se 2 (by rfl) ⟨589902, by rfl⟩ : syracuseStep 1573073 = 1179805) B1179805
theorem B1179859 : Blo 1048611 1179859 := bstep (se 1 (by rfl) ⟨884894, by rfl⟩ : syracuseStep 1179859 = 1769789) B1769789
theorem B1048787 : Blo 1048611 1048787 := bstep (se 1 (by rfl) ⟨786590, by rfl⟩ : syracuseStep 1048787 = 1573181) B1573181
theorem B1573091 : Blo 1048611 1573091 := bstep (se 1 (by rfl) ⟨1179818, by rfl⟩ : syracuseStep 1573091 = 2359637) B2359637
theorem B1048803 : Blo 1048611 1048803 := bstep (se 1 (by rfl) ⟨786602, by rfl⟩ : syracuseStep 1048803 = 1573205) B1573205
theorem B1048819 : Blo 1048611 1048819 := bstep (se 1 (by rfl) ⟨786614, by rfl⟩ : syracuseStep 1048819 = 1573229) B1573229
theorem B1573121 : Blo 1048611 1573121 := bstep (se 2 (by rfl) ⟨589920, by rfl⟩ : syracuseStep 1573121 = 1179841) B1179841
theorem B1048835 : Blo 1048611 1048835 := bstep (se 1 (by rfl) ⟨786626, by rfl⟩ : syracuseStep 1048835 = 1573253) B1573253
theorem B3539213 : Blo 1048611 3539213 := bstep (se 3 (by rfl) ⟨663602, by rfl⟩ : syracuseStep 3539213 = 1327205) B1327205
theorem B1573139 : Blo 1048611 1573139 := bstep (se 1 (by rfl) ⟨1179854, by rfl⟩ : syracuseStep 1573139 = 2359709) B2359709
theorem B1048851 : Blo 1048611 1048851 := bstep (se 1 (by rfl) ⟨786638, by rfl⟩ : syracuseStep 1048851 = 1573277) B1573277
theorem B1048867 : Blo 1048611 1048867 := bstep (se 1 (by rfl) ⟨786650, by rfl⟩ : syracuseStep 1048867 = 1573301) B1573301
theorem B2359601 : Blo 1048611 2359601 := bstep (se 2 (by rfl) ⟨884850, by rfl⟩ : syracuseStep 2359601 = 1769701) B1769701
theorem B1573169 : Blo 1048611 1573169 := bstep (se 2 (by rfl) ⟨589938, by rfl⟩ : syracuseStep 1573169 = 1179877) B1179877
theorem B1048883 : Blo 1048611 1048883 := bstep (se 1 (by rfl) ⟨786662, by rfl⟩ : syracuseStep 1048883 = 1573325) B1573325
theorem B3539267 : Blo 1048611 3539267 := bstep (se 1 (by rfl) ⟨2654450, by rfl⟩ : syracuseStep 3539267 = 5308901) B5308901
theorem B2359619 : Blo 1048611 2359619 := bstep (se 1 (by rfl) ⟨1769714, by rfl⟩ : syracuseStep 2359619 = 3539429) B3539429
theorem B1573187 : Blo 1048611 1573187 := bstep (se 1 (by rfl) ⟨1179890, by rfl⟩ : syracuseStep 1573187 = 2359781) B2359781
theorem B1048899 : Blo 1048611 1048899 := bstep (se 1 (by rfl) ⟨786674, by rfl⟩ : syracuseStep 1048899 = 1573349) B1573349
theorem B1769809 : Blo 1048611 1769809 := bstep (se 2 (by rfl) ⟨663678, by rfl⟩ : syracuseStep 1769809 = 1327357) B1327357
theorem B1048915 : Blo 1048611 1048915 := bstep (se 1 (by rfl) ⟨786686, by rfl⟩ : syracuseStep 1048915 = 1573373) B1573373
theorem B1573217 : Blo 1048611 1573217 := bstep (se 2 (by rfl) ⟨589956, by rfl⟩ : syracuseStep 1573217 = 1179913) B1179913
theorem B1180003 : Blo 1048611 1180003 := bstep (se 1 (by rfl) ⟨885002, by rfl⟩ : syracuseStep 1180003 = 1770005) B1770005
theorem B1048931 : Blo 1048611 1048931 := bstep (se 1 (by rfl) ⟨786698, by rfl⟩ : syracuseStep 1048931 = 1573397) B1573397
theorem B2523491 : Blo 1048611 2523491 := bstep (se 1 (by rfl) ⟨1892618, by rfl⟩ : syracuseStep 2523491 = 3785237) B3785237
theorem B1769843 : Blo 1048611 1769843 := bstep (se 1 (by rfl) ⟨1327382, by rfl⟩ : syracuseStep 1769843 = 2654765) B2654765
theorem B1573235 : Blo 1048611 1573235 := bstep (se 1 (by rfl) ⟨1179926, by rfl⟩ : syracuseStep 1573235 = 2359853) B2359853
theorem B1048947 : Blo 1048611 1048947 := bstep (se 1 (by rfl) ⟨786710, by rfl⟩ : syracuseStep 1048947 = 1573421) B1573421
theorem B2589059 : Blo 1048611 2589059 := bstep (se 1 (by rfl) ⟨1941794, by rfl⟩ : syracuseStep 2589059 = 3883589) B3883589
theorem B1048963 : Blo 1048611 1048963 := bstep (se 1 (by rfl) ⟨786722, by rfl⟩ : syracuseStep 1048963 = 1573445) B1573445
theorem B1573265 : Blo 1048611 1573265 := bstep (se 2 (by rfl) ⟨589974, by rfl⟩ : syracuseStep 1573265 = 1179949) B1179949
theorem B1048979 : Blo 1048611 1048979 := bstep (se 1 (by rfl) ⟨786734, by rfl⟩ : syracuseStep 1048979 = 1573469) B1573469
theorem B1573283 : Blo 1048611 1573283 := bstep (se 1 (by rfl) ⟨1179962, by rfl⟩ : syracuseStep 1573283 = 2359925) B2359925
theorem B1048995 : Blo 1048611 1048995 := bstep (se 1 (by rfl) ⟨786746, by rfl⟩ : syracuseStep 1048995 = 1573493) B1573493
theorem B1049011 : Blo 1048611 1049011 := bstep (se 1 (by rfl) ⟨786758, by rfl⟩ : syracuseStep 1049011 = 1573517) B1573517
theorem B2425265 : Blo 1048611 2425265 := bstep (se 2 (by rfl) ⟨909474, by rfl⟩ : syracuseStep 2425265 = 1818949) B1818949
theorem B1573313 : Blo 1048611 1573313 := bstep (se 2 (by rfl) ⟨589992, by rfl⟩ : syracuseStep 1573313 = 1179985) B1179985
theorem B1049027 : Blo 1048611 1049027 := bstep (se 1 (by rfl) ⟨786770, by rfl⟩ : syracuseStep 1049027 = 1573541) B1573541
theorem B1573331 : Blo 1048611 1573331 := bstep (se 1 (by rfl) ⟨1179998, by rfl⟩ : syracuseStep 1573331 = 2359997) B2359997
theorem B1049043 : Blo 1048611 1049043 := bstep (se 1 (by rfl) ⟨786782, by rfl⟩ : syracuseStep 1049043 = 1573565) B1573565
theorem B1049059 : Blo 1048611 1049059 := bstep (se 1 (by rfl) ⟨786794, by rfl⟩ : syracuseStep 1049059 = 1573589) B1573589
theorem B1573361 : Blo 1048611 1573361 := bstep (se 2 (by rfl) ⟨590010, by rfl⟩ : syracuseStep 1573361 = 1180021) B1180021
theorem B1769971 : Blo 1048611 1769971 := bstep (se 1 (by rfl) ⟨1327478, by rfl⟩ : syracuseStep 1769971 = 2654957) B2654957
theorem B1180147 : Blo 1048611 1180147 := bstep (se 1 (by rfl) ⟨885110, by rfl⟩ : syracuseStep 1180147 = 1770221) B1770221
theorem B1049075 : Blo 1048611 1049075 := bstep (se 1 (by rfl) ⟨786806, by rfl⟩ : syracuseStep 1049075 = 1573613) B1573613
theorem B1573379 : Blo 1048611 1573379 := bstep (se 1 (by rfl) ⟨1180034, by rfl⟩ : syracuseStep 1573379 = 2360069) B2360069
theorem B1049091 : Blo 1048611 1049091 := bstep (se 1 (by rfl) ⟨786818, by rfl⟩ : syracuseStep 1049091 = 1573637) B1573637
theorem B1049107 : Blo 1048611 1049107 := bstep (se 1 (by rfl) ⟨786830, by rfl⟩ : syracuseStep 1049107 = 1573661) B1573661
theorem B1573409 : Blo 1048611 1573409 := bstep (se 2 (by rfl) ⟨590028, by rfl⟩ : syracuseStep 1573409 = 1180057) B1180057
theorem B1049123 : Blo 1048611 1049123 := bstep (se 1 (by rfl) ⟨786842, by rfl⟩ : syracuseStep 1049123 = 1573685) B1573685
theorem B1573427 : Blo 1048611 1573427 := bstep (se 1 (by rfl) ⟨1180070, by rfl⟩ : syracuseStep 1573427 = 2360141) B2360141
theorem B1049139 : Blo 1048611 1049139 := bstep (se 1 (by rfl) ⟨786854, by rfl⟩ : syracuseStep 1049139 = 1573709) B1573709
theorem B1049155 : Blo 1048611 1049155 := bstep (se 1 (by rfl) ⟨786866, by rfl⟩ : syracuseStep 1049155 = 1573733) B1573733
theorem B3539537 : Blo 1048611 3539537 := bstep (se 2 (by rfl) ⟨1327326, by rfl⟩ : syracuseStep 3539537 = 2654653) B2654653
theorem B2359889 : Blo 1048611 2359889 := bstep (se 2 (by rfl) ⟨884958, by rfl⟩ : syracuseStep 2359889 = 1769917) B1769917
theorem B1573457 : Blo 1048611 1573457 := bstep (se 2 (by rfl) ⟨590046, by rfl⟩ : syracuseStep 1573457 = 1180093) B1180093
theorem B1049171 : Blo 1048611 1049171 := bstep (se 1 (by rfl) ⟨786878, by rfl⟩ : syracuseStep 1049171 = 1573757) B1573757
theorem B2359907 : Blo 1048611 2359907 := bstep (se 1 (by rfl) ⟨1769930, by rfl⟩ : syracuseStep 2359907 = 3539861) B3539861
theorem B1573475 : Blo 1048611 1573475 := bstep (se 1 (by rfl) ⟨1180106, by rfl⟩ : syracuseStep 1573475 = 2360213) B2360213
theorem B1049187 : Blo 1048611 1049187 := bstep (se 1 (by rfl) ⟨786890, by rfl⟩ : syracuseStep 1049187 = 1573781) B1573781
theorem B1049203 : Blo 1048611 1049203 := bstep (se 1 (by rfl) ⟨786902, by rfl⟩ : syracuseStep 1049203 = 1573805) B1573805
theorem B1770113 : Blo 1048611 1770113 := bstep (se 2 (by rfl) ⟨663792, by rfl⟩ : syracuseStep 1770113 = 1327585) B1327585
theorem B1573505 : Blo 1048611 1573505 := bstep (se 2 (by rfl) ⟨590064, by rfl⟩ : syracuseStep 1573505 = 1180129) B1180129
theorem B1180291 : Blo 1048611 1180291 := bstep (se 1 (by rfl) ⟨885218, by rfl⟩ : syracuseStep 1180291 = 1770437) B1770437
theorem B1049219 : Blo 1048611 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B1573523 : Blo 1048611 1573523 := bstep (se 1 (by rfl) ⟨1180142, by rfl⟩ : syracuseStep 1573523 = 2360285) B2360285
theorem B1049235 : Blo 1048611 1049235 := bstep (se 1 (by rfl) ⟨786926, by rfl⟩ : syracuseStep 1049235 = 1573853) B1573853
theorem B1049251 : Blo 1048611 1049251 := bstep (se 1 (by rfl) ⟨786938, by rfl⟩ : syracuseStep 1049251 = 1573877) B1573877
theorem B1704611 : Blo 1048611 1704611 := bstep (se 1 (by rfl) ⟨1278458, by rfl⟩ : syracuseStep 1704611 = 2556917) B2556917
theorem B1573553 : Blo 1048611 1573553 := bstep (se 2 (by rfl) ⟨590082, by rfl⟩ : syracuseStep 1573553 = 1180165) B1180165
theorem B1049267 : Blo 1048611 1049267 := bstep (se 1 (by rfl) ⟨786950, by rfl⟩ : syracuseStep 1049267 = 1573901) B1573901
theorem B1573571 : Blo 1048611 1573571 := bstep (se 1 (by rfl) ⟨1180178, by rfl⟩ : syracuseStep 1573571 = 2360357) B2360357
theorem B1049283 : Blo 1048611 1049283 := bstep (se 1 (by rfl) ⟨786962, by rfl⟩ : syracuseStep 1049283 = 1573925) B1573925
theorem B1049299 : Blo 1048611 1049299 := bstep (se 1 (by rfl) ⟨786974, by rfl⟩ : syracuseStep 1049299 = 1573949) B1573949
theorem B1573601 : Blo 1048611 1573601 := bstep (se 2 (by rfl) ⟨590100, by rfl⟩ : syracuseStep 1573601 = 1180201) B1180201
theorem B1049315 : Blo 1048611 1049315 := bstep (se 1 (by rfl) ⟨786986, by rfl⟩ : syracuseStep 1049315 = 1573973) B1573973
theorem B1573619 : Blo 1048611 1573619 := bstep (se 1 (by rfl) ⟨1180214, by rfl⟩ : syracuseStep 1573619 = 2360429) B2360429
theorem B1049331 : Blo 1048611 1049331 := bstep (se 1 (by rfl) ⟨786998, by rfl⟩ : syracuseStep 1049331 = 1573997) B1573997
theorem B1770241 : Blo 1048611 1770241 := bstep (se 2 (by rfl) ⟨663840, by rfl⟩ : syracuseStep 1770241 = 1327681) B1327681
theorem B1049347 : Blo 1048611 1049347 := bstep (se 1 (by rfl) ⟨787010, by rfl⟩ : syracuseStep 1049347 = 1574021) B1574021
theorem B1573649 : Blo 1048611 1573649 := bstep (se 2 (by rfl) ⟨590118, by rfl⟩ : syracuseStep 1573649 = 1180237) B1180237
theorem B1180435 : Blo 1048611 1180435 := bstep (se 1 (by rfl) ⟨885326, by rfl⟩ : syracuseStep 1180435 = 1770653) B1770653
theorem B1049363 : Blo 1048611 1049363 := bstep (se 1 (by rfl) ⟨787022, by rfl⟩ : syracuseStep 1049363 = 1574045) B1574045
theorem B1770275 : Blo 1048611 1770275 := bstep (se 1 (by rfl) ⟨1327706, by rfl⟩ : syracuseStep 1770275 = 2655413) B2655413
theorem B1573667 : Blo 1048611 1573667 := bstep (se 1 (by rfl) ⟨1180250, by rfl⟩ : syracuseStep 1573667 = 2360501) B2360501
theorem B1049379 : Blo 1048611 1049379 := bstep (se 1 (by rfl) ⟨787034, by rfl⟩ : syracuseStep 1049379 = 1574069) B1574069
theorem B2523953 : Blo 1048611 2523953 := bstep (se 2 (by rfl) ⟨946482, by rfl⟩ : syracuseStep 2523953 = 1892965) B1892965
theorem B1049395 : Blo 1048611 1049395 := bstep (se 1 (by rfl) ⟨787046, by rfl⟩ : syracuseStep 1049395 = 1574093) B1574093
theorem B1573697 : Blo 1048611 1573697 := bstep (se 2 (by rfl) ⟨590136, by rfl⟩ : syracuseStep 1573697 = 1180273) B1180273
theorem B1049411 : Blo 1048611 1049411 := bstep (se 1 (by rfl) ⟨787058, by rfl⟩ : syracuseStep 1049411 = 1574117) B1574117
theorem B1573715 : Blo 1048611 1573715 := bstep (se 1 (by rfl) ⟨1180286, by rfl⟩ : syracuseStep 1573715 = 2360573) B2360573
theorem B1049427 : Blo 1048611 1049427 := bstep (se 1 (by rfl) ⟨787070, by rfl⟩ : syracuseStep 1049427 = 1574141) B1574141
theorem B1049443 : Blo 1048611 1049443 := bstep (se 1 (by rfl) ⟨787082, by rfl⟩ : syracuseStep 1049443 = 1574165) B1574165
theorem B2655089 : Blo 1048611 2655089 := bstep (se 2 (by rfl) ⟨995658, by rfl⟩ : syracuseStep 2655089 = 1991317) B1991317
theorem B2360177 : Blo 1048611 2360177 := bstep (se 2 (by rfl) ⟨885066, by rfl⟩ : syracuseStep 2360177 = 1770133) B1770133
theorem B1573745 : Blo 1048611 1573745 := bstep (se 2 (by rfl) ⟨590154, by rfl⟩ : syracuseStep 1573745 = 1180309) B1180309
theorem B1049459 : Blo 1048611 1049459 := bstep (se 1 (by rfl) ⟨787094, by rfl⟩ : syracuseStep 1049459 = 1574189) B1574189
theorem B2360195 : Blo 1048611 2360195 := bstep (se 1 (by rfl) ⟨1770146, by rfl⟩ : syracuseStep 2360195 = 3540293) B3540293
theorem B1573763 : Blo 1048611 1573763 := bstep (se 1 (by rfl) ⟨1180322, by rfl⟩ : syracuseStep 1573763 = 2360645) B2360645
theorem B1049475 : Blo 1048611 1049475 := bstep (se 1 (by rfl) ⟨787106, by rfl⟩ : syracuseStep 1049475 = 1574213) B1574213
theorem B1049491 : Blo 1048611 1049491 := bstep (se 1 (by rfl) ⟨787118, by rfl⟩ : syracuseStep 1049491 = 1574237) B1574237
theorem B1573793 : Blo 1048611 1573793 := bstep (se 2 (by rfl) ⟨590172, by rfl⟩ : syracuseStep 1573793 = 1180345) B1180345
theorem B2655139 : Blo 1048611 2655139 := bstep (se 1 (by rfl) ⟨1991354, by rfl⟩ : syracuseStep 2655139 = 3982709) B3982709
theorem B1770403 : Blo 1048611 1770403 := bstep (se 1 (by rfl) ⟨1327802, by rfl⟩ : syracuseStep 1770403 = 2655605) B2655605
theorem B1180579 : Blo 1048611 1180579 := bstep (se 1 (by rfl) ⟨885434, by rfl⟩ : syracuseStep 1180579 = 1770869) B1770869
theorem B1049507 : Blo 1048611 1049507 := bstep (se 1 (by rfl) ⟨787130, by rfl⟩ : syracuseStep 1049507 = 1574261) B1574261
theorem B1573811 : Blo 1048611 1573811 := bstep (se 1 (by rfl) ⟨1180358, by rfl⟩ : syracuseStep 1573811 = 2360717) B2360717
theorem B1049523 : Blo 1048611 1049523 := bstep (se 1 (by rfl) ⟨787142, by rfl⟩ : syracuseStep 1049523 = 1574285) B1574285
theorem B1049539 : Blo 1048611 1049539 := bstep (se 1 (by rfl) ⟨787154, by rfl⟩ : syracuseStep 1049539 = 1574309) B1574309
theorem B1573841 : Blo 1048611 1573841 := bstep (se 2 (by rfl) ⟨590190, by rfl⟩ : syracuseStep 1573841 = 1180381) B1180381
theorem B1049555 : Blo 1048611 1049555 := bstep (se 1 (by rfl) ⟨787166, by rfl⟩ : syracuseStep 1049555 = 1574333) B1574333
theorem B1573859 : Blo 1048611 1573859 := bstep (se 1 (by rfl) ⟨1180394, by rfl⟩ : syracuseStep 1573859 = 2360789) B2360789
theorem B1049571 : Blo 1048611 1049571 := bstep (se 1 (by rfl) ⟨787178, by rfl⟩ : syracuseStep 1049571 = 1574357) B1574357
theorem B1049587 : Blo 1048611 1049587 := bstep (se 1 (by rfl) ⟨787190, by rfl⟩ : syracuseStep 1049587 = 1574381) B1574381
theorem B1573889 : Blo 1048611 1573889 := bstep (se 2 (by rfl) ⟨590208, by rfl⟩ : syracuseStep 1573889 = 1180417) B1180417
theorem B1049603 : Blo 1048611 1049603 := bstep (se 1 (by rfl) ⟨787202, by rfl⟩ : syracuseStep 1049603 = 1574405) B1574405
theorem B1573907 : Blo 1048611 1573907 := bstep (se 1 (by rfl) ⟨1180430, by rfl⟩ : syracuseStep 1573907 = 2360861) B2360861
theorem B1049619 : Blo 1048611 1049619 := bstep (se 1 (by rfl) ⟨787214, by rfl⟩ : syracuseStep 1049619 = 1574429) B1574429
theorem B1049635 : Blo 1048611 1049635 := bstep (se 1 (by rfl) ⟨787226, by rfl⟩ : syracuseStep 1049635 = 1574453) B1574453
theorem B2655281 : Blo 1048611 2655281 := bstep (se 2 (by rfl) ⟨995730, by rfl⟩ : syracuseStep 2655281 = 1991461) B1991461
theorem B1770545 : Blo 1048611 1770545 := bstep (se 2 (by rfl) ⟨663954, by rfl⟩ : syracuseStep 1770545 = 1327909) B1327909
theorem B1573937 : Blo 1048611 1573937 := bstep (se 2 (by rfl) ⟨590226, by rfl⟩ : syracuseStep 1573937 = 1180453) B1180453
theorem B1180723 : Blo 1048611 1180723 := bstep (se 1 (by rfl) ⟨885542, by rfl⟩ : syracuseStep 1180723 = 1771085) B1771085
theorem B1049651 : Blo 1048611 1049651 := bstep (se 1 (by rfl) ⟨787238, by rfl⟩ : syracuseStep 1049651 = 1574477) B1574477
theorem B1573955 : Blo 1048611 1573955 := bstep (se 1 (by rfl) ⟨1180466, by rfl⟩ : syracuseStep 1573955 = 2360933) B2360933
theorem B1049667 : Blo 1048611 1049667 := bstep (se 1 (by rfl) ⟨787250, by rfl⟩ : syracuseStep 1049667 = 1574501) B1574501
theorem B1049683 : Blo 1048611 1049683 := bstep (se 1 (by rfl) ⟨787262, by rfl⟩ : syracuseStep 1049683 = 1574525) B1574525
theorem B1573985 : Blo 1048611 1573985 := bstep (se 2 (by rfl) ⟨590244, by rfl⟩ : syracuseStep 1573985 = 1180489) B1180489
theorem B1049699 : Blo 1048611 1049699 := bstep (se 1 (by rfl) ⟨787274, by rfl⟩ : syracuseStep 1049699 = 1574549) B1574549
theorem B3540077 : Blo 1048611 3540077 := bstep (se 3 (by rfl) ⟨663764, by rfl⟩ : syracuseStep 3540077 = 1327529) B1327529
theorem B2393201 : Blo 1048611 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B1574003 : Blo 1048611 1574003 := bstep (se 1 (by rfl) ⟨1180502, by rfl⟩ : syracuseStep 1574003 = 2361005) B2361005
theorem B1049715 : Blo 1048611 1049715 := bstep (se 1 (by rfl) ⟨787286, by rfl⟩ : syracuseStep 1049715 = 1574573) B1574573
theorem B1049731 : Blo 1048611 1049731 := bstep (se 1 (by rfl) ⟨787298, by rfl⟩ : syracuseStep 1049731 = 1574597) B1574597
theorem B2360465 : Blo 1048611 2360465 := bstep (se 2 (by rfl) ⟨885174, by rfl⟩ : syracuseStep 2360465 = 1770349) B1770349
theorem B1574033 : Blo 1048611 1574033 := bstep (se 2 (by rfl) ⟨590262, by rfl⟩ : syracuseStep 1574033 = 1180525) B1180525
theorem B1049747 : Blo 1048611 1049747 := bstep (se 1 (by rfl) ⟨787310, by rfl⟩ : syracuseStep 1049747 = 1574621) B1574621
theorem B3540131 : Blo 1048611 3540131 := bstep (se 1 (by rfl) ⟨2655098, by rfl⟩ : syracuseStep 3540131 = 5310197) B5310197
theorem B2360483 : Blo 1048611 2360483 := bstep (se 1 (by rfl) ⟨1770362, by rfl⟩ : syracuseStep 2360483 = 3540725) B3540725
theorem B1574051 : Blo 1048611 1574051 := bstep (se 1 (by rfl) ⟨1180538, by rfl⟩ : syracuseStep 1574051 = 2361077) B2361077
theorem B1049763 : Blo 1048611 1049763 := bstep (se 1 (by rfl) ⟨787322, by rfl⟩ : syracuseStep 1049763 = 1574645) B1574645
theorem B1770673 : Blo 1048611 1770673 := bstep (se 2 (by rfl) ⟨664002, by rfl⟩ : syracuseStep 1770673 = 1328005) B1328005
theorem B1049779 : Blo 1048611 1049779 := bstep (se 1 (by rfl) ⟨787334, by rfl⟩ : syracuseStep 1049779 = 1574669) B1574669
theorem B1574081 : Blo 1048611 1574081 := bstep (se 2 (by rfl) ⟨590280, by rfl⟩ : syracuseStep 1574081 = 1180561) B1180561
theorem B1180867 : Blo 1048611 1180867 := bstep (se 1 (by rfl) ⟨885650, by rfl⟩ : syracuseStep 1180867 = 1771301) B1771301
theorem B1049795 : Blo 1048611 1049795 := bstep (se 1 (by rfl) ⟨787346, by rfl⟩ : syracuseStep 1049795 = 1574693) B1574693
theorem B1770707 : Blo 1048611 1770707 := bstep (se 1 (by rfl) ⟨1328030, by rfl⟩ : syracuseStep 1770707 = 2656061) B2656061
theorem B1574099 : Blo 1048611 1574099 := bstep (se 1 (by rfl) ⟨1180574, by rfl⟩ : syracuseStep 1574099 = 2361149) B2361149
theorem B1049811 : Blo 1048611 1049811 := bstep (se 1 (by rfl) ⟨787358, by rfl⟩ : syracuseStep 1049811 = 1574717) B1574717
theorem B1049827 : Blo 1048611 1049827 := bstep (se 1 (by rfl) ⟨787370, by rfl⟩ : syracuseStep 1049827 = 1574741) B1574741
theorem B1574129 : Blo 1048611 1574129 := bstep (se 2 (by rfl) ⟨590298, by rfl⟩ : syracuseStep 1574129 = 1180597) B1180597
theorem B13468913 : Blo 1048611 13468913 := bstep (se 2 (by rfl) ⟨5050842, by rfl⟩ : syracuseStep 13468913 = 10101685) B10101685
theorem B1049843 : Blo 1048611 1049843 := bstep (se 1 (by rfl) ⟨787382, by rfl⟩ : syracuseStep 1049843 = 1574765) B1574765
theorem B1574147 : Blo 1048611 1574147 := bstep (se 1 (by rfl) ⟨1180610, by rfl⟩ : syracuseStep 1574147 = 2361221) B2361221
theorem B1049859 : Blo 1048611 1049859 := bstep (se 1 (by rfl) ⟨787394, by rfl⟩ : syracuseStep 1049859 = 1574789) B1574789
theorem B1049875 : Blo 1048611 1049875 := bstep (se 1 (by rfl) ⟨787406, by rfl⟩ : syracuseStep 1049875 = 1574813) B1574813
theorem B1574177 : Blo 1048611 1574177 := bstep (se 2 (by rfl) ⟨590316, by rfl⟩ : syracuseStep 1574177 = 1180633) B1180633
theorem B1049891 : Blo 1048611 1049891 := bstep (se 1 (by rfl) ⟨787418, by rfl⟩ : syracuseStep 1049891 = 1574837) B1574837
theorem B1574195 : Blo 1048611 1574195 := bstep (se 1 (by rfl) ⟨1180646, by rfl⟩ : syracuseStep 1574195 = 2361293) B2361293
theorem B1049907 : Blo 1048611 1049907 := bstep (se 1 (by rfl) ⟨787430, by rfl⟩ : syracuseStep 1049907 = 1574861) B1574861
theorem B1049923 : Blo 1048611 1049923 := bstep (se 1 (by rfl) ⟨787442, by rfl⟩ : syracuseStep 1049923 = 1574885) B1574885
theorem B1574225 : Blo 1048611 1574225 := bstep (se 2 (by rfl) ⟨590334, by rfl⟩ : syracuseStep 1574225 = 1180669) B1180669
theorem B1770835 : Blo 1048611 1770835 := bstep (se 1 (by rfl) ⟨1328126, by rfl⟩ : syracuseStep 1770835 = 2656253) B2656253
theorem B1181011 : Blo 1048611 1181011 := bstep (se 1 (by rfl) ⟨885758, by rfl⟩ : syracuseStep 1181011 = 1771517) B1771517
theorem B1049939 : Blo 1048611 1049939 := bstep (se 1 (by rfl) ⟨787454, by rfl⟩ : syracuseStep 1049939 = 1574909) B1574909
theorem B1574243 : Blo 1048611 1574243 := bstep (se 1 (by rfl) ⟨1180682, by rfl⟩ : syracuseStep 1574243 = 2361365) B2361365
theorem B1049955 : Blo 1048611 1049955 := bstep (se 1 (by rfl) ⟨787466, by rfl⟩ : syracuseStep 1049955 = 1574933) B1574933
theorem B1049971 : Blo 1048611 1049971 := bstep (se 1 (by rfl) ⟨787478, by rfl⟩ : syracuseStep 1049971 = 1574957) B1574957
theorem B1574273 : Blo 1048611 1574273 := bstep (se 2 (by rfl) ⟨590352, by rfl⟩ : syracuseStep 1574273 = 1180705) B1180705
theorem B1049987 : Blo 1048611 1049987 := bstep (se 1 (by rfl) ⟨787490, by rfl⟩ : syracuseStep 1049987 = 1574981) B1574981
theorem B1574291 : Blo 1048611 1574291 := bstep (se 1 (by rfl) ⟨1180718, by rfl⟩ : syracuseStep 1574291 = 2361437) B2361437
theorem B1050003 : Blo 1048611 1050003 := bstep (se 1 (by rfl) ⟨787502, by rfl⟩ : syracuseStep 1050003 = 1575005) B1575005
theorem B1050019 : Blo 1048611 1050019 := bstep (se 1 (by rfl) ⟨787514, by rfl⟩ : syracuseStep 1050019 = 1575029) B1575029
theorem B5309873 : Blo 1048611 5309873 := bstep (se 2 (by rfl) ⟨1991202, by rfl⟩ : syracuseStep 5309873 = 3982405) B3982405
theorem B3540401 : Blo 1048611 3540401 := bstep (se 2 (by rfl) ⟨1327650, by rfl⟩ : syracuseStep 3540401 = 2655301) B2655301
theorem B2360753 : Blo 1048611 2360753 := bstep (se 2 (by rfl) ⟨885282, by rfl⟩ : syracuseStep 2360753 = 1770565) B1770565
theorem B1574321 : Blo 1048611 1574321 := bstep (se 2 (by rfl) ⟨590370, by rfl⟩ : syracuseStep 1574321 = 1180741) B1180741
theorem B1050035 : Blo 1048611 1050035 := bstep (se 1 (by rfl) ⟨787526, by rfl⟩ : syracuseStep 1050035 = 1575053) B1575053
theorem B2360771 : Blo 1048611 2360771 := bstep (se 1 (by rfl) ⟨1770578, by rfl⟩ : syracuseStep 2360771 = 3541157) B3541157
theorem B1574339 : Blo 1048611 1574339 := bstep (se 1 (by rfl) ⟨1180754, by rfl⟩ : syracuseStep 1574339 = 2361509) B2361509
theorem B1050051 : Blo 1048611 1050051 := bstep (se 1 (by rfl) ⟨787538, by rfl⟩ : syracuseStep 1050051 = 1575077) B1575077
theorem B1050067 : Blo 1048611 1050067 := bstep (se 1 (by rfl) ⟨787550, by rfl⟩ : syracuseStep 1050067 = 1575101) B1575101
theorem B1770977 : Blo 1048611 1770977 := bstep (se 2 (by rfl) ⟨664116, by rfl⟩ : syracuseStep 1770977 = 1328233) B1328233
theorem B1574369 : Blo 1048611 1574369 := bstep (se 2 (by rfl) ⟨590388, by rfl⟩ : syracuseStep 1574369 = 1180777) B1180777
theorem B1181155 : Blo 1048611 1181155 := bstep (se 1 (by rfl) ⟨885866, by rfl⟩ : syracuseStep 1181155 = 1771733) B1771733
theorem B1050083 : Blo 1048611 1050083 := bstep (se 1 (by rfl) ⟨787562, by rfl⟩ : syracuseStep 1050083 = 1575125) B1575125
theorem B1574387 : Blo 1048611 1574387 := bstep (se 1 (by rfl) ⟨1180790, by rfl⟩ : syracuseStep 1574387 = 2361581) B2361581
theorem B1050099 : Blo 1048611 1050099 := bstep (se 1 (by rfl) ⟨787574, by rfl⟩ : syracuseStep 1050099 = 1575149) B1575149
theorem B1050115 : Blo 1048611 1050115 := bstep (se 1 (by rfl) ⟨787586, by rfl⟩ : syracuseStep 1050115 = 1575173) B1575173
theorem B1574417 : Blo 1048611 1574417 := bstep (se 2 (by rfl) ⟨590406, by rfl⟩ : syracuseStep 1574417 = 1180813) B1180813
theorem B1050131 : Blo 1048611 1050131 := bstep (se 1 (by rfl) ⟨787598, by rfl⟩ : syracuseStep 1050131 = 1575197) B1575197
theorem B1574435 : Blo 1048611 1574435 := bstep (se 1 (by rfl) ⟨1180826, by rfl⟩ : syracuseStep 1574435 = 2361653) B2361653
theorem B1050147 : Blo 1048611 1050147 := bstep (se 1 (by rfl) ⟨787610, by rfl⟩ : syracuseStep 1050147 = 1575221) B1575221
theorem B4490801 : Blo 1048611 4490801 := bstep (se 2 (by rfl) ⟨1684050, by rfl⟩ : syracuseStep 4490801 = 3368101) B3368101
theorem B1050163 : Blo 1048611 1050163 := bstep (se 1 (by rfl) ⟨787622, by rfl⟩ : syracuseStep 1050163 = 1575245) B1575245
theorem B1574465 : Blo 1048611 1574465 := bstep (se 2 (by rfl) ⟨590424, by rfl⟩ : syracuseStep 1574465 = 1180849) B1180849
theorem B1050179 : Blo 1048611 1050179 := bstep (se 1 (by rfl) ⟨787634, by rfl⟩ : syracuseStep 1050179 = 1575269) B1575269
theorem B1574483 : Blo 1048611 1574483 := bstep (se 1 (by rfl) ⟨1180862, by rfl⟩ : syracuseStep 1574483 = 2361725) B2361725
theorem B1050195 : Blo 1048611 1050195 := bstep (se 1 (by rfl) ⟨787646, by rfl⟩ : syracuseStep 1050195 = 1575293) B1575293
theorem B1771105 : Blo 1048611 1771105 := bstep (se 2 (by rfl) ⟨664164, by rfl⟩ : syracuseStep 1771105 = 1328329) B1328329
theorem B1050211 : Blo 1048611 1050211 := bstep (se 1 (by rfl) ⟨787658, by rfl⟩ : syracuseStep 1050211 = 1575317) B1575317
theorem B1574513 : Blo 1048611 1574513 := bstep (se 2 (by rfl) ⟨590442, by rfl⟩ : syracuseStep 1574513 = 1180885) B1180885
theorem B1181299 : Blo 1048611 1181299 := bstep (se 1 (by rfl) ⟨885974, by rfl⟩ : syracuseStep 1181299 = 1771949) B1771949
theorem B1050227 : Blo 1048611 1050227 := bstep (se 1 (by rfl) ⟨787670, by rfl⟩ : syracuseStep 1050227 = 1575341) B1575341
theorem B1771139 : Blo 1048611 1771139 := bstep (se 1 (by rfl) ⟨1328354, by rfl⟩ : syracuseStep 1771139 = 2656709) B2656709
theorem B1574531 : Blo 1048611 1574531 := bstep (se 1 (by rfl) ⟨1180898, by rfl⟩ : syracuseStep 1574531 = 2361797) B2361797
theorem B1050243 : Blo 1048611 1050243 := bstep (se 1 (by rfl) ⟨787682, by rfl⟩ : syracuseStep 1050243 = 1575365) B1575365
theorem B1050259 : Blo 1048611 1050259 := bstep (se 1 (by rfl) ⟨787694, by rfl⟩ : syracuseStep 1050259 = 1575389) B1575389
theorem B1574561 : Blo 1048611 1574561 := bstep (se 2 (by rfl) ⟨590460, by rfl⟩ : syracuseStep 1574561 = 1180921) B1180921
theorem B1050275 : Blo 1048611 1050275 := bstep (se 1 (by rfl) ⟨787706, by rfl⟩ : syracuseStep 1050275 = 1575413) B1575413
theorem B1574579 : Blo 1048611 1574579 := bstep (se 1 (by rfl) ⟨1180934, by rfl⟩ : syracuseStep 1574579 = 2361869) B2361869
theorem B1050291 : Blo 1048611 1050291 := bstep (se 1 (by rfl) ⟨787718, by rfl⟩ : syracuseStep 1050291 = 1575437) B1575437
theorem B1050307 : Blo 1048611 1050307 := bstep (se 1 (by rfl) ⟨787730, by rfl⟩ : syracuseStep 1050307 = 1575461) B1575461
theorem B2361041 : Blo 1048611 2361041 := bstep (se 2 (by rfl) ⟨885390, by rfl⟩ : syracuseStep 2361041 = 1770781) B1770781
theorem B1574609 : Blo 1048611 1574609 := bstep (se 2 (by rfl) ⟨590478, by rfl⟩ : syracuseStep 1574609 = 1180957) B1180957
theorem B1050323 : Blo 1048611 1050323 := bstep (se 1 (by rfl) ⟨787742, by rfl⟩ : syracuseStep 1050323 = 1575485) B1575485
theorem B2361059 : Blo 1048611 2361059 := bstep (se 1 (by rfl) ⟨1770794, by rfl⟩ : syracuseStep 2361059 = 3541589) B3541589
theorem B1574627 : Blo 1048611 1574627 := bstep (se 1 (by rfl) ⟨1180970, by rfl⟩ : syracuseStep 1574627 = 2361941) B2361941
theorem B1050339 : Blo 1048611 1050339 := bstep (se 1 (by rfl) ⟨787754, by rfl⟩ : syracuseStep 1050339 = 1575509) B1575509
theorem B1050355 : Blo 1048611 1050355 := bstep (se 1 (by rfl) ⟨787766, by rfl⟩ : syracuseStep 1050355 = 1575533) B1575533
theorem B1574657 : Blo 1048611 1574657 := bstep (se 2 (by rfl) ⟨590496, by rfl⟩ : syracuseStep 1574657 = 1180993) B1180993
theorem B1771267 : Blo 1048611 1771267 := bstep (se 1 (by rfl) ⟨1328450, by rfl⟩ : syracuseStep 1771267 = 2656901) B2656901
theorem B1181443 : Blo 1048611 1181443 := bstep (se 1 (by rfl) ⟨886082, by rfl⟩ : syracuseStep 1181443 = 1772165) B1772165
theorem B1050371 : Blo 1048611 1050371 := bstep (se 1 (by rfl) ⟨787778, by rfl⟩ : syracuseStep 1050371 = 1575557) B1575557
theorem B1574675 : Blo 1048611 1574675 := bstep (se 1 (by rfl) ⟨1181006, by rfl⟩ : syracuseStep 1574675 = 2362013) B2362013
theorem B1050387 : Blo 1048611 1050387 := bstep (se 1 (by rfl) ⟨787790, by rfl⟩ : syracuseStep 1050387 = 1575581) B1575581
theorem B1050403 : Blo 1048611 1050403 := bstep (se 1 (by rfl) ⟨787802, by rfl⟩ : syracuseStep 1050403 = 1575605) B1575605
theorem B1574705 : Blo 1048611 1574705 := bstep (se 2 (by rfl) ⟨590514, by rfl⟩ : syracuseStep 1574705 = 1181029) B1181029
theorem B1050419 : Blo 1048611 1050419 := bstep (se 1 (by rfl) ⟨787814, by rfl⟩ : syracuseStep 1050419 = 1575629) B1575629
theorem B1574723 : Blo 1048611 1574723 := bstep (se 1 (by rfl) ⟨1181042, by rfl⟩ : syracuseStep 1574723 = 2362085) B2362085
theorem B1050435 : Blo 1048611 1050435 := bstep (se 1 (by rfl) ⟨787826, by rfl⟩ : syracuseStep 1050435 = 1575653) B1575653
theorem B1050451 : Blo 1048611 1050451 := bstep (se 1 (by rfl) ⟨787838, by rfl⟩ : syracuseStep 1050451 = 1575677) B1575677
theorem B1574753 : Blo 1048611 1574753 := bstep (se 2 (by rfl) ⟨590532, by rfl⟩ : syracuseStep 1574753 = 1181065) B1181065
theorem B1050467 : Blo 1048611 1050467 := bstep (se 1 (by rfl) ⟨787850, by rfl⟩ : syracuseStep 1050467 = 1575701) B1575701
theorem B1574771 : Blo 1048611 1574771 := bstep (se 1 (by rfl) ⟨1181078, by rfl⟩ : syracuseStep 1574771 = 2362157) B2362157
theorem B1050483 : Blo 1048611 1050483 := bstep (se 1 (by rfl) ⟨787862, by rfl⟩ : syracuseStep 1050483 = 1575725) B1575725
theorem B1050499 : Blo 1048611 1050499 := bstep (se 1 (by rfl) ⟨787874, by rfl⟩ : syracuseStep 1050499 = 1575749) B1575749
theorem B1771409 : Blo 1048611 1771409 := bstep (se 2 (by rfl) ⟨664278, by rfl⟩ : syracuseStep 1771409 = 1328557) B1328557
theorem B1574801 : Blo 1048611 1574801 := bstep (se 2 (by rfl) ⟨590550, by rfl⟩ : syracuseStep 1574801 = 1181101) B1181101
theorem B1181587 : Blo 1048611 1181587 := bstep (se 1 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 1181587 = 1772381) B1772381
theorem B1050515 : Blo 1048611 1050515 := bstep (se 1 (by rfl) ⟨787886, by rfl⟩ : syracuseStep 1050515 = 1575773) B1575773
theorem B1574819 : Blo 1048611 1574819 := bstep (se 1 (by rfl) ⟨1181114, by rfl⟩ : syracuseStep 1574819 = 2362229) B2362229
theorem B1050531 : Blo 1048611 1050531 := bstep (se 1 (by rfl) ⟨787898, by rfl⟩ : syracuseStep 1050531 = 1575797) B1575797
theorem B1050547 : Blo 1048611 1050547 := bstep (se 1 (by rfl) ⟨787910, by rfl⟩ : syracuseStep 1050547 = 1575821) B1575821
theorem B1574849 : Blo 1048611 1574849 := bstep (se 2 (by rfl) ⟨590568, by rfl⟩ : syracuseStep 1574849 = 1181137) B1181137
theorem B1050563 : Blo 1048611 1050563 := bstep (se 1 (by rfl) ⟨787922, by rfl⟩ : syracuseStep 1050563 = 1575845) B1575845
theorem B3540941 : Blo 1048611 3540941 := bstep (se 3 (by rfl) ⟨663926, by rfl⟩ : syracuseStep 3540941 = 1327853) B1327853
theorem B1574867 : Blo 1048611 1574867 := bstep (se 1 (by rfl) ⟨1181150, by rfl⟩ : syracuseStep 1574867 = 2362301) B2362301
theorem B1050579 : Blo 1048611 1050579 := bstep (se 1 (by rfl) ⟨787934, by rfl⟩ : syracuseStep 1050579 = 1575869) B1575869
theorem B1050595 : Blo 1048611 1050595 := bstep (se 1 (by rfl) ⟨787946, by rfl⟩ : syracuseStep 1050595 = 1575893) B1575893
theorem B2361329 : Blo 1048611 2361329 := bstep (se 2 (by rfl) ⟨885498, by rfl⟩ : syracuseStep 2361329 = 1770997) B1770997
theorem B1574897 : Blo 1048611 1574897 := bstep (se 2 (by rfl) ⟨590586, by rfl⟩ : syracuseStep 1574897 = 1181173) B1181173
theorem B1050611 : Blo 1048611 1050611 := bstep (se 1 (by rfl) ⟨787958, by rfl⟩ : syracuseStep 1050611 = 1575917) B1575917
theorem B3540995 : Blo 1048611 3540995 := bstep (se 1 (by rfl) ⟨2655746, by rfl⟩ : syracuseStep 3540995 = 5311493) B5311493
theorem B2361347 : Blo 1048611 2361347 := bstep (se 1 (by rfl) ⟨1771010, by rfl⟩ : syracuseStep 2361347 = 3542021) B3542021
theorem B1574915 : Blo 1048611 1574915 := bstep (se 1 (by rfl) ⟨1181186, by rfl⟩ : syracuseStep 1574915 = 2362373) B2362373
theorem B1050627 : Blo 1048611 1050627 := bstep (se 1 (by rfl) ⟨787970, by rfl⟩ : syracuseStep 1050627 = 1575941) B1575941
theorem B2656273 : Blo 1048611 2656273 := bstep (se 2 (by rfl) ⟨996102, by rfl⟩ : syracuseStep 2656273 = 1992205) B1992205
theorem B1771537 : Blo 1048611 1771537 := bstep (se 2 (by rfl) ⟨664326, by rfl⟩ : syracuseStep 1771537 = 1328653) B1328653
theorem B1050643 : Blo 1048611 1050643 := bstep (se 1 (by rfl) ⟨787982, by rfl⟩ : syracuseStep 1050643 = 1575965) B1575965
theorem B1574945 : Blo 1048611 1574945 := bstep (se 2 (by rfl) ⟨590604, by rfl⟩ : syracuseStep 1574945 = 1181209) B1181209
theorem B1181731 : Blo 1048611 1181731 := bstep (se 1 (by rfl) ⟨886298, by rfl⟩ : syracuseStep 1181731 = 1772597) B1772597
theorem B1050659 : Blo 1048611 1050659 := bstep (se 1 (by rfl) ⟨787994, by rfl⟩ : syracuseStep 1050659 = 1575989) B1575989
theorem B1771571 : Blo 1048611 1771571 := bstep (se 1 (by rfl) ⟨1328678, by rfl⟩ : syracuseStep 1771571 = 2657357) B2657357
theorem B1574963 : Blo 1048611 1574963 := bstep (se 1 (by rfl) ⟨1181222, by rfl⟩ : syracuseStep 1574963 = 2362445) B2362445
theorem B1050675 : Blo 1048611 1050675 := bstep (se 1 (by rfl) ⟨788006, by rfl⟩ : syracuseStep 1050675 = 1576013) B1576013
theorem B1050691 : Blo 1048611 1050691 := bstep (se 1 (by rfl) ⟨788018, by rfl⟩ : syracuseStep 1050691 = 1576037) B1576037
theorem B1574993 : Blo 1048611 1574993 := bstep (se 2 (by rfl) ⟨590622, by rfl⟩ : syracuseStep 1574993 = 1181245) B1181245
theorem B1050707 : Blo 1048611 1050707 := bstep (se 1 (by rfl) ⟨788030, by rfl⟩ : syracuseStep 1050707 = 1576061) B1576061
theorem B1575011 : Blo 1048611 1575011 := bstep (se 1 (by rfl) ⟨1181258, by rfl⟩ : syracuseStep 1575011 = 2362517) B2362517
theorem B1050723 : Blo 1048611 1050723 := bstep (se 1 (by rfl) ⟨788042, by rfl⟩ : syracuseStep 1050723 = 1576085) B1576085
theorem B1050739 : Blo 1048611 1050739 := bstep (se 1 (by rfl) ⟨788054, by rfl⟩ : syracuseStep 1050739 = 1576109) B1576109
theorem B1575041 : Blo 1048611 1575041 := bstep (se 2 (by rfl) ⟨590640, by rfl⟩ : syracuseStep 1575041 = 1181281) B1181281
theorem B1050755 : Blo 1048611 1050755 := bstep (se 1 (by rfl) ⟨788066, by rfl⟩ : syracuseStep 1050755 = 1576133) B1576133
theorem B1575059 : Blo 1048611 1575059 := bstep (se 1 (by rfl) ⟨1181294, by rfl⟩ : syracuseStep 1575059 = 2362589) B2362589
theorem B1050771 : Blo 1048611 1050771 := bstep (se 1 (by rfl) ⟨788078, by rfl⟩ : syracuseStep 1050771 = 1576157) B1576157
theorem B1050787 : Blo 1048611 1050787 := bstep (se 1 (by rfl) ⟨788090, by rfl⟩ : syracuseStep 1050787 = 1576181) B1576181
theorem B1575089 : Blo 1048611 1575089 := bstep (se 2 (by rfl) ⟨590658, by rfl⟩ : syracuseStep 1575089 = 1181317) B1181317
theorem B1771699 : Blo 1048611 1771699 := bstep (se 1 (by rfl) ⟨1328774, by rfl⟩ : syracuseStep 1771699 = 2657549) B2657549
theorem B1181875 : Blo 1048611 1181875 := bstep (se 1 (by rfl) ⟨886406, by rfl⟩ : syracuseStep 1181875 = 1772813) B1772813
theorem B1050803 : Blo 1048611 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B1575107 : Blo 1048611 1575107 := bstep (se 1 (by rfl) ⟨1181330, by rfl⟩ : syracuseStep 1575107 = 2362661) B2362661
theorem B1050819 : Blo 1048611 1050819 := bstep (se 1 (by rfl) ⟨788114, by rfl⟩ : syracuseStep 1050819 = 1576229) B1576229
theorem B1050835 : Blo 1048611 1050835 := bstep (se 1 (by rfl) ⟨788126, by rfl⟩ : syracuseStep 1050835 = 1576253) B1576253
theorem B1575137 : Blo 1048611 1575137 := bstep (se 2 (by rfl) ⟨590676, by rfl⟩ : syracuseStep 1575137 = 1181353) B1181353
theorem B1050851 : Blo 1048611 1050851 := bstep (se 1 (by rfl) ⟨788138, by rfl⟩ : syracuseStep 1050851 = 1576277) B1576277
theorem B1575155 : Blo 1048611 1575155 := bstep (se 1 (by rfl) ⟨1181366, by rfl⟩ : syracuseStep 1575155 = 2362733) B2362733
theorem B1050867 : Blo 1048611 1050867 := bstep (se 1 (by rfl) ⟨788150, by rfl⟩ : syracuseStep 1050867 = 1576301) B1576301
theorem B1050883 : Blo 1048611 1050883 := bstep (se 1 (by rfl) ⟨788162, by rfl⟩ : syracuseStep 1050883 = 1576325) B1576325
theorem B3541265 : Blo 1048611 3541265 := bstep (se 2 (by rfl) ⟨1327974, by rfl⟩ : syracuseStep 3541265 = 2655949) B2655949
theorem B2361617 : Blo 1048611 2361617 := bstep (se 2 (by rfl) ⟨885606, by rfl⟩ : syracuseStep 2361617 = 1771213) B1771213
theorem B1575185 : Blo 1048611 1575185 := bstep (se 2 (by rfl) ⟨590694, by rfl⟩ : syracuseStep 1575185 = 1181389) B1181389
theorem B1050899 : Blo 1048611 1050899 := bstep (se 1 (by rfl) ⟨788174, by rfl⟩ : syracuseStep 1050899 = 1576349) B1576349
theorem B2656547 : Blo 1048611 2656547 := bstep (se 1 (by rfl) ⟨1992410, by rfl⟩ : syracuseStep 2656547 = 3984821) B3984821
theorem B2361635 : Blo 1048611 2361635 := bstep (se 1 (by rfl) ⟨1771226, by rfl⟩ : syracuseStep 2361635 = 3542453) B3542453
theorem B1575203 : Blo 1048611 1575203 := bstep (se 1 (by rfl) ⟨1181402, by rfl⟩ : syracuseStep 1575203 = 2362805) B2362805
theorem B1050915 : Blo 1048611 1050915 := bstep (se 1 (by rfl) ⟨788186, by rfl⟩ : syracuseStep 1050915 = 1576373) B1576373
theorem B1050931 : Blo 1048611 1050931 := bstep (se 1 (by rfl) ⟨788198, by rfl⟩ : syracuseStep 1050931 = 1576397) B1576397
theorem B1771841 : Blo 1048611 1771841 := bstep (se 2 (by rfl) ⟨664440, by rfl⟩ : syracuseStep 1771841 = 1328881) B1328881
theorem B1575233 : Blo 1048611 1575233 := bstep (se 2 (by rfl) ⟨590712, by rfl⟩ : syracuseStep 1575233 = 1181425) B1181425
theorem B1182019 : Blo 1048611 1182019 := bstep (se 1 (by rfl) ⟨886514, by rfl⟩ : syracuseStep 1182019 = 1773029) B1773029
theorem B1050947 : Blo 1048611 1050947 := bstep (se 1 (by rfl) ⟨788210, by rfl⟩ : syracuseStep 1050947 = 1576421) B1576421
theorem B1575251 : Blo 1048611 1575251 := bstep (se 1 (by rfl) ⟨1181438, by rfl⟩ : syracuseStep 1575251 = 2362877) B2362877
theorem B1050963 : Blo 1048611 1050963 := bstep (se 1 (by rfl) ⟨788222, by rfl⟩ : syracuseStep 1050963 = 1576445) B1576445
theorem B5048675 : Blo 1048611 5048675 := bstep (se 1 (by rfl) ⟨3786506, by rfl⟩ : syracuseStep 5048675 = 7573013) B7573013
theorem B1050979 : Blo 1048611 1050979 := bstep (se 1 (by rfl) ⟨788234, by rfl⟩ : syracuseStep 1050979 = 1576469) B1576469
theorem B1575281 : Blo 1048611 1575281 := bstep (se 2 (by rfl) ⟨590730, by rfl⟩ : syracuseStep 1575281 = 1181461) B1181461
theorem B1050995 : Blo 1048611 1050995 := bstep (se 1 (by rfl) ⟨788246, by rfl⟩ : syracuseStep 1050995 = 1576493) B1576493
theorem B1575299 : Blo 1048611 1575299 := bstep (se 1 (by rfl) ⟨1181474, by rfl⟩ : syracuseStep 1575299 = 2362949) B2362949
theorem B1051011 : Blo 1048611 1051011 := bstep (se 1 (by rfl) ⟨788258, by rfl⟩ : syracuseStep 1051011 = 1576517) B1576517
theorem B1051027 : Blo 1048611 1051027 := bstep (se 1 (by rfl) ⟨788270, by rfl⟩ : syracuseStep 1051027 = 1576541) B1576541
theorem B1575329 : Blo 1048611 1575329 := bstep (se 2 (by rfl) ⟨590748, by rfl⟩ : syracuseStep 1575329 = 1181497) B1181497
theorem B1051043 : Blo 1048611 1051043 := bstep (se 1 (by rfl) ⟨788282, by rfl⟩ : syracuseStep 1051043 = 1576565) B1576565
theorem B1575347 : Blo 1048611 1575347 := bstep (se 1 (by rfl) ⟨1181510, by rfl⟩ : syracuseStep 1575347 = 2363021) B2363021
theorem B1051059 : Blo 1048611 1051059 := bstep (se 1 (by rfl) ⟨788294, by rfl⟩ : syracuseStep 1051059 = 1576589) B1576589
theorem B1771969 : Blo 1048611 1771969 := bstep (se 2 (by rfl) ⟨664488, by rfl⟩ : syracuseStep 1771969 = 1328977) B1328977
theorem B1051075 : Blo 1048611 1051075 := bstep (se 1 (by rfl) ⟨788306, by rfl⟩ : syracuseStep 1051075 = 1576613) B1576613
theorem B1575377 : Blo 1048611 1575377 := bstep (se 2 (by rfl) ⟨590766, by rfl⟩ : syracuseStep 1575377 = 1181533) B1181533
theorem B1182163 : Blo 1048611 1182163 := bstep (se 1 (by rfl) ⟨886622, by rfl⟩ : syracuseStep 1182163 = 1773245) B1773245
theorem B1051091 : Blo 1048611 1051091 := bstep (se 1 (by rfl) ⟨788318, by rfl⟩ : syracuseStep 1051091 = 1576637) B1576637
theorem B2656739 : Blo 1048611 2656739 := bstep (se 1 (by rfl) ⟨1992554, by rfl⟩ : syracuseStep 2656739 = 3985109) B3985109
theorem B1772003 : Blo 1048611 1772003 := bstep (se 1 (by rfl) ⟨1329002, by rfl⟩ : syracuseStep 1772003 = 2658005) B2658005
theorem B1575395 : Blo 1048611 1575395 := bstep (se 1 (by rfl) ⟨1181546, by rfl⟩ : syracuseStep 1575395 = 2363093) B2363093
theorem B1051107 : Blo 1048611 1051107 := bstep (se 1 (by rfl) ⟨788330, by rfl⟩ : syracuseStep 1051107 = 1576661) B1576661
theorem B1051123 : Blo 1048611 1051123 := bstep (se 1 (by rfl) ⟨788342, by rfl⟩ : syracuseStep 1051123 = 1576685) B1576685
theorem B1575425 : Blo 1048611 1575425 := bstep (se 2 (by rfl) ⟨590784, by rfl⟩ : syracuseStep 1575425 = 1181569) B1181569
theorem B1051139 : Blo 1048611 1051139 := bstep (se 1 (by rfl) ⟨788354, by rfl⟩ : syracuseStep 1051139 = 1576709) B1576709
theorem B1575443 : Blo 1048611 1575443 := bstep (se 1 (by rfl) ⟨1181582, by rfl⟩ : syracuseStep 1575443 = 2363165) B2363165
theorem B1051155 : Blo 1048611 1051155 := bstep (se 1 (by rfl) ⟨788366, by rfl⟩ : syracuseStep 1051155 = 1576733) B1576733
theorem B1051171 : Blo 1048611 1051171 := bstep (se 1 (by rfl) ⟨788378, by rfl⟩ : syracuseStep 1051171 = 1576757) B1576757
theorem B2361905 : Blo 1048611 2361905 := bstep (se 2 (by rfl) ⟨885714, by rfl⟩ : syracuseStep 2361905 = 1771429) B1771429
theorem B1575473 : Blo 1048611 1575473 := bstep (se 2 (by rfl) ⟨590802, by rfl⟩ : syracuseStep 1575473 = 1181605) B1181605
theorem B1051187 : Blo 1048611 1051187 := bstep (se 1 (by rfl) ⟨788390, by rfl⟩ : syracuseStep 1051187 = 1576781) B1576781
theorem B2361923 : Blo 1048611 2361923 := bstep (se 1 (by rfl) ⟨1771442, by rfl⟩ : syracuseStep 2361923 = 3542885) B3542885
theorem B1575491 : Blo 1048611 1575491 := bstep (se 1 (by rfl) ⟨1181618, by rfl⟩ : syracuseStep 1575491 = 2363237) B2363237
theorem B1051203 : Blo 1048611 1051203 := bstep (se 1 (by rfl) ⟨788402, by rfl⟩ : syracuseStep 1051203 = 1576805) B1576805
theorem B1051219 : Blo 1048611 1051219 := bstep (se 1 (by rfl) ⟨788414, by rfl⟩ : syracuseStep 1051219 = 1576829) B1576829
theorem B1575521 : Blo 1048611 1575521 := bstep (se 2 (by rfl) ⟨590820, by rfl⟩ : syracuseStep 1575521 = 1181641) B1181641
theorem B1772131 : Blo 1048611 1772131 := bstep (se 1 (by rfl) ⟨1329098, by rfl⟩ : syracuseStep 1772131 = 2658197) B2658197
theorem B1182307 : Blo 1048611 1182307 := bstep (se 1 (by rfl) ⟨886730, by rfl⟩ : syracuseStep 1182307 = 1773461) B1773461
theorem B1051235 : Blo 1048611 1051235 := bstep (se 1 (by rfl) ⟨788426, by rfl⟩ : syracuseStep 1051235 = 1576853) B1576853
theorem B1575539 : Blo 1048611 1575539 := bstep (se 1 (by rfl) ⟨1181654, by rfl⟩ : syracuseStep 1575539 = 2363309) B2363309
theorem B1051251 : Blo 1048611 1051251 := bstep (se 1 (by rfl) ⟨788438, by rfl⟩ : syracuseStep 1051251 = 1576877) B1576877
theorem B1051267 : Blo 1048611 1051267 := bstep (se 1 (by rfl) ⟨788450, by rfl⟩ : syracuseStep 1051267 = 1576901) B1576901
theorem B1575569 : Blo 1048611 1575569 := bstep (se 2 (by rfl) ⟨590838, by rfl⟩ : syracuseStep 1575569 = 1181677) B1181677
theorem B1051283 : Blo 1048611 1051283 := bstep (se 1 (by rfl) ⟨788462, by rfl⟩ : syracuseStep 1051283 = 1576925) B1576925
theorem B1575587 : Blo 1048611 1575587 := bstep (se 1 (by rfl) ⟨1181690, by rfl⟩ : syracuseStep 1575587 = 2363381) B2363381
theorem B1051299 : Blo 1048611 1051299 := bstep (se 1 (by rfl) ⟨788474, by rfl⟩ : syracuseStep 1051299 = 1576949) B1576949
theorem B1051315 : Blo 1048611 1051315 := bstep (se 1 (by rfl) ⟨788486, by rfl⟩ : syracuseStep 1051315 = 1576973) B1576973
theorem B1575617 : Blo 1048611 1575617 := bstep (se 2 (by rfl) ⟨590856, by rfl⟩ : syracuseStep 1575617 = 1181713) B1181713
theorem B11340485 : Blo 1048611 11340485 := bstep (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) B2126341
theorem B8981189 : Blo 1048611 8981189 := bstep (se 4 (by rfl) ⟨841986, by rfl⟩ : syracuseStep 8981189 = 1683973) B1683973
theorem B1051331 : Blo 1048611 1051331 := bstep (se 1 (by rfl) ⟨788498, by rfl⟩ : syracuseStep 1051331 = 1576997) B1576997
theorem B1575635 : Blo 1048611 1575635 := bstep (se 1 (by rfl) ⟨1181726, by rfl⟩ : syracuseStep 1575635 = 2363453) B2363453
theorem B1051347 : Blo 1048611 1051347 := bstep (se 1 (by rfl) ⟨788510, by rfl⟩ : syracuseStep 1051347 = 1577021) B1577021
theorem B1051363 : Blo 1048611 1051363 := bstep (se 1 (by rfl) ⟨788522, by rfl⟩ : syracuseStep 1051363 = 1577045) B1577045
theorem B1772273 : Blo 1048611 1772273 := bstep (se 2 (by rfl) ⟨664602, by rfl⟩ : syracuseStep 1772273 = 1329205) B1329205
theorem B1575665 : Blo 1048611 1575665 := bstep (se 2 (by rfl) ⟨590874, by rfl⟩ : syracuseStep 1575665 = 1181749) B1181749
theorem B1182451 : Blo 1048611 1182451 := bstep (se 1 (by rfl) ⟨886838, by rfl⟩ : syracuseStep 1182451 = 1773677) B1773677
theorem B1051379 : Blo 1048611 1051379 := bstep (se 1 (by rfl) ⟨788534, by rfl⟩ : syracuseStep 1051379 = 1577069) B1577069
theorem B1575683 : Blo 1048611 1575683 := bstep (se 1 (by rfl) ⟨1181762, by rfl⟩ : syracuseStep 1575683 = 2363525) B2363525
theorem B1051395 : Blo 1048611 1051395 := bstep (se 1 (by rfl) ⟨788546, by rfl⟩ : syracuseStep 1051395 = 1577093) B1577093
theorem B1051411 : Blo 1048611 1051411 := bstep (se 1 (by rfl) ⟨788558, by rfl⟩ : syracuseStep 1051411 = 1577117) B1577117
theorem B1575713 : Blo 1048611 1575713 := bstep (se 2 (by rfl) ⟨590892, by rfl⟩ : syracuseStep 1575713 = 1181785) B1181785
theorem B1051427 : Blo 1048611 1051427 := bstep (se 1 (by rfl) ⟨788570, by rfl⟩ : syracuseStep 1051427 = 1577141) B1577141
theorem B3541805 : Blo 1048611 3541805 := bstep (se 3 (by rfl) ⟨664088, by rfl⟩ : syracuseStep 3541805 = 1328177) B1328177
theorem B1575731 : Blo 1048611 1575731 := bstep (se 1 (by rfl) ⟨1181798, by rfl⟩ : syracuseStep 1575731 = 2363597) B2363597
theorem B1051443 : Blo 1048611 1051443 := bstep (se 1 (by rfl) ⟨788582, by rfl⟩ : syracuseStep 1051443 = 1577165) B1577165
theorem B1051459 : Blo 1048611 1051459 := bstep (se 1 (by rfl) ⟨788594, by rfl⟩ : syracuseStep 1051459 = 1577189) B1577189
theorem B2362193 : Blo 1048611 2362193 := bstep (se 2 (by rfl) ⟨885822, by rfl⟩ : syracuseStep 2362193 = 1771645) B1771645
theorem B1575761 : Blo 1048611 1575761 := bstep (se 2 (by rfl) ⟨590910, by rfl⟩ : syracuseStep 1575761 = 1181821) B1181821
theorem B1051475 : Blo 1048611 1051475 := bstep (se 1 (by rfl) ⟨788606, by rfl⟩ : syracuseStep 1051475 = 1577213) B1577213
theorem B7965539 : Blo 1048611 7965539 := bstep (se 1 (by rfl) ⟨5974154, by rfl⟩ : syracuseStep 7965539 = 11948309) B11948309
theorem B5311331 : Blo 1048611 5311331 := bstep (se 1 (by rfl) ⟨3983498, by rfl⟩ : syracuseStep 5311331 = 7966997) B7966997
theorem B3541859 : Blo 1048611 3541859 := bstep (se 1 (by rfl) ⟨2656394, by rfl⟩ : syracuseStep 3541859 = 5312789) B5312789
theorem B2362211 : Blo 1048611 2362211 := bstep (se 1 (by rfl) ⟨1771658, by rfl⟩ : syracuseStep 2362211 = 3543317) B3543317
theorem B1575779 : Blo 1048611 1575779 := bstep (se 1 (by rfl) ⟨1181834, by rfl⟩ : syracuseStep 1575779 = 2363669) B2363669
theorem B1051491 : Blo 1048611 1051491 := bstep (se 1 (by rfl) ⟨788618, by rfl⟩ : syracuseStep 1051491 = 1577237) B1577237
theorem B1772401 : Blo 1048611 1772401 := bstep (se 2 (by rfl) ⟨664650, by rfl⟩ : syracuseStep 1772401 = 1329301) B1329301
theorem B1051507 : Blo 1048611 1051507 := bstep (se 1 (by rfl) ⟨788630, by rfl⟩ : syracuseStep 1051507 = 1577261) B1577261
theorem B1575809 : Blo 1048611 1575809 := bstep (se 2 (by rfl) ⟨590928, by rfl⟩ : syracuseStep 1575809 = 1181857) B1181857
theorem B1182595 : Blo 1048611 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B1051523 : Blo 1048611 1051523 := bstep (se 1 (by rfl) ⟨788642, by rfl⟩ : syracuseStep 1051523 = 1577285) B1577285
theorem B5049229 : Blo 1048611 5049229 := bstep (se 3 (by rfl) ⟨946730, by rfl⟩ : syracuseStep 5049229 = 1893461) B1893461
theorem B1772435 : Blo 1048611 1772435 := bstep (se 1 (by rfl) ⟨1329326, by rfl⟩ : syracuseStep 1772435 = 2658653) B2658653
theorem B1575827 : Blo 1048611 1575827 := bstep (se 1 (by rfl) ⟨1181870, by rfl⟩ : syracuseStep 1575827 = 2363741) B2363741
theorem B1051539 : Blo 1048611 1051539 := bstep (se 1 (by rfl) ⟨788654, by rfl⟩ : syracuseStep 1051539 = 1577309) B1577309
theorem B1051555 : Blo 1048611 1051555 := bstep (se 1 (by rfl) ⟨788666, by rfl⟩ : syracuseStep 1051555 = 1577333) B1577333
theorem B1575857 : Blo 1048611 1575857 := bstep (se 2 (by rfl) ⟨590946, by rfl⟩ : syracuseStep 1575857 = 1181893) B1181893
theorem B1051571 : Blo 1048611 1051571 := bstep (se 1 (by rfl) ⟨788678, by rfl⟩ : syracuseStep 1051571 = 1577357) B1577357
theorem B1575875 : Blo 1048611 1575875 := bstep (se 1 (by rfl) ⟨1181906, by rfl⟩ : syracuseStep 1575875 = 2363813) B2363813
theorem B1051587 : Blo 1048611 1051587 := bstep (se 1 (by rfl) ⟨788690, by rfl⟩ : syracuseStep 1051587 = 1577381) B1577381
theorem B1051603 : Blo 1048611 1051603 := bstep (se 1 (by rfl) ⟨788702, by rfl⟩ : syracuseStep 1051603 = 1577405) B1577405
theorem B1575905 : Blo 1048611 1575905 := bstep (se 2 (by rfl) ⟨590964, by rfl⟩ : syracuseStep 1575905 = 1181929) B1181929
theorem B1051619 : Blo 1048611 1051619 := bstep (se 1 (by rfl) ⟨788714, by rfl⟩ : syracuseStep 1051619 = 1577429) B1577429
theorem B1575923 : Blo 1048611 1575923 := bstep (se 1 (by rfl) ⟨1181942, by rfl⟩ : syracuseStep 1575923 = 2363885) B2363885
theorem B1051635 : Blo 1048611 1051635 := bstep (se 1 (by rfl) ⟨788726, by rfl⟩ : syracuseStep 1051635 = 1577453) B1577453
theorem B1051651 : Blo 1048611 1051651 := bstep (se 1 (by rfl) ⟨788738, by rfl⟩ : syracuseStep 1051651 = 1577477) B1577477
theorem B1575953 : Blo 1048611 1575953 := bstep (se 2 (by rfl) ⟨590982, by rfl⟩ : syracuseStep 1575953 = 1181965) B1181965
theorem B1772563 : Blo 1048611 1772563 := bstep (se 1 (by rfl) ⟨1329422, by rfl⟩ : syracuseStep 1772563 = 2658845) B2658845
theorem B1182739 : Blo 1048611 1182739 := bstep (se 1 (by rfl) ⟨887054, by rfl⟩ : syracuseStep 1182739 = 1774109) B1774109
theorem B1051667 : Blo 1048611 1051667 := bstep (se 1 (by rfl) ⟨788750, by rfl⟩ : syracuseStep 1051667 = 1577501) B1577501
theorem B1575971 : Blo 1048611 1575971 := bstep (se 1 (by rfl) ⟨1181978, by rfl⟩ : syracuseStep 1575971 = 2363957) B2363957
theorem B1051683 : Blo 1048611 1051683 := bstep (se 1 (by rfl) ⟨788762, by rfl⟩ : syracuseStep 1051683 = 1577525) B1577525
theorem B1051699 : Blo 1048611 1051699 := bstep (se 1 (by rfl) ⟨788774, by rfl⟩ : syracuseStep 1051699 = 1577549) B1577549
theorem B1576001 : Blo 1048611 1576001 := bstep (se 2 (by rfl) ⟨591000, by rfl⟩ : syracuseStep 1576001 = 1182001) B1182001
theorem B1051715 : Blo 1048611 1051715 := bstep (se 1 (by rfl) ⟨788786, by rfl⟩ : syracuseStep 1051715 = 1577573) B1577573
theorem B1576019 : Blo 1048611 1576019 := bstep (se 1 (by rfl) ⟨1182014, by rfl⟩ : syracuseStep 1576019 = 2364029) B2364029
theorem B1051731 : Blo 1048611 1051731 := bstep (se 1 (by rfl) ⟨788798, by rfl⟩ : syracuseStep 1051731 = 1577597) B1577597
theorem B1051747 : Blo 1048611 1051747 := bstep (se 1 (by rfl) ⟨788810, by rfl⟩ : syracuseStep 1051747 = 1577621) B1577621
theorem B3542129 : Blo 1048611 3542129 := bstep (se 2 (by rfl) ⟨1328298, by rfl⟩ : syracuseStep 3542129 = 2656597) B2656597
theorem B2362481 : Blo 1048611 2362481 := bstep (se 2 (by rfl) ⟨885930, by rfl⟩ : syracuseStep 2362481 = 1771861) B1771861
theorem B1576049 : Blo 1048611 1576049 := bstep (se 2 (by rfl) ⟨591018, by rfl⟩ : syracuseStep 1576049 = 1182037) B1182037
theorem B1051763 : Blo 1048611 1051763 := bstep (se 1 (by rfl) ⟨788822, by rfl⟩ : syracuseStep 1051763 = 1577645) B1577645
theorem B2362499 : Blo 1048611 2362499 := bstep (se 1 (by rfl) ⟨1771874, by rfl⟩ : syracuseStep 2362499 = 3543749) B3543749
theorem B1576067 : Blo 1048611 1576067 := bstep (se 1 (by rfl) ⟨1182050, by rfl⟩ : syracuseStep 1576067 = 2364101) B2364101
theorem B1051779 : Blo 1048611 1051779 := bstep (se 1 (by rfl) ⟨788834, by rfl⟩ : syracuseStep 1051779 = 1577669) B1577669
theorem B1051795 : Blo 1048611 1051795 := bstep (se 1 (by rfl) ⟨788846, by rfl⟩ : syracuseStep 1051795 = 1577693) B1577693
theorem B1772705 : Blo 1048611 1772705 := bstep (se 2 (by rfl) ⟨664764, by rfl⟩ : syracuseStep 1772705 = 1329529) B1329529
theorem B1576097 : Blo 1048611 1576097 := bstep (se 2 (by rfl) ⟨591036, by rfl⟩ : syracuseStep 1576097 = 1182073) B1182073
theorem B1182883 : Blo 1048611 1182883 := bstep (se 1 (by rfl) ⟨887162, by rfl⟩ : syracuseStep 1182883 = 1774325) B1774325
theorem B1051811 : Blo 1048611 1051811 := bstep (se 1 (by rfl) ⟨788858, by rfl⟩ : syracuseStep 1051811 = 1577717) B1577717
theorem B1576115 : Blo 1048611 1576115 := bstep (se 1 (by rfl) ⟨1182086, by rfl⟩ : syracuseStep 1576115 = 2364173) B2364173
theorem B1051827 : Blo 1048611 1051827 := bstep (se 1 (by rfl) ⟨788870, by rfl⟩ : syracuseStep 1051827 = 1577741) B1577741
theorem B1051843 : Blo 1048611 1051843 := bstep (se 1 (by rfl) ⟨788882, by rfl⟩ : syracuseStep 1051843 = 1577765) B1577765
theorem B4492493 : Blo 1048611 4492493 := bstep (se 3 (by rfl) ⟨842342, by rfl⟩ : syracuseStep 4492493 = 1684685) B1684685
theorem B1576145 : Blo 1048611 1576145 := bstep (se 2 (by rfl) ⟨591054, by rfl⟩ : syracuseStep 1576145 = 1182109) B1182109
theorem B1051859 : Blo 1048611 1051859 := bstep (se 1 (by rfl) ⟨788894, by rfl⟩ : syracuseStep 1051859 = 1577789) B1577789
theorem B1576163 : Blo 1048611 1576163 := bstep (se 1 (by rfl) ⟨1182122, by rfl⟩ : syracuseStep 1576163 = 2364245) B2364245
theorem B1051875 : Blo 1048611 1051875 := bstep (se 1 (by rfl) ⟨788906, by rfl⟩ : syracuseStep 1051875 = 1577813) B1577813
theorem B1051891 : Blo 1048611 1051891 := bstep (se 1 (by rfl) ⟨788918, by rfl⟩ : syracuseStep 1051891 = 1577837) B1577837
theorem B1576193 : Blo 1048611 1576193 := bstep (se 2 (by rfl) ⟨591072, by rfl⟩ : syracuseStep 1576193 = 1182145) B1182145
theorem B1051907 : Blo 1048611 1051907 := bstep (se 1 (by rfl) ⟨788930, by rfl⟩ : syracuseStep 1051907 = 1577861) B1577861
theorem B1576211 : Blo 1048611 1576211 := bstep (se 1 (by rfl) ⟨1182158, by rfl⟩ : syracuseStep 1576211 = 2364317) B2364317
theorem B1051923 : Blo 1048611 1051923 := bstep (se 1 (by rfl) ⟨788942, by rfl⟩ : syracuseStep 1051923 = 1577885) B1577885
theorem B1772833 : Blo 1048611 1772833 := bstep (se 2 (by rfl) ⟨664812, by rfl⟩ : syracuseStep 1772833 = 1329625) B1329625
theorem B1051939 : Blo 1048611 1051939 := bstep (se 1 (by rfl) ⟨788954, by rfl⟩ : syracuseStep 1051939 = 1577909) B1577909
theorem B1576241 : Blo 1048611 1576241 := bstep (se 2 (by rfl) ⟨591090, by rfl⟩ : syracuseStep 1576241 = 1182181) B1182181
theorem B1183027 : Blo 1048611 1183027 := bstep (se 1 (by rfl) ⟨887270, by rfl⟩ : syracuseStep 1183027 = 1774541) B1774541
theorem B1051955 : Blo 1048611 1051955 := bstep (se 1 (by rfl) ⟨788966, by rfl⟩ : syracuseStep 1051955 = 1577933) B1577933
theorem B1772867 : Blo 1048611 1772867 := bstep (se 1 (by rfl) ⟨1329650, by rfl⟩ : syracuseStep 1772867 = 2659301) B2659301
theorem B1576259 : Blo 1048611 1576259 := bstep (se 1 (by rfl) ⟨1182194, by rfl⟩ : syracuseStep 1576259 = 2364389) B2364389
theorem B1051971 : Blo 1048611 1051971 := bstep (se 1 (by rfl) ⟨788978, by rfl⟩ : syracuseStep 1051971 = 1577957) B1577957
theorem B1051987 : Blo 1048611 1051987 := bstep (se 1 (by rfl) ⟨788990, by rfl⟩ : syracuseStep 1051987 = 1577981) B1577981
theorem B1576289 : Blo 1048611 1576289 := bstep (se 2 (by rfl) ⟨591108, by rfl⟩ : syracuseStep 1576289 = 1182217) B1182217
theorem B1052003 : Blo 1048611 1052003 := bstep (se 1 (by rfl) ⟨789002, by rfl⟩ : syracuseStep 1052003 = 1578005) B1578005
theorem B8981873 : Blo 1048611 8981873 := bstep (se 2 (by rfl) ⟨3368202, by rfl⟩ : syracuseStep 8981873 = 6736405) B6736405
theorem B1576307 : Blo 1048611 1576307 := bstep (se 1 (by rfl) ⟨1182230, by rfl⟩ : syracuseStep 1576307 = 2364461) B2364461
theorem B1052019 : Blo 1048611 1052019 := bstep (se 1 (by rfl) ⟨789014, by rfl⟩ : syracuseStep 1052019 = 1578029) B1578029
theorem B1052035 : Blo 1048611 1052035 := bstep (se 1 (by rfl) ⟨789026, by rfl⟩ : syracuseStep 1052035 = 1578053) B1578053
theorem B2657681 : Blo 1048611 2657681 := bstep (se 2 (by rfl) ⟨996630, by rfl⟩ : syracuseStep 2657681 = 1993261) B1993261
theorem B2362769 : Blo 1048611 2362769 := bstep (se 2 (by rfl) ⟨886038, by rfl⟩ : syracuseStep 2362769 = 1772077) B1772077
theorem B1576337 : Blo 1048611 1576337 := bstep (se 2 (by rfl) ⟨591126, by rfl⟩ : syracuseStep 1576337 = 1182253) B1182253
theorem B1052051 : Blo 1048611 1052051 := bstep (se 1 (by rfl) ⟨789038, by rfl⟩ : syracuseStep 1052051 = 1578077) B1578077
theorem B2362787 : Blo 1048611 2362787 := bstep (se 1 (by rfl) ⟨1772090, by rfl⟩ : syracuseStep 2362787 = 3544181) B3544181
theorem B1576355 : Blo 1048611 1576355 := bstep (se 1 (by rfl) ⟨1182266, by rfl⟩ : syracuseStep 1576355 = 2364533) B2364533
theorem B1052067 : Blo 1048611 1052067 := bstep (se 1 (by rfl) ⟨789050, by rfl⟩ : syracuseStep 1052067 = 1578101) B1578101
theorem B1052083 : Blo 1048611 1052083 := bstep (se 1 (by rfl) ⟨789062, by rfl⟩ : syracuseStep 1052083 = 1578125) B1578125
theorem B1576385 : Blo 1048611 1576385 := bstep (se 2 (by rfl) ⟨591144, by rfl⟩ : syracuseStep 1576385 = 1182289) B1182289
theorem B2657731 : Blo 1048611 2657731 := bstep (se 1 (by rfl) ⟨1993298, by rfl⟩ : syracuseStep 2657731 = 3986597) B3986597
theorem B1772995 : Blo 1048611 1772995 := bstep (se 1 (by rfl) ⟨1329746, by rfl⟩ : syracuseStep 1772995 = 2659493) B2659493
theorem B1183171 : Blo 1048611 1183171 := bstep (se 1 (by rfl) ⟨887378, by rfl⟩ : syracuseStep 1183171 = 1774757) B1774757
theorem B1052099 : Blo 1048611 1052099 := bstep (se 1 (by rfl) ⟨789074, by rfl⟩ : syracuseStep 1052099 = 1578149) B1578149
theorem B1576403 : Blo 1048611 1576403 := bstep (se 1 (by rfl) ⟨1182302, by rfl⟩ : syracuseStep 1576403 = 2364605) B2364605
theorem B1052115 : Blo 1048611 1052115 := bstep (se 1 (by rfl) ⟨789086, by rfl⟩ : syracuseStep 1052115 = 1578173) B1578173
theorem B1052131 : Blo 1048611 1052131 := bstep (se 1 (by rfl) ⟨789098, by rfl⟩ : syracuseStep 1052131 = 1578197) B1578197
theorem B1576433 : Blo 1048611 1576433 := bstep (se 2 (by rfl) ⟨591162, by rfl⟩ : syracuseStep 1576433 = 1182325) B1182325
theorem B1052147 : Blo 1048611 1052147 := bstep (se 1 (by rfl) ⟨789110, by rfl⟩ : syracuseStep 1052147 = 1578221) B1578221
theorem B1576451 : Blo 1048611 1576451 := bstep (se 1 (by rfl) ⟨1182338, by rfl⟩ : syracuseStep 1576451 = 2364677) B2364677
theorem B1052163 : Blo 1048611 1052163 := bstep (se 1 (by rfl) ⟨789122, by rfl⟩ : syracuseStep 1052163 = 1578245) B1578245
theorem B1052179 : Blo 1048611 1052179 := bstep (se 1 (by rfl) ⟨789134, by rfl⟩ : syracuseStep 1052179 = 1578269) B1578269
theorem B1576481 : Blo 1048611 1576481 := bstep (se 2 (by rfl) ⟨591180, by rfl⟩ : syracuseStep 1576481 = 1182361) B1182361
theorem B1052195 : Blo 1048611 1052195 := bstep (se 1 (by rfl) ⟨789146, by rfl⟩ : syracuseStep 1052195 = 1578293) B1578293
theorem B1576499 : Blo 1048611 1576499 := bstep (se 1 (by rfl) ⟨1182374, by rfl⟩ : syracuseStep 1576499 = 2364749) B2364749
theorem B1052211 : Blo 1048611 1052211 := bstep (se 1 (by rfl) ⟨789158, by rfl⟩ : syracuseStep 1052211 = 1578317) B1578317
theorem B1052227 : Blo 1048611 1052227 := bstep (se 1 (by rfl) ⟨789170, by rfl⟩ : syracuseStep 1052227 = 1578341) B1578341
theorem B2657873 : Blo 1048611 2657873 := bstep (se 2 (by rfl) ⟨996702, by rfl⟩ : syracuseStep 2657873 = 1993405) B1993405
theorem B1773137 : Blo 1048611 1773137 := bstep (se 2 (by rfl) ⟨664926, by rfl⟩ : syracuseStep 1773137 = 1329853) B1329853
theorem B1576529 : Blo 1048611 1576529 := bstep (se 2 (by rfl) ⟨591198, by rfl⟩ : syracuseStep 1576529 = 1182397) B1182397
theorem B1183315 : Blo 1048611 1183315 := bstep (se 1 (by rfl) ⟨887486, by rfl⟩ : syracuseStep 1183315 = 1774973) B1774973
theorem B1052243 : Blo 1048611 1052243 := bstep (se 1 (by rfl) ⟨789182, by rfl⟩ : syracuseStep 1052243 = 1578365) B1578365
theorem B1576547 : Blo 1048611 1576547 := bstep (se 1 (by rfl) ⟨1182410, by rfl⟩ : syracuseStep 1576547 = 2364821) B2364821
theorem B1052259 : Blo 1048611 1052259 := bstep (se 1 (by rfl) ⟨789194, by rfl⟩ : syracuseStep 1052259 = 1578389) B1578389
theorem B1052275 : Blo 1048611 1052275 := bstep (se 1 (by rfl) ⟨789206, by rfl⟩ : syracuseStep 1052275 = 1578413) B1578413
theorem B1576577 : Blo 1048611 1576577 := bstep (se 2 (by rfl) ⟨591216, by rfl⟩ : syracuseStep 1576577 = 1182433) B1182433
theorem B1052291 : Blo 1048611 1052291 := bstep (se 1 (by rfl) ⟨789218, by rfl⟩ : syracuseStep 1052291 = 1578437) B1578437
theorem B5312141 : Blo 1048611 5312141 := bstep (se 3 (by rfl) ⟨996026, by rfl⟩ : syracuseStep 5312141 = 1992053) B1992053
theorem B3542669 : Blo 1048611 3542669 := bstep (se 3 (by rfl) ⟨664250, by rfl⟩ : syracuseStep 3542669 = 1328501) B1328501
theorem B13471373 : Blo 1048611 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B1576595 : Blo 1048611 1576595 := bstep (se 1 (by rfl) ⟨1182446, by rfl⟩ : syracuseStep 1576595 = 2364893) B2364893
theorem B1052307 : Blo 1048611 1052307 := bstep (se 1 (by rfl) ⟨789230, by rfl⟩ : syracuseStep 1052307 = 1578461) B1578461
theorem B1052323 : Blo 1048611 1052323 := bstep (se 1 (by rfl) ⟨789242, by rfl⟩ : syracuseStep 1052323 = 1578485) B1578485
theorem B2363057 : Blo 1048611 2363057 := bstep (se 2 (by rfl) ⟨886146, by rfl⟩ : syracuseStep 2363057 = 1772293) B1772293
theorem B1576625 : Blo 1048611 1576625 := bstep (se 2 (by rfl) ⟨591234, by rfl⟩ : syracuseStep 1576625 = 1182469) B1182469
theorem B1052339 : Blo 1048611 1052339 := bstep (se 1 (by rfl) ⟨789254, by rfl⟩ : syracuseStep 1052339 = 1578509) B1578509
theorem B3542723 : Blo 1048611 3542723 := bstep (se 1 (by rfl) ⟨2657042, by rfl⟩ : syracuseStep 3542723 = 5314085) B5314085
theorem B2363075 : Blo 1048611 2363075 := bstep (se 1 (by rfl) ⟨1772306, by rfl⟩ : syracuseStep 2363075 = 3544613) B3544613
theorem B1576643 : Blo 1048611 1576643 := bstep (se 1 (by rfl) ⟨1182482, by rfl⟩ : syracuseStep 1576643 = 2364965) B2364965
theorem B1052355 : Blo 1048611 1052355 := bstep (se 1 (by rfl) ⟨789266, by rfl⟩ : syracuseStep 1052355 = 1578533) B1578533
theorem B1773265 : Blo 1048611 1773265 := bstep (se 2 (by rfl) ⟨664974, by rfl⟩ : syracuseStep 1773265 = 1329949) B1329949
theorem B1052371 : Blo 1048611 1052371 := bstep (se 1 (by rfl) ⟨789278, by rfl⟩ : syracuseStep 1052371 = 1578557) B1578557
theorem B1576673 : Blo 1048611 1576673 := bstep (se 2 (by rfl) ⟨591252, by rfl⟩ : syracuseStep 1576673 = 1182505) B1182505
theorem B1183459 : Blo 1048611 1183459 := bstep (se 1 (by rfl) ⟨887594, by rfl⟩ : syracuseStep 1183459 = 1775189) B1775189
theorem B1052387 : Blo 1048611 1052387 := bstep (se 1 (by rfl) ⟨789290, by rfl⟩ : syracuseStep 1052387 = 1578581) B1578581
theorem B1773299 : Blo 1048611 1773299 := bstep (se 1 (by rfl) ⟨1329974, by rfl⟩ : syracuseStep 1773299 = 2659949) B2659949
theorem B1576691 : Blo 1048611 1576691 := bstep (se 1 (by rfl) ⟨1182518, by rfl⟩ : syracuseStep 1576691 = 2365037) B2365037
theorem B1052403 : Blo 1048611 1052403 := bstep (se 1 (by rfl) ⟨789302, by rfl⟩ : syracuseStep 1052403 = 1578605) B1578605
theorem B1052419 : Blo 1048611 1052419 := bstep (se 1 (by rfl) ⟨789314, by rfl⟩ : syracuseStep 1052419 = 1578629) B1578629
theorem B2690833 : Blo 1048611 2690833 := bstep (se 2 (by rfl) ⟨1009062, by rfl⟩ : syracuseStep 2690833 = 2018125) B2018125
theorem B1576721 : Blo 1048611 1576721 := bstep (se 2 (by rfl) ⟨591270, by rfl⟩ : syracuseStep 1576721 = 1182541) B1182541
theorem B1052435 : Blo 1048611 1052435 := bstep (se 1 (by rfl) ⟨789326, by rfl⟩ : syracuseStep 1052435 = 1578653) B1578653
theorem B2395939 : Blo 1048611 2395939 := bstep (se 1 (by rfl) ⟨1796954, by rfl⟩ : syracuseStep 2395939 = 3593909) B3593909
theorem B1576739 : Blo 1048611 1576739 := bstep (se 1 (by rfl) ⟨1182554, by rfl⟩ : syracuseStep 1576739 = 2365109) B2365109
theorem B1052451 : Blo 1048611 1052451 := bstep (se 1 (by rfl) ⟨789338, by rfl⟩ : syracuseStep 1052451 = 1578677) B1578677
theorem B1052467 : Blo 1048611 1052467 := bstep (se 1 (by rfl) ⟨789350, by rfl⟩ : syracuseStep 1052467 = 1578701) B1578701
theorem B1576769 : Blo 1048611 1576769 := bstep (se 2 (by rfl) ⟨591288, by rfl⟩ : syracuseStep 1576769 = 1182577) B1182577
theorem B1052483 : Blo 1048611 1052483 := bstep (se 1 (by rfl) ⟨789362, by rfl⟩ : syracuseStep 1052483 = 1578725) B1578725
theorem B1576787 : Blo 1048611 1576787 := bstep (se 1 (by rfl) ⟨1182590, by rfl⟩ : syracuseStep 1576787 = 2365181) B2365181
theorem B1052499 : Blo 1048611 1052499 := bstep (se 1 (by rfl) ⟨789374, by rfl⟩ : syracuseStep 1052499 = 1578749) B1578749
theorem B2527075 : Blo 1048611 2527075 := bstep (se 1 (by rfl) ⟨1895306, by rfl⟩ : syracuseStep 2527075 = 3790613) B3790613
theorem B1052515 : Blo 1048611 1052515 := bstep (se 1 (by rfl) ⟨789386, by rfl⟩ : syracuseStep 1052515 = 1578773) B1578773
theorem B1576817 : Blo 1048611 1576817 := bstep (se 2 (by rfl) ⟨591306, by rfl⟩ : syracuseStep 1576817 = 1182613) B1182613
theorem B1773427 : Blo 1048611 1773427 := bstep (se 1 (by rfl) ⟨1330070, by rfl⟩ : syracuseStep 1773427 = 2660141) B2660141
theorem B1183603 : Blo 1048611 1183603 := bstep (se 1 (by rfl) ⟨887702, by rfl⟩ : syracuseStep 1183603 = 1775405) B1775405
theorem B1052531 : Blo 1048611 1052531 := bstep (se 1 (by rfl) ⟨789398, by rfl⟩ : syracuseStep 1052531 = 1578797) B1578797
theorem B1576835 : Blo 1048611 1576835 := bstep (se 1 (by rfl) ⟨1182626, by rfl⟩ : syracuseStep 1576835 = 2365253) B2365253
theorem B1052547 : Blo 1048611 1052547 := bstep (se 1 (by rfl) ⟨789410, by rfl⟩ : syracuseStep 1052547 = 1578821) B1578821
theorem B1052563 : Blo 1048611 1052563 := bstep (se 1 (by rfl) ⟨789422, by rfl⟩ : syracuseStep 1052563 = 1578845) B1578845
theorem B1576865 : Blo 1048611 1576865 := bstep (se 2 (by rfl) ⟨591324, by rfl⟩ : syracuseStep 1576865 = 1182649) B1182649
theorem B1052579 : Blo 1048611 1052579 := bstep (se 1 (by rfl) ⟨789434, by rfl⟩ : syracuseStep 1052579 = 1578869) B1578869
theorem B1576883 : Blo 1048611 1576883 := bstep (se 1 (by rfl) ⟨1182662, by rfl⟩ : syracuseStep 1576883 = 2365325) B2365325
theorem B1052595 : Blo 1048611 1052595 := bstep (se 1 (by rfl) ⟨789446, by rfl⟩ : syracuseStep 1052595 = 1578893) B1578893
theorem B1052611 : Blo 1048611 1052611 := bstep (se 1 (by rfl) ⟨789458, by rfl⟩ : syracuseStep 1052611 = 1578917) B1578917
theorem B3542993 : Blo 1048611 3542993 := bstep (se 2 (by rfl) ⟨1328622, by rfl⟩ : syracuseStep 3542993 = 2657245) B2657245
theorem B2363345 : Blo 1048611 2363345 := bstep (se 2 (by rfl) ⟨886254, by rfl⟩ : syracuseStep 2363345 = 1772509) B1772509
theorem B1576913 : Blo 1048611 1576913 := bstep (se 2 (by rfl) ⟨591342, by rfl⟩ : syracuseStep 1576913 = 1182685) B1182685
theorem B2363363 : Blo 1048611 2363363 := bstep (se 1 (by rfl) ⟨1772522, by rfl⟩ : syracuseStep 2363363 = 3545045) B3545045
theorem B1576931 : Blo 1048611 1576931 := bstep (se 1 (by rfl) ⟨1182698, by rfl⟩ : syracuseStep 1576931 = 2365397) B2365397
theorem B1773569 : Blo 1048611 1773569 := bstep (se 2 (by rfl) ⟨665088, by rfl⟩ : syracuseStep 1773569 = 1330177) B1330177
theorem B1576961 : Blo 1048611 1576961 := bstep (se 2 (by rfl) ⟨591360, by rfl⟩ : syracuseStep 1576961 = 1182721) B1182721
theorem B1183747 : Blo 1048611 1183747 := bstep (se 1 (by rfl) ⟨887810, by rfl⟩ : syracuseStep 1183747 = 1775621) B1775621
theorem B6721541 : Blo 1048611 6721541 := bstep (se 4 (by rfl) ⟨630144, by rfl⟩ : syracuseStep 6721541 = 1260289) B1260289
theorem B1576979 : Blo 1048611 1576979 := bstep (se 1 (by rfl) ⟨1182734, by rfl⟩ : syracuseStep 1576979 = 2365469) B2365469
theorem B2527267 : Blo 1048611 2527267 := bstep (se 1 (by rfl) ⟨1895450, by rfl⟩ : syracuseStep 2527267 = 3790901) B3790901
theorem B1577009 : Blo 1048611 1577009 := bstep (se 2 (by rfl) ⟨591378, by rfl⟩ : syracuseStep 1577009 = 1182757) B1182757
theorem B1577027 : Blo 1048611 1577027 := bstep (se 1 (by rfl) ⟨1182770, by rfl⟩ : syracuseStep 1577027 = 2365541) B2365541
theorem B1577057 : Blo 1048611 1577057 := bstep (se 2 (by rfl) ⟨591396, by rfl⟩ : syracuseStep 1577057 = 1182793) B1182793
theorem B1577075 : Blo 1048611 1577075 := bstep (se 1 (by rfl) ⟨1182806, by rfl⟩ : syracuseStep 1577075 = 2365613) B2365613
theorem B1773697 : Blo 1048611 1773697 := bstep (se 2 (by rfl) ⟨665136, by rfl⟩ : syracuseStep 1773697 = 1330273) B1330273
theorem B1577105 : Blo 1048611 1577105 := bstep (se 2 (by rfl) ⟨591414, by rfl⟩ : syracuseStep 1577105 = 1182829) B1182829
theorem B1183891 : Blo 1048611 1183891 := bstep (se 1 (by rfl) ⟨887918, by rfl⟩ : syracuseStep 1183891 = 1775837) B1775837
theorem B1773731 : Blo 1048611 1773731 := bstep (se 1 (by rfl) ⟨1330298, by rfl⟩ : syracuseStep 1773731 = 2660597) B2660597
theorem B1577123 : Blo 1048611 1577123 := bstep (se 1 (by rfl) ⟨1182842, by rfl⟩ : syracuseStep 1577123 = 2365685) B2365685
theorem B1577153 : Blo 1048611 1577153 := bstep (se 2 (by rfl) ⟨591432, by rfl⟩ : syracuseStep 1577153 = 1182865) B1182865
theorem B1577171 : Blo 1048611 1577171 := bstep (se 1 (by rfl) ⟨1182878, by rfl⟩ : syracuseStep 1577171 = 2365757) B2365757
theorem B2363633 : Blo 1048611 2363633 := bstep (se 2 (by rfl) ⟨886362, by rfl⟩ : syracuseStep 2363633 = 1772725) B1772725
theorem B1577201 : Blo 1048611 1577201 := bstep (se 2 (by rfl) ⟨591450, by rfl⟩ : syracuseStep 1577201 = 1182901) B1182901
theorem B2363651 : Blo 1048611 2363651 := bstep (se 1 (by rfl) ⟨1772738, by rfl⟩ : syracuseStep 2363651 = 3545477) B3545477
theorem B1577219 : Blo 1048611 1577219 := bstep (se 1 (by rfl) ⟨1182914, by rfl⟩ : syracuseStep 1577219 = 2365829) B2365829
theorem B1577249 : Blo 1048611 1577249 := bstep (se 2 (by rfl) ⟨591468, by rfl⟩ : syracuseStep 1577249 = 1182937) B1182937
theorem B1773859 : Blo 1048611 1773859 := bstep (se 1 (by rfl) ⟨1330394, by rfl⟩ : syracuseStep 1773859 = 2660789) B2660789
theorem B1184035 : Blo 1048611 1184035 := bstep (se 1 (by rfl) ⟨888026, by rfl⟩ : syracuseStep 1184035 = 1776053) B1776053
theorem B5050673 : Blo 1048611 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B2527537 : Blo 1048611 2527537 := bstep (se 2 (by rfl) ⟨947826, by rfl⟩ : syracuseStep 2527537 = 1895653) B1895653
theorem B1577267 : Blo 1048611 1577267 := bstep (se 1 (by rfl) ⟨1182950, by rfl⟩ : syracuseStep 1577267 = 2365901) B2365901
theorem B1577297 : Blo 1048611 1577297 := bstep (se 2 (by rfl) ⟨591486, by rfl⟩ : syracuseStep 1577297 = 1182973) B1182973
theorem B1577315 : Blo 1048611 1577315 := bstep (se 1 (by rfl) ⟨1182986, by rfl⟩ : syracuseStep 1577315 = 2365973) B2365973
theorem B1577345 : Blo 1048611 1577345 := bstep (se 2 (by rfl) ⟨591504, by rfl⟩ : syracuseStep 1577345 = 1183009) B1183009
theorem B1577363 : Blo 1048611 1577363 := bstep (se 1 (by rfl) ⟨1183022, by rfl⟩ : syracuseStep 1577363 = 2366045) B2366045
theorem B1774001 : Blo 1048611 1774001 := bstep (se 2 (by rfl) ⟨665250, by rfl⟩ : syracuseStep 1774001 = 1330501) B1330501
theorem B1577393 : Blo 1048611 1577393 := bstep (se 2 (by rfl) ⟨591522, by rfl⟩ : syracuseStep 1577393 = 1183045) B1183045
theorem B1184179 : Blo 1048611 1184179 := bstep (se 1 (by rfl) ⟨888134, by rfl⟩ : syracuseStep 1184179 = 1776269) B1776269
theorem B1577411 : Blo 1048611 1577411 := bstep (se 1 (by rfl) ⟨1183058, by rfl⟩ : syracuseStep 1577411 = 2366117) B2366117
theorem B1577441 : Blo 1048611 1577441 := bstep (se 2 (by rfl) ⟨591540, by rfl⟩ : syracuseStep 1577441 = 1183081) B1183081
theorem B3543533 : Blo 1048611 3543533 := bstep (se 3 (by rfl) ⟨664412, by rfl⟩ : syracuseStep 3543533 = 1328825) B1328825
theorem B1577459 : Blo 1048611 1577459 := bstep (se 1 (by rfl) ⟨1183094, by rfl⟩ : syracuseStep 1577459 = 2366189) B2366189
theorem B2363921 : Blo 1048611 2363921 := bstep (se 2 (by rfl) ⟨886470, by rfl⟩ : syracuseStep 2363921 = 1772941) B1772941
theorem B1577489 : Blo 1048611 1577489 := bstep (se 2 (by rfl) ⟨591558, by rfl⟩ : syracuseStep 1577489 = 1183117) B1183117
theorem B3543587 : Blo 1048611 3543587 := bstep (se 1 (by rfl) ⟨2657690, by rfl⟩ : syracuseStep 3543587 = 5315381) B5315381
theorem B2363939 : Blo 1048611 2363939 := bstep (se 1 (by rfl) ⟨1772954, by rfl⟩ : syracuseStep 2363939 = 3545909) B3545909
theorem B1577507 : Blo 1048611 1577507 := bstep (se 1 (by rfl) ⟨1183130, by rfl⟩ : syracuseStep 1577507 = 2366261) B2366261
theorem B2658865 : Blo 1048611 2658865 := bstep (se 2 (by rfl) ⟨997074, by rfl⟩ : syracuseStep 2658865 = 1994149) B1994149
theorem B1774129 : Blo 1048611 1774129 := bstep (se 2 (by rfl) ⟨665298, by rfl⟩ : syracuseStep 1774129 = 1330597) B1330597
theorem B1577537 : Blo 1048611 1577537 := bstep (se 2 (by rfl) ⟨591576, by rfl⟩ : syracuseStep 1577537 = 1183153) B1183153
theorem B2986577 : Blo 1048611 2986577 := bstep (se 2 (by rfl) ⟨1119966, by rfl⟩ : syracuseStep 2986577 = 2239933) B2239933
theorem B1774163 : Blo 1048611 1774163 := bstep (se 1 (by rfl) ⟨1330622, by rfl⟩ : syracuseStep 1774163 = 2661245) B2661245
theorem B1577555 : Blo 1048611 1577555 := bstep (se 1 (by rfl) ⟨1183166, by rfl⟩ : syracuseStep 1577555 = 2366333) B2366333
theorem B1577585 : Blo 1048611 1577585 := bstep (se 2 (by rfl) ⟨591594, by rfl⟩ : syracuseStep 1577585 = 1183189) B1183189
theorem B1577603 : Blo 1048611 1577603 := bstep (se 1 (by rfl) ⟨1183202, by rfl⟩ : syracuseStep 1577603 = 2366405) B2366405
theorem B20189837 : Blo 1048611 20189837 := bstep (se 3 (by rfl) ⟨3785594, by rfl⟩ : syracuseStep 20189837 = 7571189) B7571189
theorem B23368333 : Blo 1048611 23368333 := bstep (se 3 (by rfl) ⟨4381562, by rfl⟩ : syracuseStep 23368333 = 8763125) B8763125
theorem B1577633 : Blo 1048611 1577633 := bstep (se 2 (by rfl) ⟨591612, by rfl⟩ : syracuseStep 1577633 = 1183225) B1183225
theorem B1577651 : Blo 1048611 1577651 := bstep (se 1 (by rfl) ⟨1183238, by rfl⟩ : syracuseStep 1577651 = 2366477) B2366477
theorem B1577681 : Blo 1048611 1577681 := bstep (se 2 (by rfl) ⟨591630, by rfl⟩ : syracuseStep 1577681 = 1183261) B1183261
theorem B1774291 : Blo 1048611 1774291 := bstep (se 1 (by rfl) ⟨1330718, by rfl⟩ : syracuseStep 1774291 = 2661437) B2661437
theorem B1577699 : Blo 1048611 1577699 := bstep (se 1 (by rfl) ⟨1183274, by rfl⟩ : syracuseStep 1577699 = 2366549) B2366549
theorem B1577729 : Blo 1048611 1577729 := bstep (se 2 (by rfl) ⟨591648, by rfl⟩ : syracuseStep 1577729 = 1183297) B1183297
theorem B1577747 : Blo 1048611 1577747 := bstep (se 1 (by rfl) ⟨1183310, by rfl⟩ : syracuseStep 1577747 = 2366621) B2366621
theorem B3543857 : Blo 1048611 3543857 := bstep (se 2 (by rfl) ⟨1328946, by rfl⟩ : syracuseStep 3543857 = 2657893) B2657893
theorem B2364209 : Blo 1048611 2364209 := bstep (se 2 (by rfl) ⟨886578, by rfl⟩ : syracuseStep 2364209 = 1773157) B1773157
theorem B1577777 : Blo 1048611 1577777 := bstep (se 2 (by rfl) ⟨591666, by rfl⟩ : syracuseStep 1577777 = 1183333) B1183333
theorem B2659139 : Blo 1048611 2659139 := bstep (se 1 (by rfl) ⟨1994354, by rfl⟩ : syracuseStep 2659139 = 3988709) B3988709
theorem B2364227 : Blo 1048611 2364227 := bstep (se 1 (by rfl) ⟨1773170, by rfl⟩ : syracuseStep 2364227 = 3546341) B3546341
theorem B1577795 : Blo 1048611 1577795 := bstep (se 1 (by rfl) ⟨1183346, by rfl⟩ : syracuseStep 1577795 = 2366693) B2366693
theorem B1774433 : Blo 1048611 1774433 := bstep (se 2 (by rfl) ⟨665412, by rfl⟩ : syracuseStep 1774433 = 1330825) B1330825
theorem B1577825 : Blo 1048611 1577825 := bstep (se 2 (by rfl) ⟨591684, by rfl⟩ : syracuseStep 1577825 = 1183369) B1183369
theorem B2528113 : Blo 1048611 2528113 := bstep (se 2 (by rfl) ⟨948042, by rfl⟩ : syracuseStep 2528113 = 1896085) B1896085
theorem B1577843 : Blo 1048611 1577843 := bstep (se 1 (by rfl) ⟨1183382, by rfl⟩ : syracuseStep 1577843 = 2366765) B2366765
theorem B1577873 : Blo 1048611 1577873 := bstep (se 2 (by rfl) ⟨591702, by rfl⟩ : syracuseStep 1577873 = 1183405) B1183405
theorem B1577891 : Blo 1048611 1577891 := bstep (se 1 (by rfl) ⟨1183418, by rfl⟩ : syracuseStep 1577891 = 2366837) B2366837
theorem B1577921 : Blo 1048611 1577921 := bstep (se 2 (by rfl) ⟨591720, by rfl⟩ : syracuseStep 1577921 = 1183441) B1183441
theorem B1577939 : Blo 1048611 1577939 := bstep (se 1 (by rfl) ⟨1183454, by rfl⟩ : syracuseStep 1577939 = 2366909) B2366909
theorem B1774561 : Blo 1048611 1774561 := bstep (se 2 (by rfl) ⟨665460, by rfl⟩ : syracuseStep 1774561 = 1330921) B1330921
theorem B1577969 : Blo 1048611 1577969 := bstep (se 2 (by rfl) ⟨591738, by rfl⟩ : syracuseStep 1577969 = 1183477) B1183477
theorem B2659331 : Blo 1048611 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B1774595 : Blo 1048611 1774595 := bstep (se 1 (by rfl) ⟨1330946, by rfl⟩ : syracuseStep 1774595 = 2661893) B2661893
theorem B1577987 : Blo 1048611 1577987 := bstep (se 1 (by rfl) ⟨1183490, by rfl⟩ : syracuseStep 1577987 = 2366981) B2366981
theorem B1578017 : Blo 1048611 1578017 := bstep (se 2 (by rfl) ⟨591756, by rfl⟩ : syracuseStep 1578017 = 1183513) B1183513
theorem B1578035 : Blo 1048611 1578035 := bstep (se 1 (by rfl) ⟨1183526, by rfl⟩ : syracuseStep 1578035 = 2367053) B2367053
theorem B2364497 : Blo 1048611 2364497 := bstep (se 2 (by rfl) ⟨886686, by rfl⟩ : syracuseStep 2364497 = 1773373) B1773373
theorem B1578065 : Blo 1048611 1578065 := bstep (se 2 (by rfl) ⟨591774, by rfl⟩ : syracuseStep 1578065 = 1183549) B1183549
theorem B2364515 : Blo 1048611 2364515 := bstep (se 1 (by rfl) ⟨1773386, by rfl⟩ : syracuseStep 2364515 = 3546773) B3546773
theorem B1578083 : Blo 1048611 1578083 := bstep (se 1 (by rfl) ⟨1183562, by rfl⟩ : syracuseStep 1578083 = 2367125) B2367125
theorem B1578113 : Blo 1048611 1578113 := bstep (se 2 (by rfl) ⟨591792, by rfl⟩ : syracuseStep 1578113 = 1183585) B1183585
theorem B1774723 : Blo 1048611 1774723 := bstep (se 1 (by rfl) ⟨1331042, by rfl⟩ : syracuseStep 1774723 = 2662085) B2662085
theorem B1578131 : Blo 1048611 1578131 := bstep (se 1 (by rfl) ⟨1183598, by rfl⟩ : syracuseStep 1578131 = 2367197) B2367197
theorem B1578161 : Blo 1048611 1578161 := bstep (se 2 (by rfl) ⟨591810, by rfl⟩ : syracuseStep 1578161 = 1183621) B1183621
theorem B1578179 : Blo 1048611 1578179 := bstep (se 1 (by rfl) ⟨1183634, by rfl⟩ : syracuseStep 1578179 = 2367269) B2367269
theorem B1578209 : Blo 1048611 1578209 := bstep (se 2 (by rfl) ⟨591828, by rfl⟩ : syracuseStep 1578209 = 1183657) B1183657
theorem B2528497 : Blo 1048611 2528497 := bstep (se 2 (by rfl) ⟨948186, by rfl⟩ : syracuseStep 2528497 = 1896373) B1896373
theorem B1578227 : Blo 1048611 1578227 := bstep (se 1 (by rfl) ⟨1183670, by rfl⟩ : syracuseStep 1578227 = 2367341) B2367341
theorem B1774865 : Blo 1048611 1774865 := bstep (se 2 (by rfl) ⟨665574, by rfl⟩ : syracuseStep 1774865 = 1331149) B1331149
theorem B1578257 : Blo 1048611 1578257 := bstep (se 2 (by rfl) ⟨591846, by rfl⟩ : syracuseStep 1578257 = 1183693) B1183693
theorem B1578275 : Blo 1048611 1578275 := bstep (se 1 (by rfl) ⟨1183706, by rfl⟩ : syracuseStep 1578275 = 2367413) B2367413
theorem B1578305 : Blo 1048611 1578305 := bstep (se 2 (by rfl) ⟨591864, by rfl⟩ : syracuseStep 1578305 = 1183729) B1183729
theorem B3544397 : Blo 1048611 3544397 := bstep (se 3 (by rfl) ⟨664574, by rfl⟩ : syracuseStep 3544397 = 1329149) B1329149
theorem B1578323 : Blo 1048611 1578323 := bstep (se 1 (by rfl) ⟨1183742, by rfl⟩ : syracuseStep 1578323 = 2367485) B2367485
theorem B7181681 : Blo 1048611 7181681 := bstep (se 2 (by rfl) ⟨2693130, by rfl⟩ : syracuseStep 7181681 = 5386261) B5386261
theorem B2364785 : Blo 1048611 2364785 := bstep (se 2 (by rfl) ⟨886794, by rfl⟩ : syracuseStep 2364785 = 1773589) B1773589
theorem B1578353 : Blo 1048611 1578353 := bstep (se 2 (by rfl) ⟨591882, by rfl⟩ : syracuseStep 1578353 = 1183765) B1183765
theorem B3544451 : Blo 1048611 3544451 := bstep (se 1 (by rfl) ⟨2658338, by rfl⟩ : syracuseStep 3544451 = 5316677) B5316677
theorem B2364803 : Blo 1048611 2364803 := bstep (se 1 (by rfl) ⟨1773602, by rfl⟩ : syracuseStep 2364803 = 3547205) B3547205
theorem B1578371 : Blo 1048611 1578371 := bstep (se 1 (by rfl) ⟨1183778, by rfl⟩ : syracuseStep 1578371 = 2367557) B2367557
theorem B1774993 : Blo 1048611 1774993 := bstep (se 2 (by rfl) ⟨665622, by rfl⟩ : syracuseStep 1774993 = 1331245) B1331245
theorem B1578401 : Blo 1048611 1578401 := bstep (se 2 (by rfl) ⟨591900, by rfl⟩ : syracuseStep 1578401 = 1183801) B1183801
theorem B1775027 : Blo 1048611 1775027 := bstep (se 1 (by rfl) ⟨1331270, by rfl⟩ : syracuseStep 1775027 = 2662541) B2662541
theorem B1578419 : Blo 1048611 1578419 := bstep (se 1 (by rfl) ⟨1183814, by rfl⟩ : syracuseStep 1578419 = 2367629) B2367629
theorem B1578449 : Blo 1048611 1578449 := bstep (se 2 (by rfl) ⟨591918, by rfl⟩ : syracuseStep 1578449 = 1183837) B1183837
theorem B1578467 : Blo 1048611 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B1578497 : Blo 1048611 1578497 := bstep (se 2 (by rfl) ⟨591936, by rfl⟩ : syracuseStep 1578497 = 1183873) B1183873
theorem B2987533 : Blo 1048611 2987533 := bstep (se 3 (by rfl) ⟨560162, by rfl⟩ : syracuseStep 2987533 = 1120325) B1120325
theorem B1578515 : Blo 1048611 1578515 := bstep (se 1 (by rfl) ⟨1183886, by rfl⟩ : syracuseStep 1578515 = 2367773) B2367773
theorem B1578545 : Blo 1048611 1578545 := bstep (se 2 (by rfl) ⟨591954, by rfl⟩ : syracuseStep 1578545 = 1183909) B1183909
theorem B1775155 : Blo 1048611 1775155 := bstep (se 1 (by rfl) ⟨1331366, by rfl⟩ : syracuseStep 1775155 = 2662733) B2662733
theorem B1578563 : Blo 1048611 1578563 := bstep (se 1 (by rfl) ⟨1183922, by rfl⟩ : syracuseStep 1578563 = 2367845) B2367845
theorem B1578593 : Blo 1048611 1578593 := bstep (se 2 (by rfl) ⟨591972, by rfl⟩ : syracuseStep 1578593 = 1183945) B1183945
theorem B2692721 : Blo 1048611 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B1578611 : Blo 1048611 1578611 := bstep (se 1 (by rfl) ⟨1183958, by rfl⟩ : syracuseStep 1578611 = 2367917) B2367917
theorem B3544721 : Blo 1048611 3544721 := bstep (se 2 (by rfl) ⟨1329270, by rfl⟩ : syracuseStep 3544721 = 2658541) B2658541
theorem B2365073 : Blo 1048611 2365073 := bstep (se 2 (by rfl) ⟨886902, by rfl⟩ : syracuseStep 2365073 = 1773805) B1773805
theorem B1578641 : Blo 1048611 1578641 := bstep (se 2 (by rfl) ⟨591990, by rfl⟩ : syracuseStep 1578641 = 1183981) B1183981
theorem B2365091 : Blo 1048611 2365091 := bstep (se 1 (by rfl) ⟨1773818, by rfl⟩ : syracuseStep 2365091 = 3547637) B3547637
theorem B1578659 : Blo 1048611 1578659 := bstep (se 1 (by rfl) ⟨1183994, by rfl⟩ : syracuseStep 1578659 = 2367989) B2367989
theorem B1775297 : Blo 1048611 1775297 := bstep (se 2 (by rfl) ⟨665736, by rfl⟩ : syracuseStep 1775297 = 1331473) B1331473
theorem B1578689 : Blo 1048611 1578689 := bstep (se 2 (by rfl) ⟨592008, by rfl⟩ : syracuseStep 1578689 = 1184017) B1184017
theorem B1578707 : Blo 1048611 1578707 := bstep (se 1 (by rfl) ⟨1184030, by rfl⟩ : syracuseStep 1578707 = 2368061) B2368061
theorem B2987761 : Blo 1048611 2987761 := bstep (se 2 (by rfl) ⟨1120410, by rfl⟩ : syracuseStep 2987761 = 2240821) B2240821
theorem B1578737 : Blo 1048611 1578737 := bstep (se 2 (by rfl) ⟨592026, by rfl⟩ : syracuseStep 1578737 = 1184053) B1184053
theorem B1578755 : Blo 1048611 1578755 := bstep (se 1 (by rfl) ⟨1184066, by rfl⟩ : syracuseStep 1578755 = 2368133) B2368133
theorem B1578785 : Blo 1048611 1578785 := bstep (se 2 (by rfl) ⟨592044, by rfl⟩ : syracuseStep 1578785 = 1184089) B1184089
theorem B1578803 : Blo 1048611 1578803 := bstep (se 1 (by rfl) ⟨1184102, by rfl⟩ : syracuseStep 1578803 = 2368205) B2368205
theorem B1775425 : Blo 1048611 1775425 := bstep (se 2 (by rfl) ⟨665784, by rfl⟩ : syracuseStep 1775425 = 1331569) B1331569
theorem B1578833 : Blo 1048611 1578833 := bstep (se 2 (by rfl) ⟨592062, by rfl⟩ : syracuseStep 1578833 = 1184125) B1184125
theorem B1775459 : Blo 1048611 1775459 := bstep (se 1 (by rfl) ⟨1331594, by rfl⟩ : syracuseStep 1775459 = 2663189) B2663189
theorem B1578851 : Blo 1048611 1578851 := bstep (se 1 (by rfl) ⟨1184138, by rfl⟩ : syracuseStep 1578851 = 2368277) B2368277
theorem B1578881 : Blo 1048611 1578881 := bstep (se 2 (by rfl) ⟨592080, by rfl⟩ : syracuseStep 1578881 = 1184161) B1184161
theorem B2987921 : Blo 1048611 2987921 := bstep (se 2 (by rfl) ⟨1120470, by rfl⟩ : syracuseStep 2987921 = 2240941) B2240941
theorem B1578899 : Blo 1048611 1578899 := bstep (se 1 (by rfl) ⟨1184174, by rfl⟩ : syracuseStep 1578899 = 2368349) B2368349
theorem B2660273 : Blo 1048611 2660273 := bstep (se 2 (by rfl) ⟨997602, by rfl⟩ : syracuseStep 2660273 = 1995205) B1995205
theorem B2365361 : Blo 1048611 2365361 := bstep (se 2 (by rfl) ⟨887010, by rfl⟩ : syracuseStep 2365361 = 1774021) B1774021
theorem B2365379 : Blo 1048611 2365379 := bstep (se 1 (by rfl) ⟨1774034, by rfl⟩ : syracuseStep 2365379 = 3548069) B3548069
theorem B5052365 : Blo 1048611 5052365 := bstep (se 3 (by rfl) ⟨947318, by rfl⟩ : syracuseStep 5052365 = 1894637) B1894637
theorem B2660323 : Blo 1048611 2660323 := bstep (se 1 (by rfl) ⟨1995242, by rfl⟩ : syracuseStep 2660323 = 3990485) B3990485
theorem B1775587 : Blo 1048611 1775587 := bstep (se 1 (by rfl) ⟨1331690, by rfl⟩ : syracuseStep 1775587 = 2663381) B2663381
theorem B2988035 : Blo 1048611 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B2660465 : Blo 1048611 2660465 := bstep (se 2 (by rfl) ⟨997674, by rfl⟩ : syracuseStep 2660465 = 1995349) B1995349
theorem B1775729 : Blo 1048611 1775729 := bstep (se 2 (by rfl) ⟨665898, by rfl⟩ : syracuseStep 1775729 = 1331797) B1331797
theorem B3545261 : Blo 1048611 3545261 := bstep (se 3 (by rfl) ⟨664736, by rfl⟩ : syracuseStep 3545261 = 1329473) B1329473
theorem B2365649 : Blo 1048611 2365649 := bstep (se 2 (by rfl) ⟨887118, by rfl⟩ : syracuseStep 2365649 = 1774237) B1774237
theorem B3545315 : Blo 1048611 3545315 := bstep (se 1 (by rfl) ⟨2658986, by rfl⟩ : syracuseStep 3545315 = 5317973) B5317973
theorem B2365667 : Blo 1048611 2365667 := bstep (se 1 (by rfl) ⟨1774250, by rfl⟩ : syracuseStep 2365667 = 3548501) B3548501
theorem B1775857 : Blo 1048611 1775857 := bstep (se 2 (by rfl) ⟨665946, by rfl⟩ : syracuseStep 1775857 = 1331893) B1331893
theorem B1775891 : Blo 1048611 1775891 := bstep (se 1 (by rfl) ⟨1331918, by rfl⟩ : syracuseStep 1775891 = 2663837) B2663837
theorem B1776019 : Blo 1048611 1776019 := bstep (se 1 (by rfl) ⟨1332014, by rfl⟩ : syracuseStep 1776019 = 2664029) B2664029
theorem B5315057 : Blo 1048611 5315057 := bstep (se 2 (by rfl) ⟨1993146, by rfl⟩ : syracuseStep 5315057 = 3986293) B3986293
theorem B3545585 : Blo 1048611 3545585 := bstep (se 2 (by rfl) ⟨1329594, by rfl⟩ : syracuseStep 3545585 = 2659189) B2659189
theorem B2365937 : Blo 1048611 2365937 := bstep (se 2 (by rfl) ⟨887226, by rfl⟩ : syracuseStep 2365937 = 1774453) B1774453
theorem B2365955 : Blo 1048611 2365955 := bstep (se 1 (by rfl) ⟨1774466, by rfl⟩ : syracuseStep 2365955 = 3548933) B3548933
theorem B1776161 : Blo 1048611 1776161 := bstep (se 2 (by rfl) ⟨666060, by rfl⟩ : syracuseStep 1776161 = 1332121) B1332121
theorem B1120915 : Blo 1048611 1120915 := bstep (se 1 (by rfl) ⟨840686, by rfl⟩ : syracuseStep 1120915 = 1681373) B1681373
theorem B2366225 : Blo 1048611 2366225 := bstep (se 2 (by rfl) ⟨887334, by rfl⟩ : syracuseStep 2366225 = 1774669) B1774669
theorem B2366243 : Blo 1048611 2366243 := bstep (se 1 (by rfl) ⟨1774682, by rfl⟩ : syracuseStep 2366243 = 3549365) B3549365
theorem B2989037 : Blo 1048611 2989037 := bstep (se 3 (by rfl) ⟨560444, by rfl⟩ : syracuseStep 2989037 = 1120889) B1120889
theorem B3546125 : Blo 1048611 3546125 := bstep (se 3 (by rfl) ⟨664898, by rfl⟩ : syracuseStep 3546125 = 1329797) B1329797
theorem B2366513 : Blo 1048611 2366513 := bstep (se 2 (by rfl) ⟨887442, by rfl⟩ : syracuseStep 2366513 = 1774885) B1774885
theorem B3546179 : Blo 1048611 3546179 := bstep (se 1 (by rfl) ⟨2659634, by rfl⟩ : syracuseStep 3546179 = 5319269) B5319269
theorem B2366531 : Blo 1048611 2366531 := bstep (se 1 (by rfl) ⟨1774898, by rfl⟩ : syracuseStep 2366531 = 3549797) B3549797
theorem B2661457 : Blo 1048611 2661457 := bstep (se 2 (by rfl) ⟨998046, by rfl⟩ : syracuseStep 2661457 = 1996093) B1996093
theorem B2989219 : Blo 1048611 2989219 := bstep (se 1 (by rfl) ⟨2241914, by rfl⟩ : syracuseStep 2989219 = 4483829) B4483829
theorem B2989379 : Blo 1048611 2989379 := bstep (se 1 (by rfl) ⟨2242034, by rfl⟩ : syracuseStep 2989379 = 4484069) B4484069
theorem B3546449 : Blo 1048611 3546449 := bstep (se 2 (by rfl) ⟨1329918, by rfl⟩ : syracuseStep 3546449 = 2659837) B2659837
theorem B2366801 : Blo 1048611 2366801 := bstep (se 2 (by rfl) ⟨887550, by rfl⟩ : syracuseStep 2366801 = 1775101) B1775101
theorem B2661731 : Blo 1048611 2661731 := bstep (se 1 (by rfl) ⟨1996298, by rfl⟩ : syracuseStep 2661731 = 3992597) B3992597
theorem B2366819 : Blo 1048611 2366819 := bstep (se 1 (by rfl) ⟨1775114, by rfl⟩ : syracuseStep 2366819 = 3550229) B3550229
theorem B2661923 : Blo 1048611 2661923 := bstep (se 1 (by rfl) ⟨1996442, by rfl⟩ : syracuseStep 2661923 = 3992885) B3992885
theorem B2367089 : Blo 1048611 2367089 := bstep (se 2 (by rfl) ⟨887658, by rfl⟩ : syracuseStep 2367089 = 1775317) B1775317
theorem B2367107 : Blo 1048611 2367107 := bstep (se 1 (by rfl) ⟨1775330, by rfl⟩ : syracuseStep 2367107 = 3550661) B3550661
theorem B6233861 : Blo 1048611 6233861 := bstep (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) B1168849
theorem B1515361 : Blo 1048611 1515361 := bstep (se 2 (by rfl) ⟨568260, by rfl⟩ : syracuseStep 1515361 = 1136521) B1136521
theorem B3546989 : Blo 1048611 3546989 := bstep (se 3 (by rfl) ⟨665060, by rfl⟩ : syracuseStep 3546989 = 1330121) B1330121
theorem B1122179 : Blo 1048611 1122179 := bstep (se 1 (by rfl) ⟨841634, by rfl⟩ : syracuseStep 1122179 = 1683269) B1683269
theorem B2367377 : Blo 1048611 2367377 := bstep (se 2 (by rfl) ⟨887766, by rfl⟩ : syracuseStep 2367377 = 1775533) B1775533
theorem B5316515 : Blo 1048611 5316515 := bstep (se 1 (by rfl) ⟨3987386, by rfl⟩ : syracuseStep 5316515 = 7974773) B7974773
theorem B3547043 : Blo 1048611 3547043 := bstep (se 1 (by rfl) ⟨2660282, by rfl⟩ : syracuseStep 3547043 = 5320565) B5320565
theorem B2367395 : Blo 1048611 2367395 := bstep (se 1 (by rfl) ⟨1775546, by rfl⟩ : syracuseStep 2367395 = 3551093) B3551093
theorem B7970885 : Blo 1048611 7970885 := bstep (se 4 (by rfl) ⟨747270, by rfl⟩ : syracuseStep 7970885 = 1494541) B1494541
theorem B3547313 : Blo 1048611 3547313 := bstep (se 2 (by rfl) ⟨1330242, by rfl⟩ : syracuseStep 3547313 = 2660485) B2660485
theorem B2367665 : Blo 1048611 2367665 := bstep (se 2 (by rfl) ⟨887874, by rfl⟩ : syracuseStep 2367665 = 1775749) B1775749
theorem B2367683 : Blo 1048611 2367683 := bstep (se 1 (by rfl) ⟨1775762, by rfl⟩ : syracuseStep 2367683 = 3551525) B3551525
theorem B2433233 : Blo 1048611 2433233 := bstep (se 2 (by rfl) ⟨912462, by rfl⟩ : syracuseStep 2433233 = 1824925) B1824925
theorem B7184645 : Blo 1048611 7184645 := bstep (se 4 (by rfl) ⟨673560, by rfl⟩ : syracuseStep 7184645 = 1347121) B1347121
theorem B2990449 : Blo 1048611 2990449 := bstep (se 2 (by rfl) ⟨1121418, by rfl⟩ : syracuseStep 2990449 = 2242837) B2242837
theorem B2662865 : Blo 1048611 2662865 := bstep (se 2 (by rfl) ⟨998574, by rfl⟩ : syracuseStep 2662865 = 1997149) B1997149
theorem B2367953 : Blo 1048611 2367953 := bstep (se 2 (by rfl) ⟨887982, by rfl⟩ : syracuseStep 2367953 = 1775965) B1775965
theorem B2367971 : Blo 1048611 2367971 := bstep (se 1 (by rfl) ⟨1775978, by rfl⟩ : syracuseStep 2367971 = 3551957) B3551957
theorem B2662915 : Blo 1048611 2662915 := bstep (se 1 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 2662915 = 3994373) B3994373
theorem B5677573 : Blo 1048611 5677573 := bstep (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) B1064545
theorem B1516099 : Blo 1048611 1516099 := bstep (se 1 (by rfl) ⟨1137074, by rfl⟩ : syracuseStep 1516099 = 2274149) B2274149
theorem B1122931 : Blo 1048611 1122931 := bstep (se 1 (by rfl) ⟨842198, by rfl⟩ : syracuseStep 1122931 = 1684397) B1684397
theorem B2663057 : Blo 1048611 2663057 := bstep (se 2 (by rfl) ⟨998646, by rfl⟩ : syracuseStep 2663057 = 1997293) B1997293
theorem B5317325 : Blo 1048611 5317325 := bstep (se 3 (by rfl) ⟨996998, by rfl⟩ : syracuseStep 5317325 = 1993997) B1993997
theorem B3547853 : Blo 1048611 3547853 := bstep (se 3 (by rfl) ⟨665222, by rfl⟩ : syracuseStep 3547853 = 1330445) B1330445
theorem B2368241 : Blo 1048611 2368241 := bstep (se 2 (by rfl) ⟨888090, by rfl⟩ : syracuseStep 2368241 = 1776181) B1776181
theorem B3547907 : Blo 1048611 3547907 := bstep (se 1 (by rfl) ⟨2660930, by rfl⟩ : syracuseStep 3547907 = 5321861) B5321861
theorem B2368259 : Blo 1048611 2368259 := bstep (se 1 (by rfl) ⟨1776194, by rfl⟩ : syracuseStep 2368259 = 3552389) B3552389
theorem B1680193 : Blo 1048611 1680193 := bstep (se 2 (by rfl) ⟨630072, by rfl⟩ : syracuseStep 1680193 = 1260145) B1260145
theorem B3548177 : Blo 1048611 3548177 := bstep (se 2 (by rfl) ⟨1330566, by rfl⟩ : syracuseStep 3548177 = 2661133) B2661133
theorem B5973061 : Blo 1048611 5973061 := bstep (se 4 (by rfl) ⟨559974, by rfl⟩ : syracuseStep 5973061 = 1119949) B1119949
theorem B3548717 : Blo 1048611 3548717 := bstep (se 3 (by rfl) ⟨665384, by rfl⟩ : syracuseStep 3548717 = 1330769) B1330769
theorem B1680995 : Blo 1048611 1680995 := bstep (se 1 (by rfl) ⟨1260746, by rfl⟩ : syracuseStep 1680995 = 2521493) B2521493
theorem B3548771 : Blo 1048611 3548771 := bstep (se 1 (by rfl) ⟨2661578, by rfl⟩ : syracuseStep 3548771 = 5323157) B5323157
theorem B2991725 : Blo 1048611 2991725 := bstep (se 3 (by rfl) ⟨560948, by rfl⟩ : syracuseStep 2991725 = 1121897) B1121897
theorem B2664049 : Blo 1048611 2664049 := bstep (se 2 (by rfl) ⟨999018, by rfl⟩ : syracuseStep 2664049 = 1998037) B1998037
theorem B2991907 : Blo 1048611 2991907 := bstep (se 1 (by rfl) ⟨2243930, by rfl⟩ : syracuseStep 2991907 = 4487861) B4487861
theorem B2991953 : Blo 1048611 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B3549041 : Blo 1048611 3549041 := bstep (se 2 (by rfl) ⟨1330890, by rfl⟩ : syracuseStep 3549041 = 2661781) B2661781
theorem B2664323 : Blo 1048611 2664323 := bstep (se 1 (by rfl) ⟨1998242, by rfl⟩ : syracuseStep 2664323 = 3996485) B3996485
theorem B11380661 : Blo 1048611 11380661 := bstep (se 5 (by rfl) ⟨533468, by rfl⟩ : syracuseStep 11380661 = 1066937) B1066937
theorem B1681507 : Blo 1048611 1681507 := bstep (se 1 (by rfl) ⟨1261130, by rfl⟩ : syracuseStep 1681507 = 2522261) B2522261
theorem B8530019 : Blo 1048611 8530019 := bstep (se 1 (by rfl) ⟨6397514, by rfl⟩ : syracuseStep 8530019 = 12795029) B12795029
theorem B1419425 : Blo 1048611 1419425 := bstep (se 2 (by rfl) ⟨532284, by rfl⟩ : syracuseStep 1419425 = 1064569) B1064569
theorem B3549581 : Blo 1048611 3549581 := bstep (se 3 (by rfl) ⟨665546, by rfl⟩ : syracuseStep 3549581 = 1331093) B1331093
theorem B1419697 : Blo 1048611 1419697 := bstep (se 2 (by rfl) ⟨532386, by rfl⟩ : syracuseStep 1419697 = 1064773) B1064773
theorem B3549635 : Blo 1048611 3549635 := bstep (se 1 (by rfl) ⟨2662226, by rfl⟩ : syracuseStep 3549635 = 5324453) B5324453
theorem B26913221 : Blo 1048611 26913221 := bstep (se 4 (by rfl) ⟨2523114, by rfl⟩ : syracuseStep 26913221 = 5046229) B5046229
theorem B16394723 : Blo 1048611 16394723 := bstep (se 1 (by rfl) ⟨12296042, by rfl⟩ : syracuseStep 16394723 = 24592085) B24592085
theorem B3648077 : Blo 1048611 3648077 := bstep (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) B1368029
theorem B1682051 : Blo 1048611 1682051 := bstep (se 1 (by rfl) ⟨1261538, by rfl⟩ : syracuseStep 1682051 = 2523077) B2523077
theorem B3549905 : Blo 1048611 3549905 := bstep (se 2 (by rfl) ⟨1331214, by rfl⟩ : syracuseStep 3549905 = 2662429) B2662429
theorem B7383821 : Blo 1048611 7383821 := bstep (se 3 (by rfl) ⟨1384466, by rfl⟩ : syracuseStep 7383821 = 2768933) B2768933
theorem B1682225 : Blo 1048611 1682225 := bstep (se 2 (by rfl) ⟨630834, by rfl⟩ : syracuseStep 1682225 = 1261669) B1261669
theorem B4926307 : Blo 1048611 4926307 := bstep (se 1 (by rfl) ⟨3694730, by rfl⟩ : syracuseStep 4926307 = 7389461) B7389461
theorem B14560181 : Blo 1048611 14560181 := bstep (se 5 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 14560181 = 1365017) B1365017
theorem B3845069 : Blo 1048611 3845069 := bstep (se 3 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 3845069 = 1441901) B1441901
theorem B5975045 : Blo 1048611 5975045 := bstep (se 4 (by rfl) ⟨560160, by rfl⟩ : syracuseStep 5975045 = 1120321) B1120321
theorem B11971637 : Blo 1048611 11971637 := bstep (se 5 (by rfl) ⟨561170, by rfl⟩ : syracuseStep 11971637 = 1122341) B1122341
theorem B18197617 : Blo 1048611 18197617 := bstep (se 2 (by rfl) ⟨6824106, by rfl⟩ : syracuseStep 18197617 = 13648213) B13648213
theorem B3550445 : Blo 1048611 3550445 := bstep (se 3 (by rfl) ⟨665708, by rfl⟩ : syracuseStep 3550445 = 1331417) B1331417
theorem B8989937 : Blo 1048611 8989937 := bstep (se 2 (by rfl) ⟨3371226, by rfl⟩ : syracuseStep 8989937 = 6742453) B6742453
theorem B2993411 : Blo 1048611 2993411 := bstep (se 1 (by rfl) ⟨2245058, by rfl⟩ : syracuseStep 2993411 = 4490117) B4490117
theorem B3550499 : Blo 1048611 3550499 := bstep (se 1 (by rfl) ⟨2662874, by rfl⟩ : syracuseStep 3550499 = 5325749) B5325749
theorem B2698705 : Blo 1048611 2698705 := bstep (se 2 (by rfl) ⟨1012014, by rfl⟩ : syracuseStep 2698705 = 2024029) B2024029
theorem B5320241 : Blo 1048611 5320241 := bstep (se 2 (by rfl) ⟨1995090, by rfl⟩ : syracuseStep 5320241 = 3990181) B3990181
theorem B3550769 : Blo 1048611 3550769 := bstep (se 2 (by rfl) ⟨1331538, by rfl⟩ : syracuseStep 3550769 = 2663077) B2663077
theorem B13446769 : Blo 1048611 13446769 := bstep (se 2 (by rfl) ⟨5042538, by rfl⟩ : syracuseStep 13446769 = 10085077) B10085077
theorem B5746403 : Blo 1048611 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B1421123 : Blo 1048611 1421123 := bstep (se 1 (by rfl) ⟨1065842, by rfl⟩ : syracuseStep 1421123 = 2131685) B2131685
theorem B2240369 : Blo 1048611 2240369 := bstep (se 2 (by rfl) ⟨840138, by rfl⟩ : syracuseStep 2240369 = 1680277) B1680277
theorem B4042637 : Blo 1048611 4042637 := bstep (se 3 (by rfl) ⟨757994, by rfl⟩ : syracuseStep 4042637 = 1515989) B1515989
theorem B3190691 : Blo 1048611 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B3551309 : Blo 1048611 3551309 := bstep (se 3 (by rfl) ⟨665870, by rfl⟩ : syracuseStep 3551309 = 1331741) B1331741
theorem B3551363 : Blo 1048611 3551363 := bstep (se 1 (by rfl) ⟨2663522, by rfl⟩ : syracuseStep 3551363 = 5327045) B5327045
theorem B3551633 : Blo 1048611 3551633 := bstep (se 2 (by rfl) ⟨1331862, by rfl⟩ : syracuseStep 3551633 = 2663725) B2663725
theorem B1421761 : Blo 1048611 1421761 := bstep (se 2 (by rfl) ⟨533160, by rfl⟩ : syracuseStep 1421761 = 1066321) B1066321
theorem B40350149 : Blo 1048611 40350149 := bstep (se 4 (by rfl) ⟨3782826, by rfl⟩ : syracuseStep 40350149 = 7565653) B7565653
theorem B2994641 : Blo 1048611 2994641 := bstep (se 2 (by rfl) ⟨1122990, by rfl⟩ : syracuseStep 2994641 = 2245981) B2245981
theorem B20165233 : Blo 1048611 20165233 := bstep (se 2 (by rfl) ⟨7561962, by rfl⟩ : syracuseStep 20165233 = 15123925) B15123925
theorem B2241265 : Blo 1048611 2241265 := bstep (se 2 (by rfl) ⟨840474, by rfl⟩ : syracuseStep 2241265 = 1680949) B1680949
theorem B2241283 : Blo 1048611 2241283 := bstep (se 1 (by rfl) ⟨1680962, by rfl⟩ : syracuseStep 2241283 = 3361925) B3361925
theorem B1684243 : Blo 1048611 1684243 := bstep (se 1 (by rfl) ⟨1263182, by rfl⟩ : syracuseStep 1684243 = 2526365) B2526365
theorem B1684307 : Blo 1048611 1684307 := bstep (se 1 (by rfl) ⟨1263230, by rfl⟩ : syracuseStep 1684307 = 2526461) B2526461
theorem B3191665 : Blo 1048611 3191665 := bstep (se 2 (by rfl) ⟨1196874, by rfl⟩ : syracuseStep 3191665 = 2393749) B2393749
theorem B10236785 : Blo 1048611 10236785 := bstep (se 2 (by rfl) ⟨3838794, by rfl⟩ : syracuseStep 10236785 = 7677589) B7677589
theorem B26227597 : Blo 1048611 26227597 := bstep (se 3 (by rfl) ⟨4917674, by rfl⟩ : syracuseStep 26227597 = 9835349) B9835349
theorem B3552173 : Blo 1048611 3552173 := bstep (se 3 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 3552173 = 1332065) B1332065
theorem B5321699 : Blo 1048611 5321699 := bstep (se 1 (by rfl) ⟨3991274, by rfl⟩ : syracuseStep 5321699 = 7982549) B7982549
theorem B3552227 : Blo 1048611 3552227 := bstep (se 1 (by rfl) ⟨2664170, by rfl⟩ : syracuseStep 3552227 = 5328341) B5328341
theorem B8959045 : Blo 1048611 8959045 := bstep (se 4 (by rfl) ⟨839910, by rfl⟩ : syracuseStep 8959045 = 1679821) B1679821
theorem B3552497 : Blo 1048611 3552497 := bstep (se 2 (by rfl) ⟨1332186, by rfl⟩ : syracuseStep 3552497 = 2664373) B2664373
theorem B5387555 : Blo 1048611 5387555 := bstep (se 1 (by rfl) ⟨4040666, by rfl⟩ : syracuseStep 5387555 = 8081333) B8081333
theorem B4044131 : Blo 1048611 4044131 := bstep (se 1 (by rfl) ⟨3033098, by rfl⟩ : syracuseStep 4044131 = 6066197) B6066197
theorem B8992397 : Blo 1048611 8992397 := bstep (se 3 (by rfl) ⟨1686074, by rfl⟩ : syracuseStep 8992397 = 3372149) B3372149
theorem B1619603 : Blo 1048611 1619603 := bstep (se 1 (by rfl) ⟨1214702, by rfl⟩ : syracuseStep 1619603 = 2429405) B2429405
theorem B7976717 : Blo 1048611 7976717 := bstep (se 3 (by rfl) ⟨1495634, by rfl⟩ : syracuseStep 7976717 = 2991269) B2991269
theorem B5322509 : Blo 1048611 5322509 := bstep (se 3 (by rfl) ⟨997970, by rfl⟩ : syracuseStep 5322509 = 1995941) B1995941
theorem B1685281 : Blo 1048611 1685281 := bstep (se 2 (by rfl) ⟨631980, by rfl⟩ : syracuseStep 1685281 = 1263961) B1263961
theorem B2996099 : Blo 1048611 2996099 := bstep (se 1 (by rfl) ⟨2247074, by rfl⟩ : syracuseStep 2996099 = 4494149) B4494149
theorem B1685537 : Blo 1048611 1685537 := bstep (se 2 (by rfl) ⟨632076, by rfl⟩ : syracuseStep 1685537 = 1264153) B1264153
theorem B1685729 : Blo 1048611 1685729 := bstep (se 2 (by rfl) ⟨632148, by rfl⟩ : syracuseStep 1685729 = 1264297) B1264297
theorem B3783203 : Blo 1048611 3783203 := bstep (se 1 (by rfl) ⟨2837402, by rfl⟩ : syracuseStep 3783203 = 5674805) B5674805
theorem B2996909 : Blo 1048611 2996909 := bstep (se 3 (by rfl) ⟨561920, by rfl⟩ : syracuseStep 2996909 = 1123841) B1123841
theorem B1948355 : Blo 1048611 1948355 := bstep (se 1 (by rfl) ⟨1461266, by rfl⟩ : syracuseStep 1948355 = 2922533) B2922533
theorem B5978893 : Blo 1048611 5978893 := bstep (se 3 (by rfl) ⟨1121042, by rfl⟩ : syracuseStep 5978893 = 2242085) B2242085
theorem B5454641 : Blo 1048611 5454641 := bstep (se 2 (by rfl) ⟨2045490, by rfl⟩ : syracuseStep 5454641 = 4090981) B4090981
theorem B2997101 : Blo 1048611 2997101 := bstep (se 3 (by rfl) ⟨561956, by rfl⟩ : syracuseStep 2997101 = 1123913) B1123913
theorem B3193805 : Blo 1048611 3193805 := bstep (se 3 (by rfl) ⟨598838, by rfl⟩ : syracuseStep 3193805 = 1197677) B1197677
theorem B2243555 : Blo 1048611 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B3783665 : Blo 1048611 3783665 := bstep (se 2 (by rfl) ⟨1418874, by rfl⟩ : syracuseStep 3783665 = 2837749) B2837749
theorem B5750129 : Blo 1048611 5750129 := bstep (se 2 (by rfl) ⟨2156298, by rfl⟩ : syracuseStep 5750129 = 4312597) B4312597
theorem B2244017 : Blo 1048611 2244017 := bstep (se 2 (by rfl) ⟨841506, by rfl⟩ : syracuseStep 2244017 = 1683013) B1683013
theorem B1064675 : Blo 1048611 1064675 := bstep (se 1 (by rfl) ⟨798506, by rfl⟩ : syracuseStep 1064675 = 1597013) B1597013
theorem B4800269 : Blo 1048611 4800269 := bstep (se 3 (by rfl) ⟨900050, by rfl⟩ : syracuseStep 4800269 = 1800101) B1800101
theorem B6733637 : Blo 1048611 6733637 := bstep (se 4 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 6733637 = 1262557) B1262557
theorem B3784589 : Blo 1048611 3784589 := bstep (se 3 (by rfl) ⟨709610, by rfl⟩ : syracuseStep 3784589 = 1419221) B1419221
theorem B20431331 : Blo 1048611 20431331 := bstep (se 1 (by rfl) ⟨15323498, by rfl⟩ : syracuseStep 20431331 = 30646997) B30646997
theorem B7979633 : Blo 1048611 7979633 := bstep (se 2 (by rfl) ⟨2992362, by rfl⟩ : syracuseStep 7979633 = 5984725) B5984725
theorem B5325425 : Blo 1048611 5325425 := bstep (se 2 (by rfl) ⟨1997034, by rfl⟩ : syracuseStep 5325425 = 3994069) B3994069
theorem B1327747 : Blo 1048611 1327747 := bstep (se 1 (by rfl) ⟨995810, by rfl⟩ : syracuseStep 1327747 = 1991621) B1991621
theorem B2245315 : Blo 1048611 2245315 := bstep (se 1 (by rfl) ⟨1683986, by rfl⟩ : syracuseStep 2245315 = 3367973) B3367973
theorem B5980877 : Blo 1048611 5980877 := bstep (se 3 (by rfl) ⟨1121414, by rfl⟩ : syracuseStep 5980877 = 2242829) B2242829
theorem B1327843 : Blo 1048611 1327843 := bstep (se 1 (by rfl) ⟨995882, by rfl⟩ : syracuseStep 1327843 = 1991765) B1991765
theorem B10109681 : Blo 1048611 10109681 := bstep (se 2 (by rfl) ⟨3791130, by rfl⟩ : syracuseStep 10109681 = 7582261) B7582261
theorem B13452101 : Blo 1048611 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B3982193 : Blo 1048611 3982193 := bstep (se 2 (by rfl) ⟨1493322, by rfl⟩ : syracuseStep 3982193 = 2986645) B2986645
theorem B2245571 : Blo 1048611 2245571 := bstep (se 1 (by rfl) ⟨1684178, by rfl⟩ : syracuseStep 2245571 = 3368357) B3368357
theorem B1328339 : Blo 1048611 1328339 := bstep (se 1 (by rfl) ⟨996254, by rfl⟩ : syracuseStep 1328339 = 1992509) B1992509
theorem B1918243 : Blo 1048611 1918243 := bstep (se 1 (by rfl) ⟨1438682, by rfl⟩ : syracuseStep 1918243 = 2877365) B2877365
theorem B1262899 : Blo 1048611 1262899 := bstep (se 1 (by rfl) ⟨947174, by rfl⟩ : syracuseStep 1262899 = 1894349) B1894349
theorem B5981809 : Blo 1048611 5981809 := bstep (se 2 (by rfl) ⟨2243178, by rfl⟩ : syracuseStep 5981809 = 4486357) B4486357
theorem B2246545 : Blo 1048611 2246545 := bstep (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) B1684909
theorem B1329043 : Blo 1048611 1329043 := bstep (se 1 (by rfl) ⟨996782, by rfl⟩ : syracuseStep 1329043 = 1993565) B1993565
theorem B1329139 : Blo 1048611 1329139 := bstep (se 1 (by rfl) ⟨996854, by rfl⟩ : syracuseStep 1329139 = 1993709) B1993709
theorem B5326883 : Blo 1048611 5326883 := bstep (se 1 (by rfl) ⟨3995162, by rfl⟩ : syracuseStep 5326883 = 7990325) B7990325
theorem B3786851 : Blo 1048611 3786851 := bstep (se 1 (by rfl) ⟨2840138, by rfl⟩ : syracuseStep 3786851 = 5680277) B5680277
theorem B3786979 : Blo 1048611 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B3361027 : Blo 1048611 3361027 := bstep (se 1 (by rfl) ⟨2520770, by rfl⟩ : syracuseStep 3361027 = 5041541) B5041541
theorem B3983651 : Blo 1048611 3983651 := bstep (se 1 (by rfl) ⟨2987738, by rfl⟩ : syracuseStep 3983651 = 5975477) B5975477
theorem B3590513 : Blo 1048611 3590513 := bstep (se 2 (by rfl) ⟨1346442, by rfl⟩ : syracuseStep 3590513 = 2692885) B2692885
theorem B3361169 : Blo 1048611 3361169 := bstep (se 2 (by rfl) ⟨1260438, by rfl⟩ : syracuseStep 3361169 = 2520877) B2520877
theorem B1493425 : Blo 1048611 1493425 := bstep (se 2 (by rfl) ⟨560034, by rfl⟩ : syracuseStep 1493425 = 1120069) B1120069
theorem B6736355 : Blo 1048611 6736355 := bstep (se 1 (by rfl) ⟨5052266, by rfl⟩ : syracuseStep 6736355 = 10104533) B10104533
theorem B1329635 : Blo 1048611 1329635 := bstep (se 1 (by rfl) ⟨997226, by rfl⟩ : syracuseStep 1329635 = 1994453) B1994453
theorem B2247203 : Blo 1048611 2247203 := bstep (se 1 (by rfl) ⟨1685402, by rfl⟩ : syracuseStep 2247203 = 3370805) B3370805
theorem B2837197 : Blo 1048611 2837197 := bstep (se 3 (by rfl) ⟨531974, by rfl⟩ : syracuseStep 2837197 = 1063949) B1063949
theorem B5327693 : Blo 1048611 5327693 := bstep (se 3 (by rfl) ⟨998942, by rfl⟩ : syracuseStep 5327693 = 1997885) B1997885
theorem B11946851 : Blo 1048611 11946851 := bstep (se 1 (by rfl) ⟨8960138, by rfl⟩ : syracuseStep 11946851 = 17920277) B17920277
theorem B5983267 : Blo 1048611 5983267 := bstep (se 1 (by rfl) ⟨4487450, by rfl⟩ : syracuseStep 5983267 = 8974901) B8974901
theorem B1494131 : Blo 1048611 1494131 := bstep (se 1 (by rfl) ⟨1120598, by rfl⟩ : syracuseStep 1494131 = 2241197) B2241197
theorem B10112141 : Blo 1048611 10112141 := bstep (se 3 (by rfl) ⟨1896026, by rfl⟩ : syracuseStep 10112141 = 3792053) B3792053
theorem B2018449 : Blo 1048611 2018449 := bstep (se 2 (by rfl) ⟨756918, by rfl⟩ : syracuseStep 2018449 = 1513837) B1513837
theorem B1330339 : Blo 1048611 1330339 := bstep (se 1 (by rfl) ⟨997754, by rfl⟩ : syracuseStep 1330339 = 1995509) B1995509
theorem B1330435 : Blo 1048611 1330435 := bstep (se 1 (by rfl) ⟨997826, by rfl⟩ : syracuseStep 1330435 = 1995653) B1995653
theorem B3984653 : Blo 1048611 3984653 := bstep (se 3 (by rfl) ⟨747122, by rfl⟩ : syracuseStep 3984653 = 1494245) B1494245
theorem B2248049 : Blo 1048611 2248049 := bstep (se 2 (by rfl) ⟨843018, by rfl⟩ : syracuseStep 2248049 = 1686037) B1686037
theorem B2772433 : Blo 1048611 2772433 := bstep (se 2 (by rfl) ⟨1039662, by rfl⟩ : syracuseStep 2772433 = 2079325) B2079325
theorem B2837987 : Blo 1048611 2837987 := bstep (se 1 (by rfl) ⟨2128490, by rfl⟩ : syracuseStep 2837987 = 4256981) B4256981
theorem B5983793 : Blo 1048611 5983793 := bstep (se 2 (by rfl) ⟨2243922, by rfl⟩ : syracuseStep 5983793 = 4487845) B4487845
theorem B1494769 : Blo 1048611 1494769 := bstep (se 2 (by rfl) ⟨560538, by rfl⟩ : syracuseStep 1494769 = 1121077) B1121077
theorem B1330931 : Blo 1048611 1330931 := bstep (se 1 (by rfl) ⟨998198, by rfl⟩ : syracuseStep 1330931 = 1996397) B1996397
theorem B1494883 : Blo 1048611 1494883 := bstep (se 1 (by rfl) ⟨1121162, by rfl⟩ : syracuseStep 1494883 = 2242325) B2242325
theorem B3592045 : Blo 1048611 3592045 := bstep (se 3 (by rfl) ⟨673508, by rfl⟩ : syracuseStep 3592045 = 1347017) B1347017
theorem B16175045 : Blo 1048611 16175045 := bstep (se 4 (by rfl) ⟨1516410, by rfl⟩ : syracuseStep 16175045 = 3032821) B3032821
theorem B3198989 : Blo 1048611 3198989 := bstep (se 3 (by rfl) ⟨599810, by rfl⟩ : syracuseStep 3198989 = 1199621) B1199621
theorem B5689379 : Blo 1048611 5689379 := bstep (se 1 (by rfl) ⟨4267034, by rfl⟩ : syracuseStep 5689379 = 8534069) B8534069
theorem B4313357 : Blo 1048611 4313357 := bstep (se 3 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 4313357 = 1617509) B1617509
theorem B6738353 : Blo 1048611 6738353 := bstep (se 2 (by rfl) ⟨2526882, by rfl⟩ : syracuseStep 6738353 = 5053765) B5053765
theorem B1331635 : Blo 1048611 1331635 := bstep (se 1 (by rfl) ⟨998726, by rfl⟩ : syracuseStep 1331635 = 1997453) B1997453
theorem B1331731 : Blo 1048611 1331731 := bstep (se 1 (by rfl) ⟨998798, by rfl⟩ : syracuseStep 1331731 = 1997597) B1997597
theorem B3789517 : Blo 1048611 3789517 := bstep (se 3 (by rfl) ⟨710534, by rfl⟩ : syracuseStep 3789517 = 1421069) B1421069
theorem B3363565 : Blo 1048611 3363565 := bstep (se 3 (by rfl) ⟨630668, by rfl⟩ : syracuseStep 3363565 = 1261337) B1261337
theorem B1135507 : Blo 1048611 1135507 := bstep (se 1 (by rfl) ⟨851630, by rfl⟩ : syracuseStep 1135507 = 1703261) B1703261
theorem B5985251 : Blo 1048611 5985251 := bstep (se 1 (by rfl) ⟨4488938, by rfl⟩ : syracuseStep 5985251 = 8977877) B8977877
theorem B6378659 : Blo 1048611 6378659 := bstep (se 1 (by rfl) ⟨4783994, by rfl⟩ : syracuseStep 6378659 = 9567989) B9567989
theorem B3232931 : Blo 1048611 3232931 := bstep (se 1 (by rfl) ⟨2424698, by rfl⟩ : syracuseStep 3232931 = 4849397) B4849397
theorem B1496227 : Blo 1048611 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B2184401 : Blo 1048611 2184401 := bstep (se 2 (by rfl) ⟨819150, by rfl⟩ : syracuseStep 2184401 = 1638301) B1638301
theorem B3986765 : Blo 1048611 3986765 := bstep (se 3 (by rfl) ⟨747518, by rfl⟩ : syracuseStep 3986765 = 1495037) B1495037
theorem B8967793 : Blo 1048611 8967793 := bstep (se 2 (by rfl) ⟨3362922, by rfl⟩ : syracuseStep 8967793 = 6725845) B6725845
theorem B1890001 : Blo 1048611 1890001 := bstep (se 2 (by rfl) ⟨708750, by rfl⟩ : syracuseStep 1890001 = 1417501) B1417501
theorem B7198541 : Blo 1048611 7198541 := bstep (se 3 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 7198541 = 2699453) B2699453
theorem B3987569 : Blo 1048611 3987569 := bstep (se 2 (by rfl) ⟨1495338, by rfl⟩ : syracuseStep 3987569 = 2990677) B2990677
theorem B3790961 : Blo 1048611 3790961 := bstep (se 2 (by rfl) ⟨1421610, by rfl⟩ : syracuseStep 3790961 = 2843221) B2843221
theorem B1890449 : Blo 1048611 1890449 := bstep (se 2 (by rfl) ⟨708918, by rfl⟩ : syracuseStep 1890449 = 1417837) B1417837
theorem B1497361 : Blo 1048611 1497361 := bstep (se 2 (by rfl) ⟨561510, by rfl⟩ : syracuseStep 1497361 = 1123021) B1123021
theorem B3234125 : Blo 1048611 3234125 := bstep (se 3 (by rfl) ⟨606398, by rfl⟩ : syracuseStep 3234125 = 1212797) B1212797
theorem B1497457 : Blo 1048611 1497457 := bstep (se 2 (by rfl) ⟨561546, by rfl⟩ : syracuseStep 1497457 = 1123093) B1123093
theorem B11983301 : Blo 1048611 11983301 := bstep (se 4 (by rfl) ⟨1123434, by rfl⟩ : syracuseStep 11983301 = 2246869) B2246869
theorem B1595857 : Blo 1048611 1595857 := bstep (se 2 (by rfl) ⟨598446, by rfl⟩ : syracuseStep 1595857 = 1196893) B1196893
theorem B1890947 : Blo 1048611 1890947 := bstep (se 1 (by rfl) ⟨1418210, by rfl⟩ : syracuseStep 1890947 = 2836421) B2836421
theorem B12114613 : Blo 1048611 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B3988237 : Blo 1048611 3988237 := bstep (se 3 (by rfl) ⟨747794, by rfl⟩ : syracuseStep 3988237 = 1495589) B1495589
theorem B5987141 : Blo 1048611 5987141 := bstep (se 4 (by rfl) ⟨561294, by rfl⟩ : syracuseStep 5987141 = 1122589) B1122589
theorem B6740813 : Blo 1048611 6740813 := bstep (se 3 (by rfl) ⟨1263902, by rfl⟩ : syracuseStep 6740813 = 2527805) B2527805
theorem B1497953 : Blo 1048611 1497953 := bstep (se 2 (by rfl) ⟨561732, by rfl⟩ : syracuseStep 1497953 = 1123465) B1123465
theorem B1596611 : Blo 1048611 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B7200049 : Blo 1048611 7200049 := bstep (se 2 (by rfl) ⟨2700018, by rfl⟩ : syracuseStep 7200049 = 5400037) B5400037
theorem B15162677 : Blo 1048611 15162677 := bstep (se 5 (by rfl) ⟨710750, by rfl⟩ : syracuseStep 15162677 = 1421501) B1421501
theorem B2841965 : Blo 1048611 2841965 := bstep (se 3 (by rfl) ⟨532868, by rfl⟩ : syracuseStep 2841965 = 1065737) B1065737
theorem B3595661 : Blo 1048611 3595661 := bstep (se 3 (by rfl) ⟨674186, by rfl⟩ : syracuseStep 3595661 = 1348373) B1348373
theorem B3989027 : Blo 1048611 3989027 := bstep (se 1 (by rfl) ⟨2991770, by rfl⟩ : syracuseStep 3989027 = 5983541) B5983541
theorem B3595907 : Blo 1048611 3595907 := bstep (se 1 (by rfl) ⟨2696930, by rfl⟩ : syracuseStep 3595907 = 5393861) B5393861
theorem B4480753 : Blo 1048611 4480753 := bstep (se 2 (by rfl) ⟨1680282, by rfl⟩ : syracuseStep 4480753 = 3360565) B3360565
theorem B13656005 : Blo 1048611 13656005 := bstep (se 4 (by rfl) ⟨1280250, by rfl⟩ : syracuseStep 13656005 = 2560501) B2560501
theorem B3366947 : Blo 1048611 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B2842733 : Blo 1048611 2842733 := bstep (se 3 (by rfl) ⟨533012, by rfl⟩ : syracuseStep 2842733 = 1066025) B1066025
theorem B1794163 : Blo 1048611 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B3989681 : Blo 1048611 3989681 := bstep (se 2 (by rfl) ⟨1496130, by rfl⟩ : syracuseStep 3989681 = 2992261) B2992261
theorem B4251953 : Blo 1048611 4251953 := bstep (se 2 (by rfl) ⟨1594482, by rfl⟩ : syracuseStep 4251953 = 3188965) B3188965
theorem B2220419 : Blo 1048611 2220419 := bstep (se 1 (by rfl) ⟨1665314, by rfl⟩ : syracuseStep 2220419 = 3330629) B3330629
theorem B5399153 : Blo 1048611 5399153 := bstep (se 2 (by rfl) ⟨2024682, by rfl⟩ : syracuseStep 5399153 = 4049365) B4049365
theorem B1991537 : Blo 1048611 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B3367793 : Blo 1048611 3367793 := bstep (se 2 (by rfl) ⟨1262922, by rfl⟩ : syracuseStep 3367793 = 2525845) B2525845
theorem B1794977 : Blo 1048611 1794977 := bstep (se 2 (by rfl) ⟨673116, by rfl⟩ : syracuseStep 1794977 = 1346233) B1346233
theorem B12116963 : Blo 1048611 12116963 := bstep (se 1 (by rfl) ⟨9087722, by rfl⟩ : syracuseStep 12116963 = 18175445) B18175445
theorem B1893635 : Blo 1048611 1893635 := bstep (se 1 (by rfl) ⟨1420226, by rfl⟩ : syracuseStep 1893635 = 2840453) B2840453
theorem B1598897 : Blo 1048611 1598897 := bstep (se 2 (by rfl) ⟨599586, by rfl⟩ : syracuseStep 1598897 = 1199173) B1199173
theorem B3991139 : Blo 1048611 3991139 := bstep (se 1 (by rfl) ⟨2993354, by rfl⟩ : syracuseStep 3991139 = 5986709) B5986709
theorem B3991153 : Blo 1048611 3991153 := bstep (se 2 (by rfl) ⟨1496682, by rfl⟩ : syracuseStep 3991153 = 2993365) B2993365
theorem B1894097 : Blo 1048611 1894097 := bstep (se 2 (by rfl) ⟨710286, by rfl⟩ : syracuseStep 1894097 = 1420573) B1420573
theorem B1992433 : Blo 1048611 1992433 := bstep (se 2 (by rfl) ⟨747162, by rfl⟩ : syracuseStep 1992433 = 1494325) B1494325
theorem B2844497 : Blo 1048611 2844497 := bstep (se 2 (by rfl) ⟨1066686, by rfl⟩ : syracuseStep 2844497 = 2133373) B2133373
theorem B1992593 : Blo 1048611 1992593 := bstep (se 2 (by rfl) ⟨747222, by rfl⟩ : syracuseStep 1992593 = 1494445) B1494445
theorem B1599427 : Blo 1048611 1599427 := bstep (se 1 (by rfl) ⟨1199570, by rfl⟩ : syracuseStep 1599427 = 2399141) B2399141
theorem B3598285 : Blo 1048611 3598285 := bstep (se 3 (by rfl) ⟨674678, by rfl⟩ : syracuseStep 3598285 = 1349357) B1349357
theorem B32368693 : Blo 1048611 32368693 := bstep (se 5 (by rfl) ⟨1517282, by rfl⟩ : syracuseStep 32368693 = 3034565) B3034565
theorem B1992995 : Blo 1048611 1992995 := bstep (se 1 (by rfl) ⟨1494746, by rfl⟩ : syracuseStep 1992995 = 2989493) B2989493
theorem B2845037 : Blo 1048611 2845037 := bstep (se 3 (by rfl) ⟨533444, by rfl⟩ : syracuseStep 2845037 = 1066889) B1066889
theorem B3369613 : Blo 1048611 3369613 := bstep (se 3 (by rfl) ⟨631802, by rfl⟩ : syracuseStep 3369613 = 1263605) B1263605
theorem B12151565 : Blo 1048611 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B1796899 : Blo 1048611 1796899 := bstep (se 1 (by rfl) ⟨1347674, by rfl⟩ : syracuseStep 1796899 = 2695349) B2695349
theorem B8973125 : Blo 1048611 8973125 := bstep (se 4 (by rfl) ⟨841230, by rfl⟩ : syracuseStep 8973125 = 1682461) B1682461
theorem B3992611 : Blo 1048611 3992611 := bstep (se 1 (by rfl) ⟨2994458, by rfl⟩ : syracuseStep 3992611 = 5988917) B5988917
theorem B1993891 : Blo 1048611 1993891 := bstep (se 1 (by rfl) ⟨1495418, by rfl⟩ : syracuseStep 1993891 = 2990837) B2990837
theorem B1994051 : Blo 1048611 1994051 := bstep (se 1 (by rfl) ⟨1495538, by rfl⟩ : syracuseStep 1994051 = 2991077) B2991077
theorem B4484429 : Blo 1048611 4484429 := bstep (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) B1681661
theorem B1896547 : Blo 1048611 1896547 := bstep (se 1 (by rfl) ⟨1422410, by rfl⟩ : syracuseStep 1896547 = 2844821) B2844821
theorem B11989133 : Blo 1048611 11989133 := bstep (se 3 (by rfl) ⟨2247962, by rfl⟩ : syracuseStep 11989133 = 4495925) B4495925
theorem B2126083 : Blo 1048611 2126083 := bstep (se 1 (by rfl) ⟨1594562, by rfl⟩ : syracuseStep 2126083 = 3189125) B3189125
theorem B1995121 : Blo 1048611 1995121 := bstep (se 2 (by rfl) ⟨748170, by rfl⟩ : syracuseStep 1995121 = 1496341) B1496341
theorem B5992973 : Blo 1048611 5992973 := bstep (se 3 (by rfl) ⟨1123682, by rfl⟩ : syracuseStep 5992973 = 2247365) B2247365
theorem B6386245 : Blo 1048611 6386245 := bstep (se 4 (by rfl) ⟨598710, by rfl⟩ : syracuseStep 6386245 = 1197421) B1197421
theorem B8090723 : Blo 1048611 8090723 := bstep (se 1 (by rfl) ⟨6068042, by rfl⟩ : syracuseStep 8090723 = 12136085) B12136085
theorem B3994829 : Blo 1048611 3994829 := bstep (se 3 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 3994829 = 1498061) B1498061
theorem B1996177 : Blo 1048611 1996177 := bstep (se 2 (by rfl) ⟨748566, by rfl⟩ : syracuseStep 1996177 = 1497133) B1497133
theorem B1799827 : Blo 1048611 1799827 := bstep (se 1 (by rfl) ⟨1349870, by rfl⟩ : syracuseStep 1799827 = 2699741) B2699741
theorem B11368163 : Blo 1048611 11368163 := bstep (se 1 (by rfl) ⟨8526122, by rfl⟩ : syracuseStep 11368163 = 17052245) B17052245
theorem B1996579 : Blo 1048611 1996579 := bstep (se 1 (by rfl) ⟨1497434, by rfl⟩ : syracuseStep 1996579 = 2994869) B2994869
theorem B1996625 : Blo 1048611 1996625 := bstep (se 2 (by rfl) ⟨748734, by rfl⟩ : syracuseStep 1996625 = 1497469) B1497469
theorem B1996913 : Blo 1048611 1996913 := bstep (se 2 (by rfl) ⟨748842, by rfl⟩ : syracuseStep 1996913 = 1497685) B1497685
theorem B1440019 : Blo 1048611 1440019 := bstep (se 1 (by rfl) ⟨1080014, by rfl⟩ : syracuseStep 1440019 = 2160029) B2160029
theorem B17955269 : Blo 1048611 17955269 := bstep (se 4 (by rfl) ⟨1683306, by rfl⟩ : syracuseStep 17955269 = 3366613) B3366613
theorem B1440545 : Blo 1048611 1440545 := bstep (se 2 (by rfl) ⟨540204, by rfl⟩ : syracuseStep 1440545 = 1080409) B1080409
theorem B1997635 : Blo 1048611 1997635 := bstep (se 1 (by rfl) ⟨1498226, by rfl⟩ : syracuseStep 1997635 = 2996453) B2996453
theorem B1998083 : Blo 1048611 1998083 := bstep (se 1 (by rfl) ⟨1498562, by rfl⟩ : syracuseStep 1998083 = 2997125) B2997125
theorem B7568653 : Blo 1048611 7568653 := bstep (se 3 (by rfl) ⟨1419122, by rfl⟩ : syracuseStep 7568653 = 2838245) B2838245
theorem B1080787 : Blo 1048611 1080787 := bstep (se 1 (by rfl) ⟨810590, by rfl⟩ : syracuseStep 1080787 = 1621181) B1621181
theorem B6389219 : Blo 1048611 6389219 := bstep (se 1 (by rfl) ⟨4791914, by rfl⟩ : syracuseStep 6389219 = 9583829) B9583829
theorem B4488803 : Blo 1048611 4488803 := bstep (se 1 (by rfl) ⟨3366602, by rfl⟩ : syracuseStep 4488803 = 6733205) B6733205
theorem B2391697 : Blo 1048611 2391697 := bstep (se 2 (by rfl) ⟨896886, by rfl⟩ : syracuseStep 2391697 = 1793773) B1793773
theorem B2162659 : Blo 1048611 2162659 := bstep (se 1 (by rfl) ⟨1621994, by rfl⟩ : syracuseStep 2162659 = 3243989) B3243989
theorem B1048619 : Blo 1048611 1048619 := bstep (se 1 (by rfl) ⟨786464, by rfl⟩ : syracuseStep 1048619 = 1572929) B1572929
theorem B1048631 : Blo 1048611 1048631 := bstep (se 1 (by rfl) ⟨786473, by rfl⟩ : syracuseStep 1048631 = 1572947) B1572947
theorem B1048651 : Blo 1048611 1048651 := bstep (se 1 (by rfl) ⟨786488, by rfl⟩ : syracuseStep 1048651 = 1572977) B1572977
theorem B1048663 : Blo 1048611 1048663 := bstep (se 1 (by rfl) ⟨786497, by rfl⟩ : syracuseStep 1048663 = 1572995) B1572995
theorem B2359385 : Blo 1048611 2359385 := bstep (se 2 (by rfl) ⟨884769, by rfl⟩ : syracuseStep 2359385 = 1769539) B1769539
theorem B1572953 : Blo 1048611 1572953 := bstep (se 2 (by rfl) ⟨589857, by rfl⟩ : syracuseStep 1572953 = 1179715) B1179715
theorem B8978525 : Blo 1048611 8978525 := bstep (se 3 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 8978525 = 3366947) B3366947
theorem B1048683 : Blo 1048611 1048683 := bstep (se 1 (by rfl) ⟨786512, by rfl⟩ : syracuseStep 1048683 = 1573025) B1573025
theorem B1048695 : Blo 1048611 1048695 := bstep (se 1 (by rfl) ⟨786521, by rfl⟩ : syracuseStep 1048695 = 1573043) B1573043
theorem B1179787 : Blo 1048611 1179787 := bstep (se 1 (by rfl) ⟨884840, by rfl⟩ : syracuseStep 1179787 = 1769681) B1769681
theorem B1048715 : Blo 1048611 1048715 := bstep (se 1 (by rfl) ⟨786536, by rfl⟩ : syracuseStep 1048715 = 1573073) B1573073
theorem B1048727 : Blo 1048611 1048727 := bstep (se 1 (by rfl) ⟨786545, by rfl⟩ : syracuseStep 1048727 = 1573091) B1573091
theorem B2392217 : Blo 1048611 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B1048747 : Blo 1048611 1048747 := bstep (se 1 (by rfl) ⟨786560, by rfl⟩ : syracuseStep 1048747 = 1573121) B1573121
theorem B2359475 : Blo 1048611 2359475 := bstep (se 1 (by rfl) ⟨1769606, by rfl⟩ : syracuseStep 2359475 = 3539213) B3539213
theorem B1048759 : Blo 1048611 1048759 := bstep (se 1 (by rfl) ⟨786569, by rfl⟩ : syracuseStep 1048759 = 1573139) B1573139
theorem B1573067 : Blo 1048611 1573067 := bstep (se 1 (by rfl) ⟨1179800, by rfl⟩ : syracuseStep 1573067 = 2359601) B2359601
theorem B1048779 : Blo 1048611 1048779 := bstep (se 1 (by rfl) ⟨786584, by rfl⟩ : syracuseStep 1048779 = 1573169) B1573169
theorem B2359511 : Blo 1048611 2359511 := bstep (se 1 (by rfl) ⟨1769633, by rfl⟩ : syracuseStep 2359511 = 3539267) B3539267
theorem B1573079 : Blo 1048611 1573079 := bstep (se 1 (by rfl) ⟨1179809, by rfl⟩ : syracuseStep 1573079 = 2359619) B2359619
theorem B1048791 : Blo 1048611 1048791 := bstep (se 1 (by rfl) ⟨786593, by rfl⟩ : syracuseStep 1048791 = 1573187) B1573187
theorem B1048811 : Blo 1048611 1048811 := bstep (se 1 (by rfl) ⟨786608, by rfl⟩ : syracuseStep 1048811 = 1573217) B1573217
theorem B1179895 : Blo 1048611 1179895 := bstep (se 1 (by rfl) ⟨884921, by rfl⟩ : syracuseStep 1179895 = 1769843) B1769843
theorem B1048823 : Blo 1048611 1048823 := bstep (se 1 (by rfl) ⟨786617, by rfl⟩ : syracuseStep 1048823 = 1573235) B1573235
theorem B1048843 : Blo 1048611 1048843 := bstep (se 1 (by rfl) ⟨786632, by rfl⟩ : syracuseStep 1048843 = 1573265) B1573265
theorem B1048855 : Blo 1048611 1048855 := bstep (se 1 (by rfl) ⟨786641, by rfl⟩ : syracuseStep 1048855 = 1573283) B1573283
theorem B1573145 : Blo 1048611 1573145 := bstep (se 2 (by rfl) ⟨589929, by rfl⟩ : syracuseStep 1573145 = 1179859) B1179859
theorem B1048875 : Blo 1048611 1048875 := bstep (se 1 (by rfl) ⟨786656, by rfl⟩ : syracuseStep 1048875 = 1573313) B1573313
theorem B1048887 : Blo 1048611 1048887 := bstep (se 1 (by rfl) ⟨786665, by rfl⟩ : syracuseStep 1048887 = 1573331) B1573331
theorem B1048907 : Blo 1048611 1048907 := bstep (se 1 (by rfl) ⟨786680, by rfl⟩ : syracuseStep 1048907 = 1573361) B1573361
theorem B1048919 : Blo 1048611 1048919 := bstep (se 1 (by rfl) ⟨786689, by rfl⟩ : syracuseStep 1048919 = 1573379) B1573379
theorem B1048939 : Blo 1048611 1048939 := bstep (se 1 (by rfl) ⟨786704, by rfl⟩ : syracuseStep 1048939 = 1573409) B1573409
theorem B1048951 : Blo 1048611 1048951 := bstep (se 1 (by rfl) ⟨786713, by rfl⟩ : syracuseStep 1048951 = 1573427) B1573427
theorem B2359691 : Blo 1048611 2359691 := bstep (se 1 (by rfl) ⟨1769768, by rfl⟩ : syracuseStep 2359691 = 3539537) B3539537
theorem B1573259 : Blo 1048611 1573259 := bstep (se 1 (by rfl) ⟨1179944, by rfl⟩ : syracuseStep 1573259 = 2359889) B2359889
theorem B1048971 : Blo 1048611 1048971 := bstep (se 1 (by rfl) ⟨786728, by rfl⟩ : syracuseStep 1048971 = 1573457) B1573457
theorem B1573271 : Blo 1048611 1573271 := bstep (se 1 (by rfl) ⟨1179953, by rfl⟩ : syracuseStep 1573271 = 2359907) B2359907
theorem B1048983 : Blo 1048611 1048983 := bstep (se 1 (by rfl) ⟨786737, by rfl⟩ : syracuseStep 1048983 = 1573475) B1573475
theorem B1180075 : Blo 1048611 1180075 := bstep (se 1 (by rfl) ⟨885056, by rfl⟩ : syracuseStep 1180075 = 1770113) B1770113
theorem B1049003 : Blo 1048611 1049003 := bstep (se 1 (by rfl) ⟨786752, by rfl⟩ : syracuseStep 1049003 = 1573505) B1573505
theorem B1049015 : Blo 1048611 1049015 := bstep (se 1 (by rfl) ⟨786761, by rfl⟩ : syracuseStep 1049015 = 1573523) B1573523
theorem B2359745 : Blo 1048611 2359745 := bstep (se 2 (by rfl) ⟨884904, by rfl⟩ : syracuseStep 2359745 = 1769809) B1769809
theorem B1049035 : Blo 1048611 1049035 := bstep (se 1 (by rfl) ⟨786776, by rfl⟩ : syracuseStep 1049035 = 1573553) B1573553
theorem B1049047 : Blo 1048611 1049047 := bstep (se 1 (by rfl) ⟨786785, by rfl⟩ : syracuseStep 1049047 = 1573571) B1573571
theorem B1573337 : Blo 1048611 1573337 := bstep (se 2 (by rfl) ⟨590001, by rfl⟩ : syracuseStep 1573337 = 1180003) B1180003
theorem B1049067 : Blo 1048611 1049067 := bstep (se 1 (by rfl) ⟨786800, by rfl⟩ : syracuseStep 1049067 = 1573601) B1573601
theorem B1049079 : Blo 1048611 1049079 := bstep (se 1 (by rfl) ⟨786809, by rfl⟩ : syracuseStep 1049079 = 1573619) B1573619
theorem B1049099 : Blo 1048611 1049099 := bstep (se 1 (by rfl) ⟨786824, by rfl⟩ : syracuseStep 1049099 = 1573649) B1573649
theorem B1180183 : Blo 1048611 1180183 := bstep (se 1 (by rfl) ⟨885137, by rfl⟩ : syracuseStep 1180183 = 1770275) B1770275
theorem B1049111 : Blo 1048611 1049111 := bstep (se 1 (by rfl) ⟨786833, by rfl⟩ : syracuseStep 1049111 = 1573667) B1573667
theorem B1049131 : Blo 1048611 1049131 := bstep (se 1 (by rfl) ⟨786848, by rfl⟩ : syracuseStep 1049131 = 1573697) B1573697
theorem B1049143 : Blo 1048611 1049143 := bstep (se 1 (by rfl) ⟨786857, by rfl⟩ : syracuseStep 1049143 = 1573715) B1573715
theorem B2654795 : Blo 1048611 2654795 := bstep (se 1 (by rfl) ⟨1991096, by rfl⟩ : syracuseStep 2654795 = 3982193) B3982193
theorem B1770059 : Blo 1048611 1770059 := bstep (se 1 (by rfl) ⟨1327544, by rfl⟩ : syracuseStep 1770059 = 2655089) B2655089
theorem B1573451 : Blo 1048611 1573451 := bstep (se 1 (by rfl) ⟨1180088, by rfl⟩ : syracuseStep 1573451 = 2360177) B2360177
theorem B1049163 : Blo 1048611 1049163 := bstep (se 1 (by rfl) ⟨786872, by rfl⟩ : syracuseStep 1049163 = 1573745) B1573745
theorem B1573463 : Blo 1048611 1573463 := bstep (se 1 (by rfl) ⟨1180097, by rfl⟩ : syracuseStep 1573463 = 2360195) B2360195
theorem B1049175 : Blo 1048611 1049175 := bstep (se 1 (by rfl) ⟨786881, by rfl⟩ : syracuseStep 1049175 = 1573763) B1573763
theorem B1049195 : Blo 1048611 1049195 := bstep (se 1 (by rfl) ⟨786896, by rfl⟩ : syracuseStep 1049195 = 1573793) B1573793
theorem B1049207 : Blo 1048611 1049207 := bstep (se 1 (by rfl) ⟨786905, by rfl⟩ : syracuseStep 1049207 = 1573811) B1573811
theorem B1049227 : Blo 1048611 1049227 := bstep (se 1 (by rfl) ⟨786920, by rfl⟩ : syracuseStep 1049227 = 1573841) B1573841
theorem B1049239 : Blo 1048611 1049239 := bstep (se 1 (by rfl) ⟨786929, by rfl⟩ : syracuseStep 1049239 = 1573859) B1573859
theorem B2359961 : Blo 1048611 2359961 := bstep (se 2 (by rfl) ⟨884985, by rfl⟩ : syracuseStep 2359961 = 1769971) B1769971
theorem B1573529 : Blo 1048611 1573529 := bstep (se 2 (by rfl) ⟨590073, by rfl⟩ : syracuseStep 1573529 = 1180147) B1180147
theorem B1049259 : Blo 1048611 1049259 := bstep (se 1 (by rfl) ⟨786944, by rfl⟩ : syracuseStep 1049259 = 1573889) B1573889
theorem B7570097 : Blo 1048611 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B1049271 : Blo 1048611 1049271 := bstep (se 1 (by rfl) ⟨786953, by rfl⟩ : syracuseStep 1049271 = 1573907) B1573907
theorem B1770187 : Blo 1048611 1770187 := bstep (se 1 (by rfl) ⟨1327640, by rfl⟩ : syracuseStep 1770187 = 2655281) B2655281
theorem B1180363 : Blo 1048611 1180363 := bstep (se 1 (by rfl) ⟨885272, by rfl⟩ : syracuseStep 1180363 = 1770545) B1770545
theorem B1049291 : Blo 1048611 1049291 := bstep (se 1 (by rfl) ⟨786968, by rfl⟩ : syracuseStep 1049291 = 1573937) B1573937
theorem B1049303 : Blo 1048611 1049303 := bstep (se 1 (by rfl) ⟨786977, by rfl⟩ : syracuseStep 1049303 = 1573955) B1573955
theorem B1049323 : Blo 1048611 1049323 := bstep (se 1 (by rfl) ⟨786992, by rfl⟩ : syracuseStep 1049323 = 1573985) B1573985
theorem B2360051 : Blo 1048611 2360051 := bstep (se 1 (by rfl) ⟨1770038, by rfl⟩ : syracuseStep 2360051 = 3540077) B3540077
theorem B1049335 : Blo 1048611 1049335 := bstep (se 1 (by rfl) ⟨787001, by rfl⟩ : syracuseStep 1049335 = 1574003) B1574003
theorem B1573643 : Blo 1048611 1573643 := bstep (se 1 (by rfl) ⟨1180232, by rfl⟩ : syracuseStep 1573643 = 2360465) B2360465
theorem B1049355 : Blo 1048611 1049355 := bstep (se 1 (by rfl) ⟨787016, by rfl⟩ : syracuseStep 1049355 = 1574033) B1574033
theorem B2360087 : Blo 1048611 2360087 := bstep (se 1 (by rfl) ⟨1770065, by rfl⟩ : syracuseStep 2360087 = 3540131) B3540131
theorem B1573655 : Blo 1048611 1573655 := bstep (se 1 (by rfl) ⟨1180241, by rfl⟩ : syracuseStep 1573655 = 2360483) B2360483
theorem B1049367 : Blo 1048611 1049367 := bstep (se 1 (by rfl) ⟨787025, by rfl⟩ : syracuseStep 1049367 = 1574051) B1574051
theorem B1049387 : Blo 1048611 1049387 := bstep (se 1 (by rfl) ⟨787040, by rfl⟩ : syracuseStep 1049387 = 1574081) B1574081
theorem B1180471 : Blo 1048611 1180471 := bstep (se 1 (by rfl) ⟨885353, by rfl⟩ : syracuseStep 1180471 = 1770707) B1770707
theorem B1049399 : Blo 1048611 1049399 := bstep (se 1 (by rfl) ⟨787049, by rfl⟩ : syracuseStep 1049399 = 1574099) B1574099
theorem B1049419 : Blo 1048611 1049419 := bstep (se 1 (by rfl) ⟨787064, by rfl⟩ : syracuseStep 1049419 = 1574129) B1574129
theorem B8979275 : Blo 1048611 8979275 := bstep (se 1 (by rfl) ⟨6734456, by rfl⟩ : syracuseStep 8979275 = 13468913) B13468913
theorem B1049431 : Blo 1048611 1049431 := bstep (se 1 (by rfl) ⟨787073, by rfl⟩ : syracuseStep 1049431 = 1574147) B1574147
theorem B1770329 : Blo 1048611 1770329 := bstep (se 2 (by rfl) ⟨663873, by rfl⟩ : syracuseStep 1770329 = 1327747) B1327747
theorem B1573721 : Blo 1048611 1573721 := bstep (se 2 (by rfl) ⟨590145, by rfl⟩ : syracuseStep 1573721 = 1180291) B1180291
theorem B1049451 : Blo 1048611 1049451 := bstep (se 1 (by rfl) ⟨787088, by rfl⟩ : syracuseStep 1049451 = 1574177) B1574177
theorem B1049463 : Blo 1048611 1049463 := bstep (se 1 (by rfl) ⟨787097, by rfl⟩ : syracuseStep 1049463 = 1574195) B1574195
theorem B1049483 : Blo 1048611 1049483 := bstep (se 1 (by rfl) ⟨787112, by rfl⟩ : syracuseStep 1049483 = 1574225) B1574225
theorem B1049495 : Blo 1048611 1049495 := bstep (se 1 (by rfl) ⟨787121, by rfl⟩ : syracuseStep 1049495 = 1574243) B1574243
theorem B1049515 : Blo 1048611 1049515 := bstep (se 1 (by rfl) ⟨787136, by rfl⟩ : syracuseStep 1049515 = 1574273) B1574273
theorem B1049527 : Blo 1048611 1049527 := bstep (se 1 (by rfl) ⟨787145, by rfl⟩ : syracuseStep 1049527 = 1574291) B1574291
theorem B3539915 : Blo 1048611 3539915 := bstep (se 1 (by rfl) ⟨2654936, by rfl⟩ : syracuseStep 3539915 = 5309873) B5309873
theorem B2360267 : Blo 1048611 2360267 := bstep (se 1 (by rfl) ⟨1770200, by rfl⟩ : syracuseStep 2360267 = 3540401) B3540401
theorem B1573835 : Blo 1048611 1573835 := bstep (se 1 (by rfl) ⟨1180376, by rfl⟩ : syracuseStep 1573835 = 2360753) B2360753
theorem B1049547 : Blo 1048611 1049547 := bstep (se 1 (by rfl) ⟨787160, by rfl⟩ : syracuseStep 1049547 = 1574321) B1574321
theorem B1573847 : Blo 1048611 1573847 := bstep (se 1 (by rfl) ⟨1180385, by rfl⟩ : syracuseStep 1573847 = 2360771) B2360771
theorem B1049559 : Blo 1048611 1049559 := bstep (se 1 (by rfl) ⟨787169, by rfl⟩ : syracuseStep 1049559 = 1574339) B1574339
theorem B1770457 : Blo 1048611 1770457 := bstep (se 2 (by rfl) ⟨663921, by rfl⟩ : syracuseStep 1770457 = 1327843) B1327843
theorem B1180651 : Blo 1048611 1180651 := bstep (se 1 (by rfl) ⟨885488, by rfl⟩ : syracuseStep 1180651 = 1770977) B1770977
theorem B1049579 : Blo 1048611 1049579 := bstep (se 1 (by rfl) ⟨787184, by rfl⟩ : syracuseStep 1049579 = 1574369) B1574369
theorem B1049591 : Blo 1048611 1049591 := bstep (se 1 (by rfl) ⟨787193, by rfl⟩ : syracuseStep 1049591 = 1574387) B1574387
theorem B2360321 : Blo 1048611 2360321 := bstep (se 2 (by rfl) ⟨885120, by rfl⟩ : syracuseStep 2360321 = 1770241) B1770241
theorem B1049611 : Blo 1048611 1049611 := bstep (se 1 (by rfl) ⟨787208, by rfl⟩ : syracuseStep 1049611 = 1574417) B1574417
theorem B1049623 : Blo 1048611 1049623 := bstep (se 1 (by rfl) ⟨787217, by rfl⟩ : syracuseStep 1049623 = 1574435) B1574435
theorem B1573913 : Blo 1048611 1573913 := bstep (se 2 (by rfl) ⟨590217, by rfl⟩ : syracuseStep 1573913 = 1180435) B1180435
theorem B1049643 : Blo 1048611 1049643 := bstep (se 1 (by rfl) ⟨787232, by rfl⟩ : syracuseStep 1049643 = 1574465) B1574465
theorem B1049655 : Blo 1048611 1049655 := bstep (se 1 (by rfl) ⟨787241, by rfl⟩ : syracuseStep 1049655 = 1574483) B1574483
theorem B1049675 : Blo 1048611 1049675 := bstep (se 1 (by rfl) ⟨787256, by rfl⟩ : syracuseStep 1049675 = 1574513) B1574513
theorem B1180759 : Blo 1048611 1180759 := bstep (se 1 (by rfl) ⟨885569, by rfl⟩ : syracuseStep 1180759 = 1771139) B1771139
theorem B1049687 : Blo 1048611 1049687 := bstep (se 1 (by rfl) ⟨787265, by rfl⟩ : syracuseStep 1049687 = 1574531) B1574531
theorem B1049707 : Blo 1048611 1049707 := bstep (se 1 (by rfl) ⟨787280, by rfl⟩ : syracuseStep 1049707 = 1574561) B1574561
theorem B1049719 : Blo 1048611 1049719 := bstep (se 1 (by rfl) ⟨787289, by rfl⟩ : syracuseStep 1049719 = 1574579) B1574579
theorem B1574027 : Blo 1048611 1574027 := bstep (se 1 (by rfl) ⟨1180520, by rfl⟩ : syracuseStep 1574027 = 2361041) B2361041
theorem B1049739 : Blo 1048611 1049739 := bstep (se 1 (by rfl) ⟨787304, by rfl⟩ : syracuseStep 1049739 = 1574609) B1574609
theorem B1574039 : Blo 1048611 1574039 := bstep (se 1 (by rfl) ⟨1180529, by rfl⟩ : syracuseStep 1574039 = 2361059) B2361059
theorem B1049751 : Blo 1048611 1049751 := bstep (se 1 (by rfl) ⟨787313, by rfl⟩ : syracuseStep 1049751 = 1574627) B1574627
theorem B1049771 : Blo 1048611 1049771 := bstep (se 1 (by rfl) ⟨787328, by rfl⟩ : syracuseStep 1049771 = 1574657) B1574657
theorem B1049783 : Blo 1048611 1049783 := bstep (se 1 (by rfl) ⟨787337, by rfl⟩ : syracuseStep 1049783 = 1574675) B1574675
theorem B1049803 : Blo 1048611 1049803 := bstep (se 1 (by rfl) ⟨787352, by rfl⟩ : syracuseStep 1049803 = 1574705) B1574705
theorem B1049815 : Blo 1048611 1049815 := bstep (se 1 (by rfl) ⟨787361, by rfl⟩ : syracuseStep 1049815 = 1574723) B1574723
theorem B3540185 : Blo 1048611 3540185 := bstep (se 2 (by rfl) ⟨1327569, by rfl⟩ : syracuseStep 3540185 = 2655139) B2655139
theorem B2360537 : Blo 1048611 2360537 := bstep (se 2 (by rfl) ⟨885201, by rfl⟩ : syracuseStep 2360537 = 1770403) B1770403
theorem B1574105 : Blo 1048611 1574105 := bstep (se 2 (by rfl) ⟨590289, by rfl⟩ : syracuseStep 1574105 = 1180579) B1180579
theorem B1049835 : Blo 1048611 1049835 := bstep (se 1 (by rfl) ⟨787376, by rfl⟩ : syracuseStep 1049835 = 1574753) B1574753
theorem B1049847 : Blo 1048611 1049847 := bstep (se 1 (by rfl) ⟨787385, by rfl⟩ : syracuseStep 1049847 = 1574771) B1574771
theorem B1180939 : Blo 1048611 1180939 := bstep (se 1 (by rfl) ⟨885704, by rfl⟩ : syracuseStep 1180939 = 1771409) B1771409
theorem B1049867 : Blo 1048611 1049867 := bstep (se 1 (by rfl) ⟨787400, by rfl⟩ : syracuseStep 1049867 = 1574801) B1574801
theorem B1049879 : Blo 1048611 1049879 := bstep (se 1 (by rfl) ⟨787409, by rfl⟩ : syracuseStep 1049879 = 1574819) B1574819
theorem B1049899 : Blo 1048611 1049899 := bstep (se 1 (by rfl) ⟨787424, by rfl⟩ : syracuseStep 1049899 = 1574849) B1574849
theorem B2360627 : Blo 1048611 2360627 := bstep (se 1 (by rfl) ⟨1770470, by rfl⟩ : syracuseStep 2360627 = 3540941) B3540941
theorem B1049911 : Blo 1048611 1049911 := bstep (se 1 (by rfl) ⟨787433, by rfl⟩ : syracuseStep 1049911 = 1574867) B1574867
theorem B1574219 : Blo 1048611 1574219 := bstep (se 1 (by rfl) ⟨1180664, by rfl⟩ : syracuseStep 1574219 = 2361329) B2361329
theorem B1049931 : Blo 1048611 1049931 := bstep (se 1 (by rfl) ⟨787448, by rfl⟩ : syracuseStep 1049931 = 1574897) B1574897
theorem B2360663 : Blo 1048611 2360663 := bstep (se 1 (by rfl) ⟨1770497, by rfl⟩ : syracuseStep 2360663 = 3540995) B3540995
theorem B1574231 : Blo 1048611 1574231 := bstep (se 1 (by rfl) ⟨1180673, by rfl⟩ : syracuseStep 1574231 = 2361347) B2361347
theorem B1049943 : Blo 1048611 1049943 := bstep (se 1 (by rfl) ⟨787457, by rfl⟩ : syracuseStep 1049943 = 1574915) B1574915
theorem B1049963 : Blo 1048611 1049963 := bstep (se 1 (by rfl) ⟨787472, by rfl⟩ : syracuseStep 1049963 = 1574945) B1574945
theorem B1181047 : Blo 1048611 1181047 := bstep (se 1 (by rfl) ⟨885785, by rfl⟩ : syracuseStep 1181047 = 1771571) B1771571
theorem B1049975 : Blo 1048611 1049975 := bstep (se 1 (by rfl) ⟨787481, by rfl⟩ : syracuseStep 1049975 = 1574963) B1574963
theorem B1049995 : Blo 1048611 1049995 := bstep (se 1 (by rfl) ⟨787496, by rfl⟩ : syracuseStep 1049995 = 1574993) B1574993
theorem B1050007 : Blo 1048611 1050007 := bstep (se 1 (by rfl) ⟨787505, by rfl⟩ : syracuseStep 1050007 = 1575011) B1575011
theorem B1574297 : Blo 1048611 1574297 := bstep (se 2 (by rfl) ⟨590361, by rfl⟩ : syracuseStep 1574297 = 1180723) B1180723
theorem B1050027 : Blo 1048611 1050027 := bstep (se 1 (by rfl) ⟨787520, by rfl⟩ : syracuseStep 1050027 = 1575041) B1575041
theorem B7964081 : Blo 1048611 7964081 := bstep (se 2 (by rfl) ⟨2986530, by rfl⟩ : syracuseStep 7964081 = 5973061) B5973061
theorem B1050039 : Blo 1048611 1050039 := bstep (se 1 (by rfl) ⟨787529, by rfl⟩ : syracuseStep 1050039 = 1575059) B1575059
theorem B1050059 : Blo 1048611 1050059 := bstep (se 1 (by rfl) ⟨787544, by rfl⟩ : syracuseStep 1050059 = 1575089) B1575089
theorem B1050071 : Blo 1048611 1050071 := bstep (se 1 (by rfl) ⟨787553, by rfl⟩ : syracuseStep 1050071 = 1575107) B1575107
theorem B1050091 : Blo 1048611 1050091 := bstep (se 1 (by rfl) ⟨787568, by rfl⟩ : syracuseStep 1050091 = 1575137) B1575137
theorem B1050103 : Blo 1048611 1050103 := bstep (se 1 (by rfl) ⟨787577, by rfl⟩ : syracuseStep 1050103 = 1575155) B1575155
theorem B2360843 : Blo 1048611 2360843 := bstep (se 1 (by rfl) ⟨1770632, by rfl⟩ : syracuseStep 2360843 = 3541265) B3541265
theorem B1574411 : Blo 1048611 1574411 := bstep (se 1 (by rfl) ⟨1180808, by rfl⟩ : syracuseStep 1574411 = 2361617) B2361617
theorem B1050123 : Blo 1048611 1050123 := bstep (se 1 (by rfl) ⟨787592, by rfl⟩ : syracuseStep 1050123 = 1575185) B1575185
theorem B2655767 : Blo 1048611 2655767 := bstep (se 1 (by rfl) ⟨1991825, by rfl⟩ : syracuseStep 2655767 = 3983651) B3983651
theorem B1771031 : Blo 1048611 1771031 := bstep (se 1 (by rfl) ⟨1328273, by rfl⟩ : syracuseStep 1771031 = 2656547) B2656547
theorem B1574423 : Blo 1048611 1574423 := bstep (se 1 (by rfl) ⟨1180817, by rfl⟩ : syracuseStep 1574423 = 2361635) B2361635
theorem B1050135 : Blo 1048611 1050135 := bstep (se 1 (by rfl) ⟨787601, by rfl⟩ : syracuseStep 1050135 = 1575203) B1575203
theorem B1181227 : Blo 1048611 1181227 := bstep (se 1 (by rfl) ⟨885920, by rfl⟩ : syracuseStep 1181227 = 1771841) B1771841
theorem B1050155 : Blo 1048611 1050155 := bstep (se 1 (by rfl) ⟨787616, by rfl⟩ : syracuseStep 1050155 = 1575233) B1575233
theorem B1050167 : Blo 1048611 1050167 := bstep (se 1 (by rfl) ⟨787625, by rfl⟩ : syracuseStep 1050167 = 1575251) B1575251
theorem B2360897 : Blo 1048611 2360897 := bstep (se 2 (by rfl) ⟨885336, by rfl⟩ : syracuseStep 2360897 = 1770673) B1770673
theorem B2393675 : Blo 1048611 2393675 := bstep (se 1 (by rfl) ⟨1795256, by rfl⟩ : syracuseStep 2393675 = 3590513) B3590513
theorem B1050187 : Blo 1048611 1050187 := bstep (se 1 (by rfl) ⟨787640, by rfl⟩ : syracuseStep 1050187 = 1575281) B1575281
theorem B1574489 : Blo 1048611 1574489 := bstep (se 2 (by rfl) ⟨590433, by rfl⟩ : syracuseStep 1574489 = 1180867) B1180867
theorem B1050199 : Blo 1048611 1050199 := bstep (se 1 (by rfl) ⟨787649, by rfl⟩ : syracuseStep 1050199 = 1575299) B1575299
theorem B1050219 : Blo 1048611 1050219 := bstep (se 1 (by rfl) ⟨787664, by rfl⟩ : syracuseStep 1050219 = 1575329) B1575329
theorem B1050231 : Blo 1048611 1050231 := bstep (se 1 (by rfl) ⟨787673, by rfl⟩ : syracuseStep 1050231 = 1575347) B1575347
theorem B1050251 : Blo 1048611 1050251 := bstep (se 1 (by rfl) ⟨787688, by rfl⟩ : syracuseStep 1050251 = 1575377) B1575377
theorem B4490903 : Blo 1048611 4490903 := bstep (se 1 (by rfl) ⟨3368177, by rfl⟩ : syracuseStep 4490903 = 6736355) B6736355
theorem B1771159 : Blo 1048611 1771159 := bstep (se 1 (by rfl) ⟨1328369, by rfl⟩ : syracuseStep 1771159 = 2656739) B2656739
theorem B1181335 : Blo 1048611 1181335 := bstep (se 1 (by rfl) ⟨886001, by rfl⟩ : syracuseStep 1181335 = 1772003) B1772003
theorem B1050263 : Blo 1048611 1050263 := bstep (se 1 (by rfl) ⟨787697, by rfl⟩ : syracuseStep 1050263 = 1575395) B1575395
theorem B1050283 : Blo 1048611 1050283 := bstep (se 1 (by rfl) ⟨787712, by rfl⟩ : syracuseStep 1050283 = 1575425) B1575425
theorem B15140533 : Blo 1048611 15140533 := bstep (se 5 (by rfl) ⟨709712, by rfl⟩ : syracuseStep 15140533 = 1419425) B1419425
theorem B1050295 : Blo 1048611 1050295 := bstep (se 1 (by rfl) ⟨787721, by rfl⟩ : syracuseStep 1050295 = 1575443) B1575443
theorem B1574603 : Blo 1048611 1574603 := bstep (se 1 (by rfl) ⟨1180952, by rfl⟩ : syracuseStep 1574603 = 2361905) B2361905
theorem B1050315 : Blo 1048611 1050315 := bstep (se 1 (by rfl) ⟨787736, by rfl⟩ : syracuseStep 1050315 = 1575473) B1575473
theorem B1574615 : Blo 1048611 1574615 := bstep (se 1 (by rfl) ⟨1180961, by rfl⟩ : syracuseStep 1574615 = 2361923) B2361923
theorem B1050327 : Blo 1048611 1050327 := bstep (se 1 (by rfl) ⟨787745, by rfl⟩ : syracuseStep 1050327 = 1575491) B1575491
theorem B2557657 : Blo 1048611 2557657 := bstep (se 2 (by rfl) ⟨959121, by rfl⟩ : syracuseStep 2557657 = 1918243) B1918243
theorem B1050347 : Blo 1048611 1050347 := bstep (se 1 (by rfl) ⟨787760, by rfl⟩ : syracuseStep 1050347 = 1575521) B1575521
theorem B1050359 : Blo 1048611 1050359 := bstep (se 1 (by rfl) ⟨787769, by rfl⟩ : syracuseStep 1050359 = 1575539) B1575539
theorem B1050379 : Blo 1048611 1050379 := bstep (se 1 (by rfl) ⟨787784, by rfl⟩ : syracuseStep 1050379 = 1575569) B1575569
theorem B1050391 : Blo 1048611 1050391 := bstep (se 1 (by rfl) ⟨787793, by rfl⟩ : syracuseStep 1050391 = 1575587) B1575587
theorem B2361113 : Blo 1048611 2361113 := bstep (se 2 (by rfl) ⟨885417, by rfl⟩ : syracuseStep 2361113 = 1770835) B1770835
theorem B1574681 : Blo 1048611 1574681 := bstep (se 2 (by rfl) ⟨590505, by rfl⟩ : syracuseStep 1574681 = 1181011) B1181011
theorem B1050411 : Blo 1048611 1050411 := bstep (se 1 (by rfl) ⟨787808, by rfl⟩ : syracuseStep 1050411 = 1575617) B1575617
theorem B1050423 : Blo 1048611 1050423 := bstep (se 1 (by rfl) ⟨787817, by rfl⟩ : syracuseStep 1050423 = 1575635) B1575635
theorem B1181515 : Blo 1048611 1181515 := bstep (se 1 (by rfl) ⟨886136, by rfl⟩ : syracuseStep 1181515 = 1772273) B1772273
theorem B1050443 : Blo 1048611 1050443 := bstep (se 1 (by rfl) ⟨787832, by rfl⟩ : syracuseStep 1050443 = 1575665) B1575665
theorem B1050455 : Blo 1048611 1050455 := bstep (se 1 (by rfl) ⟨787841, by rfl⟩ : syracuseStep 1050455 = 1575683) B1575683
theorem B1050475 : Blo 1048611 1050475 := bstep (se 1 (by rfl) ⟨787856, by rfl⟩ : syracuseStep 1050475 = 1575713) B1575713
theorem B2361203 : Blo 1048611 2361203 := bstep (se 1 (by rfl) ⟨1770902, by rfl⟩ : syracuseStep 2361203 = 3541805) B3541805
theorem B1050487 : Blo 1048611 1050487 := bstep (se 1 (by rfl) ⟨787865, by rfl⟩ : syracuseStep 1050487 = 1575731) B1575731
theorem B1574795 : Blo 1048611 1574795 := bstep (se 1 (by rfl) ⟨1181096, by rfl⟩ : syracuseStep 1574795 = 2362193) B2362193
theorem B1050507 : Blo 1048611 1050507 := bstep (se 1 (by rfl) ⟨787880, by rfl⟩ : syracuseStep 1050507 = 1575761) B1575761
theorem B7964567 : Blo 1048611 7964567 := bstep (se 1 (by rfl) ⟨5973425, by rfl⟩ : syracuseStep 7964567 = 11946851) B11946851
theorem B5310359 : Blo 1048611 5310359 := bstep (se 1 (by rfl) ⟨3982769, by rfl⟩ : syracuseStep 5310359 = 7965539) B7965539
theorem B3540887 : Blo 1048611 3540887 := bstep (se 1 (by rfl) ⟨2655665, by rfl⟩ : syracuseStep 3540887 = 5311331) B5311331
theorem B2361239 : Blo 1048611 2361239 := bstep (se 1 (by rfl) ⟨1770929, by rfl⟩ : syracuseStep 2361239 = 3541859) B3541859
theorem B1574807 : Blo 1048611 1574807 := bstep (se 1 (by rfl) ⟨1181105, by rfl⟩ : syracuseStep 1574807 = 2362211) B2362211
theorem B1050519 : Blo 1048611 1050519 := bstep (se 1 (by rfl) ⟨787889, by rfl⟩ : syracuseStep 1050519 = 1575779) B1575779
theorem B1050539 : Blo 1048611 1050539 := bstep (se 1 (by rfl) ⟨787904, by rfl⟩ : syracuseStep 1050539 = 1575809) B1575809
theorem B1181623 : Blo 1048611 1181623 := bstep (se 1 (by rfl) ⟨886217, by rfl⟩ : syracuseStep 1181623 = 1772435) B1772435
theorem B1050551 : Blo 1048611 1050551 := bstep (se 1 (by rfl) ⟨787913, by rfl⟩ : syracuseStep 1050551 = 1575827) B1575827
theorem B1050571 : Blo 1048611 1050571 := bstep (se 1 (by rfl) ⟨787928, by rfl⟩ : syracuseStep 1050571 = 1575857) B1575857
theorem B1050583 : Blo 1048611 1050583 := bstep (se 1 (by rfl) ⟨787937, by rfl⟩ : syracuseStep 1050583 = 1575875) B1575875
theorem B1574873 : Blo 1048611 1574873 := bstep (se 2 (by rfl) ⟨590577, by rfl⟩ : syracuseStep 1574873 = 1181155) B1181155
theorem B1050603 : Blo 1048611 1050603 := bstep (se 1 (by rfl) ⟨787952, by rfl⟩ : syracuseStep 1050603 = 1575905) B1575905
theorem B1050615 : Blo 1048611 1050615 := bstep (se 1 (by rfl) ⟨787961, by rfl⟩ : syracuseStep 1050615 = 1575923) B1575923
theorem B1050635 : Blo 1048611 1050635 := bstep (se 1 (by rfl) ⟨787976, by rfl⟩ : syracuseStep 1050635 = 1575953) B1575953
theorem B1050647 : Blo 1048611 1050647 := bstep (se 1 (by rfl) ⟨787985, by rfl⟩ : syracuseStep 1050647 = 1575971) B1575971
theorem B1050667 : Blo 1048611 1050667 := bstep (se 1 (by rfl) ⟨788000, by rfl⟩ : syracuseStep 1050667 = 1576001) B1576001
theorem B1050679 : Blo 1048611 1050679 := bstep (se 1 (by rfl) ⟨788009, by rfl⟩ : syracuseStep 1050679 = 1576019) B1576019
theorem B2361419 : Blo 1048611 2361419 := bstep (se 1 (by rfl) ⟨1771064, by rfl⟩ : syracuseStep 2361419 = 3542129) B3542129
theorem B1574987 : Blo 1048611 1574987 := bstep (se 1 (by rfl) ⟨1181240, by rfl⟩ : syracuseStep 1574987 = 2362481) B2362481
theorem B1050699 : Blo 1048611 1050699 := bstep (se 1 (by rfl) ⟨788024, by rfl⟩ : syracuseStep 1050699 = 1576049) B1576049
theorem B1574999 : Blo 1048611 1574999 := bstep (se 1 (by rfl) ⟨1181249, by rfl⟩ : syracuseStep 1574999 = 2362499) B2362499
theorem B1050711 : Blo 1048611 1050711 := bstep (se 1 (by rfl) ⟨788033, by rfl⟩ : syracuseStep 1050711 = 1576067) B1576067
theorem B1181803 : Blo 1048611 1181803 := bstep (se 1 (by rfl) ⟨886352, by rfl⟩ : syracuseStep 1181803 = 1772705) B1772705
theorem B1050731 : Blo 1048611 1050731 := bstep (se 1 (by rfl) ⟨788048, by rfl⟩ : syracuseStep 1050731 = 1576097) B1576097
theorem B1050743 : Blo 1048611 1050743 := bstep (se 1 (by rfl) ⟨788057, by rfl⟩ : syracuseStep 1050743 = 1576115) B1576115
theorem B2361473 : Blo 1048611 2361473 := bstep (se 2 (by rfl) ⟨885552, by rfl⟩ : syracuseStep 2361473 = 1771105) B1771105
theorem B1050763 : Blo 1048611 1050763 := bstep (se 1 (by rfl) ⟨788072, by rfl⟩ : syracuseStep 1050763 = 1576145) B1576145
theorem B1050775 : Blo 1048611 1050775 := bstep (se 1 (by rfl) ⟨788081, by rfl⟩ : syracuseStep 1050775 = 1576163) B1576163
theorem B1575065 : Blo 1048611 1575065 := bstep (se 2 (by rfl) ⟨590649, by rfl⟩ : syracuseStep 1575065 = 1181299) B1181299
theorem B1050795 : Blo 1048611 1050795 := bstep (se 1 (by rfl) ⟨788096, by rfl⟩ : syracuseStep 1050795 = 1576193) B1576193
theorem B2656435 : Blo 1048611 2656435 := bstep (se 1 (by rfl) ⟨1992326, by rfl⟩ : syracuseStep 2656435 = 3984653) B3984653
theorem B1050807 : Blo 1048611 1050807 := bstep (se 1 (by rfl) ⟨788105, by rfl⟩ : syracuseStep 1050807 = 1576211) B1576211
theorem B1050827 : Blo 1048611 1050827 := bstep (se 1 (by rfl) ⟨788120, by rfl⟩ : syracuseStep 1050827 = 1576241) B1576241
theorem B1181911 : Blo 1048611 1181911 := bstep (se 1 (by rfl) ⟨886433, by rfl⟩ : syracuseStep 1181911 = 1772867) B1772867
theorem B1050839 : Blo 1048611 1050839 := bstep (se 1 (by rfl) ⟨788129, by rfl⟩ : syracuseStep 1050839 = 1576259) B1576259
theorem B1050859 : Blo 1048611 1050859 := bstep (se 1 (by rfl) ⟨788144, by rfl⟩ : syracuseStep 1050859 = 1576289) B1576289
theorem B1050871 : Blo 1048611 1050871 := bstep (se 1 (by rfl) ⟨788153, by rfl⟩ : syracuseStep 1050871 = 1576307) B1576307
theorem B1771787 : Blo 1048611 1771787 := bstep (se 1 (by rfl) ⟨1328840, by rfl⟩ : syracuseStep 1771787 = 2657681) B2657681
theorem B1575179 : Blo 1048611 1575179 := bstep (se 1 (by rfl) ⟨1181384, by rfl⟩ : syracuseStep 1575179 = 2362769) B2362769
theorem B1050891 : Blo 1048611 1050891 := bstep (se 1 (by rfl) ⟨788168, by rfl⟩ : syracuseStep 1050891 = 1576337) B1576337
theorem B1575191 : Blo 1048611 1575191 := bstep (se 1 (by rfl) ⟨1181393, by rfl⟩ : syracuseStep 1575191 = 2362787) B2362787
theorem B1050903 : Blo 1048611 1050903 := bstep (se 1 (by rfl) ⟨788177, by rfl⟩ : syracuseStep 1050903 = 1576355) B1576355
theorem B1050923 : Blo 1048611 1050923 := bstep (se 1 (by rfl) ⟨788192, by rfl⟩ : syracuseStep 1050923 = 1576385) B1576385
theorem B27298093 : Blo 1048611 27298093 := bstep (se 3 (by rfl) ⟨5118392, by rfl⟩ : syracuseStep 27298093 = 10236785) B10236785
theorem B1050935 : Blo 1048611 1050935 := bstep (se 1 (by rfl) ⟨788201, by rfl⟩ : syracuseStep 1050935 = 1576403) B1576403
theorem B2656577 : Blo 1048611 2656577 := bstep (se 2 (by rfl) ⟨996216, by rfl⟩ : syracuseStep 2656577 = 1992433) B1992433
theorem B1050955 : Blo 1048611 1050955 := bstep (se 1 (by rfl) ⟨788216, by rfl⟩ : syracuseStep 1050955 = 1576433) B1576433
theorem B1050967 : Blo 1048611 1050967 := bstep (se 1 (by rfl) ⟨788225, by rfl⟩ : syracuseStep 1050967 = 1576451) B1576451
theorem B2361689 : Blo 1048611 2361689 := bstep (se 2 (by rfl) ⟨885633, by rfl⟩ : syracuseStep 2361689 = 1771267) B1771267
theorem B1575257 : Blo 1048611 1575257 := bstep (se 2 (by rfl) ⟨590721, by rfl⟩ : syracuseStep 1575257 = 1181443) B1181443
theorem B1050987 : Blo 1048611 1050987 := bstep (se 1 (by rfl) ⟨788240, by rfl⟩ : syracuseStep 1050987 = 1576481) B1576481
theorem B1050999 : Blo 1048611 1050999 := bstep (se 1 (by rfl) ⟨788249, by rfl⟩ : syracuseStep 1050999 = 1576499) B1576499
theorem B1771915 : Blo 1048611 1771915 := bstep (se 1 (by rfl) ⟨1328936, by rfl⟩ : syracuseStep 1771915 = 2657873) B2657873
theorem B1182091 : Blo 1048611 1182091 := bstep (se 1 (by rfl) ⟨886568, by rfl⟩ : syracuseStep 1182091 = 1773137) B1773137
theorem B1051019 : Blo 1048611 1051019 := bstep (se 1 (by rfl) ⟨788264, by rfl⟩ : syracuseStep 1051019 = 1576529) B1576529
theorem B1051031 : Blo 1048611 1051031 := bstep (se 1 (by rfl) ⟨788273, by rfl⟩ : syracuseStep 1051031 = 1576547) B1576547
theorem B1051051 : Blo 1048611 1051051 := bstep (se 1 (by rfl) ⟨788288, by rfl⟩ : syracuseStep 1051051 = 1576577) B1576577
theorem B3541427 : Blo 1048611 3541427 := bstep (se 1 (by rfl) ⟨2656070, by rfl⟩ : syracuseStep 3541427 = 5312141) B5312141
theorem B2361779 : Blo 1048611 2361779 := bstep (se 1 (by rfl) ⟨1771334, by rfl⟩ : syracuseStep 2361779 = 3542669) B3542669
theorem B1051063 : Blo 1048611 1051063 := bstep (se 1 (by rfl) ⟨788297, by rfl⟩ : syracuseStep 1051063 = 1576595) B1576595
theorem B8980915 : Blo 1048611 8980915 := bstep (se 1 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 8980915 = 13471373) B13471373
theorem B1575371 : Blo 1048611 1575371 := bstep (se 1 (by rfl) ⟨1181528, by rfl⟩ : syracuseStep 1575371 = 2363057) B2363057
theorem B1051083 : Blo 1048611 1051083 := bstep (se 1 (by rfl) ⟨788312, by rfl⟩ : syracuseStep 1051083 = 1576625) B1576625
theorem B2361815 : Blo 1048611 2361815 := bstep (se 1 (by rfl) ⟨1771361, by rfl⟩ : syracuseStep 2361815 = 3542723) B3542723
theorem B1575383 : Blo 1048611 1575383 := bstep (se 1 (by rfl) ⟨1181537, by rfl⟩ : syracuseStep 1575383 = 2363075) B2363075
theorem B1051095 : Blo 1048611 1051095 := bstep (se 1 (by rfl) ⟨788321, by rfl⟩ : syracuseStep 1051095 = 1576643) B1576643
theorem B1051115 : Blo 1048611 1051115 := bstep (se 1 (by rfl) ⟨788336, by rfl⟩ : syracuseStep 1051115 = 1576673) B1576673
theorem B1182199 : Blo 1048611 1182199 := bstep (se 1 (by rfl) ⟨886649, by rfl⟩ : syracuseStep 1182199 = 1773299) B1773299
theorem B1051127 : Blo 1048611 1051127 := bstep (se 1 (by rfl) ⟨788345, by rfl⟩ : syracuseStep 1051127 = 1576691) B1576691
theorem B1051147 : Blo 1048611 1051147 := bstep (se 1 (by rfl) ⟨788360, by rfl⟩ : syracuseStep 1051147 = 1576721) B1576721
theorem B1051159 : Blo 1048611 1051159 := bstep (se 1 (by rfl) ⟨788369, by rfl⟩ : syracuseStep 1051159 = 1576739) B1576739
theorem B1772057 : Blo 1048611 1772057 := bstep (se 2 (by rfl) ⟨664521, by rfl⟩ : syracuseStep 1772057 = 1329043) B1329043
theorem B1575449 : Blo 1048611 1575449 := bstep (se 2 (by rfl) ⟨590793, by rfl⟩ : syracuseStep 1575449 = 1181587) B1181587
theorem B1051179 : Blo 1048611 1051179 := bstep (se 1 (by rfl) ⟨788384, by rfl⟩ : syracuseStep 1051179 = 1576769) B1576769
theorem B1051191 : Blo 1048611 1051191 := bstep (se 1 (by rfl) ⟨788393, by rfl⟩ : syracuseStep 1051191 = 1576787) B1576787
theorem B1051211 : Blo 1048611 1051211 := bstep (se 1 (by rfl) ⟨788408, by rfl⟩ : syracuseStep 1051211 = 1576817) B1576817
theorem B1051223 : Blo 1048611 1051223 := bstep (se 1 (by rfl) ⟨788417, by rfl⟩ : syracuseStep 1051223 = 1576835) B1576835
theorem B2132569 : Blo 1048611 2132569 := bstep (se 2 (by rfl) ⟨799713, by rfl⟩ : syracuseStep 2132569 = 1599427) B1599427
theorem B1051243 : Blo 1048611 1051243 := bstep (se 1 (by rfl) ⟨788432, by rfl⟩ : syracuseStep 1051243 = 1576865) B1576865
theorem B1051255 : Blo 1048611 1051255 := bstep (se 1 (by rfl) ⟨788441, by rfl⟩ : syracuseStep 1051255 = 1576883) B1576883
theorem B10783363 : Blo 1048611 10783363 := bstep (se 1 (by rfl) ⟨8087522, by rfl⟩ : syracuseStep 10783363 = 16175045) B16175045
theorem B2361995 : Blo 1048611 2361995 := bstep (se 1 (by rfl) ⟨1771496, by rfl⟩ : syracuseStep 2361995 = 3542993) B3542993
theorem B1575563 : Blo 1048611 1575563 := bstep (se 1 (by rfl) ⟨1181672, by rfl⟩ : syracuseStep 1575563 = 2363345) B2363345
theorem B1051275 : Blo 1048611 1051275 := bstep (se 1 (by rfl) ⟨788456, by rfl⟩ : syracuseStep 1051275 = 1576913) B1576913
theorem B1575575 : Blo 1048611 1575575 := bstep (se 1 (by rfl) ⟨1181681, by rfl⟩ : syracuseStep 1575575 = 2363363) B2363363
theorem B1051287 : Blo 1048611 1051287 := bstep (se 1 (by rfl) ⟨788465, by rfl⟩ : syracuseStep 1051287 = 1576931) B1576931
theorem B1772185 : Blo 1048611 1772185 := bstep (se 2 (by rfl) ⟨664569, by rfl⟩ : syracuseStep 1772185 = 1329139) B1329139
theorem B1182379 : Blo 1048611 1182379 := bstep (se 1 (by rfl) ⟨886784, by rfl⟩ : syracuseStep 1182379 = 1773569) B1773569
theorem B1051307 : Blo 1048611 1051307 := bstep (se 1 (by rfl) ⟨788480, by rfl⟩ : syracuseStep 1051307 = 1576961) B1576961
theorem B2132659 : Blo 1048611 2132659 := bstep (se 1 (by rfl) ⟨1599494, by rfl⟩ : syracuseStep 2132659 = 3198989) B3198989
theorem B1051319 : Blo 1048611 1051319 := bstep (se 1 (by rfl) ⟨788489, by rfl⟩ : syracuseStep 1051319 = 1576979) B1576979
theorem B3541697 : Blo 1048611 3541697 := bstep (se 2 (by rfl) ⟨1328136, by rfl⟩ : syracuseStep 3541697 = 2656273) B2656273
theorem B2362049 : Blo 1048611 2362049 := bstep (se 2 (by rfl) ⟨885768, by rfl⟩ : syracuseStep 2362049 = 1771537) B1771537
theorem B1051339 : Blo 1048611 1051339 := bstep (se 1 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 1051339 = 1577009) B1577009
theorem B1051351 : Blo 1048611 1051351 := bstep (se 1 (by rfl) ⟨788513, by rfl⟩ : syracuseStep 1051351 = 1577027) B1577027
theorem B1575641 : Blo 1048611 1575641 := bstep (se 2 (by rfl) ⟨590865, by rfl⟩ : syracuseStep 1575641 = 1181731) B1181731
theorem B1051371 : Blo 1048611 1051371 := bstep (se 1 (by rfl) ⟨788528, by rfl⟩ : syracuseStep 1051371 = 1577057) B1577057
theorem B43158257 : Blo 1048611 43158257 := bstep (se 2 (by rfl) ⟨16184346, by rfl⟩ : syracuseStep 43158257 = 32368693) B32368693
theorem B1051383 : Blo 1048611 1051383 := bstep (se 1 (by rfl) ⟨788537, by rfl⟩ : syracuseStep 1051383 = 1577075) B1577075
theorem B1051403 : Blo 1048611 1051403 := bstep (se 1 (by rfl) ⟨788552, by rfl⟩ : syracuseStep 1051403 = 1577105) B1577105
theorem B1182487 : Blo 1048611 1182487 := bstep (se 1 (by rfl) ⟨886865, by rfl⟩ : syracuseStep 1182487 = 1773731) B1773731
theorem B1051415 : Blo 1048611 1051415 := bstep (se 1 (by rfl) ⟨788561, by rfl⟩ : syracuseStep 1051415 = 1577123) B1577123
theorem B1051435 : Blo 1048611 1051435 := bstep (se 1 (by rfl) ⟨788576, by rfl⟩ : syracuseStep 1051435 = 1577153) B1577153
theorem B1051447 : Blo 1048611 1051447 := bstep (se 1 (by rfl) ⟨788585, by rfl⟩ : syracuseStep 1051447 = 1577171) B1577171
theorem B1575755 : Blo 1048611 1575755 := bstep (se 1 (by rfl) ⟨1181816, by rfl⟩ : syracuseStep 1575755 = 2363633) B2363633
theorem B1051467 : Blo 1048611 1051467 := bstep (se 1 (by rfl) ⟨788600, by rfl⟩ : syracuseStep 1051467 = 1577201) B1577201
theorem B1575767 : Blo 1048611 1575767 := bstep (se 1 (by rfl) ⟨1181825, by rfl⟩ : syracuseStep 1575767 = 2363651) B2363651
theorem B1051479 : Blo 1048611 1051479 := bstep (se 1 (by rfl) ⟨788609, by rfl⟩ : syracuseStep 1051479 = 1577219) B1577219
theorem B1051499 : Blo 1048611 1051499 := bstep (se 1 (by rfl) ⟨788624, by rfl⟩ : syracuseStep 1051499 = 1577249) B1577249
theorem B1051511 : Blo 1048611 1051511 := bstep (se 1 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 1051511 = 1577267) B1577267
theorem B1051531 : Blo 1048611 1051531 := bstep (se 1 (by rfl) ⟨788648, by rfl⟩ : syracuseStep 1051531 = 1577297) B1577297
theorem B1051543 : Blo 1048611 1051543 := bstep (se 1 (by rfl) ⟨788657, by rfl⟩ : syracuseStep 1051543 = 1577315) B1577315
theorem B2362265 : Blo 1048611 2362265 := bstep (se 2 (by rfl) ⟨885849, by rfl⟩ : syracuseStep 2362265 = 1771699) B1771699
theorem B1575833 : Blo 1048611 1575833 := bstep (se 2 (by rfl) ⟨590937, by rfl⟩ : syracuseStep 1575833 = 1181875) B1181875
theorem B1051563 : Blo 1048611 1051563 := bstep (se 1 (by rfl) ⟨788672, by rfl⟩ : syracuseStep 1051563 = 1577345) B1577345
theorem B1051575 : Blo 1048611 1051575 := bstep (se 1 (by rfl) ⟨788681, by rfl⟩ : syracuseStep 1051575 = 1577363) B1577363
theorem B1182667 : Blo 1048611 1182667 := bstep (se 1 (by rfl) ⟨887000, by rfl⟩ : syracuseStep 1182667 = 1774001) B1774001
theorem B1051595 : Blo 1048611 1051595 := bstep (se 1 (by rfl) ⟨788696, by rfl⟩ : syracuseStep 1051595 = 1577393) B1577393
theorem B4492235 : Blo 1048611 4492235 := bstep (se 1 (by rfl) ⟨3369176, by rfl⟩ : syracuseStep 4492235 = 6738353) B6738353
theorem B1051607 : Blo 1048611 1051607 := bstep (se 1 (by rfl) ⟨788705, by rfl⟩ : syracuseStep 1051607 = 1577411) B1577411
theorem B5049305 : Blo 1048611 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B1051627 : Blo 1048611 1051627 := bstep (se 1 (by rfl) ⟨788720, by rfl⟩ : syracuseStep 1051627 = 1577441) B1577441
theorem B2362355 : Blo 1048611 2362355 := bstep (se 1 (by rfl) ⟨1771766, by rfl⟩ : syracuseStep 2362355 = 3543533) B3543533
theorem B1051639 : Blo 1048611 1051639 := bstep (se 1 (by rfl) ⟨788729, by rfl⟩ : syracuseStep 1051639 = 1577459) B1577459
theorem B1575947 : Blo 1048611 1575947 := bstep (se 1 (by rfl) ⟨1181960, by rfl⟩ : syracuseStep 1575947 = 2363921) B2363921
theorem B1051659 : Blo 1048611 1051659 := bstep (se 1 (by rfl) ⟨788744, by rfl⟩ : syracuseStep 1051659 = 1577489) B1577489
theorem B2362391 : Blo 1048611 2362391 := bstep (se 1 (by rfl) ⟨1771793, by rfl⟩ : syracuseStep 2362391 = 3543587) B3543587
theorem B1575959 : Blo 1048611 1575959 := bstep (se 1 (by rfl) ⟨1181969, by rfl⟩ : syracuseStep 1575959 = 2363939) B2363939
theorem B1051671 : Blo 1048611 1051671 := bstep (se 1 (by rfl) ⟨788753, by rfl⟩ : syracuseStep 1051671 = 1577507) B1577507
theorem B1051691 : Blo 1048611 1051691 := bstep (se 1 (by rfl) ⟨788768, by rfl⟩ : syracuseStep 1051691 = 1577537) B1577537
theorem B1182775 : Blo 1048611 1182775 := bstep (se 1 (by rfl) ⟨887081, by rfl⟩ : syracuseStep 1182775 = 1774163) B1774163
theorem B1051703 : Blo 1048611 1051703 := bstep (se 1 (by rfl) ⟨788777, by rfl⟩ : syracuseStep 1051703 = 1577555) B1577555
theorem B1051723 : Blo 1048611 1051723 := bstep (se 1 (by rfl) ⟨788792, by rfl⟩ : syracuseStep 1051723 = 1577585) B1577585
theorem B1051735 : Blo 1048611 1051735 := bstep (se 1 (by rfl) ⟨788801, by rfl⟩ : syracuseStep 1051735 = 1577603) B1577603
theorem B1576025 : Blo 1048611 1576025 := bstep (se 2 (by rfl) ⟨591009, by rfl⟩ : syracuseStep 1576025 = 1182019) B1182019
theorem B8621149 : Blo 1048611 8621149 := bstep (se 3 (by rfl) ⟨1616465, by rfl⟩ : syracuseStep 8621149 = 3232931) B3232931
theorem B1051755 : Blo 1048611 1051755 := bstep (se 1 (by rfl) ⟨788816, by rfl⟩ : syracuseStep 1051755 = 1577633) B1577633
theorem B1051767 : Blo 1048611 1051767 := bstep (se 1 (by rfl) ⟨788825, by rfl⟩ : syracuseStep 1051767 = 1577651) B1577651
theorem B1051787 : Blo 1048611 1051787 := bstep (se 1 (by rfl) ⟨788840, by rfl⟩ : syracuseStep 1051787 = 1577681) B1577681
theorem B1051799 : Blo 1048611 1051799 := bstep (se 1 (by rfl) ⟨788849, by rfl⟩ : syracuseStep 1051799 = 1577699) B1577699
theorem B1051819 : Blo 1048611 1051819 := bstep (se 1 (by rfl) ⟨788864, by rfl⟩ : syracuseStep 1051819 = 1577729) B1577729
theorem B1051831 : Blo 1048611 1051831 := bstep (se 1 (by rfl) ⟨788873, by rfl⟩ : syracuseStep 1051831 = 1577747) B1577747
theorem B2362571 : Blo 1048611 2362571 := bstep (se 1 (by rfl) ⟨1771928, by rfl⟩ : syracuseStep 2362571 = 3543857) B3543857
theorem B1576139 : Blo 1048611 1576139 := bstep (se 1 (by rfl) ⟨1182104, by rfl⟩ : syracuseStep 1576139 = 2364209) B2364209
theorem B1051851 : Blo 1048611 1051851 := bstep (se 1 (by rfl) ⟨788888, by rfl⟩ : syracuseStep 1051851 = 1577777) B1577777
theorem B1772759 : Blo 1048611 1772759 := bstep (se 1 (by rfl) ⟨1329569, by rfl⟩ : syracuseStep 1772759 = 2659139) B2659139
theorem B1576151 : Blo 1048611 1576151 := bstep (se 1 (by rfl) ⟨1182113, by rfl⟩ : syracuseStep 1576151 = 2364227) B2364227
theorem B1051863 : Blo 1048611 1051863 := bstep (se 1 (by rfl) ⟨788897, by rfl⟩ : syracuseStep 1051863 = 1577795) B1577795
theorem B3542237 : Blo 1048611 3542237 := bstep (se 3 (by rfl) ⟨664169, by rfl⟩ : syracuseStep 3542237 = 1328339) B1328339
theorem B1051883 : Blo 1048611 1051883 := bstep (se 1 (by rfl) ⟨788912, by rfl⟩ : syracuseStep 1051883 = 1577825) B1577825
theorem B1182955 : Blo 1048611 1182955 := bstep (se 1 (by rfl) ⟨887216, by rfl⟩ : syracuseStep 1182955 = 1774433) B1774433
theorem B1051895 : Blo 1048611 1051895 := bstep (se 1 (by rfl) ⟨788921, by rfl⟩ : syracuseStep 1051895 = 1577843) B1577843
theorem B2362625 : Blo 1048611 2362625 := bstep (se 2 (by rfl) ⟨885984, by rfl⟩ : syracuseStep 2362625 = 1771969) B1771969
theorem B1051915 : Blo 1048611 1051915 := bstep (se 1 (by rfl) ⟨788936, by rfl⟩ : syracuseStep 1051915 = 1577873) B1577873
theorem B1051927 : Blo 1048611 1051927 := bstep (se 1 (by rfl) ⟨788945, by rfl⟩ : syracuseStep 1051927 = 1577891) B1577891
theorem B1576217 : Blo 1048611 1576217 := bstep (se 2 (by rfl) ⟨591081, by rfl⟩ : syracuseStep 1576217 = 1182163) B1182163
theorem B1051947 : Blo 1048611 1051947 := bstep (se 1 (by rfl) ⟨788960, by rfl⟩ : syracuseStep 1051947 = 1577921) B1577921
theorem B1051959 : Blo 1048611 1051959 := bstep (se 1 (by rfl) ⟨788969, by rfl⟩ : syracuseStep 1051959 = 1577939) B1577939
theorem B1051979 : Blo 1048611 1051979 := bstep (se 1 (by rfl) ⟨788984, by rfl⟩ : syracuseStep 1051979 = 1577969) B1577969
theorem B1772887 : Blo 1048611 1772887 := bstep (se 1 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 1772887 = 2659331) B2659331
theorem B1183063 : Blo 1048611 1183063 := bstep (se 1 (by rfl) ⟨887297, by rfl⟩ : syracuseStep 1183063 = 1774595) B1774595
theorem B1051991 : Blo 1048611 1051991 := bstep (se 1 (by rfl) ⟨788993, by rfl⟩ : syracuseStep 1051991 = 1577987) B1577987
theorem B1052011 : Blo 1048611 1052011 := bstep (se 1 (by rfl) ⟨789008, by rfl⟩ : syracuseStep 1052011 = 1578017) B1578017
theorem B1052023 : Blo 1048611 1052023 := bstep (se 1 (by rfl) ⟨789017, by rfl⟩ : syracuseStep 1052023 = 1578035) B1578035
theorem B1576331 : Blo 1048611 1576331 := bstep (se 1 (by rfl) ⟨1182248, by rfl⟩ : syracuseStep 1576331 = 2364497) B2364497
theorem B1052043 : Blo 1048611 1052043 := bstep (se 1 (by rfl) ⟨789032, by rfl⟩ : syracuseStep 1052043 = 1578065) B1578065
theorem B1576343 : Blo 1048611 1576343 := bstep (se 1 (by rfl) ⟨1182257, by rfl⟩ : syracuseStep 1576343 = 2364515) B2364515
theorem B1052055 : Blo 1048611 1052055 := bstep (se 1 (by rfl) ⟨789041, by rfl⟩ : syracuseStep 1052055 = 1578083) B1578083
theorem B1052075 : Blo 1048611 1052075 := bstep (se 1 (by rfl) ⟨789056, by rfl⟩ : syracuseStep 1052075 = 1578113) B1578113
theorem B1052087 : Blo 1048611 1052087 := bstep (se 1 (by rfl) ⟨789065, by rfl⟩ : syracuseStep 1052087 = 1578131) B1578131
theorem B1052107 : Blo 1048611 1052107 := bstep (se 1 (by rfl) ⟨789080, by rfl⟩ : syracuseStep 1052107 = 1578161) B1578161
theorem B1052119 : Blo 1048611 1052119 := bstep (se 1 (by rfl) ⟨789089, by rfl⟩ : syracuseStep 1052119 = 1578179) B1578179
theorem B2362841 : Blo 1048611 2362841 := bstep (se 2 (by rfl) ⟨886065, by rfl⟩ : syracuseStep 2362841 = 1772131) B1772131
theorem B1576409 : Blo 1048611 1576409 := bstep (se 2 (by rfl) ⟨591153, by rfl⟩ : syracuseStep 1576409 = 1182307) B1182307
theorem B1052139 : Blo 1048611 1052139 := bstep (se 1 (by rfl) ⟨789104, by rfl⟩ : syracuseStep 1052139 = 1578209) B1578209
theorem B1052151 : Blo 1048611 1052151 := bstep (se 1 (by rfl) ⟨789113, by rfl⟩ : syracuseStep 1052151 = 1578227) B1578227
theorem B1183243 : Blo 1048611 1183243 := bstep (se 1 (by rfl) ⟨887432, by rfl⟩ : syracuseStep 1183243 = 1774865) B1774865
theorem B1052171 : Blo 1048611 1052171 := bstep (se 1 (by rfl) ⟨789128, by rfl⟩ : syracuseStep 1052171 = 1578257) B1578257
theorem B4492817 : Blo 1048611 4492817 := bstep (se 2 (by rfl) ⟨1684806, by rfl⟩ : syracuseStep 4492817 = 3369613) B3369613
theorem B1052183 : Blo 1048611 1052183 := bstep (se 1 (by rfl) ⟨789137, by rfl⟩ : syracuseStep 1052183 = 1578275) B1578275
theorem B1052203 : Blo 1048611 1052203 := bstep (se 1 (by rfl) ⟨789152, by rfl⟩ : syracuseStep 1052203 = 1578305) B1578305
theorem B2657843 : Blo 1048611 2657843 := bstep (se 1 (by rfl) ⟨1993382, by rfl⟩ : syracuseStep 2657843 = 3986765) B3986765
theorem B2362931 : Blo 1048611 2362931 := bstep (se 1 (by rfl) ⟨1772198, by rfl⟩ : syracuseStep 2362931 = 3544397) B3544397
theorem B1052215 : Blo 1048611 1052215 := bstep (se 1 (by rfl) ⟨789161, by rfl⟩ : syracuseStep 1052215 = 1578323) B1578323
theorem B1576523 : Blo 1048611 1576523 := bstep (se 1 (by rfl) ⟨1182392, by rfl⟩ : syracuseStep 1576523 = 2364785) B2364785
theorem B1052235 : Blo 1048611 1052235 := bstep (se 1 (by rfl) ⟨789176, by rfl⟩ : syracuseStep 1052235 = 1578353) B1578353
theorem B2362967 : Blo 1048611 2362967 := bstep (se 1 (by rfl) ⟨1772225, by rfl⟩ : syracuseStep 2362967 = 3544451) B3544451
theorem B1576535 : Blo 1048611 1576535 := bstep (se 1 (by rfl) ⟨1182401, by rfl⟩ : syracuseStep 1576535 = 2364803) B2364803
theorem B1052247 : Blo 1048611 1052247 := bstep (se 1 (by rfl) ⟨789185, by rfl⟩ : syracuseStep 1052247 = 1578371) B1578371
theorem B1052267 : Blo 1048611 1052267 := bstep (se 1 (by rfl) ⟨789200, by rfl⟩ : syracuseStep 1052267 = 1578401) B1578401
theorem B1183351 : Blo 1048611 1183351 := bstep (se 1 (by rfl) ⟨887513, by rfl⟩ : syracuseStep 1183351 = 1775027) B1775027
theorem B1052279 : Blo 1048611 1052279 := bstep (se 1 (by rfl) ⟨789209, by rfl⟩ : syracuseStep 1052279 = 1578419) B1578419
theorem B1052299 : Blo 1048611 1052299 := bstep (se 1 (by rfl) ⟨789224, by rfl⟩ : syracuseStep 1052299 = 1578449) B1578449
theorem B1052311 : Blo 1048611 1052311 := bstep (se 1 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 1052311 = 1578467) B1578467
theorem B1576601 : Blo 1048611 1576601 := bstep (se 2 (by rfl) ⟨591225, by rfl⟩ : syracuseStep 1576601 = 1182451) B1182451
theorem B1052331 : Blo 1048611 1052331 := bstep (se 1 (by rfl) ⟨789248, by rfl⟩ : syracuseStep 1052331 = 1578497) B1578497
theorem B1052343 : Blo 1048611 1052343 := bstep (se 1 (by rfl) ⟨789257, by rfl⟩ : syracuseStep 1052343 = 1578515) B1578515
theorem B1052363 : Blo 1048611 1052363 := bstep (se 1 (by rfl) ⟨789272, by rfl⟩ : syracuseStep 1052363 = 1578545) B1578545
theorem B1052375 : Blo 1048611 1052375 := bstep (se 1 (by rfl) ⟨789281, by rfl⟩ : syracuseStep 1052375 = 1578563) B1578563
theorem B2395865 : Blo 1048611 2395865 := bstep (se 2 (by rfl) ⟨898449, by rfl⟩ : syracuseStep 2395865 = 1796899) B1796899
theorem B1052395 : Blo 1048611 1052395 := bstep (se 1 (by rfl) ⟨789296, by rfl⟩ : syracuseStep 1052395 = 1578593) B1578593
theorem B1052407 : Blo 1048611 1052407 := bstep (se 1 (by rfl) ⟨789305, by rfl⟩ : syracuseStep 1052407 = 1578611) B1578611
theorem B2363147 : Blo 1048611 2363147 := bstep (se 1 (by rfl) ⟨1772360, by rfl⟩ : syracuseStep 2363147 = 3544721) B3544721
theorem B1576715 : Blo 1048611 1576715 := bstep (se 1 (by rfl) ⟨1182536, by rfl⟩ : syracuseStep 1576715 = 2365073) B2365073
theorem B1052427 : Blo 1048611 1052427 := bstep (se 1 (by rfl) ⟨789320, by rfl⟩ : syracuseStep 1052427 = 1578641) B1578641
theorem B1576727 : Blo 1048611 1576727 := bstep (se 1 (by rfl) ⟨1182545, by rfl⟩ : syracuseStep 1576727 = 2365091) B2365091
theorem B1052439 : Blo 1048611 1052439 := bstep (se 1 (by rfl) ⟨789329, by rfl⟩ : syracuseStep 1052439 = 1578659) B1578659
theorem B1183531 : Blo 1048611 1183531 := bstep (se 1 (by rfl) ⟨887648, by rfl⟩ : syracuseStep 1183531 = 1775297) B1775297
theorem B1052459 : Blo 1048611 1052459 := bstep (se 1 (by rfl) ⟨789344, by rfl⟩ : syracuseStep 1052459 = 1578689) B1578689
theorem B4263725 : Blo 1048611 4263725 := bstep (se 3 (by rfl) ⟨799448, by rfl⟩ : syracuseStep 4263725 = 1598897) B1598897
theorem B1052471 : Blo 1048611 1052471 := bstep (se 1 (by rfl) ⟨789353, by rfl⟩ : syracuseStep 1052471 = 1578707) B1578707
theorem B2363201 : Blo 1048611 2363201 := bstep (se 2 (by rfl) ⟨886200, by rfl⟩ : syracuseStep 2363201 = 1772401) B1772401
theorem B1052491 : Blo 1048611 1052491 := bstep (se 1 (by rfl) ⟨789368, by rfl⟩ : syracuseStep 1052491 = 1578737) B1578737
theorem B1052503 : Blo 1048611 1052503 := bstep (se 1 (by rfl) ⟨789377, by rfl⟩ : syracuseStep 1052503 = 1578755) B1578755
theorem B1576793 : Blo 1048611 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B1052523 : Blo 1048611 1052523 := bstep (se 1 (by rfl) ⟨789392, by rfl⟩ : syracuseStep 1052523 = 1578785) B1578785
theorem B1052535 : Blo 1048611 1052535 := bstep (se 1 (by rfl) ⟨789401, by rfl⟩ : syracuseStep 1052535 = 1578803) B1578803
theorem B1052555 : Blo 1048611 1052555 := bstep (se 1 (by rfl) ⟨789416, by rfl⟩ : syracuseStep 1052555 = 1578833) B1578833
theorem B1183639 : Blo 1048611 1183639 := bstep (se 1 (by rfl) ⟨887729, by rfl⟩ : syracuseStep 1183639 = 1775459) B1775459
theorem B1052567 : Blo 1048611 1052567 := bstep (se 1 (by rfl) ⟨789425, by rfl⟩ : syracuseStep 1052567 = 1578851) B1578851
theorem B1052587 : Blo 1048611 1052587 := bstep (se 1 (by rfl) ⟨789440, by rfl⟩ : syracuseStep 1052587 = 1578881) B1578881
theorem B1052599 : Blo 1048611 1052599 := bstep (se 1 (by rfl) ⟨789449, by rfl⟩ : syracuseStep 1052599 = 1578899) B1578899
theorem B1773515 : Blo 1048611 1773515 := bstep (se 1 (by rfl) ⟨1330136, by rfl⟩ : syracuseStep 1773515 = 2660273) B2660273
theorem B1576907 : Blo 1048611 1576907 := bstep (se 1 (by rfl) ⟨1182680, by rfl⟩ : syracuseStep 1576907 = 2365361) B2365361
theorem B1576919 : Blo 1048611 1576919 := bstep (se 1 (by rfl) ⟨1182689, by rfl⟩ : syracuseStep 1576919 = 2365379) B2365379
theorem B2363417 : Blo 1048611 2363417 := bstep (se 2 (by rfl) ⟨886281, by rfl⟩ : syracuseStep 2363417 = 1772563) B1772563
theorem B1576985 : Blo 1048611 1576985 := bstep (se 2 (by rfl) ⟨591369, by rfl⟩ : syracuseStep 1576985 = 1182739) B1182739
theorem B2658379 : Blo 1048611 2658379 := bstep (se 1 (by rfl) ⟨1993784, by rfl⟩ : syracuseStep 2658379 = 3987569) B3987569
theorem B1773643 : Blo 1048611 1773643 := bstep (se 1 (by rfl) ⟨1330232, by rfl⟩ : syracuseStep 1773643 = 2660465) B2660465
theorem B2527307 : Blo 1048611 2527307 := bstep (se 1 (by rfl) ⟨1895480, by rfl⟩ : syracuseStep 2527307 = 3790961) B3790961
theorem B1183819 : Blo 1048611 1183819 := bstep (se 1 (by rfl) ⟨887864, by rfl⟩ : syracuseStep 1183819 = 1775729) B1775729
theorem B2363507 : Blo 1048611 2363507 := bstep (se 1 (by rfl) ⟨1772630, by rfl⟩ : syracuseStep 2363507 = 3545261) B3545261
theorem B1577099 : Blo 1048611 1577099 := bstep (se 1 (by rfl) ⟨1182824, by rfl⟩ : syracuseStep 1577099 = 2365649) B2365649
theorem B2363543 : Blo 1048611 2363543 := bstep (se 1 (by rfl) ⟨1772657, by rfl⟩ : syracuseStep 2363543 = 3545315) B3545315
theorem B1577111 : Blo 1048611 1577111 := bstep (se 1 (by rfl) ⟨1182833, by rfl⟩ : syracuseStep 1577111 = 2365667) B2365667
theorem B1183927 : Blo 1048611 1183927 := bstep (se 1 (by rfl) ⟨887945, by rfl⟩ : syracuseStep 1183927 = 1775891) B1775891
theorem B2691265 : Blo 1048611 2691265 := bstep (se 2 (by rfl) ⟨1009224, by rfl⟩ : syracuseStep 2691265 = 2018449) B2018449
theorem B2658521 : Blo 1048611 2658521 := bstep (se 2 (by rfl) ⟨996945, by rfl⟩ : syracuseStep 2658521 = 1993891) B1993891
theorem B1773785 : Blo 1048611 1773785 := bstep (se 2 (by rfl) ⟨665169, by rfl⟩ : syracuseStep 1773785 = 1330339) B1330339
theorem B1577177 : Blo 1048611 1577177 := bstep (se 2 (by rfl) ⟨591441, by rfl⟩ : syracuseStep 1577177 = 1182883) B1182883
theorem B7180589 : Blo 1048611 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B3543371 : Blo 1048611 3543371 := bstep (se 1 (by rfl) ⟨2657528, by rfl⟩ : syracuseStep 3543371 = 5315057) B5315057
theorem B2363723 : Blo 1048611 2363723 := bstep (se 1 (by rfl) ⟨1772792, by rfl⟩ : syracuseStep 2363723 = 3545585) B3545585
theorem B1577291 : Blo 1048611 1577291 := bstep (se 1 (by rfl) ⟨1182968, by rfl⟩ : syracuseStep 1577291 = 2365937) B2365937
theorem B1577303 : Blo 1048611 1577303 := bstep (se 1 (by rfl) ⟨1182977, by rfl⟩ : syracuseStep 1577303 = 2365955) B2365955
theorem B1773913 : Blo 1048611 1773913 := bstep (se 2 (by rfl) ⟨665217, by rfl⟩ : syracuseStep 1773913 = 1330435) B1330435
theorem B1184107 : Blo 1048611 1184107 := bstep (se 1 (by rfl) ⟨888080, by rfl⟩ : syracuseStep 1184107 = 1776161) B1776161
theorem B2363777 : Blo 1048611 2363777 := bstep (se 2 (by rfl) ⟨886416, by rfl⟩ : syracuseStep 2363777 = 1772833) B1772833
theorem B1577369 : Blo 1048611 1577369 := bstep (se 2 (by rfl) ⟨591513, by rfl⟩ : syracuseStep 1577369 = 1183027) B1183027
theorem B1577483 : Blo 1048611 1577483 := bstep (se 1 (by rfl) ⟨1183112, by rfl⟩ : syracuseStep 1577483 = 2366225) B2366225
theorem B1577495 : Blo 1048611 1577495 := bstep (se 1 (by rfl) ⟨1183121, by rfl⟩ : syracuseStep 1577495 = 2366243) B2366243
theorem B4493875 : Blo 1048611 4493875 := bstep (se 1 (by rfl) ⟨3370406, by rfl⟩ : syracuseStep 4493875 = 6740813) B6740813
theorem B3543641 : Blo 1048611 3543641 := bstep (se 2 (by rfl) ⟨1328865, by rfl⟩ : syracuseStep 3543641 = 2657731) B2657731
theorem B2363993 : Blo 1048611 2363993 := bstep (se 2 (by rfl) ⟨886497, by rfl⟩ : syracuseStep 2363993 = 1772995) B1772995
theorem B1577561 : Blo 1048611 1577561 := bstep (se 2 (by rfl) ⟨591585, by rfl⟩ : syracuseStep 1577561 = 1183171) B1183171
theorem B2364083 : Blo 1048611 2364083 := bstep (se 1 (by rfl) ⟨1773062, by rfl⟩ : syracuseStep 2364083 = 3546125) B3546125
theorem B1577675 : Blo 1048611 1577675 := bstep (se 1 (by rfl) ⟨1183256, by rfl⟩ : syracuseStep 1577675 = 2366513) B2366513
theorem B2364119 : Blo 1048611 2364119 := bstep (se 1 (by rfl) ⟨1773089, by rfl⟩ : syracuseStep 2364119 = 3546179) B3546179
theorem B1577687 : Blo 1048611 1577687 := bstep (se 1 (by rfl) ⟨1183265, by rfl⟩ : syracuseStep 1577687 = 2366531) B2366531
theorem B1577753 : Blo 1048611 1577753 := bstep (se 2 (by rfl) ⟨591657, by rfl⟩ : syracuseStep 1577753 = 1183315) B1183315
theorem B17929025 : Blo 1048611 17929025 := bstep (se 2 (by rfl) ⟨6723384, by rfl⟩ : syracuseStep 17929025 = 13446769) B13446769
theorem B2364299 : Blo 1048611 2364299 := bstep (se 1 (by rfl) ⟨1773224, by rfl⟩ : syracuseStep 2364299 = 3546449) B3546449
theorem B1577867 : Blo 1048611 1577867 := bstep (se 1 (by rfl) ⟨1183400, by rfl⟩ : syracuseStep 1577867 = 2366801) B2366801
theorem B1774487 : Blo 1048611 1774487 := bstep (se 1 (by rfl) ⟨1330865, by rfl⟩ : syracuseStep 1774487 = 2661731) B2661731
theorem B1577879 : Blo 1048611 1577879 := bstep (se 1 (by rfl) ⟨1183409, by rfl⟩ : syracuseStep 1577879 = 2366819) B2366819
theorem B2397107 : Blo 1048611 2397107 := bstep (se 1 (by rfl) ⟨1797830, by rfl⟩ : syracuseStep 2397107 = 3595661) B3595661
theorem B2364353 : Blo 1048611 2364353 := bstep (se 2 (by rfl) ⟨886632, by rfl⟩ : syracuseStep 2364353 = 1773265) B1773265
theorem B1577945 : Blo 1048611 1577945 := bstep (se 2 (by rfl) ⟨591729, by rfl⟩ : syracuseStep 1577945 = 1183459) B1183459
theorem B2659351 : Blo 1048611 2659351 := bstep (se 1 (by rfl) ⟨1994513, by rfl⟩ : syracuseStep 2659351 = 3989027) B3989027
theorem B1774615 : Blo 1048611 1774615 := bstep (se 1 (by rfl) ⟨1330961, by rfl⟩ : syracuseStep 1774615 = 2661923) B2661923
theorem B1578059 : Blo 1048611 1578059 := bstep (se 1 (by rfl) ⟨1183544, by rfl⟩ : syracuseStep 1578059 = 2367089) B2367089
theorem B2397271 : Blo 1048611 2397271 := bstep (se 1 (by rfl) ⟨1797953, by rfl⟩ : syracuseStep 2397271 = 3595907) B3595907
theorem B1578071 : Blo 1048611 1578071 := bstep (se 1 (by rfl) ⟨1183553, by rfl⟩ : syracuseStep 1578071 = 2367107) B2367107
theorem B2364569 : Blo 1048611 2364569 := bstep (se 2 (by rfl) ⟨886713, by rfl⟩ : syracuseStep 2364569 = 1773427) B1773427
theorem B1578137 : Blo 1048611 1578137 := bstep (se 2 (by rfl) ⟨591801, by rfl⟩ : syracuseStep 1578137 = 1183603) B1183603
theorem B2364659 : Blo 1048611 2364659 := bstep (se 1 (by rfl) ⟨1773494, by rfl⟩ : syracuseStep 2364659 = 3546989) B3546989
theorem B1578251 : Blo 1048611 1578251 := bstep (se 1 (by rfl) ⟨1183688, by rfl⟩ : syracuseStep 1578251 = 2367377) B2367377
theorem B3544343 : Blo 1048611 3544343 := bstep (se 1 (by rfl) ⟨2658257, by rfl⟩ : syracuseStep 3544343 = 5316515) B5316515
theorem B2364695 : Blo 1048611 2364695 := bstep (se 1 (by rfl) ⟨1773521, by rfl⟩ : syracuseStep 2364695 = 3547043) B3547043
theorem B1578263 : Blo 1048611 1578263 := bstep (se 1 (by rfl) ⟨1183697, by rfl⟩ : syracuseStep 1578263 = 2367395) B2367395
theorem B1578329 : Blo 1048611 1578329 := bstep (se 2 (by rfl) ⟨591873, by rfl⟩ : syracuseStep 1578329 = 1183747) B1183747
theorem B5313923 : Blo 1048611 5313923 := bstep (se 1 (by rfl) ⟨3985442, by rfl⟩ : syracuseStep 5313923 = 7970885) B7970885
theorem B2659787 : Blo 1048611 2659787 := bstep (se 1 (by rfl) ⟨1994840, by rfl⟩ : syracuseStep 2659787 = 3989681) B3989681
theorem B2364875 : Blo 1048611 2364875 := bstep (se 1 (by rfl) ⟨1773656, by rfl⟩ : syracuseStep 2364875 = 3547313) B3547313
theorem B1578443 : Blo 1048611 1578443 := bstep (se 1 (by rfl) ⟨1183832, by rfl⟩ : syracuseStep 1578443 = 2367665) B2367665
theorem B1578455 : Blo 1048611 1578455 := bstep (se 1 (by rfl) ⟨1183841, by rfl⟩ : syracuseStep 1578455 = 2367683) B2367683
theorem B2528729 : Blo 1048611 2528729 := bstep (se 2 (by rfl) ⟨948273, by rfl⟩ : syracuseStep 2528729 = 1896547) B1896547
theorem B2364929 : Blo 1048611 2364929 := bstep (se 2 (by rfl) ⟨886848, by rfl⟩ : syracuseStep 2364929 = 1773697) B1773697
theorem B4789763 : Blo 1048611 4789763 := bstep (se 1 (by rfl) ⟨3592322, by rfl⟩ : syracuseStep 4789763 = 7184645) B7184645
theorem B1578521 : Blo 1048611 1578521 := bstep (se 2 (by rfl) ⟨591945, by rfl⟩ : syracuseStep 1578521 = 1183891) B1183891
theorem B1480279 : Blo 1048611 1480279 := bstep (se 1 (by rfl) ⟨1110209, by rfl⟩ : syracuseStep 1480279 = 2220419) B2220419
theorem B10098269 : Blo 1048611 10098269 := bstep (se 3 (by rfl) ⟨1893425, by rfl⟩ : syracuseStep 10098269 = 3786851) B3786851
theorem B1775243 : Blo 1048611 1775243 := bstep (se 1 (by rfl) ⟨1331432, by rfl⟩ : syracuseStep 1775243 = 2662865) B2662865
theorem B1578635 : Blo 1048611 1578635 := bstep (se 1 (by rfl) ⟨1183976, by rfl⟩ : syracuseStep 1578635 = 2367953) B2367953
theorem B1578647 : Blo 1048611 1578647 := bstep (se 1 (by rfl) ⟨1183985, by rfl⟩ : syracuseStep 1578647 = 2367971) B2367971
theorem B2365145 : Blo 1048611 2365145 := bstep (se 2 (by rfl) ⟨886929, by rfl⟩ : syracuseStep 2365145 = 1773859) B1773859
theorem B1578713 : Blo 1048611 1578713 := bstep (se 2 (by rfl) ⟨592017, by rfl⟩ : syracuseStep 1578713 = 1184035) B1184035
theorem B1775371 : Blo 1048611 1775371 := bstep (se 1 (by rfl) ⟨1331528, by rfl⟩ : syracuseStep 1775371 = 2663057) B2663057
theorem B3544883 : Blo 1048611 3544883 := bstep (se 1 (by rfl) ⟨2658662, by rfl⟩ : syracuseStep 3544883 = 5317325) B5317325
theorem B2365235 : Blo 1048611 2365235 := bstep (se 1 (by rfl) ⟨1773926, by rfl⟩ : syracuseStep 2365235 = 3547853) B3547853
theorem B2660161 : Blo 1048611 2660161 := bstep (se 2 (by rfl) ⟨997560, by rfl⟩ : syracuseStep 2660161 = 1995121) B1995121
theorem B1578827 : Blo 1048611 1578827 := bstep (se 1 (by rfl) ⟨1184120, by rfl⟩ : syracuseStep 1578827 = 2368241) B2368241
theorem B2365271 : Blo 1048611 2365271 := bstep (se 1 (by rfl) ⟨1773953, by rfl⟩ : syracuseStep 2365271 = 3547907) B3547907
theorem B1578839 : Blo 1048611 1578839 := bstep (se 1 (by rfl) ⟨1184129, by rfl⟩ : syracuseStep 1578839 = 2368259) B2368259
theorem B1775513 : Blo 1048611 1775513 := bstep (se 2 (by rfl) ⟨665817, by rfl⟩ : syracuseStep 1775513 = 1331635) B1331635
theorem B1578905 : Blo 1048611 1578905 := bstep (se 2 (by rfl) ⟨592089, by rfl⟩ : syracuseStep 1578905 = 1184179) B1184179
theorem B4495277 : Blo 1048611 4495277 := bstep (se 3 (by rfl) ⟨842864, by rfl⟩ : syracuseStep 4495277 = 1685729) B1685729
theorem B2365451 : Blo 1048611 2365451 := bstep (se 1 (by rfl) ⟨1774088, by rfl⟩ : syracuseStep 2365451 = 3548177) B3548177
theorem B1775641 : Blo 1048611 1775641 := bstep (se 2 (by rfl) ⟨665865, by rfl⟩ : syracuseStep 1775641 = 1331731) B1331731
theorem B3545153 : Blo 1048611 3545153 := bstep (se 2 (by rfl) ⟨1329432, by rfl⟩ : syracuseStep 3545153 = 2658865) B2658865
theorem B2365505 : Blo 1048611 2365505 := bstep (se 2 (by rfl) ⟨887064, by rfl⟩ : syracuseStep 2365505 = 1774129) B1774129
theorem B8624333 : Blo 1048611 8624333 := bstep (se 3 (by rfl) ⟨1617062, by rfl⟩ : syracuseStep 8624333 = 3234125) B3234125
theorem B5052689 : Blo 1048611 5052689 := bstep (se 2 (by rfl) ⟨1894758, by rfl⟩ : syracuseStep 5052689 = 3789517) B3789517
theorem B2365721 : Blo 1048611 2365721 := bstep (se 2 (by rfl) ⟨887145, by rfl⟩ : syracuseStep 2365721 = 1774291) B1774291
theorem B2988353 : Blo 1048611 2988353 := bstep (se 2 (by rfl) ⟨1120632, by rfl⟩ : syracuseStep 2988353 = 2241265) B2241265
theorem B2988377 : Blo 1048611 2988377 := bstep (se 2 (by rfl) ⟨1120641, by rfl⟩ : syracuseStep 2988377 = 2241283) B2241283
theorem B2365811 : Blo 1048611 2365811 := bstep (se 1 (by rfl) ⟨1774358, by rfl⟩ : syracuseStep 2365811 = 3548717) B3548717
theorem B1120663 : Blo 1048611 1120663 := bstep (se 1 (by rfl) ⟨840497, by rfl⟩ : syracuseStep 1120663 = 1680995) B1680995
theorem B2660759 : Blo 1048611 2660759 := bstep (se 1 (by rfl) ⟨1995569, by rfl⟩ : syracuseStep 2660759 = 3991139) B3991139
theorem B2365847 : Blo 1048611 2365847 := bstep (se 1 (by rfl) ⟨1774385, by rfl⟩ : syracuseStep 2365847 = 3548771) B3548771
theorem B34970129 : Blo 1048611 34970129 := bstep (se 2 (by rfl) ⟨13113798, by rfl⟩ : syracuseStep 34970129 = 26227597) B26227597
theorem B1514009 : Blo 1048611 1514009 := bstep (se 2 (by rfl) ⟨567753, by rfl⟩ : syracuseStep 1514009 = 1135507) B1135507
theorem B2366027 : Blo 1048611 2366027 := bstep (se 1 (by rfl) ⟨1774520, by rfl⟩ : syracuseStep 2366027 = 3549041) B3549041
theorem B1776215 : Blo 1048611 1776215 := bstep (se 1 (by rfl) ⟨1332161, by rfl⟩ : syracuseStep 1776215 = 2664323) B2664323
theorem B3545693 : Blo 1048611 3545693 := bstep (se 3 (by rfl) ⟨664817, by rfl⟩ : syracuseStep 3545693 = 1329635) B1329635
theorem B2366081 : Blo 1048611 2366081 := bstep (se 2 (by rfl) ⟨887280, by rfl⟩ : syracuseStep 2366081 = 1774561) B1774561
theorem B2366297 : Blo 1048611 2366297 := bstep (se 2 (by rfl) ⟨887361, by rfl⟩ : syracuseStep 2366297 = 1774723) B1774723
theorem B2366387 : Blo 1048611 2366387 := bstep (se 1 (by rfl) ⟨1774790, by rfl⟩ : syracuseStep 2366387 = 3549581) B3549581
theorem B2366423 : Blo 1048611 2366423 := bstep (se 1 (by rfl) ⟨1774817, by rfl⟩ : syracuseStep 2366423 = 3549635) B3549635
theorem B2432051 : Blo 1048611 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B2366603 : Blo 1048611 2366603 := bstep (se 1 (by rfl) ⟨1774952, by rfl⟩ : syracuseStep 2366603 = 3549905) B3549905
theorem B8101043 : Blo 1048611 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B2661569 : Blo 1048611 2661569 := bstep (se 2 (by rfl) ⟨998088, by rfl⟩ : syracuseStep 2661569 = 1996177) B1996177
theorem B2366657 : Blo 1048611 2366657 := bstep (se 2 (by rfl) ⟨887496, by rfl⟩ : syracuseStep 2366657 = 1774993) B1774993
theorem B1121483 : Blo 1048611 1121483 := bstep (se 1 (by rfl) ⟨841112, by rfl⟩ : syracuseStep 1121483 = 1682225) B1682225
theorem B9706787 : Blo 1048611 9706787 := bstep (se 1 (by rfl) ⟨7280090, by rfl⟩ : syracuseStep 9706787 = 14560181) B14560181
theorem B2563379 : Blo 1048611 2563379 := bstep (se 1 (by rfl) ⟨1922534, by rfl⟩ : syracuseStep 2563379 = 3845069) B3845069
theorem B5610853 : Blo 1048611 5610853 := bstep (se 4 (by rfl) ⟨526017, by rfl⟩ : syracuseStep 5610853 = 1052035) B1052035
theorem B2366873 : Blo 1048611 2366873 := bstep (se 2 (by rfl) ⟨887577, by rfl⟩ : syracuseStep 2366873 = 1775155) B1775155
theorem B3841453 : Blo 1048611 3841453 := bstep (se 3 (by rfl) ⟨720272, by rfl⟩ : syracuseStep 3841453 = 1440545) B1440545
theorem B2366963 : Blo 1048611 2366963 := bstep (se 1 (by rfl) ⟨1775222, by rfl⟩ : syracuseStep 2366963 = 3550445) B3550445
theorem B2366999 : Blo 1048611 2366999 := bstep (se 1 (by rfl) ⟨1775249, by rfl⟩ : syracuseStep 2366999 = 3550499) B3550499
theorem B2989619 : Blo 1048611 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B3546827 : Blo 1048611 3546827 := bstep (se 1 (by rfl) ⟨2660120, by rfl⟩ : syracuseStep 3546827 = 5320241) B5320241
theorem B2367179 : Blo 1048611 2367179 := bstep (se 1 (by rfl) ⟨1775384, by rfl⟩ : syracuseStep 2367179 = 3550769) B3550769
theorem B2662105 : Blo 1048611 2662105 := bstep (se 2 (by rfl) ⟨998289, by rfl⟩ : syracuseStep 2662105 = 1996579) B1996579
theorem B2367233 : Blo 1048611 2367233 := bstep (se 2 (by rfl) ⟨887712, by rfl⟩ : syracuseStep 2367233 = 1775425) B1775425
theorem B14786309 : Blo 1048611 14786309 := bstep (se 4 (by rfl) ⟨1386216, by rfl⟩ : syracuseStep 14786309 = 2772433) B2772433
theorem B2695091 : Blo 1048611 2695091 := bstep (se 1 (by rfl) ⟨2021318, by rfl⟩ : syracuseStep 2695091 = 4042637) B4042637
theorem B3547097 : Blo 1048611 3547097 := bstep (se 2 (by rfl) ⟨1330161, by rfl⟩ : syracuseStep 3547097 = 2660323) B2660323
theorem B2367449 : Blo 1048611 2367449 := bstep (se 2 (by rfl) ⟨887793, by rfl⟩ : syracuseStep 2367449 = 1775587) B1775587
theorem B2367539 : Blo 1048611 2367539 := bstep (se 1 (by rfl) ⟨1775654, by rfl⟩ : syracuseStep 2367539 = 3551309) B3551309
theorem B2367575 : Blo 1048611 2367575 := bstep (se 1 (by rfl) ⟨1775681, by rfl⟩ : syracuseStep 2367575 = 3551363) B3551363
theorem B2367755 : Blo 1048611 2367755 := bstep (se 1 (by rfl) ⟨1775816, by rfl⟩ : syracuseStep 2367755 = 3551633) B3551633
theorem B2367809 : Blo 1048611 2367809 := bstep (se 2 (by rfl) ⟨887928, by rfl⟩ : syracuseStep 2367809 = 1775857) B1775857
theorem B2368025 : Blo 1048611 2368025 := bstep (se 2 (by rfl) ⟨888009, by rfl⟩ : syracuseStep 2368025 = 1776019) B1776019
theorem B1122871 : Blo 1048611 1122871 := bstep (se 1 (by rfl) ⟨842153, by rfl⟩ : syracuseStep 1122871 = 1684307) B1684307
theorem B2368115 : Blo 1048611 2368115 := bstep (se 1 (by rfl) ⟨1776086, by rfl⟩ : syracuseStep 2368115 = 3552173) B3552173
theorem B3547799 : Blo 1048611 3547799 := bstep (se 1 (by rfl) ⟨2660849, by rfl⟩ : syracuseStep 3547799 = 5321699) B5321699
theorem B2368151 : Blo 1048611 2368151 := bstep (se 1 (by rfl) ⟨1776113, by rfl⟩ : syracuseStep 2368151 = 3552227) B3552227
theorem B2663219 : Blo 1048611 2663219 := bstep (se 1 (by rfl) ⟨1997414, by rfl⟩ : syracuseStep 2663219 = 3994829) B3994829
theorem B2368331 : Blo 1048611 2368331 := bstep (se 1 (by rfl) ⟨1776248, by rfl⟩ : syracuseStep 2368331 = 3552497) B3552497
theorem B2696087 : Blo 1048611 2696087 := bstep (se 1 (by rfl) ⟨2022065, by rfl⟩ : syracuseStep 2696087 = 4044131) B4044131
theorem B7971857 : Blo 1048611 7971857 := bstep (se 2 (by rfl) ⟨2989446, by rfl⟩ : syracuseStep 7971857 = 5978893) B5978893
theorem B5317649 : Blo 1048611 5317649 := bstep (se 2 (by rfl) ⟨1994118, by rfl⟩ : syracuseStep 5317649 = 3988237) B3988237
theorem B2663513 : Blo 1048611 2663513 := bstep (se 2 (by rfl) ⟨998817, by rfl⟩ : syracuseStep 2663513 = 1997635) B1997635
theorem B7578775 : Blo 1048611 7578775 := bstep (se 1 (by rfl) ⟨5684081, by rfl⟩ : syracuseStep 7578775 = 11368163) B11368163
theorem B5317811 : Blo 1048611 5317811 := bstep (se 1 (by rfl) ⟨3988358, by rfl⟩ : syracuseStep 5317811 = 7976717) B7976717
theorem B3548339 : Blo 1048611 3548339 := bstep (se 1 (by rfl) ⟨2661254, by rfl⟩ : syracuseStep 3548339 = 5322509) B5322509
theorem B1123691 : Blo 1048611 1123691 := bstep (se 1 (by rfl) ⟨842768, by rfl⟩ : syracuseStep 1123691 = 1685537) B1685537
theorem B3548609 : Blo 1048611 3548609 := bstep (se 2 (by rfl) ⟨1330728, by rfl⟩ : syracuseStep 3548609 = 2661457) B2661457
theorem B11970179 : Blo 1048611 11970179 := bstep (se 1 (by rfl) ⟨8977634, by rfl⟩ : syracuseStep 11970179 = 17955269) B17955269
theorem B3549149 : Blo 1048611 3549149 := bstep (se 3 (by rfl) ⟨665465, by rfl⟩ : syracuseStep 3549149 = 1330931) B1330931
theorem B3188929 : Blo 1048611 3188929 := bstep (se 2 (by rfl) ⟨1195848, by rfl⟩ : syracuseStep 3188929 = 2391697) B2391697
theorem B5974337 : Blo 1048611 5974337 := bstep (se 2 (by rfl) ⟨2240376, by rfl⟩ : syracuseStep 5974337 = 4480753) B4480753
theorem B2992477 : Blo 1048611 2992477 := bstep (se 3 (by rfl) ⟨561089, by rfl⟩ : syracuseStep 2992477 = 1122179) B1122179
theorem B2992535 : Blo 1048611 2992535 := bstep (se 1 (by rfl) ⟨2244401, by rfl⟩ : syracuseStep 2992535 = 4488803) B4488803
theorem B1682327 : Blo 1048611 1682327 := bstep (se 1 (by rfl) ⟨1261745, by rfl⟩ : syracuseStep 1682327 = 2523491) B2523491
theorem B1616843 : Blo 1048611 1616843 := bstep (se 1 (by rfl) ⟨1212632, by rfl⟩ : syracuseStep 1616843 = 2425265) B2425265
theorem B7580621 : Blo 1048611 7580621 := bstep (se 3 (by rfl) ⟨1421366, by rfl⟩ : syracuseStep 7580621 = 2842733) B2842733
theorem B5319755 : Blo 1048611 5319755 := bstep (se 1 (by rfl) ⟨3989816, by rfl⟩ : syracuseStep 5319755 = 7979633) B7979633
theorem B3550283 : Blo 1048611 3550283 := bstep (se 1 (by rfl) ⟨2662712, by rfl⟩ : syracuseStep 3550283 = 5325425) B5325425
theorem B1682635 : Blo 1048611 1682635 := bstep (se 1 (by rfl) ⟨1261976, by rfl⟩ : syracuseStep 1682635 = 2523953) B2523953
theorem B3550553 : Blo 1048611 3550553 := bstep (se 2 (by rfl) ⟨1331457, by rfl⟩ : syracuseStep 3550553 = 2662915) B2662915
theorem B2993753 : Blo 1048611 2993753 := bstep (se 2 (by rfl) ⟨1122657, by rfl⟩ : syracuseStep 2993753 = 2245315) B2245315
theorem B2993867 : Blo 1048611 2993867 := bstep (se 1 (by rfl) ⟨2245400, by rfl⟩ : syracuseStep 2993867 = 4490801) B4490801
theorem B3551255 : Blo 1048611 3551255 := bstep (se 1 (by rfl) ⟨2663441, by rfl⟩ : syracuseStep 3551255 = 5326883) B5326883
theorem B2240779 : Blo 1048611 2240779 := bstep (se 1 (by rfl) ⟨1680584, by rfl⟩ : syracuseStep 2240779 = 3361169) B3361169
theorem B1683865 : Blo 1048611 1683865 := bstep (se 2 (by rfl) ⟨631449, by rfl⟩ : syracuseStep 1683865 = 1262899) B1262899
theorem B3551795 : Blo 1048611 3551795 := bstep (se 1 (by rfl) ⟨2663846, by rfl⟩ : syracuseStep 3551795 = 5327693) B5327693
theorem B2994995 : Blo 1048611 2994995 := bstep (se 1 (by rfl) ⟨2246246, by rfl⟩ : syracuseStep 2994995 = 4492493) B4492493
theorem B7975745 : Blo 1048611 7975745 := bstep (se 2 (by rfl) ⟨2990904, by rfl⟩ : syracuseStep 7975745 = 5981809) B5981809
theorem B5321537 : Blo 1048611 5321537 := bstep (se 2 (by rfl) ⟨1995576, by rfl⟩ : syracuseStep 5321537 = 3991153) B3991153
theorem B3552065 : Blo 1048611 3552065 := bstep (se 2 (by rfl) ⟨1332024, by rfl⟩ : syracuseStep 3552065 = 2664049) B2664049
theorem B2995393 : Blo 1048611 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B4797713 : Blo 1048611 4797713 := bstep (se 2 (by rfl) ⟨1799142, by rfl⟩ : syracuseStep 4797713 = 3598285) B3598285
theorem B2242009 : Blo 1048611 2242009 := bstep (se 2 (by rfl) ⟨840753, by rfl⟩ : syracuseStep 2242009 = 1681507) B1681507
theorem B21575261 : Blo 1048611 21575261 := bstep (se 3 (by rfl) ⟨4045361, by rfl⟩ : syracuseStep 21575261 = 8090723) B8090723
theorem B34059973 : Blo 1048611 34059973 := bstep (se 4 (by rfl) ⟨3193122, by rfl⟩ : syracuseStep 34059973 = 6386245) B6386245
theorem B14366813 : Blo 1048611 14366813 := bstep (se 3 (by rfl) ⟨2693777, by rfl⟩ : syracuseStep 14366813 = 5387555) B5387555
theorem B1456267 : Blo 1048611 1456267 := bstep (se 1 (by rfl) ⟨1092200, by rfl⟩ : syracuseStep 1456267 = 2184401) B2184401
theorem B19151149 : Blo 1048611 19151149 := bstep (se 3 (by rfl) ⟨3590840, by rfl⟩ : syracuseStep 19151149 = 7181681) B7181681
theorem B6568409 : Blo 1048611 6568409 := bstep (se 2 (by rfl) ⟨2463153, by rfl⟩ : syracuseStep 6568409 = 4926307) B4926307
theorem B6732305 : Blo 1048611 6732305 := bstep (se 2 (by rfl) ⟨2524614, by rfl⟩ : syracuseStep 6732305 = 5049229) B5049229
theorem B4799027 : Blo 1048611 4799027 := bstep (se 1 (by rfl) ⟨3599270, by rfl⟩ : syracuseStep 4799027 = 7198541) B7198541
theorem B7977689 : Blo 1048611 7977689 := bstep (se 2 (by rfl) ⟨2991633, by rfl⟩ : syracuseStep 7977689 = 5983267) B5983267
theorem B5323481 : Blo 1048611 5323481 := bstep (se 2 (by rfl) ⟨1996305, by rfl⟩ : syracuseStep 5323481 = 3992611) B3992611
theorem B1260299 : Blo 1048611 1260299 := bstep (se 1 (by rfl) ⟨945224, by rfl⟩ : syracuseStep 1260299 = 1890449) B1890449
theorem B24263489 : Blo 1048611 24263489 := bstep (se 2 (by rfl) ⟨9098808, by rfl⟩ : syracuseStep 24263489 = 18197617) B18197617
theorem B8961029 : Blo 1048611 8961029 := bstep (se 4 (by rfl) ⟨840096, by rfl⟩ : syracuseStep 8961029 = 1680193) B1680193
theorem B1260631 : Blo 1048611 1260631 := bstep (se 1 (by rfl) ⟨945473, by rfl⟩ : syracuseStep 1260631 = 1890947) B1890947
theorem B10108451 : Blo 1048611 10108451 := bstep (se 1 (by rfl) ⟨7581338, by rfl⟩ : syracuseStep 10108451 = 15162677) B15162677
theorem B3587777 : Blo 1048611 3587777 := bstep (se 2 (by rfl) ⟨1345416, by rfl⟩ : syracuseStep 3587777 = 2690833) B2690833
theorem B3194585 : Blo 1048611 3194585 := bstep (se 2 (by rfl) ⟨1197969, by rfl⟩ : syracuseStep 3194585 = 2395939) B2395939
theorem B1622155 : Blo 1048611 1622155 := bstep (se 1 (by rfl) ⟨1216616, by rfl⟩ : syracuseStep 1622155 = 2433233) B2433233
theorem B2834635 : Blo 1048611 2834635 := bstep (se 1 (by rfl) ⟨2125976, by rfl⟩ : syracuseStep 2834635 = 4251953) B4251953
theorem B5325101 : Blo 1048611 5325101 := bstep (se 3 (by rfl) ⟨998456, by rfl⟩ : syracuseStep 5325101 = 1996913) B1996913
theorem B2834777 : Blo 1048611 2834777 := bstep (se 2 (by rfl) ⟨1063041, by rfl⟩ : syracuseStep 2834777 = 2126083) B2126083
theorem B1327691 : Blo 1048611 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B2245195 : Blo 1048611 2245195 := bstep (se 1 (by rfl) ⟨1683896, by rfl⟩ : syracuseStep 2245195 = 3367793) B3367793
theorem B1196651 : Blo 1048611 1196651 := bstep (se 1 (by rfl) ⟨897488, by rfl⟩ : syracuseStep 1196651 = 1794977) B1794977
theorem B8077975 : Blo 1048611 8077975 := bstep (se 1 (by rfl) ⟨6058481, by rfl⟩ : syracuseStep 8077975 = 12116963) B12116963
theorem B26886977 : Blo 1048611 26886977 := bstep (se 2 (by rfl) ⟨10082616, by rfl⟩ : syracuseStep 26886977 = 20165233) B20165233
theorem B1262423 : Blo 1048611 1262423 := bstep (se 1 (by rfl) ⟨946817, by rfl⟩ : syracuseStep 1262423 = 1893635) B1893635
theorem B2245657 : Blo 1048611 2245657 := bstep (se 2 (by rfl) ⟨842121, by rfl⟩ : syracuseStep 2245657 = 1684243) B1684243
theorem B1262731 : Blo 1048611 1262731 := bstep (se 1 (by rfl) ⟨947048, by rfl⟩ : syracuseStep 1262731 = 1894097) B1894097
theorem B1328395 : Blo 1048611 1328395 := bstep (se 1 (by rfl) ⟨996296, by rfl⟩ : syracuseStep 1328395 = 1992593) B1992593
theorem B7587107 : Blo 1048611 7587107 := bstep (se 1 (by rfl) ⟨5690330, by rfl⟩ : syracuseStep 7587107 = 11380661) B11380661
theorem B5686679 : Blo 1048611 5686679 := bstep (se 1 (by rfl) ⟨4265009, by rfl⟩ : syracuseStep 5686679 = 8530019) B8530019
theorem B11945393 : Blo 1048611 11945393 := bstep (se 2 (by rfl) ⟨4479522, by rfl⟩ : syracuseStep 11945393 = 8959045) B8959045
theorem B1328663 : Blo 1048611 1328663 := bstep (se 1 (by rfl) ⟨996497, by rfl⟩ : syracuseStep 1328663 = 1992995) B1992995
theorem B92227157 : Blo 1048611 92227157 := bstep (se 8 (by rfl) ⟨540393, by rfl⟩ : syracuseStep 92227157 = 1080787) B1080787
theorem B17942147 : Blo 1048611 17942147 := bstep (se 1 (by rfl) ⟨13456610, by rfl⟩ : syracuseStep 17942147 = 26913221) B26913221
theorem B10929815 : Blo 1048611 10929815 := bstep (se 1 (by rfl) ⟨8197361, by rfl⟩ : syracuseStep 10929815 = 16394723) B16394723
theorem B5982083 : Blo 1048611 5982083 := bstep (se 1 (by rfl) ⟨4486562, by rfl⟩ : syracuseStep 5982083 = 8973125) B8973125
theorem B3983363 : Blo 1048611 3983363 := bstep (se 1 (by rfl) ⟨2987522, by rfl⟩ : syracuseStep 3983363 = 5975045) B5975045
theorem B3983377 : Blo 1048611 3983377 := bstep (se 2 (by rfl) ⟨1493766, by rfl⟩ : syracuseStep 3983377 = 2987533) B2987533
theorem B7981091 : Blo 1048611 7981091 := bstep (se 1 (by rfl) ⟨5985818, by rfl⟩ : syracuseStep 7981091 = 11971637) B11971637
theorem B1329367 : Blo 1048611 1329367 := bstep (se 1 (by rfl) ⟨997025, by rfl⟩ : syracuseStep 1329367 = 1994051) B1994051
theorem B3983681 : Blo 1048611 3983681 := bstep (se 2 (by rfl) ⟨1493880, by rfl⟩ : syracuseStep 3983681 = 2987761) B2987761
theorem B2247041 : Blo 1048611 2247041 := bstep (se 2 (by rfl) ⟨842640, by rfl⟩ : syracuseStep 2247041 = 1685281) B1685281
theorem B1493579 : Blo 1048611 1493579 := bstep (se 1 (by rfl) ⟨1120184, by rfl⟩ : syracuseStep 1493579 = 2240369) B2240369
theorem B3984349 : Blo 1048611 3984349 := bstep (se 3 (by rfl) ⟨747065, by rfl⟩ : syracuseStep 3984349 = 1494131) B1494131
theorem B1920025 : Blo 1048611 1920025 := bstep (se 2 (by rfl) ⟨720009, by rfl⟩ : syracuseStep 1920025 = 1440019) B1440019
theorem B1494553 : Blo 1048611 1494553 := bstep (se 2 (by rfl) ⟨560457, by rfl⟩ : syracuseStep 1494553 = 1120915) B1120915
theorem B1331083 : Blo 1048611 1331083 := bstep (se 1 (by rfl) ⟨998312, by rfl⟩ : syracuseStep 1331083 = 1996625) B1996625
theorem B3985625 : Blo 1048611 3985625 := bstep (se 2 (by rfl) ⟨1494609, by rfl⟩ : syracuseStep 3985625 = 2989219) B2989219
theorem B1298903 : Blo 1048611 1298903 := bstep (se 1 (by rfl) ⟨974177, by rfl⟩ : syracuseStep 1298903 = 1948355) B1948355
theorem B19157573 : Blo 1048611 19157573 := bstep (se 4 (by rfl) ⟨1796022, by rfl⟩ : syracuseStep 19157573 = 3592045) B3592045
theorem B15323741 : Blo 1048611 15323741 := bstep (se 3 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 15323741 = 5746403) B5746403
theorem B2839133 : Blo 1048611 2839133 := bstep (se 3 (by rfl) ⟨532337, by rfl⟩ : syracuseStep 2839133 = 1064675) B1064675
theorem B1495703 : Blo 1048611 1495703 := bstep (se 1 (by rfl) ⟨1121777, by rfl⟩ : syracuseStep 1495703 = 2243555) B2243555
theorem B12800717 : Blo 1048611 12800717 := bstep (se 3 (by rfl) ⟨2400134, by rfl⟩ : syracuseStep 12800717 = 4800269) B4800269
theorem B1332055 : Blo 1048611 1332055 := bstep (se 1 (by rfl) ⟨999041, by rfl⟩ : syracuseStep 1332055 = 1998083) B1998083
theorem B3789661 : Blo 1048611 3789661 := bstep (se 3 (by rfl) ⟨710561, by rfl⟩ : syracuseStep 3789661 = 1421123) B1421123
theorem B1496011 : Blo 1048611 1496011 := bstep (se 1 (by rfl) ⟨1122008, by rfl⟩ : syracuseStep 1496011 = 2244017) B2244017
theorem B8508509 : Blo 1048611 8508509 := bstep (se 3 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 8508509 = 3190691) B3190691
theorem B2020481 : Blo 1048611 2020481 := bstep (se 2 (by rfl) ⟨757680, by rfl⟩ : syracuseStep 2020481 = 1515361) B1515361
theorem B1726039 : Blo 1048611 1726039 := bstep (se 1 (by rfl) ⟨1294529, by rfl⟩ : syracuseStep 1726039 = 2589059) B2589059
theorem B13620887 : Blo 1048611 13620887 := bstep (se 1 (by rfl) ⟨10215665, by rfl⟩ : syracuseStep 13620887 = 20431331) B20431331
theorem B3987251 : Blo 1048611 3987251 := bstep (se 1 (by rfl) ⟨2990438, by rfl⟩ : syracuseStep 3987251 = 5980877) B5980877
theorem B3987265 : Blo 1048611 3987265 := bstep (se 2 (by rfl) ⟨1495224, by rfl⟩ : syracuseStep 3987265 = 2990449) B2990449
theorem B6739787 : Blo 1048611 6739787 := bstep (se 1 (by rfl) ⟨5054840, by rfl⟩ : syracuseStep 6739787 = 10109681) B10109681
theorem B8968067 : Blo 1048611 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B1497047 : Blo 1048611 1497047 := bstep (se 1 (by rfl) ⟨1122785, by rfl⟩ : syracuseStep 1497047 = 2245571) B2245571
theorem B1595467 : Blo 1048611 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B2021465 : Blo 1048611 2021465 := bstep (se 2 (by rfl) ⟨758049, by rfl⟩ : syracuseStep 2021465 = 1516099) B1516099
theorem B1497241 : Blo 1048611 1497241 := bstep (se 2 (by rfl) ⟨561465, by rfl⟩ : syracuseStep 1497241 = 1122931) B1122931
theorem B3365783 : Blo 1048611 3365783 := bstep (se 1 (by rfl) ⟨2524337, by rfl⟩ : syracuseStep 3365783 = 5048675) B5048675
theorem B4545629 : Blo 1048611 4545629 := bstep (se 3 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 4545629 = 1704611) B1704611
theorem B7560323 : Blo 1048611 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B5987459 : Blo 1048611 5987459 := bstep (se 1 (by rfl) ⟨4490594, by rfl⟩ : syracuseStep 5987459 = 8981189) B8981189
theorem B7986437 : Blo 1048611 7986437 := bstep (se 4 (by rfl) ⟨748728, by rfl⟩ : syracuseStep 7986437 = 1497457) B1497457
theorem B5987915 : Blo 1048611 5987915 := bstep (se 1 (by rfl) ⟨4490936, by rfl⟩ : syracuseStep 5987915 = 8981873) B8981873
theorem B1498699 : Blo 1048611 1498699 := bstep (se 1 (by rfl) ⟨1124024, by rfl⟩ : syracuseStep 1498699 = 2248049) B2248049
theorem B1891991 : Blo 1048611 1891991 := bstep (se 1 (by rfl) ⟨1418993, by rfl⟩ : syracuseStep 1891991 = 2837987) B2837987
theorem B3989195 : Blo 1048611 3989195 := bstep (se 1 (by rfl) ⟨2991896, by rfl⟩ : syracuseStep 3989195 = 5983793) B5983793
theorem B3989209 : Blo 1048611 3989209 := bstep (se 2 (by rfl) ⟨1495953, by rfl⟩ : syracuseStep 3989209 = 2991907) B2991907
theorem B4481027 : Blo 1048611 4481027 := bstep (se 1 (by rfl) ⟨3360770, by rfl⟩ : syracuseStep 4481027 = 6721541) B6721541
theorem B3792919 : Blo 1048611 3792919 := bstep (se 1 (by rfl) ⟨2844689, by rfl⟩ : syracuseStep 3792919 = 5689379) B5689379
theorem B2875571 : Blo 1048611 2875571 := bstep (se 1 (by rfl) ⟨2156678, by rfl⟩ : syracuseStep 2875571 = 4313357) B4313357
theorem B3367115 : Blo 1048611 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B4481369 : Blo 1048611 4481369 := bstep (se 2 (by rfl) ⟨1680513, by rfl⟩ : syracuseStep 4481369 = 3361027) B3361027
theorem B1991051 : Blo 1048611 1991051 := bstep (se 1 (by rfl) ⟨1493288, by rfl⟩ : syracuseStep 1991051 = 2986577) B2986577
theorem B13459891 : Blo 1048611 13459891 := bstep (se 1 (by rfl) ⟨10094918, by rfl⟩ : syracuseStep 13459891 = 20189837) B20189837
theorem B1991233 : Blo 1048611 1991233 := bstep (se 2 (by rfl) ⟨746712, by rfl⟩ : syracuseStep 1991233 = 1493425) B1493425
theorem B1892929 : Blo 1048611 1892929 := bstep (se 2 (by rfl) ⟨709848, by rfl⟩ : syracuseStep 1892929 = 1419697) B1419697
theorem B3990167 : Blo 1048611 3990167 := bstep (se 1 (by rfl) ⟨2992625, by rfl⟩ : syracuseStep 3990167 = 5985251) B5985251
theorem B4252439 : Blo 1048611 4252439 := bstep (se 1 (by rfl) ⟨3189329, by rfl⟩ : syracuseStep 4252439 = 6378659) B6378659
theorem B15131717 : Blo 1048611 15131717 := bstep (se 4 (by rfl) ⟨1418598, by rfl⟩ : syracuseStep 15131717 = 2837197) B2837197
theorem B1991947 : Blo 1048611 1991947 := bstep (se 1 (by rfl) ⟨1493960, by rfl⟩ : syracuseStep 1991947 = 2987921) B2987921
theorem B3368243 : Blo 1048611 3368243 := bstep (se 1 (by rfl) ⟨2526182, by rfl⟩ : syracuseStep 3368243 = 5052365) B5052365
theorem B1992023 : Blo 1048611 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B7988867 : Blo 1048611 7988867 := bstep (se 1 (by rfl) ⟨5991650, by rfl⟩ : syracuseStep 7988867 = 11983301) B11983301
theorem B3991427 : Blo 1048611 3991427 := bstep (se 1 (by rfl) ⟨2993570, by rfl⟩ : syracuseStep 3991427 = 5987141) B5987141
theorem B3598273 : Blo 1048611 3598273 := bstep (se 2 (by rfl) ⟨1349352, by rfl⟩ : syracuseStep 3598273 = 2698705) B2698705
theorem B1992691 : Blo 1048611 1992691 := bstep (se 1 (by rfl) ⟨1494518, by rfl⟩ : syracuseStep 1992691 = 2989037) B2989037
theorem B1992919 : Blo 1048611 1992919 := bstep (se 1 (by rfl) ⟨1494689, by rfl⟩ : syracuseStep 1992919 = 2989379) B2989379
theorem B1894643 : Blo 1048611 1894643 := bstep (se 1 (by rfl) ⟨1420982, by rfl⟩ : syracuseStep 1894643 = 2841965) B2841965
theorem B1993025 : Blo 1048611 1993025 := bstep (se 2 (by rfl) ⟨747384, by rfl⟩ : syracuseStep 1993025 = 1494769) B1494769
theorem B1993177 : Blo 1048611 1993177 := bstep (se 2 (by rfl) ⟨747441, by rfl⟩ : syracuseStep 1993177 = 1494883) B1494883
theorem B3369433 : Blo 1048611 3369433 := bstep (se 2 (by rfl) ⟨1263537, by rfl⟩ : syracuseStep 3369433 = 2527075) B2527075
theorem B4155907 : Blo 1048611 4155907 := bstep (se 1 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 4155907 = 6233861) B6233861
theorem B9104003 : Blo 1048611 9104003 := bstep (se 1 (by rfl) ⟨6828002, by rfl⟩ : syracuseStep 9104003 = 13656005) B13656005
theorem B3369689 : Blo 1048611 3369689 := bstep (se 2 (by rfl) ⟨1263633, by rfl⟩ : syracuseStep 3369689 = 2527267) B2527267
theorem B3370049 : Blo 1048611 3370049 := bstep (se 2 (by rfl) ⟨1263768, by rfl⟩ : syracuseStep 3370049 = 2527537) B2527537
theorem B3599435 : Blo 1048611 3599435 := bstep (se 1 (by rfl) ⟨2699576, by rfl⟩ : syracuseStep 3599435 = 5399153) B5399153
theorem B1895681 : Blo 1048611 1895681 := bstep (se 2 (by rfl) ⟨710880, by rfl⟩ : syracuseStep 1895681 = 1421761) B1421761
theorem B31157777 : Blo 1048611 31157777 := bstep (se 2 (by rfl) ⟨11684166, by rfl⟩ : syracuseStep 31157777 = 23368333) B23368333
theorem B4484753 : Blo 1048611 4484753 := bstep (se 2 (by rfl) ⟨1681782, by rfl⟩ : syracuseStep 4484753 = 3363565) B3363565
theorem B1994483 : Blo 1048611 1994483 := bstep (se 1 (by rfl) ⟨1495862, by rfl⟩ : syracuseStep 1994483 = 2991725) B2991725
theorem B4255553 : Blo 1048611 4255553 := bstep (se 2 (by rfl) ⟨1595832, by rfl⟩ : syracuseStep 4255553 = 3191665) B3191665
theorem B3370817 : Blo 1048611 3370817 := bstep (se 2 (by rfl) ⟨1264056, by rfl⟩ : syracuseStep 3370817 = 2528113) B2528113
theorem B1994635 : Blo 1048611 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B1896331 : Blo 1048611 1896331 := bstep (se 1 (by rfl) ⟨1422248, by rfl⟩ : syracuseStep 1896331 = 2844497) B2844497
theorem B5992541 : Blo 1048611 5992541 := bstep (se 3 (by rfl) ⟨1123601, by rfl⟩ : syracuseStep 5992541 = 2247203) B2247203
theorem B1994969 : Blo 1048611 1994969 := bstep (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) B1496227
theorem B1896691 : Blo 1048611 1896691 := bstep (se 1 (by rfl) ⟨1422518, by rfl⟩ : syracuseStep 1896691 = 2845037) B2845037
theorem B3371329 : Blo 1048611 3371329 := bstep (se 2 (by rfl) ⟨1264248, by rfl⟩ : syracuseStep 3371329 = 2528497) B2528497
theorem B4485469 : Blo 1048611 4485469 := bstep (se 3 (by rfl) ⟨841025, by rfl⟩ : syracuseStep 4485469 = 1682051) B1682051
theorem B19690189 : Blo 1048611 19690189 := bstep (se 3 (by rfl) ⟨3691910, by rfl⟩ : syracuseStep 19690189 = 7383821) B7383821
theorem B11957057 : Blo 1048611 11957057 := bstep (se 2 (by rfl) ⟨4483896, by rfl⟩ : syracuseStep 11957057 = 8967793) B8967793
theorem B5993291 : Blo 1048611 5993291 := bstep (se 1 (by rfl) ⟨4494968, by rfl⟩ : syracuseStep 5993291 = 8989937) B8989937
theorem B1995607 : Blo 1048611 1995607 := bstep (se 1 (by rfl) ⟨1496705, by rfl⟩ : syracuseStep 1995607 = 2993411) B2993411
theorem B3994541 : Blo 1048611 3994541 := bstep (se 3 (by rfl) ⟨748976, by rfl⟩ : syracuseStep 3994541 = 1497953) B1497953
theorem B2520001 : Blo 1048611 2520001 := bstep (se 2 (by rfl) ⟨945000, by rfl⟩ : syracuseStep 2520001 = 1890001) B1890001
theorem B7992269 : Blo 1048611 7992269 := bstep (se 3 (by rfl) ⟨1498550, by rfl⟩ : syracuseStep 7992269 = 2997101) B2997101
theorem B7992755 : Blo 1048611 7992755 := bstep (se 1 (by rfl) ⟨5994566, by rfl⟩ : syracuseStep 7992755 = 11989133) B11989133
theorem B26900099 : Blo 1048611 26900099 := bstep (se 1 (by rfl) ⟨20175074, by rfl⟩ : syracuseStep 26900099 = 40350149) B40350149
theorem B1996427 : Blo 1048611 1996427 := bstep (se 1 (by rfl) ⟨1497320, by rfl⟩ : syracuseStep 1996427 = 2994641) B2994641
theorem B3995315 : Blo 1048611 3995315 := bstep (se 1 (by rfl) ⟨2996486, by rfl⟩ : syracuseStep 3995315 = 5992973) B5992973
theorem B1996481 : Blo 1048611 1996481 := bstep (se 2 (by rfl) ⟨748680, by rfl⟩ : syracuseStep 1996481 = 1497361) B1497361
theorem B26965709 : Blo 1048611 26965709 := bstep (se 3 (by rfl) ⟨5056070, by rfl⟩ : syracuseStep 26965709 = 10112141) B10112141
theorem B4257629 : Blo 1048611 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B2127809 : Blo 1048611 2127809 := bstep (se 2 (by rfl) ⟨797928, by rfl⟩ : syracuseStep 2127809 = 1595857) B1595857
theorem B9599077 : Blo 1048611 9599077 := bstep (se 4 (by rfl) ⟨899913, by rfl⟩ : syracuseStep 9599077 = 1799827) B1799827
theorem B16152817 : Blo 1048611 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B5994931 : Blo 1048611 5994931 := bstep (se 1 (by rfl) ⟨4496198, by rfl⟩ : syracuseStep 5994931 = 8992397) B8992397
theorem B1079735 : Blo 1048611 1079735 := bstep (se 1 (by rfl) ⟨809801, by rfl⟩ : syracuseStep 1079735 = 1619603) B1619603
theorem B1997399 : Blo 1048611 1997399 := bstep (se 1 (by rfl) ⟨1498049, by rfl⟩ : syracuseStep 1997399 = 2996099) B2996099
theorem B10091537 : Blo 1048611 10091537 := bstep (se 2 (by rfl) ⟨3784326, by rfl⟩ : syracuseStep 10091537 = 7568653) B7568653
theorem B2522135 : Blo 1048611 2522135 := bstep (se 1 (by rfl) ⟨1891601, by rfl⟩ : syracuseStep 2522135 = 3783203) B3783203
theorem B9600065 : Blo 1048611 9600065 := bstep (se 2 (by rfl) ⟨3600024, by rfl⟩ : syracuseStep 9600065 = 7200049) B7200049
theorem B1997939 : Blo 1048611 1997939 := bstep (se 1 (by rfl) ⟨1498454, by rfl⟩ : syracuseStep 1997939 = 2996909) B2996909
theorem B3636427 : Blo 1048611 3636427 := bstep (se 1 (by rfl) ⟨2727320, by rfl⟩ : syracuseStep 3636427 = 5454641) B5454641
theorem B2129203 : Blo 1048611 2129203 := bstep (se 1 (by rfl) ⟨1596902, by rfl⟩ : syracuseStep 2129203 = 3193805) B3193805
theorem B2522443 : Blo 1048611 2522443 := bstep (se 1 (by rfl) ⟨1891832, by rfl⟩ : syracuseStep 2522443 = 3783665) B3783665
theorem B3833419 : Blo 1048611 3833419 := bstep (se 1 (by rfl) ⟨2875064, by rfl⟩ : syracuseStep 3833419 = 5750129) B5750129
theorem B4259479 : Blo 1048611 4259479 := bstep (se 1 (by rfl) ⟨3194609, by rfl⟩ : syracuseStep 4259479 = 6389219) B6389219
theorem B4489091 : Blo 1048611 4489091 := bstep (se 1 (by rfl) ⟨3366818, by rfl⟩ : syracuseStep 4489091 = 6733637) B6733637
theorem B2523059 : Blo 1048611 2523059 := bstep (se 1 (by rfl) ⟨1892294, by rfl⟩ : syracuseStep 2523059 = 3784589) B3784589
theorem B2883545 : Blo 1048611 2883545 := bstep (se 2 (by rfl) ⟨1081329, by rfl⟩ : syracuseStep 2883545 = 2162659) B2162659
theorem B1572923 : Blo 1048611 1572923 := bstep (se 1 (by rfl) ⟨1179692, by rfl⟩ : syracuseStep 1572923 = 2359385) B2359385
theorem B1048635 : Blo 1048611 1048635 := bstep (se 1 (by rfl) ⟨786476, by rfl⟩ : syracuseStep 1048635 = 1572953) B1572953
theorem B1572983 : Blo 1048611 1572983 := bstep (se 1 (by rfl) ⟨1179737, by rfl⟩ : syracuseStep 1572983 = 2359475) B2359475
theorem B1048711 : Blo 1048611 1048711 := bstep (se 1 (by rfl) ⟨786533, by rfl⟩ : syracuseStep 1048711 = 1573067) B1573067
theorem B1573007 : Blo 1048611 1573007 := bstep (se 1 (by rfl) ⟨1179755, by rfl⟩ : syracuseStep 1573007 = 2359511) B2359511
theorem B1048719 : Blo 1048611 1048719 := bstep (se 1 (by rfl) ⟨786539, by rfl⟩ : syracuseStep 1048719 = 1573079) B1573079
theorem B1573049 : Blo 1048611 1573049 := bstep (se 2 (by rfl) ⟨589893, by rfl⟩ : syracuseStep 1573049 = 1179787) B1179787
theorem B2162873 : Blo 1048611 2162873 := bstep (se 2 (by rfl) ⟨811077, by rfl⟩ : syracuseStep 2162873 = 1622155) B1622155
theorem B1048763 : Blo 1048611 1048763 := bstep (se 1 (by rfl) ⟨786572, by rfl⟩ : syracuseStep 1048763 = 1573145) B1573145
theorem B1573127 : Blo 1048611 1573127 := bstep (se 1 (by rfl) ⟨1179845, by rfl⟩ : syracuseStep 1573127 = 2359691) B2359691
theorem B1048839 : Blo 1048611 1048839 := bstep (se 1 (by rfl) ⟨786629, by rfl⟩ : syracuseStep 1048839 = 1573259) B1573259
theorem B1048847 : Blo 1048611 1048847 := bstep (se 1 (by rfl) ⟨786635, by rfl⟩ : syracuseStep 1048847 = 1573271) B1573271
theorem B1573163 : Blo 1048611 1573163 := bstep (se 1 (by rfl) ⟨1179872, by rfl⟩ : syracuseStep 1573163 = 2359745) B2359745
theorem B1048891 : Blo 1048611 1048891 := bstep (se 1 (by rfl) ⟨786668, by rfl⟩ : syracuseStep 1048891 = 1573337) B1573337
theorem B1573193 : Blo 1048611 1573193 := bstep (se 2 (by rfl) ⟨589947, by rfl⟩ : syracuseStep 1573193 = 1179895) B1179895
theorem B1769863 : Blo 1048611 1769863 := bstep (se 1 (by rfl) ⟨1327397, by rfl⟩ : syracuseStep 1769863 = 2654795) B2654795
theorem B1180039 : Blo 1048611 1180039 := bstep (se 1 (by rfl) ⟨885029, by rfl⟩ : syracuseStep 1180039 = 1770059) B1770059
theorem B1048967 : Blo 1048611 1048967 := bstep (se 1 (by rfl) ⟨786725, by rfl⟩ : syracuseStep 1048967 = 1573451) B1573451
theorem B1048975 : Blo 1048611 1048975 := bstep (se 1 (by rfl) ⟨786731, by rfl⟩ : syracuseStep 1048975 = 1573463) B1573463
theorem B1573307 : Blo 1048611 1573307 := bstep (se 1 (by rfl) ⟨1179980, by rfl⟩ : syracuseStep 1573307 = 2359961) B2359961
theorem B1049019 : Blo 1048611 1049019 := bstep (se 1 (by rfl) ⟨786764, by rfl⟩ : syracuseStep 1049019 = 1573529) B1573529
theorem B5046731 : Blo 1048611 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B1573367 : Blo 1048611 1573367 := bstep (se 1 (by rfl) ⟨1180025, by rfl⟩ : syracuseStep 1573367 = 2360051) B2360051
theorem B1049095 : Blo 1048611 1049095 := bstep (se 1 (by rfl) ⟨786821, by rfl⟩ : syracuseStep 1049095 = 1573643) B1573643
theorem B1573391 : Blo 1048611 1573391 := bstep (se 1 (by rfl) ⟨1180043, by rfl⟩ : syracuseStep 1573391 = 2360087) B2360087
theorem B1049103 : Blo 1048611 1049103 := bstep (se 1 (by rfl) ⟨786827, by rfl⟩ : syracuseStep 1049103 = 1573655) B1573655
theorem B17924651 : Blo 1048611 17924651 := bstep (se 1 (by rfl) ⟨13443488, by rfl⟩ : syracuseStep 17924651 = 26886977) B26886977
theorem B1573433 : Blo 1048611 1573433 := bstep (se 2 (by rfl) ⟨590037, by rfl⟩ : syracuseStep 1573433 = 1180075) B1180075
theorem B1180219 : Blo 1048611 1180219 := bstep (se 1 (by rfl) ⟨885164, by rfl⟩ : syracuseStep 1180219 = 1770329) B1770329
theorem B1049147 : Blo 1048611 1049147 := bstep (se 1 (by rfl) ⟨786860, by rfl⟩ : syracuseStep 1049147 = 1573721) B1573721
theorem B2359943 : Blo 1048611 2359943 := bstep (se 1 (by rfl) ⟨1769957, by rfl⟩ : syracuseStep 2359943 = 3539915) B3539915
theorem B1573511 : Blo 1048611 1573511 := bstep (se 1 (by rfl) ⟨1180133, by rfl⟩ : syracuseStep 1573511 = 2360267) B2360267
theorem B1049223 : Blo 1048611 1049223 := bstep (se 1 (by rfl) ⟨786917, by rfl⟩ : syracuseStep 1049223 = 1573835) B1573835
theorem B1049231 : Blo 1048611 1049231 := bstep (se 1 (by rfl) ⟨786923, by rfl⟩ : syracuseStep 1049231 = 1573847) B1573847
theorem B1573547 : Blo 1048611 1573547 := bstep (se 1 (by rfl) ⟨1180160, by rfl⟩ : syracuseStep 1573547 = 2360321) B2360321
theorem B1049275 : Blo 1048611 1049275 := bstep (se 1 (by rfl) ⟨786956, by rfl⟩ : syracuseStep 1049275 = 1573913) B1573913
theorem B1573577 : Blo 1048611 1573577 := bstep (se 2 (by rfl) ⟨590091, by rfl⟩ : syracuseStep 1573577 = 1180183) B1180183
theorem B2654977 : Blo 1048611 2654977 := bstep (se 2 (by rfl) ⟨995616, by rfl⟩ : syracuseStep 2654977 = 1991233) B1991233
theorem B1049351 : Blo 1048611 1049351 := bstep (se 1 (by rfl) ⟨787013, by rfl⟩ : syracuseStep 1049351 = 1574027) B1574027
theorem B2523905 : Blo 1048611 2523905 := bstep (se 2 (by rfl) ⟨946464, by rfl⟩ : syracuseStep 2523905 = 1892929) B1892929
theorem B1049359 : Blo 1048611 1049359 := bstep (se 1 (by rfl) ⟨787019, by rfl⟩ : syracuseStep 1049359 = 1574039) B1574039
theorem B2360123 : Blo 1048611 2360123 := bstep (se 1 (by rfl) ⟨1770092, by rfl⟩ : syracuseStep 2360123 = 3540185) B3540185
theorem B1573691 : Blo 1048611 1573691 := bstep (se 1 (by rfl) ⟨1180268, by rfl⟩ : syracuseStep 1573691 = 2360537) B2360537
theorem B1049403 : Blo 1048611 1049403 := bstep (se 1 (by rfl) ⟨787052, by rfl⟩ : syracuseStep 1049403 = 1574105) B1574105
theorem B1573751 : Blo 1048611 1573751 := bstep (se 1 (by rfl) ⟨1180313, by rfl⟩ : syracuseStep 1573751 = 2360627) B2360627
theorem B1049479 : Blo 1048611 1049479 := bstep (se 1 (by rfl) ⟨787109, by rfl⟩ : syracuseStep 1049479 = 1574219) B1574219
theorem B1573775 : Blo 1048611 1573775 := bstep (se 1 (by rfl) ⟨1180331, by rfl⟩ : syracuseStep 1573775 = 2360663) B2360663
theorem B1049487 : Blo 1048611 1049487 := bstep (se 1 (by rfl) ⟨787115, by rfl⟩ : syracuseStep 1049487 = 1574231) B1574231
theorem B2360249 : Blo 1048611 2360249 := bstep (se 2 (by rfl) ⟨885093, by rfl⟩ : syracuseStep 2360249 = 1770187) B1770187
theorem B1573817 : Blo 1048611 1573817 := bstep (se 2 (by rfl) ⟨590181, by rfl⟩ : syracuseStep 1573817 = 1180363) B1180363
theorem B1049531 : Blo 1048611 1049531 := bstep (se 1 (by rfl) ⟨787148, by rfl⟩ : syracuseStep 1049531 = 1574297) B1574297
theorem B7963595 : Blo 1048611 7963595 := bstep (se 1 (by rfl) ⟨5972696, by rfl⟩ : syracuseStep 7963595 = 11945393) B11945393
theorem B5309387 : Blo 1048611 5309387 := bstep (se 1 (by rfl) ⟨3982040, by rfl⟩ : syracuseStep 5309387 = 7964081) B7964081
theorem B1573895 : Blo 1048611 1573895 := bstep (se 1 (by rfl) ⟨1180421, by rfl⟩ : syracuseStep 1573895 = 2360843) B2360843
theorem B1049607 : Blo 1048611 1049607 := bstep (se 1 (by rfl) ⟨787205, by rfl⟩ : syracuseStep 1049607 = 1574411) B1574411
theorem B1770511 : Blo 1048611 1770511 := bstep (se 1 (by rfl) ⟨1327883, by rfl⟩ : syracuseStep 1770511 = 2655767) B2655767
theorem B1180687 : Blo 1048611 1180687 := bstep (se 1 (by rfl) ⟨885515, by rfl⟩ : syracuseStep 1180687 = 1771031) B1771031
theorem B1049615 : Blo 1048611 1049615 := bstep (se 1 (by rfl) ⟨787211, by rfl⟩ : syracuseStep 1049615 = 1574423) B1574423
theorem B1573931 : Blo 1048611 1573931 := bstep (se 1 (by rfl) ⟨1180448, by rfl⟩ : syracuseStep 1573931 = 2360897) B2360897
theorem B1049659 : Blo 1048611 1049659 := bstep (se 1 (by rfl) ⟨787244, by rfl⟩ : syracuseStep 1049659 = 1574489) B1574489
theorem B1573961 : Blo 1048611 1573961 := bstep (se 2 (by rfl) ⟨590235, by rfl⟩ : syracuseStep 1573961 = 1180471) B1180471
theorem B11961431 : Blo 1048611 11961431 := bstep (se 1 (by rfl) ⟨8971073, by rfl⟩ : syracuseStep 11961431 = 17942147) B17942147
theorem B1049735 : Blo 1048611 1049735 := bstep (se 1 (by rfl) ⟨787301, by rfl⟩ : syracuseStep 1049735 = 1574603) B1574603
theorem B1049743 : Blo 1048611 1049743 := bstep (se 1 (by rfl) ⟨787307, by rfl⟩ : syracuseStep 1049743 = 1574615) B1574615
theorem B1574075 : Blo 1048611 1574075 := bstep (se 1 (by rfl) ⟨1180556, by rfl⟩ : syracuseStep 1574075 = 2361113) B2361113
theorem B1049787 : Blo 1048611 1049787 := bstep (se 1 (by rfl) ⟨787340, by rfl⟩ : syracuseStep 1049787 = 1574681) B1574681
theorem B1574135 : Blo 1048611 1574135 := bstep (se 1 (by rfl) ⟨1180601, by rfl⟩ : syracuseStep 1574135 = 2361203) B2361203
theorem B1049863 : Blo 1048611 1049863 := bstep (se 1 (by rfl) ⟨787397, by rfl⟩ : syracuseStep 1049863 = 1574795) B1574795
theorem B5309711 : Blo 1048611 5309711 := bstep (se 1 (by rfl) ⟨3982283, by rfl⟩ : syracuseStep 5309711 = 7964567) B7964567
theorem B3540239 : Blo 1048611 3540239 := bstep (se 1 (by rfl) ⟨2655179, by rfl⟩ : syracuseStep 3540239 = 5310359) B5310359
theorem B2360591 : Blo 1048611 2360591 := bstep (se 1 (by rfl) ⟨1770443, by rfl⟩ : syracuseStep 2360591 = 3540887) B3540887
theorem B1574159 : Blo 1048611 1574159 := bstep (se 1 (by rfl) ⟨1180619, by rfl⟩ : syracuseStep 1574159 = 2361239) B2361239
theorem B1049871 : Blo 1048611 1049871 := bstep (se 1 (by rfl) ⟨787403, by rfl⟩ : syracuseStep 1049871 = 1574807) B1574807
theorem B2360609 : Blo 1048611 2360609 := bstep (se 2 (by rfl) ⟨885228, by rfl⟩ : syracuseStep 2360609 = 1770457) B1770457
theorem B1574201 : Blo 1048611 1574201 := bstep (se 2 (by rfl) ⟨590325, by rfl⟩ : syracuseStep 1574201 = 1180651) B1180651
theorem B1049915 : Blo 1048611 1049915 := bstep (se 1 (by rfl) ⟨787436, by rfl⟩ : syracuseStep 1049915 = 1574873) B1574873
theorem B2655575 : Blo 1048611 2655575 := bstep (se 1 (by rfl) ⟨1991681, by rfl⟩ : syracuseStep 2655575 = 3983363) B3983363
theorem B1574279 : Blo 1048611 1574279 := bstep (se 1 (by rfl) ⟨1180709, by rfl⟩ : syracuseStep 1574279 = 2361419) B2361419
theorem B1049991 : Blo 1048611 1049991 := bstep (se 1 (by rfl) ⟨787493, by rfl⟩ : syracuseStep 1049991 = 1574987) B1574987
theorem B1049999 : Blo 1048611 1049999 := bstep (se 1 (by rfl) ⟨787499, by rfl⟩ : syracuseStep 1049999 = 1574999) B1574999
theorem B1574315 : Blo 1048611 1574315 := bstep (se 1 (by rfl) ⟨1180736, by rfl⟩ : syracuseStep 1574315 = 2361473) B2361473
theorem B1050043 : Blo 1048611 1050043 := bstep (se 1 (by rfl) ⟨787532, by rfl⟩ : syracuseStep 1050043 = 1575065) B1575065
theorem B1574345 : Blo 1048611 1574345 := bstep (se 2 (by rfl) ⟨590379, by rfl⟩ : syracuseStep 1574345 = 1180759) B1180759
theorem B1181191 : Blo 1048611 1181191 := bstep (se 1 (by rfl) ⟨885893, by rfl⟩ : syracuseStep 1181191 = 1771787) B1771787
theorem B1050119 : Blo 1048611 1050119 := bstep (se 1 (by rfl) ⟨787589, by rfl⟩ : syracuseStep 1050119 = 1575179) B1575179
theorem B1050127 : Blo 1048611 1050127 := bstep (se 1 (by rfl) ⟨787595, by rfl⟩ : syracuseStep 1050127 = 1575191) B1575191
theorem B3540509 : Blo 1048611 3540509 := bstep (se 3 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 3540509 = 1327691) B1327691
theorem B2655787 : Blo 1048611 2655787 := bstep (se 1 (by rfl) ⟨1991840, by rfl⟩ : syracuseStep 2655787 = 3983681) B3983681
theorem B1771051 : Blo 1048611 1771051 := bstep (se 1 (by rfl) ⟨1328288, by rfl⟩ : syracuseStep 1771051 = 2656577) B2656577
theorem B1574459 : Blo 1048611 1574459 := bstep (se 1 (by rfl) ⟨1180844, by rfl⟩ : syracuseStep 1574459 = 2361689) B2361689
theorem B1050171 : Blo 1048611 1050171 := bstep (se 1 (by rfl) ⟨787628, by rfl⟩ : syracuseStep 1050171 = 1575257) B1575257
theorem B2360951 : Blo 1048611 2360951 := bstep (se 1 (by rfl) ⟨1770713, by rfl⟩ : syracuseStep 2360951 = 3541427) B3541427
theorem B1574519 : Blo 1048611 1574519 := bstep (se 1 (by rfl) ⟨1180889, by rfl⟩ : syracuseStep 1574519 = 2361779) B2361779
theorem B1050247 : Blo 1048611 1050247 := bstep (se 1 (by rfl) ⟨787685, by rfl⟩ : syracuseStep 1050247 = 1575371) B1575371
theorem B1574543 : Blo 1048611 1574543 := bstep (se 1 (by rfl) ⟨1180907, by rfl⟩ : syracuseStep 1574543 = 2361815) B2361815
theorem B1050255 : Blo 1048611 1050255 := bstep (se 1 (by rfl) ⟨787691, by rfl⟩ : syracuseStep 1050255 = 1575383) B1575383
theorem B2655929 : Blo 1048611 2655929 := bstep (se 2 (by rfl) ⟨995973, by rfl⟩ : syracuseStep 2655929 = 1991947) B1991947
theorem B1771193 : Blo 1048611 1771193 := bstep (se 2 (by rfl) ⟨664197, by rfl⟩ : syracuseStep 1771193 = 1328395) B1328395
theorem B1574585 : Blo 1048611 1574585 := bstep (se 2 (by rfl) ⟨590469, by rfl⟩ : syracuseStep 1574585 = 1180939) B1180939
theorem B1181371 : Blo 1048611 1181371 := bstep (se 1 (by rfl) ⟨886028, by rfl⟩ : syracuseStep 1181371 = 1772057) B1772057
theorem B1050299 : Blo 1048611 1050299 := bstep (se 1 (by rfl) ⟨787724, by rfl⟩ : syracuseStep 1050299 = 1575449) B1575449
theorem B1574663 : Blo 1048611 1574663 := bstep (se 1 (by rfl) ⟨1180997, by rfl⟩ : syracuseStep 1574663 = 2361995) B2361995
theorem B1050375 : Blo 1048611 1050375 := bstep (se 1 (by rfl) ⟨787781, by rfl⟩ : syracuseStep 1050375 = 1575563) B1575563
theorem B1050383 : Blo 1048611 1050383 := bstep (se 1 (by rfl) ⟨787787, by rfl⟩ : syracuseStep 1050383 = 1575575) B1575575
theorem B2361131 : Blo 1048611 2361131 := bstep (se 1 (by rfl) ⟨1770848, by rfl⟩ : syracuseStep 2361131 = 3541697) B3541697
theorem B1574699 : Blo 1048611 1574699 := bstep (se 1 (by rfl) ⟨1181024, by rfl⟩ : syracuseStep 1574699 = 2362049) B2362049
theorem B1050427 : Blo 1048611 1050427 := bstep (se 1 (by rfl) ⟨787820, by rfl⟩ : syracuseStep 1050427 = 1575641) B1575641
theorem B1574729 : Blo 1048611 1574729 := bstep (se 2 (by rfl) ⟨590523, by rfl⟩ : syracuseStep 1574729 = 1181047) B1181047
theorem B28772171 : Blo 1048611 28772171 := bstep (se 1 (by rfl) ⟨21579128, by rfl⟩ : syracuseStep 28772171 = 43158257) B43158257
theorem B1050503 : Blo 1048611 1050503 := bstep (se 1 (by rfl) ⟨787877, by rfl⟩ : syracuseStep 1050503 = 1575755) B1575755
theorem B1050511 : Blo 1048611 1050511 := bstep (se 1 (by rfl) ⟨787883, by rfl⟩ : syracuseStep 1050511 = 1575767) B1575767
theorem B1574843 : Blo 1048611 1574843 := bstep (se 1 (by rfl) ⟨1181132, by rfl⟩ : syracuseStep 1574843 = 2362265) B2362265
theorem B1050555 : Blo 1048611 1050555 := bstep (se 1 (by rfl) ⟨787916, by rfl⟩ : syracuseStep 1050555 = 1575833) B1575833
theorem B1574903 : Blo 1048611 1574903 := bstep (se 1 (by rfl) ⟨1181177, by rfl⟩ : syracuseStep 1574903 = 2362355) B2362355
theorem B1050631 : Blo 1048611 1050631 := bstep (se 1 (by rfl) ⟨787973, by rfl⟩ : syracuseStep 1050631 = 1575947) B1575947
theorem B1574927 : Blo 1048611 1574927 := bstep (se 1 (by rfl) ⟨1181195, by rfl⟩ : syracuseStep 1574927 = 2362391) B2362391
theorem B1050639 : Blo 1048611 1050639 := bstep (se 1 (by rfl) ⟨787979, by rfl⟩ : syracuseStep 1050639 = 1575959) B1575959
theorem B1574969 : Blo 1048611 1574969 := bstep (se 2 (by rfl) ⟨590613, by rfl⟩ : syracuseStep 1574969 = 1181227) B1181227
theorem B11339837 : Blo 1048611 11339837 := bstep (se 3 (by rfl) ⟨2126219, by rfl⟩ : syracuseStep 11339837 = 4252439) B4252439
theorem B1050683 : Blo 1048611 1050683 := bstep (se 1 (by rfl) ⟨788012, by rfl⟩ : syracuseStep 1050683 = 1576025) B1576025
theorem B1575047 : Blo 1048611 1575047 := bstep (se 1 (by rfl) ⟨1181285, by rfl⟩ : syracuseStep 1575047 = 2362571) B2362571
theorem B1050759 : Blo 1048611 1050759 := bstep (se 1 (by rfl) ⟨788069, by rfl⟩ : syracuseStep 1050759 = 1576139) B1576139
theorem B1181839 : Blo 1048611 1181839 := bstep (se 1 (by rfl) ⟨886379, by rfl⟩ : syracuseStep 1181839 = 1772759) B1772759
theorem B1050767 : Blo 1048611 1050767 := bstep (se 1 (by rfl) ⟨788075, by rfl⟩ : syracuseStep 1050767 = 1576151) B1576151
theorem B2361491 : Blo 1048611 2361491 := bstep (se 1 (by rfl) ⟨1771118, by rfl⟩ : syracuseStep 2361491 = 3542237) B3542237
theorem B1575083 : Blo 1048611 1575083 := bstep (se 1 (by rfl) ⟨1181312, by rfl⟩ : syracuseStep 1575083 = 2362625) B2362625
theorem B1050811 : Blo 1048611 1050811 := bstep (se 1 (by rfl) ⟨788108, by rfl⟩ : syracuseStep 1050811 = 1576217) B1576217
theorem B2361545 : Blo 1048611 2361545 := bstep (se 2 (by rfl) ⟨885579, by rfl⟩ : syracuseStep 2361545 = 1771159) B1771159
theorem B1575113 : Blo 1048611 1575113 := bstep (se 2 (by rfl) ⟨590667, by rfl⟩ : syracuseStep 1575113 = 1181335) B1181335
theorem B20187377 : Blo 1048611 20187377 := bstep (se 2 (by rfl) ⟨7570266, by rfl⟩ : syracuseStep 20187377 = 15140533) B15140533
theorem B1050887 : Blo 1048611 1050887 := bstep (se 1 (by rfl) ⟨788165, by rfl⟩ : syracuseStep 1050887 = 1576331) B1576331
theorem B1050895 : Blo 1048611 1050895 := bstep (se 1 (by rfl) ⟨788171, by rfl⟩ : syracuseStep 1050895 = 1576343) B1576343
theorem B3410209 : Blo 1048611 3410209 := bstep (se 2 (by rfl) ⟨1278828, by rfl⟩ : syracuseStep 3410209 = 2557657) B2557657
theorem B1575227 : Blo 1048611 1575227 := bstep (se 1 (by rfl) ⟨1181420, by rfl⟩ : syracuseStep 1575227 = 2362841) B2362841
theorem B1050939 : Blo 1048611 1050939 := bstep (se 1 (by rfl) ⟨788204, by rfl⟩ : syracuseStep 1050939 = 1576409) B1576409
theorem B1771895 : Blo 1048611 1771895 := bstep (se 1 (by rfl) ⟨1328921, by rfl⟩ : syracuseStep 1771895 = 2657843) B2657843
theorem B1575287 : Blo 1048611 1575287 := bstep (se 1 (by rfl) ⟨1181465, by rfl⟩ : syracuseStep 1575287 = 2362931) B2362931
theorem B1051015 : Blo 1048611 1051015 := bstep (se 1 (by rfl) ⟨788261, by rfl⟩ : syracuseStep 1051015 = 1576523) B1576523
theorem B1575311 : Blo 1048611 1575311 := bstep (se 1 (by rfl) ⟨1181483, by rfl⟩ : syracuseStep 1575311 = 2362967) B2362967
theorem B1051023 : Blo 1048611 1051023 := bstep (se 1 (by rfl) ⟨788267, by rfl⟩ : syracuseStep 1051023 = 1576535) B1576535
theorem B1575353 : Blo 1048611 1575353 := bstep (se 2 (by rfl) ⟨590757, by rfl⟩ : syracuseStep 1575353 = 1181515) B1181515
theorem B1051067 : Blo 1048611 1051067 := bstep (se 1 (by rfl) ⟨788300, by rfl⟩ : syracuseStep 1051067 = 1576601) B1576601
theorem B1575431 : Blo 1048611 1575431 := bstep (se 1 (by rfl) ⟨1181573, by rfl⟩ : syracuseStep 1575431 = 2363147) B2363147
theorem B1051143 : Blo 1048611 1051143 := bstep (se 1 (by rfl) ⟨788357, by rfl⟩ : syracuseStep 1051143 = 1576715) B1576715
theorem B1051151 : Blo 1048611 1051151 := bstep (se 1 (by rfl) ⟨788363, by rfl⟩ : syracuseStep 1051151 = 1576727) B1576727
theorem B1575467 : Blo 1048611 1575467 := bstep (se 1 (by rfl) ⟨1181600, by rfl⟩ : syracuseStep 1575467 = 2363201) B2363201
theorem B1051195 : Blo 1048611 1051195 := bstep (se 1 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 1051195 = 1576793) B1576793
theorem B1575497 : Blo 1048611 1575497 := bstep (se 2 (by rfl) ⟨590811, by rfl⟩ : syracuseStep 1575497 = 1181623) B1181623
theorem B1182343 : Blo 1048611 1182343 := bstep (se 1 (by rfl) ⟨886757, by rfl⟩ : syracuseStep 1182343 = 1773515) B1773515
theorem B1051271 : Blo 1048611 1051271 := bstep (se 1 (by rfl) ⟨788453, by rfl⟩ : syracuseStep 1051271 = 1576907) B1576907
theorem B1051279 : Blo 1048611 1051279 := bstep (se 1 (by rfl) ⟨788459, by rfl⟩ : syracuseStep 1051279 = 1576919) B1576919
theorem B2656921 : Blo 1048611 2656921 := bstep (se 2 (by rfl) ⟨996345, by rfl⟩ : syracuseStep 2656921 = 1992691) B1992691
theorem B1575611 : Blo 1048611 1575611 := bstep (se 1 (by rfl) ⟨1181708, by rfl⟩ : syracuseStep 1575611 = 2363417) B2363417
theorem B1051323 : Blo 1048611 1051323 := bstep (se 1 (by rfl) ⟨788492, by rfl⟩ : syracuseStep 1051323 = 1576985) B1576985
theorem B5311169 : Blo 1048611 5311169 := bstep (se 2 (by rfl) ⟨1991688, by rfl⟩ : syracuseStep 5311169 = 3983377) B3983377
theorem B1575671 : Blo 1048611 1575671 := bstep (se 1 (by rfl) ⟨1181753, by rfl⟩ : syracuseStep 1575671 = 2363507) B2363507
theorem B1051399 : Blo 1048611 1051399 := bstep (se 1 (by rfl) ⟨788549, by rfl⟩ : syracuseStep 1051399 = 1577099) B1577099
theorem B1575695 : Blo 1048611 1575695 := bstep (se 1 (by rfl) ⟨1181771, by rfl⟩ : syracuseStep 1575695 = 2363543) B2363543
theorem B1051407 : Blo 1048611 1051407 := bstep (se 1 (by rfl) ⟨788555, by rfl⟩ : syracuseStep 1051407 = 1577111) B1577111
theorem B1575737 : Blo 1048611 1575737 := bstep (se 2 (by rfl) ⟨590901, by rfl⟩ : syracuseStep 1575737 = 1181803) B1181803
theorem B2657083 : Blo 1048611 2657083 := bstep (se 1 (by rfl) ⟨1992812, by rfl⟩ : syracuseStep 2657083 = 3985625) B3985625
theorem B1772347 : Blo 1048611 1772347 := bstep (se 1 (by rfl) ⟨1329260, by rfl⟩ : syracuseStep 1772347 = 2658521) B2658521
theorem B1182523 : Blo 1048611 1182523 := bstep (se 1 (by rfl) ⟨886892, by rfl⟩ : syracuseStep 1182523 = 1773785) B1773785
theorem B1051451 : Blo 1048611 1051451 := bstep (se 1 (by rfl) ⟨788588, by rfl⟩ : syracuseStep 1051451 = 1577177) B1577177
theorem B4787059 : Blo 1048611 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B2362247 : Blo 1048611 2362247 := bstep (se 1 (by rfl) ⟨1771685, by rfl⟩ : syracuseStep 2362247 = 3543371) B3543371
theorem B1575815 : Blo 1048611 1575815 := bstep (se 1 (by rfl) ⟨1181861, by rfl⟩ : syracuseStep 1575815 = 2363723) B2363723
theorem B1051527 : Blo 1048611 1051527 := bstep (se 1 (by rfl) ⟨788645, by rfl⟩ : syracuseStep 1051527 = 1577291) B1577291
theorem B1051535 : Blo 1048611 1051535 := bstep (se 1 (by rfl) ⟨788651, by rfl⟩ : syracuseStep 1051535 = 1577303) B1577303
theorem B3541913 : Blo 1048611 3541913 := bstep (se 2 (by rfl) ⟨1328217, by rfl⟩ : syracuseStep 3541913 = 2656435) B2656435
theorem B1575851 : Blo 1048611 1575851 := bstep (se 1 (by rfl) ⟨1181888, by rfl⟩ : syracuseStep 1575851 = 2363777) B2363777
theorem B1051579 : Blo 1048611 1051579 := bstep (se 1 (by rfl) ⟨788684, by rfl⟩ : syracuseStep 1051579 = 1577369) B1577369
theorem B2657225 : Blo 1048611 2657225 := bstep (se 2 (by rfl) ⟨996459, by rfl⟩ : syracuseStep 2657225 = 1992919) B1992919
theorem B1772489 : Blo 1048611 1772489 := bstep (se 2 (by rfl) ⟨664683, by rfl⟩ : syracuseStep 1772489 = 1329367) B1329367
theorem B1575881 : Blo 1048611 1575881 := bstep (se 2 (by rfl) ⟨590955, by rfl⟩ : syracuseStep 1575881 = 1181911) B1181911
theorem B1051655 : Blo 1048611 1051655 := bstep (se 1 (by rfl) ⟨788741, by rfl⟩ : syracuseStep 1051655 = 1577483) B1577483
theorem B1051663 : Blo 1048611 1051663 := bstep (se 1 (by rfl) ⟨788747, by rfl⟩ : syracuseStep 1051663 = 1577495) B1577495
theorem B2362427 : Blo 1048611 2362427 := bstep (se 1 (by rfl) ⟨1771820, by rfl⟩ : syracuseStep 2362427 = 3543641) B3543641
theorem B1575995 : Blo 1048611 1575995 := bstep (se 1 (by rfl) ⟨1181996, by rfl⟩ : syracuseStep 1575995 = 2363993) B2363993
theorem B1051707 : Blo 1048611 1051707 := bstep (se 1 (by rfl) ⟨788780, by rfl⟩ : syracuseStep 1051707 = 1577561) B1577561
theorem B1576055 : Blo 1048611 1576055 := bstep (se 1 (by rfl) ⟨1182041, by rfl⟩ : syracuseStep 1576055 = 2364083) B2364083
theorem B1051783 : Blo 1048611 1051783 := bstep (se 1 (by rfl) ⟨788837, by rfl⟩ : syracuseStep 1051783 = 1577675) B1577675
theorem B1576079 : Blo 1048611 1576079 := bstep (se 1 (by rfl) ⟨1182059, by rfl⟩ : syracuseStep 1576079 = 2364119) B2364119
theorem B1051791 : Blo 1048611 1051791 := bstep (se 1 (by rfl) ⟨788843, by rfl⟩ : syracuseStep 1051791 = 1577687) B1577687
theorem B2362553 : Blo 1048611 2362553 := bstep (se 2 (by rfl) ⟨885957, by rfl⟩ : syracuseStep 2362553 = 1771915) B1771915
theorem B1576121 : Blo 1048611 1576121 := bstep (se 2 (by rfl) ⟨591045, by rfl⟩ : syracuseStep 1576121 = 1182091) B1182091
theorem B1051835 : Blo 1048611 1051835 := bstep (se 1 (by rfl) ⟨788876, by rfl⟩ : syracuseStep 1051835 = 1577753) B1577753
theorem B1576199 : Blo 1048611 1576199 := bstep (se 1 (by rfl) ⟨1182149, by rfl⟩ : syracuseStep 1576199 = 2364299) B2364299
theorem B1051911 : Blo 1048611 1051911 := bstep (se 1 (by rfl) ⟨788933, by rfl⟩ : syracuseStep 1051911 = 1577867) B1577867
theorem B1182991 : Blo 1048611 1182991 := bstep (se 1 (by rfl) ⟨887243, by rfl⟩ : syracuseStep 1182991 = 1774487) B1774487
theorem B1051919 : Blo 1048611 1051919 := bstep (se 1 (by rfl) ⟨788939, by rfl⟩ : syracuseStep 1051919 = 1577879) B1577879
theorem B2657569 : Blo 1048611 2657569 := bstep (se 2 (by rfl) ⟨996588, by rfl⟩ : syracuseStep 2657569 = 1993177) B1993177
theorem B4492577 : Blo 1048611 4492577 := bstep (se 2 (by rfl) ⟨1684716, by rfl⟩ : syracuseStep 4492577 = 3369433) B3369433
theorem B1576235 : Blo 1048611 1576235 := bstep (se 1 (by rfl) ⟨1182176, by rfl⟩ : syracuseStep 1576235 = 2364353) B2364353
theorem B1051963 : Blo 1048611 1051963 := bstep (se 1 (by rfl) ⟨788972, by rfl⟩ : syracuseStep 1051963 = 1577945) B1577945
theorem B1576265 : Blo 1048611 1576265 := bstep (se 2 (by rfl) ⟨591099, by rfl⟩ : syracuseStep 1576265 = 1182199) B1182199
theorem B5541209 : Blo 1048611 5541209 := bstep (se 2 (by rfl) ⟨2077953, by rfl⟩ : syracuseStep 5541209 = 4155907) B4155907
theorem B1052039 : Blo 1048611 1052039 := bstep (se 1 (by rfl) ⟨789029, by rfl⟩ : syracuseStep 1052039 = 1578059) B1578059
theorem B1052047 : Blo 1048611 1052047 := bstep (se 1 (by rfl) ⟨789035, by rfl⟩ : syracuseStep 1052047 = 1578071) B1578071
theorem B5672339 : Blo 1048611 5672339 := bstep (se 1 (by rfl) ⟨4254254, by rfl⟩ : syracuseStep 5672339 = 8508509) B8508509
theorem B1346987 : Blo 1048611 1346987 := bstep (se 1 (by rfl) ⟨1010240, by rfl⟩ : syracuseStep 1346987 = 2020481) B2020481
theorem B1576379 : Blo 1048611 1576379 := bstep (se 1 (by rfl) ⟨1182284, by rfl⟩ : syracuseStep 1576379 = 2364569) B2364569
theorem B1052091 : Blo 1048611 1052091 := bstep (se 1 (by rfl) ⟨789068, by rfl⟩ : syracuseStep 1052091 = 1578137) B1578137
theorem B1576439 : Blo 1048611 1576439 := bstep (se 1 (by rfl) ⟨1182329, by rfl⟩ : syracuseStep 1576439 = 2364659) B2364659
theorem B1052167 : Blo 1048611 1052167 := bstep (se 1 (by rfl) ⟨789125, by rfl⟩ : syracuseStep 1052167 = 1578251) B1578251
theorem B2362895 : Blo 1048611 2362895 := bstep (se 1 (by rfl) ⟨1772171, by rfl⟩ : syracuseStep 2362895 = 3544343) B3544343
theorem B1576463 : Blo 1048611 1576463 := bstep (se 1 (by rfl) ⟨1182347, by rfl⟩ : syracuseStep 1576463 = 2364695) B2364695
theorem B1052175 : Blo 1048611 1052175 := bstep (se 1 (by rfl) ⟨789131, by rfl⟩ : syracuseStep 1052175 = 1578263) B1578263
theorem B2362913 : Blo 1048611 2362913 := bstep (se 2 (by rfl) ⟨886092, by rfl⟩ : syracuseStep 2362913 = 1772185) B1772185
theorem B1576505 : Blo 1048611 1576505 := bstep (se 2 (by rfl) ⟨591189, by rfl⟩ : syracuseStep 1576505 = 1182379) B1182379
theorem B1052219 : Blo 1048611 1052219 := bstep (se 1 (by rfl) ⟨789164, by rfl⟩ : syracuseStep 1052219 = 1578329) B1578329
theorem B3542615 : Blo 1048611 3542615 := bstep (se 1 (by rfl) ⟨2656961, by rfl⟩ : syracuseStep 3542615 = 5313923) B5313923
theorem B1773191 : Blo 1048611 1773191 := bstep (se 1 (by rfl) ⟨1329893, by rfl⟩ : syracuseStep 1773191 = 2659787) B2659787
theorem B1576583 : Blo 1048611 1576583 := bstep (se 1 (by rfl) ⟨1182437, by rfl⟩ : syracuseStep 1576583 = 2364875) B2364875
theorem B1052295 : Blo 1048611 1052295 := bstep (se 1 (by rfl) ⟨789221, by rfl⟩ : syracuseStep 1052295 = 1578443) B1578443
theorem B1052303 : Blo 1048611 1052303 := bstep (se 1 (by rfl) ⟨789227, by rfl⟩ : syracuseStep 1052303 = 1578455) B1578455
theorem B1576619 : Blo 1048611 1576619 := bstep (se 1 (by rfl) ⟨1182464, by rfl⟩ : syracuseStep 1576619 = 2364929) B2364929
theorem B1052347 : Blo 1048611 1052347 := bstep (se 1 (by rfl) ⟨789260, by rfl⟩ : syracuseStep 1052347 = 1578521) B1578521
theorem B1576649 : Blo 1048611 1576649 := bstep (se 2 (by rfl) ⟨591243, by rfl⟩ : syracuseStep 1576649 = 1182487) B1182487
theorem B1183495 : Blo 1048611 1183495 := bstep (se 1 (by rfl) ⟨887621, by rfl⟩ : syracuseStep 1183495 = 1775243) B1775243
theorem B1052423 : Blo 1048611 1052423 := bstep (se 1 (by rfl) ⟨789317, by rfl⟩ : syracuseStep 1052423 = 1578635) B1578635
theorem B9080591 : Blo 1048611 9080591 := bstep (se 1 (by rfl) ⟨6810443, by rfl⟩ : syracuseStep 9080591 = 13620887) B13620887
theorem B1052431 : Blo 1048611 1052431 := bstep (se 1 (by rfl) ⟨789323, by rfl⟩ : syracuseStep 1052431 = 1578647) B1578647
theorem B1576763 : Blo 1048611 1576763 := bstep (se 1 (by rfl) ⟨1182572, by rfl⟩ : syracuseStep 1576763 = 2365145) B2365145
theorem B1052475 : Blo 1048611 1052475 := bstep (se 1 (by rfl) ⟨789356, by rfl⟩ : syracuseStep 1052475 = 1578713) B1578713
theorem B2658167 : Blo 1048611 2658167 := bstep (se 1 (by rfl) ⟨1993625, by rfl⟩ : syracuseStep 2658167 = 3987251) B3987251
theorem B2363255 : Blo 1048611 2363255 := bstep (se 1 (by rfl) ⟨1772441, by rfl⟩ : syracuseStep 2363255 = 3544883) B3544883
theorem B1576823 : Blo 1048611 1576823 := bstep (se 1 (by rfl) ⟨1182617, by rfl⟩ : syracuseStep 1576823 = 2365235) B2365235
theorem B1052551 : Blo 1048611 1052551 := bstep (se 1 (by rfl) ⟨789413, by rfl⟩ : syracuseStep 1052551 = 1578827) B1578827
theorem B1576847 : Blo 1048611 1576847 := bstep (se 1 (by rfl) ⟨1182635, by rfl⟩ : syracuseStep 1576847 = 2365271) B2365271
theorem B1052559 : Blo 1048611 1052559 := bstep (se 1 (by rfl) ⟨789419, by rfl⟩ : syracuseStep 1052559 = 1578839) B1578839
theorem B1576889 : Blo 1048611 1576889 := bstep (se 2 (by rfl) ⟨591333, by rfl⟩ : syracuseStep 1576889 = 1182667) B1182667
theorem B1183675 : Blo 1048611 1183675 := bstep (se 1 (by rfl) ⟨887756, by rfl⟩ : syracuseStep 1183675 = 1775513) B1775513
theorem B1052603 : Blo 1048611 1052603 := bstep (se 1 (by rfl) ⟨789452, by rfl⟩ : syracuseStep 1052603 = 1578905) B1578905
theorem B5312465 : Blo 1048611 5312465 := bstep (se 2 (by rfl) ⟨1992174, by rfl⟩ : syracuseStep 5312465 = 3984349) B3984349
theorem B1576967 : Blo 1048611 1576967 := bstep (se 1 (by rfl) ⟨1182725, by rfl⟩ : syracuseStep 1576967 = 2365451) B2365451
theorem B2560033 : Blo 1048611 2560033 := bstep (se 2 (by rfl) ⟨960012, by rfl⟩ : syracuseStep 2560033 = 1920025) B1920025
theorem B2363435 : Blo 1048611 2363435 := bstep (se 1 (by rfl) ⟨1772576, by rfl⟩ : syracuseStep 2363435 = 3545153) B3545153
theorem B1577003 : Blo 1048611 1577003 := bstep (se 1 (by rfl) ⟨1182752, by rfl⟩ : syracuseStep 1577003 = 2365505) B2365505
theorem B1347643 : Blo 1048611 1347643 := bstep (se 1 (by rfl) ⟨1010732, by rfl⟩ : syracuseStep 1347643 = 2021465) B2021465
theorem B3543101 : Blo 1048611 3543101 := bstep (se 3 (by rfl) ⟨664331, by rfl⟩ : syracuseStep 3543101 = 1328663) B1328663
theorem B1577033 : Blo 1048611 1577033 := bstep (se 2 (by rfl) ⟨591387, by rfl⟩ : syracuseStep 1577033 = 1182775) B1182775
theorem B1577147 : Blo 1048611 1577147 := bstep (se 1 (by rfl) ⟨1182860, by rfl⟩ : syracuseStep 1577147 = 2365721) B2365721
theorem B1577207 : Blo 1048611 1577207 := bstep (se 1 (by rfl) ⟨1182905, by rfl⟩ : syracuseStep 1577207 = 2365811) B2365811
theorem B1773839 : Blo 1048611 1773839 := bstep (se 1 (by rfl) ⟨1330379, by rfl⟩ : syracuseStep 1773839 = 2660759) B2660759
theorem B1577231 : Blo 1048611 1577231 := bstep (se 1 (by rfl) ⟨1182923, by rfl⟩ : syracuseStep 1577231 = 2365847) B2365847
theorem B1577273 : Blo 1048611 1577273 := bstep (se 2 (by rfl) ⟨591477, by rfl⟩ : syracuseStep 1577273 = 1182955) B1182955
theorem B1577351 : Blo 1048611 1577351 := bstep (se 1 (by rfl) ⟨1183013, by rfl⟩ : syracuseStep 1577351 = 2366027) B2366027
theorem B1184143 : Blo 1048611 1184143 := bstep (se 1 (by rfl) ⟨888107, by rfl⟩ : syracuseStep 1184143 = 1776215) B1776215
theorem B2363795 : Blo 1048611 2363795 := bstep (se 1 (by rfl) ⟨1772846, by rfl⟩ : syracuseStep 2363795 = 3545693) B3545693
theorem B1577387 : Blo 1048611 1577387 := bstep (se 1 (by rfl) ⟨1183040, by rfl⟩ : syracuseStep 1577387 = 2366081) B2366081
theorem B2363849 : Blo 1048611 2363849 := bstep (se 2 (by rfl) ⟨886443, by rfl⟩ : syracuseStep 2363849 = 1772887) B1772887
theorem B1577417 : Blo 1048611 1577417 := bstep (se 2 (by rfl) ⟨591531, by rfl⟩ : syracuseStep 1577417 = 1183063) B1183063
theorem B1577531 : Blo 1048611 1577531 := bstep (se 1 (by rfl) ⟨1183148, by rfl⟩ : syracuseStep 1577531 = 2366297) B2366297
theorem B1577591 : Blo 1048611 1577591 := bstep (se 1 (by rfl) ⟨1183193, by rfl⟩ : syracuseStep 1577591 = 2366387) B2366387
theorem B1577615 : Blo 1048611 1577615 := bstep (se 1 (by rfl) ⟨1183211, by rfl⟩ : syracuseStep 1577615 = 2366423) B2366423
theorem B1577657 : Blo 1048611 1577657 := bstep (se 2 (by rfl) ⟨591621, by rfl⟩ : syracuseStep 1577657 = 1183243) B1183243
theorem B1577735 : Blo 1048611 1577735 := bstep (se 1 (by rfl) ⟨1183301, by rfl⟩ : syracuseStep 1577735 = 2366603) B2366603
theorem B1774379 : Blo 1048611 1774379 := bstep (se 1 (by rfl) ⟨1330784, by rfl⟩ : syracuseStep 1774379 = 2661569) B2661569
theorem B1577771 : Blo 1048611 1577771 := bstep (se 1 (by rfl) ⟨1183328, by rfl⟩ : syracuseStep 1577771 = 2366657) B2366657
theorem B1577801 : Blo 1048611 1577801 := bstep (se 2 (by rfl) ⟨591675, by rfl⟩ : syracuseStep 1577801 = 1183351) B1183351
theorem B1708919 : Blo 1048611 1708919 := bstep (se 1 (by rfl) ⟨1281689, by rfl⟩ : syracuseStep 1708919 = 2563379) B2563379
theorem B1577915 : Blo 1048611 1577915 := bstep (se 1 (by rfl) ⟨1183436, by rfl⟩ : syracuseStep 1577915 = 2366873) B2366873
theorem B1577975 : Blo 1048611 1577975 := bstep (se 1 (by rfl) ⟨1183481, by rfl⟩ : syracuseStep 1577975 = 2366963) B2366963
theorem B13440005 : Blo 1048611 13440005 := bstep (se 4 (by rfl) ⟨1260000, by rfl⟩ : syracuseStep 13440005 = 2520001) B2520001
theorem B1577999 : Blo 1048611 1577999 := bstep (se 1 (by rfl) ⟨1183499, by rfl⟩ : syracuseStep 1577999 = 2366999) B2366999
theorem B1578041 : Blo 1048611 1578041 := bstep (se 2 (by rfl) ⟨591765, by rfl⟩ : syracuseStep 1578041 = 1183531) B1183531
theorem B2659463 : Blo 1048611 2659463 := bstep (se 1 (by rfl) ⟨1994597, by rfl⟩ : syracuseStep 2659463 = 3989195) B3989195
theorem B2364551 : Blo 1048611 2364551 := bstep (se 1 (by rfl) ⟨1773413, by rfl⟩ : syracuseStep 2364551 = 3546827) B3546827
theorem B1578119 : Blo 1048611 1578119 := bstep (se 1 (by rfl) ⟨1183589, by rfl⟩ : syracuseStep 1578119 = 2367179) B2367179
theorem B5674157 : Blo 1048611 5674157 := bstep (se 3 (by rfl) ⟨1063904, by rfl⟩ : syracuseStep 5674157 = 2127809) B2127809
theorem B1578155 : Blo 1048611 1578155 := bstep (se 1 (by rfl) ⟨1183616, by rfl⟩ : syracuseStep 1578155 = 2367233) B2367233
theorem B2659513 : Blo 1048611 2659513 := bstep (se 2 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 2659513 = 1994635) B1994635
theorem B1774777 : Blo 1048611 1774777 := bstep (se 2 (by rfl) ⟨665541, by rfl⟩ : syracuseStep 1774777 = 1331083) B1331083
theorem B2528441 : Blo 1048611 2528441 := bstep (se 2 (by rfl) ⟨948165, by rfl⟩ : syracuseStep 2528441 = 1896331) B1896331
theorem B1578185 : Blo 1048611 1578185 := bstep (se 2 (by rfl) ⟨591819, by rfl⟩ : syracuseStep 1578185 = 1183639) B1183639
theorem B2364731 : Blo 1048611 2364731 := bstep (se 1 (by rfl) ⟨1773548, by rfl⟩ : syracuseStep 2364731 = 3547097) B3547097
theorem B1578299 : Blo 1048611 1578299 := bstep (se 1 (by rfl) ⟨1183724, by rfl⟩ : syracuseStep 1578299 = 2367449) B2367449
theorem B2987351 : Blo 1048611 2987351 := bstep (se 1 (by rfl) ⟨2240513, by rfl⟩ : syracuseStep 2987351 = 4481027) B4481027
theorem B1578359 : Blo 1048611 1578359 := bstep (se 1 (by rfl) ⟨1183769, by rfl⟩ : syracuseStep 1578359 = 2367539) B2367539
theorem B1578383 : Blo 1048611 1578383 := bstep (se 1 (by rfl) ⟨1183787, by rfl⟩ : syracuseStep 1578383 = 2367575) B2367575
theorem B3544505 : Blo 1048611 3544505 := bstep (se 2 (by rfl) ⟨1329189, by rfl⟩ : syracuseStep 3544505 = 2658379) B2658379
theorem B2364857 : Blo 1048611 2364857 := bstep (se 2 (by rfl) ⟨886821, by rfl⟩ : syracuseStep 2364857 = 1773643) B1773643
theorem B1578425 : Blo 1048611 1578425 := bstep (se 2 (by rfl) ⟨591909, by rfl⟩ : syracuseStep 1578425 = 1183819) B1183819
theorem B1578503 : Blo 1048611 1578503 := bstep (se 1 (by rfl) ⟨1183877, by rfl⟩ : syracuseStep 1578503 = 2367755) B2367755
theorem B1578539 : Blo 1048611 1578539 := bstep (se 1 (by rfl) ⟨1183904, by rfl⟩ : syracuseStep 1578539 = 2367809) B2367809
theorem B2987579 : Blo 1048611 2987579 := bstep (se 1 (by rfl) ⟨2240684, by rfl⟩ : syracuseStep 2987579 = 4481369) B4481369
theorem B1578569 : Blo 1048611 1578569 := bstep (se 2 (by rfl) ⟨591963, by rfl⟩ : syracuseStep 1578569 = 1183927) B1183927
theorem B38311501 : Blo 1048611 38311501 := bstep (se 3 (by rfl) ⟨7183406, by rfl⟩ : syracuseStep 38311501 = 14366813) B14366813
theorem B2528921 : Blo 1048611 2528921 := bstep (se 2 (by rfl) ⟨948345, by rfl⟩ : syracuseStep 2528921 = 1896691) B1896691
theorem B2987705 : Blo 1048611 2987705 := bstep (se 2 (by rfl) ⟨1120389, by rfl⟩ : syracuseStep 2987705 = 2240779) B2240779
theorem B1578683 : Blo 1048611 1578683 := bstep (se 1 (by rfl) ⟨1184012, by rfl⟩ : syracuseStep 1578683 = 2368025) B2368025
theorem B1578743 : Blo 1048611 1578743 := bstep (se 1 (by rfl) ⟨1184057, by rfl⟩ : syracuseStep 1578743 = 2368115) B2368115
theorem B4495105 : Blo 1048611 4495105 := bstep (se 2 (by rfl) ⟨1685664, by rfl⟩ : syracuseStep 4495105 = 3371329) B3371329
theorem B2660111 : Blo 1048611 2660111 := bstep (se 1 (by rfl) ⟨1995083, by rfl⟩ : syracuseStep 2660111 = 3990167) B3990167
theorem B2365199 : Blo 1048611 2365199 := bstep (se 1 (by rfl) ⟨1773899, by rfl⟩ : syracuseStep 2365199 = 3547799) B3547799
theorem B1578767 : Blo 1048611 1578767 := bstep (se 1 (by rfl) ⟨1184075, by rfl⟩ : syracuseStep 1578767 = 2368151) B2368151
theorem B2365217 : Blo 1048611 2365217 := bstep (se 2 (by rfl) ⟨886956, by rfl⟩ : syracuseStep 2365217 = 1773913) B1773913
theorem B1578809 : Blo 1048611 1578809 := bstep (se 2 (by rfl) ⟨592053, by rfl⟩ : syracuseStep 1578809 = 1184107) B1184107
theorem B1775479 : Blo 1048611 1775479 := bstep (se 1 (by rfl) ⟨1331609, by rfl⟩ : syracuseStep 1775479 = 2663219) B2663219
theorem B1578887 : Blo 1048611 1578887 := bstep (se 1 (by rfl) ⟨1184165, by rfl⟩ : syracuseStep 1578887 = 2368331) B2368331
theorem B5314571 : Blo 1048611 5314571 := bstep (se 1 (by rfl) ⟨3985928, by rfl⟩ : syracuseStep 5314571 = 7971857) B7971857
theorem B3545099 : Blo 1048611 3545099 := bstep (se 1 (by rfl) ⟨2658824, by rfl⟩ : syracuseStep 3545099 = 5317649) B5317649
theorem B1775675 : Blo 1048611 1775675 := bstep (se 1 (by rfl) ⟨1331756, by rfl⟩ : syracuseStep 1775675 = 2663513) B2663513
theorem B3545207 : Blo 1048611 3545207 := bstep (se 1 (by rfl) ⟨2658905, by rfl⟩ : syracuseStep 3545207 = 5317811) B5317811
theorem B2365559 : Blo 1048611 2365559 := bstep (se 1 (by rfl) ⟨1774169, by rfl⟩ : syracuseStep 2365559 = 3548339) B3548339
theorem B7968941 : Blo 1048611 7968941 := bstep (se 3 (by rfl) ⟨1494176, by rfl⟩ : syracuseStep 7968941 = 2988353) B2988353
theorem B5314733 : Blo 1048611 5314733 := bstep (se 3 (by rfl) ⟨996512, by rfl⟩ : syracuseStep 5314733 = 1993025) B1993025
theorem B2365739 : Blo 1048611 2365739 := bstep (se 1 (by rfl) ⟨1774304, by rfl⟩ : syracuseStep 2365739 = 3548609) B3548609
theorem B2660809 : Blo 1048611 2660809 := bstep (se 2 (by rfl) ⟨997803, by rfl⟩ : syracuseStep 2660809 = 1995607) B1995607
theorem B1776073 : Blo 1048611 1776073 := bstep (se 2 (by rfl) ⟨666027, by rfl⟩ : syracuseStep 1776073 = 1332055) B1332055
theorem B5052881 : Blo 1048611 5052881 := bstep (se 2 (by rfl) ⟨1894830, by rfl⟩ : syracuseStep 5052881 = 3789661) B3789661
theorem B2660951 : Blo 1048611 2660951 := bstep (se 1 (by rfl) ⟨1995713, by rfl⟩ : syracuseStep 2660951 = 3991427) B3991427
theorem B2366099 : Blo 1048611 2366099 := bstep (se 1 (by rfl) ⟨1774574, by rfl⟩ : syracuseStep 2366099 = 3549149) B3549149
theorem B3545801 : Blo 1048611 3545801 := bstep (se 2 (by rfl) ⟨1329675, by rfl⟩ : syracuseStep 3545801 = 2659351) B2659351
theorem B2366153 : Blo 1048611 2366153 := bstep (se 2 (by rfl) ⟨887307, by rfl⟩ : syracuseStep 2366153 = 1774615) B1774615
theorem B4037357 : Blo 1048611 4037357 := bstep (se 3 (by rfl) ⟨757004, by rfl⟩ : syracuseStep 4037357 = 1514009) B1514009
theorem B6069335 : Blo 1048611 6069335 := bstep (se 1 (by rfl) ⟨4552001, by rfl⟩ : syracuseStep 6069335 = 9104003) B9104003
theorem B29924549 : Blo 1048611 29924549 := bstep (se 4 (by rfl) ⟨2805426, by rfl⟩ : syracuseStep 29924549 = 5610853) B5610853
theorem B2989345 : Blo 1048611 2989345 := bstep (se 2 (by rfl) ⟨1121004, by rfl⟩ : syracuseStep 2989345 = 2242009) B2242009
theorem B5053747 : Blo 1048611 5053747 := bstep (se 1 (by rfl) ⟨3790310, by rfl⟩ : syracuseStep 5053747 = 7580621) B7580621
theorem B3546503 : Blo 1048611 3546503 := bstep (se 1 (by rfl) ⟨2659877, by rfl⟩ : syracuseStep 3546503 = 5319755) B5319755
theorem B2366855 : Blo 1048611 2366855 := bstep (se 1 (by rfl) ⟨1775141, by rfl⟩ : syracuseStep 2366855 = 3550283) B3550283
theorem B2301385 : Blo 1048611 2301385 := bstep (se 2 (by rfl) ⟨863019, by rfl⟩ : syracuseStep 2301385 = 1726039) B1726039
theorem B1973705 : Blo 1048611 1973705 := bstep (se 2 (by rfl) ⟨740139, by rfl⟩ : syracuseStep 1973705 = 1480279) B1480279
theorem B2367035 : Blo 1048611 2367035 := bstep (se 1 (by rfl) ⟨1775276, by rfl⟩ : syracuseStep 2367035 = 3550553) B3550553
theorem B2367161 : Blo 1048611 2367161 := bstep (se 2 (by rfl) ⟨887685, by rfl⟩ : syracuseStep 2367161 = 1775371) B1775371
theorem B5316353 : Blo 1048611 5316353 := bstep (se 2 (by rfl) ⟨1993632, by rfl⟩ : syracuseStep 5316353 = 3987265) B3987265
theorem B3546881 : Blo 1048611 3546881 := bstep (se 2 (by rfl) ⟨1330080, by rfl⟩ : syracuseStep 3546881 = 2660161) B2660161
theorem B2989835 : Blo 1048611 2989835 := bstep (se 1 (by rfl) ⟨2242376, by rfl⟩ : syracuseStep 2989835 = 4484753) B4484753
theorem B2367503 : Blo 1048611 2367503 := bstep (se 1 (by rfl) ⟨1775627, by rfl⟩ : syracuseStep 2367503 = 3551255) B3551255
theorem B2367521 : Blo 1048611 2367521 := bstep (se 2 (by rfl) ⟨887820, by rfl⟩ : syracuseStep 2367521 = 1775641) B1775641
theorem B6725693 : Blo 1048611 6725693 := bstep (se 3 (by rfl) ⟨1261067, by rfl⟩ : syracuseStep 6725693 = 2522135) B2522135
theorem B1941689 : Blo 1048611 1941689 := bstep (se 2 (by rfl) ⟨728133, by rfl⟩ : syracuseStep 1941689 = 1456267) B1456267
theorem B21537089 : Blo 1048611 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B2367863 : Blo 1048611 2367863 := bstep (se 1 (by rfl) ⟨1775897, by rfl⟩ : syracuseStep 2367863 = 3551795) B3551795
theorem B25534865 : Blo 1048611 25534865 := bstep (se 2 (by rfl) ⟨9575574, by rfl⟩ : syracuseStep 25534865 = 19151149) B19151149
theorem B2990621 : Blo 1048611 2990621 := bstep (se 3 (by rfl) ⟨560741, by rfl⟩ : syracuseStep 2990621 = 1121483) B1121483
theorem B5317163 : Blo 1048611 5317163 := bstep (se 1 (by rfl) ⟨3987872, by rfl⟩ : syracuseStep 5317163 = 7975745) B7975745
theorem B7971371 : Blo 1048611 7971371 := bstep (se 1 (by rfl) ⟨5978528, by rfl⟩ : syracuseStep 7971371 = 11957057) B11957057
theorem B3547691 : Blo 1048611 3547691 := bstep (se 1 (by rfl) ⟨2660768, by rfl⟩ : syracuseStep 3547691 = 5321537) B5321537
theorem B2368043 : Blo 1048611 2368043 := bstep (se 1 (by rfl) ⟨1776032, by rfl⟩ : syracuseStep 2368043 = 3552065) B3552065
theorem B2663027 : Blo 1048611 2663027 := bstep (se 1 (by rfl) ⟨1997270, by rfl⟩ : syracuseStep 2663027 = 3994541) B3994541
theorem B5055149 : Blo 1048611 5055149 := bstep (se 3 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 5055149 = 1895681) B1895681
theorem B17933399 : Blo 1048611 17933399 := bstep (se 1 (by rfl) ⟨13450049, by rfl⟩ : syracuseStep 17933399 = 26900099) B26900099
theorem B2663543 : Blo 1048611 2663543 := bstep (se 1 (by rfl) ⟨1997657, by rfl⟩ : syracuseStep 2663543 = 3995315) B3995315
theorem B1680841 : Blo 1048611 1680841 := bstep (se 2 (by rfl) ⟨630315, by rfl⟩ : syracuseStep 1680841 = 1260631) B1260631
theorem B5318459 : Blo 1048611 5318459 := bstep (se 1 (by rfl) ⟨3988844, by rfl⟩ : syracuseStep 5318459 = 7977689) B7977689
theorem B3548987 : Blo 1048611 3548987 := bstep (se 1 (by rfl) ⟨2661740, by rfl⟩ : syracuseStep 3548987 = 5323481) B5323481
theorem B28747637 : Blo 1048611 28747637 := bstep (se 5 (by rfl) ⟨1347545, by rfl⟩ : syracuseStep 28747637 = 2695091) B2695091
theorem B5121937 : Blo 1048611 5121937 := bstep (se 2 (by rfl) ⟨1920726, by rfl⟩ : syracuseStep 5121937 = 3841453) B3841453
theorem B5318621 : Blo 1048611 5318621 := bstep (se 3 (by rfl) ⟨997241, by rfl⟩ : syracuseStep 5318621 = 1994483) B1994483
theorem B5974019 : Blo 1048611 5974019 := bstep (se 1 (by rfl) ⟨4480514, by rfl⟩ : syracuseStep 5974019 = 8961029) B8961029
theorem B6727691 : Blo 1048611 6727691 := bstep (se 1 (by rfl) ⟨5045768, by rfl⟩ : syracuseStep 6727691 = 10091537) B10091537
theorem B6400043 : Blo 1048611 6400043 := bstep (se 1 (by rfl) ⟨4800032, by rfl⟩ : syracuseStep 6400043 = 9600065) B9600065
theorem B5679305 : Blo 1048611 5679305 := bstep (se 2 (by rfl) ⟨2129739, by rfl⟩ : syracuseStep 5679305 = 4259479) B4259479
theorem B5318945 : Blo 1048611 5318945 := bstep (se 2 (by rfl) ⟨1994604, by rfl⟩ : syracuseStep 5318945 = 3989209) B3989209
theorem B3549473 : Blo 1048611 3549473 := bstep (se 2 (by rfl) ⟨1331052, by rfl⟩ : syracuseStep 3549473 = 2662105) B2662105
theorem B2992727 : Blo 1048611 2992727 := bstep (se 1 (by rfl) ⟨2244545, by rfl⟩ : syracuseStep 2992727 = 4489091) B4489091
theorem B1682039 : Blo 1048611 1682039 := bstep (se 1 (by rfl) ⟨1261529, by rfl⟩ : syracuseStep 1682039 = 2523059) B2523059
theorem B5057225 : Blo 1048611 5057225 := bstep (se 2 (by rfl) ⟨1896459, by rfl⟩ : syracuseStep 5057225 = 3792919) B3792919
theorem B3550067 : Blo 1048611 3550067 := bstep (se 1 (by rfl) ⟨2662550, by rfl⟩ : syracuseStep 3550067 = 5325101) B5325101
theorem B3779513 : Blo 1048611 3779513 := bstep (se 2 (by rfl) ⟨1417317, by rfl⟩ : syracuseStep 3779513 = 2834635) B2834635
theorem B5319917 : Blo 1048611 5319917 := bstep (se 3 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 5319917 = 1994969) B1994969
theorem B2993593 : Blo 1048611 2993593 := bstep (se 2 (by rfl) ⟨1122597, by rfl⟩ : syracuseStep 2993593 = 2245195) B2245195
theorem B5058071 : Blo 1048611 5058071 := bstep (se 1 (by rfl) ⟨3793553, by rfl⟩ : syracuseStep 5058071 = 7587107) B7587107
theorem B61484771 : Blo 1048611 61484771 := bstep (se 1 (by rfl) ⟨46113578, by rfl⟩ : syracuseStep 61484771 = 92227157) B92227157
theorem B7286543 : Blo 1048611 7286543 := bstep (se 1 (by rfl) ⟨5464907, by rfl⟩ : syracuseStep 7286543 = 10929815) B10929815
theorem B2993935 : Blo 1048611 2993935 := bstep (se 1 (by rfl) ⟨2245451, by rfl⟩ : syracuseStep 2993935 = 4490903) B4490903
theorem B5320727 : Blo 1048611 5320727 := bstep (se 1 (by rfl) ⟨3990545, by rfl⟩ : syracuseStep 5320727 = 7981091) B7981091
theorem B2994209 : Blo 1048611 2994209 := bstep (se 2 (by rfl) ⟨1122828, by rfl⟩ : syracuseStep 2994209 = 2245657) B2245657
theorem B1683641 : Blo 1048611 1683641 := bstep (se 2 (by rfl) ⟨631365, by rfl⟩ : syracuseStep 1683641 = 1262731) B1262731
theorem B10105033 : Blo 1048611 10105033 := bstep (se 2 (by rfl) ⟨3789387, by rfl⟩ : syracuseStep 10105033 = 7578775) B7578775
theorem B3191069 : Blo 1048611 3191069 := bstep (se 3 (by rfl) ⟨598325, by rfl⟩ : syracuseStep 3191069 = 1196651) B1196651
theorem B2994823 : Blo 1048611 2994823 := bstep (se 1 (by rfl) ⟨2246117, by rfl⟩ : syracuseStep 2994823 = 4492235) B4492235
theorem B2995211 : Blo 1048611 2995211 := bstep (se 1 (by rfl) ⟨2246408, by rfl⟩ : syracuseStep 2995211 = 4492817) B4492817
theorem B1684871 : Blo 1048611 1684871 := bstep (se 1 (by rfl) ⟨1263653, by rfl⟩ : syracuseStep 1684871 = 2527307) B2527307
theorem B8533811 : Blo 1048611 8533811 := bstep (se 1 (by rfl) ⟨6400358, by rfl⟩ : syracuseStep 8533811 = 12800717) B12800717
theorem B11974553 : Blo 1048611 11974553 := bstep (se 2 (by rfl) ⟨4490457, by rfl⟩ : syracuseStep 11974553 = 8980915) B8980915
theorem B2996509 : Blo 1048611 2996509 := bstep (se 3 (by rfl) ⟨561845, by rfl⟩ : syracuseStep 2996509 = 1123691) B1123691
theorem B1685819 : Blo 1048611 1685819 := bstep (se 1 (by rfl) ⟨1264364, by rfl⟩ : syracuseStep 1685819 = 2528729) B2528729
theorem B3193175 : Blo 1048611 3193175 := bstep (se 1 (by rfl) ⟨2394881, by rfl⟩ : syracuseStep 3193175 = 4789763) B4789763
theorem B6732179 : Blo 1048611 6732179 := bstep (se 1 (by rfl) ⟨5049134, by rfl⟩ : syracuseStep 6732179 = 10098269) B10098269
theorem B5978711 : Blo 1048611 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B2996851 : Blo 1048611 2996851 := bstep (se 1 (by rfl) ⟨2247638, by rfl⟩ : syracuseStep 2996851 = 4495277) B4495277
theorem B5749555 : Blo 1048611 5749555 := bstep (se 1 (by rfl) ⟨4312166, by rfl⟩ : syracuseStep 5749555 = 8624333) B8624333
theorem B2243513 : Blo 1048611 2243513 := bstep (se 2 (by rfl) ⟨841317, by rfl⟩ : syracuseStep 2243513 = 1682635) B1682635
theorem B23313419 : Blo 1048611 23313419 := bstep (se 1 (by rfl) ⟨17485064, by rfl⟩ : syracuseStep 23313419 = 34970129) B34970129
theorem B5323805 : Blo 1048611 5323805 := bstep (se 3 (by rfl) ⟨998213, by rfl⟩ : syracuseStep 5323805 = 1996427) B1996427
theorem B2243855 : Blo 1048611 2243855 := bstep (se 1 (by rfl) ⟨1682891, by rfl⟩ : syracuseStep 2243855 = 3365783) B3365783
theorem B1621367 : Blo 1048611 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B3030419 : Blo 1048611 3030419 := bstep (se 1 (by rfl) ⟨2272814, by rfl⟩ : syracuseStep 3030419 = 4545629) B4545629
theorem B5324291 : Blo 1048611 5324291 := bstep (se 1 (by rfl) ⟨3993218, by rfl⟩ : syracuseStep 5324291 = 7986437) B7986437
theorem B6471191 : Blo 1048611 6471191 := bstep (se 1 (by rfl) ⟨4853393, by rfl⟩ : syracuseStep 6471191 = 9706787) B9706787
theorem B17972765 : Blo 1048611 17972765 := bstep (se 3 (by rfl) ⟨3369893, by rfl⟩ : syracuseStep 17972765 = 6739787) B6739787
theorem B1261327 : Blo 1048611 1261327 := bstep (se 1 (by rfl) ⟨945995, by rfl⟩ : syracuseStep 1261327 = 1891991) B1891991
theorem B1917047 : Blo 1048611 1917047 := bstep (se 1 (by rfl) ⟨1437785, by rfl⟩ : syracuseStep 1917047 = 2875571) B2875571
theorem B2244743 : Blo 1048611 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B3588353 : Blo 1048611 3588353 := bstep (se 2 (by rfl) ⟨1345632, by rfl⟩ : syracuseStep 3588353 = 2691265) B2691265
theorem B1327367 : Blo 1048611 1327367 := bstep (se 1 (by rfl) ⟨995525, by rfl⟩ : syracuseStep 1327367 = 1991051) B1991051
theorem B5980625 : Blo 1048611 5980625 := bstep (se 2 (by rfl) ⟨2242734, by rfl⟩ : syracuseStep 5980625 = 4485469) B4485469
theorem B2245153 : Blo 1048611 2245153 := bstep (se 2 (by rfl) ⟨841932, by rfl⟩ : syracuseStep 2245153 = 1683865) B1683865
theorem B2245495 : Blo 1048611 2245495 := bstep (se 1 (by rfl) ⟨1684121, by rfl⟩ : syracuseStep 2245495 = 3368243) B3368243
theorem B1328015 : Blo 1048611 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B7980119 : Blo 1048611 7980119 := bstep (se 1 (by rfl) ⟨5985089, by rfl⟩ : syracuseStep 7980119 = 11970179) B11970179
theorem B5325911 : Blo 1048611 5325911 := bstep (se 1 (by rfl) ⟨3994433, by rfl⟩ : syracuseStep 5325911 = 7988867) B7988867
theorem B17515757 : Blo 1048611 17515757 := bstep (se 3 (by rfl) ⟨3284204, by rfl⟩ : syracuseStep 17515757 = 6568409) B6568409
theorem B3196361 : Blo 1048611 3196361 := bstep (se 2 (by rfl) ⟨1198635, by rfl⟩ : syracuseStep 3196361 = 2397271) B2397271
theorem B1263095 : Blo 1048611 1263095 := bstep (se 1 (by rfl) ⟨947321, by rfl⟩ : syracuseStep 1263095 = 1894643) B1894643
theorem B3982877 : Blo 1048611 3982877 := bstep (se 3 (by rfl) ⟨746789, by rfl⟩ : syracuseStep 3982877 = 1493579) B1493579
theorem B3982891 : Blo 1048611 3982891 := bstep (se 1 (by rfl) ⟨2987168, by rfl⟩ : syracuseStep 3982891 = 5974337) B5974337
theorem B5326397 : Blo 1048611 5326397 := bstep (se 3 (by rfl) ⟨998699, by rfl⟩ : syracuseStep 5326397 = 1997399) B1997399
theorem B2246459 : Blo 1048611 2246459 := bstep (se 1 (by rfl) ⟨1684844, by rfl⟩ : syracuseStep 2246459 = 3369689) B3369689
theorem B3360797 : Blo 1048611 3360797 := bstep (se 3 (by rfl) ⟨630149, by rfl⟩ : syracuseStep 3360797 = 1260299) B1260299
theorem B2246699 : Blo 1048611 2246699 := bstep (se 1 (by rfl) ⟨1685024, by rfl⟩ : syracuseStep 2246699 = 3370049) B3370049
theorem B64702637 : Blo 1048611 64702637 := bstep (se 3 (by rfl) ⟨12131744, by rfl⟩ : syracuseStep 64702637 = 24263489) B24263489
theorem B2837035 : Blo 1048611 2837035 := bstep (se 1 (by rfl) ⟨2127776, by rfl⟩ : syracuseStep 2837035 = 4255553) B4255553
theorem B2247211 : Blo 1048611 2247211 := bstep (se 1 (by rfl) ⟨1685408, by rfl⟩ : syracuseStep 2247211 = 3370817) B3370817
theorem B12798769 : Blo 1048611 12798769 := bstep (se 2 (by rfl) ⟨4799538, by rfl⟩ : syracuseStep 12798769 = 9599077) B9599077
theorem B1494217 : Blo 1048611 1494217 := bstep (se 2 (by rfl) ⟨560331, by rfl⟩ : syracuseStep 1494217 = 1120663) B1120663
theorem B5328179 : Blo 1048611 5328179 := bstep (se 1 (by rfl) ⟨3996134, by rfl⟩ : syracuseStep 5328179 = 7992269) B7992269
theorem B3198475 : Blo 1048611 3198475 := bstep (se 1 (by rfl) ⟨2398856, by rfl⟩ : syracuseStep 3198475 = 4797713) B4797713
theorem B5328503 : Blo 1048611 5328503 := bstep (se 1 (by rfl) ⟨3996377, by rfl⟩ : syracuseStep 5328503 = 7992755) B7992755
theorem B1330987 : Blo 1048611 1330987 := bstep (se 1 (by rfl) ⟨998240, by rfl⟩ : syracuseStep 1330987 = 1996481) B1996481
theorem B17977139 : Blo 1048611 17977139 := bstep (se 1 (by rfl) ⟨13482854, by rfl⟩ : syracuseStep 17977139 = 26965709) B26965709
theorem B2838419 : Blo 1048611 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B3199351 : Blo 1048611 3199351 := bstep (se 1 (by rfl) ⟨2399513, by rfl⟩ : syracuseStep 3199351 = 4799027) B4799027
theorem B2838937 : Blo 1048611 2838937 := bstep (se 2 (by rfl) ⟨1064601, by rfl⟩ : syracuseStep 2838937 = 2129203) B2129203
theorem B3363257 : Blo 1048611 3363257 := bstep (se 2 (by rfl) ⟨1261221, by rfl⟩ : syracuseStep 3363257 = 2522443) B2522443
theorem B1331959 : Blo 1048611 1331959 := bstep (se 1 (by rfl) ⟨998969, by rfl⟩ : syracuseStep 1331959 = 1997939) B1997939
theorem B19190789 : Blo 1048611 19190789 := bstep (se 4 (by rfl) ⟨1799136, by rfl⟩ : syracuseStep 19190789 = 3598273) B3598273
theorem B6738967 : Blo 1048611 6738967 := bstep (se 1 (by rfl) ⟨5054225, by rfl⟩ : syracuseStep 6738967 = 10108451) B10108451
theorem B1922363 : Blo 1048611 1922363 := bstep (se 1 (by rfl) ⟨1441772, by rfl⟩ : syracuseStep 1922363 = 2883545) B2883545
theorem B5985683 : Blo 1048611 5985683 := bstep (se 1 (by rfl) ⟨4489262, by rfl⟩ : syracuseStep 5985683 = 8978525) B8978525
theorem B1594811 : Blo 1048611 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B1889851 : Blo 1048611 1889851 := bstep (se 1 (by rfl) ⟨1417388, by rfl⟩ : syracuseStep 1889851 = 2834777) B2834777
theorem B8509157 : Blo 1048611 8509157 := bstep (se 4 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 8509157 = 1595467) B1595467
theorem B5986183 : Blo 1048611 5986183 := bstep (se 1 (by rfl) ⟨4489637, by rfl⟩ : syracuseStep 5986183 = 8979275) B8979275
theorem B17946521 : Blo 1048611 17946521 := bstep (se 2 (by rfl) ⟨6729945, by rfl⟩ : syracuseStep 17946521 = 13459891) B13459891
theorem B1497161 : Blo 1048611 1497161 := bstep (se 2 (by rfl) ⟨561435, by rfl⟩ : syracuseStep 1497161 = 1122871) B1122871
theorem B3791119 : Blo 1048611 3791119 := bstep (se 1 (by rfl) ⟨2843339, by rfl⟩ : syracuseStep 3791119 = 5686679) B5686679
theorem B1595783 : Blo 1048611 1595783 := bstep (se 1 (by rfl) ⟨1196837, by rfl⟩ : syracuseStep 1595783 = 2393675) B2393675
theorem B3463741 : Blo 1048611 3463741 := bstep (se 3 (by rfl) ⟨649451, by rfl⟩ : syracuseStep 3463741 = 1298903) B1298903
theorem B3988055 : Blo 1048611 3988055 := bstep (se 1 (by rfl) ⟨2991041, by rfl⟩ : syracuseStep 3988055 = 5982083) B5982083
theorem B1498027 : Blo 1048611 1498027 := bstep (se 1 (by rfl) ⟨1123520, by rfl⟩ : syracuseStep 1498027 = 2247041) B2247041
theorem B3988541 : Blo 1048611 3988541 := bstep (se 3 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 3988541 = 1495703) B1495703
theorem B3366203 : Blo 1048611 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B3366461 : Blo 1048611 3366461 := bstep (se 3 (by rfl) ⟨631211, by rfl⟩ : syracuseStep 3366461 = 1262423) B1262423
theorem B1597243 : Blo 1048611 1597243 := bstep (se 1 (by rfl) ⟨1197932, by rfl⟩ : syracuseStep 1597243 = 2395865) B2395865
theorem B4251905 : Blo 1048611 4251905 := bstep (se 2 (by rfl) ⟨1594464, by rfl⟩ : syracuseStep 4251905 = 3188929) B3188929
theorem B12771715 : Blo 1048611 12771715 := bstep (se 1 (by rfl) ⟨9578786, by rfl⟩ : syracuseStep 12771715 = 19157573) B19157573
theorem B36397457 : Blo 1048611 36397457 := bstep (se 2 (by rfl) ⟨13649046, by rfl⟩ : syracuseStep 36397457 = 27298093) B27298093
theorem B10215827 : Blo 1048611 10215827 := bstep (se 1 (by rfl) ⟨7661870, by rfl⟩ : syracuseStep 10215827 = 15323741) B15323741
theorem B1892755 : Blo 1048611 1892755 := bstep (se 1 (by rfl) ⟨1419566, by rfl⟩ : syracuseStep 1892755 = 2839133) B2839133
theorem B3989969 : Blo 1048611 3989969 := bstep (se 2 (by rfl) ⟨1496238, by rfl⟩ : syracuseStep 3989969 = 2992477) B2992477
theorem B11952683 : Blo 1048611 11952683 := bstep (se 1 (by rfl) ⟨8964512, by rfl⟩ : syracuseStep 11952683 = 17929025) B17929025
theorem B1598071 : Blo 1048611 1598071 := bstep (se 1 (by rfl) ⟨1198553, by rfl⟩ : syracuseStep 1598071 = 2397107) B2397107
theorem B2843425 : Blo 1048611 2843425 := bstep (se 2 (by rfl) ⟨1066284, by rfl⟩ : syracuseStep 2843425 = 2132569) B2132569
theorem B43082533 : Blo 1048611 43082533 := bstep (se 4 (by rfl) ⟨4038987, by rfl⟩ : syracuseStep 43082533 = 8077975) B8077975
theorem B14377817 : Blo 1048611 14377817 := bstep (se 2 (by rfl) ⟨5391681, by rfl⟩ : syracuseStep 14377817 = 10783363) B10783363
theorem B2843545 : Blo 1048611 2843545 := bstep (se 2 (by rfl) ⟨1066329, by rfl⟩ : syracuseStep 2843545 = 2132659) B2132659
theorem B105014341 : Blo 1048611 105014341 := bstep (se 4 (by rfl) ⟨9845094, by rfl⟩ : syracuseStep 105014341 = 19690189) B19690189
theorem B11494865 : Blo 1048611 11494865 := bstep (se 2 (by rfl) ⟨4310574, by rfl⟩ : syracuseStep 11494865 = 8621149) B8621149
theorem B3368459 : Blo 1048611 3368459 := bstep (se 1 (by rfl) ⟨2526344, by rfl⟩ : syracuseStep 3368459 = 5052689) B5052689
theorem B1992251 : Blo 1048611 1992251 := bstep (se 1 (by rfl) ⟨1494188, by rfl⟩ : syracuseStep 1992251 = 2988377) B2988377
theorem B1992737 : Blo 1048611 1992737 := bstep (se 2 (by rfl) ⟨747276, by rfl⟩ : syracuseStep 1992737 = 1494553) B1494553
theorem B5040215 : Blo 1048611 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B3991639 : Blo 1048611 3991639 := bstep (se 1 (by rfl) ⟨2993729, by rfl⟩ : syracuseStep 3991639 = 5987459) B5987459
theorem B5400695 : Blo 1048611 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B1993079 : Blo 1048611 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B3991943 : Blo 1048611 3991943 := bstep (se 1 (by rfl) ⟨2993957, by rfl⟩ : syracuseStep 3991943 = 5987915) B5987915
theorem B9857539 : Blo 1048611 9857539 := bstep (se 1 (by rfl) ⟨7393154, by rfl⟩ : syracuseStep 9857539 = 14786309) B14786309
theorem B3992125 : Blo 1048611 3992125 := bstep (se 3 (by rfl) ⟨748523, by rfl⟩ : syracuseStep 3992125 = 1497047) B1497047
theorem B1797391 : Blo 1048611 1797391 := bstep (se 1 (by rfl) ⟨1348043, by rfl⟩ : syracuseStep 1797391 = 2696087) B2696087
theorem B10087811 : Blo 1048611 10087811 := bstep (se 1 (by rfl) ⟨7565858, by rfl⟩ : syracuseStep 10087811 = 15131717) B15131717
theorem B5991833 : Blo 1048611 5991833 := bstep (se 2 (by rfl) ⟨2246937, by rfl⟩ : syracuseStep 5991833 = 4493875) B4493875
theorem B2879293 : Blo 1048611 2879293 := bstep (se 3 (by rfl) ⟨539867, by rfl⟩ : syracuseStep 2879293 = 1079735) B1079735
theorem B1994681 : Blo 1048611 1994681 := bstep (se 2 (by rfl) ⟨748005, by rfl⟩ : syracuseStep 1994681 = 1496011) B1496011
theorem B3993857 : Blo 1048611 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B1995023 : Blo 1048611 1995023 := bstep (se 1 (by rfl) ⟨1496267, by rfl⟩ : syracuseStep 1995023 = 2992535) B2992535
theorem B1077895 : Blo 1048611 1077895 := bstep (se 1 (by rfl) ⟨808421, by rfl⟩ : syracuseStep 1077895 = 1616843) B1616843
theorem B45413297 : Blo 1048611 45413297 := bstep (se 2 (by rfl) ⟨17029986, by rfl⟩ : syracuseStep 45413297 = 34059973) B34059973
theorem B20771851 : Blo 1048611 20771851 := bstep (se 1 (by rfl) ⟨15578888, by rfl⟩ : syracuseStep 20771851 = 31157777) B31157777
theorem B1995835 : Blo 1048611 1995835 := bstep (se 1 (by rfl) ⟨1496876, by rfl⟩ : syracuseStep 1995835 = 2993753) B2993753
theorem B4486205 : Blo 1048611 4486205 := bstep (se 3 (by rfl) ⟨841163, by rfl⟩ : syracuseStep 4486205 = 1682327) B1682327
theorem B1995911 : Blo 1048611 1995911 := bstep (se 1 (by rfl) ⟨1496933, by rfl⟩ : syracuseStep 1995911 = 2993867) B2993867
theorem B3995027 : Blo 1048611 3995027 := bstep (se 1 (by rfl) ⟨2996270, by rfl⟩ : syracuseStep 3995027 = 5992541) B5992541
theorem B9598493 : Blo 1048611 9598493 := bstep (se 3 (by rfl) ⟨1799717, by rfl⟩ : syracuseStep 9598493 = 3599435) B3599435
theorem B1996321 : Blo 1048611 1996321 := bstep (se 2 (by rfl) ⟨748620, by rfl⟩ : syracuseStep 1996321 = 1497241) B1497241
theorem B1996663 : Blo 1048611 1996663 := bstep (se 1 (by rfl) ⟨1497497, by rfl⟩ : syracuseStep 1996663 = 2994995) B2994995
theorem B3995527 : Blo 1048611 3995527 := bstep (se 1 (by rfl) ⟨2996645, by rfl⟩ : syracuseStep 3995527 = 5993291) B5993291
theorem B7993241 : Blo 1048611 7993241 := bstep (se 2 (by rfl) ⟨2997465, by rfl⟩ : syracuseStep 7993241 = 5994931) B5994931
theorem B14383507 : Blo 1048611 14383507 := bstep (se 1 (by rfl) ⟨10787630, by rfl⟩ : syracuseStep 14383507 = 21575261) B21575261
theorem B4848569 : Blo 1048611 4848569 := bstep (se 2 (by rfl) ⟨1818213, by rfl⟩ : syracuseStep 4848569 = 3636427) B3636427
theorem B4488203 : Blo 1048611 4488203 := bstep (se 1 (by rfl) ⟨3366152, by rfl⟩ : syracuseStep 4488203 = 6732305) B6732305
theorem B5111225 : Blo 1048611 5111225 := bstep (se 2 (by rfl) ⟨1916709, by rfl⟩ : syracuseStep 5111225 = 3833419) B3833419
theorem B1998265 : Blo 1048611 1998265 := bstep (se 2 (by rfl) ⟨749349, by rfl⟩ : syracuseStep 1998265 = 1498699) B1498699
theorem B11369933 : Blo 1048611 11369933 := bstep (se 3 (by rfl) ⟨2131862, by rfl⟩ : syracuseStep 11369933 = 4263725) B4263725
theorem B2391851 : Blo 1048611 2391851 := bstep (se 1 (by rfl) ⟨1793888, by rfl⟩ : syracuseStep 2391851 = 3587777) B3587777
theorem B2129723 : Blo 1048611 2129723 := bstep (se 1 (by rfl) ⟨1597292, by rfl⟩ : syracuseStep 2129723 = 3194585) B3194585
theorem B1048615 : Blo 1048611 1048615 := bstep (se 1 (by rfl) ⟨786461, by rfl⟩ : syracuseStep 1048615 = 1572923) B1572923
theorem B1048655 : Blo 1048611 1048655 := bstep (se 1 (by rfl) ⟨786491, by rfl⟩ : syracuseStep 1048655 = 1572983) B1572983
theorem B1278031 : Blo 1048611 1278031 := bstep (se 1 (by rfl) ⟨958523, by rfl⟩ : syracuseStep 1278031 = 1917047) B1917047
theorem B1048671 : Blo 1048611 1048671 := bstep (se 1 (by rfl) ⟨786503, by rfl⟩ : syracuseStep 1048671 = 1573007) B1573007
theorem B1048699 : Blo 1048611 1048699 := bstep (se 1 (by rfl) ⟨786524, by rfl⟩ : syracuseStep 1048699 = 1573049) B1573049
theorem B2392235 : Blo 1048611 2392235 := bstep (se 1 (by rfl) ⟨1794176, by rfl⟩ : syracuseStep 2392235 = 3588353) B3588353
theorem B1048751 : Blo 1048611 1048751 := bstep (se 1 (by rfl) ⟨786563, by rfl⟩ : syracuseStep 1048751 = 1573127) B1573127
theorem B1048775 : Blo 1048611 1048775 := bstep (se 1 (by rfl) ⟨786581, by rfl⟩ : syracuseStep 1048775 = 1573163) B1573163
theorem B1048795 : Blo 1048611 1048795 := bstep (se 1 (by rfl) ⟨786596, by rfl⟩ : syracuseStep 1048795 = 1573193) B1573193
theorem B1048871 : Blo 1048611 1048871 := bstep (se 1 (by rfl) ⟨786653, by rfl⟩ : syracuseStep 1048871 = 1573307) B1573307
theorem B1048911 : Blo 1048611 1048911 := bstep (se 1 (by rfl) ⟨786683, by rfl⟩ : syracuseStep 1048911 = 1573367) B1573367
theorem B1048927 : Blo 1048611 1048927 := bstep (se 1 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 1048927 = 1573391) B1573391
theorem B1048955 : Blo 1048611 1048955 := bstep (se 1 (by rfl) ⟨786716, by rfl⟩ : syracuseStep 1048955 = 1573433) B1573433
theorem B1573295 : Blo 1048611 1573295 := bstep (se 1 (by rfl) ⟨1179971, by rfl⟩ : syracuseStep 1573295 = 2359943) B2359943
theorem B1049007 : Blo 1048611 1049007 := bstep (se 1 (by rfl) ⟨786755, by rfl⟩ : syracuseStep 1049007 = 1573511) B1573511
theorem B1049031 : Blo 1048611 1049031 := bstep (se 1 (by rfl) ⟨786773, by rfl⟩ : syracuseStep 1049031 = 1573547) B1573547
theorem B1049051 : Blo 1048611 1049051 := bstep (se 1 (by rfl) ⟨786788, by rfl⟩ : syracuseStep 1049051 = 1573577) B1573577
theorem B5177837 : Blo 1048611 5177837 := bstep (se 3 (by rfl) ⟨970844, by rfl⟩ : syracuseStep 5177837 = 1941689) B1941689
theorem B5767661 : Blo 1048611 5767661 := bstep (se 3 (by rfl) ⟨1081436, by rfl⟩ : syracuseStep 5767661 = 2162873) B2162873
theorem B2359817 : Blo 1048611 2359817 := bstep (se 2 (by rfl) ⟨884931, by rfl⟩ : syracuseStep 2359817 = 1769863) B1769863
theorem B1573385 : Blo 1048611 1573385 := bstep (se 2 (by rfl) ⟨590019, by rfl⟩ : syracuseStep 1573385 = 1180039) B1180039
theorem B2523673 : Blo 1048611 2523673 := bstep (se 2 (by rfl) ⟨946377, by rfl⟩ : syracuseStep 2523673 = 1892755) B1892755
theorem B1573415 : Blo 1048611 1573415 := bstep (se 1 (by rfl) ⟨1180061, by rfl⟩ : syracuseStep 1573415 = 2360123) B2360123
theorem B1049127 : Blo 1048611 1049127 := bstep (se 1 (by rfl) ⟨786845, by rfl⟩ : syracuseStep 1049127 = 1573691) B1573691
theorem B1049167 : Blo 1048611 1049167 := bstep (se 1 (by rfl) ⟨786875, by rfl⟩ : syracuseStep 1049167 = 1573751) B1573751
theorem B1049183 : Blo 1048611 1049183 := bstep (se 1 (by rfl) ⟨786887, by rfl⟩ : syracuseStep 1049183 = 1573775) B1573775
theorem B1573499 : Blo 1048611 1573499 := bstep (se 1 (by rfl) ⟨1180124, by rfl⟩ : syracuseStep 1573499 = 2360249) B2360249
theorem B1049211 : Blo 1048611 1049211 := bstep (se 1 (by rfl) ⟨786908, by rfl⟩ : syracuseStep 1049211 = 1573817) B1573817
theorem B5309063 : Blo 1048611 5309063 := bstep (se 1 (by rfl) ⟨3981797, by rfl⟩ : syracuseStep 5309063 = 7963595) B7963595
theorem B3539591 : Blo 1048611 3539591 := bstep (se 1 (by rfl) ⟨2654693, by rfl⟩ : syracuseStep 3539591 = 5309387) B5309387
theorem B1049263 : Blo 1048611 1049263 := bstep (se 1 (by rfl) ⟨786947, by rfl⟩ : syracuseStep 1049263 = 1573895) B1573895
theorem B3539645 : Blo 1048611 3539645 := bstep (se 3 (by rfl) ⟨663683, by rfl⟩ : syracuseStep 3539645 = 1327367) B1327367
theorem B1049287 : Blo 1048611 1049287 := bstep (se 1 (by rfl) ⟨786965, by rfl⟩ : syracuseStep 1049287 = 1573931) B1573931
theorem B1049307 : Blo 1048611 1049307 := bstep (se 1 (by rfl) ⟨786980, by rfl⟩ : syracuseStep 1049307 = 1573961) B1573961
theorem B1573625 : Blo 1048611 1573625 := bstep (se 2 (by rfl) ⟨590109, by rfl⟩ : syracuseStep 1573625 = 1180219) B1180219
theorem B1049383 : Blo 1048611 1049383 := bstep (se 1 (by rfl) ⟨787037, by rfl⟩ : syracuseStep 1049383 = 1574075) B1574075
theorem B2130761 : Blo 1048611 2130761 := bstep (se 2 (by rfl) ⟨799035, by rfl⟩ : syracuseStep 2130761 = 1598071) B1598071
theorem B1049423 : Blo 1048611 1049423 := bstep (se 1 (by rfl) ⟨787067, by rfl⟩ : syracuseStep 1049423 = 1574135) B1574135
theorem B3539807 : Blo 1048611 3539807 := bstep (se 1 (by rfl) ⟨2654855, by rfl⟩ : syracuseStep 3539807 = 5309711) B5309711
theorem B2360159 : Blo 1048611 2360159 := bstep (se 1 (by rfl) ⟨1770119, by rfl⟩ : syracuseStep 2360159 = 3540239) B3540239
theorem B1573727 : Blo 1048611 1573727 := bstep (se 1 (by rfl) ⟨1180295, by rfl⟩ : syracuseStep 1573727 = 2360591) B2360591
theorem B1049439 : Blo 1048611 1049439 := bstep (se 1 (by rfl) ⟨787079, by rfl⟩ : syracuseStep 1049439 = 1574159) B1574159
theorem B1573739 : Blo 1048611 1573739 := bstep (se 1 (by rfl) ⟨1180304, by rfl⟩ : syracuseStep 1573739 = 2360609) B2360609
theorem B1049467 : Blo 1048611 1049467 := bstep (se 1 (by rfl) ⟨787100, by rfl⟩ : syracuseStep 1049467 = 1574201) B1574201
theorem B1770383 : Blo 1048611 1770383 := bstep (se 1 (by rfl) ⟨1327787, by rfl⟩ : syracuseStep 1770383 = 2655575) B2655575
theorem B1049519 : Blo 1048611 1049519 := bstep (se 1 (by rfl) ⟨787139, by rfl⟩ : syracuseStep 1049519 = 1574279) B1574279
theorem B1049543 : Blo 1048611 1049543 := bstep (se 1 (by rfl) ⟨787157, by rfl⟩ : syracuseStep 1049543 = 1574315) B1574315
theorem B1049563 : Blo 1048611 1049563 := bstep (se 1 (by rfl) ⟨787172, by rfl⟩ : syracuseStep 1049563 = 1574345) B1574345
theorem B3539969 : Blo 1048611 3539969 := bstep (se 2 (by rfl) ⟨1327488, by rfl⟩ : syracuseStep 3539969 = 2654977) B2654977
theorem B2655251 : Blo 1048611 2655251 := bstep (se 1 (by rfl) ⟨1991438, by rfl⟩ : syracuseStep 2655251 = 3982877) B3982877
theorem B2360339 : Blo 1048611 2360339 := bstep (se 1 (by rfl) ⟨1770254, by rfl⟩ : syracuseStep 2360339 = 3540509) B3540509
theorem B1049639 : Blo 1048611 1049639 := bstep (se 1 (by rfl) ⟨787229, by rfl⟩ : syracuseStep 1049639 = 1574459) B1574459
theorem B57443377 : Blo 1048611 57443377 := bstep (se 2 (by rfl) ⟨21541266, by rfl⟩ : syracuseStep 57443377 = 43082533) B43082533
theorem B1573967 : Blo 1048611 1573967 := bstep (se 1 (by rfl) ⟨1180475, by rfl⟩ : syracuseStep 1573967 = 2360951) B2360951
theorem B1049679 : Blo 1048611 1049679 := bstep (se 1 (by rfl) ⟨787259, by rfl⟩ : syracuseStep 1049679 = 1574519) B1574519
theorem B1049695 : Blo 1048611 1049695 := bstep (se 1 (by rfl) ⟨787271, by rfl⟩ : syracuseStep 1049695 = 1574543) B1574543
theorem B1770619 : Blo 1048611 1770619 := bstep (se 1 (by rfl) ⟨1327964, by rfl⟩ : syracuseStep 1770619 = 2655929) B2655929
theorem B1180795 : Blo 1048611 1180795 := bstep (se 1 (by rfl) ⟨885596, by rfl⟩ : syracuseStep 1180795 = 1771193) B1771193
theorem B1049723 : Blo 1048611 1049723 := bstep (se 1 (by rfl) ⟨787292, by rfl⟩ : syracuseStep 1049723 = 1574585) B1574585
theorem B1049775 : Blo 1048611 1049775 := bstep (se 1 (by rfl) ⟨787331, by rfl⟩ : syracuseStep 1049775 = 1574663) B1574663
theorem B1574087 : Blo 1048611 1574087 := bstep (se 1 (by rfl) ⟨1180565, by rfl⟩ : syracuseStep 1574087 = 2361131) B2361131
theorem B1049799 : Blo 1048611 1049799 := bstep (se 1 (by rfl) ⟨787349, by rfl⟩ : syracuseStep 1049799 = 1574699) B1574699
theorem B1049819 : Blo 1048611 1049819 := bstep (se 1 (by rfl) ⟨787364, by rfl⟩ : syracuseStep 1049819 = 1574729) B1574729
theorem B1049895 : Blo 1048611 1049895 := bstep (se 1 (by rfl) ⟨787421, by rfl⟩ : syracuseStep 1049895 = 1574843) B1574843
theorem B1049935 : Blo 1048611 1049935 := bstep (se 1 (by rfl) ⟨787451, by rfl⟩ : syracuseStep 1049935 = 1574903) B1574903
theorem B1049951 : Blo 1048611 1049951 := bstep (se 1 (by rfl) ⟨787463, by rfl⟩ : syracuseStep 1049951 = 1574927) B1574927
theorem B2360681 : Blo 1048611 2360681 := bstep (se 2 (by rfl) ⟨885255, by rfl⟩ : syracuseStep 2360681 = 1770511) B1770511
theorem B1574249 : Blo 1048611 1574249 := bstep (se 2 (by rfl) ⟨590343, by rfl⟩ : syracuseStep 1574249 = 1180687) B1180687
theorem B1049979 : Blo 1048611 1049979 := bstep (se 1 (by rfl) ⟨787484, by rfl⟩ : syracuseStep 1049979 = 1574969) B1574969
theorem B1050031 : Blo 1048611 1050031 := bstep (se 1 (by rfl) ⟨787523, by rfl⟩ : syracuseStep 1050031 = 1575047) B1575047
theorem B140019121 : Blo 1048611 140019121 := bstep (se 2 (by rfl) ⟨52507170, by rfl⟩ : syracuseStep 140019121 = 105014341) B105014341
theorem B1574327 : Blo 1048611 1574327 := bstep (se 1 (by rfl) ⟨1180745, by rfl⟩ : syracuseStep 1574327 = 2361491) B2361491
theorem B1050055 : Blo 1048611 1050055 := bstep (se 1 (by rfl) ⟨787541, by rfl⟩ : syracuseStep 1050055 = 1575083) B1575083
theorem B1574363 : Blo 1048611 1574363 := bstep (se 1 (by rfl) ⟨1180772, by rfl⟩ : syracuseStep 1574363 = 2361545) B2361545
theorem B1050075 : Blo 1048611 1050075 := bstep (se 1 (by rfl) ⟨787556, by rfl⟩ : syracuseStep 1050075 = 1575113) B1575113
theorem B1050151 : Blo 1048611 1050151 := bstep (se 1 (by rfl) ⟨787613, by rfl⟩ : syracuseStep 1050151 = 1575227) B1575227
theorem B1181263 : Blo 1048611 1181263 := bstep (se 1 (by rfl) ⟨885947, by rfl⟩ : syracuseStep 1181263 = 1771895) B1771895
theorem B1050191 : Blo 1048611 1050191 := bstep (se 1 (by rfl) ⟨787643, by rfl⟩ : syracuseStep 1050191 = 1575287) B1575287
theorem B1050207 : Blo 1048611 1050207 := bstep (se 1 (by rfl) ⟨787655, by rfl⟩ : syracuseStep 1050207 = 1575311) B1575311
theorem B1050235 : Blo 1048611 1050235 := bstep (se 1 (by rfl) ⟨787676, by rfl⟩ : syracuseStep 1050235 = 1575353) B1575353
theorem B1050287 : Blo 1048611 1050287 := bstep (se 1 (by rfl) ⟨787715, by rfl⟩ : syracuseStep 1050287 = 1575431) B1575431
theorem B1050311 : Blo 1048611 1050311 := bstep (se 1 (by rfl) ⟨787733, by rfl⟩ : syracuseStep 1050311 = 1575467) B1575467
theorem B1050331 : Blo 1048611 1050331 := bstep (se 1 (by rfl) ⟨787748, by rfl⟩ : syracuseStep 1050331 = 1575497) B1575497
theorem B1050407 : Blo 1048611 1050407 := bstep (se 1 (by rfl) ⟨787805, by rfl⟩ : syracuseStep 1050407 = 1575611) B1575611
theorem B3540779 : Blo 1048611 3540779 := bstep (se 1 (by rfl) ⟨2655584, by rfl⟩ : syracuseStep 3540779 = 5311169) B5311169
theorem B1050447 : Blo 1048611 1050447 := bstep (se 1 (by rfl) ⟨787835, by rfl⟩ : syracuseStep 1050447 = 1575671) B1575671
theorem B1050463 : Blo 1048611 1050463 := bstep (se 1 (by rfl) ⟨787847, by rfl⟩ : syracuseStep 1050463 = 1575695) B1575695
theorem B1050491 : Blo 1048611 1050491 := bstep (se 1 (by rfl) ⟨787868, by rfl⟩ : syracuseStep 1050491 = 1575737) B1575737
theorem B1574831 : Blo 1048611 1574831 := bstep (se 1 (by rfl) ⟨1181123, by rfl⟩ : syracuseStep 1574831 = 2362247) B2362247
theorem B1050543 : Blo 1048611 1050543 := bstep (se 1 (by rfl) ⟨787907, by rfl⟩ : syracuseStep 1050543 = 1575815) B1575815
theorem B2361275 : Blo 1048611 2361275 := bstep (se 1 (by rfl) ⟨1770956, by rfl⟩ : syracuseStep 2361275 = 3541913) B3541913
theorem B1050567 : Blo 1048611 1050567 := bstep (se 1 (by rfl) ⟨787925, by rfl⟩ : syracuseStep 1050567 = 1575851) B1575851
theorem B1771483 : Blo 1048611 1771483 := bstep (se 1 (by rfl) ⟨1328612, by rfl⟩ : syracuseStep 1771483 = 2657225) B2657225
theorem B1181659 : Blo 1048611 1181659 := bstep (se 1 (by rfl) ⟨886244, by rfl⟩ : syracuseStep 1181659 = 1772489) B1772489
theorem B1050587 : Blo 1048611 1050587 := bstep (se 1 (by rfl) ⟨787940, by rfl⟩ : syracuseStep 1050587 = 1575881) B1575881
theorem B1574921 : Blo 1048611 1574921 := bstep (se 2 (by rfl) ⟨590595, by rfl⟩ : syracuseStep 1574921 = 1181191) B1181191
theorem B1574951 : Blo 1048611 1574951 := bstep (se 1 (by rfl) ⟨1181213, by rfl⟩ : syracuseStep 1574951 = 2362427) B2362427
theorem B1050663 : Blo 1048611 1050663 := bstep (se 1 (by rfl) ⟨787997, by rfl⟩ : syracuseStep 1050663 = 1575995) B1575995
theorem B5310521 : Blo 1048611 5310521 := bstep (se 2 (by rfl) ⟨1991445, by rfl⟩ : syracuseStep 5310521 = 3982891) B3982891
theorem B3541049 : Blo 1048611 3541049 := bstep (se 2 (by rfl) ⟨1327893, by rfl⟩ : syracuseStep 3541049 = 2655787) B2655787
theorem B2361401 : Blo 1048611 2361401 := bstep (se 2 (by rfl) ⟨885525, by rfl⟩ : syracuseStep 2361401 = 1771051) B1771051
theorem B1050703 : Blo 1048611 1050703 := bstep (se 1 (by rfl) ⟨788027, by rfl⟩ : syracuseStep 1050703 = 1576055) B1576055
theorem B1050719 : Blo 1048611 1050719 := bstep (se 1 (by rfl) ⟨788039, by rfl⟩ : syracuseStep 1050719 = 1576079) B1576079
theorem B1575035 : Blo 1048611 1575035 := bstep (se 1 (by rfl) ⟨1181276, by rfl⟩ : syracuseStep 1575035 = 2362553) B2362553
theorem B1050747 : Blo 1048611 1050747 := bstep (se 1 (by rfl) ⟨788060, by rfl⟩ : syracuseStep 1050747 = 1576121) B1576121
theorem B1050799 : Blo 1048611 1050799 := bstep (se 1 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 1050799 = 1576199) B1576199
theorem B1050823 : Blo 1048611 1050823 := bstep (se 1 (by rfl) ⟨788117, by rfl⟩ : syracuseStep 1050823 = 1576235) B1576235
theorem B1050843 : Blo 1048611 1050843 := bstep (se 1 (by rfl) ⟨788132, by rfl⟩ : syracuseStep 1050843 = 1576265) B1576265
theorem B1575161 : Blo 1048611 1575161 := bstep (se 2 (by rfl) ⟨590685, by rfl⟩ : syracuseStep 1575161 = 1181371) B1181371
theorem B1050919 : Blo 1048611 1050919 := bstep (se 1 (by rfl) ⟨788189, by rfl⟩ : syracuseStep 1050919 = 1576379) B1576379
theorem B1050959 : Blo 1048611 1050959 := bstep (se 1 (by rfl) ⟨788219, by rfl⟩ : syracuseStep 1050959 = 1576439) B1576439
theorem B1575263 : Blo 1048611 1575263 := bstep (se 1 (by rfl) ⟨1181447, by rfl⟩ : syracuseStep 1575263 = 2362895) B2362895
theorem B1050975 : Blo 1048611 1050975 := bstep (se 1 (by rfl) ⟨788231, by rfl⟩ : syracuseStep 1050975 = 1576463) B1576463
theorem B1575275 : Blo 1048611 1575275 := bstep (se 1 (by rfl) ⟨1181456, by rfl⟩ : syracuseStep 1575275 = 2362913) B2362913
theorem B1051003 : Blo 1048611 1051003 := bstep (se 1 (by rfl) ⟨788252, by rfl⟩ : syracuseStep 1051003 = 1576505) B1576505
theorem B3541373 : Blo 1048611 3541373 := bstep (se 3 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 3541373 = 1328015) B1328015
theorem B2361743 : Blo 1048611 2361743 := bstep (se 1 (by rfl) ⟨1771307, by rfl⟩ : syracuseStep 2361743 = 3542615) B3542615
theorem B1182127 : Blo 1048611 1182127 := bstep (se 1 (by rfl) ⟨886595, by rfl⟩ : syracuseStep 1182127 = 1773191) B1773191
theorem B1051055 : Blo 1048611 1051055 := bstep (se 1 (by rfl) ⟨788291, by rfl⟩ : syracuseStep 1051055 = 1576583) B1576583
theorem B1051079 : Blo 1048611 1051079 := bstep (se 1 (by rfl) ⟨788309, by rfl⟩ : syracuseStep 1051079 = 1576619) B1576619
theorem B1051099 : Blo 1048611 1051099 := bstep (se 1 (by rfl) ⟨788324, by rfl⟩ : syracuseStep 1051099 = 1576649) B1576649
theorem B1051175 : Blo 1048611 1051175 := bstep (se 1 (by rfl) ⟨788381, by rfl⟩ : syracuseStep 1051175 = 1576763) B1576763
theorem B1772111 : Blo 1048611 1772111 := bstep (se 1 (by rfl) ⟨1329083, by rfl⟩ : syracuseStep 1772111 = 2658167) B2658167
theorem B1575503 : Blo 1048611 1575503 := bstep (se 1 (by rfl) ⟨1181627, by rfl⟩ : syracuseStep 1575503 = 2363255) B2363255
theorem B1051215 : Blo 1048611 1051215 := bstep (se 1 (by rfl) ⟨788411, by rfl⟩ : syracuseStep 1051215 = 1576823) B1576823
theorem B1051231 : Blo 1048611 1051231 := bstep (se 1 (by rfl) ⟨788423, by rfl⟩ : syracuseStep 1051231 = 1576847) B1576847
theorem B1051259 : Blo 1048611 1051259 := bstep (se 1 (by rfl) ⟨788444, by rfl⟩ : syracuseStep 1051259 = 1576889) B1576889
theorem B3541643 : Blo 1048611 3541643 := bstep (se 1 (by rfl) ⟨2656232, by rfl⟩ : syracuseStep 3541643 = 5312465) B5312465
theorem B1051311 : Blo 1048611 1051311 := bstep (se 1 (by rfl) ⟨788483, by rfl⟩ : syracuseStep 1051311 = 1576967) B1576967
theorem B1575623 : Blo 1048611 1575623 := bstep (se 1 (by rfl) ⟨1181717, by rfl⟩ : syracuseStep 1575623 = 2363435) B2363435
theorem B1051335 : Blo 1048611 1051335 := bstep (se 1 (by rfl) ⟨788501, by rfl⟩ : syracuseStep 1051335 = 1577003) B1577003
theorem B2362067 : Blo 1048611 2362067 := bstep (se 1 (by rfl) ⟨1771550, by rfl⟩ : syracuseStep 2362067 = 3543101) B3543101
theorem B1051355 : Blo 1048611 1051355 := bstep (se 1 (by rfl) ⟨788516, by rfl⟩ : syracuseStep 1051355 = 1577033) B1577033
theorem B1051431 : Blo 1048611 1051431 := bstep (se 1 (by rfl) ⟨788573, by rfl⟩ : syracuseStep 1051431 = 1577147) B1577147
theorem B1051471 : Blo 1048611 1051471 := bstep (se 1 (by rfl) ⟨788603, by rfl⟩ : syracuseStep 1051471 = 1577207) B1577207
theorem B1182559 : Blo 1048611 1182559 := bstep (se 1 (by rfl) ⟨886919, by rfl⟩ : syracuseStep 1182559 = 1773839) B1773839
theorem B1051487 : Blo 1048611 1051487 := bstep (se 1 (by rfl) ⟨788615, by rfl⟩ : syracuseStep 1051487 = 1577231) B1577231
theorem B1575785 : Blo 1048611 1575785 := bstep (se 2 (by rfl) ⟨590919, by rfl⟩ : syracuseStep 1575785 = 1181839) B1181839
theorem B1051515 : Blo 1048611 1051515 := bstep (se 1 (by rfl) ⟨788636, by rfl⟩ : syracuseStep 1051515 = 1577273) B1577273
theorem B1051567 : Blo 1048611 1051567 := bstep (se 1 (by rfl) ⟨788675, by rfl⟩ : syracuseStep 1051567 = 1577351) B1577351
theorem B1575863 : Blo 1048611 1575863 := bstep (se 1 (by rfl) ⟨1181897, by rfl⟩ : syracuseStep 1575863 = 2363795) B2363795
theorem B1051591 : Blo 1048611 1051591 := bstep (se 1 (by rfl) ⟨788693, by rfl⟩ : syracuseStep 1051591 = 1577387) B1577387
theorem B1575899 : Blo 1048611 1575899 := bstep (se 1 (by rfl) ⟨1181924, by rfl⟩ : syracuseStep 1575899 = 2363849) B2363849
theorem B1051611 : Blo 1048611 1051611 := bstep (se 1 (by rfl) ⟨788708, by rfl⟩ : syracuseStep 1051611 = 1577417) B1577417
theorem B1051687 : Blo 1048611 1051687 := bstep (se 1 (by rfl) ⟨788765, by rfl⟩ : syracuseStep 1051687 = 1577531) B1577531
theorem B1051727 : Blo 1048611 1051727 := bstep (se 1 (by rfl) ⟨788795, by rfl⟩ : syracuseStep 1051727 = 1577591) B1577591
theorem B1051743 : Blo 1048611 1051743 := bstep (se 1 (by rfl) ⟨788807, by rfl⟩ : syracuseStep 1051743 = 1577615) B1577615
theorem B1051771 : Blo 1048611 1051771 := bstep (se 1 (by rfl) ⟨788828, by rfl⟩ : syracuseStep 1051771 = 1577657) B1577657
theorem B1051823 : Blo 1048611 1051823 := bstep (se 1 (by rfl) ⟨788867, by rfl⟩ : syracuseStep 1051823 = 1577735) B1577735
theorem B1182919 : Blo 1048611 1182919 := bstep (se 1 (by rfl) ⟨887189, by rfl⟩ : syracuseStep 1182919 = 1774379) B1774379
theorem B1051847 : Blo 1048611 1051847 := bstep (se 1 (by rfl) ⟨788885, by rfl⟩ : syracuseStep 1051847 = 1577771) B1577771
theorem B1051867 : Blo 1048611 1051867 := bstep (se 1 (by rfl) ⟨788900, by rfl⟩ : syracuseStep 1051867 = 1577801) B1577801
theorem B1051943 : Blo 1048611 1051943 := bstep (se 1 (by rfl) ⟨788957, by rfl⟩ : syracuseStep 1051943 = 1577915) B1577915
theorem B1051983 : Blo 1048611 1051983 := bstep (se 1 (by rfl) ⟨788987, by rfl⟩ : syracuseStep 1051983 = 1577975) B1577975
theorem B1051999 : Blo 1048611 1051999 := bstep (se 1 (by rfl) ⟨788999, by rfl⟩ : syracuseStep 1051999 = 1577999) B1577999
theorem B1052027 : Blo 1048611 1052027 := bstep (se 1 (by rfl) ⟨789020, by rfl⟩ : syracuseStep 1052027 = 1578041) B1578041
theorem B1772975 : Blo 1048611 1772975 := bstep (se 1 (by rfl) ⟨1329731, by rfl⟩ : syracuseStep 1772975 = 2659463) B2659463
theorem B1576367 : Blo 1048611 1576367 := bstep (se 1 (by rfl) ⟨1182275, by rfl⟩ : syracuseStep 1576367 = 2364551) B2364551
theorem B1052079 : Blo 1048611 1052079 := bstep (se 1 (by rfl) ⟨789059, by rfl⟩ : syracuseStep 1052079 = 1578119) B1578119
theorem B1052103 : Blo 1048611 1052103 := bstep (se 1 (by rfl) ⟨789077, by rfl⟩ : syracuseStep 1052103 = 1578155) B1578155
theorem B1052123 : Blo 1048611 1052123 := bstep (se 1 (by rfl) ⟨789092, by rfl⟩ : syracuseStep 1052123 = 1578185) B1578185
theorem B1576457 : Blo 1048611 1576457 := bstep (se 2 (by rfl) ⟨591171, by rfl⟩ : syracuseStep 1576457 = 1182343) B1182343
theorem B3542561 : Blo 1048611 3542561 := bstep (se 2 (by rfl) ⟨1328460, by rfl⟩ : syracuseStep 3542561 = 2656921) B2656921
theorem B1576487 : Blo 1048611 1576487 := bstep (se 1 (by rfl) ⟨1182365, by rfl⟩ : syracuseStep 1576487 = 2364731) B2364731
theorem B1052199 : Blo 1048611 1052199 := bstep (se 1 (by rfl) ⟨789149, by rfl⟩ : syracuseStep 1052199 = 1578299) B1578299
theorem B1281575 : Blo 1048611 1281575 := bstep (se 1 (by rfl) ⟨961181, by rfl⟩ : syracuseStep 1281575 = 1922363) B1922363
theorem B1052239 : Blo 1048611 1052239 := bstep (se 1 (by rfl) ⟨789179, by rfl⟩ : syracuseStep 1052239 = 1578359) B1578359
theorem B1052255 : Blo 1048611 1052255 := bstep (se 1 (by rfl) ⟨789191, by rfl⟩ : syracuseStep 1052255 = 1578383) B1578383
theorem B2363003 : Blo 1048611 2363003 := bstep (se 1 (by rfl) ⟨1772252, by rfl⟩ : syracuseStep 2363003 = 3544505) B3544505
theorem B1576571 : Blo 1048611 1576571 := bstep (se 1 (by rfl) ⟨1182428, by rfl⟩ : syracuseStep 1576571 = 2364857) B2364857
theorem B1052283 : Blo 1048611 1052283 := bstep (se 1 (by rfl) ⟨789212, by rfl⟩ : syracuseStep 1052283 = 1578425) B1578425
theorem B1052335 : Blo 1048611 1052335 := bstep (se 1 (by rfl) ⟨789251, by rfl⟩ : syracuseStep 1052335 = 1578503) B1578503
theorem B1052359 : Blo 1048611 1052359 := bstep (se 1 (by rfl) ⟨789269, by rfl⟩ : syracuseStep 1052359 = 1578539) B1578539
theorem B1052379 : Blo 1048611 1052379 := bstep (se 1 (by rfl) ⟨789284, by rfl⟩ : syracuseStep 1052379 = 1578569) B1578569
theorem B3542777 : Blo 1048611 3542777 := bstep (se 2 (by rfl) ⟨1328541, by rfl⟩ : syracuseStep 3542777 = 2657083) B2657083
theorem B2363129 : Blo 1048611 2363129 := bstep (se 2 (by rfl) ⟨886173, by rfl⟩ : syracuseStep 2363129 = 1772347) B1772347
theorem B1576697 : Blo 1048611 1576697 := bstep (se 2 (by rfl) ⟨591261, by rfl⟩ : syracuseStep 1576697 = 1182523) B1182523
theorem B1052455 : Blo 1048611 1052455 := bstep (se 1 (by rfl) ⟨789341, by rfl⟩ : syracuseStep 1052455 = 1578683) B1578683
theorem B5672771 : Blo 1048611 5672771 := bstep (se 1 (by rfl) ⟨4254578, by rfl⟩ : syracuseStep 5672771 = 8509157) B8509157
theorem B1052495 : Blo 1048611 1052495 := bstep (se 1 (by rfl) ⟨789371, by rfl⟩ : syracuseStep 1052495 = 1578743) B1578743
theorem B1773407 : Blo 1048611 1773407 := bstep (se 1 (by rfl) ⟨1330055, by rfl⟩ : syracuseStep 1773407 = 2660111) B2660111
theorem B1576799 : Blo 1048611 1576799 := bstep (se 1 (by rfl) ⟨1182599, by rfl⟩ : syracuseStep 1576799 = 2365199) B2365199
theorem B1052511 : Blo 1048611 1052511 := bstep (se 1 (by rfl) ⟨789383, by rfl⟩ : syracuseStep 1052511 = 1578767) B1578767
theorem B1576811 : Blo 1048611 1576811 := bstep (se 1 (by rfl) ⟨1182608, by rfl⟩ : syracuseStep 1576811 = 2365217) B2365217
theorem B8523629 : Blo 1048611 8523629 := bstep (se 3 (by rfl) ⟨1598180, by rfl⟩ : syracuseStep 8523629 = 3196361) B3196361
theorem B1052539 : Blo 1048611 1052539 := bstep (se 1 (by rfl) ⟨789404, by rfl⟩ : syracuseStep 1052539 = 1578809) B1578809
theorem B1052591 : Blo 1048611 1052591 := bstep (se 1 (by rfl) ⟨789443, by rfl⟩ : syracuseStep 1052591 = 1578887) B1578887
theorem B11964347 : Blo 1048611 11964347 := bstep (se 1 (by rfl) ⟨8973260, by rfl⟩ : syracuseStep 11964347 = 17946521) B17946521
theorem B3543047 : Blo 1048611 3543047 := bstep (se 1 (by rfl) ⟨2657285, by rfl⟩ : syracuseStep 3543047 = 5314571) B5314571
theorem B2363399 : Blo 1048611 2363399 := bstep (se 1 (by rfl) ⟨1772549, by rfl⟩ : syracuseStep 2363399 = 3545099) B3545099
theorem B1183783 : Blo 1048611 1183783 := bstep (se 1 (by rfl) ⟨887837, by rfl⟩ : syracuseStep 1183783 = 1775675) B1775675
theorem B2363471 : Blo 1048611 2363471 := bstep (se 1 (by rfl) ⟨1772603, by rfl⟩ : syracuseStep 2363471 = 3545207) B3545207
theorem B1577039 : Blo 1048611 1577039 := bstep (se 1 (by rfl) ⟨1182779, by rfl⟩ : syracuseStep 1577039 = 2365559) B2365559
theorem B5312627 : Blo 1048611 5312627 := bstep (se 1 (by rfl) ⟨3984470, by rfl⟩ : syracuseStep 5312627 = 7968941) B7968941
theorem B3543155 : Blo 1048611 3543155 := bstep (se 1 (by rfl) ⟨2657366, by rfl⟩ : syracuseStep 3543155 = 5314733) B5314733
theorem B1577159 : Blo 1048611 1577159 := bstep (se 1 (by rfl) ⟨1182869, by rfl⟩ : syracuseStep 1577159 = 2365739) B2365739
theorem B2396521 : Blo 1048611 2396521 := bstep (se 2 (by rfl) ⟨898695, by rfl⟩ : syracuseStep 2396521 = 1797391) B1797391
theorem B1577321 : Blo 1048611 1577321 := bstep (se 2 (by rfl) ⟨591495, by rfl⟩ : syracuseStep 1577321 = 1182991) B1182991
theorem B3543425 : Blo 1048611 3543425 := bstep (se 2 (by rfl) ⟨1328784, by rfl⟩ : syracuseStep 3543425 = 2657569) B2657569
theorem B2658703 : Blo 1048611 2658703 := bstep (se 1 (by rfl) ⟨1994027, by rfl⟩ : syracuseStep 2658703 = 3988055) B3988055
theorem B1773967 : Blo 1048611 1773967 := bstep (se 1 (by rfl) ⟨1330475, by rfl⟩ : syracuseStep 1773967 = 2660951) B2660951
theorem B1577399 : Blo 1048611 1577399 := bstep (se 1 (by rfl) ⟨1183049, by rfl⟩ : syracuseStep 1577399 = 2366099) B2366099
theorem B2363867 : Blo 1048611 2363867 := bstep (se 1 (by rfl) ⟨1772900, by rfl⟩ : syracuseStep 2363867 = 3545801) B3545801
theorem B1577435 : Blo 1048611 1577435 := bstep (se 1 (by rfl) ⟨1183076, by rfl⟩ : syracuseStep 1577435 = 2366153) B2366153
theorem B2691571 : Blo 1048611 2691571 := bstep (se 1 (by rfl) ⟨2018678, by rfl⟩ : syracuseStep 2691571 = 4037357) B4037357
theorem B4264633 : Blo 1048611 4264633 := bstep (se 2 (by rfl) ⟨1599237, by rfl⟩ : syracuseStep 4264633 = 3198475) B3198475
theorem B2659027 : Blo 1048611 2659027 := bstep (se 1 (by rfl) ⟨1994270, by rfl⟩ : syracuseStep 2659027 = 3988541) B3988541
theorem B2364335 : Blo 1048611 2364335 := bstep (se 1 (by rfl) ⟨1773251, by rfl⟩ : syracuseStep 2364335 = 3546503) B3546503
theorem B1577903 : Blo 1048611 1577903 := bstep (se 1 (by rfl) ⟨1183427, by rfl⟩ : syracuseStep 1577903 = 2366855) B2366855
theorem B1577993 : Blo 1048611 1577993 := bstep (se 2 (by rfl) ⟨591747, by rfl⟩ : syracuseStep 1577993 = 1183495) B1183495
theorem B1578023 : Blo 1048611 1578023 := bstep (se 1 (by rfl) ⟨1183517, by rfl⟩ : syracuseStep 1578023 = 2367035) B2367035
theorem B1774649 : Blo 1048611 1774649 := bstep (se 2 (by rfl) ⟨665493, by rfl⟩ : syracuseStep 1774649 = 1330987) B1330987
theorem B3839057 : Blo 1048611 3839057 := bstep (se 2 (by rfl) ⟨1439646, by rfl⟩ : syracuseStep 3839057 = 2879293) B2879293
theorem B1578107 : Blo 1048611 1578107 := bstep (se 1 (by rfl) ⟨1183580, by rfl⟩ : syracuseStep 1578107 = 2367161) B2367161
theorem B3544235 : Blo 1048611 3544235 := bstep (se 1 (by rfl) ⟨2658176, by rfl⟩ : syracuseStep 3544235 = 5316353) B5316353
theorem B2364587 : Blo 1048611 2364587 := bstep (se 1 (by rfl) ⟨1773440, by rfl⟩ : syracuseStep 2364587 = 3546881) B3546881
theorem B13473013 : Blo 1048611 13473013 := bstep (se 5 (by rfl) ⟨631547, by rfl⟩ : syracuseStep 13473013 = 1263095) B1263095
theorem B1578233 : Blo 1048611 1578233 := bstep (se 2 (by rfl) ⟨591837, by rfl⟩ : syracuseStep 1578233 = 1183675) B1183675
theorem B1578335 : Blo 1048611 1578335 := bstep (se 1 (by rfl) ⟨1183751, by rfl⟩ : syracuseStep 1578335 = 2367503) B2367503
theorem B1578347 : Blo 1048611 1578347 := bstep (se 1 (by rfl) ⟨1183760, by rfl⟩ : syracuseStep 1578347 = 2367521) B2367521
theorem B3413377 : Blo 1048611 3413377 := bstep (se 2 (by rfl) ⟨1280016, by rfl⟩ : syracuseStep 3413377 = 2560033) B2560033
theorem B14358059 : Blo 1048611 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B1578575 : Blo 1048611 1578575 := bstep (se 1 (by rfl) ⟨1183931, by rfl⟩ : syracuseStep 1578575 = 2367863) B2367863
theorem B13473377 : Blo 1048611 13473377 := bstep (se 2 (by rfl) ⟨5052516, by rfl⟩ : syracuseStep 13473377 = 10105033) B10105033
theorem B2659979 : Blo 1048611 2659979 := bstep (se 1 (by rfl) ⟨1994984, by rfl⟩ : syracuseStep 2659979 = 3989969) B3989969
theorem B7968455 : Blo 1048611 7968455 := bstep (se 1 (by rfl) ⟨5976341, by rfl⟩ : syracuseStep 7968455 = 11952683) B11952683
theorem B5314247 : Blo 1048611 5314247 := bstep (se 1 (by rfl) ⟨3985685, by rfl⟩ : syracuseStep 5314247 = 7971371) B7971371
theorem B3544775 : Blo 1048611 3544775 := bstep (se 1 (by rfl) ⟨2658581, by rfl⟩ : syracuseStep 3544775 = 5317163) B5317163
theorem B2365127 : Blo 1048611 2365127 := bstep (se 1 (by rfl) ⟨1773845, by rfl⟩ : syracuseStep 2365127 = 3547691) B3547691
theorem B1578695 : Blo 1048611 1578695 := bstep (se 1 (by rfl) ⟨1184021, by rfl⟩ : syracuseStep 1578695 = 2368043) B2368043
theorem B1775351 : Blo 1048611 1775351 := bstep (se 1 (by rfl) ⟨1331513, by rfl⟩ : syracuseStep 1775351 = 2663027) B2663027
theorem B4265801 : Blo 1048611 4265801 := bstep (se 2 (by rfl) ⟨1599675, by rfl⟩ : syracuseStep 4265801 = 3199351) B3199351
theorem B1578857 : Blo 1048611 1578857 := bstep (se 2 (by rfl) ⟨592071, by rfl⟩ : syracuseStep 1578857 = 1184143) B1184143
theorem B1775695 : Blo 1048611 1775695 := bstep (se 1 (by rfl) ⟨1331771, by rfl⟩ : syracuseStep 1775695 = 2663543) B2663543
theorem B1775945 : Blo 1048611 1775945 := bstep (se 2 (by rfl) ⟨665979, by rfl⟩ : syracuseStep 1775945 = 1331959) B1331959
theorem B3545639 : Blo 1048611 3545639 := bstep (se 1 (by rfl) ⟨2659229, by rfl⟩ : syracuseStep 3545639 = 5318459) B5318459
theorem B2365991 : Blo 1048611 2365991 := bstep (se 1 (by rfl) ⟨1774493, by rfl⟩ : syracuseStep 2365991 = 3548987) B3548987
theorem B13474349 : Blo 1048611 13474349 := bstep (se 3 (by rfl) ⟨2526440, by rfl⟩ : syracuseStep 13474349 = 5052881) B5052881
theorem B3545747 : Blo 1048611 3545747 := bstep (se 1 (by rfl) ⟨2659310, by rfl⟩ : syracuseStep 3545747 = 5318621) B5318621
theorem B27695801 : Blo 1048611 27695801 := bstep (se 2 (by rfl) ⟨10385925, by rfl⟩ : syracuseStep 27695801 = 20771851) B20771851
theorem B4266695 : Blo 1048611 4266695 := bstep (se 1 (by rfl) ⟨3200021, by rfl⟩ : syracuseStep 4266695 = 6400043) B6400043
theorem B8985289 : Blo 1048611 8985289 := bstep (se 2 (by rfl) ⟨3369483, by rfl⟩ : syracuseStep 8985289 = 6738967) B6738967
theorem B2661113 : Blo 1048611 2661113 := bstep (se 2 (by rfl) ⟨997917, by rfl⟩ : syracuseStep 2661113 = 1995835) B1995835
theorem B3545963 : Blo 1048611 3545963 := bstep (se 1 (by rfl) ⟨2659472, by rfl⟩ : syracuseStep 3545963 = 5318945) B5318945
theorem B2366315 : Blo 1048611 2366315 := bstep (se 1 (by rfl) ⟨1774736, by rfl⟩ : syracuseStep 2366315 = 3549473) B3549473
theorem B3546017 : Blo 1048611 3546017 := bstep (se 2 (by rfl) ⟨1329756, by rfl⟩ : syracuseStep 3546017 = 2659513) B2659513
theorem B2366369 : Blo 1048611 2366369 := bstep (se 2 (by rfl) ⟨887388, by rfl⟩ : syracuseStep 2366369 = 1774777) B1774777
theorem B2661295 : Blo 1048611 2661295 := bstep (se 1 (by rfl) ⟨1995971, by rfl⟩ : syracuseStep 2661295 = 3991943) B3991943
theorem B1121359 : Blo 1048611 1121359 := bstep (se 1 (by rfl) ⟨841019, by rfl⟩ : syracuseStep 1121359 = 1682039) B1682039
theorem B2366711 : Blo 1048611 2366711 := bstep (se 1 (by rfl) ⟨1775033, by rfl⟩ : syracuseStep 2366711 = 3550067) B3550067
theorem B2661761 : Blo 1048611 2661761 := bstep (se 2 (by rfl) ⟨998160, by rfl⟩ : syracuseStep 2661761 = 1996321) B1996321
theorem B3546611 : Blo 1048611 3546611 := bstep (se 1 (by rfl) ⟨2659958, by rfl⟩ : syracuseStep 3546611 = 5319917) B5319917
theorem B6725207 : Blo 1048611 6725207 := bstep (se 1 (by rfl) ⟨5043905, by rfl⟩ : syracuseStep 6725207 = 10087811) B10087811
theorem B2662217 : Blo 1048611 2662217 := bstep (se 2 (by rfl) ⟨998331, by rfl⟩ : syracuseStep 2662217 = 1996663) B1996663
theorem B2367305 : Blo 1048611 2367305 := bstep (se 2 (by rfl) ⟨887739, by rfl⟩ : syracuseStep 2367305 = 1775479) B1775479
theorem B4857695 : Blo 1048611 4857695 := bstep (se 1 (by rfl) ⟨3643271, by rfl⟩ : syracuseStep 4857695 = 7286543) B7286543
theorem B3547151 : Blo 1048611 3547151 := bstep (se 1 (by rfl) ⟨2660363, by rfl⟩ : syracuseStep 3547151 = 5320727) B5320727
theorem B1122427 : Blo 1048611 1122427 := bstep (se 1 (by rfl) ⟨841820, by rfl⟩ : syracuseStep 1122427 = 1683641) B1683641
theorem B2662571 : Blo 1048611 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B5054825 : Blo 1048611 5054825 := bstep (se 2 (by rfl) ⟨1895559, by rfl⟩ : syracuseStep 5054825 = 3791119) B3791119
theorem B19178009 : Blo 1048611 19178009 := bstep (se 2 (by rfl) ⟨7191753, by rfl⟩ : syracuseStep 19178009 = 14383507) B14383507
theorem B3547745 : Blo 1048611 3547745 := bstep (se 2 (by rfl) ⟨1330404, by rfl⟩ : syracuseStep 3547745 = 2660809) B2660809
theorem B2368097 : Blo 1048611 2368097 := bstep (se 2 (by rfl) ⟨888036, by rfl⟩ : syracuseStep 2368097 = 1776073) B1776073
theorem B2990803 : Blo 1048611 2990803 := bstep (se 1 (by rfl) ⟨2243102, by rfl⟩ : syracuseStep 2990803 = 4486205) B4486205
theorem B1123247 : Blo 1048611 1123247 := bstep (se 1 (by rfl) ⟨842435, by rfl⟩ : syracuseStep 1123247 = 1684871) B1684871
theorem B2663351 : Blo 1048611 2663351 := bstep (se 1 (by rfl) ⟨1997513, by rfl⟩ : syracuseStep 2663351 = 3995027) B3995027
theorem B6398995 : Blo 1048611 6398995 := bstep (se 1 (by rfl) ⟨4799246, by rfl⟩ : syracuseStep 6398995 = 9598493) B9598493
theorem B1123879 : Blo 1048611 1123879 := bstep (se 1 (by rfl) ⟨842909, by rfl⟩ : syracuseStep 1123879 = 1685819) B1685819
theorem B2664353 : Blo 1048611 2664353 := bstep (se 2 (by rfl) ⟨999132, by rfl⟩ : syracuseStep 2664353 = 1998265) B1998265
theorem B15542279 : Blo 1048611 15542279 := bstep (se 1 (by rfl) ⟨11656709, by rfl⟩ : syracuseStep 15542279 = 23313419) B23313419
theorem B2992135 : Blo 1048611 2992135 := bstep (se 1 (by rfl) ⟨2244101, by rfl⟩ : syracuseStep 2992135 = 4488203) B4488203
theorem B3549203 : Blo 1048611 3549203 := bstep (se 1 (by rfl) ⟨2661902, by rfl⟩ : syracuseStep 3549203 = 5323805) B5323805
theorem B7579955 : Blo 1048611 7579955 := bstep (se 1 (by rfl) ⟨5684966, by rfl⟩ : syracuseStep 7579955 = 11369933) B11369933
theorem B3549527 : Blo 1048611 3549527 := bstep (se 1 (by rfl) ⟨2662145, by rfl⟩ : syracuseStep 3549527 = 5324291) B5324291
theorem B1681769 : Blo 1048611 1681769 := bstep (se 2 (by rfl) ⟨630663, by rfl⟩ : syracuseStep 1681769 = 1261327) B1261327
theorem B1419815 : Blo 1048611 1419815 := bstep (se 1 (by rfl) ⟨1064861, by rfl⟩ : syracuseStep 1419815 = 2129723) B2129723
theorem B7187429 : Blo 1048611 7187429 := bstep (se 4 (by rfl) ⟨673821, by rfl⟩ : syracuseStep 7187429 = 1347643) B1347643
theorem B1682603 : Blo 1048611 1682603 := bstep (se 1 (by rfl) ⟨1261952, by rfl⟩ : syracuseStep 1682603 = 2523905) B2523905
theorem B2993537 : Blo 1048611 2993537 := bstep (se 2 (by rfl) ⟨1122576, by rfl⟩ : syracuseStep 2993537 = 2245153) B2245153
theorem B7974287 : Blo 1048611 7974287 := bstep (se 1 (by rfl) ⟨5980715, by rfl⟩ : syracuseStep 7974287 = 11961431) B11961431
theorem B5320079 : Blo 1048611 5320079 := bstep (se 1 (by rfl) ⟨3990059, by rfl⟩ : syracuseStep 5320079 = 7980119) B7980119
theorem B3550607 : Blo 1048611 3550607 := bstep (se 1 (by rfl) ⟨2662955, by rfl⟩ : syracuseStep 3550607 = 5325911) B5325911
theorem B11677171 : Blo 1048611 11677171 := bstep (se 1 (by rfl) ⟨8757878, by rfl⟩ : syracuseStep 11677171 = 17515757) B17515757
theorem B3550931 : Blo 1048611 3550931 := bstep (se 1 (by rfl) ⟨2663198, by rfl⟩ : syracuseStep 3550931 = 5326397) B5326397
theorem B2993993 : Blo 1048611 2993993 := bstep (se 2 (by rfl) ⟨1122747, by rfl⟩ : syracuseStep 2993993 = 2245495) B2245495
theorem B19181447 : Blo 1048611 19181447 := bstep (se 1 (by rfl) ⟨14386085, by rfl⟩ : syracuseStep 19181447 = 28772171) B28772171
theorem B2240531 : Blo 1048611 2240531 := bstep (se 1 (by rfl) ⟨1680398, by rfl⟩ : syracuseStep 2240531 = 3360797) B3360797
theorem B43135091 : Blo 1048611 43135091 := bstep (se 1 (by rfl) ⟨32351318, by rfl⟩ : syracuseStep 43135091 = 64702637) B64702637
theorem B2241121 : Blo 1048611 2241121 := bstep (se 2 (by rfl) ⟨840420, by rfl⟩ : syracuseStep 2241121 = 1680841) B1680841
theorem B2995051 : Blo 1048611 2995051 := bstep (se 1 (by rfl) ⟨2246288, by rfl⟩ : syracuseStep 2995051 = 4492577) B4492577
theorem B3552119 : Blo 1048611 3552119 := bstep (se 1 (by rfl) ⟨2664089, by rfl⟩ : syracuseStep 3552119 = 5328179) B5328179
theorem B3781559 : Blo 1048611 3781559 := bstep (se 1 (by rfl) ⟨2836169, by rfl⟩ : syracuseStep 3781559 = 5672339) B5672339
theorem B3552335 : Blo 1048611 3552335 := bstep (se 1 (by rfl) ⟨2664251, by rfl⟩ : syracuseStep 3552335 = 5328503) B5328503
theorem B52573541 : Blo 1048611 52573541 := bstep (se 4 (by rfl) ⟨4928769, by rfl⟩ : syracuseStep 52573541 = 9857539) B9857539
theorem B5322185 : Blo 1048611 5322185 := bstep (se 2 (by rfl) ⟨1995819, by rfl⟩ : syracuseStep 5322185 = 3991639) B3991639
theorem B2242171 : Blo 1048611 2242171 := bstep (se 1 (by rfl) ⟨1681628, by rfl⟩ : syracuseStep 2242171 = 3363257) B3363257
theorem B8960003 : Blo 1048611 8960003 := bstep (se 1 (by rfl) ⟨6720002, by rfl⟩ : syracuseStep 8960003 = 13440005) B13440005
theorem B12793859 : Blo 1048611 12793859 := bstep (se 1 (by rfl) ⟨9595394, by rfl⟩ : syracuseStep 12793859 = 19190789) B19190789
theorem B3782713 : Blo 1048611 3782713 := bstep (se 2 (by rfl) ⟨1418517, by rfl⟩ : syracuseStep 3782713 = 2837035) B2837035
theorem B2996281 : Blo 1048611 2996281 := bstep (se 2 (by rfl) ⟨1123605, by rfl⟩ : syracuseStep 2996281 = 2247211) B2247211
theorem B5322833 : Blo 1048611 5322833 := bstep (se 2 (by rfl) ⟨1996062, by rfl⟩ : syracuseStep 5322833 = 3992125) B3992125
theorem B3782771 : Blo 1048611 3782771 := bstep (se 1 (by rfl) ⟨2837078, by rfl⟩ : syracuseStep 3782771 = 5674157) B5674157
theorem B1685627 : Blo 1048611 1685627 := bstep (se 1 (by rfl) ⟨1264220, by rfl⟩ : syracuseStep 1685627 = 2528441) B2528441
theorem B1063207 : Blo 1048611 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B1685947 : Blo 1048611 1685947 := bstep (se 1 (by rfl) ⟨1264460, by rfl⟩ : syracuseStep 1685947 = 2528921) B2528921
theorem B21052853 : Blo 1048611 21052853 := bstep (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) B1973705
theorem B2244307 : Blo 1048611 2244307 := bstep (se 1 (by rfl) ⟨1683230, by rfl⟩ : syracuseStep 2244307 = 3366461) B3366461
theorem B2834603 : Blo 1048611 2834603 := bstep (se 1 (by rfl) ⟨2125952, by rfl⟩ : syracuseStep 2834603 = 4251905) B4251905
theorem B17023243 : Blo 1048611 17023243 := bstep (se 1 (by rfl) ⟨12767432, by rfl⟩ : syracuseStep 17023243 = 25534865) B25534865
theorem B24264971 : Blo 1048611 24264971 := bstep (se 1 (by rfl) ⟨18198728, by rfl⟩ : syracuseStep 24264971 = 36397457) B36397457
theorem B3785249 : Blo 1048611 3785249 := bstep (se 2 (by rfl) ⟨1419468, by rfl⟩ : syracuseStep 3785249 = 2838937) B2838937
theorem B9585211 : Blo 1048611 9585211 := bstep (se 1 (by rfl) ⟨7188908, by rfl⟩ : syracuseStep 9585211 = 14377817) B14377817
theorem B2245639 : Blo 1048611 2245639 := bstep (se 1 (by rfl) ⟨1684229, by rfl⟩ : syracuseStep 2245639 = 3368459) B3368459
theorem B1328167 : Blo 1048611 1328167 := bstep (se 1 (by rfl) ⟨996125, by rfl⟩ : syracuseStep 1328167 = 1992251) B1992251
theorem B3982679 : Blo 1048611 3982679 := bstep (se 1 (by rfl) ⟨2987009, by rfl⟩ : syracuseStep 3982679 = 5974019) B5974019
theorem B1328491 : Blo 1048611 1328491 := bstep (se 1 (by rfl) ⟨996368, by rfl⟩ : syracuseStep 1328491 = 1992737) B1992737
theorem B3360143 : Blo 1048611 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B3786203 : Blo 1048611 3786203 := bstep (se 1 (by rfl) ⟨2839652, by rfl⟩ : syracuseStep 3786203 = 5679305) B5679305
theorem B7980605 : Blo 1048611 7980605 := bstep (se 3 (by rfl) ⟨1496363, by rfl⟩ : syracuseStep 7980605 = 2992727) B2992727
theorem B1328719 : Blo 1048611 1328719 := bstep (se 1 (by rfl) ⟨996539, by rfl⟩ : syracuseStep 1328719 = 1993079) B1993079
theorem B7981577 : Blo 1048611 7981577 := bstep (se 2 (by rfl) ⟨2993091, by rfl⟩ : syracuseStep 7981577 = 5986183) B5986183
theorem B5327369 : Blo 1048611 5327369 := bstep (se 2 (by rfl) ⟨1997763, by rfl⟩ : syracuseStep 5327369 = 3995527) B3995527
theorem B1329787 : Blo 1048611 1329787 := bstep (se 1 (by rfl) ⟨997340, by rfl⟩ : syracuseStep 1329787 = 1994681) B1994681
theorem B1330015 : Blo 1048611 1330015 := bstep (se 1 (by rfl) ⟨997511, by rfl⟩ : syracuseStep 1330015 = 1995023) B1995023
theorem B1330607 : Blo 1048611 1330607 := bstep (se 1 (by rfl) ⟨997955, by rfl⟩ : syracuseStep 1330607 = 1995911) B1995911
theorem B8081117 : Blo 1048611 8081117 := bstep (se 3 (by rfl) ⟨1515209, by rfl⟩ : syracuseStep 8081117 = 3030419) B3030419
theorem B3591965 : Blo 1048611 3591965 := bstep (se 3 (by rfl) ⟨673493, by rfl⟩ : syracuseStep 3591965 = 1346987) B1346987
theorem B5689207 : Blo 1048611 5689207 := bstep (se 1 (by rfl) ⟨4266905, by rfl⟩ : syracuseStep 5689207 = 8533811) B8533811
theorem B7983035 : Blo 1048611 7983035 := bstep (se 1 (by rfl) ⟨5987276, by rfl⟩ : syracuseStep 7983035 = 11974553) B11974553
theorem B5328827 : Blo 1048611 5328827 := bstep (se 1 (by rfl) ⟨3996620, by rfl⟩ : syracuseStep 5328827 = 7993241) B7993241
theorem B17256509 : Blo 1048611 17256509 := bstep (se 3 (by rfl) ⟨3235595, by rfl⟩ : syracuseStep 17256509 = 6471191) B6471191
theorem B3985793 : Blo 1048611 3985793 := bstep (se 2 (by rfl) ⟨1494672, by rfl⟩ : syracuseStep 3985793 = 2989345) B2989345
theorem B3985807 : Blo 1048611 3985807 := bstep (se 1 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 3985807 = 5978711) B5978711
theorem B6738329 : Blo 1048611 6738329 := bstep (se 2 (by rfl) ⟨2526873, by rfl⟩ : syracuseStep 6738329 = 5053747) B5053747
theorem B3068513 : Blo 1048611 3068513 := bstep (se 2 (by rfl) ⟨1150692, by rfl⟩ : syracuseStep 3068513 = 2301385) B2301385
theorem B3232379 : Blo 1048611 3232379 := bstep (se 1 (by rfl) ⟨2424284, by rfl⟩ : syracuseStep 3232379 = 4848569) B4848569
theorem B1495675 : Blo 1048611 1495675 := bstep (se 1 (by rfl) ⟨1121756, by rfl⟩ : syracuseStep 1495675 = 2243513) B2243513
theorem B27316997 : Blo 1048611 27316997 := bstep (se 4 (by rfl) ⟨2560968, by rfl⟩ : syracuseStep 27316997 = 5121937) B5121937
theorem B1495903 : Blo 1048611 1495903 := bstep (se 1 (by rfl) ⟨1121927, by rfl⟩ : syracuseStep 1495903 = 2243855) B2243855
theorem B11981843 : Blo 1048611 11981843 := bstep (se 1 (by rfl) ⟨8986382, by rfl⟩ : syracuseStep 11981843 = 17972765) B17972765
theorem B1594567 : Blo 1048611 1594567 := bstep (se 1 (by rfl) ⟨1195925, by rfl⟩ : syracuseStep 1594567 = 2391851) B2391851
theorem B1496495 : Blo 1048611 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B3364487 : Blo 1048611 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B3987083 : Blo 1048611 3987083 := bstep (se 1 (by rfl) ⟨2990312, by rfl⟩ : syracuseStep 3987083 = 5980625) B5980625
theorem B11949767 : Blo 1048611 11949767 := bstep (se 1 (by rfl) ⟨8962325, by rfl⟩ : syracuseStep 11949767 = 17924651) B17924651
theorem B17028953 : Blo 1048611 17028953 := bstep (se 2 (by rfl) ⟨6385857, by rfl⟩ : syracuseStep 17028953 = 12771715) B12771715
theorem B64739573 : Blo 1048611 64739573 := bstep (se 5 (by rfl) ⟨3034667, by rfl⟩ : syracuseStep 64739573 = 6069335) B6069335
theorem B3791233 : Blo 1048611 3791233 := bstep (se 2 (by rfl) ⟨1421712, by rfl⟩ : syracuseStep 3791233 = 2843425) B2843425
theorem B3791393 : Blo 1048611 3791393 := bstep (se 2 (by rfl) ⟨1421772, by rfl⟩ : syracuseStep 3791393 = 2843545) B2843545
theorem B1497799 : Blo 1048611 1497799 := bstep (se 1 (by rfl) ⟨1123349, by rfl⟩ : syracuseStep 1497799 = 2246699) B2246699
theorem B7559891 : Blo 1048611 7559891 := bstep (se 1 (by rfl) ⟨5669918, by rfl⟩ : syracuseStep 7559891 = 11339837) B11339837
theorem B13458251 : Blo 1048611 13458251 := bstep (se 1 (by rfl) ⟨10093688, by rfl⟩ : syracuseStep 13458251 = 20187377) B20187377
theorem B3694139 : Blo 1048611 3694139 := bstep (se 1 (by rfl) ⟨2770604, by rfl⟩ : syracuseStep 3694139 = 5541209) B5541209
theorem B11984759 : Blo 1048611 11984759 := bstep (se 1 (by rfl) ⟨8988569, by rfl⟩ : syracuseStep 11984759 = 17977139) B17977139
theorem B1892279 : Blo 1048611 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B18473285 : Blo 1048611 18473285 := bstep (se 4 (by rfl) ⟨1731870, by rfl⟩ : syracuseStep 18473285 = 3463741) B3463741
theorem B4546945 : Blo 1048611 4546945 := bstep (se 2 (by rfl) ⟨1705104, by rfl⟩ : syracuseStep 4546945 = 3410209) B3410209
theorem B1139279 : Blo 1048611 1139279 := bstep (se 1 (by rfl) ⟨854459, by rfl⟩ : syracuseStep 1139279 = 1708919) B1708919
theorem B1991567 : Blo 1048611 1991567 := bstep (se 1 (by rfl) ⟨1493675, by rfl⟩ : syracuseStep 1991567 = 2987351) B2987351
theorem B3990455 : Blo 1048611 3990455 := bstep (se 1 (by rfl) ⟨2992841, by rfl⟩ : syracuseStep 3990455 = 5985683) B5985683
theorem B1991719 : Blo 1048611 1991719 := bstep (se 1 (by rfl) ⟨1493789, by rfl⟩ : syracuseStep 1991719 = 2987579) B2987579
theorem B17065025 : Blo 1048611 17065025 := bstep (se 2 (by rfl) ⟨6399384, by rfl⟩ : syracuseStep 17065025 = 12798769) B12798769
theorem B1991803 : Blo 1048611 1991803 := bstep (se 1 (by rfl) ⟨1493852, by rfl⟩ : syracuseStep 1991803 = 2987705) B2987705
theorem B6382745 : Blo 1048611 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B1992289 : Blo 1048611 1992289 := bstep (se 2 (by rfl) ⟨747108, by rfl⟩ : syracuseStep 1992289 = 1494217) B1494217
theorem B3991457 : Blo 1048611 3991457 := bstep (se 2 (by rfl) ⟨1496796, by rfl⟩ : syracuseStep 3991457 = 2993593) B2993593
theorem B19949699 : Blo 1048611 19949699 := bstep (se 1 (by rfl) ⟨14962274, by rfl⟩ : syracuseStep 19949699 = 29924549) B29924549
theorem B5990557 : Blo 1048611 5990557 := bstep (se 3 (by rfl) ⟨1123229, by rfl⟩ : syracuseStep 5990557 = 2246459) B2246459
theorem B3991913 : Blo 1048611 3991913 := bstep (se 2 (by rfl) ⟨1496967, by rfl⟩ : syracuseStep 3991913 = 2993935) B2993935
theorem B1993223 : Blo 1048611 1993223 := bstep (se 1 (by rfl) ⟨1494917, by rfl⟩ : syracuseStep 1993223 = 2989835) B2989835
theorem B4483795 : Blo 1048611 4483795 := bstep (se 1 (by rfl) ⟨3362846, by rfl⟩ : syracuseStep 4483795 = 6725693) B6725693
theorem B3992429 : Blo 1048611 3992429 := bstep (se 3 (by rfl) ⟨748580, by rfl⟩ : syracuseStep 3992429 = 1497161) B1497161
theorem B6810551 : Blo 1048611 6810551 := bstep (se 1 (by rfl) ⟨5107913, by rfl⟩ : syracuseStep 6810551 = 10215827) B10215827
theorem B1993747 : Blo 1048611 1993747 := bstep (se 1 (by rfl) ⟨1495310, by rfl⟩ : syracuseStep 1993747 = 2990621) B2990621
theorem B3370099 : Blo 1048611 3370099 := bstep (se 1 (by rfl) ⟨2527574, by rfl⟩ : syracuseStep 3370099 = 5055149) B5055149
theorem B11955599 : Blo 1048611 11955599 := bstep (se 1 (by rfl) ⟨8966699, by rfl⟩ : syracuseStep 11955599 = 17933399) B17933399
theorem B1437193 : Blo 1048611 1437193 := bstep (se 2 (by rfl) ⟨538947, by rfl⟩ : syracuseStep 1437193 = 1077895) B1077895
theorem B3993097 : Blo 1048611 3993097 := bstep (se 2 (by rfl) ⟨1497411, by rfl⟩ : syracuseStep 3993097 = 2994823) B2994823
theorem B7663243 : Blo 1048611 7663243 := bstep (se 1 (by rfl) ⟨5747432, by rfl⟩ : syracuseStep 7663243 = 11494865) B11494865
theorem B4255421 : Blo 1048611 4255421 := bstep (se 3 (by rfl) ⟨797891, by rfl⟩ : syracuseStep 4255421 = 1595783) B1595783
theorem B19165091 : Blo 1048611 19165091 := bstep (se 1 (by rfl) ⟨14373818, by rfl⟩ : syracuseStep 19165091 = 28747637) B28747637
theorem B4485127 : Blo 1048611 4485127 := bstep (se 1 (by rfl) ⟨3363845, by rfl⟩ : syracuseStep 4485127 = 6727691) B6727691
theorem B3600463 : Blo 1048611 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B3371483 : Blo 1048611 3371483 := bstep (se 1 (by rfl) ⟨2528612, by rfl⟩ : syracuseStep 3371483 = 5057225) B5057225
theorem B2519675 : Blo 1048611 2519675 := bstep (se 1 (by rfl) ⟨1889756, by rfl⟩ : syracuseStep 2519675 = 3779513) B3779513
theorem B2519801 : Blo 1048611 2519801 := bstep (se 2 (by rfl) ⟨944925, by rfl⟩ : syracuseStep 2519801 = 1889851) B1889851
theorem B51082001 : Blo 1048611 51082001 := bstep (se 2 (by rfl) ⟨19155750, by rfl⟩ : syracuseStep 51082001 = 38311501) B38311501
theorem B3994555 : Blo 1048611 3994555 := bstep (se 1 (by rfl) ⟨2995916, by rfl⟩ : syracuseStep 3994555 = 5991833) B5991833
theorem B5993473 : Blo 1048611 5993473 := bstep (se 2 (by rfl) ⟨2247552, by rfl⟩ : syracuseStep 5993473 = 4495105) B4495105
theorem B3372047 : Blo 1048611 3372047 := bstep (se 1 (by rfl) ⟨2529035, by rfl⟩ : syracuseStep 3372047 = 5058071) B5058071
theorem B40989847 : Blo 1048611 40989847 := bstep (se 1 (by rfl) ⟨30742385, by rfl⟩ : syracuseStep 40989847 = 61484771) B61484771
theorem B1996139 : Blo 1048611 1996139 := bstep (se 1 (by rfl) ⟨1497104, by rfl⟩ : syracuseStep 1996139 = 2994209) B2994209
theorem B2127379 : Blo 1048611 2127379 := bstep (se 1 (by rfl) ⟨1595534, by rfl⟩ : syracuseStep 2127379 = 3191069) B3191069
theorem B3995345 : Blo 1048611 3995345 := bstep (se 2 (by rfl) ⟨1498254, by rfl⟩ : syracuseStep 3995345 = 2996509) B2996509
theorem B30275531 : Blo 1048611 30275531 := bstep (se 1 (by rfl) ⟨22706648, by rfl⟩ : syracuseStep 30275531 = 45413297) B45413297
theorem B1996807 : Blo 1048611 1996807 := bstep (se 1 (by rfl) ⟨1497605, by rfl⟩ : syracuseStep 1996807 = 2995211) B2995211
theorem B3995801 : Blo 1048611 3995801 := bstep (se 2 (by rfl) ⟨1498425, by rfl⟩ : syracuseStep 3995801 = 2996851) B2996851
theorem B8976541 : Blo 1048611 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B7666073 : Blo 1048611 7666073 := bstep (se 2 (by rfl) ⟨2874777, by rfl⟩ : syracuseStep 7666073 = 5749555) B5749555
theorem B1997369 : Blo 1048611 1997369 := bstep (se 2 (by rfl) ⟨749013, by rfl⟩ : syracuseStep 1997369 = 1498027) B1498027
theorem B2128783 : Blo 1048611 2128783 := bstep (se 1 (by rfl) ⟨1596587, by rfl⟩ : syracuseStep 2128783 = 3193175) B3193175
theorem B4488119 : Blo 1048611 4488119 := bstep (se 1 (by rfl) ⟨3366089, by rfl⟩ : syracuseStep 4488119 = 6732179) B6732179
theorem B24214909 : Blo 1048611 24214909 := bstep (se 3 (by rfl) ⟨4540295, by rfl⟩ : syracuseStep 24214909 = 9080591) B9080591
theorem B1080911 : Blo 1048611 1080911 := bstep (se 1 (by rfl) ⟨810683, by rfl⟩ : syracuseStep 1080911 = 1621367) B1621367
theorem B3407483 : Blo 1048611 3407483 := bstep (se 1 (by rfl) ⟨2555612, by rfl⟩ : syracuseStep 3407483 = 5111225) B5111225
theorem B2129657 : Blo 1048611 2129657 := bstep (se 2 (by rfl) ⟨798621, by rfl⟩ : syracuseStep 2129657 = 1597243) B1597243
theorem B1704041 : Blo 1048611 1704041 := bstep (se 2 (by rfl) ⟨639015, by rfl⟩ : syracuseStep 1704041 = 1278031) B1278031
theorem B1048863 : Blo 1048611 1048863 := bstep (se 1 (by rfl) ⟨786647, by rfl⟩ : syracuseStep 1048863 = 1573295) B1573295
theorem B1573211 : Blo 1048611 1573211 := bstep (se 1 (by rfl) ⟨1179908, by rfl⟩ : syracuseStep 1573211 = 2359817) B2359817
theorem B1048923 : Blo 1048611 1048923 := bstep (se 1 (by rfl) ⟨786692, by rfl⟩ : syracuseStep 1048923 = 1573385) B1573385
theorem B1048943 : Blo 1048611 1048943 := bstep (se 1 (by rfl) ⟨786707, by rfl⟩ : syracuseStep 1048943 = 1573415) B1573415
theorem B1048999 : Blo 1048611 1048999 := bstep (se 1 (by rfl) ⟨786749, by rfl⟩ : syracuseStep 1048999 = 1573499) B1573499
theorem B3539375 : Blo 1048611 3539375 := bstep (se 1 (by rfl) ⟨2654531, by rfl⟩ : syracuseStep 3539375 = 5309063) B5309063
theorem B2359727 : Blo 1048611 2359727 := bstep (se 1 (by rfl) ⟨1769795, by rfl⟩ : syracuseStep 2359727 = 3539591) B3539591
theorem B2359763 : Blo 1048611 2359763 := bstep (se 1 (by rfl) ⟨1769822, by rfl⟩ : syracuseStep 2359763 = 3539645) B3539645
theorem B1049083 : Blo 1048611 1049083 := bstep (se 1 (by rfl) ⟨786812, by rfl⟩ : syracuseStep 1049083 = 1573625) B1573625
theorem B2359871 : Blo 1048611 2359871 := bstep (se 1 (by rfl) ⟨1769903, by rfl⟩ : syracuseStep 2359871 = 3539807) B3539807
theorem B1573439 : Blo 1048611 1573439 := bstep (se 1 (by rfl) ⟨1180079, by rfl⟩ : syracuseStep 1573439 = 2360159) B2360159
theorem B1049151 : Blo 1048611 1049151 := bstep (se 1 (by rfl) ⟨786863, by rfl⟩ : syracuseStep 1049151 = 1573727) B1573727
theorem B1049159 : Blo 1048611 1049159 := bstep (se 1 (by rfl) ⟨786869, by rfl⟩ : syracuseStep 1049159 = 1573739) B1573739
theorem B1180255 : Blo 1048611 1180255 := bstep (se 1 (by rfl) ⟨885191, by rfl⟩ : syracuseStep 1180255 = 1770383) B1770383
theorem B2359979 : Blo 1048611 2359979 := bstep (se 1 (by rfl) ⟨1769984, by rfl⟩ : syracuseStep 2359979 = 3539969) B3539969
theorem B1770167 : Blo 1048611 1770167 := bstep (se 1 (by rfl) ⟨1327625, by rfl⟩ : syracuseStep 1770167 = 2655251) B2655251
theorem B1573559 : Blo 1048611 1573559 := bstep (se 1 (by rfl) ⟨1180169, by rfl⟩ : syracuseStep 1573559 = 2360339) B2360339
theorem B1049311 : Blo 1048611 1049311 := bstep (se 1 (by rfl) ⟨786983, by rfl⟩ : syracuseStep 1049311 = 1573967) B1573967
theorem B12780281 : Blo 1048611 12780281 := bstep (se 2 (by rfl) ⟨4792605, by rfl⟩ : syracuseStep 12780281 = 9585211) B9585211
theorem B1049391 : Blo 1048611 1049391 := bstep (se 1 (by rfl) ⟨787043, by rfl⟩ : syracuseStep 1049391 = 1574087) B1574087
theorem B2655119 : Blo 1048611 2655119 := bstep (se 1 (by rfl) ⟨1991339, by rfl⟩ : syracuseStep 2655119 = 3982679) B3982679
theorem B1573787 : Blo 1048611 1573787 := bstep (se 1 (by rfl) ⟨1180340, by rfl⟩ : syracuseStep 1573787 = 2360681) B2360681
theorem B1049499 : Blo 1048611 1049499 := bstep (se 1 (by rfl) ⟨787124, by rfl⟩ : syracuseStep 1049499 = 1574249) B1574249
theorem B1049551 : Blo 1048611 1049551 := bstep (se 1 (by rfl) ⟨787163, by rfl⟩ : syracuseStep 1049551 = 1574327) B1574327
theorem B1049575 : Blo 1048611 1049575 := bstep (se 1 (by rfl) ⟨787181, by rfl⟩ : syracuseStep 1049575 = 1574363) B1574363
theorem B2524135 : Blo 1048611 2524135 := bstep (se 1 (by rfl) ⟨1893101, by rfl⟩ : syracuseStep 2524135 = 3786203) B3786203
theorem B2360519 : Blo 1048611 2360519 := bstep (se 1 (by rfl) ⟨1770389, by rfl⟩ : syracuseStep 2360519 = 3540779) B3540779
theorem B1049887 : Blo 1048611 1049887 := bstep (se 1 (by rfl) ⟨787415, by rfl⟩ : syracuseStep 1049887 = 1574831) B1574831
theorem B1574183 : Blo 1048611 1574183 := bstep (se 1 (by rfl) ⟨1180637, by rfl⟩ : syracuseStep 1574183 = 2361275) B2361275
theorem B1049947 : Blo 1048611 1049947 := bstep (se 1 (by rfl) ⟨787460, by rfl⟩ : syracuseStep 1049947 = 1574921) B1574921
theorem B1049967 : Blo 1048611 1049967 := bstep (se 1 (by rfl) ⟨787475, by rfl⟩ : syracuseStep 1049967 = 1574951) B1574951
theorem B3540347 : Blo 1048611 3540347 := bstep (se 1 (by rfl) ⟨2655260, by rfl⟩ : syracuseStep 3540347 = 5310521) B5310521
theorem B2360699 : Blo 1048611 2360699 := bstep (se 1 (by rfl) ⟨1770524, by rfl⟩ : syracuseStep 2360699 = 3541049) B3541049
theorem B1574267 : Blo 1048611 1574267 := bstep (se 1 (by rfl) ⟨1180700, by rfl⟩ : syracuseStep 1574267 = 2361401) B2361401
theorem B2655625 : Blo 1048611 2655625 := bstep (se 2 (by rfl) ⟨995859, by rfl⟩ : syracuseStep 2655625 = 1991719) B1991719
theorem B1770889 : Blo 1048611 1770889 := bstep (se 2 (by rfl) ⟨664083, by rfl⟩ : syracuseStep 1770889 = 1328167) B1328167
theorem B1050023 : Blo 1048611 1050023 := bstep (se 1 (by rfl) ⟨787517, by rfl⟩ : syracuseStep 1050023 = 1575035) B1575035
theorem B10093997 : Blo 1048611 10093997 := bstep (se 3 (by rfl) ⟨1892624, by rfl⟩ : syracuseStep 10093997 = 3785249) B3785249
theorem B2655737 : Blo 1048611 2655737 := bstep (se 2 (by rfl) ⟨995901, by rfl⟩ : syracuseStep 2655737 = 1991803) B1991803
theorem B2360825 : Blo 1048611 2360825 := bstep (se 2 (by rfl) ⟨885309, by rfl⟩ : syracuseStep 2360825 = 1770619) B1770619
theorem B1574393 : Blo 1048611 1574393 := bstep (se 2 (by rfl) ⟨590397, by rfl⟩ : syracuseStep 1574393 = 1180795) B1180795
theorem B1050107 : Blo 1048611 1050107 := bstep (se 1 (by rfl) ⟨787580, by rfl⟩ : syracuseStep 1050107 = 1575161) B1575161
theorem B1050175 : Blo 1048611 1050175 := bstep (se 1 (by rfl) ⟨787631, by rfl⟩ : syracuseStep 1050175 = 1575263) B1575263
theorem B1050183 : Blo 1048611 1050183 := bstep (se 1 (by rfl) ⟨787637, by rfl⟩ : syracuseStep 1050183 = 1575275) B1575275
theorem B2360915 : Blo 1048611 2360915 := bstep (se 1 (by rfl) ⟨1770686, by rfl⟩ : syracuseStep 2360915 = 3541373) B3541373
theorem B1574495 : Blo 1048611 1574495 := bstep (se 1 (by rfl) ⟨1180871, by rfl⟩ : syracuseStep 1574495 = 2361743) B2361743
theorem B1181407 : Blo 1048611 1181407 := bstep (se 1 (by rfl) ⟨886055, by rfl⟩ : syracuseStep 1181407 = 1772111) B1772111
theorem B1050335 : Blo 1048611 1050335 := bstep (se 1 (by rfl) ⟨787751, by rfl⟩ : syracuseStep 1050335 = 1575503) B1575503
theorem B2361095 : Blo 1048611 2361095 := bstep (se 1 (by rfl) ⟨1770821, by rfl⟩ : syracuseStep 2361095 = 3541643) B3541643
theorem B1050415 : Blo 1048611 1050415 := bstep (se 1 (by rfl) ⟨787811, by rfl⟩ : syracuseStep 1050415 = 1575623) B1575623
theorem B1574711 : Blo 1048611 1574711 := bstep (se 1 (by rfl) ⟨1181033, by rfl⟩ : syracuseStep 1574711 = 2362067) B2362067
theorem B1771321 : Blo 1048611 1771321 := bstep (se 2 (by rfl) ⟨664245, by rfl⟩ : syracuseStep 1771321 = 1328491) B1328491
theorem B1050523 : Blo 1048611 1050523 := bstep (se 1 (by rfl) ⟨787892, by rfl⟩ : syracuseStep 1050523 = 1575785) B1575785
theorem B1050575 : Blo 1048611 1050575 := bstep (se 1 (by rfl) ⟨787931, by rfl⟩ : syracuseStep 1050575 = 1575863) B1575863
theorem B1050599 : Blo 1048611 1050599 := bstep (se 1 (by rfl) ⟨787949, by rfl⟩ : syracuseStep 1050599 = 1575899) B1575899
theorem B24250373 : Blo 1048611 24250373 := bstep (se 4 (by rfl) ⟨2273472, by rfl⟩ : syracuseStep 24250373 = 4546945) B4546945
theorem B1771625 : Blo 1048611 1771625 := bstep (se 2 (by rfl) ⟨664359, by rfl⟩ : syracuseStep 1771625 = 1328719) B1328719
theorem B1575017 : Blo 1048611 1575017 := bstep (se 2 (by rfl) ⟨590631, by rfl⟩ : syracuseStep 1575017 = 1181263) B1181263
theorem B2656385 : Blo 1048611 2656385 := bstep (se 2 (by rfl) ⟨996144, by rfl⟩ : syracuseStep 2656385 = 1992289) B1992289
theorem B1181983 : Blo 1048611 1181983 := bstep (se 1 (by rfl) ⟨886487, by rfl⟩ : syracuseStep 1181983 = 1772975) B1772975
theorem B1050911 : Blo 1048611 1050911 := bstep (se 1 (by rfl) ⟨788183, by rfl⟩ : syracuseStep 1050911 = 1576367) B1576367
theorem B1050971 : Blo 1048611 1050971 := bstep (se 1 (by rfl) ⟨788228, by rfl⟩ : syracuseStep 1050971 = 1576457) B1576457
theorem B2361707 : Blo 1048611 2361707 := bstep (se 1 (by rfl) ⟨1771280, by rfl⟩ : syracuseStep 2361707 = 3542561) B3542561
theorem B1050991 : Blo 1048611 1050991 := bstep (se 1 (by rfl) ⟨788243, by rfl⟩ : syracuseStep 1050991 = 1576487) B1576487
theorem B5310845 : Blo 1048611 5310845 := bstep (se 3 (by rfl) ⟨995783, by rfl⟩ : syracuseStep 5310845 = 1991567) B1991567
theorem B1575335 : Blo 1048611 1575335 := bstep (se 1 (by rfl) ⟨1181501, by rfl⟩ : syracuseStep 1575335 = 2363003) B2363003
theorem B1051047 : Blo 1048611 1051047 := bstep (se 1 (by rfl) ⟨788285, by rfl⟩ : syracuseStep 1051047 = 1576571) B1576571
theorem B2361851 : Blo 1048611 2361851 := bstep (se 1 (by rfl) ⟨1771388, by rfl⟩ : syracuseStep 2361851 = 3542777) B3542777
theorem B1575419 : Blo 1048611 1575419 := bstep (se 1 (by rfl) ⟨1181564, by rfl⟩ : syracuseStep 1575419 = 2363129) B2363129
theorem B1051131 : Blo 1048611 1051131 := bstep (se 1 (by rfl) ⟨788348, by rfl⟩ : syracuseStep 1051131 = 1576697) B1576697
theorem B1182271 : Blo 1048611 1182271 := bstep (se 1 (by rfl) ⟨886703, by rfl⟩ : syracuseStep 1182271 = 1773407) B1773407
theorem B1051199 : Blo 1048611 1051199 := bstep (se 1 (by rfl) ⟨788399, by rfl⟩ : syracuseStep 1051199 = 1576799) B1576799
theorem B1051207 : Blo 1048611 1051207 := bstep (se 1 (by rfl) ⟨788405, by rfl⟩ : syracuseStep 1051207 = 1576811) B1576811
theorem B2361977 : Blo 1048611 2361977 := bstep (se 2 (by rfl) ⟨885741, by rfl⟩ : syracuseStep 2361977 = 1771483) B1771483
theorem B1575545 : Blo 1048611 1575545 := bstep (se 2 (by rfl) ⟨590829, by rfl⟩ : syracuseStep 1575545 = 1181659) B1181659
theorem B2362031 : Blo 1048611 2362031 := bstep (se 1 (by rfl) ⟨1771523, by rfl⟩ : syracuseStep 2362031 = 3543047) B3543047
theorem B1575599 : Blo 1048611 1575599 := bstep (se 1 (by rfl) ⟨1181699, by rfl⟩ : syracuseStep 1575599 = 2363399) B2363399
theorem B11504339 : Blo 1048611 11504339 := bstep (se 1 (by rfl) ⟨8628254, by rfl⟩ : syracuseStep 11504339 = 17256509) B17256509
theorem B1575647 : Blo 1048611 1575647 := bstep (se 1 (by rfl) ⟨1181735, by rfl⟩ : syracuseStep 1575647 = 2363471) B2363471
theorem B1051359 : Blo 1048611 1051359 := bstep (se 1 (by rfl) ⟨788519, by rfl⟩ : syracuseStep 1051359 = 1577039) B1577039
theorem B3541751 : Blo 1048611 3541751 := bstep (se 1 (by rfl) ⟨2656313, by rfl⟩ : syracuseStep 3541751 = 5312627) B5312627
theorem B2362103 : Blo 1048611 2362103 := bstep (se 1 (by rfl) ⟨1771577, by rfl⟩ : syracuseStep 2362103 = 3543155) B3543155
theorem B1051439 : Blo 1048611 1051439 := bstep (se 1 (by rfl) ⟨788579, by rfl⟩ : syracuseStep 1051439 = 1577159) B1577159
theorem B1051547 : Blo 1048611 1051547 := bstep (se 1 (by rfl) ⟨788660, by rfl⟩ : syracuseStep 1051547 = 1577321) B1577321
theorem B2657195 : Blo 1048611 2657195 := bstep (se 1 (by rfl) ⟨1992896, by rfl⟩ : syracuseStep 2657195 = 3985793) B3985793
theorem B2362283 : Blo 1048611 2362283 := bstep (se 1 (by rfl) ⟨1771712, by rfl⟩ : syracuseStep 2362283 = 3543425) B3543425
theorem B4492219 : Blo 1048611 4492219 := bstep (se 1 (by rfl) ⟨3369164, by rfl⟩ : syracuseStep 4492219 = 6738329) B6738329
theorem B1051599 : Blo 1048611 1051599 := bstep (se 1 (by rfl) ⟨788699, by rfl⟩ : syracuseStep 1051599 = 1577399) B1577399
theorem B1575911 : Blo 1048611 1575911 := bstep (se 1 (by rfl) ⟨1181933, by rfl⟩ : syracuseStep 1575911 = 2363867) B2363867
theorem B1051623 : Blo 1048611 1051623 := bstep (se 1 (by rfl) ⟨788717, by rfl⟩ : syracuseStep 1051623 = 1577435) B1577435
theorem B1576169 : Blo 1048611 1576169 := bstep (se 2 (by rfl) ⟨591063, by rfl⟩ : syracuseStep 1576169 = 1182127) B1182127
theorem B1576223 : Blo 1048611 1576223 := bstep (se 1 (by rfl) ⟨1182167, by rfl⟩ : syracuseStep 1576223 = 2364335) B2364335
theorem B1051935 : Blo 1048611 1051935 := bstep (se 1 (by rfl) ⟨788951, by rfl⟩ : syracuseStep 1051935 = 1577903) B1577903
theorem B1051995 : Blo 1048611 1051995 := bstep (se 1 (by rfl) ⟨788996, by rfl⟩ : syracuseStep 1051995 = 1577993) B1577993
theorem B1052015 : Blo 1048611 1052015 := bstep (se 1 (by rfl) ⟨789011, by rfl⟩ : syracuseStep 1052015 = 1578023) B1578023
theorem B1183099 : Blo 1048611 1183099 := bstep (se 1 (by rfl) ⟨887324, by rfl⟩ : syracuseStep 1183099 = 1774649) B1774649
theorem B2559371 : Blo 1048611 2559371 := bstep (se 1 (by rfl) ⟨1919528, by rfl⟩ : syracuseStep 2559371 = 3839057) B3839057
theorem B1052071 : Blo 1048611 1052071 := bstep (se 1 (by rfl) ⟨789053, by rfl⟩ : syracuseStep 1052071 = 1578107) B1578107
theorem B2362823 : Blo 1048611 2362823 := bstep (se 1 (by rfl) ⟨1772117, by rfl⟩ : syracuseStep 2362823 = 3544235) B3544235
theorem B1576391 : Blo 1048611 1576391 := bstep (se 1 (by rfl) ⟨1182293, by rfl⟩ : syracuseStep 1576391 = 2364587) B2364587
theorem B1773049 : Blo 1048611 1773049 := bstep (se 2 (by rfl) ⟨664893, by rfl⟩ : syracuseStep 1773049 = 1329787) B1329787
theorem B1052155 : Blo 1048611 1052155 := bstep (se 1 (by rfl) ⟨789116, by rfl⟩ : syracuseStep 1052155 = 1578233) B1578233
theorem B1052223 : Blo 1048611 1052223 := bstep (se 1 (by rfl) ⟨789167, by rfl⟩ : syracuseStep 1052223 = 1578335) B1578335
theorem B1052231 : Blo 1048611 1052231 := bstep (se 1 (by rfl) ⟨789173, by rfl⟩ : syracuseStep 1052231 = 1578347) B1578347
theorem B22744709 : Blo 1048611 22744709 := bstep (se 4 (by rfl) ⟨2132316, by rfl⟩ : syracuseStep 22744709 = 4264633) B4264633
theorem B9572039 : Blo 1048611 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B1052383 : Blo 1048611 1052383 := bstep (se 1 (by rfl) ⟨789287, by rfl⟩ : syracuseStep 1052383 = 1578575) B1578575
theorem B8982251 : Blo 1048611 8982251 := bstep (se 1 (by rfl) ⟨6736688, by rfl⟩ : syracuseStep 8982251 = 13473377) B13473377
theorem B2658055 : Blo 1048611 2658055 := bstep (se 1 (by rfl) ⟨1993541, by rfl⟩ : syracuseStep 2658055 = 3987083) B3987083
theorem B1773319 : Blo 1048611 1773319 := bstep (se 1 (by rfl) ⟨1329989, by rfl⟩ : syracuseStep 1773319 = 2659979) B2659979
theorem B1773353 : Blo 1048611 1773353 := bstep (se 2 (by rfl) ⟨665007, by rfl⟩ : syracuseStep 1773353 = 1330015) B1330015
theorem B1576745 : Blo 1048611 1576745 := bstep (se 2 (by rfl) ⟨591279, by rfl⟩ : syracuseStep 1576745 = 1182559) B1182559
theorem B7966511 : Blo 1048611 7966511 := bstep (se 1 (by rfl) ⟨5974883, by rfl⟩ : syracuseStep 7966511 = 11949767) B11949767
theorem B5312303 : Blo 1048611 5312303 := bstep (se 1 (by rfl) ⟨3984227, by rfl⟩ : syracuseStep 5312303 = 7968455) B7968455
theorem B3542831 : Blo 1048611 3542831 := bstep (se 1 (by rfl) ⟨2657123, by rfl⟩ : syracuseStep 3542831 = 5314247) B5314247
theorem B2363183 : Blo 1048611 2363183 := bstep (se 1 (by rfl) ⟨1772387, by rfl⟩ : syracuseStep 2363183 = 3544775) B3544775
theorem B1576751 : Blo 1048611 1576751 := bstep (se 1 (by rfl) ⟨1182563, by rfl⟩ : syracuseStep 1576751 = 2365127) B2365127
theorem B1052463 : Blo 1048611 1052463 := bstep (se 1 (by rfl) ⟨789347, by rfl⟩ : syracuseStep 1052463 = 1578695) B1578695
theorem B1183567 : Blo 1048611 1183567 := bstep (se 1 (by rfl) ⟨887675, by rfl⟩ : syracuseStep 1183567 = 1775351) B1775351
theorem B1052571 : Blo 1048611 1052571 := bstep (se 1 (by rfl) ⟨789428, by rfl⟩ : syracuseStep 1052571 = 1578857) B1578857
theorem B2658329 : Blo 1048611 2658329 := bstep (se 2 (by rfl) ⟨996873, by rfl⟩ : syracuseStep 2658329 = 1993747) B1993747
theorem B4493465 : Blo 1048611 4493465 := bstep (se 2 (by rfl) ⟨1685049, by rfl⟩ : syracuseStep 4493465 = 3370099) B3370099
theorem B43159715 : Blo 1048611 43159715 := bstep (se 1 (by rfl) ⟨32369786, by rfl⟩ : syracuseStep 43159715 = 64739573) B64739573
theorem B1183963 : Blo 1048611 1183963 := bstep (se 1 (by rfl) ⟨887972, by rfl⟩ : syracuseStep 1183963 = 1775945) B1775945
theorem B1577225 : Blo 1048611 1577225 := bstep (se 2 (by rfl) ⟨591459, by rfl⟩ : syracuseStep 1577225 = 1182919) B1182919
theorem B2527595 : Blo 1048611 2527595 := bstep (se 1 (by rfl) ⟨1895696, by rfl⟩ : syracuseStep 2527595 = 3791393) B3791393
theorem B2363759 : Blo 1048611 2363759 := bstep (se 1 (by rfl) ⟨1772819, by rfl⟩ : syracuseStep 2363759 = 3545639) B3545639
theorem B1577327 : Blo 1048611 1577327 := bstep (se 1 (by rfl) ⟨1182995, by rfl⟩ : syracuseStep 1577327 = 2365991) B2365991
theorem B8982899 : Blo 1048611 8982899 := bstep (se 1 (by rfl) ⟨6737174, by rfl⟩ : syracuseStep 8982899 = 13474349) B13474349
theorem B2363831 : Blo 1048611 2363831 := bstep (se 1 (by rfl) ⟨1772873, by rfl⟩ : syracuseStep 2363831 = 3545747) B3545747
theorem B1774075 : Blo 1048611 1774075 := bstep (se 1 (by rfl) ⟨1330556, by rfl⟩ : syracuseStep 1774075 = 2661113) B2661113
theorem B2363975 : Blo 1048611 2363975 := bstep (se 1 (by rfl) ⟨1772981, by rfl⟩ : syracuseStep 2363975 = 3545963) B3545963
theorem B1577543 : Blo 1048611 1577543 := bstep (se 1 (by rfl) ⟨1183157, by rfl⟩ : syracuseStep 1577543 = 2366315) B2366315
theorem B2364011 : Blo 1048611 2364011 := bstep (se 1 (by rfl) ⟨1773008, by rfl⟩ : syracuseStep 2364011 = 3546017) B3546017
theorem B1577579 : Blo 1048611 1577579 := bstep (se 1 (by rfl) ⟨1183184, by rfl⟩ : syracuseStep 1577579 = 2366369) B2366369
theorem B15569561 : Blo 1048611 15569561 := bstep (se 2 (by rfl) ⟨5838585, by rfl⟩ : syracuseStep 15569561 = 11677171) B11677171
theorem B1577807 : Blo 1048611 1577807 := bstep (se 1 (by rfl) ⟨1183355, by rfl⟩ : syracuseStep 1577807 = 2366711) B2366711
theorem B1774507 : Blo 1048611 1774507 := bstep (se 1 (by rfl) ⟨1330880, by rfl⟩ : syracuseStep 1774507 = 2661761) B2661761
theorem B2364407 : Blo 1048611 2364407 := bstep (se 1 (by rfl) ⟨1773305, by rfl⟩ : syracuseStep 2364407 = 3546611) B3546611
theorem B2462759 : Blo 1048611 2462759 := bstep (se 1 (by rfl) ⟨1847069, by rfl⟩ : syracuseStep 2462759 = 3694139) B3694139
theorem B1774811 : Blo 1048611 1774811 := bstep (se 1 (by rfl) ⟨1331108, by rfl⟩ : syracuseStep 1774811 = 2662217) B2662217
theorem B1578203 : Blo 1048611 1578203 := bstep (se 1 (by rfl) ⟨1183652, by rfl⟩ : syracuseStep 1578203 = 2367305) B2367305
theorem B2364767 : Blo 1048611 2364767 := bstep (se 1 (by rfl) ⟨1773575, by rfl⟩ : syracuseStep 2364767 = 3547151) B3547151
theorem B1578377 : Blo 1048611 1578377 := bstep (se 2 (by rfl) ⟨591891, by rfl⟩ : syracuseStep 1578377 = 1183783) B1183783
theorem B1775047 : Blo 1048611 1775047 := bstep (se 1 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 1775047 = 2662571) B2662571
theorem B12785339 : Blo 1048611 12785339 := bstep (se 1 (by rfl) ⟨9589004, by rfl⟩ : syracuseStep 12785339 = 19178009) B19178009
theorem B2365163 : Blo 1048611 2365163 := bstep (se 1 (by rfl) ⟨1773872, by rfl⟩ : syracuseStep 2365163 = 3547745) B3547745
theorem B1578731 : Blo 1048611 1578731 := bstep (se 1 (by rfl) ⟨1184048, by rfl⟩ : syracuseStep 1578731 = 2368097) B2368097
theorem B5314409 : Blo 1048611 5314409 := bstep (se 2 (by rfl) ⟨1992903, by rfl⟩ : syracuseStep 5314409 = 3985807) B3985807
theorem B3544937 : Blo 1048611 3544937 := bstep (se 2 (by rfl) ⟨1329351, by rfl⟩ : syracuseStep 3544937 = 2658703) B2658703
theorem B2365289 : Blo 1048611 2365289 := bstep (se 2 (by rfl) ⟨886983, by rfl⟩ : syracuseStep 2365289 = 1773967) B1773967
theorem B2660303 : Blo 1048611 2660303 := bstep (se 1 (by rfl) ⟨1995227, by rfl⟩ : syracuseStep 2660303 = 3990455) B3990455
theorem B1775567 : Blo 1048611 1775567 := bstep (se 1 (by rfl) ⟨1331675, by rfl⟩ : syracuseStep 1775567 = 2663351) B2663351
theorem B11376683 : Blo 1048611 11376683 := bstep (se 1 (by rfl) ⟨8532512, by rfl⟩ : syracuseStep 11376683 = 17065025) B17065025
theorem B2988161 : Blo 1048611 2988161 := bstep (se 2 (by rfl) ⟨1120560, by rfl⟩ : syracuseStep 2988161 = 2241121) B2241121
theorem B3545369 : Blo 1048611 3545369 := bstep (se 2 (by rfl) ⟨1329513, by rfl⟩ : syracuseStep 3545369 = 2659027) B2659027
theorem B2660971 : Blo 1048611 2660971 := bstep (se 1 (by rfl) ⟨1995728, by rfl⟩ : syracuseStep 2660971 = 3991457) B3991457
theorem B1776235 : Blo 1048611 1776235 := bstep (se 1 (by rfl) ⟨1332176, by rfl⟩ : syracuseStep 1776235 = 2664353) B2664353
theorem B10361519 : Blo 1048611 10361519 := bstep (se 1 (by rfl) ⟨7771139, by rfl⟩ : syracuseStep 10361519 = 15542279) B15542279
theorem B2366135 : Blo 1048611 2366135 := bstep (se 1 (by rfl) ⟨1774601, by rfl⟩ : syracuseStep 2366135 = 3549203) B3549203
theorem B5053303 : Blo 1048611 5053303 := bstep (se 1 (by rfl) ⟨3789977, by rfl⟩ : syracuseStep 5053303 = 7579955) B7579955
theorem B2366351 : Blo 1048611 2366351 := bstep (se 1 (by rfl) ⟨1774763, by rfl⟩ : syracuseStep 2366351 = 3549527) B3549527
theorem B2661275 : Blo 1048611 2661275 := bstep (se 1 (by rfl) ⟨1995956, by rfl⟩ : syracuseStep 2661275 = 3991913) B3991913
theorem B17964017 : Blo 1048611 17964017 := bstep (se 2 (by rfl) ⟨6736506, by rfl⟩ : syracuseStep 17964017 = 13473013) B13473013
theorem B11377853 : Blo 1048611 11377853 := bstep (se 3 (by rfl) ⟨2133347, by rfl⟩ : syracuseStep 11377853 = 4266695) B4266695
theorem B2661619 : Blo 1048611 2661619 := bstep (se 1 (by rfl) ⟨1996214, by rfl⟩ : syracuseStep 2661619 = 3992429) B3992429
theorem B4791619 : Blo 1048611 4791619 := bstep (se 1 (by rfl) ⟨3593714, by rfl⟩ : syracuseStep 4791619 = 7187429) B7187429
theorem B1121735 : Blo 1048611 1121735 := bstep (se 1 (by rfl) ⟨841301, by rfl⟩ : syracuseStep 1121735 = 1682603) B1682603
theorem B2989561 : Blo 1048611 2989561 := bstep (se 2 (by rfl) ⟨1121085, by rfl⟩ : syracuseStep 2989561 = 2242171) B2242171
theorem B7970399 : Blo 1048611 7970399 := bstep (se 1 (by rfl) ⟨5977799, by rfl⟩ : syracuseStep 7970399 = 11955599) B11955599
theorem B5316191 : Blo 1048611 5316191 := bstep (se 1 (by rfl) ⟨3987143, by rfl⟩ : syracuseStep 5316191 = 7974287) B7974287
theorem B3546719 : Blo 1048611 3546719 := bstep (se 1 (by rfl) ⟨2660039, by rfl⟩ : syracuseStep 3546719 = 5320079) B5320079
theorem B2367071 : Blo 1048611 2367071 := bstep (se 1 (by rfl) ⟨1775303, by rfl⟩ : syracuseStep 2367071 = 3550607) B3550607
theorem B2367287 : Blo 1048611 2367287 := bstep (se 1 (by rfl) ⟨1775465, by rfl⟩ : syracuseStep 2367287 = 3550931) B3550931
theorem B12787631 : Blo 1048611 12787631 := bstep (se 1 (by rfl) ⟨9590723, by rfl⟩ : syracuseStep 12787631 = 19181447) B19181447
theorem B2662409 : Blo 1048611 2662409 := bstep (se 2 (by rfl) ⟨998403, by rfl⟩ : syracuseStep 2662409 = 1996807) B1996807
theorem B2367593 : Blo 1048611 2367593 := bstep (se 2 (by rfl) ⟨887847, by rfl⟩ : syracuseStep 2367593 = 1775695) B1775695
theorem B11968721 : Blo 1048611 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B1417609 : Blo 1048611 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B1679783 : Blo 1048611 1679783 := bstep (se 1 (by rfl) ⟨1259837, by rfl⟩ : syracuseStep 1679783 = 2519675) B2519675
theorem B1679867 : Blo 1048611 1679867 := bstep (se 1 (by rfl) ⟨1259900, by rfl⟩ : syracuseStep 1679867 = 2519801) B2519801
theorem B5054977 : Blo 1048611 5054977 := bstep (se 2 (by rfl) ⟨1895616, by rfl⟩ : syracuseStep 5054977 = 3791233) B3791233
theorem B34054667 : Blo 1048611 34054667 := bstep (se 1 (by rfl) ⟨25541000, by rfl⟩ : syracuseStep 34054667 = 51082001) B51082001
theorem B2368079 : Blo 1048611 2368079 := bstep (se 1 (by rfl) ⟨1776059, by rfl⟩ : syracuseStep 2368079 = 3552119) B3552119
theorem B2368223 : Blo 1048611 2368223 := bstep (se 1 (by rfl) ⟨1776167, by rfl⟩ : syracuseStep 2368223 = 3552335) B3552335
theorem B3548123 : Blo 1048611 3548123 := bstep (se 1 (by rfl) ⟨2661092, by rfl⟩ : syracuseStep 3548123 = 5322185) B5322185
theorem B3548285 : Blo 1048611 3548285 := bstep (se 3 (by rfl) ⟨665303, by rfl⟩ : syracuseStep 3548285 = 1330607) B1330607
theorem B2663563 : Blo 1048611 2663563 := bstep (se 1 (by rfl) ⟨1997672, by rfl⟩ : syracuseStep 2663563 = 3995345) B3995345
theorem B3548393 : Blo 1048611 3548393 := bstep (se 2 (by rfl) ⟨1330647, by rfl⟩ : syracuseStep 3548393 = 2661295) B2661295
theorem B5973335 : Blo 1048611 5973335 := bstep (se 1 (by rfl) ⟨4480001, by rfl⟩ : syracuseStep 5973335 = 8960003) B8960003
theorem B8529239 : Blo 1048611 8529239 := bstep (se 1 (by rfl) ⟨6396929, by rfl⟩ : syracuseStep 8529239 = 12793859) B12793859
theorem B3548555 : Blo 1048611 3548555 := bstep (se 1 (by rfl) ⟨2661416, by rfl⟩ : syracuseStep 3548555 = 5322833) B5322833
theorem B1123751 : Blo 1048611 1123751 := bstep (se 1 (by rfl) ⟨842813, by rfl⟩ : syracuseStep 1123751 = 1685627) B1685627
theorem B2663867 : Blo 1048611 2663867 := bstep (se 1 (by rfl) ⟨1997900, by rfl⟩ : syracuseStep 2663867 = 3995801) B3995801
theorem B3417533 : Blo 1048611 3417533 := bstep (se 3 (by rfl) ⟨640787, by rfl⟩ : syracuseStep 3417533 = 1281575) B1281575
theorem B11347789 : Blo 1048611 11347789 := bstep (se 3 (by rfl) ⟨2127710, by rfl⟩ : syracuseStep 11347789 = 4255421) B4255421
theorem B32286545 : Blo 1048611 32286545 := bstep (se 2 (by rfl) ⟨12107454, by rfl⟩ : syracuseStep 32286545 = 24214909) B24214909
theorem B2992079 : Blo 1048611 2992079 := bstep (se 1 (by rfl) ⟨2244059, by rfl⟩ : syracuseStep 2992079 = 4488119) B4488119
theorem B5679085 : Blo 1048611 5679085 := bstep (se 3 (by rfl) ⟨1064828, by rfl⟩ : syracuseStep 5679085 = 2129657) B2129657
theorem B9578573 : Blo 1048611 9578573 := bstep (se 3 (by rfl) ⟨1795982, by rfl⟩ : syracuseStep 9578573 = 3591965) B3591965
theorem B2992409 : Blo 1048611 2992409 := bstep (se 2 (by rfl) ⟨1122153, by rfl⟩ : syracuseStep 2992409 = 2244307) B2244307
theorem B14035235 : Blo 1048611 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B2271655 : Blo 1048611 2271655 := bstep (se 1 (by rfl) ⟨1703741, by rfl⟩ : syracuseStep 2271655 = 3407483) B3407483
theorem B3451891 : Blo 1048611 3451891 := bstep (se 1 (by rfl) ⟨2588918, by rfl⟩ : syracuseStep 3451891 = 5177837) B5177837
theorem B3845107 : Blo 1048611 3845107 := bstep (se 1 (by rfl) ⟨2883830, by rfl⟩ : syracuseStep 3845107 = 5767661) B5767661
theorem B1420507 : Blo 1048611 1420507 := bstep (se 1 (by rfl) ⟨1065380, by rfl⟩ : syracuseStep 1420507 = 2130761) B2130761
theorem B49262093 : Blo 1048611 49262093 := bstep (se 3 (by rfl) ⟨9236642, by rfl⟩ : syracuseStep 49262093 = 18473285) B18473285
theorem B5320403 : Blo 1048611 5320403 := bstep (se 1 (by rfl) ⟨3990302, by rfl⟩ : syracuseStep 5320403 = 7980605) B7980605
theorem B8990621 : Blo 1048611 8990621 := bstep (se 3 (by rfl) ⟨1685741, by rfl⟩ : syracuseStep 8990621 = 3371483) B3371483
theorem B2994185 : Blo 1048611 2994185 := bstep (se 2 (by rfl) ⟨1122819, by rfl⟩ : syracuseStep 2994185 = 2245639) B2245639
theorem B8531993 : Blo 1048611 8531993 := bstep (se 2 (by rfl) ⟨3199497, by rfl⟩ : syracuseStep 8531993 = 6398995) B6398995
theorem B76591169 : Blo 1048611 76591169 := bstep (se 2 (by rfl) ⟨28721688, by rfl⟩ : syracuseStep 76591169 = 57443377) B57443377
theorem B5321051 : Blo 1048611 5321051 := bstep (se 1 (by rfl) ⟨3990788, by rfl⟩ : syracuseStep 5321051 = 7981577) B7981577
theorem B3551579 : Blo 1048611 3551579 := bstep (se 1 (by rfl) ⟨2663684, by rfl⟩ : syracuseStep 3551579 = 5327369) B5327369
theorem B2995325 : Blo 1048611 2995325 := bstep (se 3 (by rfl) ⟨561623, by rfl⟩ : syracuseStep 2995325 = 1123247) B1123247
theorem B5387411 : Blo 1048611 5387411 := bstep (se 1 (by rfl) ⟨4040558, by rfl⟩ : syracuseStep 5387411 = 8081117) B8081117
theorem B3781847 : Blo 1048611 3781847 := bstep (se 1 (by rfl) ⟨2836385, by rfl⟩ : syracuseStep 3781847 = 5672771) B5672771
theorem B5682419 : Blo 1048611 5682419 := bstep (se 1 (by rfl) ⟨4261814, by rfl⟩ : syracuseStep 5682419 = 8523629) B8523629
theorem B7976231 : Blo 1048611 7976231 := bstep (se 1 (by rfl) ⟨5982173, by rfl⟩ : syracuseStep 7976231 = 11964347) B11964347
theorem B5322023 : Blo 1048611 5322023 := bstep (se 1 (by rfl) ⟨3991517, by rfl⟩ : syracuseStep 5322023 = 7983035) B7983035
theorem B3552551 : Blo 1048611 3552551 := bstep (se 1 (by rfl) ⟨2664413, by rfl⟩ : syracuseStep 3552551 = 5328827) B5328827
theorem B2045675 : Blo 1048611 2045675 := bstep (se 1 (by rfl) ⟨1534256, by rfl⟩ : syracuseStep 2045675 = 3068513) B3068513
theorem B140196109 : Blo 1048611 140196109 := bstep (se 3 (by rfl) ⟨26286770, by rfl⟩ : syracuseStep 140196109 = 52573541) B52573541
theorem B5978393 : Blo 1048611 5978393 := bstep (se 2 (by rfl) ⟨2241897, by rfl⟩ : syracuseStep 5978393 = 4483795) B4483795
theorem B8960381 : Blo 1048611 8960381 := bstep (se 3 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 8960381 = 3360143) B3360143
theorem B2242991 : Blo 1048611 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B11352635 : Blo 1048611 11352635 := bstep (se 1 (by rfl) ⟨8514476, by rfl⟩ : syracuseStep 11352635 = 17028953) B17028953
theorem B1916257 : Blo 1048611 1916257 := bstep (se 2 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 1916257 = 1437193) B1437193
theorem B5324129 : Blo 1048611 5324129 := bstep (se 2 (by rfl) ⟨1996548, by rfl⟩ : syracuseStep 5324129 = 3993097) B3993097
theorem B7585609 : Blo 1048611 7585609 := bstep (se 2 (by rfl) ⟨2844603, by rfl⟩ : syracuseStep 7585609 = 5689207) B5689207
theorem B5980169 : Blo 1048611 5980169 := bstep (se 2 (by rfl) ⟨2242563, by rfl⟩ : syracuseStep 5980169 = 4485127) B4485127
theorem B4800617 : Blo 1048611 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B53199197 : Blo 1048611 53199197 := bstep (se 3 (by rfl) ⟨9974849, by rfl⟩ : syracuseStep 53199197 = 19949699) B19949699
theorem B3195361 : Blo 1048611 3195361 := bstep (se 2 (by rfl) ⟨1198260, by rfl⟩ : syracuseStep 3195361 = 2396521) B2396521
theorem B3588761 : Blo 1048611 3588761 := bstep (se 2 (by rfl) ⟨1345785, by rfl⟩ : syracuseStep 3588761 = 2691571) B2691571
theorem B5326073 : Blo 1048611 5326073 := bstep (se 2 (by rfl) ⟨1997277, by rfl⟩ : syracuseStep 5326073 = 3994555) B3994555
theorem B3786173 : Blo 1048611 3786173 := bstep (se 3 (by rfl) ⟨709907, by rfl⟩ : syracuseStep 3786173 = 1419815) B1419815
theorem B1328815 : Blo 1048611 1328815 := bstep (se 1 (by rfl) ⟨996611, by rfl⟩ : syracuseStep 1328815 = 1993223) B1993223
theorem B4540367 : Blo 1048611 4540367 := bstep (se 1 (by rfl) ⟨3405275, by rfl⟩ : syracuseStep 4540367 = 6810551) B6810551
theorem B2836505 : Blo 1048611 2836505 := bstep (se 2 (by rfl) ⟨1063689, by rfl⟩ : syracuseStep 2836505 = 2127379) B2127379
theorem B746768645 : Blo 1048611 746768645 := bstep (se 4 (by rfl) ⟨70009560, by rfl⟩ : syracuseStep 746768645 = 140019121) B140019121
theorem B1493687 : Blo 1048611 1493687 := bstep (se 1 (by rfl) ⟨1120265, by rfl⟩ : syracuseStep 1493687 = 2240531) B2240531
theorem B28756727 : Blo 1048611 28756727 := bstep (se 1 (by rfl) ⟨21567545, by rfl⟩ : syracuseStep 28756727 = 43135091) B43135091
theorem B2247929 : Blo 1048611 2247929 := bstep (se 2 (by rfl) ⟨842973, by rfl⟩ : syracuseStep 2247929 = 1685947) B1685947
theorem B2248031 : Blo 1048611 2248031 := bstep (se 1 (by rfl) ⟨1686023, by rfl⟩ : syracuseStep 2248031 = 3372047) B3372047
theorem B1330759 : Blo 1048611 1330759 := bstep (se 1 (by rfl) ⟨998069, by rfl⟩ : syracuseStep 1330759 = 1996139) B1996139
theorem B11980385 : Blo 1048611 11980385 := bstep (se 2 (by rfl) ⟨4492644, by rfl⟩ : syracuseStep 11980385 = 8985289) B8985289
theorem B2838377 : Blo 1048611 2838377 := bstep (se 2 (by rfl) ⟨1064391, by rfl⟩ : syracuseStep 2838377 = 2128783) B2128783
theorem B1495145 : Blo 1048611 1495145 := bstep (se 2 (by rfl) ⟨560679, by rfl⟩ : syracuseStep 1495145 = 1121359) B1121359
theorem B1331579 : Blo 1048611 1331579 := bstep (se 1 (by rfl) ⟨998684, by rfl⟩ : syracuseStep 1331579 = 1997369) B1997369
theorem B51106909 : Blo 1048611 51106909 := bstep (se 3 (by rfl) ⟨9582545, by rfl⟩ : syracuseStep 51106909 = 19165091) B19165091
theorem B1889735 : Blo 1048611 1889735 := bstep (se 1 (by rfl) ⟨1417301, by rfl⟩ : syracuseStep 1889735 = 2834603) B2834603
theorem B1594823 : Blo 1048611 1594823 := bstep (se 1 (by rfl) ⟨1196117, by rfl⟩ : syracuseStep 1594823 = 2392235) B2392235
theorem B1496569 : Blo 1048611 1496569 := bstep (se 2 (by rfl) ⟨561213, by rfl⟩ : syracuseStep 1496569 = 1122427) B1122427
theorem B16176647 : Blo 1048611 16176647 := bstep (se 1 (by rfl) ⟨12132485, by rfl⟩ : syracuseStep 16176647 = 24264971) B24264971
theorem B22697657 : Blo 1048611 22697657 := bstep (se 2 (by rfl) ⟨8511621, by rfl⟩ : syracuseStep 22697657 = 17023243) B17023243
theorem B3364897 : Blo 1048611 3364897 := bstep (se 2 (by rfl) ⟨1261836, by rfl⟩ : syracuseStep 3364897 = 2523673) B2523673
theorem B3987737 : Blo 1048611 3987737 := bstep (se 2 (by rfl) ⟨1495401, by rfl⟩ : syracuseStep 3987737 = 2990803) B2990803
theorem B3038077 : Blo 1048611 3038077 := bstep (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) B1139279
theorem B1498505 : Blo 1048611 1498505 := bstep (se 2 (by rfl) ⟨561939, by rfl⟩ : syracuseStep 1498505 = 1123879) B1123879
theorem B3989513 : Blo 1048611 3989513 := bstep (se 2 (by rfl) ⟨1496067, by rfl⟩ : syracuseStep 3989513 = 2992135) B2992135
theorem B7987409 : Blo 1048611 7987409 := bstep (se 2 (by rfl) ⟨2995278, by rfl⟩ : syracuseStep 7987409 = 5990557) B5990557
theorem B2154919 : Blo 1048611 2154919 := bstep (se 1 (by rfl) ⟨1616189, by rfl⟩ : syracuseStep 2154919 = 3232379) B3232379
theorem B18211331 : Blo 1048611 18211331 := bstep (se 1 (by rfl) ⟨13658498, by rfl⟩ : syracuseStep 18211331 = 27316997) B27316997
theorem B7987895 : Blo 1048611 7987895 := bstep (se 1 (by rfl) ⟨5990921, by rfl⟩ : syracuseStep 7987895 = 11981843) B11981843
theorem B3990653 : Blo 1048611 3990653 := bstep (se 3 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 3990653 = 1496495) B1496495
theorem B2843867 : Blo 1048611 2843867 := bstep (se 1 (by rfl) ⟨2132900, by rfl⟩ : syracuseStep 2843867 = 4265801) B4265801
theorem B5039927 : Blo 1048611 5039927 := bstep (se 1 (by rfl) ⟨3779945, by rfl⟩ : syracuseStep 5039927 = 7559891) B7559891
theorem B8972167 : Blo 1048611 8972167 := bstep (se 1 (by rfl) ⟨6729125, by rfl⟩ : syracuseStep 8972167 = 13458251) B13458251
theorem B10217657 : Blo 1048611 10217657 := bstep (se 2 (by rfl) ⟨3831621, by rfl⟩ : syracuseStep 10217657 = 7663243) B7663243
theorem B4483471 : Blo 1048611 4483471 := bstep (se 1 (by rfl) ⟨3362603, by rfl⟩ : syracuseStep 4483471 = 6725207) B6725207
theorem B3238463 : Blo 1048611 3238463 := bstep (se 1 (by rfl) ⟨2428847, by rfl⟩ : syracuseStep 3238463 = 4857695) B4857695
theorem B7989839 : Blo 1048611 7989839 := bstep (se 1 (by rfl) ⟨5992379, by rfl⟩ : syracuseStep 7989839 = 11984759) B11984759
theorem B3369883 : Blo 1048611 3369883 := bstep (se 1 (by rfl) ⟨2527412, by rfl⟩ : syracuseStep 3369883 = 5054825) B5054825
theorem B4255163 : Blo 1048611 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B1994233 : Blo 1048611 1994233 := bstep (se 2 (by rfl) ⟨747837, by rfl⟩ : syracuseStep 1994233 = 1495675) B1495675
theorem B4484717 : Blo 1048611 4484717 := bstep (se 3 (by rfl) ⟨840884, by rfl⟩ : syracuseStep 4484717 = 1681769) B1681769
theorem B1994537 : Blo 1048611 1994537 := bstep (se 2 (by rfl) ⟨747951, by rfl⟩ : syracuseStep 1994537 = 1495903) B1495903
theorem B3993401 : Blo 1048611 3993401 := bstep (se 2 (by rfl) ⟨1497525, by rfl⟩ : syracuseStep 3993401 = 2995051) B2995051
theorem B7991297 : Blo 1048611 7991297 := bstep (se 2 (by rfl) ⟨2996736, by rfl⟩ : syracuseStep 7991297 = 5993473) B5993473
theorem B54653129 : Blo 1048611 54653129 := bstep (se 2 (by rfl) ⟨20494923, by rfl⟩ : syracuseStep 54653129 = 40989847) B40989847
theorem B2126089 : Blo 1048611 2126089 := bstep (se 2 (by rfl) ⟨797283, by rfl⟩ : syracuseStep 2126089 = 1594567) B1594567
theorem B73855469 : Blo 1048611 73855469 := bstep (se 3 (by rfl) ⟨13847900, by rfl⟩ : syracuseStep 73855469 = 27695801) B27695801
theorem B4551169 : Blo 1048611 4551169 := bstep (se 2 (by rfl) ⟨1706688, by rfl⟩ : syracuseStep 4551169 = 3413377) B3413377
theorem B1995691 : Blo 1048611 1995691 := bstep (se 1 (by rfl) ⟨1496768, by rfl⟩ : syracuseStep 1995691 = 2993537) B2993537
theorem B1995995 : Blo 1048611 1995995 := bstep (se 1 (by rfl) ⟨1496996, by rfl⟩ : syracuseStep 1995995 = 2993993) B2993993
theorem B5043617 : Blo 1048611 5043617 := bstep (se 2 (by rfl) ⟨1891356, by rfl⟩ : syracuseStep 5043617 = 3782713) B3782713
theorem B3995041 : Blo 1048611 3995041 := bstep (se 2 (by rfl) ⟨1498140, by rfl⟩ : syracuseStep 3995041 = 2996281) B2996281
theorem B2521039 : Blo 1048611 2521039 := bstep (se 1 (by rfl) ⟨1890779, by rfl⟩ : syracuseStep 2521039 = 3781559) B3781559
theorem B1997065 : Blo 1048611 1997065 := bstep (se 2 (by rfl) ⟨748899, by rfl⟩ : syracuseStep 1997065 = 1497799) B1497799
theorem B20183687 : Blo 1048611 20183687 := bstep (se 1 (by rfl) ⟨15137765, by rfl⟩ : syracuseStep 20183687 = 30275531) B30275531
theorem B2521847 : Blo 1048611 2521847 := bstep (se 1 (by rfl) ⟨1891385, by rfl⟩ : syracuseStep 2521847 = 3782771) B3782771
theorem B2882429 : Blo 1048611 2882429 := bstep (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) B1080911
theorem B5110715 : Blo 1048611 5110715 := bstep (se 1 (by rfl) ⟨3833036, by rfl⟩ : syracuseStep 5110715 = 7666073) B7666073
theorem B5046077 : Blo 1048611 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B1048807 : Blo 1048611 1048807 := bstep (se 1 (by rfl) ⟨786605, by rfl⟩ : syracuseStep 1048807 = 1573211) B1573211
theorem B2359583 : Blo 1048611 2359583 := bstep (se 1 (by rfl) ⟨1769687, by rfl⟩ : syracuseStep 2359583 = 3539375) B3539375
theorem B1573151 : Blo 1048611 1573151 := bstep (se 1 (by rfl) ⟨1179863, by rfl⟩ : syracuseStep 1573151 = 2359727) B2359727
theorem B1573175 : Blo 1048611 1573175 := bstep (se 1 (by rfl) ⟨1179881, by rfl⟩ : syracuseStep 1573175 = 2359763) B2359763
theorem B1573247 : Blo 1048611 1573247 := bstep (se 1 (by rfl) ⟨1179935, by rfl⟩ : syracuseStep 1573247 = 2359871) B2359871
theorem B1048959 : Blo 1048611 1048959 := bstep (se 1 (by rfl) ⟨786719, by rfl⟩ : syracuseStep 1048959 = 1573439) B1573439
theorem B2392507 : Blo 1048611 2392507 := bstep (se 1 (by rfl) ⟨1794380, by rfl⟩ : syracuseStep 2392507 = 3588761) B3588761
theorem B1573319 : Blo 1048611 1573319 := bstep (se 1 (by rfl) ⟨1179989, by rfl⟩ : syracuseStep 1573319 = 2359979) B2359979
theorem B1180111 : Blo 1048611 1180111 := bstep (se 1 (by rfl) ⟨885083, by rfl⟩ : syracuseStep 1180111 = 1770167) B1770167
theorem B1049039 : Blo 1048611 1049039 := bstep (se 1 (by rfl) ⟨786779, by rfl⟩ : syracuseStep 1049039 = 1573559) B1573559
theorem B8520187 : Blo 1048611 8520187 := bstep (se 1 (by rfl) ⟨6390140, by rfl⟩ : syracuseStep 8520187 = 12780281) B12780281
theorem B1770079 : Blo 1048611 1770079 := bstep (se 1 (by rfl) ⟨1327559, by rfl⟩ : syracuseStep 1770079 = 2655119) B2655119
theorem B1049191 : Blo 1048611 1049191 := bstep (se 1 (by rfl) ⟨786893, by rfl⟩ : syracuseStep 1049191 = 1573787) B1573787
theorem B4260481 : Blo 1048611 4260481 := bstep (se 2 (by rfl) ⟨1597680, by rfl⟩ : syracuseStep 4260481 = 3195361) B3195361
theorem B1573673 : Blo 1048611 1573673 := bstep (se 2 (by rfl) ⟨590127, by rfl⟩ : syracuseStep 1573673 = 1180255) B1180255
theorem B1573679 : Blo 1048611 1573679 := bstep (se 1 (by rfl) ⟨1180259, by rfl⟩ : syracuseStep 1573679 = 2360519) B2360519
theorem B1049455 : Blo 1048611 1049455 := bstep (se 1 (by rfl) ⟨787091, by rfl⟩ : syracuseStep 1049455 = 1574183) B1574183
theorem B2360231 : Blo 1048611 2360231 := bstep (se 1 (by rfl) ⟨1770173, by rfl⟩ : syracuseStep 2360231 = 3540347) B3540347
theorem B1573799 : Blo 1048611 1573799 := bstep (se 1 (by rfl) ⟨1180349, by rfl⟩ : syracuseStep 1573799 = 2360699) B2360699
theorem B1049511 : Blo 1048611 1049511 := bstep (se 1 (by rfl) ⟨787133, by rfl⟩ : syracuseStep 1049511 = 1574267) B1574267
theorem B2524115 : Blo 1048611 2524115 := bstep (se 1 (by rfl) ⟨1893086, by rfl⟩ : syracuseStep 2524115 = 3786173) B3786173
theorem B1770491 : Blo 1048611 1770491 := bstep (se 1 (by rfl) ⟨1327868, by rfl⟩ : syracuseStep 1770491 = 2655737) B2655737
theorem B1573883 : Blo 1048611 1573883 := bstep (se 1 (by rfl) ⟨1180412, by rfl⟩ : syracuseStep 1573883 = 2360825) B2360825
theorem B1049595 : Blo 1048611 1049595 := bstep (se 1 (by rfl) ⟨787196, by rfl⟩ : syracuseStep 1049595 = 1574393) B1574393
theorem B1573943 : Blo 1048611 1573943 := bstep (se 1 (by rfl) ⟨1180457, by rfl⟩ : syracuseStep 1573943 = 2360915) B2360915
theorem B1049663 : Blo 1048611 1049663 := bstep (se 1 (by rfl) ⟨787247, by rfl⟩ : syracuseStep 1049663 = 1574495) B1574495
theorem B1574063 : Blo 1048611 1574063 := bstep (se 1 (by rfl) ⟨1180547, by rfl⟩ : syracuseStep 1574063 = 2361095) B2361095
theorem B1049807 : Blo 1048611 1049807 := bstep (se 1 (by rfl) ⟨787355, by rfl⟩ : syracuseStep 1049807 = 1574711) B1574711
theorem B1181083 : Blo 1048611 1181083 := bstep (se 1 (by rfl) ⟨885812, by rfl⟩ : syracuseStep 1181083 = 1771625) B1771625
theorem B1050011 : Blo 1048611 1050011 := bstep (se 1 (by rfl) ⟨787508, by rfl⟩ : syracuseStep 1050011 = 1575017) B1575017
theorem B1770923 : Blo 1048611 1770923 := bstep (se 1 (by rfl) ⟨1328192, by rfl⟩ : syracuseStep 1770923 = 2656385) B2656385
theorem B497845763 : Blo 1048611 497845763 := bstep (se 1 (by rfl) ⟨373384322, by rfl⟩ : syracuseStep 497845763 = 746768645) B746768645
theorem B1574471 : Blo 1048611 1574471 := bstep (se 1 (by rfl) ⟨1180853, by rfl⟩ : syracuseStep 1574471 = 2361707) B2361707
theorem B3540563 : Blo 1048611 3540563 := bstep (se 1 (by rfl) ⟨2655422, by rfl⟩ : syracuseStep 3540563 = 5310845) B5310845
theorem B1050223 : Blo 1048611 1050223 := bstep (se 1 (by rfl) ⟨787667, by rfl⟩ : syracuseStep 1050223 = 1575335) B1575335
theorem B1574567 : Blo 1048611 1574567 := bstep (se 1 (by rfl) ⟨1180925, by rfl⟩ : syracuseStep 1574567 = 2361851) B2361851
theorem B1050279 : Blo 1048611 1050279 := bstep (se 1 (by rfl) ⟨787709, by rfl⟩ : syracuseStep 1050279 = 1575419) B1575419
theorem B1574651 : Blo 1048611 1574651 := bstep (se 1 (by rfl) ⟨1180988, by rfl⟩ : syracuseStep 1574651 = 2361977) B2361977
theorem B1050363 : Blo 1048611 1050363 := bstep (se 1 (by rfl) ⟨787772, by rfl⟩ : syracuseStep 1050363 = 1575545) B1575545
theorem B1574687 : Blo 1048611 1574687 := bstep (se 1 (by rfl) ⟨1181015, by rfl⟩ : syracuseStep 1574687 = 2362031) B2362031
theorem B1050399 : Blo 1048611 1050399 := bstep (se 1 (by rfl) ⟨787799, by rfl⟩ : syracuseStep 1050399 = 1575599) B1575599
theorem B7669559 : Blo 1048611 7669559 := bstep (se 1 (by rfl) ⟨5752169, by rfl⟩ : syracuseStep 7669559 = 11504339) B11504339
theorem B1050431 : Blo 1048611 1050431 := bstep (se 1 (by rfl) ⟨787823, by rfl⟩ : syracuseStep 1050431 = 1575647) B1575647
theorem B2361167 : Blo 1048611 2361167 := bstep (se 1 (by rfl) ⟨1770875, by rfl⟩ : syracuseStep 2361167 = 3541751) B3541751
theorem B1574735 : Blo 1048611 1574735 := bstep (se 1 (by rfl) ⟨1181051, by rfl⟩ : syracuseStep 1574735 = 2362103) B2362103
theorem B19171151 : Blo 1048611 19171151 := bstep (se 1 (by rfl) ⟨14378363, by rfl⟩ : syracuseStep 19171151 = 28756727) B28756727
theorem B3540833 : Blo 1048611 3540833 := bstep (se 2 (by rfl) ⟨1327812, by rfl⟩ : syracuseStep 3540833 = 2655625) B2655625
theorem B2361185 : Blo 1048611 2361185 := bstep (se 2 (by rfl) ⟨885444, by rfl⟩ : syracuseStep 2361185 = 1770889) B1770889
theorem B1771463 : Blo 1048611 1771463 := bstep (se 1 (by rfl) ⟨1328597, by rfl⟩ : syracuseStep 1771463 = 2657195) B2657195
theorem B1574855 : Blo 1048611 1574855 := bstep (se 1 (by rfl) ⟨1181141, by rfl⟩ : syracuseStep 1574855 = 2362283) B2362283
theorem B1050607 : Blo 1048611 1050607 := bstep (se 1 (by rfl) ⟨787955, by rfl⟩ : syracuseStep 1050607 = 1575911) B1575911
theorem B1050779 : Blo 1048611 1050779 := bstep (se 1 (by rfl) ⟨788084, by rfl⟩ : syracuseStep 1050779 = 1576169) B1576169
theorem B1050815 : Blo 1048611 1050815 := bstep (se 1 (by rfl) ⟨788111, by rfl⟩ : syracuseStep 1050815 = 1576223) B1576223
theorem B1771753 : Blo 1048611 1771753 := bstep (se 2 (by rfl) ⟨664407, by rfl⟩ : syracuseStep 1771753 = 1328815) B1328815
theorem B1575209 : Blo 1048611 1575209 := bstep (se 2 (by rfl) ⟨590703, by rfl⟩ : syracuseStep 1575209 = 1181407) B1181407
theorem B1575215 : Blo 1048611 1575215 := bstep (se 1 (by rfl) ⟨1181411, by rfl⟩ : syracuseStep 1575215 = 2362823) B2362823
theorem B1050927 : Blo 1048611 1050927 := bstep (se 1 (by rfl) ⟨788195, by rfl⟩ : syracuseStep 1050927 = 1576391) B1576391
theorem B2361761 : Blo 1048611 2361761 := bstep (se 2 (by rfl) ⟨885660, by rfl⟩ : syracuseStep 2361761 = 1771321) B1771321
theorem B11962889 : Blo 1048611 11962889 := bstep (se 2 (by rfl) ⟨4486083, by rfl⟩ : syracuseStep 11962889 = 8972167) B8972167
theorem B1182235 : Blo 1048611 1182235 := bstep (se 1 (by rfl) ⟨886676, by rfl⟩ : syracuseStep 1182235 = 1773353) B1773353
theorem B1051163 : Blo 1048611 1051163 := bstep (se 1 (by rfl) ⟨788372, by rfl⟩ : syracuseStep 1051163 = 1576745) B1576745
theorem B5311007 : Blo 1048611 5311007 := bstep (se 1 (by rfl) ⟨3983255, by rfl⟩ : syracuseStep 5311007 = 7966511) B7966511
theorem B3541535 : Blo 1048611 3541535 := bstep (se 1 (by rfl) ⟨2656151, by rfl⟩ : syracuseStep 3541535 = 5312303) B5312303
theorem B2361887 : Blo 1048611 2361887 := bstep (se 1 (by rfl) ⟨1771415, by rfl⟩ : syracuseStep 2361887 = 3542831) B3542831
theorem B1575455 : Blo 1048611 1575455 := bstep (se 1 (by rfl) ⟨1181591, by rfl⟩ : syracuseStep 1575455 = 2363183) B2363183
theorem B1051167 : Blo 1048611 1051167 := bstep (se 1 (by rfl) ⟨788375, by rfl⟩ : syracuseStep 1051167 = 1576751) B1576751
theorem B7572113 : Blo 1048611 7572113 := bstep (se 2 (by rfl) ⟨2839542, by rfl⟩ : syracuseStep 7572113 = 5679085) B5679085
theorem B1772219 : Blo 1048611 1772219 := bstep (se 1 (by rfl) ⟨1329164, by rfl⟩ : syracuseStep 1772219 = 2658329) B2658329
theorem B28773143 : Blo 1048611 28773143 := bstep (se 1 (by rfl) ⟨21579857, by rfl⟩ : syracuseStep 28773143 = 43159715) B43159715
theorem B1051483 : Blo 1048611 1051483 := bstep (se 1 (by rfl) ⟨788612, by rfl⟩ : syracuseStep 1051483 = 1577225) B1577225
theorem B1575839 : Blo 1048611 1575839 := bstep (se 1 (by rfl) ⟨1181879, by rfl⟩ : syracuseStep 1575839 = 2363759) B2363759
theorem B1051551 : Blo 1048611 1051551 := bstep (se 1 (by rfl) ⟨788663, by rfl⟩ : syracuseStep 1051551 = 1577327) B1577327
theorem B1575887 : Blo 1048611 1575887 := bstep (se 1 (by rfl) ⟨1181915, by rfl⟩ : syracuseStep 1575887 = 2363831) B2363831
theorem B1575977 : Blo 1048611 1575977 := bstep (se 2 (by rfl) ⟨590991, by rfl⟩ : syracuseStep 1575977 = 1181983) B1181983
theorem B1575983 : Blo 1048611 1575983 := bstep (se 1 (by rfl) ⟨1181987, by rfl⟩ : syracuseStep 1575983 = 2363975) B2363975
theorem B1051695 : Blo 1048611 1051695 := bstep (se 1 (by rfl) ⟨788771, by rfl⟩ : syracuseStep 1051695 = 1577543) B1577543
theorem B1576007 : Blo 1048611 1576007 := bstep (se 1 (by rfl) ⟨1182005, by rfl⟩ : syracuseStep 1576007 = 2364011) B2364011
theorem B1051719 : Blo 1048611 1051719 := bstep (se 1 (by rfl) ⟨788789, by rfl⟩ : syracuseStep 1051719 = 1577579) B1577579
theorem B1051871 : Blo 1048611 1051871 := bstep (se 1 (by rfl) ⟨788903, by rfl⟩ : syracuseStep 1051871 = 1577807) B1577807
theorem B1576271 : Blo 1048611 1576271 := bstep (se 1 (by rfl) ⟨1182203, by rfl⟩ : syracuseStep 1576271 = 2364407) B2364407
theorem B1641839 : Blo 1048611 1641839 := bstep (se 1 (by rfl) ⟨1231379, by rfl⟩ : syracuseStep 1641839 = 2462759) B2462759
theorem B1576361 : Blo 1048611 1576361 := bstep (se 2 (by rfl) ⟨591135, by rfl⟩ : syracuseStep 1576361 = 1182271) B1182271
theorem B1183207 : Blo 1048611 1183207 := bstep (se 1 (by rfl) ⟨887405, by rfl⟩ : syracuseStep 1183207 = 1774811) B1774811
theorem B1052135 : Blo 1048611 1052135 := bstep (se 1 (by rfl) ⟨789101, by rfl⟩ : syracuseStep 1052135 = 1578203) B1578203
theorem B1576511 : Blo 1048611 1576511 := bstep (se 1 (by rfl) ⟨1182383, by rfl⟩ : syracuseStep 1576511 = 2364767) B2364767
theorem B1052251 : Blo 1048611 1052251 := bstep (se 1 (by rfl) ⟨789188, by rfl⟩ : syracuseStep 1052251 = 1578377) B1578377
theorem B10784431 : Blo 1048611 10784431 := bstep (se 1 (by rfl) ⟨8088323, by rfl⟩ : syracuseStep 10784431 = 16176647) B16176647
theorem B8523559 : Blo 1048611 8523559 := bstep (se 1 (by rfl) ⟨6392669, by rfl⟩ : syracuseStep 8523559 = 12785339) B12785339
theorem B1576775 : Blo 1048611 1576775 := bstep (se 1 (by rfl) ⟨1182581, by rfl⟩ : syracuseStep 1576775 = 2365163) B2365163
theorem B1052487 : Blo 1048611 1052487 := bstep (se 1 (by rfl) ⟨789365, by rfl⟩ : syracuseStep 1052487 = 1578731) B1578731
theorem B4493177 : Blo 1048611 4493177 := bstep (se 2 (by rfl) ⟨1684941, by rfl⟩ : syracuseStep 4493177 = 3369883) B3369883
theorem B3542939 : Blo 1048611 3542939 := bstep (se 1 (by rfl) ⟨2657204, by rfl⟩ : syracuseStep 3542939 = 5314409) B5314409
theorem B2363291 : Blo 1048611 2363291 := bstep (se 1 (by rfl) ⟨1772468, by rfl⟩ : syracuseStep 2363291 = 3544937) B3544937
theorem B1576859 : Blo 1048611 1576859 := bstep (se 1 (by rfl) ⟨1182644, by rfl⟩ : syracuseStep 1576859 = 2365289) B2365289
theorem B1773535 : Blo 1048611 1773535 := bstep (se 1 (by rfl) ⟨1330151, by rfl⟩ : syracuseStep 1773535 = 2660303) B2660303
theorem B1183711 : Blo 1048611 1183711 := bstep (se 1 (by rfl) ⟨887783, by rfl⟩ : syracuseStep 1183711 = 1775567) B1775567
theorem B2658491 : Blo 1048611 2658491 := bstep (se 1 (by rfl) ⟨1993868, by rfl⟩ : syracuseStep 2658491 = 3987737) B3987737
theorem B2363579 : Blo 1048611 2363579 := bstep (se 1 (by rfl) ⟨1772684, by rfl⟩ : syracuseStep 2363579 = 3545369) B3545369
theorem B1577423 : Blo 1048611 1577423 := bstep (se 1 (by rfl) ⟨1183067, by rfl⟩ : syracuseStep 1577423 = 2366135) B2366135
theorem B1577465 : Blo 1048611 1577465 := bstep (se 2 (by rfl) ⟨591549, by rfl⟩ : syracuseStep 1577465 = 1183099) B1183099
theorem B1577567 : Blo 1048611 1577567 := bstep (se 1 (by rfl) ⟨1183175, by rfl⟩ : syracuseStep 1577567 = 2366351) B2366351
theorem B1774183 : Blo 1048611 1774183 := bstep (se 1 (by rfl) ⟨1330637, by rfl⟩ : syracuseStep 1774183 = 2661275) B2661275
theorem B2658977 : Blo 1048611 2658977 := bstep (se 2 (by rfl) ⟨997116, by rfl⟩ : syracuseStep 2658977 = 1994233) B1994233
theorem B2364065 : Blo 1048611 2364065 := bstep (se 2 (by rfl) ⟨886524, by rfl⟩ : syracuseStep 2364065 = 1773049) B1773049
theorem B1774345 : Blo 1048611 1774345 := bstep (se 2 (by rfl) ⟨665379, by rfl⟩ : syracuseStep 1774345 = 1330759) B1330759
theorem B3544073 : Blo 1048611 3544073 := bstep (se 2 (by rfl) ⟨1329027, by rfl⟩ : syracuseStep 3544073 = 2658055) B2658055
theorem B2364425 : Blo 1048611 2364425 := bstep (se 2 (by rfl) ⟨886659, by rfl⟩ : syracuseStep 2364425 = 1773319) B1773319
theorem B5313599 : Blo 1048611 5313599 := bstep (se 1 (by rfl) ⟨3985199, by rfl⟩ : syracuseStep 5313599 = 7970399) B7970399
theorem B3544127 : Blo 1048611 3544127 := bstep (se 1 (by rfl) ⟨2658095, by rfl⟩ : syracuseStep 3544127 = 5316191) B5316191
theorem B2364479 : Blo 1048611 2364479 := bstep (se 1 (by rfl) ⟨1773359, by rfl⟩ : syracuseStep 2364479 = 3546719) B3546719
theorem B1578047 : Blo 1048611 1578047 := bstep (se 1 (by rfl) ⟨1183535, by rfl⟩ : syracuseStep 1578047 = 2367071) B2367071
theorem B1578089 : Blo 1048611 1578089 := bstep (se 2 (by rfl) ⟨591783, by rfl⟩ : syracuseStep 1578089 = 1183567) B1183567
theorem B1578191 : Blo 1048611 1578191 := bstep (se 1 (by rfl) ⟨1183643, by rfl⟩ : syracuseStep 1578191 = 2367287) B2367287
theorem B8525087 : Blo 1048611 8525087 := bstep (se 1 (by rfl) ⟨6393815, by rfl⟩ : syracuseStep 8525087 = 12787631) B12787631
theorem B2659675 : Blo 1048611 2659675 := bstep (se 1 (by rfl) ⟨1994756, by rfl⟩ : syracuseStep 2659675 = 3989513) B3989513
theorem B1774939 : Blo 1048611 1774939 := bstep (se 1 (by rfl) ⟨1331204, by rfl⟩ : syracuseStep 1774939 = 2662409) B2662409
theorem B1578395 : Blo 1048611 1578395 := bstep (se 1 (by rfl) ⟨1183796, by rfl⟩ : syracuseStep 1578395 = 2367593) B2367593
theorem B1578617 : Blo 1048611 1578617 := bstep (se 2 (by rfl) ⟨591981, by rfl⟩ : syracuseStep 1578617 = 1183963) B1183963
theorem B1119911 : Blo 1048611 1119911 := bstep (se 1 (by rfl) ⟨839933, by rfl⟩ : syracuseStep 1119911 = 1679867) B1679867
theorem B1578719 : Blo 1048611 1578719 := bstep (se 1 (by rfl) ⟨1184039, by rfl⟩ : syracuseStep 1578719 = 2368079) B2368079
theorem B1578815 : Blo 1048611 1578815 := bstep (se 1 (by rfl) ⟨1184111, by rfl⟩ : syracuseStep 1578815 = 2368223) B2368223
theorem B2365415 : Blo 1048611 2365415 := bstep (se 1 (by rfl) ⟨1774061, by rfl⟩ : syracuseStep 2365415 = 3548123) B3548123
theorem B2365433 : Blo 1048611 2365433 := bstep (se 2 (by rfl) ⟨887037, by rfl⟩ : syracuseStep 2365433 = 1774075) B1774075
theorem B6068225 : Blo 1048611 6068225 := bstep (se 2 (by rfl) ⟨2275584, by rfl⟩ : syracuseStep 6068225 = 4551169) B4551169
theorem B2660435 : Blo 1048611 2660435 := bstep (se 1 (by rfl) ⟨1995326, by rfl⟩ : syracuseStep 2660435 = 3990653) B3990653
theorem B2365523 : Blo 1048611 2365523 := bstep (se 1 (by rfl) ⟨1774142, by rfl⟩ : syracuseStep 2365523 = 3548285) B3548285
theorem B37427293 : Blo 1048611 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B2365595 : Blo 1048611 2365595 := bstep (se 1 (by rfl) ⟨1774196, by rfl⟩ : syracuseStep 2365595 = 3548393) B3548393
theorem B2365703 : Blo 1048611 2365703 := bstep (se 1 (by rfl) ⟨1774277, by rfl⟩ : syracuseStep 2365703 = 3548555) B3548555
theorem B1775911 : Blo 1048611 1775911 := bstep (se 1 (by rfl) ⟨1331933, by rfl⟩ : syracuseStep 1775911 = 2663867) B2663867
theorem B2660921 : Blo 1048611 2660921 := bstep (se 2 (by rfl) ⟨997845, by rfl⟩ : syracuseStep 2660921 = 1995691) B1995691
theorem B2366009 : Blo 1048611 2366009 := bstep (se 2 (by rfl) ⟨887253, by rfl⟩ : syracuseStep 2366009 = 1774507) B1774507
theorem B2366729 : Blo 1048611 2366729 := bstep (se 2 (by rfl) ⟨887523, by rfl⟩ : syracuseStep 2366729 = 1775047) B1775047
theorem B32841395 : Blo 1048611 32841395 := bstep (se 1 (by rfl) ⟨24631046, by rfl⟩ : syracuseStep 32841395 = 49262093) B49262093
theorem B2989811 : Blo 1048611 2989811 := bstep (se 1 (by rfl) ⟨2242358, by rfl⟩ : syracuseStep 2989811 = 4484717) B4484717
theorem B3546935 : Blo 1048611 3546935 := bstep (se 1 (by rfl) ⟨2660201, by rfl⟩ : syracuseStep 3546935 = 5320403) B5320403
theorem B2662267 : Blo 1048611 2662267 := bstep (se 1 (by rfl) ⟨1996700, by rfl⟩ : syracuseStep 2662267 = 3993401) B3993401
theorem B51060779 : Blo 1048611 51060779 := bstep (se 1 (by rfl) ⟨38295584, by rfl⟩ : syracuseStep 51060779 = 76591169) B76591169
theorem B3547367 : Blo 1048611 3547367 := bstep (se 1 (by rfl) ⟨2660525, by rfl⟩ : syracuseStep 3547367 = 5321051) B5321051
theorem B2367719 : Blo 1048611 2367719 := bstep (se 1 (by rfl) ⟨1775789, by rfl⟩ : syracuseStep 2367719 = 3551579) B3551579
theorem B2662753 : Blo 1048611 2662753 := bstep (se 2 (by rfl) ⟨998532, by rfl⟩ : syracuseStep 2662753 = 1997065) B1997065
theorem B3547961 : Blo 1048611 3547961 := bstep (se 2 (by rfl) ⟨1330485, by rfl⟩ : syracuseStep 3547961 = 2660971) B2660971
theorem B2368313 : Blo 1048611 2368313 := bstep (se 2 (by rfl) ⟨888117, by rfl⟩ : syracuseStep 2368313 = 1776235) B1776235
theorem B3548015 : Blo 1048611 3548015 := bstep (se 1 (by rfl) ⟨2661011, by rfl⟩ : syracuseStep 3548015 = 5322023) B5322023
theorem B5317487 : Blo 1048611 5317487 := bstep (se 1 (by rfl) ⟨3988115, by rfl⟩ : syracuseStep 5317487 = 7976231) B7976231
theorem B2368367 : Blo 1048611 2368367 := bstep (se 1 (by rfl) ⟨1776275, by rfl⟩ : syracuseStep 2368367 = 3552551) B3552551
theorem B6824989 : Blo 1048611 6824989 := bstep (se 3 (by rfl) ⟨1279685, by rfl⟩ : syracuseStep 6824989 = 2559371) B2559371
theorem B2991293 : Blo 1048611 2991293 := bstep (se 3 (by rfl) ⟨560867, by rfl⟩ : syracuseStep 2991293 = 1121735) B1121735
theorem B5973587 : Blo 1048611 5973587 := bstep (se 1 (by rfl) ⟨4480190, by rfl⟩ : syracuseStep 5973587 = 8960381) B8960381
theorem B3548825 : Blo 1048611 3548825 := bstep (se 2 (by rfl) ⟨1330809, by rfl⟩ : syracuseStep 3548825 = 2661619) B2661619
theorem B1681231 : Blo 1048611 1681231 := bstep (se 1 (by rfl) ⟨1260923, by rfl⟩ : syracuseStep 1681231 = 2521847) B2521847
theorem B3549419 : Blo 1048611 3549419 := bstep (se 1 (by rfl) ⟨2662064, by rfl⟩ : syracuseStep 3549419 = 5324129) B5324129
theorem B35466131 : Blo 1048611 35466131 := bstep (se 1 (by rfl) ⟨26599598, by rfl⟩ : syracuseStep 35466131 = 53199197) B53199197
theorem B3550715 : Blo 1048611 3550715 := bstep (se 1 (by rfl) ⟨2663036, by rfl⟩ : syracuseStep 3550715 = 5326073) B5326073
theorem B6729331 : Blo 1048611 6729331 := bstep (se 1 (by rfl) ⟨5046998, by rfl⟩ : syracuseStep 6729331 = 10093997) B10093997
theorem B3550877 : Blo 1048611 3550877 := bstep (se 3 (by rfl) ⟨665789, by rfl⟩ : syracuseStep 3550877 = 1331579) B1331579
theorem B3026911 : Blo 1048611 3026911 := bstep (se 1 (by rfl) ⟨2270183, by rfl⟩ : syracuseStep 3026911 = 4540367) B4540367
theorem B16166915 : Blo 1048611 16166915 := bstep (se 1 (by rfl) ⟨12125186, by rfl⟩ : syracuseStep 16166915 = 24250373) B24250373
theorem B3551417 : Blo 1048611 3551417 := bstep (se 2 (by rfl) ⟨1331781, by rfl⟩ : syracuseStep 3551417 = 2663563) B2663563
theorem B2995643 : Blo 1048611 2995643 := bstep (se 1 (by rfl) ⟨2246732, by rfl⟩ : syracuseStep 2995643 = 4493465) B4493465
theorem B1685063 : Blo 1048611 1685063 := bstep (se 1 (by rfl) ⟨1263797, by rfl⟩ : syracuseStep 1685063 = 2527595) B2527595
theorem B5977961 : Blo 1048611 5977961 := bstep (se 2 (by rfl) ⟨2241735, by rfl⟩ : syracuseStep 5977961 = 4483471) B4483471
theorem B7583645 : Blo 1048611 7583645 := bstep (se 3 (by rfl) ⟨1421933, by rfl⟩ : syracuseStep 7583645 = 2843867) B2843867
theorem B2996669 : Blo 1048611 2996669 := bstep (se 3 (by rfl) ⟨561875, by rfl⟩ : syracuseStep 2996669 = 1123751) B1123751
theorem B4602521 : Blo 1048611 4602521 := bstep (se 2 (by rfl) ⟨1725945, by rfl⟩ : syracuseStep 4602521 = 3451891) B3451891
theorem B5126809 : Blo 1048611 5126809 := bstep (se 2 (by rfl) ⟨1922553, by rfl⟩ : syracuseStep 5126809 = 3845107) B3845107
theorem B7584455 : Blo 1048611 7584455 := bstep (se 1 (by rfl) ⟨5688341, by rfl⟩ : syracuseStep 7584455 = 11376683) B11376683
theorem B5455133 : Blo 1048611 5455133 := bstep (se 3 (by rfl) ⟨1022837, by rfl⟩ : syracuseStep 5455133 = 2045675) B2045675
theorem B11976011 : Blo 1048611 11976011 := bstep (se 1 (by rfl) ⟨8982008, by rfl⟩ : syracuseStep 11976011 = 17964017) B17964017
theorem B7585235 : Blo 1048611 7585235 := bstep (se 1 (by rfl) ⟨5688926, by rfl⟩ : syracuseStep 7585235 = 11377853) B11377853
theorem B7979147 : Blo 1048611 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B5324939 : Blo 1048611 5324939 := bstep (se 1 (by rfl) ⟨3993704, by rfl⟩ : syracuseStep 5324939 = 7987409) B7987409
theorem B12140887 : Blo 1048611 12140887 := bstep (se 1 (by rfl) ⟨9105665, by rfl⟩ : syracuseStep 12140887 = 18211331) B18211331
theorem B2834785 : Blo 1048611 2834785 := bstep (se 2 (by rfl) ⟨1063044, by rfl⟩ : syracuseStep 2834785 = 2126089) B2126089
theorem B5325263 : Blo 1048611 5325263 := bstep (se 1 (by rfl) ⟨3993947, by rfl⟩ : syracuseStep 5325263 = 7987895) B7987895
theorem B3982223 : Blo 1048611 3982223 := bstep (se 1 (by rfl) ⟨2986667, by rfl⟩ : syracuseStep 3982223 = 5973335) B5973335
theorem B5686159 : Blo 1048611 5686159 := bstep (se 1 (by rfl) ⟨4264619, by rfl⟩ : syracuseStep 5686159 = 8529239) B8529239
theorem B5981309 : Blo 1048611 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B3359951 : Blo 1048611 3359951 := bstep (se 1 (by rfl) ⟨2519963, by rfl⟩ : syracuseStep 3359951 = 5039927) B5039927
theorem B68142545 : Blo 1048611 68142545 := bstep (se 2 (by rfl) ⟨25553454, by rfl⟩ : syracuseStep 68142545 = 51106909) B51106909
theorem B8635901 : Blo 1048611 8635901 := bstep (se 3 (by rfl) ⟨1619231, by rfl⟩ : syracuseStep 8635901 = 3238463) B3238463
theorem B5326559 : Blo 1048611 5326559 := bstep (se 1 (by rfl) ⟨3994919, by rfl⟩ : syracuseStep 5326559 = 7989839) B7989839
theorem B3983165 : Blo 1048611 3983165 := bstep (se 3 (by rfl) ⟨746843, by rfl⟩ : syracuseStep 3983165 = 1493687) B1493687
theorem B5326721 : Blo 1048611 5326721 := bstep (se 2 (by rfl) ⟨1997520, by rfl⟩ : syracuseStep 5326721 = 3995041) B3995041
theorem B2836775 : Blo 1048611 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B1329691 : Blo 1048611 1329691 := bstep (se 1 (by rfl) ⟨997268, by rfl⟩ : syracuseStep 1329691 = 1994537) B1994537
theorem B3361385 : Blo 1048611 3361385 := bstep (se 2 (by rfl) ⟨1260519, by rfl⟩ : syracuseStep 3361385 = 2521039) B2521039
theorem B5327531 : Blo 1048611 5327531 := bstep (se 1 (by rfl) ⟨3995648, by rfl⟩ : syracuseStep 5327531 = 7991297) B7991297
theorem B5687995 : Blo 1048611 5687995 := bstep (se 1 (by rfl) ⟨4265996, by rfl⟩ : syracuseStep 5687995 = 8531993) B8531993
theorem B49236979 : Blo 1048611 49236979 := bstep (se 1 (by rfl) ⟨36927734, by rfl⟩ : syracuseStep 49236979 = 73855469) B73855469
theorem B186928145 : Blo 1048611 186928145 := bstep (se 2 (by rfl) ⟨70098054, by rfl⟩ : syracuseStep 186928145 = 140196109) B140196109
theorem B3591607 : Blo 1048611 3591607 := bstep (se 1 (by rfl) ⟨2693705, by rfl⟩ : syracuseStep 3591607 = 5387411) B5387411
theorem B1330663 : Blo 1048611 1330663 := bstep (se 1 (by rfl) ⟨997997, by rfl⟩ : syracuseStep 1330663 = 1995995) B1995995
theorem B3788279 : Blo 1048611 3788279 := bstep (se 1 (by rfl) ⟨2841209, by rfl⟩ : syracuseStep 3788279 = 5682419) B5682419
theorem B3362411 : Blo 1048611 3362411 := bstep (se 1 (by rfl) ⟨2521808, by rfl⟩ : syracuseStep 3362411 = 5043617) B5043617
theorem B6737737 : Blo 1048611 6737737 := bstep (se 2 (by rfl) ⟨2526651, by rfl⟩ : syracuseStep 6737737 = 5053303) B5053303
theorem B4050769 : Blo 1048611 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B3985595 : Blo 1048611 3985595 := bstep (se 1 (by rfl) ⟨2989196, by rfl⟩ : syracuseStep 3985595 = 5978393) B5978393
theorem B13455791 : Blo 1048611 13455791 := bstep (se 1 (by rfl) ⟨10091843, by rfl⟩ : syracuseStep 13455791 = 20183687) B20183687
theorem B1921619 : Blo 1048611 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B3986081 : Blo 1048611 3986081 := bstep (se 2 (by rfl) ⟨1494780, by rfl⟩ : syracuseStep 3986081 = 2989561) B2989561
theorem B10114145 : Blo 1048611 10114145 := bstep (se 2 (by rfl) ⟨3792804, by rfl⟩ : syracuseStep 10114145 = 7585609) B7585609
theorem B3364051 : Blo 1048611 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B3986779 : Blo 1048611 3986779 := bstep (se 1 (by rfl) ⟨2990084, by rfl⟩ : syracuseStep 3986779 = 5980169) B5980169
theorem B7984493 : Blo 1048611 7984493 := bstep (se 3 (by rfl) ⟨1497092, by rfl⟩ : syracuseStep 7984493 = 2994185) B2994185
theorem B1136027 : Blo 1048611 1136027 := bstep (se 1 (by rfl) ⟨852020, by rfl⟩ : syracuseStep 1136027 = 1704041) B1704041
theorem B3200411 : Blo 1048611 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B3987053 : Blo 1048611 3987053 := bstep (se 3 (by rfl) ⟨747572, by rfl⟩ : syracuseStep 3987053 = 1495145) B1495145
theorem B1890145 : Blo 1048611 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B2873225 : Blo 1048611 2873225 := bstep (se 2 (by rfl) ⟨1077459, by rfl⟩ : syracuseStep 2873225 = 2154919) B2154919
theorem B6739969 : Blo 1048611 6739969 := bstep (se 2 (by rfl) ⟨2527488, by rfl⟩ : syracuseStep 6739969 = 5054977) B5054977
theorem B4479421 : Blo 1048611 4479421 := bstep (se 3 (by rfl) ⟨839891, by rfl⟩ : syracuseStep 4479421 = 1679783) B1679783
theorem B3365513 : Blo 1048611 3365513 := bstep (se 2 (by rfl) ⟨1262067, by rfl⟩ : syracuseStep 3365513 = 2524135) B2524135
theorem B1498619 : Blo 1048611 1498619 := bstep (se 1 (by rfl) ⟨1123964, by rfl⟩ : syracuseStep 1498619 = 2247929) B2247929
theorem B12115493 : Blo 1048611 12115493 := bstep (se 4 (by rfl) ⟨1135827, by rfl⟩ : syracuseStep 12115493 = 2271655) B2271655
theorem B7986923 : Blo 1048611 7986923 := bstep (se 1 (by rfl) ⟨5990192, by rfl⟩ : syracuseStep 7986923 = 11980385) B11980385
theorem B15163139 : Blo 1048611 15163139 := bstep (se 1 (by rfl) ⟨11372354, by rfl⟩ : syracuseStep 15163139 = 22744709) B22744709
theorem B15130385 : Blo 1048611 15130385 := bstep (se 2 (by rfl) ⟨5673894, by rfl⟩ : syracuseStep 15130385 = 11347789) B11347789
theorem B6381359 : Blo 1048611 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B5988167 : Blo 1048611 5988167 := bstep (se 1 (by rfl) ⟨4491125, by rfl⟩ : syracuseStep 5988167 = 8982251) B8982251
theorem B1892251 : Blo 1048611 1892251 := bstep (se 1 (by rfl) ⟨1419188, by rfl⟩ : syracuseStep 1892251 = 2838377) B2838377
theorem B5988599 : Blo 1048611 5988599 := bstep (se 1 (by rfl) ⟨4491449, by rfl⟩ : syracuseStep 5988599 = 8982899) B8982899
theorem B10379707 : Blo 1048611 10379707 := bstep (se 1 (by rfl) ⟨7784780, by rfl⟩ : syracuseStep 10379707 = 15569561) B15569561
theorem B10084925 : Blo 1048611 10084925 := bstep (se 3 (by rfl) ⟨1890923, by rfl⟩ : syracuseStep 10084925 = 3781847) B3781847
theorem B15131771 : Blo 1048611 15131771 := bstep (se 1 (by rfl) ⟨11348828, by rfl⟩ : syracuseStep 15131771 = 22697657) B22697657
theorem B5039293 : Blo 1048611 5039293 := bstep (se 3 (by rfl) ⟨944867, by rfl⟩ : syracuseStep 5039293 = 1889735) B1889735
theorem B4252861 : Blo 1048611 4252861 := bstep (se 3 (by rfl) ⟨797411, by rfl⟩ : syracuseStep 4252861 = 1594823) B1594823
theorem B5989625 : Blo 1048611 5989625 := bstep (se 2 (by rfl) ⟨2246109, by rfl⟩ : syracuseStep 5989625 = 4492219) B4492219
theorem B1992107 : Blo 1048611 1992107 := bstep (se 1 (by rfl) ⟨1494080, by rfl⟩ : syracuseStep 1992107 = 2988161) B2988161
theorem B1894009 : Blo 1048611 1894009 := bstep (se 2 (by rfl) ⟨710253, by rfl⟩ : syracuseStep 1894009 = 1420507) B1420507
theorem B6907679 : Blo 1048611 6907679 := bstep (se 1 (by rfl) ⟨5180759, by rfl⟩ : syracuseStep 6907679 = 10361519) B10361519
theorem B7564013 : Blo 1048611 7564013 := bstep (se 3 (by rfl) ⟨1418252, by rfl⟩ : syracuseStep 7564013 = 2836505) B2836505
theorem B22703111 : Blo 1048611 22703111 := bstep (se 1 (by rfl) ⟨17027333, by rfl⟩ : syracuseStep 22703111 = 34054667) B34054667
theorem B21524363 : Blo 1048611 21524363 := bstep (se 1 (by rfl) ⟨16143272, by rfl⟩ : syracuseStep 21524363 = 32286545) B32286545
theorem B1994719 : Blo 1048611 1994719 := bstep (se 1 (by rfl) ⟨1496039, by rfl⟩ : syracuseStep 1994719 = 2992079) B2992079
theorem B6385715 : Blo 1048611 6385715 := bstep (se 1 (by rfl) ⟨4789286, by rfl⟩ : syracuseStep 6385715 = 9578573) B9578573
theorem B6811771 : Blo 1048611 6811771 := bstep (se 1 (by rfl) ⟨5108828, by rfl⟩ : syracuseStep 6811771 = 10217657) B10217657
theorem B1994939 : Blo 1048611 1994939 := bstep (se 1 (by rfl) ⟨1496204, by rfl⟩ : syracuseStep 1994939 = 2992409) B2992409
theorem B25555301 : Blo 1048611 25555301 := bstep (se 4 (by rfl) ⟨2395809, by rfl⟩ : syracuseStep 25555301 = 4791619) B4791619
theorem B1995425 : Blo 1048611 1995425 := bstep (se 2 (by rfl) ⟨748284, by rfl⟩ : syracuseStep 1995425 = 1496569) B1496569
theorem B13628573 : Blo 1048611 13628573 := bstep (se 3 (by rfl) ⟨2555357, by rfl⟩ : syracuseStep 13628573 = 5110715) B5110715
theorem B145814741 : Blo 1048611 145814741 := bstep (se 7 (by rfl) ⟨1708766, by rfl⟩ : syracuseStep 145814741 = 3417533) B3417533
theorem B5993747 : Blo 1048611 5993747 := bstep (se 1 (by rfl) ⟨4495310, by rfl⟩ : syracuseStep 5993747 = 8990621) B8990621
theorem B4486529 : Blo 1048611 4486529 := bstep (se 2 (by rfl) ⟨1682448, by rfl⟩ : syracuseStep 4486529 = 3364897) B3364897
theorem B36435419 : Blo 1048611 36435419 := bstep (se 1 (by rfl) ⟨27326564, by rfl⟩ : syracuseStep 36435419 = 54653129) B54653129
theorem B1996883 : Blo 1048611 1996883 := bstep (se 1 (by rfl) ⟨1497662, by rfl⟩ : syracuseStep 1996883 = 2995325) B2995325
theorem B5994749 : Blo 1048611 5994749 := bstep (se 3 (by rfl) ⟨1124015, by rfl⟩ : syracuseStep 5994749 = 2248031) B2248031
theorem B3996013 : Blo 1048611 3996013 := bstep (se 3 (by rfl) ⟨749252, by rfl⟩ : syracuseStep 3996013 = 1498505) B1498505
theorem B7568423 : Blo 1048611 7568423 := bstep (se 1 (by rfl) ⟨5676317, by rfl⟩ : syracuseStep 7568423 = 11352635) B11352635
theorem B2555009 : Blo 1048611 2555009 := bstep (se 2 (by rfl) ⟨958128, by rfl⟩ : syracuseStep 2555009 = 1916257) B1916257
theorem B1573055 : Blo 1048611 1573055 := bstep (se 1 (by rfl) ⟨1179791, by rfl⟩ : syracuseStep 1573055 = 2359583) B2359583
theorem B1048767 : Blo 1048611 1048767 := bstep (se 1 (by rfl) ⟨786575, by rfl⟩ : syracuseStep 1048767 = 1573151) B1573151
theorem B1048783 : Blo 1048611 1048783 := bstep (se 1 (by rfl) ⟨786587, by rfl⟩ : syracuseStep 1048783 = 1573175) B1573175
theorem B1048831 : Blo 1048611 1048831 := bstep (se 1 (by rfl) ⟨786623, by rfl⟩ : syracuseStep 1048831 = 1573247) B1573247
theorem B1048879 : Blo 1048611 1048879 := bstep (se 1 (by rfl) ⟨786659, by rfl⟩ : syracuseStep 1048879 = 1573319) B1573319
theorem B16187849 : Blo 1048611 16187849 := bstep (se 2 (by rfl) ⟨6070443, by rfl⟩ : syracuseStep 16187849 = 12140887) B12140887
theorem B1049115 : Blo 1048611 1049115 := bstep (se 1 (by rfl) ⟨786836, by rfl⟩ : syracuseStep 1049115 = 1573673) B1573673
theorem B1049119 : Blo 1048611 1049119 := bstep (se 1 (by rfl) ⟨786839, by rfl⟩ : syracuseStep 1049119 = 1573679) B1573679
theorem B2654815 : Blo 1048611 2654815 := bstep (se 1 (by rfl) ⟨1991111, by rfl⟩ : syracuseStep 2654815 = 3982223) B3982223
theorem B1573481 : Blo 1048611 1573481 := bstep (se 2 (by rfl) ⟨590055, by rfl⟩ : syracuseStep 1573481 = 1180111) B1180111
theorem B1573487 : Blo 1048611 1573487 := bstep (se 1 (by rfl) ⟨1180115, by rfl⟩ : syracuseStep 1573487 = 2360231) B2360231
theorem B1049199 : Blo 1048611 1049199 := bstep (se 1 (by rfl) ⟨786899, by rfl⟩ : syracuseStep 1049199 = 1573799) B1573799
theorem B1180327 : Blo 1048611 1180327 := bstep (se 1 (by rfl) ⟨885245, by rfl⟩ : syracuseStep 1180327 = 1770491) B1770491
theorem B1049255 : Blo 1048611 1049255 := bstep (se 1 (by rfl) ⟨786941, by rfl⟩ : syracuseStep 1049255 = 1573883) B1573883
theorem B1049295 : Blo 1048611 1049295 := bstep (se 1 (by rfl) ⟨786971, by rfl⟩ : syracuseStep 1049295 = 1573943) B1573943
theorem B1049375 : Blo 1048611 1049375 := bstep (se 1 (by rfl) ⟨787031, by rfl⟩ : syracuseStep 1049375 = 1574063) B1574063
theorem B2360105 : Blo 1048611 2360105 := bstep (se 2 (by rfl) ⟨885039, by rfl⟩ : syracuseStep 2360105 = 1770079) B1770079
theorem B1180615 : Blo 1048611 1180615 := bstep (se 1 (by rfl) ⟨885461, by rfl⟩ : syracuseStep 1180615 = 1770923) B1770923
theorem B1049647 : Blo 1048611 1049647 := bstep (se 1 (by rfl) ⟨787235, by rfl⟩ : syracuseStep 1049647 = 1574471) B1574471
theorem B2360375 : Blo 1048611 2360375 := bstep (se 1 (by rfl) ⟨1770281, by rfl⟩ : syracuseStep 2360375 = 3540563) B3540563
theorem B1049711 : Blo 1048611 1049711 := bstep (se 1 (by rfl) ⟨787283, by rfl⟩ : syracuseStep 1049711 = 1574567) B1574567
theorem B1049767 : Blo 1048611 1049767 := bstep (se 1 (by rfl) ⟨787325, by rfl⟩ : syracuseStep 1049767 = 1574651) B1574651
theorem B1049791 : Blo 1048611 1049791 := bstep (se 1 (by rfl) ⟨787343, by rfl⟩ : syracuseStep 1049791 = 1574687) B1574687
theorem B5113039 : Blo 1048611 5113039 := bstep (se 1 (by rfl) ⟨3834779, by rfl⟩ : syracuseStep 5113039 = 7669559) B7669559
theorem B2655443 : Blo 1048611 2655443 := bstep (se 1 (by rfl) ⟨1991582, by rfl⟩ : syracuseStep 2655443 = 3983165) B3983165
theorem B1574111 : Blo 1048611 1574111 := bstep (se 1 (by rfl) ⟨1180583, by rfl⟩ : syracuseStep 1574111 = 2361167) B2361167
theorem B1049823 : Blo 1048611 1049823 := bstep (se 1 (by rfl) ⟨787367, by rfl⟩ : syracuseStep 1049823 = 1574735) B1574735
theorem B12780767 : Blo 1048611 12780767 := bstep (se 1 (by rfl) ⟨9585575, by rfl⟩ : syracuseStep 12780767 = 19171151) B19171151
theorem B2360555 : Blo 1048611 2360555 := bstep (se 1 (by rfl) ⟨1770416, by rfl⟩ : syracuseStep 2360555 = 3540833) B3540833
theorem B1574123 : Blo 1048611 1574123 := bstep (se 1 (by rfl) ⟨1180592, by rfl⟩ : syracuseStep 1574123 = 2361185) B2361185
theorem B1180975 : Blo 1048611 1180975 := bstep (se 1 (by rfl) ⟨885731, by rfl⟩ : syracuseStep 1180975 = 1771463) B1771463
theorem B1049903 : Blo 1048611 1049903 := bstep (se 1 (by rfl) ⟨787427, by rfl⟩ : syracuseStep 1049903 = 1574855) B1574855
theorem B1050139 : Blo 1048611 1050139 := bstep (se 1 (by rfl) ⟨787604, by rfl⟩ : syracuseStep 1050139 = 1575209) B1575209
theorem B1050143 : Blo 1048611 1050143 := bstep (se 1 (by rfl) ⟨787607, by rfl⟩ : syracuseStep 1050143 = 1575215) B1575215
theorem B6719057 : Blo 1048611 6719057 := bstep (se 2 (by rfl) ⟨2519646, by rfl⟩ : syracuseStep 6719057 = 5039293) B5039293
theorem B5670481 : Blo 1048611 5670481 := bstep (se 2 (by rfl) ⟨2126430, by rfl⟩ : syracuseStep 5670481 = 4252861) B4252861
theorem B1574507 : Blo 1048611 1574507 := bstep (se 1 (by rfl) ⟨1180880, by rfl⟩ : syracuseStep 1574507 = 2361761) B2361761
theorem B3540671 : Blo 1048611 3540671 := bstep (se 1 (by rfl) ⟨2655503, by rfl⟩ : syracuseStep 3540671 = 5311007) B5311007
theorem B2361023 : Blo 1048611 2361023 := bstep (se 1 (by rfl) ⟨1770767, by rfl⟩ : syracuseStep 2361023 = 3541535) B3541535
theorem B1574591 : Blo 1048611 1574591 := bstep (se 1 (by rfl) ⟨1180943, by rfl⟩ : syracuseStep 1574591 = 2361887) B2361887
theorem B1050303 : Blo 1048611 1050303 := bstep (se 1 (by rfl) ⟨787727, by rfl⟩ : syracuseStep 1050303 = 1575455) B1575455
theorem B5048075 : Blo 1048611 5048075 := bstep (se 1 (by rfl) ⟨3786056, by rfl⟩ : syracuseStep 5048075 = 7572113) B7572113
theorem B1181479 : Blo 1048611 1181479 := bstep (se 1 (by rfl) ⟨886109, by rfl⟩ : syracuseStep 1181479 = 1772219) B1772219
theorem B1574777 : Blo 1048611 1574777 := bstep (se 2 (by rfl) ⟨590541, by rfl⟩ : syracuseStep 1574777 = 1181083) B1181083
theorem B1050559 : Blo 1048611 1050559 := bstep (se 1 (by rfl) ⟨787919, by rfl⟩ : syracuseStep 1050559 = 1575839) B1575839
theorem B1050591 : Blo 1048611 1050591 := bstep (se 1 (by rfl) ⟨787943, by rfl⟩ : syracuseStep 1050591 = 1575887) B1575887
theorem B124618763 : Blo 1048611 124618763 := bstep (se 1 (by rfl) ⟨93464072, by rfl⟩ : syracuseStep 124618763 = 186928145) B186928145
theorem B1050651 : Blo 1048611 1050651 := bstep (se 1 (by rfl) ⟨787988, by rfl⟩ : syracuseStep 1050651 = 1575977) B1575977
theorem B1050655 : Blo 1048611 1050655 := bstep (se 1 (by rfl) ⟨787991, by rfl⟩ : syracuseStep 1050655 = 1575983) B1575983
theorem B1050671 : Blo 1048611 1050671 := bstep (se 1 (by rfl) ⟨788003, by rfl⟩ : syracuseStep 1050671 = 1576007) B1576007
theorem B2525345 : Blo 1048611 2525345 := bstep (se 2 (by rfl) ⟨947004, by rfl⟩ : syracuseStep 2525345 = 1894009) B1894009
theorem B1050847 : Blo 1048611 1050847 := bstep (se 1 (by rfl) ⟨788135, by rfl⟩ : syracuseStep 1050847 = 1576271) B1576271
theorem B1050907 : Blo 1048611 1050907 := bstep (se 1 (by rfl) ⟨788180, by rfl⟩ : syracuseStep 1050907 = 1576361) B1576361
theorem B2525519 : Blo 1048611 2525519 := bstep (se 1 (by rfl) ⟨1894139, by rfl⟩ : syracuseStep 2525519 = 3788279) B3788279
theorem B1051007 : Blo 1048611 1051007 := bstep (se 1 (by rfl) ⟨788255, by rfl⟩ : syracuseStep 1051007 = 1576511) B1576511
theorem B1051183 : Blo 1048611 1051183 := bstep (se 1 (by rfl) ⟨788387, by rfl⟩ : syracuseStep 1051183 = 1576775) B1576775
theorem B2361959 : Blo 1048611 2361959 := bstep (se 1 (by rfl) ⟨1771469, by rfl⟩ : syracuseStep 2361959 = 3542939) B3542939
theorem B1575527 : Blo 1048611 1575527 := bstep (se 1 (by rfl) ⟨1181645, by rfl⟩ : syracuseStep 1575527 = 2363291) B2363291
theorem B1051239 : Blo 1048611 1051239 := bstep (se 1 (by rfl) ⟨788429, by rfl⟩ : syracuseStep 1051239 = 1576859) B1576859
theorem B2657063 : Blo 1048611 2657063 := bstep (se 1 (by rfl) ⟨1992797, by rfl⟩ : syracuseStep 2657063 = 3985595) B3985595
theorem B1772327 : Blo 1048611 1772327 := bstep (se 1 (by rfl) ⟨1329245, by rfl⟩ : syracuseStep 1772327 = 2658491) B2658491
theorem B1575719 : Blo 1048611 1575719 := bstep (se 1 (by rfl) ⟨1181789, by rfl⟩ : syracuseStep 1575719 = 2363579) B2363579
theorem B1051615 : Blo 1048611 1051615 := bstep (se 1 (by rfl) ⟨788711, by rfl⟩ : syracuseStep 1051615 = 1577423) B1577423
theorem B2362337 : Blo 1048611 2362337 := bstep (se 2 (by rfl) ⟨885876, by rfl⟩ : syracuseStep 2362337 = 1771753) B1771753
theorem B1051643 : Blo 1048611 1051643 := bstep (se 1 (by rfl) ⟨788732, by rfl⟩ : syracuseStep 1051643 = 1577465) B1577465
theorem B1281079 : Blo 1048611 1281079 := bstep (se 1 (by rfl) ⟨960809, by rfl⟩ : syracuseStep 1281079 = 1921619) B1921619
theorem B1051711 : Blo 1048611 1051711 := bstep (se 1 (by rfl) ⟨788783, by rfl⟩ : syracuseStep 1051711 = 1577567) B1577567
theorem B2657387 : Blo 1048611 2657387 := bstep (se 1 (by rfl) ⟨1993040, by rfl⟩ : syracuseStep 2657387 = 3986081) B3986081
theorem B1772651 : Blo 1048611 1772651 := bstep (se 1 (by rfl) ⟨1329488, by rfl⟩ : syracuseStep 1772651 = 2658977) B2658977
theorem B1576043 : Blo 1048611 1576043 := bstep (se 1 (by rfl) ⟨1182032, by rfl⟩ : syracuseStep 1576043 = 2364065) B2364065
theorem B2362715 : Blo 1048611 2362715 := bstep (se 1 (by rfl) ⟨1772036, by rfl⟩ : syracuseStep 2362715 = 3544073) B3544073
theorem B1576283 : Blo 1048611 1576283 := bstep (se 1 (by rfl) ⟨1182212, by rfl⟩ : syracuseStep 1576283 = 2364425) B2364425
theorem B1772921 : Blo 1048611 1772921 := bstep (se 2 (by rfl) ⟨664845, by rfl⟩ : syracuseStep 1772921 = 1329691) B1329691
theorem B1576313 : Blo 1048611 1576313 := bstep (se 2 (by rfl) ⟨591117, by rfl⟩ : syracuseStep 1576313 = 1182235) B1182235
theorem B3542399 : Blo 1048611 3542399 := bstep (se 1 (by rfl) ⟨2656799, by rfl⟩ : syracuseStep 3542399 = 5313599) B5313599
theorem B2362751 : Blo 1048611 2362751 := bstep (se 1 (by rfl) ⟨1772063, by rfl⟩ : syracuseStep 2362751 = 3544127) B3544127
theorem B1576319 : Blo 1048611 1576319 := bstep (se 1 (by rfl) ⟨1182239, by rfl⟩ : syracuseStep 1576319 = 2364479) B2364479
theorem B1052031 : Blo 1048611 1052031 := bstep (se 1 (by rfl) ⟨789023, by rfl⟩ : syracuseStep 1052031 = 1578047) B1578047
theorem B1052059 : Blo 1048611 1052059 := bstep (se 1 (by rfl) ⟨789044, by rfl⟩ : syracuseStep 1052059 = 1578089) B1578089
theorem B1052127 : Blo 1048611 1052127 := bstep (se 1 (by rfl) ⟨789095, by rfl⟩ : syracuseStep 1052127 = 1578191) B1578191
theorem B1052263 : Blo 1048611 1052263 := bstep (se 1 (by rfl) ⟨789197, by rfl⟩ : syracuseStep 1052263 = 1578395) B1578395
theorem B2133607 : Blo 1048611 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B2658035 : Blo 1048611 2658035 := bstep (se 1 (by rfl) ⟨1993526, by rfl⟩ : syracuseStep 2658035 = 3987053) B3987053
theorem B1052411 : Blo 1048611 1052411 := bstep (se 1 (by rfl) ⟨789308, by rfl⟩ : syracuseStep 1052411 = 1578617) B1578617
theorem B1052479 : Blo 1048611 1052479 := bstep (se 1 (by rfl) ⟨789359, by rfl⟩ : syracuseStep 1052479 = 1578719) B1578719
theorem B1052543 : Blo 1048611 1052543 := bstep (se 1 (by rfl) ⟨789407, by rfl⟩ : syracuseStep 1052543 = 1578815) B1578815
theorem B1576943 : Blo 1048611 1576943 := bstep (se 1 (by rfl) ⟨1182707, by rfl⟩ : syracuseStep 1576943 = 2365415) B2365415
theorem B1576955 : Blo 1048611 1576955 := bstep (se 1 (by rfl) ⟨1182716, by rfl⟩ : syracuseStep 1576955 = 2365433) B2365433
theorem B1773623 : Blo 1048611 1773623 := bstep (se 1 (by rfl) ⟨1330217, by rfl⟩ : syracuseStep 1773623 = 2660435) B2660435
theorem B1577015 : Blo 1048611 1577015 := bstep (se 1 (by rfl) ⟨1182761, by rfl⟩ : syracuseStep 1577015 = 2365523) B2365523
theorem B1577063 : Blo 1048611 1577063 := bstep (se 1 (by rfl) ⟨1182797, by rfl⟩ : syracuseStep 1577063 = 2365595) B2365595
theorem B1577135 : Blo 1048611 1577135 := bstep (se 1 (by rfl) ⟨1182851, by rfl⟩ : syracuseStep 1577135 = 2365703) B2365703
theorem B4493501 : Blo 1048611 4493501 := bstep (se 3 (by rfl) ⟨842531, by rfl⟩ : syracuseStep 4493501 = 1685063) B1685063
theorem B1773947 : Blo 1048611 1773947 := bstep (se 1 (by rfl) ⟨1330460, by rfl⟩ : syracuseStep 1773947 = 2660921) B2660921
theorem B1577339 : Blo 1048611 1577339 := bstep (se 1 (by rfl) ⟨1183004, by rfl⟩ : syracuseStep 1577339 = 2366009) B2366009
theorem B2986429 : Blo 1048611 2986429 := bstep (se 3 (by rfl) ⟨559955, by rfl⟩ : syracuseStep 2986429 = 1119911) B1119911
theorem B4788809 : Blo 1048611 4788809 := bstep (se 2 (by rfl) ⟨1795803, by rfl⟩ : syracuseStep 4788809 = 3591607) B3591607
theorem B1774217 : Blo 1048611 1774217 := bstep (se 2 (by rfl) ⟨665331, by rfl⟩ : syracuseStep 1774217 = 1330663) B1330663
theorem B1577609 : Blo 1048611 1577609 := bstep (se 2 (by rfl) ⟨591603, by rfl⟩ : syracuseStep 1577609 = 1183207) B1183207
theorem B1577819 : Blo 1048611 1577819 := bstep (se 1 (by rfl) ⟨1183364, by rfl⟩ : syracuseStep 1577819 = 2366729) B2366729
theorem B20223053 : Blo 1048611 20223053 := bstep (se 3 (by rfl) ⟨3791822, by rfl⟩ : syracuseStep 20223053 = 7583645) B7583645
theorem B8983649 : Blo 1048611 8983649 := bstep (se 2 (by rfl) ⟨3368868, by rfl⟩ : syracuseStep 8983649 = 6737737) B6737737
theorem B21894263 : Blo 1048611 21894263 := bstep (se 1 (by rfl) ⟨16420697, by rfl⟩ : syracuseStep 21894263 = 32841395) B32841395
theorem B2364623 : Blo 1048611 2364623 := bstep (se 1 (by rfl) ⟨1773467, by rfl⟩ : syracuseStep 2364623 = 3546935) B3546935
theorem B4035881 : Blo 1048611 4035881 := bstep (se 2 (by rfl) ⟨1513455, by rfl⟩ : syracuseStep 4035881 = 3026911) B3026911
theorem B2659625 : Blo 1048611 2659625 := bstep (se 2 (by rfl) ⟨997359, by rfl⟩ : syracuseStep 2659625 = 1994719) B1994719
theorem B2364713 : Blo 1048611 2364713 := bstep (se 2 (by rfl) ⟨886767, by rfl⟩ : syracuseStep 2364713 = 1773535) B1773535
theorem B1578281 : Blo 1048611 1578281 := bstep (se 2 (by rfl) ⟨591855, by rfl⟩ : syracuseStep 1578281 = 1183711) B1183711
theorem B2364911 : Blo 1048611 2364911 := bstep (se 1 (by rfl) ⟨1773683, by rfl⟩ : syracuseStep 2364911 = 3547367) B3547367
theorem B1578479 : Blo 1048611 1578479 := bstep (se 1 (by rfl) ⟨1183859, by rfl⟩ : syracuseStep 1578479 = 2367719) B2367719
theorem B9082361 : Blo 1048611 9082361 := bstep (se 2 (by rfl) ⟨3405885, by rfl⟩ : syracuseStep 9082361 = 6811771) B6811771
theorem B6723283 : Blo 1048611 6723283 := bstep (se 1 (by rfl) ⟨5042462, by rfl⟩ : syracuseStep 6723283 = 10084925) B10084925
theorem B2365307 : Blo 1048611 2365307 := bstep (se 1 (by rfl) ⟨1773980, by rfl⟩ : syracuseStep 2365307 = 3547961) B3547961
theorem B1578875 : Blo 1048611 1578875 := bstep (se 1 (by rfl) ⟨1184156, by rfl⟩ : syracuseStep 1578875 = 2368313) B2368313
theorem B3544991 : Blo 1048611 3544991 := bstep (se 1 (by rfl) ⟨2658743, by rfl⟩ : syracuseStep 3544991 = 5317487) B5317487
theorem B2365343 : Blo 1048611 2365343 := bstep (se 1 (by rfl) ⟨1774007, by rfl⟩ : syracuseStep 2365343 = 3548015) B3548015
theorem B1578911 : Blo 1048611 1578911 := bstep (se 1 (by rfl) ⟨1184183, by rfl⟩ : syracuseStep 1578911 = 2368367) B2368367
theorem B2365577 : Blo 1048611 2365577 := bstep (se 2 (by rfl) ⟨887091, by rfl⟩ : syracuseStep 2365577 = 1774183) B1774183
theorem B2365793 : Blo 1048611 2365793 := bstep (se 2 (by rfl) ⟨887172, by rfl⟩ : syracuseStep 2365793 = 1774345) B1774345
theorem B2365883 : Blo 1048611 2365883 := bstep (se 1 (by rfl) ⟨1774412, by rfl⟩ : syracuseStep 2365883 = 3548825) B3548825
theorem B2366279 : Blo 1048611 2366279 := bstep (se 1 (by rfl) ⟨1774709, by rfl⟩ : syracuseStep 2366279 = 3549419) B3549419
theorem B5315705 : Blo 1048611 5315705 := bstep (se 2 (by rfl) ⟨1993389, by rfl⟩ : syracuseStep 5315705 = 3986779) B3986779
theorem B3546233 : Blo 1048611 3546233 := bstep (se 2 (by rfl) ⟨1329837, by rfl⟩ : syracuseStep 3546233 = 2659675) B2659675
theorem B2366585 : Blo 1048611 2366585 := bstep (se 2 (by rfl) ⟨887469, by rfl⟩ : syracuseStep 2366585 = 1774939) B1774939
theorem B2367143 : Blo 1048611 2367143 := bstep (se 1 (by rfl) ⟨1775357, by rfl⟩ : syracuseStep 2367143 = 3550715) B3550715
theorem B94576349 : Blo 1048611 94576349 := bstep (se 3 (by rfl) ⟨17733065, by rfl⟩ : syracuseStep 94576349 = 35466131) B35466131
theorem B2367251 : Blo 1048611 2367251 := bstep (se 1 (by rfl) ⟨1775438, by rfl⟩ : syracuseStep 2367251 = 3550877) B3550877
theorem B8986625 : Blo 1048611 8986625 := bstep (se 2 (by rfl) ⟨3369984, by rfl⟩ : syracuseStep 8986625 = 6739969) B6739969
theorem B2367611 : Blo 1048611 2367611 := bstep (se 1 (by rfl) ⟨1775708, by rfl⟩ : syracuseStep 2367611 = 3551417) B3551417
theorem B2367881 : Blo 1048611 2367881 := bstep (se 2 (by rfl) ⟨887955, by rfl⟩ : syracuseStep 2367881 = 1775911) B1775911
theorem B5972561 : Blo 1048611 5972561 := bstep (se 2 (by rfl) ⟨2239710, by rfl⟩ : syracuseStep 5972561 = 4479421) B4479421
theorem B9085715 : Blo 1048611 9085715 := bstep (se 1 (by rfl) ⟨6814286, by rfl⟩ : syracuseStep 9085715 = 13628573) B13628573
theorem B2991019 : Blo 1048611 2991019 := bstep (se 1 (by rfl) ⟨2243264, by rfl⟩ : syracuseStep 2991019 = 4486529) B4486529
theorem B24290279 : Blo 1048611 24290279 := bstep (se 1 (by rfl) ⟨18217709, by rfl⟩ : syracuseStep 24290279 = 36435419) B36435419
theorem B5056303 : Blo 1048611 5056303 := bstep (se 1 (by rfl) ⟨3792227, by rfl⟩ : syracuseStep 5056303 = 7584455) B7584455
theorem B7972829 : Blo 1048611 7972829 := bstep (se 3 (by rfl) ⟨1494905, by rfl⟩ : syracuseStep 7972829 = 2989811) B2989811
theorem B5056823 : Blo 1048611 5056823 := bstep (se 1 (by rfl) ⟨3792617, by rfl⟩ : syracuseStep 5056823 = 7585235) B7585235
theorem B3549689 : Blo 1048611 3549689 := bstep (se 2 (by rfl) ⟨1331133, by rfl⟩ : syracuseStep 3549689 = 2662267) B2662267
theorem B5319431 : Blo 1048611 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B3549959 : Blo 1048611 3549959 := bstep (se 1 (by rfl) ⟨2662469, by rfl⟩ : syracuseStep 3549959 = 5324939) B5324939
theorem B3550175 : Blo 1048611 3550175 := bstep (se 1 (by rfl) ⟨2662631, by rfl⟩ : syracuseStep 3550175 = 5325263) B5325263
theorem B3779713 : Blo 1048611 3779713 := bstep (se 2 (by rfl) ⟨1417392, by rfl⟩ : syracuseStep 3779713 = 2834785) B2834785
theorem B3550337 : Blo 1048611 3550337 := bstep (se 2 (by rfl) ⟨1331376, by rfl⟩ : syracuseStep 3550337 = 2662753) B2662753
theorem B1682743 : Blo 1048611 1682743 := bstep (se 1 (by rfl) ⟨1262057, by rfl⟩ : syracuseStep 1682743 = 2524115) B2524115
theorem B2239967 : Blo 1048611 2239967 := bstep (se 1 (by rfl) ⟨1679975, by rfl⟩ : syracuseStep 2239967 = 3359951) B3359951
theorem B45428363 : Blo 1048611 45428363 := bstep (se 1 (by rfl) ⟨34071272, by rfl⟩ : syracuseStep 45428363 = 68142545) B68142545
theorem B3551039 : Blo 1048611 3551039 := bstep (se 1 (by rfl) ⟨2663279, by rfl⟩ : syracuseStep 3551039 = 5326559) B5326559
theorem B7581545 : Blo 1048611 7581545 := bstep (se 2 (by rfl) ⟨2843079, by rfl⟩ : syracuseStep 7581545 = 5686159) B5686159
theorem B3551147 : Blo 1048611 3551147 := bstep (se 1 (by rfl) ⟨2663360, by rfl⟩ : syracuseStep 3551147 = 5326721) B5326721
theorem B7975259 : Blo 1048611 7975259 := bstep (se 1 (by rfl) ⟨5981444, by rfl⟩ : syracuseStep 7975259 = 11962889) B11962889
theorem B3551687 : Blo 1048611 3551687 := bstep (se 1 (by rfl) ⟨2663765, by rfl⟩ : syracuseStep 3551687 = 5327531) B5327531
theorem B19182095 : Blo 1048611 19182095 := bstep (se 1 (by rfl) ⟨14386571, by rfl⟩ : syracuseStep 19182095 = 28773143) B28773143
theorem B12760037 : Blo 1048611 12760037 := bstep (se 4 (by rfl) ⟨1196253, by rfl⟩ : syracuseStep 12760037 = 2392507) B2392507
theorem B55358437 : Blo 1048611 55358437 := bstep (se 4 (by rfl) ⟨5189853, by rfl⟩ : syracuseStep 55358437 = 10379707) B10379707
theorem B2241607 : Blo 1048611 2241607 := bstep (se 1 (by rfl) ⟨1681205, by rfl⟩ : syracuseStep 2241607 = 3362411) B3362411
theorem B2241641 : Blo 1048611 2241641 := bstep (se 2 (by rfl) ⟨840615, by rfl⟩ : syracuseStep 2241641 = 1681231) B1681231
theorem B2995451 : Blo 1048611 2995451 := bstep (se 1 (by rfl) ⟨2246588, by rfl⟩ : syracuseStep 2995451 = 4493177) B4493177
theorem B22722565 : Blo 1048611 22722565 := bstep (se 4 (by rfl) ⟨2130240, by rfl⟩ : syracuseStep 22722565 = 4260481) B4260481
theorem B5683391 : Blo 1048611 5683391 := bstep (se 1 (by rfl) ⟨4262543, by rfl⟩ : syracuseStep 5683391 = 8525087) B8525087
theorem B5322995 : Blo 1048611 5322995 := bstep (se 1 (by rfl) ⟨3992246, by rfl⟩ : syracuseStep 5322995 = 7984493) B7984493
theorem B7583993 : Blo 1048611 7583993 := bstep (se 2 (by rfl) ⟨2843997, by rfl⟩ : syracuseStep 7583993 = 5687995) B5687995
theorem B3029405 : Blo 1048611 3029405 := bstep (se 3 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 3029405 = 1136027) B1136027
theorem B17512949 : Blo 1048611 17512949 := bstep (se 5 (by rfl) ⟨820919, by rfl⟩ : syracuseStep 17512949 = 1641839) B1641839
theorem B1915483 : Blo 1048611 1915483 := bstep (se 1 (by rfl) ⟨1436612, by rfl⟩ : syracuseStep 1915483 = 2873225) B2873225
theorem B65649305 : Blo 1048611 65649305 := bstep (se 2 (by rfl) ⟨24618489, by rfl⟩ : syracuseStep 65649305 = 49236979) B49236979
theorem B4045483 : Blo 1048611 4045483 := bstep (se 1 (by rfl) ⟨3034112, by rfl⟩ : syracuseStep 4045483 = 6068225) B6068225
theorem B2243675 : Blo 1048611 2243675 := bstep (se 1 (by rfl) ⟨1682756, by rfl⟩ : syracuseStep 2243675 = 3365513) B3365513
theorem B8076995 : Blo 1048611 8076995 := bstep (se 1 (by rfl) ⟨6057746, by rfl⟩ : syracuseStep 8076995 = 12115493) B12115493
theorem B5324615 : Blo 1048611 5324615 := bstep (se 1 (by rfl) ⟨3993461, by rfl⟩ : syracuseStep 5324615 = 7986923) B7986923
theorem B10108759 : Blo 1048611 10108759 := bstep (se 1 (by rfl) ⟨7581569, by rfl⟩ : syracuseStep 10108759 = 15163139) B15163139
theorem B1328071 : Blo 1048611 1328071 := bstep (se 1 (by rfl) ⟨996053, by rfl⟩ : syracuseStep 1328071 = 1992107) B1992107
theorem B3982391 : Blo 1048611 3982391 := bstep (se 1 (by rfl) ⟨2986793, by rfl⟩ : syracuseStep 3982391 = 5973587) B5973587
theorem B4605119 : Blo 1048611 4605119 := bstep (se 1 (by rfl) ⟨3453839, by rfl⟩ : syracuseStep 4605119 = 6907679) B6907679
theorem B8963693 : Blo 1048611 8963693 := bstep (se 3 (by rfl) ⟨1680692, by rfl⟩ : syracuseStep 8963693 = 3361385) B3361385
theorem B12273389 : Blo 1048611 12273389 := bstep (se 3 (by rfl) ⟨2301260, by rfl⟩ : syracuseStep 12273389 = 4602521) B4602521
theorem B1329959 : Blo 1048611 1329959 := bstep (se 1 (by rfl) ⟨997469, by rfl⟩ : syracuseStep 1329959 = 1994939) B1994939
theorem B1330283 : Blo 1048611 1330283 := bstep (se 1 (by rfl) ⟨997712, by rfl⟩ : syracuseStep 1330283 = 1995425) B1995425
theorem B5328017 : Blo 1048611 5328017 := bstep (se 2 (by rfl) ⟨1998006, by rfl⟩ : syracuseStep 5328017 = 3996013) B3996013
theorem B97209827 : Blo 1048611 97209827 := bstep (se 1 (by rfl) ⟨72907370, by rfl⟩ : syracuseStep 97209827 = 145814741) B145814741
theorem B6835745 : Blo 1048611 6835745 := bstep (se 2 (by rfl) ⟨2563404, by rfl⟩ : syracuseStep 6835745 = 5126809) B5126809
theorem B3985307 : Blo 1048611 3985307 := bstep (se 1 (by rfl) ⟨2988980, by rfl⟩ : syracuseStep 3985307 = 5977961) B5977961
theorem B1331255 : Blo 1048611 1331255 := bstep (se 1 (by rfl) ⟨998441, by rfl⟩ : syracuseStep 1331255 = 1996883) B1996883
theorem B10080773 : Blo 1048611 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B7984007 : Blo 1048611 7984007 := bstep (se 1 (by rfl) ⟨5988005, by rfl⟩ : syracuseStep 7984007 = 11976011) B11976011
theorem B11360249 : Blo 1048611 11360249 := bstep (se 2 (by rfl) ⟨4260093, by rfl⟩ : syracuseStep 11360249 = 8520187) B8520187
theorem B3987539 : Blo 1048611 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B331897175 : Blo 1048611 331897175 := bstep (se 1 (by rfl) ⟨248922881, by rfl⟩ : syracuseStep 331897175 = 497845763) B497845763
theorem B9099985 : Blo 1048611 9099985 := bstep (se 2 (by rfl) ⟨3412494, by rfl⟩ : syracuseStep 9099985 = 6824989) B6824989
theorem B1891183 : Blo 1048611 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B8970527 : Blo 1048611 8970527 := bstep (se 1 (by rfl) ⟨6727895, by rfl⟩ : syracuseStep 8970527 = 13455791) B13455791
theorem B6742763 : Blo 1048611 6742763 := bstep (se 1 (by rfl) ⟨5057072, by rfl⟩ : syracuseStep 6742763 = 10114145) B10114145
theorem B7988381 : Blo 1048611 7988381 := bstep (se 3 (by rfl) ⟨1497821, by rfl⟩ : syracuseStep 7988381 = 2995643) B2995643
theorem B23029069 : Blo 1048611 23029069 := bstep (se 3 (by rfl) ⟨4317950, by rfl⟩ : syracuseStep 23029069 = 8635901) B8635901
theorem B8972441 : Blo 1048611 8972441 := bstep (se 2 (by rfl) ⟨3364665, by rfl⟩ : syracuseStep 8972441 = 6729331) B6729331
theorem B14379241 : Blo 1048611 14379241 := bstep (se 2 (by rfl) ⟨5392215, by rfl⟩ : syracuseStep 14379241 = 10784431) B10784431
theorem B11364745 : Blo 1048611 11364745 := bstep (se 2 (by rfl) ⟨4261779, by rfl⟩ : syracuseStep 11364745 = 8523559) B8523559
theorem B5401025 : Blo 1048611 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B10086923 : Blo 1048611 10086923 := bstep (se 1 (by rfl) ⟨7565192, by rfl⟩ : syracuseStep 10086923 = 15130385) B15130385
theorem B4254239 : Blo 1048611 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B3992111 : Blo 1048611 3992111 := bstep (se 1 (by rfl) ⟨2994083, by rfl⟩ : syracuseStep 3992111 = 5988167) B5988167
theorem B34040519 : Blo 1048611 34040519 := bstep (se 1 (by rfl) ⟨25530389, by rfl⟩ : syracuseStep 34040519 = 51060779) B51060779
theorem B3992399 : Blo 1048611 3992399 := bstep (se 1 (by rfl) ⟨2994299, by rfl⟩ : syracuseStep 3992399 = 5988599) B5988599
theorem B10087847 : Blo 1048611 10087847 := bstep (se 1 (by rfl) ⟨7565885, by rfl⟩ : syracuseStep 10087847 = 15131771) B15131771
theorem B1994195 : Blo 1048611 1994195 := bstep (se 1 (by rfl) ⟨1495646, by rfl⟩ : syracuseStep 1994195 = 2991293) B2991293
theorem B3993083 : Blo 1048611 3993083 := bstep (se 1 (by rfl) ⟨2994812, by rfl⟩ : syracuseStep 3993083 = 5989625) B5989625
theorem B4485401 : Blo 1048611 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B5042675 : Blo 1048611 5042675 := bstep (se 1 (by rfl) ⟨3782006, by rfl⟩ : syracuseStep 5042675 = 7564013) B7564013
theorem B15135407 : Blo 1048611 15135407 := bstep (se 1 (by rfl) ⟨11351555, by rfl⟩ : syracuseStep 15135407 = 22703111) B22703111
theorem B14349575 : Blo 1048611 14349575 := bstep (se 1 (by rfl) ⟨10762181, by rfl⟩ : syracuseStep 14349575 = 21524363) B21524363
theorem B10777943 : Blo 1048611 10777943 := bstep (se 1 (by rfl) ⟨8083457, by rfl⟩ : syracuseStep 10777943 = 16166915) B16166915
theorem B4257143 : Blo 1048611 4257143 := bstep (se 1 (by rfl) ⟨3192857, by rfl⟩ : syracuseStep 4257143 = 6385715) B6385715
theorem B49903057 : Blo 1048611 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B17036867 : Blo 1048611 17036867 := bstep (se 1 (by rfl) ⟨12777650, by rfl⟩ : syracuseStep 17036867 = 25555301) B25555301
theorem B3995831 : Blo 1048611 3995831 := bstep (se 1 (by rfl) ⟨2996873, by rfl⟩ : syracuseStep 3995831 = 5993747) B5993747
theorem B3996317 : Blo 1048611 3996317 := bstep (se 3 (by rfl) ⟨749309, by rfl⟩ : syracuseStep 3996317 = 1498619) B1498619
theorem B3996499 : Blo 1048611 3996499 := bstep (se 1 (by rfl) ⟨2997374, by rfl⟩ : syracuseStep 3996499 = 5994749) B5994749
theorem B1997779 : Blo 1048611 1997779 := bstep (se 1 (by rfl) ⟨1498334, by rfl⟩ : syracuseStep 1997779 = 2996669) B2996669
theorem B5045615 : Blo 1048611 5045615 := bstep (se 1 (by rfl) ⟨3784211, by rfl⟩ : syracuseStep 5045615 = 7568423) B7568423
theorem B1703339 : Blo 1048611 1703339 := bstep (se 1 (by rfl) ⟨1277504, by rfl⟩ : syracuseStep 1703339 = 2555009) B2555009
theorem B3636755 : Blo 1048611 3636755 := bstep (se 1 (by rfl) ⟨2727566, by rfl⟩ : syracuseStep 3636755 = 5455133) B5455133
theorem B2523001 : Blo 1048611 2523001 := bstep (se 2 (by rfl) ⟨946125, by rfl⟩ : syracuseStep 2523001 = 1892251) B1892251
theorem B1048703 : Blo 1048611 1048703 := bstep (se 1 (by rfl) ⟨786527, by rfl⟩ : syracuseStep 1048703 = 1573055) B1573055
theorem B1048987 : Blo 1048611 1048987 := bstep (se 1 (by rfl) ⟨786740, by rfl⟩ : syracuseStep 1048987 = 1573481) B1573481
theorem B1048991 : Blo 1048611 1048991 := bstep (se 1 (by rfl) ⟨786743, by rfl⟩ : syracuseStep 1048991 = 1573487) B1573487
theorem B1573403 : Blo 1048611 1573403 := bstep (se 1 (by rfl) ⟨1180052, by rfl⟩ : syracuseStep 1573403 = 2360105) B2360105
theorem B2654927 : Blo 1048611 2654927 := bstep (se 1 (by rfl) ⟨1991195, by rfl⟩ : syracuseStep 2654927 = 3982391) B3982391
theorem B1573583 : Blo 1048611 1573583 := bstep (se 1 (by rfl) ⟨1180187, by rfl⟩ : syracuseStep 1573583 = 2360375) B2360375
theorem B3539753 : Blo 1048611 3539753 := bstep (se 2 (by rfl) ⟨1327407, by rfl⟩ : syracuseStep 3539753 = 2654815) B2654815
theorem B1770295 : Blo 1048611 1770295 := bstep (se 1 (by rfl) ⟨1327721, by rfl⟩ : syracuseStep 1770295 = 2655443) B2655443
theorem B1049407 : Blo 1048611 1049407 := bstep (se 1 (by rfl) ⟨787055, by rfl⟩ : syracuseStep 1049407 = 1574111) B1574111
theorem B8520511 : Blo 1048611 8520511 := bstep (se 1 (by rfl) ⟨6390383, by rfl⟩ : syracuseStep 8520511 = 12780767) B12780767
theorem B1573703 : Blo 1048611 1573703 := bstep (se 1 (by rfl) ⟨1180277, by rfl⟩ : syracuseStep 1573703 = 2360555) B2360555
theorem B1049415 : Blo 1048611 1049415 := bstep (se 1 (by rfl) ⟨787061, by rfl⟩ : syracuseStep 1049415 = 1574123) B1574123
theorem B1573769 : Blo 1048611 1573769 := bstep (se 2 (by rfl) ⟨590163, by rfl⟩ : syracuseStep 1573769 = 1180327) B1180327
theorem B1049671 : Blo 1048611 1049671 := bstep (se 1 (by rfl) ⟨787253, by rfl⟩ : syracuseStep 1049671 = 1574507) B1574507
theorem B2360447 : Blo 1048611 2360447 := bstep (se 1 (by rfl) ⟨1770335, by rfl⟩ : syracuseStep 2360447 = 3540671) B3540671
theorem B1574015 : Blo 1048611 1574015 := bstep (se 1 (by rfl) ⟨1180511, by rfl⟩ : syracuseStep 1574015 = 2361023) B2361023
theorem B1049727 : Blo 1048611 1049727 := bstep (se 1 (by rfl) ⟨787295, by rfl⟩ : syracuseStep 1049727 = 1574591) B1574591
theorem B1049851 : Blo 1048611 1049851 := bstep (se 1 (by rfl) ⟨787388, by rfl⟩ : syracuseStep 1049851 = 1574777) B1574777
theorem B1770761 : Blo 1048611 1770761 := bstep (se 2 (by rfl) ⟨664035, by rfl⟩ : syracuseStep 1770761 = 1328071) B1328071
theorem B1574153 : Blo 1048611 1574153 := bstep (se 2 (by rfl) ⟨590307, by rfl⟩ : syracuseStep 1574153 = 1180615) B1180615
theorem B6817385 : Blo 1048611 6817385 := bstep (se 2 (by rfl) ⟨2556519, by rfl⟩ : syracuseStep 6817385 = 5113039) B5113039
theorem B1574633 : Blo 1048611 1574633 := bstep (se 2 (by rfl) ⟨590487, by rfl⟩ : syracuseStep 1574633 = 1180975) B1180975
theorem B1050351 : Blo 1048611 1050351 := bstep (se 1 (by rfl) ⟨787763, by rfl⟩ : syracuseStep 1050351 = 1575527) B1575527
theorem B1574639 : Blo 1048611 1574639 := bstep (se 1 (by rfl) ⟨1180979, by rfl⟩ : syracuseStep 1574639 = 2361959) B2361959
theorem B30705425 : Blo 1048611 30705425 := bstep (se 2 (by rfl) ⟨11514534, by rfl⟩ : syracuseStep 30705425 = 23029069) B23029069
theorem B1771375 : Blo 1048611 1771375 := bstep (se 1 (by rfl) ⟨1328531, by rfl⟩ : syracuseStep 1771375 = 2657063) B2657063
theorem B1181551 : Blo 1048611 1181551 := bstep (se 1 (by rfl) ⟨886163, by rfl⟩ : syracuseStep 1181551 = 1772327) B1772327
theorem B1050479 : Blo 1048611 1050479 := bstep (se 1 (by rfl) ⟨787859, by rfl⟩ : syracuseStep 1050479 = 1575719) B1575719
theorem B1574891 : Blo 1048611 1574891 := bstep (se 1 (by rfl) ⟨1181168, by rfl⟩ : syracuseStep 1574891 = 2362337) B2362337
theorem B1771591 : Blo 1048611 1771591 := bstep (se 1 (by rfl) ⟨1328693, by rfl⟩ : syracuseStep 1771591 = 2657387) B2657387
theorem B1181767 : Blo 1048611 1181767 := bstep (se 1 (by rfl) ⟨886325, by rfl⟩ : syracuseStep 1181767 = 1772651) B1772651
theorem B1050695 : Blo 1048611 1050695 := bstep (se 1 (by rfl) ⟨788021, by rfl⟩ : syracuseStep 1050695 = 1576043) B1576043
theorem B1575143 : Blo 1048611 1575143 := bstep (se 1 (by rfl) ⟨1181357, by rfl⟩ : syracuseStep 1575143 = 2362715) B2362715
theorem B1050855 : Blo 1048611 1050855 := bstep (se 1 (by rfl) ⟨788141, by rfl⟩ : syracuseStep 1050855 = 1576283) B1576283
theorem B1181947 : Blo 1048611 1181947 := bstep (se 1 (by rfl) ⟨886460, by rfl⟩ : syracuseStep 1181947 = 1772921) B1772921
theorem B1050875 : Blo 1048611 1050875 := bstep (se 1 (by rfl) ⟨788156, by rfl⟩ : syracuseStep 1050875 = 1576313) B1576313
theorem B2361599 : Blo 1048611 2361599 := bstep (se 1 (by rfl) ⟨1771199, by rfl⟩ : syracuseStep 2361599 = 3542399) B3542399
theorem B1575167 : Blo 1048611 1575167 := bstep (se 1 (by rfl) ⟨1181375, by rfl⟩ : syracuseStep 1575167 = 2362751) B2362751
theorem B1050879 : Blo 1048611 1050879 := bstep (se 1 (by rfl) ⟨788159, by rfl⟩ : syracuseStep 1050879 = 1576319) B1576319
theorem B4557163 : Blo 1048611 4557163 := bstep (se 1 (by rfl) ⟨3417872, by rfl⟩ : syracuseStep 4557163 = 6835745) B6835745
theorem B1575305 : Blo 1048611 1575305 := bstep (se 2 (by rfl) ⟨590739, by rfl⟩ : syracuseStep 1575305 = 1181479) B1181479
theorem B1772023 : Blo 1048611 1772023 := bstep (se 1 (by rfl) ⟨1329017, by rfl⟩ : syracuseStep 1772023 = 2658035) B2658035
theorem B2656871 : Blo 1048611 2656871 := bstep (se 1 (by rfl) ⟨1992653, by rfl⟩ : syracuseStep 2656871 = 3985307) B3985307
theorem B1051295 : Blo 1048611 1051295 := bstep (se 1 (by rfl) ⟨788471, by rfl⟩ : syracuseStep 1051295 = 1576943) B1576943
theorem B1051303 : Blo 1048611 1051303 := bstep (se 1 (by rfl) ⟨788477, by rfl⟩ : syracuseStep 1051303 = 1576955) B1576955
theorem B1182415 : Blo 1048611 1182415 := bstep (se 1 (by rfl) ⟨886811, by rfl⟩ : syracuseStep 1182415 = 1773623) B1773623
theorem B1051343 : Blo 1048611 1051343 := bstep (se 1 (by rfl) ⟨788507, by rfl⟩ : syracuseStep 1051343 = 1577015) B1577015
theorem B1051375 : Blo 1048611 1051375 := bstep (se 1 (by rfl) ⟨788531, by rfl⟩ : syracuseStep 1051375 = 1577063) B1577063
theorem B1051423 : Blo 1048611 1051423 := bstep (se 1 (by rfl) ⟨788567, by rfl⟩ : syracuseStep 1051423 = 1577135) B1577135
theorem B1182631 : Blo 1048611 1182631 := bstep (se 1 (by rfl) ⟨886973, by rfl⟩ : syracuseStep 1182631 = 1773947) B1773947
theorem B1051559 : Blo 1048611 1051559 := bstep (se 1 (by rfl) ⟨788669, by rfl⟩ : syracuseStep 1051559 = 1577339) B1577339
theorem B19172321 : Blo 1048611 19172321 := bstep (se 2 (by rfl) ⟨7189620, by rfl⟩ : syracuseStep 19172321 = 14379241) B14379241
theorem B6720515 : Blo 1048611 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B1182811 : Blo 1048611 1182811 := bstep (se 1 (by rfl) ⟨887108, by rfl⟩ : syracuseStep 1182811 = 1774217) B1774217
theorem B1051739 : Blo 1048611 1051739 := bstep (se 1 (by rfl) ⟨788804, by rfl⟩ : syracuseStep 1051739 = 1577609) B1577609
theorem B1051879 : Blo 1048611 1051879 := bstep (se 1 (by rfl) ⟨788909, by rfl⟩ : syracuseStep 1051879 = 1577819) B1577819
theorem B1576415 : Blo 1048611 1576415 := bstep (se 1 (by rfl) ⟨1182311, by rfl⟩ : syracuseStep 1576415 = 2364623) B2364623
theorem B2690587 : Blo 1048611 2690587 := bstep (se 1 (by rfl) ⟨2017940, by rfl⟩ : syracuseStep 2690587 = 4035881) B4035881
theorem B1773083 : Blo 1048611 1773083 := bstep (se 1 (by rfl) ⟨1329812, by rfl⟩ : syracuseStep 1773083 = 2659625) B2659625
theorem B1576475 : Blo 1048611 1576475 := bstep (se 1 (by rfl) ⟨1182356, by rfl⟩ : syracuseStep 1576475 = 2364713) B2364713
theorem B1052187 : Blo 1048611 1052187 := bstep (se 1 (by rfl) ⟨789140, by rfl⟩ : syracuseStep 1052187 = 1578281) B1578281
theorem B1576607 : Blo 1048611 1576607 := bstep (se 1 (by rfl) ⟨1182455, by rfl⟩ : syracuseStep 1576607 = 2364911) B2364911
theorem B1052319 : Blo 1048611 1052319 := bstep (se 1 (by rfl) ⟨789239, by rfl⟩ : syracuseStep 1052319 = 1578479) B1578479
theorem B1576871 : Blo 1048611 1576871 := bstep (se 1 (by rfl) ⟨1182653, by rfl⟩ : syracuseStep 1576871 = 2365307) B2365307
theorem B1052583 : Blo 1048611 1052583 := bstep (se 1 (by rfl) ⟨789437, by rfl⟩ : syracuseStep 1052583 = 1578875) B1578875
theorem B2363327 : Blo 1048611 2363327 := bstep (se 1 (by rfl) ⟨1772495, by rfl⟩ : syracuseStep 2363327 = 3544991) B3544991
theorem B1576895 : Blo 1048611 1576895 := bstep (se 1 (by rfl) ⟨1182671, by rfl⟩ : syracuseStep 1576895 = 2365343) B2365343
theorem B1052607 : Blo 1048611 1052607 := bstep (se 1 (by rfl) ⟨789455, by rfl⟩ : syracuseStep 1052607 = 1578911) B1578911
theorem B7573499 : Blo 1048611 7573499 := bstep (se 1 (by rfl) ⟨5680124, by rfl⟩ : syracuseStep 7573499 = 11360249) B11360249
theorem B2658359 : Blo 1048611 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B1577051 : Blo 1048611 1577051 := bstep (se 1 (by rfl) ⟨1182788, by rfl⟩ : syracuseStep 1577051 = 2365577) B2365577
theorem B1577195 : Blo 1048611 1577195 := bstep (se 1 (by rfl) ⟨1182896, by rfl⟩ : syracuseStep 1577195 = 2365793) B2365793
theorem B1577255 : Blo 1048611 1577255 := bstep (se 1 (by rfl) ⟨1182941, by rfl⟩ : syracuseStep 1577255 = 2365883) B2365883
theorem B1577519 : Blo 1048611 1577519 := bstep (se 1 (by rfl) ⟨1183139, by rfl⟩ : syracuseStep 1577519 = 2366279) B2366279
theorem B3543803 : Blo 1048611 3543803 := bstep (se 1 (by rfl) ⟨2657852, by rfl⟩ : syracuseStep 3543803 = 5315705) B5315705
theorem B2364155 : Blo 1048611 2364155 := bstep (se 1 (by rfl) ⟨1773116, by rfl⟩ : syracuseStep 2364155 = 3546233) B3546233
theorem B1577723 : Blo 1048611 1577723 := bstep (se 1 (by rfl) ⟨1183292, by rfl⟩ : syracuseStep 1577723 = 2366585) B2366585
theorem B1578095 : Blo 1048611 1578095 := bstep (se 1 (by rfl) ⟨1183571, by rfl⟩ : syracuseStep 1578095 = 2367143) B2367143
theorem B63050899 : Blo 1048611 63050899 := bstep (se 1 (by rfl) ⟨47288174, by rfl⟩ : syracuseStep 63050899 = 94576349) B94576349
theorem B1578167 : Blo 1048611 1578167 := bstep (se 1 (by rfl) ⟨1183625, by rfl⟩ : syracuseStep 1578167 = 2367251) B2367251
theorem B1578407 : Blo 1048611 1578407 := bstep (se 1 (by rfl) ⟨1183805, by rfl⟩ : syracuseStep 1578407 = 2367611) B2367611
theorem B1578587 : Blo 1048611 1578587 := bstep (se 1 (by rfl) ⟨1183940, by rfl⟩ : syracuseStep 1578587 = 2367881) B2367881
theorem B4495175 : Blo 1048611 4495175 := bstep (se 1 (by rfl) ⟨3371381, by rfl⟩ : syracuseStep 4495175 = 6742763) B6742763
theorem B16193519 : Blo 1048611 16193519 := bstep (se 1 (by rfl) ⟨12145139, by rfl⟩ : syracuseStep 16193519 = 24290279) B24290279
theorem B20158469 : Blo 1048611 20158469 := bstep (se 4 (by rfl) ⟨1889856, by rfl⟩ : syracuseStep 20158469 = 3779713) B3779713
theorem B46701197 : Blo 1048611 46701197 := bstep (se 3 (by rfl) ⟨8756474, by rfl⟩ : syracuseStep 46701197 = 17512949) B17512949
theorem B5315219 : Blo 1048611 5315219 := bstep (se 1 (by rfl) ⟨3986414, by rfl⟩ : syracuseStep 5315219 = 7972829) B7972829
theorem B11344637 : Blo 1048611 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B2988809 : Blo 1048611 2988809 := bstep (se 2 (by rfl) ⟨1120803, by rfl⟩ : syracuseStep 2988809 = 2241607) B2241607
theorem B2366459 : Blo 1048611 2366459 := bstep (se 1 (by rfl) ⟨1774844, by rfl⟩ : syracuseStep 2366459 = 3549689) B3549689
theorem B6724615 : Blo 1048611 6724615 := bstep (se 1 (by rfl) ⟨5043461, by rfl⟩ : syracuseStep 6724615 = 10086923) B10086923
theorem B2661407 : Blo 1048611 2661407 := bstep (se 1 (by rfl) ⟨1996055, by rfl⟩ : syracuseStep 2661407 = 3992111) B3992111
theorem B3546287 : Blo 1048611 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B2366639 : Blo 1048611 2366639 := bstep (se 1 (by rfl) ⟨1774979, by rfl⟩ : syracuseStep 2366639 = 3549959) B3549959
theorem B2661599 : Blo 1048611 2661599 := bstep (se 1 (by rfl) ⟨1996199, by rfl⟩ : syracuseStep 2661599 = 3992399) B3992399
theorem B2366783 : Blo 1048611 2366783 := bstep (se 1 (by rfl) ⟨1775087, by rfl⟩ : syracuseStep 2366783 = 3550175) B3550175
theorem B2366891 : Blo 1048611 2366891 := bstep (se 1 (by rfl) ⟨1775168, by rfl⟩ : syracuseStep 2366891 = 3550337) B3550337
theorem B3546557 : Blo 1048611 3546557 := bstep (se 3 (by rfl) ⟨664979, by rfl⟩ : syracuseStep 3546557 = 1329959) B1329959
theorem B6725231 : Blo 1048611 6725231 := bstep (se 1 (by rfl) ⟨5043923, by rfl⟩ : syracuseStep 6725231 = 10087847) B10087847
theorem B2662055 : Blo 1048611 2662055 := bstep (se 1 (by rfl) ⟨1996541, by rfl⟩ : syracuseStep 2662055 = 3993083) B3993083
theorem B30285575 : Blo 1048611 30285575 := bstep (se 1 (by rfl) ⟨22714181, by rfl⟩ : syracuseStep 30285575 = 45428363) B45428363
theorem B2367359 : Blo 1048611 2367359 := bstep (se 1 (by rfl) ⟨1775519, by rfl⟩ : syracuseStep 2367359 = 3551039) B3551039
theorem B5054363 : Blo 1048611 5054363 := bstep (se 1 (by rfl) ⟨3790772, by rfl⟩ : syracuseStep 5054363 = 7581545) B7581545
theorem B2367431 : Blo 1048611 2367431 := bstep (se 1 (by rfl) ⟨1775573, by rfl⟩ : syracuseStep 2367431 = 3551147) B3551147
theorem B2990267 : Blo 1048611 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B5316839 : Blo 1048611 5316839 := bstep (se 1 (by rfl) ⟨3987629, by rfl⟩ : syracuseStep 5316839 = 7975259) B7975259
theorem B3547421 : Blo 1048611 3547421 := bstep (se 3 (by rfl) ⟨665141, by rfl⟩ : syracuseStep 3547421 = 1330283) B1330283
theorem B2367791 : Blo 1048611 2367791 := bstep (se 1 (by rfl) ⟨1775843, by rfl⟩ : syracuseStep 2367791 = 3551687) B3551687
theorem B12788063 : Blo 1048611 12788063 := bstep (se 1 (by rfl) ⟨9591047, by rfl⟩ : syracuseStep 12788063 = 19182095) B19182095
theorem B7185295 : Blo 1048611 7185295 := bstep (se 1 (by rfl) ⟨5388971, by rfl⟩ : syracuseStep 7185295 = 10777943) B10777943
theorem B12133313 : Blo 1048611 12133313 := bstep (se 2 (by rfl) ⟨4549992, by rfl⟩ : syracuseStep 12133313 = 9099985) B9099985
theorem B2663705 : Blo 1048611 2663705 := bstep (se 2 (by rfl) ⟨998889, by rfl⟩ : syracuseStep 2663705 = 1997779) B1997779
theorem B2663887 : Blo 1048611 2663887 := bstep (se 1 (by rfl) ⟨1997915, by rfl⟩ : syracuseStep 2663887 = 3995831) B3995831
theorem B3548663 : Blo 1048611 3548663 := bstep (se 1 (by rfl) ⟨2661497, by rfl⟩ : syracuseStep 3548663 = 5322995) B5322995
theorem B5055995 : Blo 1048611 5055995 := bstep (se 1 (by rfl) ⟨3791996, by rfl⟩ : syracuseStep 5055995 = 7583993) B7583993
theorem B2664211 : Blo 1048611 2664211 := bstep (se 1 (by rfl) ⟨1998158, by rfl⟩ : syracuseStep 2664211 = 3996317) B3996317
theorem B13478345 : Blo 1048611 13478345 := bstep (se 2 (by rfl) ⟨5054379, by rfl⟩ : syracuseStep 13478345 = 10108759) B10108759
theorem B5384663 : Blo 1048611 5384663 := bstep (se 1 (by rfl) ⟨4038497, by rfl⟩ : syracuseStep 5384663 = 8076995) B8076995
theorem B3549743 : Blo 1048611 3549743 := bstep (se 1 (by rfl) ⟨2662307, by rfl⟩ : syracuseStep 3549743 = 5324615) B5324615
theorem B3550013 : Blo 1048611 3550013 := bstep (se 3 (by rfl) ⟨665627, by rfl⟩ : syracuseStep 3550013 = 1331255) B1331255
theorem B10791899 : Blo 1048611 10791899 := bstep (se 1 (by rfl) ⟨8093924, by rfl⟩ : syracuseStep 10791899 = 16187849) B16187849
theorem B5975795 : Blo 1048611 5975795 := bstep (se 1 (by rfl) ⟨4481846, by rfl⟩ : syracuseStep 5975795 = 8963693) B8963693
theorem B13447133 : Blo 1048611 13447133 := bstep (se 3 (by rfl) ⟨2521337, by rfl⟩ : syracuseStep 13447133 = 5042675) B5042675
theorem B1683563 : Blo 1048611 1683563 := bstep (se 1 (by rfl) ⟨1262672, by rfl⟩ : syracuseStep 1683563 = 2525345) B2525345
theorem B1683679 : Blo 1048611 1683679 := bstep (se 1 (by rfl) ⟨1262759, by rfl⟩ : syracuseStep 1683679 = 2525519) B2525519
theorem B3552011 : Blo 1048611 3552011 := bstep (se 1 (by rfl) ⟨2664008, by rfl⟩ : syracuseStep 3552011 = 5328017) B5328017
theorem B2995667 : Blo 1048611 2995667 := bstep (se 1 (by rfl) ⟨2246750, by rfl⟩ : syracuseStep 2995667 = 4493501) B4493501
theorem B5977709 : Blo 1048611 5977709 := bstep (se 3 (by rfl) ⟨1120820, by rfl⟩ : syracuseStep 5977709 = 2241641) B2241641
theorem B3192539 : Blo 1048611 3192539 := bstep (se 1 (by rfl) ⟨2394404, by rfl⟩ : syracuseStep 3192539 = 4788809) B4788809
theorem B15152993 : Blo 1048611 15152993 := bstep (se 2 (by rfl) ⟨5682372, by rfl⟩ : syracuseStep 15152993 = 11364745) B11364745
theorem B5322671 : Blo 1048611 5322671 := bstep (se 1 (by rfl) ⟨3992003, by rfl⟩ : syracuseStep 5322671 = 7984007) B7984007
theorem B13482035 : Blo 1048611 13482035 := bstep (se 1 (by rfl) ⟨10111526, by rfl⟩ : syracuseStep 13482035 = 20223053) B20223053
theorem B14596175 : Blo 1048611 14596175 := bstep (se 1 (by rfl) ⟨10947131, by rfl⟩ : syracuseStep 14596175 = 21894263) B21894263
theorem B21575909 : Blo 1048611 21575909 := bstep (se 4 (by rfl) ⟨2022741, by rfl⟩ : syracuseStep 21575909 = 4045483) B4045483
theorem B221264783 : Blo 1048611 221264783 := bstep (se 1 (by rfl) ⟨165948587, by rfl⟩ : syracuseStep 221264783 = 331897175) B331897175
theorem B2243657 : Blo 1048611 2243657 := bstep (se 2 (by rfl) ⟨841371, by rfl⟩ : syracuseStep 2243657 = 1682743) B1682743
theorem B332316701 : Blo 1048611 332316701 := bstep (se 3 (by rfl) ⟨62309381, by rfl⟩ : syracuseStep 332316701 = 124618763) B124618763
theorem B5980351 : Blo 1048611 5980351 := bstep (se 1 (by rfl) ⟨4485263, by rfl⟩ : syracuseStep 5980351 = 8970527) B8970527
theorem B6832421 : Blo 1048611 6832421 := bstep (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) B1281079
theorem B3981707 : Blo 1048611 3981707 := bstep (se 1 (by rfl) ⟨2986280, by rfl⟩ : syracuseStep 3981707 = 5972561) B5972561
theorem B3981905 : Blo 1048611 3981905 := bstep (se 2 (by rfl) ⟨1493214, by rfl⟩ : syracuseStep 3981905 = 2986429) B2986429
theorem B5325587 : Blo 1048611 5325587 := bstep (se 1 (by rfl) ⟨3994190, by rfl⟩ : syracuseStep 5325587 = 7988381) B7988381
theorem B8078413 : Blo 1048611 8078413 := bstep (se 3 (by rfl) ⟨1514702, by rfl⟩ : syracuseStep 8078413 = 3029405) B3029405
theorem B73811249 : Blo 1048611 73811249 := bstep (se 2 (by rfl) ⟨27679218, by rfl⟩ : syracuseStep 73811249 = 55358437) B55358437
theorem B5981627 : Blo 1048611 5981627 := bstep (se 1 (by rfl) ⟨4486220, by rfl⟩ : syracuseStep 5981627 = 8972441) B8972441
theorem B22693679 : Blo 1048611 22693679 := bstep (se 1 (by rfl) ⟨17020259, by rfl⟩ : syracuseStep 22693679 = 34040519) B34040519
theorem B66537409 : Blo 1048611 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B8964377 : Blo 1048611 8964377 := bstep (se 2 (by rfl) ⟨3361641, by rfl⟩ : syracuseStep 8964377 = 6723283) B6723283
theorem B1329463 : Blo 1048611 1329463 := bstep (se 1 (by rfl) ⟨997097, by rfl⟩ : syracuseStep 1329463 = 1994195) B1994195
theorem B1493311 : Blo 1048611 1493311 := bstep (se 1 (by rfl) ⟨1119983, by rfl⟩ : syracuseStep 1493311 = 2239967) B2239967
theorem B30296753 : Blo 1048611 30296753 := bstep (se 2 (by rfl) ⟨11361282, by rfl⟩ : syracuseStep 30296753 = 22722565) B22722565
theorem B8506691 : Blo 1048611 8506691 := bstep (se 1 (by rfl) ⟨6380018, by rfl⟩ : syracuseStep 8506691 = 12760037) B12760037
theorem B2838095 : Blo 1048611 2838095 := bstep (se 1 (by rfl) ⟨2128571, by rfl⟩ : syracuseStep 2838095 = 4257143) B4257143
theorem B11357911 : Blo 1048611 11357911 := bstep (se 1 (by rfl) ⟨8518433, by rfl⟩ : syracuseStep 11357911 = 17036867) B17036867
theorem B5328665 : Blo 1048611 5328665 := bstep (se 2 (by rfl) ⟨1998249, by rfl⟩ : syracuseStep 5328665 = 3996499) B3996499
theorem B3788927 : Blo 1048611 3788927 := bstep (se 1 (by rfl) ⟨2841695, by rfl⟩ : syracuseStep 3788927 = 5683391) B5683391
theorem B43766203 : Blo 1048611 43766203 := bstep (se 1 (by rfl) ⟨32824652, by rfl⟩ : syracuseStep 43766203 = 65649305) B65649305
theorem B1495783 : Blo 1048611 1495783 := bstep (se 1 (by rfl) ⟨1121837, by rfl⟩ : syracuseStep 1495783 = 2243675) B2243675
theorem B3363743 : Blo 1048611 3363743 := bstep (se 1 (by rfl) ⟨2522807, by rfl⟩ : syracuseStep 3363743 = 5045615) B5045615
theorem B1135559 : Blo 1048611 1135559 := bstep (se 1 (by rfl) ⟨851669, by rfl⟩ : syracuseStep 1135559 = 1703339) B1703339
theorem B3364001 : Blo 1048611 3364001 := bstep (se 2 (by rfl) ⟨1261500, by rfl⟩ : syracuseStep 3364001 = 2523001) B2523001
theorem B3070079 : Blo 1048611 3070079 := bstep (se 1 (by rfl) ⟨2302559, by rfl⟩ : syracuseStep 3070079 = 4605119) B4605119
theorem B4479371 : Blo 1048611 4479371 := bstep (se 1 (by rfl) ⟨3359528, by rfl⟩ : syracuseStep 4479371 = 6719057) B6719057
theorem B8182259 : Blo 1048611 8182259 := bstep (se 1 (by rfl) ⟨6136694, by rfl⟩ : syracuseStep 8182259 = 12273389) B12273389
theorem B3365383 : Blo 1048611 3365383 := bstep (se 1 (by rfl) ⟨2524037, by rfl⟩ : syracuseStep 3365383 = 5048075) B5048075
theorem B3988025 : Blo 1048611 3988025 := bstep (se 2 (by rfl) ⟨1495509, by rfl⟩ : syracuseStep 3988025 = 2991019) B2991019
theorem B7560641 : Blo 1048611 7560641 := bstep (se 2 (by rfl) ⟨2835240, by rfl⟩ : syracuseStep 7560641 = 5670481) B5670481
theorem B64806551 : Blo 1048611 64806551 := bstep (se 1 (by rfl) ⟨48604913, by rfl⟩ : syracuseStep 64806551 = 97209827) B97209827
theorem B6741737 : Blo 1048611 6741737 := bstep (se 2 (by rfl) ⟨2528151, by rfl⟩ : syracuseStep 6741737 = 5056303) B5056303
theorem B5989099 : Blo 1048611 5989099 := bstep (se 1 (by rfl) ⟨4491824, by rfl⟩ : syracuseStep 5989099 = 8983649) B8983649
theorem B6054907 : Blo 1048611 6054907 := bstep (se 1 (by rfl) ⟨4541180, by rfl⟩ : syracuseStep 6054907 = 9082361) B9082361
theorem B2844809 : Blo 1048611 2844809 := bstep (se 2 (by rfl) ⟨1066803, by rfl⟩ : syracuseStep 2844809 = 2133607) B2133607
theorem B5991083 : Blo 1048611 5991083 := bstep (se 1 (by rfl) ⟨4493312, by rfl⟩ : syracuseStep 5991083 = 8986625) B8986625
theorem B6057143 : Blo 1048611 6057143 := bstep (se 1 (by rfl) ⟨4542857, by rfl⟩ : syracuseStep 6057143 = 9085715) B9085715
theorem B3371215 : Blo 1048611 3371215 := bstep (se 1 (by rfl) ⟨2528411, by rfl⟩ : syracuseStep 3371215 = 5056823) B5056823
theorem B3600683 : Blo 1048611 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B10090271 : Blo 1048611 10090271 := bstep (se 1 (by rfl) ⟨7567703, by rfl⟩ : syracuseStep 10090271 = 15135407) B15135407
theorem B2553977 : Blo 1048611 2553977 := bstep (se 2 (by rfl) ⟨957741, by rfl⟩ : syracuseStep 2553977 = 1915483) B1915483
theorem B1996967 : Blo 1048611 1996967 := bstep (se 1 (by rfl) ⟨1497725, by rfl⟩ : syracuseStep 1996967 = 2995451) B2995451
theorem B9566383 : Blo 1048611 9566383 := bstep (se 1 (by rfl) ⟨7174787, by rfl⟩ : syracuseStep 9566383 = 14349575) B14349575
theorem B2521577 : Blo 1048611 2521577 := bstep (se 2 (by rfl) ⟨945591, by rfl⟩ : syracuseStep 2521577 = 1891183) B1891183
theorem B2424503 : Blo 1048611 2424503 := bstep (se 1 (by rfl) ⟨1818377, by rfl⟩ : syracuseStep 2424503 = 3636755) B3636755
theorem B221544467 : Blo 1048611 221544467 := bstep (se 1 (by rfl) ⟨166158350, by rfl⟩ : syracuseStep 221544467 = 332316701) B332316701
theorem B4554947 : Blo 1048611 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B2654471 : Blo 1048611 2654471 := bstep (se 1 (by rfl) ⟨1990853, by rfl⟩ : syracuseStep 2654471 = 3981707) B3981707
theorem B4489501 : Blo 1048611 4489501 := bstep (se 3 (by rfl) ⟨841781, by rfl⟩ : syracuseStep 4489501 = 1683563) B1683563
theorem B1048935 : Blo 1048611 1048935 := bstep (se 1 (by rfl) ⟨786701, by rfl⟩ : syracuseStep 1048935 = 1573403) B1573403
theorem B2654603 : Blo 1048611 2654603 := bstep (se 1 (by rfl) ⟨1990952, by rfl⟩ : syracuseStep 2654603 = 3981905) B3981905
theorem B1049055 : Blo 1048611 1049055 := bstep (se 1 (by rfl) ⟨786791, by rfl⟩ : syracuseStep 1049055 = 1573583) B1573583
theorem B1769951 : Blo 1048611 1769951 := bstep (se 1 (by rfl) ⟨1327463, by rfl⟩ : syracuseStep 1769951 = 2654927) B2654927
theorem B2359835 : Blo 1048611 2359835 := bstep (se 1 (by rfl) ⟨1769876, by rfl⟩ : syracuseStep 2359835 = 3539753) B3539753
theorem B1049135 : Blo 1048611 1049135 := bstep (se 1 (by rfl) ⟨786851, by rfl⟩ : syracuseStep 1049135 = 1573703) B1573703
theorem B1049179 : Blo 1048611 1049179 := bstep (se 1 (by rfl) ⟨786884, by rfl⟩ : syracuseStep 1049179 = 1573769) B1573769
theorem B1573631 : Blo 1048611 1573631 := bstep (se 1 (by rfl) ⟨1180223, by rfl⟩ : syracuseStep 1573631 = 2360447) B2360447
theorem B1049343 : Blo 1048611 1049343 := bstep (se 1 (by rfl) ⟨787007, by rfl⟩ : syracuseStep 1049343 = 1574015) B1574015
theorem B1180507 : Blo 1048611 1180507 := bstep (se 1 (by rfl) ⟨885380, by rfl⟩ : syracuseStep 1180507 = 1770761) B1770761
theorem B1049435 : Blo 1048611 1049435 := bstep (se 1 (by rfl) ⟨787076, by rfl⟩ : syracuseStep 1049435 = 1574153) B1574153
theorem B2360393 : Blo 1048611 2360393 := bstep (se 2 (by rfl) ⟨885147, by rfl⟩ : syracuseStep 2360393 = 1770295) B1770295
theorem B1049755 : Blo 1048611 1049755 := bstep (se 1 (by rfl) ⟨787316, by rfl⟩ : syracuseStep 1049755 = 1574633) B1574633
theorem B1049759 : Blo 1048611 1049759 := bstep (se 1 (by rfl) ⟨787319, by rfl⟩ : syracuseStep 1049759 = 1574639) B1574639
theorem B1049927 : Blo 1048611 1049927 := bstep (se 1 (by rfl) ⟨787445, by rfl⟩ : syracuseStep 1049927 = 1574891) B1574891
theorem B1050095 : Blo 1048611 1050095 := bstep (se 1 (by rfl) ⟨787571, by rfl⟩ : syracuseStep 1050095 = 1575143) B1575143
theorem B1574399 : Blo 1048611 1574399 := bstep (se 1 (by rfl) ⟨1180799, by rfl⟩ : syracuseStep 1574399 = 2361599) B2361599
theorem B1050111 : Blo 1048611 1050111 := bstep (se 1 (by rfl) ⟨787583, by rfl⟩ : syracuseStep 1050111 = 1575167) B1575167
theorem B1050203 : Blo 1048611 1050203 := bstep (se 1 (by rfl) ⟨787652, by rfl⟩ : syracuseStep 1050203 = 1575305) B1575305
theorem B1771247 : Blo 1048611 1771247 := bstep (se 1 (by rfl) ⟨1328435, by rfl⟩ : syracuseStep 1771247 = 2656871) B2656871
theorem B12781547 : Blo 1048611 12781547 := bstep (se 1 (by rfl) ⟨9586160, by rfl⟩ : syracuseStep 12781547 = 19172321) B19172321
theorem B5671127 : Blo 1048611 5671127 := bstep (se 1 (by rfl) ⟨4253345, by rfl⟩ : syracuseStep 5671127 = 8506691) B8506691
theorem B1050943 : Blo 1048611 1050943 := bstep (se 1 (by rfl) ⟨788207, by rfl⟩ : syracuseStep 1050943 = 1576415) B1576415
theorem B1182055 : Blo 1048611 1182055 := bstep (se 1 (by rfl) ⟨886541, by rfl⟩ : syracuseStep 1182055 = 1773083) B1773083
theorem B1050983 : Blo 1048611 1050983 := bstep (se 1 (by rfl) ⟨788237, by rfl⟩ : syracuseStep 1050983 = 1576475) B1576475
theorem B1051071 : Blo 1048611 1051071 := bstep (se 1 (by rfl) ⟨788303, by rfl⟩ : syracuseStep 1051071 = 1576607) B1576607
theorem B2361833 : Blo 1048611 2361833 := bstep (se 2 (by rfl) ⟨885687, by rfl⟩ : syracuseStep 2361833 = 1771375) B1771375
theorem B1575401 : Blo 1048611 1575401 := bstep (se 2 (by rfl) ⟨590775, by rfl⟩ : syracuseStep 1575401 = 1181551) B1181551
theorem B1051247 : Blo 1048611 1051247 := bstep (se 1 (by rfl) ⟨788435, by rfl⟩ : syracuseStep 1051247 = 1576871) B1576871
theorem B1575551 : Blo 1048611 1575551 := bstep (se 1 (by rfl) ⟨1181663, by rfl⟩ : syracuseStep 1575551 = 2363327) B2363327
theorem B1051263 : Blo 1048611 1051263 := bstep (se 1 (by rfl) ⟨788447, by rfl⟩ : syracuseStep 1051263 = 1576895) B1576895
theorem B5048999 : Blo 1048611 5048999 := bstep (se 1 (by rfl) ⟨3786749, by rfl⟩ : syracuseStep 5048999 = 7573499) B7573499
theorem B1772239 : Blo 1048611 1772239 := bstep (se 1 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 1772239 = 2658359) B2658359
theorem B1051367 : Blo 1048611 1051367 := bstep (se 1 (by rfl) ⟨788525, by rfl⟩ : syracuseStep 1051367 = 1577051) B1577051
theorem B2525951 : Blo 1048611 2525951 := bstep (se 1 (by rfl) ⟨1894463, by rfl⟩ : syracuseStep 2525951 = 3788927) B3788927
theorem B2362121 : Blo 1048611 2362121 := bstep (se 2 (by rfl) ⟨885795, by rfl⟩ : syracuseStep 2362121 = 1771591) B1771591
theorem B1575689 : Blo 1048611 1575689 := bstep (se 2 (by rfl) ⟨590883, by rfl⟩ : syracuseStep 1575689 = 1181767) B1181767
theorem B1051463 : Blo 1048611 1051463 := bstep (se 1 (by rfl) ⟨788597, by rfl⟩ : syracuseStep 1051463 = 1577195) B1577195
theorem B1051503 : Blo 1048611 1051503 := bstep (se 1 (by rfl) ⟨788627, by rfl⟩ : syracuseStep 1051503 = 1577255) B1577255
theorem B1575929 : Blo 1048611 1575929 := bstep (se 2 (by rfl) ⟨590973, by rfl⟩ : syracuseStep 1575929 = 1181947) B1181947
theorem B1051679 : Blo 1048611 1051679 := bstep (se 1 (by rfl) ⟨788759, by rfl⟩ : syracuseStep 1051679 = 1577519) B1577519
theorem B1772617 : Blo 1048611 1772617 := bstep (se 2 (by rfl) ⟨664731, by rfl⟩ : syracuseStep 1772617 = 1329463) B1329463
theorem B2362535 : Blo 1048611 2362535 := bstep (se 1 (by rfl) ⟨1771901, by rfl⟩ : syracuseStep 2362535 = 3543803) B3543803
theorem B1576103 : Blo 1048611 1576103 := bstep (se 1 (by rfl) ⟨1182077, by rfl⟩ : syracuseStep 1576103 = 2364155) B2364155
theorem B1051815 : Blo 1048611 1051815 := bstep (se 1 (by rfl) ⟨788861, by rfl⟩ : syracuseStep 1051815 = 1577723) B1577723
theorem B2362697 : Blo 1048611 2362697 := bstep (se 2 (by rfl) ⟨886011, by rfl⟩ : syracuseStep 2362697 = 1772023) B1772023
theorem B1052063 : Blo 1048611 1052063 := bstep (se 1 (by rfl) ⟨789047, by rfl⟩ : syracuseStep 1052063 = 1578095) B1578095
theorem B1052111 : Blo 1048611 1052111 := bstep (se 1 (by rfl) ⟨789083, by rfl⟩ : syracuseStep 1052111 = 1578167) B1578167
theorem B1576553 : Blo 1048611 1576553 := bstep (se 2 (by rfl) ⟨591207, by rfl⟩ : syracuseStep 1576553 = 1182415) B1182415
theorem B1052271 : Blo 1048611 1052271 := bstep (se 1 (by rfl) ⟨789203, by rfl⟩ : syracuseStep 1052271 = 1578407) B1578407
theorem B1052391 : Blo 1048611 1052391 := bstep (se 1 (by rfl) ⟨789293, by rfl⟩ : syracuseStep 1052391 = 1578587) B1578587
theorem B1576841 : Blo 1048611 1576841 := bstep (se 2 (by rfl) ⟨591315, by rfl⟩ : syracuseStep 1576841 = 1182631) B1182631
theorem B13438979 : Blo 1048611 13438979 := bstep (se 1 (by rfl) ⟨10079234, by rfl⟩ : syracuseStep 13438979 = 20158469) B20158469
theorem B1577081 : Blo 1048611 1577081 := bstep (se 2 (by rfl) ⟨591405, by rfl⟩ : syracuseStep 1577081 = 1182811) B1182811
theorem B2986247 : Blo 1048611 2986247 := bstep (se 1 (by rfl) ⟨2239685, by rfl⟩ : syracuseStep 2986247 = 4479371) B4479371
theorem B2658683 : Blo 1048611 2658683 := bstep (se 1 (by rfl) ⟨1994012, by rfl⟩ : syracuseStep 2658683 = 3988025) B3988025
theorem B31134131 : Blo 1048611 31134131 := bstep (se 1 (by rfl) ⟨23350598, by rfl⟩ : syracuseStep 31134131 = 46701197) B46701197
theorem B3543479 : Blo 1048611 3543479 := bstep (se 1 (by rfl) ⟨2657609, by rfl⟩ : syracuseStep 3543479 = 5315219) B5315219
theorem B1577639 : Blo 1048611 1577639 := bstep (se 1 (by rfl) ⟨1183229, by rfl⟩ : syracuseStep 1577639 = 2366459) B2366459
theorem B1774271 : Blo 1048611 1774271 := bstep (se 1 (by rfl) ⟨1330703, by rfl⟩ : syracuseStep 1774271 = 2661407) B2661407
theorem B2364191 : Blo 1048611 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B1577759 : Blo 1048611 1577759 := bstep (se 1 (by rfl) ⟨1183319, by rfl⟩ : syracuseStep 1577759 = 2366639) B2366639
theorem B1774399 : Blo 1048611 1774399 := bstep (se 1 (by rfl) ⟨1330799, by rfl⟩ : syracuseStep 1774399 = 2661599) B2661599
theorem B1577855 : Blo 1048611 1577855 := bstep (se 1 (by rfl) ⟨1183391, by rfl⟩ : syracuseStep 1577855 = 2366783) B2366783
theorem B1577927 : Blo 1048611 1577927 := bstep (se 1 (by rfl) ⟨1183445, by rfl⟩ : syracuseStep 1577927 = 2366891) B2366891
theorem B15143881 : Blo 1048611 15143881 := bstep (se 2 (by rfl) ⟨5678955, by rfl⟩ : syracuseStep 15143881 = 11357911) B11357911
theorem B2364371 : Blo 1048611 2364371 := bstep (se 1 (by rfl) ⟨1773278, by rfl⟩ : syracuseStep 2364371 = 3546557) B3546557
theorem B1774703 : Blo 1048611 1774703 := bstep (se 1 (by rfl) ⟨1331027, by rfl⟩ : syracuseStep 1774703 = 2662055) B2662055
theorem B4494491 : Blo 1048611 4494491 := bstep (se 1 (by rfl) ⟨3370868, by rfl⟩ : syracuseStep 4494491 = 6741737) B6741737
theorem B20190383 : Blo 1048611 20190383 := bstep (se 1 (by rfl) ⟨15142787, by rfl⟩ : syracuseStep 20190383 = 30285575) B30285575
theorem B1578239 : Blo 1048611 1578239 := bstep (se 1 (by rfl) ⟨1183679, by rfl⟩ : syracuseStep 1578239 = 2367359) B2367359
theorem B1578287 : Blo 1048611 1578287 := bstep (se 1 (by rfl) ⟨1183715, by rfl⟩ : syracuseStep 1578287 = 2367431) B2367431
theorem B3544559 : Blo 1048611 3544559 := bstep (se 1 (by rfl) ⟨2658419, by rfl⟩ : syracuseStep 3544559 = 5316839) B5316839
theorem B2364947 : Blo 1048611 2364947 := bstep (se 1 (by rfl) ⟨1773710, by rfl⟩ : syracuseStep 2364947 = 3547421) B3547421
theorem B1578527 : Blo 1048611 1578527 := bstep (se 1 (by rfl) ⟨1183895, by rfl⟩ : syracuseStep 1578527 = 2367791) B2367791
theorem B8525375 : Blo 1048611 8525375 := bstep (se 1 (by rfl) ⟨6394031, by rfl⟩ : syracuseStep 8525375 = 12788063) B12788063
theorem B4494953 : Blo 1048611 4494953 := bstep (se 2 (by rfl) ⟨1685607, by rfl⟩ : syracuseStep 4494953 = 3371215) B3371215
theorem B1775803 : Blo 1048611 1775803 := bstep (se 1 (by rfl) ⟨1331852, by rfl⟩ : syracuseStep 1775803 = 2663705) B2663705
theorem B2365775 : Blo 1048611 2365775 := bstep (se 1 (by rfl) ⟨1774331, by rfl⟩ : syracuseStep 2365775 = 3548663) B3548663
theorem B6724205 : Blo 1048611 6724205 := bstep (se 3 (by rfl) ⟨1260788, by rfl⟩ : syracuseStep 6724205 = 2521577) B2521577
theorem B8985563 : Blo 1048611 8985563 := bstep (se 1 (by rfl) ⟨6739172, by rfl⟩ : syracuseStep 8985563 = 13478345) B13478345
theorem B2366495 : Blo 1048611 2366495 := bstep (se 1 (by rfl) ⟨1774871, by rfl⟩ : syracuseStep 2366495 = 3549743) B3549743
theorem B2366675 : Blo 1048611 2366675 := bstep (se 1 (by rfl) ⟨1775006, by rfl⟩ : syracuseStep 2366675 = 3550013) B3550013
theorem B4038095 : Blo 1048611 4038095 := bstep (se 1 (by rfl) ⟨3028571, by rfl⟩ : syracuseStep 4038095 = 6057143) B6057143
theorem B2400455 : Blo 1048611 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B12755177 : Blo 1048611 12755177 := bstep (se 2 (by rfl) ⟨4783191, by rfl⟩ : syracuseStep 12755177 = 9566383) B9566383
theorem B2368007 : Blo 1048611 2368007 := bstep (se 1 (by rfl) ⟨1776005, by rfl⟩ : syracuseStep 2368007 = 3552011) B3552011
theorem B6726847 : Blo 1048611 6726847 := bstep (se 1 (by rfl) ⟨5045135, by rfl⟩ : syracuseStep 6726847 = 10090271) B10090271
theorem B10101995 : Blo 1048611 10101995 := bstep (se 1 (by rfl) ⟨7576496, by rfl⟩ : syracuseStep 10101995 = 15152993) B15152993
theorem B3548447 : Blo 1048611 3548447 := bstep (se 1 (by rfl) ⟨2661335, by rfl⟩ : syracuseStep 3548447 = 5322671) B5322671
theorem B8988023 : Blo 1048611 8988023 := bstep (se 1 (by rfl) ⟨6741017, by rfl⟩ : syracuseStep 8988023 = 13482035) B13482035
theorem B1616335 : Blo 1048611 1616335 := bstep (se 1 (by rfl) ⟨1212251, by rfl⟩ : syracuseStep 1616335 = 2424503) B2424503
theorem B7973801 : Blo 1048611 7973801 := bstep (se 2 (by rfl) ⟨2990175, by rfl⟩ : syracuseStep 7973801 = 5980351) B5980351
theorem B3550391 : Blo 1048611 3550391 := bstep (se 1 (by rfl) ⟨2662793, by rfl⟩ : syracuseStep 3550391 = 5325587) B5325587
theorem B9580393 : Blo 1048611 9580393 := bstep (se 2 (by rfl) ⟨3592647, by rfl⟩ : syracuseStep 9580393 = 7185295) B7185295
theorem B8073209 : Blo 1048611 8073209 := bstep (se 2 (by rfl) ⟨3027453, by rfl⟩ : syracuseStep 8073209 = 6054907) B6054907
theorem B5976251 : Blo 1048611 5976251 := bstep (se 1 (by rfl) ⟨4482188, by rfl⟩ : syracuseStep 5976251 = 8964377) B8964377
theorem B20197835 : Blo 1048611 20197835 := bstep (se 1 (by rfl) ⟨15148376, by rfl⟩ : syracuseStep 20197835 = 30296753) B30296753
theorem B3551849 : Blo 1048611 3551849 := bstep (se 2 (by rfl) ⟨1331943, by rfl⟩ : syracuseStep 3551849 = 2663887) B2663887
theorem B3552281 : Blo 1048611 3552281 := bstep (se 2 (by rfl) ⟨1332105, by rfl⟩ : syracuseStep 3552281 = 2664211) B2664211
theorem B3552443 : Blo 1048611 3552443 := bstep (se 1 (by rfl) ⟨2664332, by rfl⟩ : syracuseStep 3552443 = 5328665) B5328665
theorem B3028157 : Blo 1048611 3028157 := bstep (se 3 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 3028157 = 1135559) B1135559
theorem B88716545 : Blo 1048611 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B6076217 : Blo 1048611 6076217 := bstep (se 2 (by rfl) ⟨2278581, by rfl⟩ : syracuseStep 6076217 = 4557163) B4557163
theorem B2242495 : Blo 1048611 2242495 := bstep (se 1 (by rfl) ⟨1681871, by rfl⟩ : syracuseStep 2242495 = 3363743) B3363743
theorem B2242667 : Blo 1048611 2242667 := bstep (se 1 (by rfl) ⟨1682000, by rfl⟩ : syracuseStep 2242667 = 3364001) B3364001
theorem B2996783 : Blo 1048611 2996783 := bstep (se 1 (by rfl) ⟨2247587, by rfl⟩ : syracuseStep 2996783 = 4495175) B4495175
theorem B10795679 : Blo 1048611 10795679 := bstep (se 1 (by rfl) ⟨8096759, by rfl⟩ : syracuseStep 10795679 = 16193519) B16193519
theorem B2046719 : Blo 1048611 2046719 := bstep (se 1 (by rfl) ⟨1535039, by rfl⟩ : syracuseStep 2046719 = 3070079) B3070079
theorem B5454839 : Blo 1048611 5454839 := bstep (se 1 (by rfl) ⟨4091129, by rfl⟩ : syracuseStep 5454839 = 8182259) B8182259
theorem B43204367 : Blo 1048611 43204367 := bstep (se 1 (by rfl) ⟨32403275, by rfl⟩ : syracuseStep 43204367 = 64806551) B64806551
theorem B2244905 : Blo 1048611 2244905 := bstep (se 2 (by rfl) ⟨841839, by rfl⟩ : syracuseStep 2244905 = 1683679) B1683679
theorem B84067865 : Blo 1048611 84067865 := bstep (se 2 (by rfl) ⟨31525449, by rfl⟩ : syracuseStep 84067865 = 63050899) B63050899
theorem B3589775 : Blo 1048611 3589775 := bstep (se 1 (by rfl) ⟨2692331, by rfl⟩ : syracuseStep 3589775 = 5384663) B5384663
theorem B7194599 : Blo 1048611 7194599 := bstep (se 1 (by rfl) ⟨5395949, by rfl⟩ : syracuseStep 7194599 = 10791899) B10791899
theorem B3983863 : Blo 1048611 3983863 := bstep (se 1 (by rfl) ⟨2987897, by rfl⟩ : syracuseStep 3983863 = 5975795) B5975795
theorem B8964755 : Blo 1048611 8964755 := bstep (se 1 (by rfl) ⟨6723566, by rfl⟩ : syracuseStep 8964755 = 13447133) B13447133
theorem B5983085 : Blo 1048611 5983085 := bstep (se 3 (by rfl) ⟨1121828, by rfl⟩ : syracuseStep 5983085 = 2243657) B2243657
theorem B3985139 : Blo 1048611 3985139 := bstep (se 1 (by rfl) ⟨2988854, by rfl⟩ : syracuseStep 3985139 = 5977709) B5977709
theorem B8966153 : Blo 1048611 8966153 := bstep (se 2 (by rfl) ⟨3362307, by rfl⟩ : syracuseStep 8966153 = 6724615) B6724615
theorem B1331311 : Blo 1048611 1331311 := bstep (se 1 (by rfl) ⟨998483, by rfl⟩ : syracuseStep 1331311 = 1996967) B1996967
theorem B147509855 : Blo 1048611 147509855 := bstep (se 1 (by rfl) ⟨110632391, by rfl⟩ : syracuseStep 147509855 = 221264783) B221264783
theorem B49207499 : Blo 1048611 49207499 := bstep (se 1 (by rfl) ⟨36905624, by rfl⟩ : syracuseStep 49207499 = 73811249) B73811249
theorem B3987751 : Blo 1048611 3987751 := bstep (se 1 (by rfl) ⟨2990813, by rfl⟩ : syracuseStep 3987751 = 5981627) B5981627
theorem B7985465 : Blo 1048611 7985465 := bstep (se 2 (by rfl) ⟨2994549, by rfl⟩ : syracuseStep 7985465 = 5989099) B5989099
theorem B4544923 : Blo 1048611 4544923 := bstep (se 1 (by rfl) ⟨3408692, by rfl⟩ : syracuseStep 4544923 = 6817385) B6817385
theorem B11360681 : Blo 1048611 11360681 := bstep (se 2 (by rfl) ⟨4260255, by rfl⟩ : syracuseStep 11360681 = 8520511) B8520511
theorem B20470283 : Blo 1048611 20470283 := bstep (se 1 (by rfl) ⟨15352712, by rfl⟩ : syracuseStep 20470283 = 30705425) B30705425
theorem B15129119 : Blo 1048611 15129119 := bstep (se 1 (by rfl) ⟨11346839, by rfl⟩ : syracuseStep 15129119 = 22693679) B22693679
theorem B10771217 : Blo 1048611 10771217 := bstep (se 2 (by rfl) ⟨4039206, by rfl⟩ : syracuseStep 10771217 = 8078413) B8078413
theorem B4480343 : Blo 1048611 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B1892063 : Blo 1048611 1892063 := bstep (se 1 (by rfl) ⟨1419047, by rfl⟩ : syracuseStep 1892063 = 2838095) B2838095
theorem B1991081 : Blo 1048611 1991081 := bstep (se 2 (by rfl) ⟨746655, by rfl⟩ : syracuseStep 1991081 = 1493311) B1493311
theorem B7563091 : Blo 1048611 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B1992539 : Blo 1048611 1992539 := bstep (se 1 (by rfl) ⟨1494404, by rfl⟩ : syracuseStep 1992539 = 2988809) B2988809
theorem B8513437 : Blo 1048611 8513437 := bstep (se 3 (by rfl) ⟨1596269, by rfl⟩ : syracuseStep 8513437 = 3192539) B3192539
theorem B5040427 : Blo 1048611 5040427 := bstep (se 1 (by rfl) ⟨3780320, by rfl⟩ : syracuseStep 5040427 = 7560641) B7560641
theorem B4483487 : Blo 1048611 4483487 := bstep (se 1 (by rfl) ⟨3362615, by rfl⟩ : syracuseStep 4483487 = 6725231) B6725231
theorem B3369575 : Blo 1048611 3369575 := bstep (se 1 (by rfl) ⟨2527181, by rfl⟩ : syracuseStep 3369575 = 5054363) B5054363
theorem B1993511 : Blo 1048611 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B58354937 : Blo 1048611 58354937 := bstep (se 2 (by rfl) ⟨21883101, by rfl⟩ : syracuseStep 58354937 = 43766203) B43766203
theorem B57535757 : Blo 1048611 57535757 := bstep (se 3 (by rfl) ⟨10787954, by rfl⟩ : syracuseStep 57535757 = 21575909) B21575909
theorem B8088875 : Blo 1048611 8088875 := bstep (se 1 (by rfl) ⟨6066656, by rfl⟩ : syracuseStep 8088875 = 12133313) B12133313
theorem B1994377 : Blo 1048611 1994377 := bstep (se 2 (by rfl) ⟨747891, by rfl⟩ : syracuseStep 1994377 = 1495783) B1495783
theorem B3370663 : Blo 1048611 3370663 := bstep (se 1 (by rfl) ⟨2527997, by rfl⟩ : syracuseStep 3370663 = 5055995) B5055995
theorem B1896539 : Blo 1048611 1896539 := bstep (se 1 (by rfl) ⟨1422404, by rfl⟩ : syracuseStep 1896539 = 2844809) B2844809
theorem B3994055 : Blo 1048611 3994055 := bstep (se 1 (by rfl) ⟨2995541, by rfl⟩ : syracuseStep 3994055 = 5991083) B5991083
theorem B14349797 : Blo 1048611 14349797 := bstep (se 4 (by rfl) ⟨1345293, by rfl⟩ : syracuseStep 14349797 = 2690587) B2690587
theorem B4487177 : Blo 1048611 4487177 := bstep (se 2 (by rfl) ⟨1682691, by rfl⟩ : syracuseStep 4487177 = 3365383) B3365383
theorem B1997111 : Blo 1048611 1997111 := bstep (se 1 (by rfl) ⟨1497833, by rfl⟩ : syracuseStep 1997111 = 2995667) B2995667
theorem B9730783 : Blo 1048611 9730783 := bstep (se 1 (by rfl) ⟨7298087, by rfl⟩ : syracuseStep 9730783 = 14596175) B14596175
theorem B1702651 : Blo 1048611 1702651 := bstep (se 1 (by rfl) ⟨1276988, by rfl⟩ : syracuseStep 1702651 = 2553977) B2553977
theorem B1769647 : Blo 1048611 1769647 := bstep (se 1 (by rfl) ⟨1327235, by rfl⟩ : syracuseStep 1769647 = 2654471) B2654471
theorem B1769735 : Blo 1048611 1769735 := bstep (se 1 (by rfl) ⟨1327301, by rfl⟩ : syracuseStep 1769735 = 2654603) B2654603
theorem B1179967 : Blo 1048611 1179967 := bstep (se 1 (by rfl) ⟨884975, by rfl⟩ : syracuseStep 1179967 = 1769951) B1769951
theorem B1573223 : Blo 1048611 1573223 := bstep (se 1 (by rfl) ⟨1179917, by rfl⟩ : syracuseStep 1573223 = 2359835) B2359835
theorem B1049087 : Blo 1048611 1049087 := bstep (se 1 (by rfl) ⟨786815, by rfl⟩ : syracuseStep 1049087 = 1573631) B1573631
theorem B1573595 : Blo 1048611 1573595 := bstep (se 1 (by rfl) ⟨1180196, by rfl⟩ : syracuseStep 1573595 = 2360393) B2360393
theorem B1049599 : Blo 1048611 1049599 := bstep (se 1 (by rfl) ⟨787199, by rfl⟩ : syracuseStep 1049599 = 1574399) B1574399
theorem B2393183 : Blo 1048611 2393183 := bstep (se 1 (by rfl) ⟨1794887, by rfl⟩ : syracuseStep 2393183 = 3589775) B3589775
theorem B5309549 : Blo 1048611 5309549 := bstep (se 3 (by rfl) ⟨995540, by rfl⟩ : syracuseStep 5309549 = 1991081) B1991081
theorem B1574009 : Blo 1048611 1574009 := bstep (se 2 (by rfl) ⟨590253, by rfl⟩ : syracuseStep 1574009 = 1180507) B1180507
theorem B1180831 : Blo 1048611 1180831 := bstep (se 1 (by rfl) ⟨885623, by rfl⟩ : syracuseStep 1180831 = 1771247) B1771247
theorem B8521031 : Blo 1048611 8521031 := bstep (se 1 (by rfl) ⟨6390773, by rfl⟩ : syracuseStep 8521031 = 12781547) B12781547
theorem B1574555 : Blo 1048611 1574555 := bstep (se 1 (by rfl) ⟨1180916, by rfl⟩ : syracuseStep 1574555 = 2361833) B2361833
theorem B1050267 : Blo 1048611 1050267 := bstep (se 1 (by rfl) ⟨787700, by rfl⟩ : syracuseStep 1050267 = 1575401) B1575401
theorem B1050367 : Blo 1048611 1050367 := bstep (se 1 (by rfl) ⟨787775, by rfl⟩ : syracuseStep 1050367 = 1575551) B1575551
theorem B1050459 : Blo 1048611 1050459 := bstep (se 1 (by rfl) ⟨787844, by rfl⟩ : syracuseStep 1050459 = 1575689) B1575689
theorem B1574747 : Blo 1048611 1574747 := bstep (se 1 (by rfl) ⟨1181060, by rfl⟩ : syracuseStep 1574747 = 2362121) B2362121
theorem B1050619 : Blo 1048611 1050619 := bstep (se 1 (by rfl) ⟨787964, by rfl⟩ : syracuseStep 1050619 = 1575929) B1575929
theorem B1575023 : Blo 1048611 1575023 := bstep (se 1 (by rfl) ⟨1181267, by rfl⟩ : syracuseStep 1575023 = 2362535) B2362535
theorem B1050735 : Blo 1048611 1050735 := bstep (se 1 (by rfl) ⟨788051, by rfl⟩ : syracuseStep 1050735 = 1576103) B1576103
theorem B1575131 : Blo 1048611 1575131 := bstep (se 1 (by rfl) ⟨1181348, by rfl⟩ : syracuseStep 1575131 = 2362697) B2362697
theorem B1051035 : Blo 1048611 1051035 := bstep (se 1 (by rfl) ⟨788276, by rfl⟩ : syracuseStep 1051035 = 1576553) B1576553
theorem B8620453 : Blo 1048611 8620453 := bstep (se 4 (by rfl) ⟨808167, by rfl⟩ : syracuseStep 8620453 = 1616335) B1616335
theorem B2656759 : Blo 1048611 2656759 := bstep (se 1 (by rfl) ⟨1992569, by rfl⟩ : syracuseStep 2656759 = 3985139) B3985139
theorem B1051227 : Blo 1048611 1051227 := bstep (se 1 (by rfl) ⟨788420, by rfl⟩ : syracuseStep 1051227 = 1576841) B1576841
theorem B1051387 : Blo 1048611 1051387 := bstep (se 1 (by rfl) ⟨788540, by rfl⟩ : syracuseStep 1051387 = 1577081) B1577081
theorem B1772455 : Blo 1048611 1772455 := bstep (se 1 (by rfl) ⟨1329341, by rfl⟩ : syracuseStep 1772455 = 2658683) B2658683
theorem B2362319 : Blo 1048611 2362319 := bstep (se 1 (by rfl) ⟨1771739, by rfl⟩ : syracuseStep 2362319 = 3543479) B3543479
theorem B6720569 : Blo 1048611 6720569 := bstep (se 2 (by rfl) ⟨2520213, by rfl⟩ : syracuseStep 6720569 = 5040427) B5040427
theorem B98339903 : Blo 1048611 98339903 := bstep (se 1 (by rfl) ⟨73754927, by rfl⟩ : syracuseStep 98339903 = 147509855) B147509855
theorem B1051759 : Blo 1048611 1051759 := bstep (se 1 (by rfl) ⟨788819, by rfl⟩ : syracuseStep 1051759 = 1577639) B1577639
theorem B1182847 : Blo 1048611 1182847 := bstep (se 1 (by rfl) ⟨887135, by rfl⟩ : syracuseStep 1182847 = 1774271) B1774271
theorem B1576073 : Blo 1048611 1576073 := bstep (se 2 (by rfl) ⟨591027, by rfl⟩ : syracuseStep 1576073 = 1182055) B1182055
theorem B1576127 : Blo 1048611 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B1051839 : Blo 1048611 1051839 := bstep (se 1 (by rfl) ⟨788879, by rfl⟩ : syracuseStep 1051839 = 1577759) B1577759
theorem B1051903 : Blo 1048611 1051903 := bstep (se 1 (by rfl) ⟨788927, by rfl⟩ : syracuseStep 1051903 = 1577855) B1577855
theorem B1051951 : Blo 1048611 1051951 := bstep (se 1 (by rfl) ⟨788963, by rfl⟩ : syracuseStep 1051951 = 1577927) B1577927
theorem B1576247 : Blo 1048611 1576247 := bstep (se 1 (by rfl) ⟨1182185, by rfl⟩ : syracuseStep 1576247 = 2364371) B2364371
theorem B5311817 : Blo 1048611 5311817 := bstep (se 2 (by rfl) ⟨1991931, by rfl⟩ : syracuseStep 5311817 = 3983863) B3983863
theorem B1183135 : Blo 1048611 1183135 := bstep (se 1 (by rfl) ⟨887351, by rfl⟩ : syracuseStep 1183135 = 1774703) B1774703
theorem B1052159 : Blo 1048611 1052159 := bstep (se 1 (by rfl) ⟨789119, by rfl⟩ : syracuseStep 1052159 = 1578239) B1578239
theorem B1052191 : Blo 1048611 1052191 := bstep (se 1 (by rfl) ⟨789143, by rfl⟩ : syracuseStep 1052191 = 1578287) B1578287
theorem B2362985 : Blo 1048611 2362985 := bstep (se 2 (by rfl) ⟨886119, by rfl⟩ : syracuseStep 2362985 = 1772239) B1772239
theorem B2363039 : Blo 1048611 2363039 := bstep (se 1 (by rfl) ⟨1772279, by rfl⟩ : syracuseStep 2363039 = 3544559) B3544559
theorem B1576631 : Blo 1048611 1576631 := bstep (se 1 (by rfl) ⟨1182473, by rfl⟩ : syracuseStep 1576631 = 2364947) B2364947
theorem B1052351 : Blo 1048611 1052351 := bstep (se 1 (by rfl) ⟨789263, by rfl⟩ : syracuseStep 1052351 = 1578527) B1578527
theorem B2363489 : Blo 1048611 2363489 := bstep (se 2 (by rfl) ⟨886308, by rfl⟩ : syracuseStep 2363489 = 1772617) B1772617
theorem B32804999 : Blo 1048611 32804999 := bstep (se 1 (by rfl) ⟨24603749, by rfl⟩ : syracuseStep 32804999 = 49207499) B49207499
theorem B1577183 : Blo 1048611 1577183 := bstep (se 1 (by rfl) ⟨1182887, by rfl⟩ : syracuseStep 1577183 = 2365775) B2365775
theorem B7573787 : Blo 1048611 7573787 := bstep (se 1 (by rfl) ⟨5680340, by rfl⟩ : syracuseStep 7573787 = 11360681) B11360681
theorem B7180811 : Blo 1048611 7180811 := bstep (se 1 (by rfl) ⟨5385608, by rfl⟩ : syracuseStep 7180811 = 10771217) B10771217
theorem B1577663 : Blo 1048611 1577663 := bstep (se 1 (by rfl) ⟨1183247, by rfl⟩ : syracuseStep 1577663 = 2366495) B2366495
theorem B1577783 : Blo 1048611 1577783 := bstep (se 1 (by rfl) ⟨1183337, by rfl⟩ : syracuseStep 1577783 = 2366675) B2366675
theorem B2659169 : Blo 1048611 2659169 := bstep (se 2 (by rfl) ⟨997188, by rfl⟩ : syracuseStep 2659169 = 1994377) B1994377
theorem B4494217 : Blo 1048611 4494217 := bstep (se 2 (by rfl) ⟨1685331, by rfl⟩ : syracuseStep 4494217 = 3370663) B3370663
theorem B2986895 : Blo 1048611 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B5313437 : Blo 1048611 5313437 := bstep (se 3 (by rfl) ⟨996269, by rfl⟩ : syracuseStep 5313437 = 1992539) B1992539
theorem B2692063 : Blo 1048611 2692063 := bstep (se 1 (by rfl) ⟨2019047, by rfl⟩ : syracuseStep 2692063 = 4038095) B4038095
theorem B11965805 : Blo 1048611 11965805 := bstep (se 3 (by rfl) ⟨2243588, by rfl⟩ : syracuseStep 11965805 = 4487177) B4487177
theorem B1775081 : Blo 1048611 1775081 := bstep (se 2 (by rfl) ⟨665655, by rfl⟩ : syracuseStep 1775081 = 1331311) B1331311
theorem B1578671 : Blo 1048611 1578671 := bstep (se 1 (by rfl) ⟨1184003, by rfl⟩ : syracuseStep 1578671 = 2368007) B2368007
theorem B2365631 : Blo 1048611 2365631 := bstep (se 1 (by rfl) ⟨1774223, by rfl⟩ : syracuseStep 2365631 = 3548447) B3548447
theorem B2365865 : Blo 1048611 2365865 := bstep (se 2 (by rfl) ⟨887199, by rfl⟩ : syracuseStep 2365865 = 1774399) B1774399
theorem B20191841 : Blo 1048611 20191841 := bstep (se 2 (by rfl) ⟨7571940, by rfl⟩ : syracuseStep 20191841 = 15143881) B15143881
theorem B2988991 : Blo 1048611 2988991 := bstep (se 1 (by rfl) ⟨2241743, by rfl⟩ : syracuseStep 2988991 = 4483487) B4483487
theorem B5315867 : Blo 1048611 5315867 := bstep (se 1 (by rfl) ⟨3986900, by rfl⟩ : syracuseStep 5315867 = 7973801) B7973801
theorem B5316029 : Blo 1048611 5316029 := bstep (se 3 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 5316029 = 1993511) B1993511
theorem B2366927 : Blo 1048611 2366927 := bstep (se 1 (by rfl) ⟨1775195, by rfl⟩ : syracuseStep 2366927 = 3550391) B3550391
theorem B38903291 : Blo 1048611 38903291 := bstep (se 1 (by rfl) ⟨29177468, by rfl⟩ : syracuseStep 38903291 = 58354937) B58354937
theorem B5382139 : Blo 1048611 5382139 := bstep (se 1 (by rfl) ⟨4036604, by rfl⟩ : syracuseStep 5382139 = 8073209) B8073209
theorem B2367737 : Blo 1048611 2367737 := bstep (se 2 (by rfl) ⟨887901, by rfl⟩ : syracuseStep 2367737 = 1775803) B1775803
theorem B2662703 : Blo 1048611 2662703 := bstep (se 1 (by rfl) ⟨1997027, by rfl⟩ : syracuseStep 2662703 = 3994055) B3994055
theorem B5317001 : Blo 1048611 5317001 := bstep (se 2 (by rfl) ⟨1993875, by rfl⟩ : syracuseStep 5317001 = 3987751) B3987751
theorem B2367899 : Blo 1048611 2367899 := bstep (se 1 (by rfl) ⟨1775924, by rfl⟩ : syracuseStep 2367899 = 3551849) B3551849
theorem B2368187 : Blo 1048611 2368187 := bstep (se 1 (by rfl) ⟨1776140, by rfl⟩ : syracuseStep 2368187 = 3552281) B3552281
theorem B2368295 : Blo 1048611 2368295 := bstep (se 1 (by rfl) ⟨1776221, by rfl⟩ : syracuseStep 2368295 = 3552443) B3552443
theorem B2270201 : Blo 1048611 2270201 := bstep (se 2 (by rfl) ⟨851325, by rfl⟩ : syracuseStep 2270201 = 1702651) B1702651
theorem B147696311 : Blo 1048611 147696311 := bstep (se 1 (by rfl) ⟨110772233, by rfl⟩ : syracuseStep 147696311 = 221544467) B221544467
theorem B6401213 : Blo 1048611 6401213 := bstep (se 3 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 6401213 = 2400455) B2400455
theorem B20229749 : Blo 1048611 20229749 := bstep (se 5 (by rfl) ⟨948269, by rfl⟩ : syracuseStep 20229749 = 1896539) B1896539
theorem B56045243 : Blo 1048611 56045243 := bstep (se 1 (by rfl) ⟨42033932, by rfl⟩ : syracuseStep 56045243 = 84067865) B84067865
theorem B4796399 : Blo 1048611 4796399 := bstep (se 1 (by rfl) ⟨3597299, by rfl⟩ : syracuseStep 4796399 = 7194599) B7194599
theorem B3780751 : Blo 1048611 3780751 := bstep (se 1 (by rfl) ⟨2835563, by rfl⟩ : syracuseStep 3780751 = 5671127) B5671127
theorem B5976503 : Blo 1048611 5976503 := bstep (se 1 (by rfl) ⟨4482377, by rfl⟩ : syracuseStep 5976503 = 8964755) B8964755
theorem B11351249 : Blo 1048611 11351249 := bstep (se 2 (by rfl) ⟨4256718, by rfl⟩ : syracuseStep 11351249 = 8513437) B8513437
theorem B8959319 : Blo 1048611 8959319 := bstep (se 1 (by rfl) ⟨6719489, by rfl⟩ : syracuseStep 8959319 = 13438979) B13438979
theorem B5977435 : Blo 1048611 5977435 := bstep (se 1 (by rfl) ⟨4483076, by rfl⟩ : syracuseStep 5977435 = 8966153) B8966153
theorem B20756087 : Blo 1048611 20756087 := bstep (se 1 (by rfl) ⟨15567065, by rfl⟩ : syracuseStep 20756087 = 31134131) B31134131
theorem B2996327 : Blo 1048611 2996327 := bstep (se 1 (by rfl) ⟨2247245, by rfl⟩ : syracuseStep 2996327 = 4494491) B4494491
theorem B5683583 : Blo 1048611 5683583 := bstep (se 1 (by rfl) ⟨4262687, by rfl⟩ : syracuseStep 5683583 = 8525375) B8525375
theorem B2996635 : Blo 1048611 2996635 := bstep (se 1 (by rfl) ⟨2247476, by rfl⟩ : syracuseStep 2996635 = 4494953) B4494953
theorem B5323643 : Blo 1048611 5323643 := bstep (se 1 (by rfl) ⟨3992732, by rfl⟩ : syracuseStep 5323643 = 7985465) B7985465
theorem B13646855 : Blo 1048611 13646855 := bstep (se 1 (by rfl) ⟨10235141, by rfl⟩ : syracuseStep 13646855 = 20470283) B20470283
theorem B1261375 : Blo 1048611 1261375 := bstep (se 1 (by rfl) ⟨946031, by rfl⟩ : syracuseStep 1261375 = 1892063) B1892063
theorem B8503451 : Blo 1048611 8503451 := bstep (se 1 (by rfl) ⟨6377588, by rfl⟩ : syracuseStep 8503451 = 12755177) B12755177
theorem B6734663 : Blo 1048611 6734663 := bstep (se 1 (by rfl) ⟨5050997, by rfl⟩ : syracuseStep 6734663 = 10101995) B10101995
theorem B2246383 : Blo 1048611 2246383 := bstep (se 1 (by rfl) ⟨1684787, by rfl⟩ : syracuseStep 2246383 = 3369575) B3369575
theorem B6735869 : Blo 1048611 6735869 := bstep (se 3 (by rfl) ⟨1262975, by rfl⟩ : syracuseStep 6735869 = 2525951) B2525951
theorem B38357171 : Blo 1048611 38357171 := bstep (se 1 (by rfl) ⟨28767878, by rfl⟩ : syracuseStep 38357171 = 57535757) B57535757
theorem B5392583 : Blo 1048611 5392583 := bstep (se 1 (by rfl) ⟨4044437, by rfl⟩ : syracuseStep 5392583 = 8088875) B8088875
theorem B3984167 : Blo 1048611 3984167 := bstep (se 1 (by rfl) ⟨2988125, by rfl⟩ : syracuseStep 3984167 = 5976251) B5976251
theorem B2018771 : Blo 1048611 2018771 := bstep (se 1 (by rfl) ⟨1514078, by rfl⟩ : syracuseStep 2018771 = 3028157) B3028157
theorem B4050811 : Blo 1048611 4050811 := bstep (se 1 (by rfl) ⟨3038108, by rfl⟩ : syracuseStep 4050811 = 6076217) B6076217
theorem B1495111 : Blo 1048611 1495111 := bstep (se 1 (by rfl) ⟨1121333, by rfl⟩ : syracuseStep 1495111 = 2242667) B2242667
theorem B1331407 : Blo 1048611 1331407 := bstep (se 1 (by rfl) ⟨998555, by rfl⟩ : syracuseStep 1331407 = 1997111) B1997111
theorem B7197119 : Blo 1048611 7197119 := bstep (se 1 (by rfl) ⟨5397839, by rfl⟩ : syracuseStep 7197119 = 10795679) B10795679
theorem B1364479 : Blo 1048611 1364479 := bstep (se 1 (by rfl) ⟨1023359, by rfl⟩ : syracuseStep 1364479 = 2046719) B2046719
theorem B3036631 : Blo 1048611 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B1496603 : Blo 1048611 1496603 := bstep (se 1 (by rfl) ⟨1122452, by rfl⟩ : syracuseStep 1496603 = 2244905) B2244905
theorem B5986001 : Blo 1048611 5986001 := bstep (se 2 (by rfl) ⟨2244750, by rfl⟩ : syracuseStep 5986001 = 4489501) B4489501
theorem B8969129 : Blo 1048611 8969129 := bstep (se 2 (by rfl) ⟨3363423, by rfl⟩ : syracuseStep 8969129 = 6726847) B6726847
theorem B3365999 : Blo 1048611 3365999 := bstep (se 1 (by rfl) ⟨2524499, by rfl⟩ : syracuseStep 3365999 = 5048999) B5048999
theorem B3988723 : Blo 1048611 3988723 := bstep (se 1 (by rfl) ⟨2991542, by rfl⟩ : syracuseStep 3988723 = 5983085) B5983085
theorem B10084121 : Blo 1048611 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B1990831 : Blo 1048611 1990831 := bstep (se 1 (by rfl) ⟨1493123, by rfl⟩ : syracuseStep 1990831 = 2986247) B2986247
theorem B13460255 : Blo 1048611 13460255 := bstep (se 1 (by rfl) ⟨10095191, by rfl⟩ : syracuseStep 13460255 = 20190383) B20190383
theorem B51897509 : Blo 1048611 51897509 := bstep (se 4 (by rfl) ⟨4865391, by rfl⟩ : syracuseStep 51897509 = 9730783) B9730783
theorem B10086079 : Blo 1048611 10086079 := bstep (se 1 (by rfl) ⟨7564559, by rfl⟩ : syracuseStep 10086079 = 15129119) B15129119
theorem B4482803 : Blo 1048611 4482803 := bstep (se 1 (by rfl) ⟨3362102, by rfl⟩ : syracuseStep 4482803 = 6724205) B6724205
theorem B5990375 : Blo 1048611 5990375 := bstep (se 1 (by rfl) ⟨4492781, by rfl⟩ : syracuseStep 5990375 = 8985563) B8985563
theorem B12773857 : Blo 1048611 12773857 := bstep (se 2 (by rfl) ⟨4790196, by rfl⟩ : syracuseStep 12773857 = 9580393) B9580393
theorem B5992015 : Blo 1048611 5992015 := bstep (se 1 (by rfl) ⟨4494011, by rfl⟩ : syracuseStep 5992015 = 8988023) B8988023
theorem B13465223 : Blo 1048611 13465223 := bstep (se 1 (by rfl) ⟨10098917, by rfl⟩ : syracuseStep 13465223 = 20197835) B20197835
theorem B6059897 : Blo 1048611 6059897 := bstep (se 2 (by rfl) ⟨2272461, by rfl⟩ : syracuseStep 6059897 = 4544923) B4544923
theorem B59144363 : Blo 1048611 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B9566531 : Blo 1048611 9566531 := bstep (se 1 (by rfl) ⟨7174898, by rfl⟩ : syracuseStep 9566531 = 14349797) B14349797
theorem B1997855 : Blo 1048611 1997855 := bstep (se 1 (by rfl) ⟨1498391, by rfl⟩ : syracuseStep 1997855 = 2996783) B2996783
theorem B3636559 : Blo 1048611 3636559 := bstep (se 1 (by rfl) ⟨2727419, by rfl⟩ : syracuseStep 3636559 = 5454839) B5454839
theorem B11959973 : Blo 1048611 11959973 := bstep (se 4 (by rfl) ⟨1121247, by rfl⟩ : syracuseStep 11959973 = 2242495) B2242495
theorem B28802911 : Blo 1048611 28802911 := bstep (se 1 (by rfl) ⟨21602183, by rfl⟩ : syracuseStep 28802911 = 43204367) B43204367
theorem B5668967 : Blo 1048611 5668967 := bstep (se 1 (by rfl) ⟨4251725, by rfl⟩ : syracuseStep 5668967 = 8503451) B8503451
theorem B1179823 : Blo 1048611 1179823 := bstep (se 1 (by rfl) ⟨884867, by rfl⟩ : syracuseStep 1179823 = 1769735) B1769735
theorem B2654441 : Blo 1048611 2654441 := bstep (se 2 (by rfl) ⟨995415, by rfl⟩ : syracuseStep 2654441 = 1990831) B1990831
theorem B2359529 : Blo 1048611 2359529 := bstep (se 2 (by rfl) ⟨884823, by rfl⟩ : syracuseStep 2359529 = 1769647) B1769647
theorem B1048815 : Blo 1048611 1048815 := bstep (se 1 (by rfl) ⟨786611, by rfl⟩ : syracuseStep 1048815 = 1573223) B1573223
theorem B1573289 : Blo 1048611 1573289 := bstep (se 2 (by rfl) ⟨589983, by rfl⟩ : syracuseStep 1573289 = 1179967) B1179967
theorem B1049063 : Blo 1048611 1049063 := bstep (se 1 (by rfl) ⟨786797, by rfl⟩ : syracuseStep 1049063 = 1573595) B1573595
theorem B4489775 : Blo 1048611 4489775 := bstep (se 1 (by rfl) ⟨3367331, by rfl⟩ : syracuseStep 4489775 = 6734663) B6734663
theorem B3539699 : Blo 1048611 3539699 := bstep (se 1 (by rfl) ⟨2654774, by rfl⟩ : syracuseStep 3539699 = 5309549) B5309549
theorem B1049339 : Blo 1048611 1049339 := bstep (se 1 (by rfl) ⟨787004, by rfl⟩ : syracuseStep 1049339 = 1574009) B1574009
theorem B1049703 : Blo 1048611 1049703 := bstep (se 1 (by rfl) ⟨787277, by rfl⟩ : syracuseStep 1049703 = 1574555) B1574555
theorem B1049831 : Blo 1048611 1049831 := bstep (se 1 (by rfl) ⟨787373, by rfl⟩ : syracuseStep 1049831 = 1574747) B1574747
theorem B4490579 : Blo 1048611 4490579 := bstep (se 1 (by rfl) ⟨3367934, by rfl⟩ : syracuseStep 4490579 = 6735869) B6735869
theorem B1050015 : Blo 1048611 1050015 := bstep (se 1 (by rfl) ⟨787511, by rfl⟩ : syracuseStep 1050015 = 1575023) B1575023
theorem B1050087 : Blo 1048611 1050087 := bstep (se 1 (by rfl) ⟨787565, by rfl⟩ : syracuseStep 1050087 = 1575131) B1575131
theorem B1574441 : Blo 1048611 1574441 := bstep (se 2 (by rfl) ⟨590415, by rfl⟩ : syracuseStep 1574441 = 1180831) B1180831
theorem B2656111 : Blo 1048611 2656111 := bstep (se 1 (by rfl) ⟨1992083, by rfl⟩ : syracuseStep 2656111 = 3984167) B3984167
theorem B1574879 : Blo 1048611 1574879 := bstep (se 1 (by rfl) ⟨1181159, by rfl⟩ : syracuseStep 1574879 = 2362319) B2362319
theorem B1050715 : Blo 1048611 1050715 := bstep (se 1 (by rfl) ⟨788036, by rfl⟩ : syracuseStep 1050715 = 1576073) B1576073
theorem B1050751 : Blo 1048611 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B1050831 : Blo 1048611 1050831 := bstep (se 1 (by rfl) ⟨788123, by rfl⟩ : syracuseStep 1050831 = 1576247) B1576247
theorem B3541211 : Blo 1048611 3541211 := bstep (se 1 (by rfl) ⟨2655908, by rfl⟩ : syracuseStep 3541211 = 5311817) B5311817
theorem B1345847 : Blo 1048611 1345847 := bstep (se 1 (by rfl) ⟨1009385, by rfl⟩ : syracuseStep 1345847 = 2018771) B2018771
theorem B7965053 : Blo 1048611 7965053 := bstep (se 3 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 7965053 = 2986895) B2986895
theorem B1575323 : Blo 1048611 1575323 := bstep (se 1 (by rfl) ⟨1181492, by rfl⟩ : syracuseStep 1575323 = 2362985) B2362985
theorem B1575359 : Blo 1048611 1575359 := bstep (se 1 (by rfl) ⟨1181519, by rfl⟩ : syracuseStep 1575359 = 2363039) B2363039
theorem B1051087 : Blo 1048611 1051087 := bstep (se 1 (by rfl) ⟨788315, by rfl⟩ : syracuseStep 1051087 = 1576631) B1576631
theorem B7277221 : Blo 1048611 7277221 := bstep (se 4 (by rfl) ⟨682239, by rfl⟩ : syracuseStep 7277221 = 1364479) B1364479
theorem B1575659 : Blo 1048611 1575659 := bstep (se 1 (by rfl) ⟨1181744, by rfl⟩ : syracuseStep 1575659 = 2363489) B2363489
theorem B1051455 : Blo 1048611 1051455 := bstep (se 1 (by rfl) ⟨788591, by rfl⟩ : syracuseStep 1051455 = 1577183) B1577183
theorem B5049191 : Blo 1048611 5049191 := bstep (se 1 (by rfl) ⟨3786893, by rfl⟩ : syracuseStep 5049191 = 7573787) B7573787
theorem B4787207 : Blo 1048611 4787207 := bstep (se 1 (by rfl) ⟨3590405, by rfl⟩ : syracuseStep 4787207 = 7180811) B7180811
theorem B1051775 : Blo 1048611 1051775 := bstep (se 1 (by rfl) ⟨788831, by rfl⟩ : syracuseStep 1051775 = 1577663) B1577663
theorem B1051855 : Blo 1048611 1051855 := bstep (se 1 (by rfl) ⟨788891, by rfl⟩ : syracuseStep 1051855 = 1577783) B1577783
theorem B1772779 : Blo 1048611 1772779 := bstep (se 1 (by rfl) ⟨1329584, by rfl⟩ : syracuseStep 1772779 = 2659169) B2659169
theorem B3542291 : Blo 1048611 3542291 := bstep (se 1 (by rfl) ⟨2656718, by rfl⟩ : syracuseStep 3542291 = 5313437) B5313437
theorem B3542345 : Blo 1048611 3542345 := bstep (se 2 (by rfl) ⟨1328379, by rfl⟩ : syracuseStep 3542345 = 2656759) B2656759
theorem B1183387 : Blo 1048611 1183387 := bstep (se 1 (by rfl) ⟨887540, by rfl⟩ : syracuseStep 1183387 = 1775081) B1775081
theorem B1052447 : Blo 1048611 1052447 := bstep (se 1 (by rfl) ⟨789335, by rfl⟩ : syracuseStep 1052447 = 1578671) B1578671
theorem B2363273 : Blo 1048611 2363273 := bstep (se 2 (by rfl) ⟨886227, by rfl⟩ : syracuseStep 2363273 = 1772455) B1772455
theorem B1577087 : Blo 1048611 1577087 := bstep (se 1 (by rfl) ⟨1182815, by rfl⟩ : syracuseStep 1577087 = 2365631) B2365631
theorem B1577129 : Blo 1048611 1577129 := bstep (se 2 (by rfl) ⟨591423, by rfl⟩ : syracuseStep 1577129 = 1182847) B1182847
theorem B1577243 : Blo 1048611 1577243 := bstep (se 1 (by rfl) ⟨1182932, by rfl⟩ : syracuseStep 1577243 = 2365865) B2365865
theorem B1577513 : Blo 1048611 1577513 := bstep (se 2 (by rfl) ⟨591567, by rfl⟩ : syracuseStep 1577513 = 1183135) B1183135
theorem B3543911 : Blo 1048611 3543911 := bstep (se 1 (by rfl) ⟨2657933, by rfl⟩ : syracuseStep 3543911 = 5315867) B5315867
theorem B3544019 : Blo 1048611 3544019 := bstep (se 1 (by rfl) ⟨2658014, by rfl⟩ : syracuseStep 3544019 = 5316029) B5316029
theorem B1577951 : Blo 1048611 1577951 := bstep (se 1 (by rfl) ⟨1183463, by rfl⟩ : syracuseStep 1577951 = 2366927) B2366927
theorem B6722747 : Blo 1048611 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B1578491 : Blo 1048611 1578491 := bstep (se 1 (by rfl) ⟨1183868, by rfl⟩ : syracuseStep 1578491 = 2367737) B2367737
theorem B1775135 : Blo 1048611 1775135 := bstep (se 1 (by rfl) ⟨1331351, by rfl⟩ : syracuseStep 1775135 = 2662703) B2662703
theorem B3544667 : Blo 1048611 3544667 := bstep (se 1 (by rfl) ⟨2658500, by rfl⟩ : syracuseStep 3544667 = 5317001) B5317001
theorem B1578599 : Blo 1048611 1578599 := bstep (se 1 (by rfl) ⟨1183949, by rfl⟩ : syracuseStep 1578599 = 2367899) B2367899
theorem B1775209 : Blo 1048611 1775209 := bstep (se 2 (by rfl) ⟨665703, by rfl⟩ : syracuseStep 1775209 = 1331407) B1331407
theorem B1578791 : Blo 1048611 1578791 := bstep (se 1 (by rfl) ⟨1184093, by rfl⟩ : syracuseStep 1578791 = 2368187) B2368187
theorem B1578863 : Blo 1048611 1578863 := bstep (se 1 (by rfl) ⟨1184147, by rfl⟩ : syracuseStep 1578863 = 2368295) B2368295
theorem B7969913 : Blo 1048611 7969913 := bstep (se 2 (by rfl) ⟨2988717, by rfl⟩ : syracuseStep 7969913 = 5977435) B5977435
theorem B4267475 : Blo 1048611 4267475 := bstep (se 1 (by rfl) ⟨3200606, by rfl⟩ : syracuseStep 4267475 = 6401213) B6401213
theorem B5972879 : Blo 1048611 5972879 := bstep (se 1 (by rfl) ⟨4479659, by rfl⟩ : syracuseStep 5972879 = 8959319) B8959319
theorem B13837391 : Blo 1048611 13837391 := bstep (se 1 (by rfl) ⟨10378043, by rfl⟩ : syracuseStep 13837391 = 20756087) B20756087
theorem B4039931 : Blo 1048611 4039931 := bstep (se 1 (by rfl) ⟨3029948, by rfl⟩ : syracuseStep 4039931 = 6059897) B6059897
theorem B39429575 : Blo 1048611 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B5318297 : Blo 1048611 5318297 := bstep (se 2 (by rfl) ⟨1994361, by rfl⟩ : syracuseStep 5318297 = 3988723) B3988723
theorem B6727333 : Blo 1048611 6727333 := bstep (se 4 (by rfl) ⟨630687, by rfl⟩ : syracuseStep 6727333 = 1261375) B1261375
theorem B3549095 : Blo 1048611 3549095 := bstep (se 1 (by rfl) ⟨2661821, by rfl⟩ : syracuseStep 3549095 = 5323643) B5323643
theorem B7973315 : Blo 1048611 7973315 := bstep (se 1 (by rfl) ⟨5979986, by rfl⟩ : syracuseStep 7973315 = 11959973) B11959973
theorem B5680687 : Blo 1048611 5680687 := bstep (se 1 (by rfl) ⟨4260515, by rfl⟩ : syracuseStep 5680687 = 8521031) B8521031
theorem B25571447 : Blo 1048611 25571447 := bstep (se 1 (by rfl) ⟨19178585, by rfl⟩ : syracuseStep 25571447 = 38357171) B38357171
theorem B13448105 : Blo 1048611 13448105 := bstep (se 2 (by rfl) ⟨5043039, by rfl⟩ : syracuseStep 13448105 = 10086079) B10086079
theorem B2995177 : Blo 1048611 2995177 := bstep (se 2 (by rfl) ⟨1123191, by rfl⟩ : syracuseStep 2995177 = 2246383) B2246383
theorem B21869999 : Blo 1048611 21869999 := bstep (se 1 (by rfl) ⟨16402499, by rfl⟩ : syracuseStep 21869999 = 32804999) B32804999
theorem B4798079 : Blo 1048611 4798079 := bstep (se 1 (by rfl) ⟨3598559, by rfl⟩ : syracuseStep 4798079 = 7197119) B7197119
theorem B7977203 : Blo 1048611 7977203 := bstep (se 1 (by rfl) ⟨5982902, by rfl⟩ : syracuseStep 7977203 = 11965805) B11965805
theorem B5979419 : Blo 1048611 5979419 := bstep (se 1 (by rfl) ⟨4484564, by rfl⟩ : syracuseStep 5979419 = 8969129) B8969129
theorem B2243999 : Blo 1048611 2243999 := bstep (se 1 (by rfl) ⟨1682999, by rfl⟩ : syracuseStep 2243999 = 3365999) B3365999
theorem B25935527 : Blo 1048611 25935527 := bstep (se 1 (by rfl) ⟨19451645, by rfl⟩ : syracuseStep 25935527 = 38903291) B38903291
theorem B3589417 : Blo 1048611 3589417 := bstep (se 2 (by rfl) ⟨1346031, by rfl⟩ : syracuseStep 3589417 = 2692063) B2692063
theorem B4048841 : Blo 1048611 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B13486499 : Blo 1048611 13486499 := bstep (se 1 (by rfl) ⟨10114874, by rfl⟩ : syracuseStep 13486499 = 20229749) B20229749
theorem B3197599 : Blo 1048611 3197599 := bstep (se 1 (by rfl) ⟨2398199, by rfl⟩ : syracuseStep 3197599 = 4796399) B4796399
theorem B3984335 : Blo 1048611 3984335 := bstep (se 1 (by rfl) ⟨2988251, by rfl⟩ : syracuseStep 3984335 = 5976503) B5976503
theorem B3985321 : Blo 1048611 3985321 := bstep (se 2 (by rfl) ⟨1494495, by rfl⟩ : syracuseStep 3985321 = 2988991) B2988991
theorem B6377687 : Blo 1048611 6377687 := bstep (se 1 (by rfl) ⟨4783265, by rfl⟩ : syracuseStep 6377687 = 9566531) B9566531
theorem B3789055 : Blo 1048611 3789055 := bstep (se 1 (by rfl) ⟨2841791, by rfl⟩ : syracuseStep 3789055 = 5683583) B5683583
theorem B9097903 : Blo 1048611 9097903 := bstep (se 1 (by rfl) ⟨6823427, by rfl⟩ : syracuseStep 9097903 = 13646855) B13646855
theorem B1331903 : Blo 1048611 1331903 := bstep (se 1 (by rfl) ⟨998927, by rfl⟩ : syracuseStep 1331903 = 1997855) B1997855
theorem B3595055 : Blo 1048611 3595055 := bstep (se 1 (by rfl) ⟨2696291, by rfl⟩ : syracuseStep 3595055 = 5392583) B5392583
theorem B4480379 : Blo 1048611 4480379 := bstep (se 1 (by rfl) ⟨3360284, by rfl⟩ : syracuseStep 4480379 = 6720569) B6720569
theorem B65559935 : Blo 1048611 65559935 := bstep (se 1 (by rfl) ⟨49169951, by rfl⟩ : syracuseStep 65559935 = 98339903) B98339903
theorem B6053869 : Blo 1048611 6053869 := bstep (se 3 (by rfl) ⟨1135100, by rfl⟩ : syracuseStep 6053869 = 2270201) B2270201
theorem B6381821 : Blo 1048611 6381821 := bstep (se 3 (by rfl) ⟨1196591, by rfl⟩ : syracuseStep 6381821 = 2393183) B2393183
theorem B11493937 : Blo 1048611 11493937 := bstep (se 2 (by rfl) ⟨4310226, by rfl⟩ : syracuseStep 11493937 = 8620453) B8620453
theorem B17031809 : Blo 1048611 17031809 := bstep (se 2 (by rfl) ⟨6386928, by rfl⟩ : syracuseStep 17031809 = 12773857) B12773857
theorem B3990667 : Blo 1048611 3990667 := bstep (se 1 (by rfl) ⟨2993000, by rfl⟩ : syracuseStep 3990667 = 5986001) B5986001
theorem B3990941 : Blo 1048611 3990941 := bstep (se 3 (by rfl) ⟨748301, by rfl⟩ : syracuseStep 3990941 = 1496603) B1496603
theorem B13461227 : Blo 1048611 13461227 := bstep (se 1 (by rfl) ⟨10095920, by rfl⟩ : syracuseStep 13461227 = 20191841) B20191841
theorem B11954141 : Blo 1048611 11954141 := bstep (se 3 (by rfl) ⟨2241401, by rfl⟩ : syracuseStep 11954141 = 4482803) B4482803
theorem B7989353 : Blo 1048611 7989353 := bstep (se 2 (by rfl) ⟨2996007, by rfl⟩ : syracuseStep 7989353 = 5992015) B5992015
theorem B5401081 : Blo 1048611 5401081 := bstep (se 2 (by rfl) ⟨2025405, by rfl⟩ : syracuseStep 5401081 = 4050811) B4050811
theorem B1993481 : Blo 1048611 1993481 := bstep (se 2 (by rfl) ⟨747555, by rfl⟩ : syracuseStep 1993481 = 1495111) B1495111
theorem B5041001 : Blo 1048611 5041001 := bstep (se 2 (by rfl) ⟨1890375, by rfl⟩ : syracuseStep 5041001 = 3780751) B3780751
theorem B8973503 : Blo 1048611 8973503 := bstep (se 1 (by rfl) ⟨6730127, by rfl⟩ : syracuseStep 8973503 = 13460255) B13460255
theorem B34598339 : Blo 1048611 34598339 := bstep (se 1 (by rfl) ⟨25948754, by rfl⟩ : syracuseStep 34598339 = 51897509) B51897509
theorem B5992289 : Blo 1048611 5992289 := bstep (se 2 (by rfl) ⟨2247108, by rfl⟩ : syracuseStep 5992289 = 4494217) B4494217
theorem B3993583 : Blo 1048611 3993583 := bstep (se 1 (by rfl) ⟨2995187, by rfl⟩ : syracuseStep 3993583 = 5990375) B5990375
theorem B98464207 : Blo 1048611 98464207 := bstep (se 1 (by rfl) ⟨73848155, by rfl⟩ : syracuseStep 98464207 = 147696311) B147696311
theorem B3995513 : Blo 1048611 3995513 := bstep (se 2 (by rfl) ⟨1498317, by rfl⟩ : syracuseStep 3995513 = 2996635) B2996635
theorem B7567499 : Blo 1048611 7567499 := bstep (se 1 (by rfl) ⟨5675624, by rfl⟩ : syracuseStep 7567499 = 11351249) B11351249
theorem B8976815 : Blo 1048611 8976815 := bstep (se 1 (by rfl) ⟨6732611, by rfl⟩ : syracuseStep 8976815 = 13465223) B13465223
theorem B1997551 : Blo 1048611 1997551 := bstep (se 1 (by rfl) ⟨1498163, by rfl⟩ : syracuseStep 1997551 = 2996327) B2996327
theorem B4848745 : Blo 1048611 4848745 := bstep (se 2 (by rfl) ⟨1818279, by rfl⟩ : syracuseStep 4848745 = 3636559) B3636559
theorem B149453981 : Blo 1048611 149453981 := bstep (se 3 (by rfl) ⟨28022621, by rfl⟩ : syracuseStep 149453981 = 56045243) B56045243
theorem B38403881 : Blo 1048611 38403881 := bstep (se 2 (by rfl) ⟨14401455, by rfl⟩ : syracuseStep 38403881 = 28802911) B28802911
theorem B7176185 : Blo 1048611 7176185 := bstep (se 2 (by rfl) ⟨2691069, by rfl⟩ : syracuseStep 7176185 = 5382139) B5382139
theorem B1769627 : Blo 1048611 1769627 := bstep (se 1 (by rfl) ⟨1327220, by rfl⟩ : syracuseStep 1769627 = 2654441) B2654441
theorem B1573019 : Blo 1048611 1573019 := bstep (se 1 (by rfl) ⟨1179764, by rfl⟩ : syracuseStep 1573019 = 2359529) B2359529
theorem B1573097 : Blo 1048611 1573097 := bstep (se 2 (by rfl) ⟨589911, by rfl⟩ : syracuseStep 1573097 = 1179823) B1179823
theorem B1048859 : Blo 1048611 1048859 := bstep (se 1 (by rfl) ⟨786644, by rfl⟩ : syracuseStep 1048859 = 1573289) B1573289
theorem B2359799 : Blo 1048611 2359799 := bstep (se 1 (by rfl) ⟨1769849, by rfl⟩ : syracuseStep 2359799 = 3539699) B3539699
theorem B1049627 : Blo 1048611 1049627 := bstep (se 1 (by rfl) ⟨787220, by rfl⟩ : syracuseStep 1049627 = 1574441) B1574441
theorem B1049919 : Blo 1048611 1049919 := bstep (se 1 (by rfl) ⟨787439, by rfl⟩ : syracuseStep 1049919 = 1574879) B1574879
theorem B2360807 : Blo 1048611 2360807 := bstep (se 1 (by rfl) ⟨1770605, by rfl⟩ : syracuseStep 2360807 = 3541211) B3541211
theorem B5310035 : Blo 1048611 5310035 := bstep (se 1 (by rfl) ⟨3982526, by rfl⟩ : syracuseStep 5310035 = 7965053) B7965053
theorem B1050215 : Blo 1048611 1050215 := bstep (se 1 (by rfl) ⟨787661, by rfl⟩ : syracuseStep 1050215 = 1575323) B1575323
theorem B1050239 : Blo 1048611 1050239 := bstep (se 1 (by rfl) ⟨787679, by rfl⟩ : syracuseStep 1050239 = 1575359) B1575359
theorem B4785889 : Blo 1048611 4785889 := bstep (se 2 (by rfl) ⟨1794708, by rfl⟩ : syracuseStep 4785889 = 3589417) B3589417
theorem B1050439 : Blo 1048611 1050439 := bstep (se 1 (by rfl) ⟨787829, by rfl⟩ : syracuseStep 1050439 = 1575659) B1575659
theorem B2656223 : Blo 1048611 2656223 := bstep (se 1 (by rfl) ⟨1992167, by rfl⟩ : syracuseStep 2656223 = 3984335) B3984335
theorem B2361527 : Blo 1048611 2361527 := bstep (se 1 (by rfl) ⟨1771145, by rfl⟩ : syracuseStep 2361527 = 3542291) B3542291
theorem B2361563 : Blo 1048611 2361563 := bstep (se 1 (by rfl) ⟨1771172, by rfl⟩ : syracuseStep 2361563 = 3542345) B3542345
theorem B3541481 : Blo 1048611 3541481 := bstep (se 2 (by rfl) ⟨1328055, by rfl⟩ : syracuseStep 3541481 = 2656111) B2656111
theorem B1575515 : Blo 1048611 1575515 := bstep (se 1 (by rfl) ⟨1181636, by rfl⟩ : syracuseStep 1575515 = 2363273) B2363273
theorem B1051391 : Blo 1048611 1051391 := bstep (se 1 (by rfl) ⟨788543, by rfl⟩ : syracuseStep 1051391 = 1577087) B1577087
theorem B1051419 : Blo 1048611 1051419 := bstep (se 1 (by rfl) ⟨788564, by rfl⟩ : syracuseStep 1051419 = 1577129) B1577129
theorem B1051495 : Blo 1048611 1051495 := bstep (se 1 (by rfl) ⟨788621, by rfl⟩ : syracuseStep 1051495 = 1577243) B1577243
theorem B1051675 : Blo 1048611 1051675 := bstep (se 1 (by rfl) ⟨788756, by rfl⟩ : syracuseStep 1051675 = 1577513) B1577513
theorem B2362607 : Blo 1048611 2362607 := bstep (se 1 (by rfl) ⟨1771955, by rfl⟩ : syracuseStep 2362607 = 3543911) B3543911
theorem B14355701 : Blo 1048611 14355701 := bstep (se 5 (by rfl) ⟨672923, by rfl⟩ : syracuseStep 14355701 = 1345847) B1345847
theorem B2362679 : Blo 1048611 2362679 := bstep (se 1 (by rfl) ⟨1772009, by rfl⟩ : syracuseStep 2362679 = 3544019) B3544019
theorem B1051967 : Blo 1048611 1051967 := bstep (se 1 (by rfl) ⟨788975, by rfl⟩ : syracuseStep 1051967 = 1577951) B1577951
theorem B1052327 : Blo 1048611 1052327 := bstep (se 1 (by rfl) ⟨789245, by rfl⟩ : syracuseStep 1052327 = 1578491) B1578491
theorem B1183423 : Blo 1048611 1183423 := bstep (se 1 (by rfl) ⟨887567, by rfl⟩ : syracuseStep 1183423 = 1775135) B1775135
theorem B2363111 : Blo 1048611 2363111 := bstep (se 1 (by rfl) ⟨1772333, by rfl⟩ : syracuseStep 2363111 = 3544667) B3544667
theorem B1052399 : Blo 1048611 1052399 := bstep (se 1 (by rfl) ⟨789299, by rfl⟩ : syracuseStep 1052399 = 1578599) B1578599
theorem B1052527 : Blo 1048611 1052527 := bstep (se 1 (by rfl) ⟨789395, by rfl⟩ : syracuseStep 1052527 = 1578791) B1578791
theorem B1052575 : Blo 1048611 1052575 := bstep (se 1 (by rfl) ⟨789431, by rfl⟩ : syracuseStep 1052575 = 1578863) B1578863
theorem B2363705 : Blo 1048611 2363705 := bstep (se 2 (by rfl) ⟨886389, by rfl⟩ : syracuseStep 2363705 = 1772779) B1772779
theorem B7574249 : Blo 1048611 7574249 := bstep (se 2 (by rfl) ⟨2840343, by rfl⟩ : syracuseStep 7574249 = 5680687) B5680687
theorem B5313275 : Blo 1048611 5313275 := bstep (se 1 (by rfl) ⟨3984956, by rfl⟩ : syracuseStep 5313275 = 7969913) B7969913
theorem B1577849 : Blo 1048611 1577849 := bstep (se 2 (by rfl) ⟨591693, by rfl⟩ : syracuseStep 1577849 = 1183387) B1183387
theorem B2986919 : Blo 1048611 2986919 := bstep (se 1 (by rfl) ⟨2240189, by rfl⟩ : syracuseStep 2986919 = 4480379) B4480379
theorem B5313761 : Blo 1048611 5313761 := bstep (se 2 (by rfl) ⟨1992660, by rfl⟩ : syracuseStep 5313761 = 3985321) B3985321
theorem B5052073 : Blo 1048611 5052073 := bstep (se 2 (by rfl) ⟨1894527, by rfl⟩ : syracuseStep 5052073 = 3789055) B3789055
theorem B2693287 : Blo 1048611 2693287 := bstep (se 1 (by rfl) ⟨2019965, by rfl⟩ : syracuseStep 2693287 = 4039931) B4039931
theorem B2660627 : Blo 1048611 2660627 := bstep (se 1 (by rfl) ⟨1995470, by rfl⟩ : syracuseStep 2660627 = 3990941) B3990941
theorem B26286383 : Blo 1048611 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B3545531 : Blo 1048611 3545531 := bstep (se 1 (by rfl) ⟨2659148, by rfl⟩ : syracuseStep 3545531 = 5318297) B5318297
theorem B2366063 : Blo 1048611 2366063 := bstep (se 1 (by rfl) ⟨1774547, by rfl⟩ : syracuseStep 2366063 = 3549095) B3549095
theorem B7969427 : Blo 1048611 7969427 := bstep (se 1 (by rfl) ⟨5977070, by rfl⟩ : syracuseStep 7969427 = 11954141) B11954141
theorem B5315543 : Blo 1048611 5315543 := bstep (se 1 (by rfl) ⟨3986657, by rfl⟩ : syracuseStep 5315543 = 7973315) B7973315
theorem B2366945 : Blo 1048611 2366945 := bstep (se 2 (by rfl) ⟨887604, by rfl⟩ : syracuseStep 2366945 = 1775209) B1775209
theorem B13442669 : Blo 1048611 13442669 := bstep (se 3 (by rfl) ⟨2520500, by rfl⟩ : syracuseStep 13442669 = 5041001) B5041001
theorem B17047631 : Blo 1048611 17047631 := bstep (se 1 (by rfl) ⟨12785723, by rfl⟩ : syracuseStep 17047631 = 25571447) B25571447
theorem B38347253 : Blo 1048611 38347253 := bstep (se 5 (by rfl) ⟨1797527, by rfl⟩ : syracuseStep 38347253 = 3595055) B3595055
theorem B2663401 : Blo 1048611 2663401 := bstep (se 2 (by rfl) ⟨998775, by rfl⟩ : syracuseStep 2663401 = 1997551) B1997551
theorem B2663675 : Blo 1048611 2663675 := bstep (se 1 (by rfl) ⟨1997756, by rfl⟩ : syracuseStep 2663675 = 3995513) B3995513
theorem B6464993 : Blo 1048611 6464993 := bstep (se 2 (by rfl) ⟨2424372, by rfl⟩ : syracuseStep 6464993 = 4848745) B4848745
theorem B5318135 : Blo 1048611 5318135 := bstep (se 1 (by rfl) ⟨3988601, by rfl⟩ : syracuseStep 5318135 = 7977203) B7977203
theorem B25602587 : Blo 1048611 25602587 := bstep (se 1 (by rfl) ⟨19201940, by rfl⟩ : syracuseStep 25602587 = 38403881) B38403881
theorem B8071825 : Blo 1048611 8071825 := bstep (se 2 (by rfl) ⟨3026934, by rfl⟩ : syracuseStep 8071825 = 6053869) B6053869
theorem B3779311 : Blo 1048611 3779311 := bstep (se 1 (by rfl) ⟨2834483, by rfl⟩ : syracuseStep 3779311 = 5668967) B5668967
theorem B2993183 : Blo 1048611 2993183 := bstep (se 1 (by rfl) ⟨2244887, by rfl⟩ : syracuseStep 2993183 = 4489775) B4489775
theorem B2993719 : Blo 1048611 2993719 := bstep (se 1 (by rfl) ⟨2245289, by rfl⟩ : syracuseStep 2993719 = 4490579) B4490579
theorem B2699227 : Blo 1048611 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B5320889 : Blo 1048611 5320889 := bstep (se 2 (by rfl) ⟨1995333, by rfl⟩ : syracuseStep 5320889 = 3990667) B3990667
theorem B8990999 : Blo 1048611 8990999 := bstep (se 1 (by rfl) ⟨6743249, by rfl⟩ : syracuseStep 8990999 = 13486499) B13486499
theorem B3551741 : Blo 1048611 3551741 := bstep (se 3 (by rfl) ⟨665951, by rfl⟩ : syracuseStep 3551741 = 1331903) B1331903
theorem B3191471 : Blo 1048611 3191471 := bstep (se 1 (by rfl) ⟨2393603, by rfl⟩ : syracuseStep 3191471 = 4787207) B4787207
theorem B17053861 : Blo 1048611 17053861 := bstep (se 4 (by rfl) ⟨1598799, by rfl⟩ : syracuseStep 17053861 = 3197599) B3197599
theorem B38811845 : Blo 1048611 38811845 := bstep (se 4 (by rfl) ⟨3638610, by rfl⟩ : syracuseStep 38811845 = 7277221) B7277221
theorem B5324777 : Blo 1048611 5324777 := bstep (se 2 (by rfl) ⟨1996791, by rfl⟩ : syracuseStep 5324777 = 3993583) B3993583
theorem B11354539 : Blo 1048611 11354539 := bstep (se 1 (by rfl) ⟨8515904, by rfl⟩ : syracuseStep 11354539 = 17031809) B17031809
theorem B3981919 : Blo 1048611 3981919 := bstep (se 1 (by rfl) ⟨2986439, by rfl⟩ : syracuseStep 3981919 = 5972879) B5972879
theorem B131285609 : Blo 1048611 131285609 := bstep (se 2 (by rfl) ⟨49232103, by rfl⟩ : syracuseStep 131285609 = 98464207) B98464207
theorem B9224927 : Blo 1048611 9224927 := bstep (se 1 (by rfl) ⟨6918695, by rfl⟩ : syracuseStep 9224927 = 13837391) B13837391
theorem B5326235 : Blo 1048611 5326235 := bstep (se 1 (by rfl) ⟨3994676, by rfl⟩ : syracuseStep 5326235 = 7989353) B7989353
theorem B1328987 : Blo 1048611 1328987 := bstep (se 1 (by rfl) ⟨996740, by rfl⟩ : syracuseStep 1328987 = 1993481) B1993481
theorem B5982335 : Blo 1048611 5982335 := bstep (se 1 (by rfl) ⟨4486751, by rfl⟩ : syracuseStep 5982335 = 8973503) B8973503
theorem B8965403 : Blo 1048611 8965403 := bstep (se 1 (by rfl) ⟨6724052, by rfl⟩ : syracuseStep 8965403 = 13448105) B13448105
theorem B3198719 : Blo 1048611 3198719 := bstep (se 1 (by rfl) ⟨2399039, by rfl⟩ : syracuseStep 3198719 = 4798079) B4798079
theorem B5984543 : Blo 1048611 5984543 := bstep (se 1 (by rfl) ⟨4488407, by rfl⟩ : syracuseStep 5984543 = 8976815) B8976815
theorem B99635987 : Blo 1048611 99635987 := bstep (se 1 (by rfl) ⟨74726990, by rfl⟩ : syracuseStep 99635987 = 149453981) B149453981
theorem B3986279 : Blo 1048611 3986279 := bstep (se 1 (by rfl) ⟨2989709, by rfl⟩ : syracuseStep 3986279 = 5979419) B5979419
theorem B1495999 : Blo 1048611 1495999 := bstep (se 1 (by rfl) ⟨1121999, by rfl⟩ : syracuseStep 1495999 = 2243999) B2243999
theorem B17290351 : Blo 1048611 17290351 := bstep (se 1 (by rfl) ⟨12967763, by rfl⟩ : syracuseStep 17290351 = 25935527) B25935527
theorem B15325249 : Blo 1048611 15325249 := bstep (se 2 (by rfl) ⟨5746968, by rfl⟩ : syracuseStep 15325249 = 11493937) B11493937
theorem B3366127 : Blo 1048611 3366127 := bstep (se 1 (by rfl) ⟨2524595, by rfl⟩ : syracuseStep 3366127 = 5049191) B5049191
theorem B8969777 : Blo 1048611 8969777 := bstep (se 2 (by rfl) ⟨3363666, by rfl⟩ : syracuseStep 8969777 = 6727333) B6727333
theorem B4251791 : Blo 1048611 4251791 := bstep (se 1 (by rfl) ⟨3188843, by rfl⟩ : syracuseStep 4251791 = 6377687) B6377687
theorem B7201441 : Blo 1048611 7201441 := bstep (se 2 (by rfl) ⟨2700540, by rfl⟩ : syracuseStep 7201441 = 5401081) B5401081
theorem B4481831 : Blo 1048611 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B48522149 : Blo 1048611 48522149 := bstep (se 4 (by rfl) ⟨4548951, by rfl⟩ : syracuseStep 48522149 = 9097903) B9097903
theorem B43706623 : Blo 1048611 43706623 := bstep (se 1 (by rfl) ⟨32779967, by rfl⟩ : syracuseStep 43706623 = 65559935) B65559935
theorem B2844983 : Blo 1048611 2844983 := bstep (se 1 (by rfl) ⟨2133737, by rfl⟩ : syracuseStep 2844983 = 4267475) B4267475
theorem B4254547 : Blo 1048611 4254547 := bstep (se 1 (by rfl) ⟨3190910, by rfl⟩ : syracuseStep 4254547 = 6381821) B6381821
theorem B8974151 : Blo 1048611 8974151 := bstep (se 1 (by rfl) ⟨6730613, by rfl⟩ : syracuseStep 8974151 = 13461227) B13461227
theorem B3993569 : Blo 1048611 3993569 := bstep (se 2 (by rfl) ⟨1497588, by rfl⟩ : syracuseStep 3993569 = 2995177) B2995177
theorem B23065559 : Blo 1048611 23065559 := bstep (se 1 (by rfl) ⟨17299169, by rfl⟩ : syracuseStep 23065559 = 34598339) B34598339
theorem B3994859 : Blo 1048611 3994859 := bstep (se 1 (by rfl) ⟨2996144, by rfl⟩ : syracuseStep 3994859 = 5992289) B5992289
theorem B14579999 : Blo 1048611 14579999 := bstep (se 1 (by rfl) ⟨10934999, by rfl⟩ : syracuseStep 14579999 = 21869999) B21869999
theorem B5044999 : Blo 1048611 5044999 := bstep (se 1 (by rfl) ⟨3783749, by rfl⟩ : syracuseStep 5044999 = 7567499) B7567499
theorem B4784123 : Blo 1048611 4784123 := bstep (se 1 (by rfl) ⟨3588092, by rfl⟩ : syracuseStep 4784123 = 7176185) B7176185
theorem B1179751 : Blo 1048611 1179751 := bstep (se 1 (by rfl) ⟨884813, by rfl⟩ : syracuseStep 1179751 = 1769627) B1769627
theorem B1048679 : Blo 1048611 1048679 := bstep (se 1 (by rfl) ⟨786509, by rfl⟩ : syracuseStep 1048679 = 1573019) B1573019
theorem B1048731 : Blo 1048611 1048731 := bstep (se 1 (by rfl) ⟨786548, by rfl⟩ : syracuseStep 1048731 = 1573097) B1573097
theorem B1573199 : Blo 1048611 1573199 := bstep (se 1 (by rfl) ⟨1179899, by rfl⟩ : syracuseStep 1573199 = 2359799) B2359799
theorem B87523739 : Blo 1048611 87523739 := bstep (se 1 (by rfl) ⟨65642804, by rfl⟩ : syracuseStep 87523739 = 131285609) B131285609
theorem B15139385 : Blo 1048611 15139385 := bstep (se 2 (by rfl) ⟨5677269, by rfl⟩ : syracuseStep 15139385 = 11354539) B11354539
theorem B5309225 : Blo 1048611 5309225 := bstep (se 2 (by rfl) ⟨1990959, by rfl⟩ : syracuseStep 5309225 = 3981919) B3981919
theorem B9601921 : Blo 1048611 9601921 := bstep (se 2 (by rfl) ⟨3600720, by rfl⟩ : syracuseStep 9601921 = 7201441) B7201441
theorem B1573871 : Blo 1048611 1573871 := bstep (se 1 (by rfl) ⟨1180403, by rfl⟩ : syracuseStep 1573871 = 2360807) B2360807
theorem B3540023 : Blo 1048611 3540023 := bstep (se 1 (by rfl) ⟨2655017, by rfl⟩ : syracuseStep 3540023 = 5310035) B5310035
theorem B1770815 : Blo 1048611 1770815 := bstep (se 1 (by rfl) ⟨1328111, by rfl⟩ : syracuseStep 1770815 = 2656223) B2656223
theorem B1574351 : Blo 1048611 1574351 := bstep (se 1 (by rfl) ⟨1180763, by rfl⟩ : syracuseStep 1574351 = 2361527) B2361527
theorem B1574375 : Blo 1048611 1574375 := bstep (se 1 (by rfl) ⟨1180781, by rfl⟩ : syracuseStep 1574375 = 2361563) B2361563
theorem B2360987 : Blo 1048611 2360987 := bstep (se 1 (by rfl) ⟨1770740, by rfl⟩ : syracuseStep 2360987 = 3541481) B3541481
theorem B1050343 : Blo 1048611 1050343 := bstep (se 1 (by rfl) ⟨787757, by rfl⟩ : syracuseStep 1050343 = 1575515) B1575515
theorem B1575071 : Blo 1048611 1575071 := bstep (se 1 (by rfl) ⟨1181303, by rfl⟩ : syracuseStep 1575071 = 2362607) B2362607
theorem B9570467 : Blo 1048611 9570467 := bstep (se 1 (by rfl) ⟨7177850, by rfl⟩ : syracuseStep 9570467 = 14355701) B14355701
theorem B1575119 : Blo 1048611 1575119 := bstep (se 1 (by rfl) ⟨1181339, by rfl⟩ : syracuseStep 1575119 = 2362679) B2362679
theorem B1575407 : Blo 1048611 1575407 := bstep (se 1 (by rfl) ⟨1181555, by rfl⟩ : syracuseStep 1575407 = 2363111) B2363111
theorem B2132479 : Blo 1048611 2132479 := bstep (se 1 (by rfl) ⟨1599359, by rfl⟩ : syracuseStep 2132479 = 3198719) B3198719
theorem B1575803 : Blo 1048611 1575803 := bstep (se 1 (by rfl) ⟨1181852, by rfl⟩ : syracuseStep 1575803 = 2363705) B2363705
theorem B5049499 : Blo 1048611 5049499 := bstep (se 1 (by rfl) ⟨3787124, by rfl⟩ : syracuseStep 5049499 = 7574249) B7574249
theorem B3542183 : Blo 1048611 3542183 := bstep (se 1 (by rfl) ⟨2656637, by rfl⟩ : syracuseStep 3542183 = 5313275) B5313275
theorem B2657519 : Blo 1048611 2657519 := bstep (se 1 (by rfl) ⟨1993139, by rfl⟩ : syracuseStep 2657519 = 3986279) B3986279
theorem B1051899 : Blo 1048611 1051899 := bstep (se 1 (by rfl) ⟨788924, by rfl⟩ : syracuseStep 1051899 = 1577849) B1577849
theorem B3542507 : Blo 1048611 3542507 := bstep (se 1 (by rfl) ⟨2656880, by rfl⟩ : syracuseStep 3542507 = 5313761) B5313761
theorem B5672729 : Blo 1048611 5672729 := bstep (se 2 (by rfl) ⟨2127273, by rfl⟩ : syracuseStep 5672729 = 4254547) B4254547
theorem B17239981 : Blo 1048611 17239981 := bstep (se 3 (by rfl) ⟨3232496, by rfl⟩ : syracuseStep 17239981 = 6464993) B6464993
theorem B1773751 : Blo 1048611 1773751 := bstep (se 1 (by rfl) ⟨1330313, by rfl⟩ : syracuseStep 1773751 = 2660627) B2660627
theorem B2363687 : Blo 1048611 2363687 := bstep (se 1 (by rfl) ⟨1772765, by rfl⟩ : syracuseStep 2363687 = 3545531) B3545531
theorem B1577375 : Blo 1048611 1577375 := bstep (se 1 (by rfl) ⟨1183031, by rfl⟩ : syracuseStep 1577375 = 2366063) B2366063
theorem B5312951 : Blo 1048611 5312951 := bstep (se 1 (by rfl) ⟨3984713, by rfl⟩ : syracuseStep 5312951 = 7969427) B7969427
theorem B3543695 : Blo 1048611 3543695 := bstep (se 1 (by rfl) ⟨2657771, by rfl⟩ : syracuseStep 3543695 = 5315543) B5315543
theorem B3543965 : Blo 1048611 3543965 := bstep (se 3 (by rfl) ⟨664493, by rfl⟩ : syracuseStep 3543965 = 1328987) B1328987
theorem B1577897 : Blo 1048611 1577897 := bstep (se 2 (by rfl) ⟨591711, by rfl⟩ : syracuseStep 1577897 = 1183423) B1183423
theorem B1577963 : Blo 1048611 1577963 := bstep (se 1 (by rfl) ⟨1183472, by rfl⟩ : syracuseStep 1577963 = 2366945) B2366945
theorem B25564835 : Blo 1048611 25564835 := bstep (se 1 (by rfl) ⟨19173626, by rfl⟩ : syracuseStep 25564835 = 38347253) B38347253
theorem B2987887 : Blo 1048611 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B92215205 : Blo 1048611 92215205 := bstep (se 4 (by rfl) ⟨8645175, by rfl⟩ : syracuseStep 92215205 = 17290351) B17290351
theorem B32348099 : Blo 1048611 32348099 := bstep (se 1 (by rfl) ⟨24261074, by rfl⟩ : syracuseStep 32348099 = 48522149) B48522149
theorem B1775783 : Blo 1048611 1775783 := bstep (se 1 (by rfl) ⟨1331837, by rfl⟩ : syracuseStep 1775783 = 2663675) B2663675
theorem B3545423 : Blo 1048611 3545423 := bstep (se 1 (by rfl) ⟨2659067, by rfl⟩ : syracuseStep 3545423 = 5318135) B5318135
theorem B2662379 : Blo 1048611 2662379 := bstep (se 1 (by rfl) ⟨1996784, by rfl⟩ : syracuseStep 2662379 = 3993569) B3993569
theorem B3547259 : Blo 1048611 3547259 := bstep (se 1 (by rfl) ⟨2660444, by rfl⟩ : syracuseStep 3547259 = 5320889) B5320889
theorem B2367827 : Blo 1048611 2367827 := bstep (se 1 (by rfl) ⟨1775870, by rfl⟩ : syracuseStep 2367827 = 3551741) B3551741
theorem B15377039 : Blo 1048611 15377039 := bstep (se 1 (by rfl) ⟨11532779, by rfl⟩ : syracuseStep 15377039 = 23065559) B23065559
theorem B2663239 : Blo 1048611 2663239 := bstep (se 1 (by rfl) ⟨1997429, by rfl⟩ : syracuseStep 2663239 = 3994859) B3994859
theorem B6726665 : Blo 1048611 6726665 := bstep (se 2 (by rfl) ⟨2522499, by rfl⟩ : syracuseStep 6726665 = 5044999) B5044999
theorem B14395877 : Blo 1048611 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B3549851 : Blo 1048611 3549851 := bstep (se 1 (by rfl) ⟨2662388, by rfl⟩ : syracuseStep 3549851 = 5324777) B5324777
theorem B12757661 : Blo 1048611 12757661 := bstep (se 3 (by rfl) ⟨2392061, by rfl⟩ : syracuseStep 12757661 = 4784123) B4784123
theorem B45460349 : Blo 1048611 45460349 := bstep (se 3 (by rfl) ⟨8523815, by rfl⟩ : syracuseStep 45460349 = 17047631) B17047631
theorem B3550823 : Blo 1048611 3550823 := bstep (se 1 (by rfl) ⟨2663117, by rfl⟩ : syracuseStep 3550823 = 5326235) B5326235
theorem B3551201 : Blo 1048611 3551201 := bstep (se 2 (by rfl) ⟨1331700, by rfl⟩ : syracuseStep 3551201 = 2663401) B2663401
theorem B265695965 : Blo 1048611 265695965 := bstep (se 3 (by rfl) ⟨49817993, by rfl⟩ : syracuseStep 265695965 = 99635987) B99635987
theorem B5976935 : Blo 1048611 5976935 := bstep (se 1 (by rfl) ⟨4482701, by rfl⟩ : syracuseStep 5976935 = 8965403) B8965403
theorem B58275497 : Blo 1048611 58275497 := bstep (se 2 (by rfl) ⟨21853311, by rfl⟩ : syracuseStep 58275497 = 43706623) B43706623
theorem B10762433 : Blo 1048611 10762433 := bstep (se 2 (by rfl) ⟨4035912, by rfl⟩ : syracuseStep 10762433 = 8071825) B8071825
theorem B7978661 : Blo 1048611 7978661 := bstep (se 4 (by rfl) ⟨747999, by rfl⟩ : syracuseStep 7978661 = 1495999) B1495999
theorem B5979851 : Blo 1048611 5979851 := bstep (se 1 (by rfl) ⟨4484888, by rfl⟩ : syracuseStep 5979851 = 8969777) B8969777
theorem B8961779 : Blo 1048611 8961779 := bstep (se 1 (by rfl) ⟨6721334, by rfl⟩ : syracuseStep 8961779 = 13442669) B13442669
theorem B2834527 : Blo 1048611 2834527 := bstep (se 1 (by rfl) ⟨2125895, by rfl⟩ : syracuseStep 2834527 = 4251791) B4251791
theorem B7586621 : Blo 1048611 7586621 := bstep (se 3 (by rfl) ⟨1422491, by rfl⟩ : syracuseStep 7586621 = 2844983) B2844983
theorem B6736097 : Blo 1048611 6736097 := bstep (se 2 (by rfl) ⟨2526036, by rfl⟩ : syracuseStep 6736097 = 5052073) B5052073
theorem B5982767 : Blo 1048611 5982767 := bstep (se 1 (by rfl) ⟨4487075, by rfl⟩ : syracuseStep 5982767 = 8974151) B8974151
theorem B20433665 : Blo 1048611 20433665 := bstep (se 2 (by rfl) ⟨7662624, by rfl⟩ : syracuseStep 20433665 = 15325249) B15325249
theorem B3591049 : Blo 1048611 3591049 := bstep (se 2 (by rfl) ⟨1346643, by rfl⟩ : syracuseStep 3591049 = 2693287) B2693287
theorem B25874563 : Blo 1048611 25874563 := bstep (se 1 (by rfl) ⟨19405922, by rfl⟩ : syracuseStep 25874563 = 38811845) B38811845
theorem B9719999 : Blo 1048611 9719999 := bstep (se 1 (by rfl) ⟨7289999, by rfl⟩ : syracuseStep 9719999 = 14579999) B14579999
theorem B6149951 : Blo 1048611 6149951 := bstep (se 1 (by rfl) ⟨4612463, by rfl⟩ : syracuseStep 6149951 = 9224927) B9224927
theorem B3988223 : Blo 1048611 3988223 := bstep (se 1 (by rfl) ⟨2991167, by rfl⟩ : syracuseStep 3988223 = 5982335) B5982335
theorem B6381185 : Blo 1048611 6381185 := bstep (se 2 (by rfl) ⟨2392944, by rfl⟩ : syracuseStep 6381185 = 4785889) B4785889
theorem B3989695 : Blo 1048611 3989695 := bstep (se 1 (by rfl) ⟨2992271, by rfl⟩ : syracuseStep 3989695 = 5984543) B5984543
theorem B1991279 : Blo 1048611 1991279 := bstep (se 1 (by rfl) ⟨1493459, by rfl⟩ : syracuseStep 1991279 = 2986919) B2986919
theorem B5039081 : Blo 1048611 5039081 := bstep (se 2 (by rfl) ⟨1889655, by rfl⟩ : syracuseStep 5039081 = 3779311) B3779311
theorem B17524255 : Blo 1048611 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B3991625 : Blo 1048611 3991625 := bstep (se 2 (by rfl) ⟨1496859, by rfl⟩ : syracuseStep 3991625 = 2993719) B2993719
theorem B17068391 : Blo 1048611 17068391 := bstep (se 1 (by rfl) ⟨12801293, by rfl⟩ : syracuseStep 17068391 = 25602587) B25602587
theorem B1995455 : Blo 1048611 1995455 := bstep (se 1 (by rfl) ⟨1496591, by rfl⟩ : syracuseStep 1995455 = 2993183) B2993183
theorem B5993999 : Blo 1048611 5993999 := bstep (se 1 (by rfl) ⟨4495499, by rfl⟩ : syracuseStep 5993999 = 8990999) B8990999
theorem B22738481 : Blo 1048611 22738481 := bstep (se 2 (by rfl) ⟨8526930, by rfl⟩ : syracuseStep 22738481 = 17053861) B17053861
theorem B2127647 : Blo 1048611 2127647 := bstep (se 1 (by rfl) ⟨1595735, by rfl⟩ : syracuseStep 2127647 = 3191471) B3191471
theorem B4488169 : Blo 1048611 4488169 := bstep (se 2 (by rfl) ⟨1683063, by rfl⟩ : syracuseStep 4488169 = 3366127) B3366127
theorem B1573001 : Blo 1048611 1573001 := bstep (se 2 (by rfl) ⟨589875, by rfl⟩ : syracuseStep 1573001 = 1179751) B1179751
theorem B1048799 : Blo 1048611 1048799 := bstep (se 1 (by rfl) ⟨786599, by rfl⟩ : syracuseStep 1048799 = 1573199) B1573199
theorem B10092923 : Blo 1048611 10092923 := bstep (se 1 (by rfl) ⟨7569692, by rfl⟩ : syracuseStep 10092923 = 15139385) B15139385
theorem B3539483 : Blo 1048611 3539483 := bstep (se 1 (by rfl) ⟨2654612, by rfl⟩ : syracuseStep 3539483 = 5309225) B5309225
theorem B1049247 : Blo 1048611 1049247 := bstep (se 1 (by rfl) ⟨786935, by rfl⟩ : syracuseStep 1049247 = 1573871) B1573871
theorem B2360015 : Blo 1048611 2360015 := bstep (se 1 (by rfl) ⟨1770011, by rfl⟩ : syracuseStep 2360015 = 3540023) B3540023
theorem B1180543 : Blo 1048611 1180543 := bstep (se 1 (by rfl) ⟨885407, by rfl⟩ : syracuseStep 1180543 = 1770815) B1770815
theorem B1049567 : Blo 1048611 1049567 := bstep (se 1 (by rfl) ⟨787175, by rfl⟩ : syracuseStep 1049567 = 1574351) B1574351
theorem B1049583 : Blo 1048611 1049583 := bstep (se 1 (by rfl) ⟨787187, by rfl⟩ : syracuseStep 1049583 = 1574375) B1574375
theorem B1573991 : Blo 1048611 1573991 := bstep (se 1 (by rfl) ⟨1180493, by rfl⟩ : syracuseStep 1573991 = 2360987) B2360987
theorem B1050047 : Blo 1048611 1050047 := bstep (se 1 (by rfl) ⟨787535, by rfl⟩ : syracuseStep 1050047 = 1575071) B1575071
theorem B1050079 : Blo 1048611 1050079 := bstep (se 1 (by rfl) ⟨787559, by rfl⟩ : syracuseStep 1050079 = 1575119) B1575119
theorem B4490731 : Blo 1048611 4490731 := bstep (se 1 (by rfl) ⟨3368048, by rfl⟩ : syracuseStep 4490731 = 6736097) B6736097
theorem B1050271 : Blo 1048611 1050271 := bstep (se 1 (by rfl) ⟨787703, by rfl⟩ : syracuseStep 1050271 = 1575407) B1575407
theorem B1050535 : Blo 1048611 1050535 := bstep (se 1 (by rfl) ⟨787901, by rfl⟩ : syracuseStep 1050535 = 1575803) B1575803
theorem B23365673 : Blo 1048611 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B2361455 : Blo 1048611 2361455 := bstep (se 1 (by rfl) ⟨1771091, by rfl⟩ : syracuseStep 2361455 = 3542183) B3542183
theorem B1771679 : Blo 1048611 1771679 := bstep (se 1 (by rfl) ⟨1328759, by rfl⟩ : syracuseStep 1771679 = 2657519) B2657519
theorem B2361671 : Blo 1048611 2361671 := bstep (se 1 (by rfl) ⟨1771253, by rfl⟩ : syracuseStep 2361671 = 3542507) B3542507
theorem B1575791 : Blo 1048611 1575791 := bstep (se 1 (by rfl) ⟨1181843, by rfl⟩ : syracuseStep 1575791 = 2363687) B2363687
theorem B1051583 : Blo 1048611 1051583 := bstep (se 1 (by rfl) ⟨788687, by rfl⟩ : syracuseStep 1051583 = 1577375) B1577375
theorem B3541967 : Blo 1048611 3541967 := bstep (se 1 (by rfl) ⟨2656475, by rfl⟩ : syracuseStep 3541967 = 5312951) B5312951
theorem B2362463 : Blo 1048611 2362463 := bstep (se 1 (by rfl) ⟨1771847, by rfl⟩ : syracuseStep 2362463 = 3543695) B3543695
theorem B2362643 : Blo 1048611 2362643 := bstep (se 1 (by rfl) ⟨1771982, by rfl⟩ : syracuseStep 2362643 = 3543965) B3543965
theorem B1051931 : Blo 1048611 1051931 := bstep (se 1 (by rfl) ⟨788948, by rfl⟩ : syracuseStep 1051931 = 1577897) B1577897
theorem B1051975 : Blo 1048611 1051975 := bstep (se 1 (by rfl) ⟨788981, by rfl⟩ : syracuseStep 1051975 = 1577963) B1577963
theorem B17043223 : Blo 1048611 17043223 := bstep (se 1 (by rfl) ⟨12782417, by rfl⟩ : syracuseStep 17043223 = 25564835) B25564835
theorem B4788065 : Blo 1048611 4788065 := bstep (se 2 (by rfl) ⟨1795524, by rfl⟩ : syracuseStep 4788065 = 3591049) B3591049
theorem B4099967 : Blo 1048611 4099967 := bstep (se 1 (by rfl) ⟨3074975, by rfl⟩ : syracuseStep 4099967 = 6149951) B6149951
theorem B61476803 : Blo 1048611 61476803 := bstep (se 1 (by rfl) ⟨46107602, by rfl⟩ : syracuseStep 61476803 = 92215205) B92215205
theorem B1183855 : Blo 1048611 1183855 := bstep (se 1 (by rfl) ⟨887891, by rfl⟩ : syracuseStep 1183855 = 1775783) B1775783
theorem B2363615 : Blo 1048611 2363615 := bstep (se 1 (by rfl) ⟨1772711, by rfl⟩ : syracuseStep 2363615 = 3545423) B3545423
theorem B2658815 : Blo 1048611 2658815 := bstep (se 1 (by rfl) ⟨1994111, by rfl⟩ : syracuseStep 2658815 = 3988223) B3988223
theorem B5673725 : Blo 1048611 5673725 := bstep (se 3 (by rfl) ⟨1063823, by rfl⟩ : syracuseStep 5673725 = 2127647) B2127647
theorem B1774919 : Blo 1048611 1774919 := bstep (se 1 (by rfl) ⟨1331189, by rfl⟩ : syracuseStep 1774919 = 2662379) B2662379
theorem B2364839 : Blo 1048611 2364839 := bstep (se 1 (by rfl) ⟨1773629, by rfl⟩ : syracuseStep 2364839 = 3547259) B3547259
theorem B1578551 : Blo 1048611 1578551 := bstep (se 1 (by rfl) ⟨1183913, by rfl⟩ : syracuseStep 1578551 = 2367827) B2367827
theorem B2365001 : Blo 1048611 2365001 := bstep (se 2 (by rfl) ⟨886875, by rfl⟩ : syracuseStep 2365001 = 1773751) B1773751
theorem B2661083 : Blo 1048611 2661083 := bstep (se 1 (by rfl) ⟨1995812, by rfl⟩ : syracuseStep 2661083 = 3991625) B3991625
theorem B2366567 : Blo 1048611 2366567 := bstep (se 1 (by rfl) ⟨1774925, by rfl⟩ : syracuseStep 2366567 = 3549851) B3549851
theorem B2367215 : Blo 1048611 2367215 := bstep (se 1 (by rfl) ⟨1775411, by rfl⟩ : syracuseStep 2367215 = 3550823) B3550823
theorem B2367467 : Blo 1048611 2367467 := bstep (se 1 (by rfl) ⟨1775600, by rfl⟩ : syracuseStep 2367467 = 3551201) B3551201
theorem B11378927 : Blo 1048611 11378927 := bstep (se 1 (by rfl) ⟨8534195, by rfl⟩ : syracuseStep 11378927 = 17068391) B17068391
theorem B17016493 : Blo 1048611 17016493 := bstep (se 3 (by rfl) ⟨3190592, by rfl⟩ : syracuseStep 17016493 = 6381185) B6381185
theorem B5319107 : Blo 1048611 5319107 := bstep (se 1 (by rfl) ⟨3989330, by rfl⟩ : syracuseStep 5319107 = 7978661) B7978661
theorem B5974519 : Blo 1048611 5974519 := bstep (se 1 (by rfl) ⟨4480889, by rfl⟩ : syracuseStep 5974519 = 8961779) B8961779
theorem B3779369 : Blo 1048611 3779369 := bstep (se 2 (by rfl) ⟨1417263, by rfl⟩ : syracuseStep 3779369 = 2834527) B2834527
theorem B5319593 : Blo 1048611 5319593 := bstep (se 2 (by rfl) ⟨1994847, by rfl⟩ : syracuseStep 5319593 = 3989695) B3989695
theorem B5057747 : Blo 1048611 5057747 := bstep (se 1 (by rfl) ⟨3793310, by rfl⟩ : syracuseStep 5057747 = 7586621) B7586621
theorem B3550985 : Blo 1048611 3550985 := bstep (se 2 (by rfl) ⟨1331619, by rfl⟩ : syracuseStep 3550985 = 2663239) B2663239
theorem B5321213 : Blo 1048611 5321213 := bstep (se 3 (by rfl) ⟨997727, by rfl⟩ : syracuseStep 5321213 = 1995455) B1995455
theorem B3781819 : Blo 1048611 3781819 := bstep (se 1 (by rfl) ⟨2836364, by rfl⟩ : syracuseStep 3781819 = 5672729) B5672729
theorem B17937773 : Blo 1048611 17937773 := bstep (se 3 (by rfl) ⟨3363332, by rfl⟩ : syracuseStep 17937773 = 6726665) B6726665
theorem B6732665 : Blo 1048611 6732665 := bstep (se 2 (by rfl) ⟨2524749, by rfl⟩ : syracuseStep 6732665 = 5049499) B5049499
theorem B155401325 : Blo 1048611 155401325 := bstep (se 3 (by rfl) ⟨29137748, by rfl⟩ : syracuseStep 155401325 = 58275497) B58275497
theorem B86261597 : Blo 1048611 86261597 := bstep (se 3 (by rfl) ⟨16174049, by rfl⟩ : syracuseStep 86261597 = 32348099) B32348099
theorem B22986641 : Blo 1048611 22986641 := bstep (se 2 (by rfl) ⟨8619990, by rfl⟩ : syracuseStep 22986641 = 17239981) B17239981
theorem B1327519 : Blo 1048611 1327519 := bstep (se 1 (by rfl) ⟨995639, by rfl⟩ : syracuseStep 1327519 = 1991279) B1991279
theorem B3359387 : Blo 1048611 3359387 := bstep (se 1 (by rfl) ⟨2519540, by rfl⟩ : syracuseStep 3359387 = 5039081) B5039081
theorem B8505107 : Blo 1048611 8505107 := bstep (se 1 (by rfl) ⟨6378830, by rfl⟩ : syracuseStep 8505107 = 12757661) B12757661
theorem B3983849 : Blo 1048611 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B177130643 : Blo 1048611 177130643 := bstep (se 1 (by rfl) ⟨132847982, by rfl⟩ : syracuseStep 177130643 = 265695965) B265695965
theorem B3984623 : Blo 1048611 3984623 := bstep (se 1 (by rfl) ⟨2988467, by rfl⟩ : syracuseStep 3984623 = 5976935) B5976935
theorem B15158987 : Blo 1048611 15158987 := bstep (se 1 (by rfl) ⟨11369240, by rfl⟩ : syracuseStep 15158987 = 22738481) B22738481
theorem B5984225 : Blo 1048611 5984225 := bstep (se 2 (by rfl) ⟨2244084, by rfl⟩ : syracuseStep 5984225 = 4488169) B4488169
theorem B3986567 : Blo 1048611 3986567 := bstep (se 1 (by rfl) ⟨2989925, by rfl⟩ : syracuseStep 3986567 = 5979851) B5979851
theorem B58349159 : Blo 1048611 58349159 := bstep (se 1 (by rfl) ⟨43761869, by rfl⟩ : syracuseStep 58349159 = 87523739) B87523739
theorem B6380311 : Blo 1048611 6380311 := bstep (se 1 (by rfl) ⟨4785233, by rfl⟩ : syracuseStep 6380311 = 9570467) B9570467
theorem B3988511 : Blo 1048611 3988511 := bstep (se 1 (by rfl) ⟨2991383, by rfl⟩ : syracuseStep 3988511 = 5982767) B5982767
theorem B6479999 : Blo 1048611 6479999 := bstep (se 1 (by rfl) ⟨4859999, by rfl⟩ : syracuseStep 6479999 = 9719999) B9719999
theorem B2843305 : Blo 1048611 2843305 := bstep (se 2 (by rfl) ⟨1066239, by rfl⟩ : syracuseStep 2843305 = 2132479) B2132479
theorem B51210245 : Blo 1048611 51210245 := bstep (se 4 (by rfl) ⟨4800960, by rfl⟩ : syracuseStep 51210245 = 9601921) B9601921
theorem B34499417 : Blo 1048611 34499417 := bstep (se 2 (by rfl) ⟨12937281, by rfl⟩ : syracuseStep 34499417 = 25874563) B25874563
theorem B10251359 : Blo 1048611 10251359 := bstep (se 1 (by rfl) ⟨7688519, by rfl⟩ : syracuseStep 10251359 = 15377039) B15377039
theorem B9597251 : Blo 1048611 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B30306899 : Blo 1048611 30306899 := bstep (se 1 (by rfl) ⟨22730174, by rfl⟩ : syracuseStep 30306899 = 45460349) B45460349
theorem B54489773 : Blo 1048611 54489773 := bstep (se 3 (by rfl) ⟨10216832, by rfl⟩ : syracuseStep 54489773 = 20433665) B20433665
theorem B3995999 : Blo 1048611 3995999 := bstep (se 1 (by rfl) ⟨2996999, by rfl⟩ : syracuseStep 3995999 = 5993999) B5993999
theorem B7174955 : Blo 1048611 7174955 := bstep (se 1 (by rfl) ⟨5381216, by rfl⟩ : syracuseStep 7174955 = 10762433) B10762433
theorem B1048667 : Blo 1048611 1048667 := bstep (se 1 (by rfl) ⟨786500, by rfl⟩ : syracuseStep 1048667 = 1573001) B1573001
theorem B2359655 : Blo 1048611 2359655 := bstep (se 1 (by rfl) ⟨1769741, by rfl⟩ : syracuseStep 2359655 = 3539483) B3539483
theorem B1573343 : Blo 1048611 1573343 := bstep (se 1 (by rfl) ⟨1180007, by rfl⟩ : syracuseStep 1573343 = 2360015) B2360015
theorem B1770025 : Blo 1048611 1770025 := bstep (se 2 (by rfl) ⟨663759, by rfl⟩ : syracuseStep 1770025 = 1327519) B1327519
theorem B30343805 : Blo 1048611 30343805 := bstep (se 3 (by rfl) ⟨5689463, by rfl⟩ : syracuseStep 30343805 = 11378927) B11378927
theorem B1049327 : Blo 1048611 1049327 := bstep (se 1 (by rfl) ⟨786995, by rfl⟩ : syracuseStep 1049327 = 1573991) B1573991
theorem B25592669 : Blo 1048611 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B1574057 : Blo 1048611 1574057 := bstep (se 2 (by rfl) ⟨590271, by rfl⟩ : syracuseStep 1574057 = 1180543) B1180543
theorem B5670071 : Blo 1048611 5670071 := bstep (se 1 (by rfl) ⟨4252553, by rfl⟩ : syracuseStep 5670071 = 8505107) B8505107
theorem B1574303 : Blo 1048611 1574303 := bstep (se 1 (by rfl) ⟨1180727, by rfl⟩ : syracuseStep 1574303 = 2361455) B2361455
theorem B1181119 : Blo 1048611 1181119 := bstep (se 1 (by rfl) ⟨885839, by rfl⟩ : syracuseStep 1181119 = 1771679) B1771679
theorem B1574447 : Blo 1048611 1574447 := bstep (se 1 (by rfl) ⟨1180835, by rfl⟩ : syracuseStep 1574447 = 2361671) B2361671
theorem B2655899 : Blo 1048611 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B1050527 : Blo 1048611 1050527 := bstep (se 1 (by rfl) ⟨787895, by rfl⟩ : syracuseStep 1050527 = 1575791) B1575791
theorem B2361311 : Blo 1048611 2361311 := bstep (se 1 (by rfl) ⟨1770983, by rfl⟩ : syracuseStep 2361311 = 3541967) B3541967
theorem B1574975 : Blo 1048611 1574975 := bstep (se 1 (by rfl) ⟨1181231, by rfl⟩ : syracuseStep 1574975 = 2362463) B2362463
theorem B2656415 : Blo 1048611 2656415 := bstep (se 1 (by rfl) ⟨1992311, by rfl⟩ : syracuseStep 2656415 = 3984623) B3984623
theorem B1575095 : Blo 1048611 1575095 := bstep (se 1 (by rfl) ⟨1181321, by rfl⟩ : syracuseStep 1575095 = 2362643) B2362643
theorem B1575743 : Blo 1048611 1575743 := bstep (se 1 (by rfl) ⟨1181807, by rfl⟩ : syracuseStep 1575743 = 2363615) B2363615
theorem B1772543 : Blo 1048611 1772543 := bstep (se 1 (by rfl) ⟨1329407, by rfl⟩ : syracuseStep 1772543 = 2658815) B2658815
theorem B7966025 : Blo 1048611 7966025 := bstep (se 2 (by rfl) ⟨2987259, by rfl⟩ : syracuseStep 7966025 = 5974519) B5974519
theorem B2657711 : Blo 1048611 2657711 := bstep (se 1 (by rfl) ⟨1993283, by rfl⟩ : syracuseStep 2657711 = 3986567) B3986567
theorem B1183279 : Blo 1048611 1183279 := bstep (se 1 (by rfl) ⟨887459, by rfl⟩ : syracuseStep 1183279 = 1774919) B1774919
theorem B1576559 : Blo 1048611 1576559 := bstep (se 1 (by rfl) ⟨1182419, by rfl⟩ : syracuseStep 1576559 = 2364839) B2364839
theorem B1052367 : Blo 1048611 1052367 := bstep (se 1 (by rfl) ⟨789275, by rfl⟩ : syracuseStep 1052367 = 1578551) B1578551
theorem B1576667 : Blo 1048611 1576667 := bstep (se 1 (by rfl) ⟨1182500, by rfl⟩ : syracuseStep 1576667 = 2365001) B2365001
theorem B38899439 : Blo 1048611 38899439 := bstep (se 1 (by rfl) ⟨29174579, by rfl⟩ : syracuseStep 38899439 = 58349159) B58349159
theorem B1774055 : Blo 1048611 1774055 := bstep (se 1 (by rfl) ⟨1330541, by rfl⟩ : syracuseStep 1774055 = 2661083) B2661083
theorem B2659007 : Blo 1048611 2659007 := bstep (se 1 (by rfl) ⟨1994255, by rfl⟩ : syracuseStep 2659007 = 3988511) B3988511
theorem B1577711 : Blo 1048611 1577711 := bstep (se 1 (by rfl) ⟨1183283, by rfl⟩ : syracuseStep 1577711 = 2366567) B2366567
theorem B1578143 : Blo 1048611 1578143 := bstep (se 1 (by rfl) ⟨1183607, by rfl⟩ : syracuseStep 1578143 = 2367215) B2367215
theorem B1578311 : Blo 1048611 1578311 := bstep (se 1 (by rfl) ⟨1183733, by rfl⟩ : syracuseStep 1578311 = 2367467) B2367467
theorem B1578473 : Blo 1048611 1578473 := bstep (se 2 (by rfl) ⟨591927, by rfl⟩ : syracuseStep 1578473 = 1183855) B1183855
theorem B3546071 : Blo 1048611 3546071 := bstep (se 1 (by rfl) ⟨2659553, by rfl⟩ : syracuseStep 3546071 = 5319107) B5319107
theorem B3546395 : Blo 1048611 3546395 := bstep (se 1 (by rfl) ⟨2659796, by rfl⟩ : syracuseStep 3546395 = 5319593) B5319593
theorem B2367323 : Blo 1048611 2367323 := bstep (se 1 (by rfl) ⟨1775492, by rfl⟩ : syracuseStep 2367323 = 3550985) B3550985
theorem B3547475 : Blo 1048611 3547475 := bstep (se 1 (by rfl) ⟨2660606, by rfl⟩ : syracuseStep 3547475 = 5321213) B5321213
theorem B2663999 : Blo 1048611 2663999 := bstep (se 1 (by rfl) ⟨1997999, by rfl⟩ : syracuseStep 2663999 = 3995999) B3995999
theorem B6728615 : Blo 1048611 6728615 := bstep (se 1 (by rfl) ⟨5046461, by rfl⟩ : syracuseStep 6728615 = 10092923) B10092923
theorem B2239591 : Blo 1048611 2239591 := bstep (se 1 (by rfl) ⟨1679693, by rfl⟩ : syracuseStep 2239591 = 3359387) B3359387
theorem B15577115 : Blo 1048611 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B22688657 : Blo 1048611 22688657 := bstep (se 2 (by rfl) ⟨8508246, by rfl⟩ : syracuseStep 22688657 = 17016493) B17016493
theorem B10105991 : Blo 1048611 10105991 := bstep (se 1 (by rfl) ⟨7579493, by rfl⟩ : syracuseStep 10105991 = 15158987) B15158987
theorem B3192043 : Blo 1048611 3192043 := bstep (se 1 (by rfl) ⟨2394032, by rfl⟩ : syracuseStep 3192043 = 4788065) B4788065
theorem B2733311 : Blo 1048611 2733311 := bstep (se 1 (by rfl) ⟨2049983, by rfl⟩ : syracuseStep 2733311 = 4099967) B4099967
theorem B3782483 : Blo 1048611 3782483 := bstep (se 1 (by rfl) ⟨2836862, by rfl⟩ : syracuseStep 3782483 = 5673725) B5673725
theorem B22724297 : Blo 1048611 22724297 := bstep (se 2 (by rfl) ⟨8521611, by rfl⟩ : syracuseStep 22724297 = 17043223) B17043223
theorem B6834239 : Blo 1048611 6834239 := bstep (se 1 (by rfl) ⟨5125679, by rfl⟩ : syracuseStep 6834239 = 10251359) B10251359
theorem B91998445 : Blo 1048611 91998445 := bstep (se 3 (by rfl) ⟨17249708, by rfl⟩ : syracuseStep 91998445 = 34499417) B34499417
theorem B20204599 : Blo 1048611 20204599 := bstep (se 1 (by rfl) ⟨15153449, by rfl⟩ : syracuseStep 20204599 = 30306899) B30306899
theorem B36326515 : Blo 1048611 36326515 := bstep (se 1 (by rfl) ⟨27244886, by rfl⟩ : syracuseStep 36326515 = 54489773) B54489773
theorem B8507081 : Blo 1048611 8507081 := bstep (se 2 (by rfl) ⟨3190155, by rfl⟩ : syracuseStep 8507081 = 6380311) B6380311
theorem B103600883 : Blo 1048611 103600883 := bstep (se 1 (by rfl) ⟨77700662, by rfl⟩ : syracuseStep 103600883 = 155401325) B155401325
theorem B15324427 : Blo 1048611 15324427 := bstep (se 1 (by rfl) ⟨11493320, by rfl⟩ : syracuseStep 15324427 = 22986641) B22986641
theorem B5987641 : Blo 1048611 5987641 := bstep (se 2 (by rfl) ⟨2245365, by rfl⟩ : syracuseStep 5987641 = 4490731) B4490731
theorem B40984535 : Blo 1048611 40984535 := bstep (se 1 (by rfl) ⟨30738401, by rfl⟩ : syracuseStep 40984535 = 61476803) B61476803
theorem B3989483 : Blo 1048611 3989483 := bstep (se 1 (by rfl) ⟨2992112, by rfl⟩ : syracuseStep 3989483 = 5984225) B5984225
theorem B15164293 : Blo 1048611 15164293 := bstep (se 4 (by rfl) ⟨1421652, by rfl⟩ : syracuseStep 15164293 = 2843305) B2843305
theorem B4319999 : Blo 1048611 4319999 := bstep (se 1 (by rfl) ⟨3239999, by rfl⟩ : syracuseStep 4319999 = 6479999) B6479999
theorem B34140163 : Blo 1048611 34140163 := bstep (se 1 (by rfl) ⟨25605122, by rfl⟩ : syracuseStep 34140163 = 51210245) B51210245
theorem B5042425 : Blo 1048611 5042425 := bstep (se 2 (by rfl) ⟨1890909, by rfl⟩ : syracuseStep 5042425 = 3781819) B3781819
theorem B2519579 : Blo 1048611 2519579 := bstep (se 1 (by rfl) ⟨1889684, by rfl⟩ : syracuseStep 2519579 = 3779369) B3779369
theorem B3371831 : Blo 1048611 3371831 := bstep (se 1 (by rfl) ⟨2528873, by rfl⟩ : syracuseStep 3371831 = 5057747) B5057747
theorem B472348381 : Blo 1048611 472348381 := bstep (se 3 (by rfl) ⟨88565321, by rfl⟩ : syracuseStep 472348381 = 177130643) B177130643
theorem B11958515 : Blo 1048611 11958515 := bstep (se 1 (by rfl) ⟨8968886, by rfl⟩ : syracuseStep 11958515 = 17937773) B17937773
theorem B4783303 : Blo 1048611 4783303 := bstep (se 1 (by rfl) ⟨3587477, by rfl⟩ : syracuseStep 4783303 = 7174955) B7174955
theorem B4488443 : Blo 1048611 4488443 := bstep (se 1 (by rfl) ⟨3366332, by rfl⟩ : syracuseStep 4488443 = 6732665) B6732665
theorem B57507731 : Blo 1048611 57507731 := bstep (se 1 (by rfl) ⟨43130798, by rfl⟩ : syracuseStep 57507731 = 86261597) B86261597
theorem B1573103 : Blo 1048611 1573103 := bstep (se 1 (by rfl) ⟨1179827, by rfl⟩ : syracuseStep 1573103 = 2359655) B2359655
theorem B1048895 : Blo 1048611 1048895 := bstep (se 1 (by rfl) ⟨786671, by rfl⟩ : syracuseStep 1048895 = 1573343) B1573343
theorem B2360033 : Blo 1048611 2360033 := bstep (se 2 (by rfl) ⟨885012, by rfl⟩ : syracuseStep 2360033 = 1770025) B1770025
theorem B1049371 : Blo 1048611 1049371 := bstep (se 1 (by rfl) ⟨787028, by rfl⟩ : syracuseStep 1049371 = 1574057) B1574057
theorem B1049535 : Blo 1048611 1049535 := bstep (se 1 (by rfl) ⟨787151, by rfl⟩ : syracuseStep 1049535 = 1574303) B1574303
theorem B1049631 : Blo 1048611 1049631 := bstep (se 1 (by rfl) ⟨787223, by rfl⟩ : syracuseStep 1049631 = 1574447) B1574447
theorem B1770599 : Blo 1048611 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B20219057 : Blo 1048611 20219057 := bstep (se 2 (by rfl) ⟨7582146, by rfl⟩ : syracuseStep 20219057 = 15164293) B15164293
theorem B1574207 : Blo 1048611 1574207 := bstep (se 1 (by rfl) ⟨1180655, by rfl⟩ : syracuseStep 1574207 = 2361311) B2361311
theorem B1049983 : Blo 1048611 1049983 := bstep (se 1 (by rfl) ⟨787487, by rfl⟩ : syracuseStep 1049983 = 1574975) B1574975
theorem B4556159 : Blo 1048611 4556159 := bstep (se 1 (by rfl) ⟨3417119, by rfl⟩ : syracuseStep 4556159 = 6834239) B6834239
theorem B1770943 : Blo 1048611 1770943 := bstep (se 1 (by rfl) ⟨1328207, by rfl⟩ : syracuseStep 1770943 = 2656415) B2656415
theorem B1050063 : Blo 1048611 1050063 := bstep (se 1 (by rfl) ⟨787547, by rfl⟩ : syracuseStep 1050063 = 1575095) B1575095
theorem B1050495 : Blo 1048611 1050495 := bstep (se 1 (by rfl) ⟨787871, by rfl⟩ : syracuseStep 1050495 = 1575743) B1575743
theorem B1574825 : Blo 1048611 1574825 := bstep (se 2 (by rfl) ⟨590559, by rfl⟩ : syracuseStep 1574825 = 1181119) B1181119
theorem B1181695 : Blo 1048611 1181695 := bstep (se 1 (by rfl) ⟨886271, by rfl⟩ : syracuseStep 1181695 = 1772543) B1772543
theorem B5310683 : Blo 1048611 5310683 := bstep (se 1 (by rfl) ⟨3983012, by rfl⟩ : syracuseStep 5310683 = 7966025) B7966025
theorem B1771807 : Blo 1048611 1771807 := bstep (se 1 (by rfl) ⟨1328855, by rfl⟩ : syracuseStep 1771807 = 2657711) B2657711
theorem B1051039 : Blo 1048611 1051039 := bstep (se 1 (by rfl) ⟨788279, by rfl⟩ : syracuseStep 1051039 = 1576559) B1576559
theorem B5671387 : Blo 1048611 5671387 := bstep (se 1 (by rfl) ⟨4253540, by rfl⟩ : syracuseStep 5671387 = 8507081) B8507081
theorem B1051111 : Blo 1048611 1051111 := bstep (se 1 (by rfl) ⟨788333, by rfl⟩ : syracuseStep 1051111 = 1576667) B1576667
theorem B1182703 : Blo 1048611 1182703 := bstep (se 1 (by rfl) ⟨887027, by rfl⟩ : syracuseStep 1182703 = 1774055) B1774055
theorem B1772671 : Blo 1048611 1772671 := bstep (se 1 (by rfl) ⟨1329503, by rfl⟩ : syracuseStep 1772671 = 2659007) B2659007
theorem B1051807 : Blo 1048611 1051807 := bstep (se 1 (by rfl) ⟨788855, by rfl⟩ : syracuseStep 1051807 = 1577711) B1577711
theorem B1052095 : Blo 1048611 1052095 := bstep (se 1 (by rfl) ⟨789071, by rfl⟩ : syracuseStep 1052095 = 1578143) B1578143
theorem B1052207 : Blo 1048611 1052207 := bstep (se 1 (by rfl) ⟨789155, by rfl⟩ : syracuseStep 1052207 = 1578311) B1578311
theorem B1052315 : Blo 1048611 1052315 := bstep (se 1 (by rfl) ⟨789236, by rfl⟩ : syracuseStep 1052315 = 1578473) B1578473
theorem B26939465 : Blo 1048611 26939465 := bstep (se 2 (by rfl) ⟨10102299, by rfl⟩ : syracuseStep 26939465 = 20204599) B20204599
theorem B2986121 : Blo 1048611 2986121 := bstep (se 2 (by rfl) ⟨1119795, by rfl⟩ : syracuseStep 2986121 = 2239591) B2239591
theorem B48435353 : Blo 1048611 48435353 := bstep (se 2 (by rfl) ⟨18163257, by rfl⟩ : syracuseStep 48435353 = 36326515) B36326515
theorem B2364047 : Blo 1048611 2364047 := bstep (se 1 (by rfl) ⟨1773035, by rfl⟩ : syracuseStep 2364047 = 3546071) B3546071
theorem B1577705 : Blo 1048611 1577705 := bstep (se 2 (by rfl) ⟨591639, by rfl⟩ : syracuseStep 1577705 = 1183279) B1183279
theorem B2364263 : Blo 1048611 2364263 := bstep (se 1 (by rfl) ⟨1773197, by rfl⟩ : syracuseStep 2364263 = 3546395) B3546395
theorem B1578215 : Blo 1048611 1578215 := bstep (se 1 (by rfl) ⟨1183661, by rfl⟩ : syracuseStep 1578215 = 2367323) B2367323
theorem B2659655 : Blo 1048611 2659655 := bstep (se 1 (by rfl) ⟨1994741, by rfl⟩ : syracuseStep 2659655 = 3989483) B3989483
theorem B45520217 : Blo 1048611 45520217 := bstep (se 2 (by rfl) ⟨17070081, by rfl⟩ : syracuseStep 45520217 = 34140163) B34140163
theorem B2364983 : Blo 1048611 2364983 := bstep (se 1 (by rfl) ⟨1773737, by rfl⟩ : syracuseStep 2364983 = 3547475) B3547475
theorem B6723233 : Blo 1048611 6723233 := bstep (se 2 (by rfl) ⟨2521212, by rfl⟩ : syracuseStep 6723233 = 5042425) B5042425
theorem B1775999 : Blo 1048611 1775999 := bstep (se 1 (by rfl) ⟨1331999, by rfl⟩ : syracuseStep 1775999 = 2663999) B2663999
theorem B1679719 : Blo 1048611 1679719 := bstep (se 1 (by rfl) ⟨1259789, by rfl⟩ : syracuseStep 1679719 = 2519579) B2519579
theorem B7972343 : Blo 1048611 7972343 := bstep (se 1 (by rfl) ⟨5979257, by rfl⟩ : syracuseStep 7972343 = 11958515) B11958515
theorem B2992295 : Blo 1048611 2992295 := bstep (se 1 (by rfl) ⟨2244221, by rfl⟩ : syracuseStep 2992295 = 4488443) B4488443
theorem B15149531 : Blo 1048611 15149531 := bstep (se 1 (by rfl) ⟨11362148, by rfl⟩ : syracuseStep 15149531 = 22724297) B22724297
theorem B20229203 : Blo 1048611 20229203 := bstep (se 1 (by rfl) ⟨15171902, by rfl⟩ : syracuseStep 20229203 = 30343805) B30343805
theorem B3780047 : Blo 1048611 3780047 := bstep (se 1 (by rfl) ⟨2835035, by rfl⟩ : syracuseStep 3780047 = 5670071) B5670071
theorem B25932959 : Blo 1048611 25932959 := bstep (se 1 (by rfl) ⟨19449719, by rfl⟩ : syracuseStep 25932959 = 38899439) B38899439
theorem B122664593 : Blo 1048611 122664593 := bstep (se 2 (by rfl) ⟨45999222, by rfl⟩ : syracuseStep 122664593 = 91998445) B91998445
theorem B20432569 : Blo 1048611 20432569 := bstep (se 2 (by rfl) ⟨7662213, by rfl⟩ : syracuseStep 20432569 = 15324427) B15324427
theorem B2247887 : Blo 1048611 2247887 := bstep (se 1 (by rfl) ⟨1685915, by rfl⟩ : syracuseStep 2247887 = 3371831) B3371831
theorem B15125771 : Blo 1048611 15125771 := bstep (se 1 (by rfl) ⟨11344328, by rfl⟩ : syracuseStep 15125771 = 22688657) B22688657
theorem B6737327 : Blo 1048611 6737327 := bstep (se 1 (by rfl) ⟨5052995, by rfl⟩ : syracuseStep 6737327 = 10105991) B10105991
theorem B1822207 : Blo 1048611 1822207 := bstep (se 1 (by rfl) ⟨1366655, by rfl⟩ : syracuseStep 1822207 = 2733311) B2733311
theorem B6377737 : Blo 1048611 6377737 := bstep (se 2 (by rfl) ⟨2391651, by rfl⟩ : syracuseStep 6377737 = 4783303) B4783303
theorem B7983521 : Blo 1048611 7983521 := bstep (se 2 (by rfl) ⟨2993820, by rfl⟩ : syracuseStep 7983521 = 5987641) B5987641
theorem B41538973 : Blo 1048611 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B17061779 : Blo 1048611 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B69067255 : Blo 1048611 69067255 := bstep (se 1 (by rfl) ⟨51800441, by rfl⟩ : syracuseStep 69067255 = 103600883) B103600883
theorem B27323023 : Blo 1048611 27323023 := bstep (se 1 (by rfl) ⟨20492267, by rfl⟩ : syracuseStep 27323023 = 40984535) B40984535
theorem B4256057 : Blo 1048611 4256057 := bstep (se 2 (by rfl) ⟨1596021, by rfl⟩ : syracuseStep 4256057 = 3192043) B3192043
theorem B2879999 : Blo 1048611 2879999 := bstep (se 1 (by rfl) ⟨2159999, by rfl⟩ : syracuseStep 2879999 = 4319999) B4319999
theorem B4485743 : Blo 1048611 4485743 := bstep (se 1 (by rfl) ⟨3364307, by rfl⟩ : syracuseStep 4485743 = 6728615) B6728615
theorem B629797841 : Blo 1048611 629797841 := bstep (se 2 (by rfl) ⟨236174190, by rfl⟩ : syracuseStep 629797841 = 472348381) B472348381
theorem B2521655 : Blo 1048611 2521655 := bstep (se 1 (by rfl) ⟨1891241, by rfl⟩ : syracuseStep 2521655 = 3782483) B3782483
theorem B38338487 : Blo 1048611 38338487 := bstep (se 1 (by rfl) ⟨28753865, by rfl⟩ : syracuseStep 38338487 = 57507731) B57507731
theorem B1048735 : Blo 1048611 1048735 := bstep (se 1 (by rfl) ⟨786551, by rfl⟩ : syracuseStep 1048735 = 1573103) B1573103
theorem B1573355 : Blo 1048611 1573355 := bstep (se 1 (by rfl) ⟨1180016, by rfl⟩ : syracuseStep 1573355 = 2360033) B2360033
theorem B1180399 : Blo 1048611 1180399 := bstep (se 1 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 1180399 = 1770599) B1770599
theorem B1049471 : Blo 1048611 1049471 := bstep (se 1 (by rfl) ⟨787103, by rfl⟩ : syracuseStep 1049471 = 1574207) B1574207
theorem B1049883 : Blo 1048611 1049883 := bstep (se 1 (by rfl) ⟨787412, by rfl⟩ : syracuseStep 1049883 = 1574825) B1574825
theorem B3540455 : Blo 1048611 3540455 := bstep (se 1 (by rfl) ⟨2655341, by rfl⟩ : syracuseStep 3540455 = 5310683) B5310683
theorem B2361257 : Blo 1048611 2361257 := bstep (se 2 (by rfl) ⟨885471, by rfl⟩ : syracuseStep 2361257 = 1770943) B1770943
theorem B4491551 : Blo 1048611 4491551 := bstep (se 1 (by rfl) ⟨3368663, by rfl⟩ : syracuseStep 4491551 = 6737327) B6737327
theorem B1575593 : Blo 1048611 1575593 := bstep (se 2 (by rfl) ⟨590847, by rfl⟩ : syracuseStep 1575593 = 1181695) B1181695
theorem B17959643 : Blo 1048611 17959643 := bstep (se 1 (by rfl) ⟨13469732, by rfl⟩ : syracuseStep 17959643 = 26939465) B26939465
theorem B2362409 : Blo 1048611 2362409 := bstep (se 2 (by rfl) ⟨885903, by rfl⟩ : syracuseStep 2362409 = 1771807) B1771807
theorem B1576031 : Blo 1048611 1576031 := bstep (se 1 (by rfl) ⟨1182023, by rfl⟩ : syracuseStep 1576031 = 2364047) B2364047
theorem B1051803 : Blo 1048611 1051803 := bstep (se 1 (by rfl) ⟨788852, by rfl⟩ : syracuseStep 1051803 = 1577705) B1577705
theorem B1576175 : Blo 1048611 1576175 := bstep (se 1 (by rfl) ⟨1182131, by rfl⟩ : syracuseStep 1576175 = 2364263) B2364263
theorem B1052143 : Blo 1048611 1052143 := bstep (se 1 (by rfl) ⟨789107, by rfl⟩ : syracuseStep 1052143 = 1578215) B1578215
theorem B1773103 : Blo 1048611 1773103 := bstep (se 1 (by rfl) ⟨1329827, by rfl⟩ : syracuseStep 1773103 = 2659655) B2659655
theorem B30346811 : Blo 1048611 30346811 := bstep (se 1 (by rfl) ⟨22760108, by rfl⟩ : syracuseStep 30346811 = 45520217) B45520217
theorem B1576655 : Blo 1048611 1576655 := bstep (se 1 (by rfl) ⟨1182491, by rfl⟩ : syracuseStep 1576655 = 2364983) B2364983
theorem B11374519 : Blo 1048611 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B1576937 : Blo 1048611 1576937 := bstep (se 2 (by rfl) ⟨591351, by rfl⟩ : syracuseStep 1576937 = 1182703) B1182703
theorem B2363561 : Blo 1048611 2363561 := bstep (se 2 (by rfl) ⟨886335, by rfl⟩ : syracuseStep 2363561 = 1772671) B1772671
theorem B1183999 : Blo 1048611 1183999 := bstep (se 1 (by rfl) ⟨887999, by rfl⟩ : syracuseStep 1183999 = 1775999) B1775999
theorem B2429609 : Blo 1048611 2429609 := bstep (se 2 (by rfl) ⟨911103, by rfl⟩ : syracuseStep 2429609 = 1822207) B1822207
theorem B5314895 : Blo 1048611 5314895 := bstep (se 1 (by rfl) ⟨3986171, by rfl⟩ : syracuseStep 5314895 = 7972343) B7972343
theorem B10099687 : Blo 1048611 10099687 := bstep (se 1 (by rfl) ⟨7574765, by rfl⟩ : syracuseStep 10099687 = 15149531) B15149531
theorem B55385297 : Blo 1048611 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B2990495 : Blo 1048611 2990495 := bstep (se 1 (by rfl) ⟨2242871, by rfl⟩ : syracuseStep 2990495 = 4485743) B4485743
theorem B419865227 : Blo 1048611 419865227 := bstep (se 1 (by rfl) ⟨314898920, by rfl⟩ : syracuseStep 419865227 = 629797841) B629797841
theorem B1681103 : Blo 1048611 1681103 := bstep (se 1 (by rfl) ⟨1260827, by rfl⟩ : syracuseStep 1681103 = 2521655) B2521655
theorem B2239625 : Blo 1048611 2239625 := bstep (se 2 (by rfl) ⟨839859, by rfl⟩ : syracuseStep 2239625 = 1679719) B1679719
theorem B92089673 : Blo 1048611 92089673 := bstep (se 2 (by rfl) ⟨34533627, by rfl⟩ : syracuseStep 92089673 = 69067255) B69067255
theorem B13479371 : Blo 1048611 13479371 := bstep (se 1 (by rfl) ⟨10109528, by rfl⟩ : syracuseStep 13479371 = 20219057) B20219057
theorem B27243425 : Blo 1048611 27243425 := bstep (se 2 (by rfl) ⟨10216284, by rfl⟩ : syracuseStep 27243425 = 20432569) B20432569
theorem B32290235 : Blo 1048611 32290235 := bstep (se 1 (by rfl) ⟨24217676, by rfl⟩ : syracuseStep 32290235 = 48435353) B48435353
theorem B5322347 : Blo 1048611 5322347 := bstep (se 1 (by rfl) ⟨3991760, by rfl⟩ : syracuseStep 5322347 = 7983521) B7983521
theorem B8503649 : Blo 1048611 8503649 := bstep (se 2 (by rfl) ⟨3188868, by rfl⟩ : syracuseStep 8503649 = 6377737) B6377737
theorem B13486135 : Blo 1048611 13486135 := bstep (se 1 (by rfl) ⟨10114601, by rfl⟩ : syracuseStep 13486135 = 20229203) B20229203
theorem B2837371 : Blo 1048611 2837371 := bstep (se 1 (by rfl) ⟨2128028, by rfl⟩ : syracuseStep 2837371 = 4256057) B4256057
theorem B1919999 : Blo 1048611 1919999 := bstep (se 1 (by rfl) ⟨1439999, by rfl⟩ : syracuseStep 1919999 = 2879999) B2879999
theorem B17288639 : Blo 1048611 17288639 := bstep (se 1 (by rfl) ⟨12966479, by rfl⟩ : syracuseStep 17288639 = 25932959) B25932959
theorem B81776395 : Blo 1048611 81776395 := bstep (se 1 (by rfl) ⟨61332296, by rfl⟩ : syracuseStep 81776395 = 122664593) B122664593
theorem B10080125 : Blo 1048611 10080125 := bstep (se 3 (by rfl) ⟨1890023, by rfl⟩ : syracuseStep 10080125 = 3780047) B3780047
theorem B3037439 : Blo 1048611 3037439 := bstep (se 1 (by rfl) ⟨2278079, by rfl⟩ : syracuseStep 3037439 = 4556159) B4556159
theorem B1498591 : Blo 1048611 1498591 := bstep (se 1 (by rfl) ⟨1123943, by rfl⟩ : syracuseStep 1498591 = 2247887) B2247887
theorem B10083847 : Blo 1048611 10083847 := bstep (se 1 (by rfl) ⟨7562885, by rfl⟩ : syracuseStep 10083847 = 15125771) B15125771
theorem B1990747 : Blo 1048611 1990747 := bstep (se 1 (by rfl) ⟨1493060, by rfl⟩ : syracuseStep 1990747 = 2986121) B2986121
theorem B7561849 : Blo 1048611 7561849 := bstep (se 2 (by rfl) ⟨2835693, by rfl⟩ : syracuseStep 7561849 = 5671387) B5671387
theorem B36430697 : Blo 1048611 36430697 := bstep (se 2 (by rfl) ⟨13661511, by rfl⟩ : syracuseStep 36430697 = 27323023) B27323023
theorem B4482155 : Blo 1048611 4482155 := bstep (se 1 (by rfl) ⟨3361616, by rfl⟩ : syracuseStep 4482155 = 6723233) B6723233
theorem B1994863 : Blo 1048611 1994863 := bstep (se 1 (by rfl) ⟨1496147, by rfl⟩ : syracuseStep 1994863 = 2992295) B2992295
theorem B25558991 : Blo 1048611 25558991 := bstep (se 1 (by rfl) ⟨19169243, by rfl⟩ : syracuseStep 25558991 = 38338487) B38338487
theorem B2654329 : Blo 1048611 2654329 := bstep (se 2 (by rfl) ⟨995373, by rfl⟩ : syracuseStep 2654329 = 1990747) B1990747
theorem B5669099 : Blo 1048611 5669099 := bstep (se 1 (by rfl) ⟨4251824, by rfl⟩ : syracuseStep 5669099 = 8503649) B8503649
theorem B1048903 : Blo 1048611 1048903 := bstep (se 1 (by rfl) ⟨786677, by rfl⟩ : syracuseStep 1048903 = 1573355) B1573355
theorem B1573865 : Blo 1048611 1573865 := bstep (se 2 (by rfl) ⟨590199, by rfl⟩ : syracuseStep 1573865 = 1180399) B1180399
theorem B2360303 : Blo 1048611 2360303 := bstep (se 1 (by rfl) ⟨1770227, by rfl⟩ : syracuseStep 2360303 = 3540455) B3540455
theorem B1574171 : Blo 1048611 1574171 := bstep (se 1 (by rfl) ⟨1180628, by rfl⟩ : syracuseStep 1574171 = 2361257) B2361257
theorem B1050395 : Blo 1048611 1050395 := bstep (se 1 (by rfl) ⟨787796, by rfl⟩ : syracuseStep 1050395 = 1575593) B1575593
theorem B1279999 : Blo 1048611 1279999 := bstep (se 1 (by rfl) ⟨959999, by rfl⟩ : syracuseStep 1279999 = 1919999) B1919999
theorem B1574939 : Blo 1048611 1574939 := bstep (se 1 (by rfl) ⟨1181204, by rfl⟩ : syracuseStep 1574939 = 2362409) B2362409
theorem B1050687 : Blo 1048611 1050687 := bstep (se 1 (by rfl) ⟨788015, by rfl⟩ : syracuseStep 1050687 = 1576031) B1576031
theorem B72649133 : Blo 1048611 72649133 := bstep (se 3 (by rfl) ⟨13621712, by rfl⟩ : syracuseStep 72649133 = 27243425) B27243425
theorem B1051103 : Blo 1048611 1051103 := bstep (se 1 (by rfl) ⟨788327, by rfl⟩ : syracuseStep 1051103 = 1576655) B1576655
theorem B6720083 : Blo 1048611 6720083 := bstep (se 1 (by rfl) ⟨5040062, by rfl⟩ : syracuseStep 6720083 = 10080125) B10080125
theorem B1051291 : Blo 1048611 1051291 := bstep (se 1 (by rfl) ⟨788468, by rfl⟩ : syracuseStep 1051291 = 1576937) B1576937
theorem B1575707 : Blo 1048611 1575707 := bstep (se 1 (by rfl) ⟨1181780, by rfl⟩ : syracuseStep 1575707 = 2363561) B2363561
theorem B3543263 : Blo 1048611 3543263 := bstep (se 1 (by rfl) ⟨2657447, by rfl⟩ : syracuseStep 3543263 = 5314895) B5314895
theorem B2364137 : Blo 1048611 2364137 := bstep (se 2 (by rfl) ⟨886551, by rfl⟩ : syracuseStep 2364137 = 1773103) B1773103
theorem B2659817 : Blo 1048611 2659817 := bstep (se 2 (by rfl) ⟨997431, by rfl⟩ : syracuseStep 2659817 = 1994863) B1994863
theorem B1578665 : Blo 1048611 1578665 := bstep (se 2 (by rfl) ⟨591999, by rfl⟩ : syracuseStep 1578665 = 1183999) B1183999
theorem B279910151 : Blo 1048611 279910151 := bstep (se 1 (by rfl) ⟨209932613, by rfl⟩ : syracuseStep 279910151 = 419865227) B419865227
theorem B24287131 : Blo 1048611 24287131 := bstep (se 1 (by rfl) ⟨18215348, by rfl⟩ : syracuseStep 24287131 = 36430697) B36430697
theorem B2988103 : Blo 1048611 2988103 := bstep (se 1 (by rfl) ⟨2241077, by rfl⟩ : syracuseStep 2988103 = 4482155) B4482155
theorem B1120735 : Blo 1048611 1120735 := bstep (se 1 (by rfl) ⟨840551, by rfl⟩ : syracuseStep 1120735 = 1681103) B1681103
theorem B8986247 : Blo 1048611 8986247 := bstep (se 1 (by rfl) ⟨6739685, by rfl⟩ : syracuseStep 8986247 = 13479371) B13479371
theorem B3548231 : Blo 1048611 3548231 := bstep (se 1 (by rfl) ⟨2661173, by rfl⟩ : syracuseStep 3548231 = 5322347) B5322347
theorem B13445129 : Blo 1048611 13445129 := bstep (se 2 (by rfl) ⟨5041923, by rfl⟩ : syracuseStep 13445129 = 10083847) B10083847
theorem B1050783 : Blo 1048611 1050783 := bstep (se 1 (by rfl) ⟨788087, by rfl⟩ : syracuseStep 1050783 = 1576175) B1576175
theorem B11973095 : Blo 1048611 11973095 := bstep (se 1 (by rfl) ⟨8979821, by rfl⟩ : syracuseStep 11973095 = 17959643) B17959643
theorem B20231207 : Blo 1048611 20231207 := bstep (se 1 (by rfl) ⟨15173405, by rfl⟩ : syracuseStep 20231207 = 30346811) B30346811
theorem B3783161 : Blo 1048611 3783161 := bstep (se 2 (by rfl) ⟨1418685, by rfl⟩ : syracuseStep 3783161 = 2837371) B2837371
theorem B109035193 : Blo 1048611 109035193 := bstep (se 2 (by rfl) ⟨40888197, by rfl⟩ : syracuseStep 109035193 = 81776395) B81776395
theorem B11977469 : Blo 1048611 11977469 := bstep (se 3 (by rfl) ⟨2245775, by rfl⟩ : syracuseStep 11977469 = 4491551) B4491551
theorem B1493083 : Blo 1048611 1493083 := bstep (se 1 (by rfl) ⟨1119812, by rfl⟩ : syracuseStep 1493083 = 2239625) B2239625
theorem B61393115 : Blo 1048611 61393115 := bstep (se 1 (by rfl) ⟨46044836, by rfl⟩ : syracuseStep 61393115 = 92089673) B92089673
theorem B10082465 : Blo 1048611 10082465 := bstep (se 2 (by rfl) ⟨3780924, by rfl⟩ : syracuseStep 10082465 = 7561849) B7561849
theorem B6478957 : Blo 1048611 6478957 := bstep (se 3 (by rfl) ⟨1214804, by rfl⟩ : syracuseStep 6478957 = 2429609) B2429609
theorem B11525759 : Blo 1048611 11525759 := bstep (se 1 (by rfl) ⟨8644319, by rfl⟩ : syracuseStep 11525759 = 17288639) B17288639
theorem B17981513 : Blo 1048611 17981513 := bstep (se 2 (by rfl) ⟨6743067, by rfl⟩ : syracuseStep 17981513 = 13486135) B13486135
theorem B2024959 : Blo 1048611 2024959 := bstep (se 1 (by rfl) ⟨1518719, by rfl⟩ : syracuseStep 2024959 = 3037439) B3037439
theorem B36923531 : Blo 1048611 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B15166025 : Blo 1048611 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B1993663 : Blo 1048611 1993663 := bstep (se 1 (by rfl) ⟨1495247, by rfl⟩ : syracuseStep 1993663 = 2990495) B2990495
theorem B21526823 : Blo 1048611 21526823 := bstep (se 1 (by rfl) ⟨16145117, by rfl⟩ : syracuseStep 21526823 = 32290235) B32290235
theorem B13466249 : Blo 1048611 13466249 := bstep (se 2 (by rfl) ⟨5049843, by rfl⟩ : syracuseStep 13466249 = 10099687) B10099687
theorem B1998121 : Blo 1048611 1998121 := bstep (se 2 (by rfl) ⟨749295, by rfl⟩ : syracuseStep 1998121 = 1498591) B1498591
theorem B17039327 : Blo 1048611 17039327 := bstep (se 1 (by rfl) ⟨12779495, by rfl⟩ : syracuseStep 17039327 = 25558991) B25558991
theorem B3539105 : Blo 1048611 3539105 := bstep (se 2 (by rfl) ⟨1327164, by rfl⟩ : syracuseStep 3539105 = 2654329) B2654329
theorem B7963109 : Blo 1048611 7963109 := bstep (se 4 (by rfl) ⟨746541, by rfl⟩ : syracuseStep 7963109 = 1493083) B1493083
theorem B1049243 : Blo 1048611 1049243 := bstep (se 1 (by rfl) ⟨786932, by rfl⟩ : syracuseStep 1049243 = 1573865) B1573865
theorem B1573535 : Blo 1048611 1573535 := bstep (se 1 (by rfl) ⟨1180151, by rfl⟩ : syracuseStep 1573535 = 2360303) B2360303
theorem B1049447 : Blo 1048611 1049447 := bstep (se 1 (by rfl) ⟨787085, by rfl⟩ : syracuseStep 1049447 = 1574171) B1574171
theorem B1049959 : Blo 1048611 1049959 := bstep (se 1 (by rfl) ⟨787469, by rfl⟩ : syracuseStep 1049959 = 1574939) B1574939
theorem B40928743 : Blo 1048611 40928743 := bstep (se 1 (by rfl) ⟨30696557, by rfl⟩ : syracuseStep 40928743 = 61393115) B61393115
theorem B48432755 : Blo 1048611 48432755 := bstep (se 1 (by rfl) ⟨36324566, by rfl⟩ : syracuseStep 48432755 = 72649133) B72649133
theorem B1050471 : Blo 1048611 1050471 := bstep (se 1 (by rfl) ⟨787853, by rfl⟩ : syracuseStep 1050471 = 1575707) B1575707
theorem B1706665 : Blo 1048611 1706665 := bstep (se 2 (by rfl) ⟨639999, by rfl⟩ : syracuseStep 1706665 = 1279999) B1279999
theorem B2362175 : Blo 1048611 2362175 := bstep (se 1 (by rfl) ⟨1771631, by rfl⟩ : syracuseStep 2362175 = 3543263) B3543263
theorem B1576091 : Blo 1048611 1576091 := bstep (se 1 (by rfl) ⟨1182068, by rfl⟩ : syracuseStep 1576091 = 2364137) B2364137
theorem B1773211 : Blo 1048611 1773211 := bstep (se 1 (by rfl) ⟨1329908, by rfl⟩ : syracuseStep 1773211 = 2659817) B2659817
theorem B1052443 : Blo 1048611 1052443 := bstep (se 1 (by rfl) ⟨789332, by rfl⟩ : syracuseStep 1052443 = 1578665) B1578665
theorem B2658217 : Blo 1048611 2658217 := bstep (se 2 (by rfl) ⟨996831, by rfl⟩ : syracuseStep 2658217 = 1993663) B1993663
theorem B6721643 : Blo 1048611 6721643 := bstep (se 1 (by rfl) ⟨5041232, by rfl⟩ : syracuseStep 6721643 = 10082465) B10082465
theorem B2365487 : Blo 1048611 2365487 := bstep (se 1 (by rfl) ⟨1774115, by rfl⟩ : syracuseStep 2365487 = 3548231) B3548231
theorem B32382841 : Blo 1048611 32382841 := bstep (se 2 (by rfl) ⟨12143565, by rfl⟩ : syracuseStep 32382841 = 24287131) B24287131
theorem B2664161 : Blo 1048611 2664161 := bstep (se 2 (by rfl) ⟨999060, by rfl⟩ : syracuseStep 2664161 = 1998121) B1998121
theorem B3779399 : Blo 1048611 3779399 := bstep (se 1 (by rfl) ⟨2834549, by rfl⟩ : syracuseStep 3779399 = 5669099) B5669099
theorem B2699945 : Blo 1048611 2699945 := bstep (se 2 (by rfl) ⟨1012479, by rfl⟩ : syracuseStep 2699945 = 2024959) B2024959
theorem B5977253 : Blo 1048611 5977253 := bstep (se 4 (by rfl) ⟨560367, by rfl⟩ : syracuseStep 5977253 = 1120735) B1120735
theorem B7683839 : Blo 1048611 7683839 := bstep (se 1 (by rfl) ⟨5762879, by rfl⟩ : syracuseStep 7683839 = 11525759) B11525759
theorem B8963419 : Blo 1048611 8963419 := bstep (se 1 (by rfl) ⟨6722564, by rfl⟩ : syracuseStep 8963419 = 13445129) B13445129
theorem B10110683 : Blo 1048611 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B3984137 : Blo 1048611 3984137 := bstep (se 2 (by rfl) ⟨1494051, by rfl⟩ : syracuseStep 3984137 = 2988103) B2988103
theorem B7982063 : Blo 1048611 7982063 := bstep (se 1 (by rfl) ⟨5986547, by rfl⟩ : syracuseStep 7982063 = 11973095) B11973095
theorem B13487471 : Blo 1048611 13487471 := bstep (se 1 (by rfl) ⟨10115603, by rfl⟩ : syracuseStep 13487471 = 20231207) B20231207
theorem B8638609 : Blo 1048611 8638609 := bstep (se 2 (by rfl) ⟨3239478, by rfl⟩ : syracuseStep 8638609 = 6478957) B6478957
theorem B145380257 : Blo 1048611 145380257 := bstep (se 2 (by rfl) ⟨54517596, by rfl⟩ : syracuseStep 145380257 = 109035193) B109035193
theorem B45438205 : Blo 1048611 45438205 := bstep (se 3 (by rfl) ⟨8519663, by rfl⟩ : syracuseStep 45438205 = 17039327) B17039327
theorem B7984979 : Blo 1048611 7984979 := bstep (se 1 (by rfl) ⟨5988734, by rfl⟩ : syracuseStep 7984979 = 11977469) B11977469
theorem B4480055 : Blo 1048611 4480055 := bstep (se 1 (by rfl) ⟨3360041, by rfl⟩ : syracuseStep 4480055 = 6720083) B6720083
theorem B186606767 : Blo 1048611 186606767 := bstep (se 1 (by rfl) ⟨139955075, by rfl⟩ : syracuseStep 186606767 = 279910151) B279910151
theorem B5990831 : Blo 1048611 5990831 := bstep (se 1 (by rfl) ⟨4493123, by rfl⟩ : syracuseStep 5990831 = 8986247) B8986247
theorem B11987675 : Blo 1048611 11987675 := bstep (se 1 (by rfl) ⟨8990756, by rfl⟩ : syracuseStep 11987675 = 17981513) B17981513
theorem B98462749 : Blo 1048611 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B14351215 : Blo 1048611 14351215 := bstep (se 1 (by rfl) ⟨10763411, by rfl⟩ : syracuseStep 14351215 = 21526823) B21526823
theorem B2522107 : Blo 1048611 2522107 := bstep (se 1 (by rfl) ⟨1891580, by rfl⟩ : syracuseStep 2522107 = 3783161) B3783161
theorem B8977499 : Blo 1048611 8977499 := bstep (se 1 (by rfl) ⟨6733124, by rfl⟩ : syracuseStep 8977499 = 13466249) B13466249
theorem B2359403 : Blo 1048611 2359403 := bstep (se 1 (by rfl) ⟨1769552, by rfl⟩ : syracuseStep 2359403 = 3539105) B3539105
theorem B5308739 : Blo 1048611 5308739 := bstep (se 1 (by rfl) ⟨3981554, by rfl⟩ : syracuseStep 5308739 = 7963109) B7963109
theorem B1049023 : Blo 1048611 1049023 := bstep (se 1 (by rfl) ⟨786767, by rfl⟩ : syracuseStep 1049023 = 1573535) B1573535
theorem B2656091 : Blo 1048611 2656091 := bstep (se 1 (by rfl) ⟨1992068, by rfl⟩ : syracuseStep 2656091 = 3984137) B3984137
theorem B1574783 : Blo 1048611 1574783 := bstep (se 1 (by rfl) ⟨1181087, by rfl⟩ : syracuseStep 1574783 = 2362175) B2362175
theorem B1050727 : Blo 1048611 1050727 := bstep (se 1 (by rfl) ⟨788045, by rfl⟩ : syracuseStep 1050727 = 1576091) B1576091
theorem B1576991 : Blo 1048611 1576991 := bstep (se 1 (by rfl) ⟨1182743, by rfl⟩ : syracuseStep 1576991 = 2365487) B2365487
theorem B2986703 : Blo 1048611 2986703 := bstep (se 1 (by rfl) ⟨2240027, by rfl⟩ : syracuseStep 2986703 = 4480055) B4480055
theorem B2364281 : Blo 1048611 2364281 := bstep (se 2 (by rfl) ⟨886605, by rfl⟩ : syracuseStep 2364281 = 1773211) B1773211
theorem B3544289 : Blo 1048611 3544289 := bstep (se 2 (by rfl) ⟨1329108, by rfl⟩ : syracuseStep 3544289 = 2658217) B2658217
theorem B1776107 : Blo 1048611 1776107 := bstep (se 1 (by rfl) ⟨1332080, by rfl⟩ : syracuseStep 1776107 = 2664161) B2664161
theorem B5122559 : Blo 1048611 5122559 := bstep (se 1 (by rfl) ⟨3841919, by rfl⟩ : syracuseStep 5122559 = 7683839) B7683839
theorem B32288503 : Blo 1048611 32288503 := bstep (se 1 (by rfl) ⟨24216377, by rfl⟩ : syracuseStep 32288503 = 48432755) B48432755
theorem B54571657 : Blo 1048611 54571657 := bstep (se 2 (by rfl) ⟨20464371, by rfl⟩ : syracuseStep 54571657 = 40928743) B40928743
theorem B5321375 : Blo 1048611 5321375 := bstep (se 1 (by rfl) ⟨3991031, by rfl⟩ : syracuseStep 5321375 = 7982063) B7982063
theorem B8991647 : Blo 1048611 8991647 := bstep (se 1 (by rfl) ⟨6743735, by rfl⟩ : syracuseStep 8991647 = 13487471) B13487471
theorem B2275553 : Blo 1048611 2275553 := bstep (se 2 (by rfl) ⟨853332, by rfl⟩ : syracuseStep 2275553 = 1706665) B1706665
theorem B5323319 : Blo 1048611 5323319 := bstep (se 1 (by rfl) ⟨3992489, by rfl⟩ : syracuseStep 5323319 = 7984979) B7984979
theorem B131283665 : Blo 1048611 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B11518145 : Blo 1048611 11518145 := bstep (se 2 (by rfl) ⟨4319304, by rfl⟩ : syracuseStep 11518145 = 8638609) B8638609
theorem B124404511 : Blo 1048611 124404511 := bstep (se 1 (by rfl) ⟨93303383, by rfl⟩ : syracuseStep 124404511 = 186606767) B186606767
theorem B3984835 : Blo 1048611 3984835 := bstep (se 1 (by rfl) ⟨2988626, by rfl⟩ : syracuseStep 3984835 = 5977253) B5977253
theorem B3362809 : Blo 1048611 3362809 := bstep (se 2 (by rfl) ⟨1261053, by rfl⟩ : syracuseStep 3362809 = 2522107) B2522107
theorem B5984999 : Blo 1048611 5984999 := bstep (se 1 (by rfl) ⟨4488749, by rfl⟩ : syracuseStep 5984999 = 8977499) B8977499
theorem B43177121 : Blo 1048611 43177121 := bstep (se 2 (by rfl) ⟨16191420, by rfl⟩ : syracuseStep 43177121 = 32382841) B32382841
theorem B6740455 : Blo 1048611 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B11951225 : Blo 1048611 11951225 := bstep (se 2 (by rfl) ⟨4481709, by rfl⟩ : syracuseStep 11951225 = 8963419) B8963419
theorem B4481095 : Blo 1048611 4481095 := bstep (se 1 (by rfl) ⟨3360821, by rfl⟩ : syracuseStep 4481095 = 6721643) B6721643
theorem B96920171 : Blo 1048611 96920171 := bstep (se 1 (by rfl) ⟨72690128, by rfl⟩ : syracuseStep 96920171 = 145380257) B145380257
theorem B3993887 : Blo 1048611 3993887 := bstep (se 1 (by rfl) ⟨2995415, by rfl⟩ : syracuseStep 3993887 = 5990831) B5990831
theorem B60584273 : Blo 1048611 60584273 := bstep (se 2 (by rfl) ⟨22719102, by rfl⟩ : syracuseStep 60584273 = 45438205) B45438205
theorem B7991783 : Blo 1048611 7991783 := bstep (se 1 (by rfl) ⟨5993837, by rfl⟩ : syracuseStep 7991783 = 11987675) B11987675
theorem B2519599 : Blo 1048611 2519599 := bstep (se 1 (by rfl) ⟨1889699, by rfl⟩ : syracuseStep 2519599 = 3779399) B3779399
theorem B1799963 : Blo 1048611 1799963 := bstep (se 1 (by rfl) ⟨1349972, by rfl⟩ : syracuseStep 1799963 = 2699945) B2699945
theorem B19134953 : Blo 1048611 19134953 := bstep (se 2 (by rfl) ⟨7175607, by rfl⟩ : syracuseStep 19134953 = 14351215) B14351215
theorem B1572935 : Blo 1048611 1572935 := bstep (se 1 (by rfl) ⟨1179701, by rfl⟩ : syracuseStep 1572935 = 2359403) B2359403
theorem B3539159 : Blo 1048611 3539159 := bstep (se 1 (by rfl) ⟨2654369, by rfl⟩ : syracuseStep 3539159 = 5308739) B5308739
theorem B165872681 : Blo 1048611 165872681 := bstep (se 2 (by rfl) ⟨62202255, by rfl⟩ : syracuseStep 165872681 = 124404511) B124404511
theorem B1770727 : Blo 1048611 1770727 := bstep (se 1 (by rfl) ⟨1328045, by rfl⟩ : syracuseStep 1770727 = 2656091) B2656091
theorem B1049855 : Blo 1048611 1049855 := bstep (se 1 (by rfl) ⟨787391, by rfl⟩ : syracuseStep 1049855 = 1574783) B1574783
theorem B1051327 : Blo 1048611 1051327 := bstep (se 1 (by rfl) ⟨788495, by rfl⟩ : syracuseStep 1051327 = 1576991) B1576991
theorem B1576187 : Blo 1048611 1576187 := bstep (se 1 (by rfl) ⟨1182140, by rfl⟩ : syracuseStep 1576187 = 2364281) B2364281
theorem B2362859 : Blo 1048611 2362859 := bstep (se 1 (by rfl) ⟨1772144, by rfl⟩ : syracuseStep 2362859 = 3544289) B3544289
theorem B1184071 : Blo 1048611 1184071 := bstep (se 1 (by rfl) ⟨888053, by rfl⟩ : syracuseStep 1184071 = 1776107) B1776107
theorem B5313113 : Blo 1048611 5313113 := bstep (se 2 (by rfl) ⟨1992417, by rfl⟩ : syracuseStep 5313113 = 3984835) B3984835
theorem B7967483 : Blo 1048611 7967483 := bstep (se 1 (by rfl) ⟨5975612, by rfl⟩ : syracuseStep 7967483 = 11951225) B11951225
theorem B6068141 : Blo 1048611 6068141 := bstep (se 3 (by rfl) ⟨1137776, by rfl⟩ : syracuseStep 6068141 = 2275553) B2275553
theorem B3415039 : Blo 1048611 3415039 := bstep (se 1 (by rfl) ⟨2561279, by rfl⟩ : syracuseStep 3415039 = 5122559) B5122559
theorem B2662591 : Blo 1048611 2662591 := bstep (se 1 (by rfl) ⟨1996943, by rfl⟩ : syracuseStep 2662591 = 3993887) B3993887
theorem B3547583 : Blo 1048611 3547583 := bstep (se 1 (by rfl) ⟨2660687, by rfl⟩ : syracuseStep 3547583 = 5321375) B5321375
theorem B8987273 : Blo 1048611 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B12756635 : Blo 1048611 12756635 := bstep (se 1 (by rfl) ⟨9567476, by rfl⟩ : syracuseStep 12756635 = 19134953) B19134953
theorem B3548879 : Blo 1048611 3548879 := bstep (se 1 (by rfl) ⟨2661659, by rfl⟩ : syracuseStep 3548879 = 5323319) B5323319
theorem B5974793 : Blo 1048611 5974793 := bstep (se 2 (by rfl) ⟨2240547, by rfl⟩ : syracuseStep 5974793 = 4481095) B4481095
theorem B7678763 : Blo 1048611 7678763 := bstep (se 1 (by rfl) ⟨5759072, by rfl⟩ : syracuseStep 7678763 = 11518145) B11518145
theorem B28784747 : Blo 1048611 28784747 := bstep (se 1 (by rfl) ⟨21588560, by rfl⟩ : syracuseStep 28784747 = 43177121) B43177121
theorem B3359465 : Blo 1048611 3359465 := bstep (se 2 (by rfl) ⟨1259799, by rfl⟩ : syracuseStep 3359465 = 2519599) B2519599
theorem B72762209 : Blo 1048611 72762209 := bstep (se 2 (by rfl) ⟨27285828, by rfl⟩ : syracuseStep 72762209 = 54571657) B54571657
theorem B40389515 : Blo 1048611 40389515 := bstep (se 1 (by rfl) ⟨30292136, by rfl⟩ : syracuseStep 40389515 = 60584273) B60584273
theorem B5327855 : Blo 1048611 5327855 := bstep (se 1 (by rfl) ⟨3995891, by rfl⟩ : syracuseStep 5327855 = 7991783) B7991783
theorem B1991135 : Blo 1048611 1991135 := bstep (se 1 (by rfl) ⟨1493351, by rfl⟩ : syracuseStep 1991135 = 2986703) B2986703
theorem B3989999 : Blo 1048611 3989999 := bstep (se 1 (by rfl) ⟨2992499, by rfl⟩ : syracuseStep 3989999 = 5984999) B5984999
theorem B43051337 : Blo 1048611 43051337 := bstep (se 2 (by rfl) ⟨16144251, by rfl⟩ : syracuseStep 43051337 = 32288503) B32288503
theorem B4483745 : Blo 1048611 4483745 := bstep (se 2 (by rfl) ⟨1681404, by rfl⟩ : syracuseStep 4483745 = 3362809) B3362809
theorem B64613447 : Blo 1048611 64613447 := bstep (se 1 (by rfl) ⟨48460085, by rfl⟩ : syracuseStep 64613447 = 96920171) B96920171
theorem B19199605 : Blo 1048611 19199605 := bstep (se 5 (by rfl) ⟨899981, by rfl⟩ : syracuseStep 19199605 = 1799963) B1799963
theorem B5994431 : Blo 1048611 5994431 := bstep (se 1 (by rfl) ⟨4495823, by rfl⟩ : syracuseStep 5994431 = 8991647) B8991647
theorem B87522443 : Blo 1048611 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B1048623 : Blo 1048611 1048623 := bstep (se 1 (by rfl) ⟨786467, by rfl⟩ : syracuseStep 1048623 = 1572935) B1572935
theorem B2359439 : Blo 1048611 2359439 := bstep (se 1 (by rfl) ⟨1769579, by rfl⟩ : syracuseStep 2359439 = 3539159) B3539159
theorem B2360969 : Blo 1048611 2360969 := bstep (se 2 (by rfl) ⟨885363, by rfl⟩ : syracuseStep 2360969 = 1770727) B1770727
theorem B1050791 : Blo 1048611 1050791 := bstep (se 1 (by rfl) ⟨788093, by rfl⟩ : syracuseStep 1050791 = 1576187) B1576187
theorem B1575239 : Blo 1048611 1575239 := bstep (se 1 (by rfl) ⟨1181429, by rfl⟩ : syracuseStep 1575239 = 2362859) B2362859
theorem B3542075 : Blo 1048611 3542075 := bstep (se 1 (by rfl) ⟨2656556, by rfl⟩ : syracuseStep 3542075 = 5313113) B5313113
theorem B5311655 : Blo 1048611 5311655 := bstep (se 1 (by rfl) ⟨3983741, by rfl⟩ : syracuseStep 5311655 = 7967483) B7967483
theorem B2365055 : Blo 1048611 2365055 := bstep (se 1 (by rfl) ⟨1773791, by rfl⟩ : syracuseStep 2365055 = 3547583) B3547583
theorem B2659999 : Blo 1048611 2659999 := bstep (se 1 (by rfl) ⟨1994999, by rfl⟩ : syracuseStep 2659999 = 3989999) B3989999
theorem B1578761 : Blo 1048611 1578761 := bstep (se 2 (by rfl) ⟨592035, by rfl⟩ : syracuseStep 1578761 = 1184071) B1184071
theorem B2365919 : Blo 1048611 2365919 := bstep (se 1 (by rfl) ⟨1774439, by rfl⟩ : syracuseStep 2365919 = 3548879) B3548879
theorem B2989163 : Blo 1048611 2989163 := bstep (se 1 (by rfl) ⟨2241872, by rfl⟩ : syracuseStep 2989163 = 4483745) B4483745
theorem B5119175 : Blo 1048611 5119175 := bstep (se 1 (by rfl) ⟨3839381, by rfl⟩ : syracuseStep 5119175 = 7678763) B7678763
theorem B25599473 : Blo 1048611 25599473 := bstep (se 2 (by rfl) ⟨9599802, by rfl⟩ : syracuseStep 25599473 = 19199605) B19199605
theorem B3550121 : Blo 1048611 3550121 := bstep (se 2 (by rfl) ⟨1331295, by rfl⟩ : syracuseStep 3550121 = 2662591) B2662591
theorem B2239643 : Blo 1048611 2239643 := bstep (se 1 (by rfl) ⟨1679732, by rfl⟩ : syracuseStep 2239643 = 3359465) B3359465
theorem B48508139 : Blo 1048611 48508139 := bstep (se 1 (by rfl) ⟨36381104, by rfl⟩ : syracuseStep 48508139 = 72762209) B72762209
theorem B3551903 : Blo 1048611 3551903 := bstep (se 1 (by rfl) ⟨2663927, by rfl⟩ : syracuseStep 3551903 = 5327855) B5327855
theorem B4045427 : Blo 1048611 4045427 := bstep (se 1 (by rfl) ⟨3034070, by rfl⟩ : syracuseStep 4045427 = 6068141) B6068141
theorem B76759325 : Blo 1048611 76759325 := bstep (se 3 (by rfl) ⟨14392373, by rfl⟩ : syracuseStep 76759325 = 28784747) B28784747
theorem B1327423 : Blo 1048611 1327423 := bstep (se 1 (by rfl) ⟨995567, by rfl⟩ : syracuseStep 1327423 = 1991135) B1991135
theorem B8504423 : Blo 1048611 8504423 := bstep (se 1 (by rfl) ⟨6378317, by rfl⟩ : syracuseStep 8504423 = 12756635) B12756635
theorem B3983195 : Blo 1048611 3983195 := bstep (se 1 (by rfl) ⟨2987396, by rfl⟩ : syracuseStep 3983195 = 5974793) B5974793
theorem B43075631 : Blo 1048611 43075631 := bstep (se 1 (by rfl) ⟨32306723, by rfl⟩ : syracuseStep 43075631 = 64613447) B64613447
theorem B58348295 : Blo 1048611 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B110581787 : Blo 1048611 110581787 := bstep (se 1 (by rfl) ⟨82936340, by rfl⟩ : syracuseStep 110581787 = 165872681) B165872681
theorem B26926343 : Blo 1048611 26926343 := bstep (se 1 (by rfl) ⟨20194757, by rfl⟩ : syracuseStep 26926343 = 40389515) B40389515
theorem B18213541 : Blo 1048611 18213541 := bstep (se 4 (by rfl) ⟨1707519, by rfl⟩ : syracuseStep 18213541 = 3415039) B3415039
theorem B5991515 : Blo 1048611 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B28700891 : Blo 1048611 28700891 := bstep (se 1 (by rfl) ⟨21525668, by rfl⟩ : syracuseStep 28700891 = 43051337) B43051337
theorem B3996287 : Blo 1048611 3996287 := bstep (se 1 (by rfl) ⟨2997215, by rfl⟩ : syracuseStep 3996287 = 5994431) B5994431
theorem B1572959 : Blo 1048611 1572959 := bstep (se 1 (by rfl) ⟨1179719, by rfl⟩ : syracuseStep 1572959 = 2359439) B2359439
theorem B1769897 : Blo 1048611 1769897 := bstep (se 2 (by rfl) ⟨663711, by rfl⟩ : syracuseStep 1769897 = 1327423) B1327423
theorem B5669615 : Blo 1048611 5669615 := bstep (se 1 (by rfl) ⟨4252211, by rfl⟩ : syracuseStep 5669615 = 8504423) B8504423
theorem B1573979 : Blo 1048611 1573979 := bstep (se 1 (by rfl) ⟨1180484, by rfl⟩ : syracuseStep 1573979 = 2360969) B2360969
theorem B2655463 : Blo 1048611 2655463 := bstep (se 1 (by rfl) ⟨1991597, by rfl⟩ : syracuseStep 2655463 = 3983195) B3983195
theorem B1050159 : Blo 1048611 1050159 := bstep (se 1 (by rfl) ⟨787619, by rfl⟩ : syracuseStep 1050159 = 1575239) B1575239
theorem B2361383 : Blo 1048611 2361383 := bstep (se 1 (by rfl) ⟨1771037, by rfl⟩ : syracuseStep 2361383 = 3542075) B3542075
theorem B3541103 : Blo 1048611 3541103 := bstep (se 1 (by rfl) ⟨2655827, by rfl⟩ : syracuseStep 3541103 = 5311655) B5311655
theorem B38898863 : Blo 1048611 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B1576703 : Blo 1048611 1576703 := bstep (se 1 (by rfl) ⟨1182527, by rfl⟩ : syracuseStep 1576703 = 2365055) B2365055
theorem B1052507 : Blo 1048611 1052507 := bstep (se 1 (by rfl) ⟨789380, by rfl⟩ : syracuseStep 1052507 = 1578761) B1578761
theorem B1577279 : Blo 1048611 1577279 := bstep (se 1 (by rfl) ⟨1182959, by rfl⟩ : syracuseStep 1577279 = 2365919) B2365919
theorem B3412783 : Blo 1048611 3412783 := bstep (se 1 (by rfl) ⟨2559587, by rfl⟩ : syracuseStep 3412783 = 5119175) B5119175
theorem B2366747 : Blo 1048611 2366747 := bstep (se 1 (by rfl) ⟨1775060, by rfl⟩ : syracuseStep 2366747 = 3550121) B3550121
theorem B3546665 : Blo 1048611 3546665 := bstep (se 2 (by rfl) ⟨1329999, by rfl⟩ : syracuseStep 3546665 = 2659999) B2659999
theorem B2367935 : Blo 1048611 2367935 := bstep (se 1 (by rfl) ⟨1775951, by rfl⟩ : syracuseStep 2367935 = 3551903) B3551903
theorem B2696951 : Blo 1048611 2696951 := bstep (se 1 (by rfl) ⟨2022713, by rfl⟩ : syracuseStep 2696951 = 4045427) B4045427
theorem B2664191 : Blo 1048611 2664191 := bstep (se 1 (by rfl) ⟨1998143, by rfl⟩ : syracuseStep 2664191 = 3996287) B3996287
theorem B28717087 : Blo 1048611 28717087 := bstep (se 1 (by rfl) ⟨21537815, by rfl⟩ : syracuseStep 28717087 = 43075631) B43075631
theorem B97138885 : Blo 1048611 97138885 := bstep (se 4 (by rfl) ⟨9106770, by rfl⟩ : syracuseStep 97138885 = 18213541) B18213541
theorem B1493095 : Blo 1048611 1493095 := bstep (se 1 (by rfl) ⟨1119821, by rfl⟩ : syracuseStep 1493095 = 2239643) B2239643
theorem B51172883 : Blo 1048611 51172883 := bstep (se 1 (by rfl) ⟨38379662, by rfl⟩ : syracuseStep 51172883 = 76759325) B76759325
theorem B73721191 : Blo 1048611 73721191 := bstep (se 1 (by rfl) ⟨55290893, by rfl⟩ : syracuseStep 73721191 = 110581787) B110581787
theorem B1992775 : Blo 1048611 1992775 := bstep (se 1 (by rfl) ⟨1494581, by rfl⟩ : syracuseStep 1992775 = 2989163) B2989163
theorem B17950895 : Blo 1048611 17950895 := bstep (se 1 (by rfl) ⟨13463171, by rfl⟩ : syracuseStep 17950895 = 26926343) B26926343
theorem B17066315 : Blo 1048611 17066315 := bstep (se 1 (by rfl) ⟨12799736, by rfl⟩ : syracuseStep 17066315 = 25599473) B25599473
theorem B3994343 : Blo 1048611 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B32338759 : Blo 1048611 32338759 := bstep (se 1 (by rfl) ⟨24254069, by rfl⟩ : syracuseStep 32338759 = 48508139) B48508139
theorem B19133927 : Blo 1048611 19133927 := bstep (se 1 (by rfl) ⟨14350445, by rfl⟩ : syracuseStep 19133927 = 28700891) B28700891
theorem B1048639 : Blo 1048611 1048639 := bstep (se 1 (by rfl) ⟨786479, by rfl⟩ : syracuseStep 1048639 = 1572959) B1572959
theorem B1179931 : Blo 1048611 1179931 := bstep (se 1 (by rfl) ⟨884948, by rfl⟩ : syracuseStep 1179931 = 1769897) B1769897
theorem B1049319 : Blo 1048611 1049319 := bstep (se 1 (by rfl) ⟨786989, by rfl⟩ : syracuseStep 1049319 = 1573979) B1573979
theorem B1574255 : Blo 1048611 1574255 := bstep (se 1 (by rfl) ⟨1180691, by rfl⟩ : syracuseStep 1574255 = 2361383) B2361383
theorem B2360735 : Blo 1048611 2360735 := bstep (se 1 (by rfl) ⟨1770551, by rfl⟩ : syracuseStep 2360735 = 3541103) B3541103
theorem B3540617 : Blo 1048611 3540617 := bstep (se 2 (by rfl) ⟨1327731, by rfl⟩ : syracuseStep 3540617 = 2655463) B2655463
theorem B1051135 : Blo 1048611 1051135 := bstep (se 1 (by rfl) ⟨788351, by rfl⟩ : syracuseStep 1051135 = 1576703) B1576703
theorem B2657033 : Blo 1048611 2657033 := bstep (se 2 (by rfl) ⟨996387, by rfl⟩ : syracuseStep 2657033 = 1992775) B1992775
theorem B1051519 : Blo 1048611 1051519 := bstep (se 1 (by rfl) ⟨788639, by rfl⟩ : syracuseStep 1051519 = 1577279) B1577279
theorem B34115255 : Blo 1048611 34115255 := bstep (se 1 (by rfl) ⟨25586441, by rfl⟩ : syracuseStep 34115255 = 51172883) B51172883
theorem B1577831 : Blo 1048611 1577831 := bstep (se 1 (by rfl) ⟨1183373, by rfl⟩ : syracuseStep 1577831 = 2366747) B2366747
theorem B2364443 : Blo 1048611 2364443 := bstep (se 1 (by rfl) ⟨1773332, by rfl⟩ : syracuseStep 2364443 = 3546665) B3546665
theorem B1578623 : Blo 1048611 1578623 := bstep (se 1 (by rfl) ⟨1183967, by rfl⟩ : syracuseStep 1578623 = 2367935) B2367935
theorem B1776127 : Blo 1048611 1776127 := bstep (se 1 (by rfl) ⟨1332095, by rfl⟩ : syracuseStep 1776127 = 2664191) B2664191
theorem B11967263 : Blo 1048611 11967263 := bstep (se 1 (by rfl) ⟨8975447, by rfl⟩ : syracuseStep 11967263 = 17950895) B17950895
theorem B2662895 : Blo 1048611 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B12755951 : Blo 1048611 12755951 := bstep (se 1 (by rfl) ⟨9566963, by rfl⟩ : syracuseStep 12755951 = 19133927) B19133927
theorem B15118973 : Blo 1048611 15118973 := bstep (se 3 (by rfl) ⟨2834807, by rfl⟩ : syracuseStep 15118973 = 5669615) B5669615
theorem B25932575 : Blo 1048611 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B38289449 : Blo 1048611 38289449 := bstep (se 2 (by rfl) ⟨14358543, by rfl⟩ : syracuseStep 38289449 = 28717087) B28717087
theorem B129518513 : Blo 1048611 129518513 := bstep (se 2 (by rfl) ⟨48569442, by rfl⟩ : syracuseStep 129518513 = 97138885) B97138885
theorem B98294921 : Blo 1048611 98294921 := bstep (se 2 (by rfl) ⟨36860595, by rfl⟩ : syracuseStep 98294921 = 73721191) B73721191
theorem B1990793 : Blo 1048611 1990793 := bstep (se 2 (by rfl) ⟨746547, by rfl⟩ : syracuseStep 1990793 = 1493095) B1493095
theorem B45510173 : Blo 1048611 45510173 := bstep (se 3 (by rfl) ⟨8533157, by rfl⟩ : syracuseStep 45510173 = 17066315) B17066315
theorem B4550377 : Blo 1048611 4550377 := bstep (se 2 (by rfl) ⟨1706391, by rfl⟩ : syracuseStep 4550377 = 3412783) B3412783
theorem B43118345 : Blo 1048611 43118345 := bstep (se 2 (by rfl) ⟨16169379, by rfl⟩ : syracuseStep 43118345 = 32338759) B32338759
theorem B1797967 : Blo 1048611 1797967 := bstep (se 1 (by rfl) ⟨1348475, by rfl⟩ : syracuseStep 1797967 = 2696951) B2696951
theorem B25526299 : Blo 1048611 25526299 := bstep (se 1 (by rfl) ⟨19144724, by rfl⟩ : syracuseStep 25526299 = 38289449) B38289449
theorem B1573241 : Blo 1048611 1573241 := bstep (se 2 (by rfl) ⟨589965, by rfl⟩ : syracuseStep 1573241 = 1179931) B1179931
theorem B1049503 : Blo 1048611 1049503 := bstep (se 1 (by rfl) ⟨787127, by rfl⟩ : syracuseStep 1049503 = 1574255) B1574255
theorem B1573823 : Blo 1048611 1573823 := bstep (se 1 (by rfl) ⟨1180367, by rfl⟩ : syracuseStep 1573823 = 2360735) B2360735
theorem B2360411 : Blo 1048611 2360411 := bstep (se 1 (by rfl) ⟨1770308, by rfl⟩ : syracuseStep 2360411 = 3540617) B3540617
theorem B1771355 : Blo 1048611 1771355 := bstep (se 1 (by rfl) ⟨1328516, by rfl⟩ : syracuseStep 1771355 = 2657033) B2657033
theorem B86345675 : Blo 1048611 86345675 := bstep (se 1 (by rfl) ⟨64759256, by rfl⟩ : syracuseStep 86345675 = 129518513) B129518513
theorem B22743503 : Blo 1048611 22743503 := bstep (se 1 (by rfl) ⟨17057627, by rfl⟩ : syracuseStep 22743503 = 34115255) B34115255
theorem B1051887 : Blo 1048611 1051887 := bstep (se 1 (by rfl) ⟨788915, by rfl⟩ : syracuseStep 1051887 = 1577831) B1577831
theorem B1576295 : Blo 1048611 1576295 := bstep (se 1 (by rfl) ⟨1182221, by rfl⟩ : syracuseStep 1576295 = 2364443) B2364443
theorem B1052415 : Blo 1048611 1052415 := bstep (se 1 (by rfl) ⟨789311, by rfl⟩ : syracuseStep 1052415 = 1578623) B1578623
theorem B6067169 : Blo 1048611 6067169 := bstep (se 2 (by rfl) ⟨2275188, by rfl⟩ : syracuseStep 6067169 = 4550377) B4550377
theorem B2397289 : Blo 1048611 2397289 := bstep (se 2 (by rfl) ⟨898983, by rfl⟩ : syracuseStep 2397289 = 1797967) B1797967
theorem B1775263 : Blo 1048611 1775263 := bstep (se 1 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 1775263 = 2662895) B2662895
theorem B28745563 : Blo 1048611 28745563 := bstep (se 1 (by rfl) ⟨21559172, by rfl⟩ : syracuseStep 28745563 = 43118345) B43118345
theorem B2368169 : Blo 1048611 2368169 := bstep (se 2 (by rfl) ⟨888063, by rfl⟩ : syracuseStep 2368169 = 1776127) B1776127
theorem B69153533 : Blo 1048611 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B7978175 : Blo 1048611 7978175 := bstep (se 1 (by rfl) ⟨5983631, by rfl⟩ : syracuseStep 7978175 = 11967263) B11967263
theorem B1327195 : Blo 1048611 1327195 := bstep (se 1 (by rfl) ⟨995396, by rfl⟩ : syracuseStep 1327195 = 1990793) B1990793
theorem B8503967 : Blo 1048611 8503967 := bstep (se 1 (by rfl) ⟨6377975, by rfl⟩ : syracuseStep 8503967 = 12755951) B12755951
theorem B10079315 : Blo 1048611 10079315 := bstep (se 1 (by rfl) ⟨7559486, by rfl⟩ : syracuseStep 10079315 = 15118973) B15118973
theorem B65529947 : Blo 1048611 65529947 := bstep (se 1 (by rfl) ⟨49147460, by rfl⟩ : syracuseStep 65529947 = 98294921) B98294921
theorem B30340115 : Blo 1048611 30340115 := bstep (se 1 (by rfl) ⟨22755086, by rfl⟩ : syracuseStep 30340115 = 45510173) B45510173
theorem B1769593 : Blo 1048611 1769593 := bstep (se 2 (by rfl) ⟨663597, by rfl⟩ : syracuseStep 1769593 = 1327195) B1327195
theorem B1048827 : Blo 1048611 1048827 := bstep (se 1 (by rfl) ⟨786620, by rfl⟩ : syracuseStep 1048827 = 1573241) B1573241
theorem B1049215 : Blo 1048611 1049215 := bstep (se 1 (by rfl) ⟨786911, by rfl⟩ : syracuseStep 1049215 = 1573823) B1573823
theorem B1573607 : Blo 1048611 1573607 := bstep (se 1 (by rfl) ⟨1180205, by rfl⟩ : syracuseStep 1573607 = 2360411) B2360411
theorem B1180903 : Blo 1048611 1180903 := bstep (se 1 (by rfl) ⟨885677, by rfl⟩ : syracuseStep 1180903 = 1771355) B1771355
theorem B22677245 : Blo 1048611 22677245 := bstep (se 3 (by rfl) ⟨4251983, by rfl⟩ : syracuseStep 22677245 = 8503967) B8503967
theorem B6719543 : Blo 1048611 6719543 := bstep (se 1 (by rfl) ⟨5039657, by rfl⟩ : syracuseStep 6719543 = 10079315) B10079315
theorem B1050863 : Blo 1048611 1050863 := bstep (se 1 (by rfl) ⟨788147, by rfl⟩ : syracuseStep 1050863 = 1576295) B1576295
theorem B1578779 : Blo 1048611 1578779 := bstep (se 1 (by rfl) ⟨1184084, by rfl⟩ : syracuseStep 1578779 = 2368169) B2368169
theorem B43686631 : Blo 1048611 43686631 := bstep (se 1 (by rfl) ⟨32764973, by rfl⟩ : syracuseStep 43686631 = 65529947) B65529947
theorem B2367017 : Blo 1048611 2367017 := bstep (se 2 (by rfl) ⟨887631, by rfl⟩ : syracuseStep 2367017 = 1775263) B1775263
theorem B20226743 : Blo 1048611 20226743 := bstep (se 1 (by rfl) ⟨15170057, by rfl⟩ : syracuseStep 20226743 = 30340115) B30340115
theorem B5318783 : Blo 1048611 5318783 := bstep (se 1 (by rfl) ⟨3989087, by rfl⟩ : syracuseStep 5318783 = 7978175) B7978175
theorem B4044779 : Blo 1048611 4044779 := bstep (se 1 (by rfl) ⟨3033584, by rfl⟩ : syracuseStep 4044779 = 6067169) B6067169
theorem B3196385 : Blo 1048611 3196385 := bstep (se 2 (by rfl) ⟨1198644, by rfl⟩ : syracuseStep 3196385 = 2397289) B2397289
theorem B38327417 : Blo 1048611 38327417 := bstep (se 2 (by rfl) ⟨14372781, by rfl⟩ : syracuseStep 38327417 = 28745563) B28745563
theorem B34035065 : Blo 1048611 34035065 := bstep (se 2 (by rfl) ⟨12763149, by rfl⟩ : syracuseStep 34035065 = 25526299) B25526299
theorem B57563783 : Blo 1048611 57563783 := bstep (se 1 (by rfl) ⟨43172837, by rfl⟩ : syracuseStep 57563783 = 86345675) B86345675
theorem B15162335 : Blo 1048611 15162335 := bstep (se 1 (by rfl) ⟨11371751, by rfl⟩ : syracuseStep 15162335 = 22743503) B22743503
theorem B46102355 : Blo 1048611 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B2359457 : Blo 1048611 2359457 := bstep (se 2 (by rfl) ⟨884796, by rfl⟩ : syracuseStep 2359457 = 1769593) B1769593
theorem B1049071 : Blo 1048611 1049071 := bstep (se 1 (by rfl) ⟨786803, by rfl⟩ : syracuseStep 1049071 = 1573607) B1573607
theorem B2130923 : Blo 1048611 2130923 := bstep (se 1 (by rfl) ⟨1598192, by rfl⟩ : syracuseStep 2130923 = 3196385) B3196385
theorem B1574537 : Blo 1048611 1574537 := bstep (se 2 (by rfl) ⟨590451, by rfl⟩ : syracuseStep 1574537 = 1180903) B1180903
theorem B1052519 : Blo 1048611 1052519 := bstep (se 1 (by rfl) ⟨789389, by rfl⟩ : syracuseStep 1052519 = 1578779) B1578779
theorem B38375855 : Blo 1048611 38375855 := bstep (se 1 (by rfl) ⟨28781891, by rfl⟩ : syracuseStep 38375855 = 57563783) B57563783
theorem B1578011 : Blo 1048611 1578011 := bstep (se 1 (by rfl) ⟨1183508, by rfl⟩ : syracuseStep 1578011 = 2367017) B2367017
theorem B3545855 : Blo 1048611 3545855 := bstep (se 1 (by rfl) ⟨2659391, by rfl⟩ : syracuseStep 3545855 = 5318783) B5318783
theorem B2696519 : Blo 1048611 2696519 := bstep (se 1 (by rfl) ⟨2022389, by rfl⟩ : syracuseStep 2696519 = 4044779) B4044779
theorem B15118163 : Blo 1048611 15118163 := bstep (se 1 (by rfl) ⟨11338622, by rfl⟩ : syracuseStep 15118163 = 22677245) B22677245
theorem B22690043 : Blo 1048611 22690043 := bstep (se 1 (by rfl) ⟨17017532, by rfl⟩ : syracuseStep 22690043 = 34035065) B34035065
theorem B10108223 : Blo 1048611 10108223 := bstep (se 1 (by rfl) ⟨7581167, by rfl⟩ : syracuseStep 10108223 = 15162335) B15162335
theorem B13484495 : Blo 1048611 13484495 := bstep (se 1 (by rfl) ⟨10113371, by rfl⟩ : syracuseStep 13484495 = 20226743) B20226743
theorem B58248841 : Blo 1048611 58248841 := bstep (se 2 (by rfl) ⟨21843315, by rfl⟩ : syracuseStep 58248841 = 43686631) B43686631
theorem B4479695 : Blo 1048611 4479695 := bstep (se 1 (by rfl) ⟨3359771, by rfl⟩ : syracuseStep 4479695 = 6719543) B6719543
theorem B25551611 : Blo 1048611 25551611 := bstep (se 1 (by rfl) ⟨19163708, by rfl⟩ : syracuseStep 25551611 = 38327417) B38327417
theorem B30734903 : Blo 1048611 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B1572971 : Blo 1048611 1572971 := bstep (se 1 (by rfl) ⟨1179728, by rfl⟩ : syracuseStep 1572971 = 2359457) B2359457
theorem B1049691 : Blo 1048611 1049691 := bstep (se 1 (by rfl) ⟨787268, by rfl⟩ : syracuseStep 1049691 = 1574537) B1574537
theorem B1052007 : Blo 1048611 1052007 := bstep (se 1 (by rfl) ⟨789005, by rfl⟩ : syracuseStep 1052007 = 1578011) B1578011
theorem B2986463 : Blo 1048611 2986463 := bstep (se 1 (by rfl) ⟨2239847, by rfl⟩ : syracuseStep 2986463 = 4479695) B4479695
theorem B2363903 : Blo 1048611 2363903 := bstep (se 1 (by rfl) ⟨1772927, by rfl⟩ : syracuseStep 2363903 = 3545855) B3545855
theorem B77665121 : Blo 1048611 77665121 := bstep (se 2 (by rfl) ⟨29124420, by rfl⟩ : syracuseStep 77665121 = 58248841) B58248841
theorem B20489935 : Blo 1048611 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B8989663 : Blo 1048611 8989663 := bstep (se 1 (by rfl) ⟨6742247, by rfl⟩ : syracuseStep 8989663 = 13484495) B13484495
theorem B1420615 : Blo 1048611 1420615 := bstep (se 1 (by rfl) ⟨1065461, by rfl⟩ : syracuseStep 1420615 = 2130923) B2130923
theorem B10078775 : Blo 1048611 10078775 := bstep (se 1 (by rfl) ⟨7559081, by rfl⟩ : syracuseStep 10078775 = 15118163) B15118163
theorem B15126695 : Blo 1048611 15126695 := bstep (se 1 (by rfl) ⟨11345021, by rfl⟩ : syracuseStep 15126695 = 22690043) B22690043
theorem B6738815 : Blo 1048611 6738815 := bstep (se 1 (by rfl) ⟨5054111, by rfl⟩ : syracuseStep 6738815 = 10108223) B10108223
theorem B25583903 : Blo 1048611 25583903 := bstep (se 1 (by rfl) ⟨19187927, by rfl⟩ : syracuseStep 25583903 = 38375855) B38375855
theorem B17034407 : Blo 1048611 17034407 := bstep (se 1 (by rfl) ⟨12775805, by rfl⟩ : syracuseStep 17034407 = 25551611) B25551611
theorem B1797679 : Blo 1048611 1797679 := bstep (se 1 (by rfl) ⟨1348259, by rfl⟩ : syracuseStep 1797679 = 2696519) B2696519
theorem B1048647 : Blo 1048611 1048647 := bstep (se 1 (by rfl) ⟨786485, by rfl⟩ : syracuseStep 1048647 = 1572971) B1572971
theorem B6719183 : Blo 1048611 6719183 := bstep (se 1 (by rfl) ⟨5039387, by rfl⟩ : syracuseStep 6719183 = 10078775) B10078775
theorem B1575935 : Blo 1048611 1575935 := bstep (se 1 (by rfl) ⟨1181951, by rfl⟩ : syracuseStep 1575935 = 2363903) B2363903
theorem B51776747 : Blo 1048611 51776747 := bstep (se 1 (by rfl) ⟨38832560, by rfl⟩ : syracuseStep 51776747 = 77665121) B77665121
theorem B4492543 : Blo 1048611 4492543 := bstep (se 1 (by rfl) ⟨3369407, by rfl⟩ : syracuseStep 4492543 = 6738815) B6738815
theorem B17055935 : Blo 1048611 17055935 := bstep (se 1 (by rfl) ⟨12791951, by rfl⟩ : syracuseStep 17055935 = 25583903) B25583903
theorem B11356271 : Blo 1048611 11356271 := bstep (se 1 (by rfl) ⟨8517203, by rfl⟩ : syracuseStep 11356271 = 17034407) B17034407
theorem B9587621 : Blo 1048611 9587621 := bstep (se 4 (by rfl) ⟨898839, by rfl⟩ : syracuseStep 9587621 = 1797679) B1797679
theorem B27319913 : Blo 1048611 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B10084463 : Blo 1048611 10084463 := bstep (se 1 (by rfl) ⟨7563347, by rfl⟩ : syracuseStep 10084463 = 15126695) B15126695
theorem B1990975 : Blo 1048611 1990975 := bstep (se 1 (by rfl) ⟨1493231, by rfl⟩ : syracuseStep 1990975 = 2986463) B2986463
theorem B11986217 : Blo 1048611 11986217 := bstep (se 2 (by rfl) ⟨4494831, by rfl⟩ : syracuseStep 11986217 = 8989663) B8989663
theorem B1894153 : Blo 1048611 1894153 := bstep (se 2 (by rfl) ⟨710307, by rfl⟩ : syracuseStep 1894153 = 1420615) B1420615
theorem B11370623 : Blo 1048611 11370623 := bstep (se 1 (by rfl) ⟨8527967, by rfl⟩ : syracuseStep 11370623 = 17055935) B17055935
theorem B2654633 : Blo 1048611 2654633 := bstep (se 2 (by rfl) ⟨995487, by rfl⟩ : syracuseStep 2654633 = 1990975) B1990975
theorem B7570847 : Blo 1048611 7570847 := bstep (se 1 (by rfl) ⟨5678135, by rfl⟩ : syracuseStep 7570847 = 11356271) B11356271
theorem B6391747 : Blo 1048611 6391747 := bstep (se 1 (by rfl) ⟨4793810, by rfl⟩ : syracuseStep 6391747 = 9587621) B9587621
theorem B1050623 : Blo 1048611 1050623 := bstep (se 1 (by rfl) ⟨787967, by rfl⟩ : syracuseStep 1050623 = 1575935) B1575935
theorem B2525537 : Blo 1048611 2525537 := bstep (se 2 (by rfl) ⟨947076, by rfl⟩ : syracuseStep 2525537 = 1894153) B1894153
theorem B6722975 : Blo 1048611 6722975 := bstep (se 1 (by rfl) ⟨5042231, by rfl⟩ : syracuseStep 6722975 = 10084463) B10084463
theorem B34517831 : Blo 1048611 34517831 := bstep (se 1 (by rfl) ⟨25888373, by rfl⟩ : syracuseStep 34517831 = 51776747) B51776747
theorem B4479455 : Blo 1048611 4479455 := bstep (se 1 (by rfl) ⟨3359591, by rfl⟩ : syracuseStep 4479455 = 6719183) B6719183
theorem B5990057 : Blo 1048611 5990057 := bstep (se 2 (by rfl) ⟨2246271, by rfl⟩ : syracuseStep 5990057 = 4492543) B4492543
theorem B18213275 : Blo 1048611 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B7990811 : Blo 1048611 7990811 := bstep (se 1 (by rfl) ⟨5993108, by rfl⟩ : syracuseStep 7990811 = 11986217) B11986217
theorem B1769755 : Blo 1048611 1769755 := bstep (se 1 (by rfl) ⟨1327316, by rfl⟩ : syracuseStep 1769755 = 2654633) B2654633
theorem B5047231 : Blo 1048611 5047231 := bstep (se 1 (by rfl) ⟨3785423, by rfl⟩ : syracuseStep 5047231 = 7570847) B7570847
theorem B8522329 : Blo 1048611 8522329 := bstep (se 2 (by rfl) ⟨3195873, by rfl⟩ : syracuseStep 8522329 = 6391747) B6391747
theorem B2986303 : Blo 1048611 2986303 := bstep (se 1 (by rfl) ⟨2239727, by rfl⟩ : syracuseStep 2986303 = 4479455) B4479455
theorem B368190197 : Blo 1048611 368190197 := bstep (se 5 (by rfl) ⟨17258915, by rfl⟩ : syracuseStep 368190197 = 34517831) B34517831
theorem B30321661 : Blo 1048611 30321661 := bstep (se 3 (by rfl) ⟨5685311, by rfl⟩ : syracuseStep 30321661 = 11370623) B11370623
theorem B6734765 : Blo 1048611 6734765 := bstep (se 3 (by rfl) ⟨1262768, by rfl⟩ : syracuseStep 6734765 = 2525537) B2525537
theorem B12142183 : Blo 1048611 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B5327207 : Blo 1048611 5327207 := bstep (se 1 (by rfl) ⟨3995405, by rfl⟩ : syracuseStep 5327207 = 7990811) B7990811
theorem B4481983 : Blo 1048611 4481983 := bstep (se 1 (by rfl) ⟨3361487, by rfl⟩ : syracuseStep 4481983 = 6722975) B6722975
theorem B3993371 : Blo 1048611 3993371 := bstep (se 1 (by rfl) ⟨2995028, by rfl⟩ : syracuseStep 3993371 = 5990057) B5990057
theorem B2359673 : Blo 1048611 2359673 := bstep (se 2 (by rfl) ⟨884877, by rfl⟩ : syracuseStep 2359673 = 1769755) B1769755
theorem B4489843 : Blo 1048611 4489843 := bstep (se 1 (by rfl) ⟨3367382, by rfl⟩ : syracuseStep 4489843 = 6734765) B6734765
theorem B16189577 : Blo 1048611 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B2662247 : Blo 1048611 2662247 := bstep (se 1 (by rfl) ⟨1996685, by rfl⟩ : syracuseStep 2662247 = 3993371) B3993371
theorem B5975977 : Blo 1048611 5975977 := bstep (se 2 (by rfl) ⟨2240991, by rfl⟩ : syracuseStep 5975977 = 4481983) B4481983
theorem B6729641 : Blo 1048611 6729641 := bstep (se 2 (by rfl) ⟨2523615, by rfl⟩ : syracuseStep 6729641 = 5047231) B5047231
theorem B3551471 : Blo 1048611 3551471 := bstep (se 1 (by rfl) ⟨2663603, by rfl⟩ : syracuseStep 3551471 = 5327207) B5327207
theorem B3981737 : Blo 1048611 3981737 := bstep (se 2 (by rfl) ⟨1493151, by rfl⟩ : syracuseStep 3981737 = 2986303) B2986303
theorem B11363105 : Blo 1048611 11363105 := bstep (se 2 (by rfl) ⟨4261164, by rfl⟩ : syracuseStep 11363105 = 8522329) B8522329
theorem B40428881 : Blo 1048611 40428881 := bstep (se 2 (by rfl) ⟨15160830, by rfl⟩ : syracuseStep 40428881 = 30321661) B30321661
theorem B245460131 : Blo 1048611 245460131 := bstep (se 1 (by rfl) ⟨184095098, by rfl⟩ : syracuseStep 245460131 = 368190197) B368190197
theorem B1573115 : Blo 1048611 1573115 := bstep (se 1 (by rfl) ⟨1179836, by rfl⟩ : syracuseStep 1573115 = 2359673) B2359673
theorem B2654491 : Blo 1048611 2654491 := bstep (se 1 (by rfl) ⟨1990868, by rfl⟩ : syracuseStep 2654491 = 3981737) B3981737
theorem B7967969 : Blo 1048611 7967969 := bstep (se 2 (by rfl) ⟨2987988, by rfl⟩ : syracuseStep 7967969 = 5975977) B5975977
theorem B1774831 : Blo 1048611 1774831 := bstep (se 1 (by rfl) ⟨1331123, by rfl⟩ : syracuseStep 1774831 = 2662247) B2662247
theorem B7575403 : Blo 1048611 7575403 := bstep (se 1 (by rfl) ⟨5681552, by rfl⟩ : syracuseStep 7575403 = 11363105) B11363105
theorem B2367647 : Blo 1048611 2367647 := bstep (se 1 (by rfl) ⟨1775735, by rfl⟩ : syracuseStep 2367647 = 3551471) B3551471
theorem B10793051 : Blo 1048611 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B26952587 : Blo 1048611 26952587 := bstep (se 1 (by rfl) ⟨20214440, by rfl⟩ : syracuseStep 26952587 = 40428881) B40428881
theorem B5986457 : Blo 1048611 5986457 := bstep (se 2 (by rfl) ⟨2244921, by rfl⟩ : syracuseStep 5986457 = 4489843) B4489843
theorem B163640087 : Blo 1048611 163640087 := bstep (se 1 (by rfl) ⟨122730065, by rfl⟩ : syracuseStep 163640087 = 245460131) B245460131
theorem B4486427 : Blo 1048611 4486427 := bstep (se 1 (by rfl) ⟨3364820, by rfl⟩ : syracuseStep 4486427 = 6729641) B6729641
theorem B1048743 : Blo 1048611 1048743 := bstep (se 1 (by rfl) ⟨786557, by rfl⟩ : syracuseStep 1048743 = 1573115) B1573115
theorem B3539321 : Blo 1048611 3539321 := bstep (se 2 (by rfl) ⟨1327245, by rfl⟩ : syracuseStep 3539321 = 2654491) B2654491
theorem B5311979 : Blo 1048611 5311979 := bstep (se 1 (by rfl) ⟨3983984, by rfl⟩ : syracuseStep 5311979 = 7967969) B7967969
theorem B1578431 : Blo 1048611 1578431 := bstep (se 1 (by rfl) ⟨1183823, by rfl⟩ : syracuseStep 1578431 = 2367647) B2367647
theorem B2366441 : Blo 1048611 2366441 := bstep (se 2 (by rfl) ⟨887415, by rfl⟩ : syracuseStep 2366441 = 1774831) B1774831
theorem B10100537 : Blo 1048611 10100537 := bstep (se 2 (by rfl) ⟨3787701, by rfl⟩ : syracuseStep 10100537 = 7575403) B7575403
theorem B109093391 : Blo 1048611 109093391 := bstep (se 1 (by rfl) ⟨81820043, by rfl⟩ : syracuseStep 109093391 = 163640087) B163640087
theorem B2990951 : Blo 1048611 2990951 := bstep (se 1 (by rfl) ⟨2243213, by rfl⟩ : syracuseStep 2990951 = 4486427) B4486427
theorem B17968391 : Blo 1048611 17968391 := bstep (se 1 (by rfl) ⟨13476293, by rfl⟩ : syracuseStep 17968391 = 26952587) B26952587
theorem B7195367 : Blo 1048611 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B3990971 : Blo 1048611 3990971 := bstep (se 1 (by rfl) ⟨2993228, by rfl⟩ : syracuseStep 3990971 = 5986457) B5986457
theorem B2359547 : Blo 1048611 2359547 := bstep (se 1 (by rfl) ⟨1769660, by rfl⟩ : syracuseStep 2359547 = 3539321) B3539321
theorem B3541319 : Blo 1048611 3541319 := bstep (se 1 (by rfl) ⟨2655989, by rfl⟩ : syracuseStep 3541319 = 5311979) B5311979
theorem B1052287 : Blo 1048611 1052287 := bstep (se 1 (by rfl) ⟨789215, by rfl⟩ : syracuseStep 1052287 = 1578431) B1578431
theorem B1577627 : Blo 1048611 1577627 := bstep (se 1 (by rfl) ⟨1183220, by rfl⟩ : syracuseStep 1577627 = 2366441) B2366441
theorem B2660647 : Blo 1048611 2660647 := bstep (se 1 (by rfl) ⟨1995485, by rfl⟩ : syracuseStep 2660647 = 3990971) B3990971
theorem B4796911 : Blo 1048611 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B6733691 : Blo 1048611 6733691 := bstep (se 1 (by rfl) ⟨5050268, by rfl⟩ : syracuseStep 6733691 = 10100537) B10100537
theorem B72728927 : Blo 1048611 72728927 := bstep (se 1 (by rfl) ⟨54546695, by rfl⟩ : syracuseStep 72728927 = 109093391) B109093391
theorem B11978927 : Blo 1048611 11978927 := bstep (se 1 (by rfl) ⟨8984195, by rfl⟩ : syracuseStep 11978927 = 17968391) B17968391
theorem B1993967 : Blo 1048611 1993967 := bstep (se 1 (by rfl) ⟨1495475, by rfl⟩ : syracuseStep 1993967 = 2990951) B2990951
theorem B1573031 : Blo 1048611 1573031 := bstep (se 1 (by rfl) ⟨1179773, by rfl⟩ : syracuseStep 1573031 = 2359547) B2359547
theorem B2360879 : Blo 1048611 2360879 := bstep (se 1 (by rfl) ⟨1770659, by rfl⟩ : syracuseStep 2360879 = 3541319) B3541319
theorem B1051751 : Blo 1048611 1051751 := bstep (se 1 (by rfl) ⟨788813, by rfl⟩ : syracuseStep 1051751 = 1577627) B1577627
theorem B3547529 : Blo 1048611 3547529 := bstep (se 2 (by rfl) ⟨1330323, by rfl⟩ : syracuseStep 3547529 = 2660647) B2660647
theorem B1329311 : Blo 1048611 1329311 := bstep (se 1 (by rfl) ⟨996983, by rfl⟩ : syracuseStep 1329311 = 1993967) B1993967
theorem B48485951 : Blo 1048611 48485951 := bstep (se 1 (by rfl) ⟨36364463, by rfl⟩ : syracuseStep 48485951 = 72728927) B72728927
theorem B7985951 : Blo 1048611 7985951 := bstep (se 1 (by rfl) ⟨5989463, by rfl⟩ : syracuseStep 7985951 = 11978927) B11978927
theorem B25583525 : Blo 1048611 25583525 := bstep (se 4 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 25583525 = 4796911) B4796911
theorem B4489127 : Blo 1048611 4489127 := bstep (se 1 (by rfl) ⟨3366845, by rfl⟩ : syracuseStep 4489127 = 6733691) B6733691
theorem B1048687 : Blo 1048611 1048687 := bstep (se 1 (by rfl) ⟨786515, by rfl⟩ : syracuseStep 1048687 = 1573031) B1573031
theorem B1573919 : Blo 1048611 1573919 := bstep (se 1 (by rfl) ⟨1180439, by rfl⟩ : syracuseStep 1573919 = 2360879) B2360879
theorem B2365019 : Blo 1048611 2365019 := bstep (se 1 (by rfl) ⟨1773764, by rfl⟩ : syracuseStep 2365019 = 3547529) B3547529
theorem B3544829 : Blo 1048611 3544829 := bstep (se 3 (by rfl) ⟨664655, by rfl⟩ : syracuseStep 3544829 = 1329311) B1329311
theorem B2992751 : Blo 1048611 2992751 := bstep (se 1 (by rfl) ⟨2244563, by rfl⟩ : syracuseStep 2992751 = 4489127) B4489127
theorem B32323967 : Blo 1048611 32323967 := bstep (se 1 (by rfl) ⟨24242975, by rfl⟩ : syracuseStep 32323967 = 48485951) B48485951
theorem B5323967 : Blo 1048611 5323967 := bstep (se 1 (by rfl) ⟨3992975, by rfl⟩ : syracuseStep 5323967 = 7985951) B7985951
theorem B17055683 : Blo 1048611 17055683 := bstep (se 1 (by rfl) ⟨12791762, by rfl⟩ : syracuseStep 17055683 = 25583525) B25583525
theorem B1049279 : Blo 1048611 1049279 := bstep (se 1 (by rfl) ⟨786959, by rfl⟩ : syracuseStep 1049279 = 1573919) B1573919
theorem B1576679 : Blo 1048611 1576679 := bstep (se 1 (by rfl) ⟨1182509, by rfl⟩ : syracuseStep 1576679 = 2365019) B2365019
theorem B2363219 : Blo 1048611 2363219 := bstep (se 1 (by rfl) ⟨1772414, by rfl⟩ : syracuseStep 2363219 = 3544829) B3544829
theorem B3549311 : Blo 1048611 3549311 := bstep (se 1 (by rfl) ⟨2661983, by rfl⟩ : syracuseStep 3549311 = 5323967) B5323967
theorem B21549311 : Blo 1048611 21549311 := bstep (se 1 (by rfl) ⟨16161983, by rfl⟩ : syracuseStep 21549311 = 32323967) B32323967
theorem B1995167 : Blo 1048611 1995167 := bstep (se 1 (by rfl) ⟨1496375, by rfl⟩ : syracuseStep 1995167 = 2992751) B2992751
theorem B11370455 : Blo 1048611 11370455 := bstep (se 1 (by rfl) ⟨8527841, by rfl⟩ : syracuseStep 11370455 = 17055683) B17055683
theorem B1051119 : Blo 1048611 1051119 := bstep (se 1 (by rfl) ⟨788339, by rfl⟩ : syracuseStep 1051119 = 1576679) B1576679
theorem B1575479 : Blo 1048611 1575479 := bstep (se 1 (by rfl) ⟨1181609, by rfl⟩ : syracuseStep 1575479 = 2363219) B2363219
theorem B2366207 : Blo 1048611 2366207 := bstep (se 1 (by rfl) ⟨1774655, by rfl⟩ : syracuseStep 2366207 = 3549311) B3549311
theorem B7580303 : Blo 1048611 7580303 := bstep (se 1 (by rfl) ⟨5685227, by rfl⟩ : syracuseStep 7580303 = 11370455) B11370455
theorem B14366207 : Blo 1048611 14366207 := bstep (se 1 (by rfl) ⟨10774655, by rfl⟩ : syracuseStep 14366207 = 21549311) B21549311
theorem B1330111 : Blo 1048611 1330111 := bstep (se 1 (by rfl) ⟨997583, by rfl⟩ : syracuseStep 1330111 = 1995167) B1995167
theorem B1050319 : Blo 1048611 1050319 := bstep (se 1 (by rfl) ⟨787739, by rfl⟩ : syracuseStep 1050319 = 1575479) B1575479
theorem B1773481 : Blo 1048611 1773481 := bstep (se 2 (by rfl) ⟨665055, by rfl⟩ : syracuseStep 1773481 = 1330111) B1330111
theorem B38309885 : Blo 1048611 38309885 := bstep (se 3 (by rfl) ⟨7183103, by rfl⟩ : syracuseStep 38309885 = 14366207) B14366207
theorem B1577471 : Blo 1048611 1577471 := bstep (se 1 (by rfl) ⟨1183103, by rfl⟩ : syracuseStep 1577471 = 2366207) B2366207
theorem B5053535 : Blo 1048611 5053535 := bstep (se 1 (by rfl) ⟨3790151, by rfl⟩ : syracuseStep 5053535 = 7580303) B7580303
theorem B1051647 : Blo 1048611 1051647 := bstep (se 1 (by rfl) ⟨788735, by rfl⟩ : syracuseStep 1051647 = 1577471) B1577471
theorem B2364641 : Blo 1048611 2364641 := bstep (se 2 (by rfl) ⟨886740, by rfl⟩ : syracuseStep 2364641 = 1773481) B1773481
theorem B25539923 : Blo 1048611 25539923 := bstep (se 1 (by rfl) ⟨19154942, by rfl⟩ : syracuseStep 25539923 = 38309885) B38309885
theorem B3369023 : Blo 1048611 3369023 := bstep (se 1 (by rfl) ⟨2526767, by rfl⟩ : syracuseStep 3369023 = 5053535) B5053535
theorem B1576427 : Blo 1048611 1576427 := bstep (se 1 (by rfl) ⟨1182320, by rfl⟩ : syracuseStep 1576427 = 2364641) B2364641
theorem B2246015 : Blo 1048611 2246015 := bstep (se 1 (by rfl) ⟨1684511, by rfl⟩ : syracuseStep 2246015 = 3369023) B3369023
theorem B17026615 : Blo 1048611 17026615 := bstep (se 1 (by rfl) ⟨12769961, by rfl⟩ : syracuseStep 17026615 = 25539923) B25539923
theorem B1050951 : Blo 1048611 1050951 := bstep (se 1 (by rfl) ⟨788213, by rfl⟩ : syracuseStep 1050951 = 1576427) B1576427
theorem B5989373 : Blo 1048611 5989373 := bstep (se 3 (by rfl) ⟨1123007, by rfl⟩ : syracuseStep 5989373 = 2246015) B2246015
theorem B22702153 : Blo 1048611 22702153 := bstep (se 2 (by rfl) ⟨8513307, by rfl⟩ : syracuseStep 22702153 = 17026615) B17026615
theorem B30269537 : Blo 1048611 30269537 := bstep (se 2 (by rfl) ⟨11351076, by rfl⟩ : syracuseStep 30269537 = 22702153) B22702153
theorem B3992915 : Blo 1048611 3992915 := bstep (se 1 (by rfl) ⟨2994686, by rfl⟩ : syracuseStep 3992915 = 5989373) B5989373
theorem B2661943 : Blo 1048611 2661943 := bstep (se 1 (by rfl) ⟨1996457, by rfl⟩ : syracuseStep 2661943 = 3992915) B3992915
theorem B20179691 : Blo 1048611 20179691 := bstep (se 1 (by rfl) ⟨15134768, by rfl⟩ : syracuseStep 20179691 = 30269537) B30269537
theorem B3549257 : Blo 1048611 3549257 := bstep (se 2 (by rfl) ⟨1330971, by rfl⟩ : syracuseStep 3549257 = 2661943) B2661943
theorem B13453127 : Blo 1048611 13453127 := bstep (se 1 (by rfl) ⟨10089845, by rfl⟩ : syracuseStep 13453127 = 20179691) B20179691
theorem B2366171 : Blo 1048611 2366171 := bstep (se 1 (by rfl) ⟨1774628, by rfl⟩ : syracuseStep 2366171 = 3549257) B3549257
theorem B8968751 : Blo 1048611 8968751 := bstep (se 1 (by rfl) ⟨6726563, by rfl⟩ : syracuseStep 8968751 = 13453127) B13453127
theorem B1577447 : Blo 1048611 1577447 := bstep (se 1 (by rfl) ⟨1183085, by rfl⟩ : syracuseStep 1577447 = 2366171) B2366171
theorem B5979167 : Blo 1048611 5979167 := bstep (se 1 (by rfl) ⟨4484375, by rfl⟩ : syracuseStep 5979167 = 8968751) B8968751
theorem B1051631 : Blo 1048611 1051631 := bstep (se 1 (by rfl) ⟨788723, by rfl⟩ : syracuseStep 1051631 = 1577447) B1577447
theorem B3986111 : Blo 1048611 3986111 := bstep (se 1 (by rfl) ⟨2989583, by rfl⟩ : syracuseStep 3986111 = 5979167) B5979167
theorem B2657407 : Blo 1048611 2657407 := bstep (se 1 (by rfl) ⟨1993055, by rfl⟩ : syracuseStep 2657407 = 3986111) B3986111
theorem B3543209 : Blo 1048611 3543209 := bstep (se 2 (by rfl) ⟨1328703, by rfl⟩ : syracuseStep 3543209 = 2657407) B2657407
theorem B2362139 : Blo 1048611 2362139 := bstep (se 1 (by rfl) ⟨1771604, by rfl⟩ : syracuseStep 2362139 = 3543209) B3543209
theorem B1574759 : Blo 1048611 1574759 := bstep (se 1 (by rfl) ⟨1181069, by rfl⟩ : syracuseStep 1574759 = 2362139) B2362139
theorem B1049839 : Blo 1048611 1049839 := bstep (se 1 (by rfl) ⟨787379, by rfl⟩ : syracuseStep 1049839 = 1574759) B1574759

theorem C0 (j : ℕ) (h1 : 262152 ≤ j) (h2 : j ≤ 262851) : Blo 1048611 (4 * j + 3) := by
  interval_cases j
  · exact B1048611
  · exact B1048615
  · exact B1048619
  · exact B1048623
  · exact B1048627
  · exact B1048631
  · exact B1048635
  · exact B1048639
  · exact B1048643
  · exact B1048647
  · exact B1048651
  · exact B1048655
  · exact B1048659
  · exact B1048663
  · exact B1048667
  · exact B1048671
  · exact B1048675
  · exact B1048679
  · exact B1048683
  · exact B1048687
  · exact B1048691
  · exact B1048695
  · exact B1048699
  · exact B1048703
  · exact B1048707
  · exact B1048711
  · exact B1048715
  · exact B1048719
  · exact B1048723
  · exact B1048727
  · exact B1048731
  · exact B1048735
  · exact B1048739
  · exact B1048743
  · exact B1048747
  · exact B1048751
  · exact B1048755
  · exact B1048759
  · exact B1048763
  · exact B1048767
  · exact B1048771
  · exact B1048775
  · exact B1048779
  · exact B1048783
  · exact B1048787
  · exact B1048791
  · exact B1048795
  · exact B1048799
  · exact B1048803
  · exact B1048807
  · exact B1048811
  · exact B1048815
  · exact B1048819
  · exact B1048823
  · exact B1048827
  · exact B1048831
  · exact B1048835
  · exact B1048839
  · exact B1048843
  · exact B1048847
  · exact B1048851
  · exact B1048855
  · exact B1048859
  · exact B1048863
  · exact B1048867
  · exact B1048871
  · exact B1048875
  · exact B1048879
  · exact B1048883
  · exact B1048887
  · exact B1048891
  · exact B1048895
  · exact B1048899
  · exact B1048903
  · exact B1048907
  · exact B1048911
  · exact B1048915
  · exact B1048919
  · exact B1048923
  · exact B1048927
  · exact B1048931
  · exact B1048935
  · exact B1048939
  · exact B1048943
  · exact B1048947
  · exact B1048951
  · exact B1048955
  · exact B1048959
  · exact B1048963
  · exact B1048967
  · exact B1048971
  · exact B1048975
  · exact B1048979
  · exact B1048983
  · exact B1048987
  · exact B1048991
  · exact B1048995
  · exact B1048999
  · exact B1049003
  · exact B1049007
  · exact B1049011
  · exact B1049015
  · exact B1049019
  · exact B1049023
  · exact B1049027
  · exact B1049031
  · exact B1049035
  · exact B1049039
  · exact B1049043
  · exact B1049047
  · exact B1049051
  · exact B1049055
  · exact B1049059
  · exact B1049063
  · exact B1049067
  · exact B1049071
  · exact B1049075
  · exact B1049079
  · exact B1049083
  · exact B1049087
  · exact B1049091
  · exact B1049095
  · exact B1049099
  · exact B1049103
  · exact B1049107
  · exact B1049111
  · exact B1049115
  · exact B1049119
  · exact B1049123
  · exact B1049127
  · exact B1049131
  · exact B1049135
  · exact B1049139
  · exact B1049143
  · exact B1049147
  · exact B1049151
  · exact B1049155
  · exact B1049159
  · exact B1049163
  · exact B1049167
  · exact B1049171
  · exact B1049175
  · exact B1049179
  · exact B1049183
  · exact B1049187
  · exact B1049191
  · exact B1049195
  · exact B1049199
  · exact B1049203
  · exact B1049207
  · exact B1049211
  · exact B1049215
  · exact B1049219
  · exact B1049223
  · exact B1049227
  · exact B1049231
  · exact B1049235
  · exact B1049239
  · exact B1049243
  · exact B1049247
  · exact B1049251
  · exact B1049255
  · exact B1049259
  · exact B1049263
  · exact B1049267
  · exact B1049271
  · exact B1049275
  · exact B1049279
  · exact B1049283
  · exact B1049287
  · exact B1049291
  · exact B1049295
  · exact B1049299
  · exact B1049303
  · exact B1049307
  · exact B1049311
  · exact B1049315
  · exact B1049319
  · exact B1049323
  · exact B1049327
  · exact B1049331
  · exact B1049335
  · exact B1049339
  · exact B1049343
  · exact B1049347
  · exact B1049351
  · exact B1049355
  · exact B1049359
  · exact B1049363
  · exact B1049367
  · exact B1049371
  · exact B1049375
  · exact B1049379
  · exact B1049383
  · exact B1049387
  · exact B1049391
  · exact B1049395
  · exact B1049399
  · exact B1049403
  · exact B1049407
  · exact B1049411
  · exact B1049415
  · exact B1049419
  · exact B1049423
  · exact B1049427
  · exact B1049431
  · exact B1049435
  · exact B1049439
  · exact B1049443
  · exact B1049447
  · exact B1049451
  · exact B1049455
  · exact B1049459
  · exact B1049463
  · exact B1049467
  · exact B1049471
  · exact B1049475
  · exact B1049479
  · exact B1049483
  · exact B1049487
  · exact B1049491
  · exact B1049495
  · exact B1049499
  · exact B1049503
  · exact B1049507
  · exact B1049511
  · exact B1049515
  · exact B1049519
  · exact B1049523
  · exact B1049527
  · exact B1049531
  · exact B1049535
  · exact B1049539
  · exact B1049543
  · exact B1049547
  · exact B1049551
  · exact B1049555
  · exact B1049559
  · exact B1049563
  · exact B1049567
  · exact B1049571
  · exact B1049575
  · exact B1049579
  · exact B1049583
  · exact B1049587
  · exact B1049591
  · exact B1049595
  · exact B1049599
  · exact B1049603
  · exact B1049607
  · exact B1049611
  · exact B1049615
  · exact B1049619
  · exact B1049623
  · exact B1049627
  · exact B1049631
  · exact B1049635
  · exact B1049639
  · exact B1049643
  · exact B1049647
  · exact B1049651
  · exact B1049655
  · exact B1049659
  · exact B1049663
  · exact B1049667
  · exact B1049671
  · exact B1049675
  · exact B1049679
  · exact B1049683
  · exact B1049687
  · exact B1049691
  · exact B1049695
  · exact B1049699
  · exact B1049703
  · exact B1049707
  · exact B1049711
  · exact B1049715
  · exact B1049719
  · exact B1049723
  · exact B1049727
  · exact B1049731
  · exact B1049735
  · exact B1049739
  · exact B1049743
  · exact B1049747
  · exact B1049751
  · exact B1049755
  · exact B1049759
  · exact B1049763
  · exact B1049767
  · exact B1049771
  · exact B1049775
  · exact B1049779
  · exact B1049783
  · exact B1049787
  · exact B1049791
  · exact B1049795
  · exact B1049799
  · exact B1049803
  · exact B1049807
  · exact B1049811
  · exact B1049815
  · exact B1049819
  · exact B1049823
  · exact B1049827
  · exact B1049831
  · exact B1049835
  · exact B1049839
  · exact B1049843
  · exact B1049847
  · exact B1049851
  · exact B1049855
  · exact B1049859
  · exact B1049863
  · exact B1049867
  · exact B1049871
  · exact B1049875
  · exact B1049879
  · exact B1049883
  · exact B1049887
  · exact B1049891
  · exact B1049895
  · exact B1049899
  · exact B1049903
  · exact B1049907
  · exact B1049911
  · exact B1049915
  · exact B1049919
  · exact B1049923
  · exact B1049927
  · exact B1049931
  · exact B1049935
  · exact B1049939
  · exact B1049943
  · exact B1049947
  · exact B1049951
  · exact B1049955
  · exact B1049959
  · exact B1049963
  · exact B1049967
  · exact B1049971
  · exact B1049975
  · exact B1049979
  · exact B1049983
  · exact B1049987
  · exact B1049991
  · exact B1049995
  · exact B1049999
  · exact B1050003
  · exact B1050007
  · exact B1050011
  · exact B1050015
  · exact B1050019
  · exact B1050023
  · exact B1050027
  · exact B1050031
  · exact B1050035
  · exact B1050039
  · exact B1050043
  · exact B1050047
  · exact B1050051
  · exact B1050055
  · exact B1050059
  · exact B1050063
  · exact B1050067
  · exact B1050071
  · exact B1050075
  · exact B1050079
  · exact B1050083
  · exact B1050087
  · exact B1050091
  · exact B1050095
  · exact B1050099
  · exact B1050103
  · exact B1050107
  · exact B1050111
  · exact B1050115
  · exact B1050119
  · exact B1050123
  · exact B1050127
  · exact B1050131
  · exact B1050135
  · exact B1050139
  · exact B1050143
  · exact B1050147
  · exact B1050151
  · exact B1050155
  · exact B1050159
  · exact B1050163
  · exact B1050167
  · exact B1050171
  · exact B1050175
  · exact B1050179
  · exact B1050183
  · exact B1050187
  · exact B1050191
  · exact B1050195
  · exact B1050199
  · exact B1050203
  · exact B1050207
  · exact B1050211
  · exact B1050215
  · exact B1050219
  · exact B1050223
  · exact B1050227
  · exact B1050231
  · exact B1050235
  · exact B1050239
  · exact B1050243
  · exact B1050247
  · exact B1050251
  · exact B1050255
  · exact B1050259
  · exact B1050263
  · exact B1050267
  · exact B1050271
  · exact B1050275
  · exact B1050279
  · exact B1050283
  · exact B1050287
  · exact B1050291
  · exact B1050295
  · exact B1050299
  · exact B1050303
  · exact B1050307
  · exact B1050311
  · exact B1050315
  · exact B1050319
  · exact B1050323
  · exact B1050327
  · exact B1050331
  · exact B1050335
  · exact B1050339
  · exact B1050343
  · exact B1050347
  · exact B1050351
  · exact B1050355
  · exact B1050359
  · exact B1050363
  · exact B1050367
  · exact B1050371
  · exact B1050375
  · exact B1050379
  · exact B1050383
  · exact B1050387
  · exact B1050391
  · exact B1050395
  · exact B1050399
  · exact B1050403
  · exact B1050407
  · exact B1050411
  · exact B1050415
  · exact B1050419
  · exact B1050423
  · exact B1050427
  · exact B1050431
  · exact B1050435
  · exact B1050439
  · exact B1050443
  · exact B1050447
  · exact B1050451
  · exact B1050455
  · exact B1050459
  · exact B1050463
  · exact B1050467
  · exact B1050471
  · exact B1050475
  · exact B1050479
  · exact B1050483
  · exact B1050487
  · exact B1050491
  · exact B1050495
  · exact B1050499
  · exact B1050503
  · exact B1050507
  · exact B1050511
  · exact B1050515
  · exact B1050519
  · exact B1050523
  · exact B1050527
  · exact B1050531
  · exact B1050535
  · exact B1050539
  · exact B1050543
  · exact B1050547
  · exact B1050551
  · exact B1050555
  · exact B1050559
  · exact B1050563
  · exact B1050567
  · exact B1050571
  · exact B1050575
  · exact B1050579
  · exact B1050583
  · exact B1050587
  · exact B1050591
  · exact B1050595
  · exact B1050599
  · exact B1050603
  · exact B1050607
  · exact B1050611
  · exact B1050615
  · exact B1050619
  · exact B1050623
  · exact B1050627
  · exact B1050631
  · exact B1050635
  · exact B1050639
  · exact B1050643
  · exact B1050647
  · exact B1050651
  · exact B1050655
  · exact B1050659
  · exact B1050663
  · exact B1050667
  · exact B1050671
  · exact B1050675
  · exact B1050679
  · exact B1050683
  · exact B1050687
  · exact B1050691
  · exact B1050695
  · exact B1050699
  · exact B1050703
  · exact B1050707
  · exact B1050711
  · exact B1050715
  · exact B1050719
  · exact B1050723
  · exact B1050727
  · exact B1050731
  · exact B1050735
  · exact B1050739
  · exact B1050743
  · exact B1050747
  · exact B1050751
  · exact B1050755
  · exact B1050759
  · exact B1050763
  · exact B1050767
  · exact B1050771
  · exact B1050775
  · exact B1050779
  · exact B1050783
  · exact B1050787
  · exact B1050791
  · exact B1050795
  · exact B1050799
  · exact B1050803
  · exact B1050807
  · exact B1050811
  · exact B1050815
  · exact B1050819
  · exact B1050823
  · exact B1050827
  · exact B1050831
  · exact B1050835
  · exact B1050839
  · exact B1050843
  · exact B1050847
  · exact B1050851
  · exact B1050855
  · exact B1050859
  · exact B1050863
  · exact B1050867
  · exact B1050871
  · exact B1050875
  · exact B1050879
  · exact B1050883
  · exact B1050887
  · exact B1050891
  · exact B1050895
  · exact B1050899
  · exact B1050903
  · exact B1050907
  · exact B1050911
  · exact B1050915
  · exact B1050919
  · exact B1050923
  · exact B1050927
  · exact B1050931
  · exact B1050935
  · exact B1050939
  · exact B1050943
  · exact B1050947
  · exact B1050951
  · exact B1050955
  · exact B1050959
  · exact B1050963
  · exact B1050967
  · exact B1050971
  · exact B1050975
  · exact B1050979
  · exact B1050983
  · exact B1050987
  · exact B1050991
  · exact B1050995
  · exact B1050999
  · exact B1051003
  · exact B1051007
  · exact B1051011
  · exact B1051015
  · exact B1051019
  · exact B1051023
  · exact B1051027
  · exact B1051031
  · exact B1051035
  · exact B1051039
  · exact B1051043
  · exact B1051047
  · exact B1051051
  · exact B1051055
  · exact B1051059
  · exact B1051063
  · exact B1051067
  · exact B1051071
  · exact B1051075
  · exact B1051079
  · exact B1051083
  · exact B1051087
  · exact B1051091
  · exact B1051095
  · exact B1051099
  · exact B1051103
  · exact B1051107
  · exact B1051111
  · exact B1051115
  · exact B1051119
  · exact B1051123
  · exact B1051127
  · exact B1051131
  · exact B1051135
  · exact B1051139
  · exact B1051143
  · exact B1051147
  · exact B1051151
  · exact B1051155
  · exact B1051159
  · exact B1051163
  · exact B1051167
  · exact B1051171
  · exact B1051175
  · exact B1051179
  · exact B1051183
  · exact B1051187
  · exact B1051191
  · exact B1051195
  · exact B1051199
  · exact B1051203
  · exact B1051207
  · exact B1051211
  · exact B1051215
  · exact B1051219
  · exact B1051223
  · exact B1051227
  · exact B1051231
  · exact B1051235
  · exact B1051239
  · exact B1051243
  · exact B1051247
  · exact B1051251
  · exact B1051255
  · exact B1051259
  · exact B1051263
  · exact B1051267
  · exact B1051271
  · exact B1051275
  · exact B1051279
  · exact B1051283
  · exact B1051287
  · exact B1051291
  · exact B1051295
  · exact B1051299
  · exact B1051303
  · exact B1051307
  · exact B1051311
  · exact B1051315
  · exact B1051319
  · exact B1051323
  · exact B1051327
  · exact B1051331
  · exact B1051335
  · exact B1051339
  · exact B1051343
  · exact B1051347
  · exact B1051351
  · exact B1051355
  · exact B1051359
  · exact B1051363
  · exact B1051367
  · exact B1051371
  · exact B1051375
  · exact B1051379
  · exact B1051383
  · exact B1051387
  · exact B1051391
  · exact B1051395
  · exact B1051399
  · exact B1051403
  · exact B1051407

theorem C1 (j : ℕ) (h1 : 262852 ≤ j) (h2 : j ≤ 263152) : Blo 1048611 (4 * j + 3) := by
  interval_cases j
  · exact B1051411
  · exact B1051415
  · exact B1051419
  · exact B1051423
  · exact B1051427
  · exact B1051431
  · exact B1051435
  · exact B1051439
  · exact B1051443
  · exact B1051447
  · exact B1051451
  · exact B1051455
  · exact B1051459
  · exact B1051463
  · exact B1051467
  · exact B1051471
  · exact B1051475
  · exact B1051479
  · exact B1051483
  · exact B1051487
  · exact B1051491
  · exact B1051495
  · exact B1051499
  · exact B1051503
  · exact B1051507
  · exact B1051511
  · exact B1051515
  · exact B1051519
  · exact B1051523
  · exact B1051527
  · exact B1051531
  · exact B1051535
  · exact B1051539
  · exact B1051543
  · exact B1051547
  · exact B1051551
  · exact B1051555
  · exact B1051559
  · exact B1051563
  · exact B1051567
  · exact B1051571
  · exact B1051575
  · exact B1051579
  · exact B1051583
  · exact B1051587
  · exact B1051591
  · exact B1051595
  · exact B1051599
  · exact B1051603
  · exact B1051607
  · exact B1051611
  · exact B1051615
  · exact B1051619
  · exact B1051623
  · exact B1051627
  · exact B1051631
  · exact B1051635
  · exact B1051639
  · exact B1051643
  · exact B1051647
  · exact B1051651
  · exact B1051655
  · exact B1051659
  · exact B1051663
  · exact B1051667
  · exact B1051671
  · exact B1051675
  · exact B1051679
  · exact B1051683
  · exact B1051687
  · exact B1051691
  · exact B1051695
  · exact B1051699
  · exact B1051703
  · exact B1051707
  · exact B1051711
  · exact B1051715
  · exact B1051719
  · exact B1051723
  · exact B1051727
  · exact B1051731
  · exact B1051735
  · exact B1051739
  · exact B1051743
  · exact B1051747
  · exact B1051751
  · exact B1051755
  · exact B1051759
  · exact B1051763
  · exact B1051767
  · exact B1051771
  · exact B1051775
  · exact B1051779
  · exact B1051783
  · exact B1051787
  · exact B1051791
  · exact B1051795
  · exact B1051799
  · exact B1051803
  · exact B1051807
  · exact B1051811
  · exact B1051815
  · exact B1051819
  · exact B1051823
  · exact B1051827
  · exact B1051831
  · exact B1051835
  · exact B1051839
  · exact B1051843
  · exact B1051847
  · exact B1051851
  · exact B1051855
  · exact B1051859
  · exact B1051863
  · exact B1051867
  · exact B1051871
  · exact B1051875
  · exact B1051879
  · exact B1051883
  · exact B1051887
  · exact B1051891
  · exact B1051895
  · exact B1051899
  · exact B1051903
  · exact B1051907
  · exact B1051911
  · exact B1051915
  · exact B1051919
  · exact B1051923
  · exact B1051927
  · exact B1051931
  · exact B1051935
  · exact B1051939
  · exact B1051943
  · exact B1051947
  · exact B1051951
  · exact B1051955
  · exact B1051959
  · exact B1051963
  · exact B1051967
  · exact B1051971
  · exact B1051975
  · exact B1051979
  · exact B1051983
  · exact B1051987
  · exact B1051991
  · exact B1051995
  · exact B1051999
  · exact B1052003
  · exact B1052007
  · exact B1052011
  · exact B1052015
  · exact B1052019
  · exact B1052023
  · exact B1052027
  · exact B1052031
  · exact B1052035
  · exact B1052039
  · exact B1052043
  · exact B1052047
  · exact B1052051
  · exact B1052055
  · exact B1052059
  · exact B1052063
  · exact B1052067
  · exact B1052071
  · exact B1052075
  · exact B1052079
  · exact B1052083
  · exact B1052087
  · exact B1052091
  · exact B1052095
  · exact B1052099
  · exact B1052103
  · exact B1052107
  · exact B1052111
  · exact B1052115
  · exact B1052119
  · exact B1052123
  · exact B1052127
  · exact B1052131
  · exact B1052135
  · exact B1052139
  · exact B1052143
  · exact B1052147
  · exact B1052151
  · exact B1052155
  · exact B1052159
  · exact B1052163
  · exact B1052167
  · exact B1052171
  · exact B1052175
  · exact B1052179
  · exact B1052183
  · exact B1052187
  · exact B1052191
  · exact B1052195
  · exact B1052199
  · exact B1052203
  · exact B1052207
  · exact B1052211
  · exact B1052215
  · exact B1052219
  · exact B1052223
  · exact B1052227
  · exact B1052231
  · exact B1052235
  · exact B1052239
  · exact B1052243
  · exact B1052247
  · exact B1052251
  · exact B1052255
  · exact B1052259
  · exact B1052263
  · exact B1052267
  · exact B1052271
  · exact B1052275
  · exact B1052279
  · exact B1052283
  · exact B1052287
  · exact B1052291
  · exact B1052295
  · exact B1052299
  · exact B1052303
  · exact B1052307
  · exact B1052311
  · exact B1052315
  · exact B1052319
  · exact B1052323
  · exact B1052327
  · exact B1052331
  · exact B1052335
  · exact B1052339
  · exact B1052343
  · exact B1052347
  · exact B1052351
  · exact B1052355
  · exact B1052359
  · exact B1052363
  · exact B1052367
  · exact B1052371
  · exact B1052375
  · exact B1052379
  · exact B1052383
  · exact B1052387
  · exact B1052391
  · exact B1052395
  · exact B1052399
  · exact B1052403
  · exact B1052407
  · exact B1052411
  · exact B1052415
  · exact B1052419
  · exact B1052423
  · exact B1052427
  · exact B1052431
  · exact B1052435
  · exact B1052439
  · exact B1052443
  · exact B1052447
  · exact B1052451
  · exact B1052455
  · exact B1052459
  · exact B1052463
  · exact B1052467
  · exact B1052471
  · exact B1052475
  · exact B1052479
  · exact B1052483
  · exact B1052487
  · exact B1052491
  · exact B1052495
  · exact B1052499
  · exact B1052503
  · exact B1052507
  · exact B1052511
  · exact B1052515
  · exact B1052519
  · exact B1052523
  · exact B1052527
  · exact B1052531
  · exact B1052535
  · exact B1052539
  · exact B1052543
  · exact B1052547
  · exact B1052551
  · exact B1052555
  · exact B1052559
  · exact B1052563
  · exact B1052567
  · exact B1052571
  · exact B1052575
  · exact B1052579
  · exact B1052583
  · exact B1052587
  · exact B1052591
  · exact B1052595
  · exact B1052599
  · exact B1052603
  · exact B1052607
  · exact B1052611

theorem solution (m : ℕ) (hlo : 1048611 ≤ m) (hhi : m ≤ 1052611) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 262152 ≤ j := by omega
    have hj2 : j ≤ 263152 := by omega
    have hb : Blo 1048611 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 262852 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
