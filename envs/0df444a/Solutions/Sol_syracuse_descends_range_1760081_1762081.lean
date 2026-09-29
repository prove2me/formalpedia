-- Prove2me | solution 1 for syracuse_descends_range_1760081_1762081
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:39:01.818909+00:00
-- url     : https://prove2.me/submissions/46d78f01-c942-4023-85b4-9d4d591ce0b6

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


theorem B4759573 : Blo 1760081 4759573 := bbase (se 6 (by rfl) ⟨111552, by rfl⟩ : syracuseStep 4759573 = 223105) (by norm_num)
theorem B2228249 : Blo 1760081 2228249 := bbase (se 2 (by rfl) ⟨835593, by rfl⟩ : syracuseStep 2228249 = 1671187) (by norm_num)
theorem B7520309 : Blo 1760081 7520309 := bbase (se 5 (by rfl) ⟨352514, by rfl⟩ : syracuseStep 7520309 = 705029) (by norm_num)
theorem B3342397 : Blo 1760081 3342397 := bbase (se 3 (by rfl) ⟨626699, by rfl⟩ : syracuseStep 3342397 = 1253399) (by norm_num)
theorem B2228305 : Blo 1760081 2228305 := bbase (se 2 (by rfl) ⟨835614, by rfl⟩ : syracuseStep 2228305 = 1671229) (by norm_num)
theorem B30097493 : Blo 1760081 30097493 := bbase (se 8 (by rfl) ⟨176352, by rfl⟩ : syracuseStep 30097493 = 352705) (by norm_num)
theorem B2228401 : Blo 1760081 2228401 := bbase (se 2 (by rfl) ⟨835650, by rfl⟩ : syracuseStep 2228401 = 1671301) (by norm_num)
theorem B8913077 : Blo 1760081 8913077 := bbase (se 5 (by rfl) ⟨417800, by rfl⟩ : syracuseStep 8913077 = 835601) (by norm_num)
theorem B6684869 : Blo 1760081 6684869 := bbase (se 4 (by rfl) ⟨626706, by rfl⟩ : syracuseStep 6684869 = 1253413) (by norm_num)
theorem B3342541 : Blo 1760081 3342541 := bbase (se 3 (by rfl) ⟨626726, by rfl⟩ : syracuseStep 3342541 = 1253453) (by norm_num)
theorem B2859229 : Blo 1760081 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B2506997 : Blo 1760081 2506997 := bbase (se 5 (by rfl) ⟨117515, by rfl⟩ : syracuseStep 2506997 = 235031) (by norm_num)
theorem B4456741 : Blo 1760081 4456741 := bbase (se 4 (by rfl) ⟨417819, by rfl⟩ : syracuseStep 4456741 = 835639) (by norm_num)
theorem B3760445 : Blo 1760081 3760445 := bbase (se 3 (by rfl) ⟨705083, by rfl⟩ : syracuseStep 3760445 = 1410167) (by norm_num)
theorem B5644613 : Blo 1760081 5644613 := bbase (se 4 (by rfl) ⟨529182, by rfl⟩ : syracuseStep 5644613 = 1058365) (by norm_num)
theorem B2228573 : Blo 1760081 2228573 := bbase (se 3 (by rfl) ⟨417857, by rfl⟩ : syracuseStep 2228573 = 835715) (by norm_num)
theorem B3342701 : Blo 1760081 3342701 := bbase (se 3 (by rfl) ⟨626756, by rfl⟩ : syracuseStep 3342701 = 1253513) (by norm_num)
theorem B4456853 : Blo 1760081 4456853 := bbase (se 6 (by rfl) ⟨104457, by rfl⟩ : syracuseStep 4456853 = 208915) (by norm_num)
theorem B2228629 : Blo 1760081 2228629 := bbase (se 6 (by rfl) ⟨52233, by rfl⟩ : syracuseStep 2228629 = 104467) (by norm_num)
theorem B8249813 : Blo 1760081 8249813 := bbase (se 7 (by rfl) ⟨96677, by rfl⟩ : syracuseStep 8249813 = 193355) (by norm_num)
theorem B2228725 : Blo 1760081 2228725 := bbase (se 5 (by rfl) ⟨104471, by rfl⟩ : syracuseStep 2228725 = 208943) (by norm_num)
theorem B3342845 : Blo 1760081 3342845 := bbase (se 3 (by rfl) ⟨626783, by rfl⟩ : syracuseStep 3342845 = 1253567) (by norm_num)
theorem B4457045 : Blo 1760081 4457045 := bbase (se 8 (by rfl) ⟨26115, by rfl⟩ : syracuseStep 4457045 = 52231) (by norm_num)
theorem B2228897 : Blo 1760081 2228897 := bbase (se 2 (by rfl) ⟨835836, by rfl⟩ : syracuseStep 2228897 = 1671673) (by norm_num)
theorem B2228953 : Blo 1760081 2228953 := bbase (se 2 (by rfl) ⟨835857, by rfl⟩ : syracuseStep 2228953 = 1671715) (by norm_num)
theorem B4760309 : Blo 1760081 4760309 := bbase (se 5 (by rfl) ⟨223139, by rfl⟩ : syracuseStep 4760309 = 446279) (by norm_num)
theorem B3343133 : Blo 1760081 3343133 := bbase (se 3 (by rfl) ⟨626837, by rfl⟩ : syracuseStep 3343133 = 1253675) (by norm_num)
theorem B5014325 : Blo 1760081 5014325 := bbase (se 5 (by rfl) ⟨235046, by rfl⟩ : syracuseStep 5014325 = 470093) (by norm_num)
theorem B2229049 : Blo 1760081 2229049 := bbase (se 2 (by rfl) ⟨835893, by rfl⟩ : syracuseStep 2229049 = 1671787) (by norm_num)
theorem B4457389 : Blo 1760081 4457389 := bbase (se 3 (by rfl) ⟨835760, by rfl⟩ : syracuseStep 4457389 = 1671521) (by norm_num)
theorem B3343285 : Blo 1760081 3343285 := bbase (se 5 (by rfl) ⟨156716, by rfl⟩ : syracuseStep 3343285 = 313433) (by norm_num)
theorem B3433421 : Blo 1760081 3433421 := bbase (se 3 (by rfl) ⟨643766, by rfl⟩ : syracuseStep 3433421 = 1287533) (by norm_num)
theorem B12862421 : Blo 1760081 12862421 := bbase (se 7 (by rfl) ⟨150731, by rfl⟩ : syracuseStep 12862421 = 301463) (by norm_num)
theorem B2229221 : Blo 1760081 2229221 := bbase (se 4 (by rfl) ⟨208989, by rfl⟩ : syracuseStep 2229221 = 417979) (by norm_num)
theorem B9036805 : Blo 1760081 9036805 := bbase (se 4 (by rfl) ⟨847200, by rfl⟩ : syracuseStep 9036805 = 1694401) (by norm_num)
theorem B8037397 : Blo 1760081 8037397 := bbase (se 6 (by rfl) ⟨188376, by rfl⟩ : syracuseStep 8037397 = 376753) (by norm_num)
theorem B7144469 : Blo 1760081 7144469 := bbase (se 6 (by rfl) ⟨167448, by rfl⟩ : syracuseStep 7144469 = 334897) (by norm_num)
theorem B4457501 : Blo 1760081 4457501 := bbase (se 3 (by rfl) ⟨835781, by rfl⟩ : syracuseStep 4457501 = 1671563) (by norm_num)
theorem B2229277 : Blo 1760081 2229277 := bbase (se 3 (by rfl) ⟨417989, by rfl⟩ : syracuseStep 2229277 = 835979) (by norm_num)
theorem B2008109 : Blo 1760081 2008109 := bbase (se 3 (by rfl) ⟨376520, by rfl⟩ : syracuseStep 2008109 = 753041) (by norm_num)
theorem B2229373 : Blo 1760081 2229373 := bbase (se 3 (by rfl) ⟨418007, by rfl⟩ : syracuseStep 2229373 = 836015) (by norm_num)
theorem B2114689 : Blo 1760081 2114689 := bbase (se 2 (by rfl) ⟨793008, by rfl⟩ : syracuseStep 2114689 = 1586017) (by norm_num)
theorem B3761333 : Blo 1760081 3761333 := bbase (se 5 (by rfl) ⟨176312, by rfl⟩ : syracuseStep 3761333 = 352625) (by norm_num)
theorem B36660437 : Blo 1760081 36660437 := bbase (se 7 (by rfl) ⟨429614, by rfl⟩ : syracuseStep 36660437 = 859229) (by norm_num)
theorem B4457693 : Blo 1760081 4457693 := bbase (se 3 (by rfl) ⟨835817, by rfl⟩ : syracuseStep 4457693 = 1671635) (by norm_num)
theorem B3343589 : Blo 1760081 3343589 := bbase (se 4 (by rfl) ⟨313461, by rfl⟩ : syracuseStep 3343589 = 626923) (by norm_num)
theorem B5940485 : Blo 1760081 5940485 := bbase (se 4 (by rfl) ⟨556920, by rfl⟩ : syracuseStep 5940485 = 1113841) (by norm_num)
theorem B2229545 : Blo 1760081 2229545 := bbase (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) (by norm_num)
theorem B3761453 : Blo 1760081 3761453 := bbase (se 3 (by rfl) ⟨705272, by rfl⟩ : syracuseStep 3761453 = 1410545) (by norm_num)
theorem B2229601 : Blo 1760081 2229601 := bbase (se 2 (by rfl) ⟨836100, by rfl⟩ : syracuseStep 2229601 = 1672201) (by norm_num)
theorem B4580797 : Blo 1760081 4580797 := bbase (se 3 (by rfl) ⟨858899, by rfl⟩ : syracuseStep 4580797 = 1717799) (by norm_num)
theorem B2229697 : Blo 1760081 2229697 := bbase (se 2 (by rfl) ⟨836136, by rfl⟩ : syracuseStep 2229697 = 1672273) (by norm_num)
theorem B6776261 : Blo 1760081 6776261 := bbase (se 4 (by rfl) ⟨635274, by rfl⟩ : syracuseStep 6776261 = 1270549) (by norm_num)
theorem B8914373 : Blo 1760081 8914373 := bbase (se 4 (by rfl) ⟨835722, by rfl⟩ : syracuseStep 8914373 = 1671445) (by norm_num)
theorem B5014997 : Blo 1760081 5014997 := bbase (se 7 (by rfl) ⟨58769, by rfl⟩ : syracuseStep 5014997 = 117539) (by norm_num)
theorem B8463845 : Blo 1760081 8463845 := bbase (se 4 (by rfl) ⟨793485, by rfl⟩ : syracuseStep 8463845 = 1586971) (by norm_num)
theorem B2115077 : Blo 1760081 2115077 := bbase (se 4 (by rfl) ⟨198288, by rfl⟩ : syracuseStep 2115077 = 396577) (by norm_num)
theorem B13379093 : Blo 1760081 13379093 := bbase (se 6 (by rfl) ⟨313572, by rfl⟩ : syracuseStep 13379093 = 627145) (by norm_num)
theorem B4458037 : Blo 1760081 4458037 := bbase (se 5 (by rfl) ⟨208970, by rfl⟩ : syracuseStep 4458037 = 417941) (by norm_num)
theorem B4761173 : Blo 1760081 4761173 := bbase (se 8 (by rfl) ⟨27897, by rfl⟩ : syracuseStep 4761173 = 55795) (by norm_num)
theorem B4015709 : Blo 1760081 4015709 := bbase (se 3 (by rfl) ⟨752945, by rfl⟩ : syracuseStep 4015709 = 1505891) (by norm_num)
theorem B2819693 : Blo 1760081 2819693 := bbase (se 3 (by rfl) ⟨528692, by rfl⟩ : syracuseStep 2819693 = 1057385) (by norm_num)
theorem B2229869 : Blo 1760081 2229869 := bbase (se 3 (by rfl) ⟨418100, by rfl⟩ : syracuseStep 2229869 = 836201) (by norm_num)
theorem B2508421 : Blo 1760081 2508421 := bbase (se 4 (by rfl) ⟨235164, by rfl⟩ : syracuseStep 2508421 = 470329) (by norm_num)
theorem B4458149 : Blo 1760081 4458149 := bbase (se 4 (by rfl) ⟨417951, by rfl⟩ : syracuseStep 4458149 = 835903) (by norm_num)
theorem B2229925 : Blo 1760081 2229925 := bbase (se 4 (by rfl) ⟨209055, by rfl⟩ : syracuseStep 2229925 = 418111) (by norm_num)
theorem B5940917 : Blo 1760081 5940917 := bbase (se 5 (by rfl) ⟨278480, by rfl⟩ : syracuseStep 5940917 = 556961) (by norm_num)
theorem B2541277 : Blo 1760081 2541277 := bbase (se 3 (by rfl) ⟨476489, by rfl⟩ : syracuseStep 2541277 = 952979) (by norm_num)
theorem B2230021 : Blo 1760081 2230021 := bbase (se 4 (by rfl) ⟨209064, by rfl⟩ : syracuseStep 2230021 = 418129) (by norm_num)
theorem B7522085 : Blo 1760081 7522085 := bbase (se 4 (by rfl) ⟨705195, by rfl⟩ : syracuseStep 7522085 = 1410391) (by norm_num)
theorem B2008885 : Blo 1760081 2008885 := bbase (se 5 (by rfl) ⟨94166, by rfl⟩ : syracuseStep 2008885 = 188333) (by norm_num)
theorem B4458341 : Blo 1760081 4458341 := bbase (se 4 (by rfl) ⟨417969, by rfl⟩ : syracuseStep 4458341 = 835939) (by norm_num)
theorem B2115433 : Blo 1760081 2115433 := bbase (se 2 (by rfl) ⟨793287, by rfl⟩ : syracuseStep 2115433 = 1586575) (by norm_num)
theorem B6104965 : Blo 1760081 6104965 := bbase (se 4 (by rfl) ⟨572340, by rfl⟩ : syracuseStep 6104965 = 1144681) (by norm_num)
theorem B5015429 : Blo 1760081 5015429 := bbase (se 4 (by rfl) ⟨470196, by rfl⟩ : syracuseStep 5015429 = 940393) (by norm_num)
theorem B3762085 : Blo 1760081 3762085 := bbase (se 4 (by rfl) ⟨352695, by rfl⟩ : syracuseStep 3762085 = 705391) (by norm_num)
theorem B4761509 : Blo 1760081 4761509 := bbase (se 4 (by rfl) ⟨446391, by rfl⟩ : syracuseStep 4761509 = 892783) (by norm_num)
theorem B13371317 : Blo 1760081 13371317 := bbase (se 5 (by rfl) ⟨626780, by rfl⟩ : syracuseStep 13371317 = 1253561) (by norm_num)
theorem B3344341 : Blo 1760081 3344341 := bbase (se 7 (by rfl) ⟨39191, by rfl⟩ : syracuseStep 3344341 = 78383) (by norm_num)
theorem B5941349 : Blo 1760081 5941349 := bbase (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) (by norm_num)
theorem B3344485 : Blo 1760081 3344485 := bbase (se 4 (by rfl) ⟨313545, by rfl⟩ : syracuseStep 3344485 = 627091) (by norm_num)
theorem B2820205 : Blo 1760081 2820205 := bbase (se 3 (by rfl) ⟨528788, by rfl⟩ : syracuseStep 2820205 = 1057577) (by norm_num)
theorem B22554773 : Blo 1760081 22554773 := bbase (se 6 (by rfl) ⟨528627, by rfl⟩ : syracuseStep 22554773 = 1057255) (by norm_num)
theorem B2115769 : Blo 1760081 2115769 := bbase (se 2 (by rfl) ⟨793413, by rfl⟩ : syracuseStep 2115769 = 1586827) (by norm_num)
theorem B4229309 : Blo 1760081 4229309 := bbase (se 3 (by rfl) ⟨792995, by rfl⟩ : syracuseStep 4229309 = 1585991) (by norm_num)
theorem B4458685 : Blo 1760081 4458685 := bbase (se 3 (by rfl) ⟨836003, by rfl⟩ : syracuseStep 4458685 = 1672007) (by norm_num)
theorem B2640125 : Blo 1760081 2640125 := bbase (se 3 (by rfl) ⟨495023, by rfl⟩ : syracuseStep 2640125 = 990047) (by norm_num)
theorem B6686981 : Blo 1760081 6686981 := bbase (se 4 (by rfl) ⟨626904, by rfl⟩ : syracuseStep 6686981 = 1253809) (by norm_num)
theorem B3344645 : Blo 1760081 3344645 := bbase (se 4 (by rfl) ⟨313560, by rfl⟩ : syracuseStep 3344645 = 627121) (by norm_num)
theorem B2640149 : Blo 1760081 2640149 := bbase (se 6 (by rfl) ⟨61878, by rfl⟩ : syracuseStep 2640149 = 123757) (by norm_num)
theorem B2640173 : Blo 1760081 2640173 := bbase (se 3 (by rfl) ⟨495032, by rfl⟩ : syracuseStep 2640173 = 990065) (by norm_num)
theorem B4016429 : Blo 1760081 4016429 := bbase (se 3 (by rfl) ⟨753080, by rfl⟩ : syracuseStep 4016429 = 1506161) (by norm_num)
theorem B4458797 : Blo 1760081 4458797 := bbase (se 3 (by rfl) ⟨836024, by rfl⟩ : syracuseStep 4458797 = 1672049) (by norm_num)
theorem B2640197 : Blo 1760081 2640197 := bbase (se 4 (by rfl) ⟨247518, by rfl⟩ : syracuseStep 2640197 = 495037) (by norm_num)
theorem B4229453 : Blo 1760081 4229453 := bbase (se 3 (by rfl) ⟨793022, by rfl⟩ : syracuseStep 4229453 = 1586045) (by norm_num)
theorem B2640221 : Blo 1760081 2640221 := bbase (se 3 (by rfl) ⟨495041, by rfl⟩ : syracuseStep 2640221 = 990083) (by norm_num)
theorem B2640245 : Blo 1760081 2640245 := bbase (se 5 (by rfl) ⟨123761, by rfl⟩ : syracuseStep 2640245 = 247523) (by norm_num)
theorem B2640269 : Blo 1760081 2640269 := bbase (se 3 (by rfl) ⟨495050, by rfl⟩ : syracuseStep 2640269 = 990101) (by norm_num)
theorem B3344789 : Blo 1760081 3344789 := bbase (se 6 (by rfl) ⟨78393, by rfl⟩ : syracuseStep 3344789 = 156787) (by norm_num)
theorem B2640293 : Blo 1760081 2640293 := bbase (se 4 (by rfl) ⟨247527, by rfl⟩ : syracuseStep 2640293 = 495055) (by norm_num)
theorem B4762037 : Blo 1760081 4762037 := bbase (se 5 (by rfl) ⟨223220, by rfl⟩ : syracuseStep 4762037 = 446441) (by norm_num)
theorem B2640317 : Blo 1760081 2640317 := bbase (se 3 (by rfl) ⟨495059, by rfl⟩ : syracuseStep 2640317 = 990119) (by norm_num)
theorem B2640341 : Blo 1760081 2640341 := bbase (se 7 (by rfl) ⟨30941, by rfl⟩ : syracuseStep 2640341 = 61883) (by norm_num)
theorem B2640365 : Blo 1760081 2640365 := bbase (se 3 (by rfl) ⟨495068, by rfl⟩ : syracuseStep 2640365 = 990137) (by norm_num)
theorem B4458989 : Blo 1760081 4458989 := bbase (se 3 (by rfl) ⟨836060, by rfl⟩ : syracuseStep 4458989 = 1672121) (by norm_num)
theorem B2640389 : Blo 1760081 2640389 := bbase (se 4 (by rfl) ⟨247536, by rfl⟩ : syracuseStep 2640389 = 495073) (by norm_num)
theorem B5941781 : Blo 1760081 5941781 := bbase (se 6 (by rfl) ⟨139260, by rfl⟩ : syracuseStep 5941781 = 278521) (by norm_num)
theorem B2640413 : Blo 1760081 2640413 := bbase (se 3 (by rfl) ⟨495077, by rfl⟩ : syracuseStep 2640413 = 990155) (by norm_num)
theorem B6687269 : Blo 1760081 6687269 := bbase (se 4 (by rfl) ⟨626931, by rfl⟩ : syracuseStep 6687269 = 1253863) (by norm_num)
theorem B2640437 : Blo 1760081 2640437 := bbase (se 5 (by rfl) ⟨123770, by rfl⟩ : syracuseStep 2640437 = 247541) (by norm_num)
theorem B3172933 : Blo 1760081 3172933 := bbase (se 4 (by rfl) ⟨297462, by rfl⟩ : syracuseStep 3172933 = 594925) (by norm_num)
theorem B2640461 : Blo 1760081 2640461 := bbase (se 3 (by rfl) ⟨495086, by rfl⟩ : syracuseStep 2640461 = 990173) (by norm_num)
theorem B2640485 : Blo 1760081 2640485 := bbase (se 4 (by rfl) ⟨247545, by rfl⟩ : syracuseStep 2640485 = 495091) (by norm_num)
theorem B5016181 : Blo 1760081 5016181 := bbase (se 5 (by rfl) ⟨235133, by rfl⟩ : syracuseStep 5016181 = 470267) (by norm_num)
theorem B2640509 : Blo 1760081 2640509 := bbase (se 3 (by rfl) ⟨495095, by rfl⟩ : syracuseStep 2640509 = 990191) (by norm_num)
theorem B2640533 : Blo 1760081 2640533 := bbase (se 6 (by rfl) ⟨61887, by rfl⟩ : syracuseStep 2640533 = 123775) (by norm_num)
theorem B2640557 : Blo 1760081 2640557 := bbase (se 3 (by rfl) ⟨495104, by rfl⟩ : syracuseStep 2640557 = 990209) (by norm_num)
theorem B3345077 : Blo 1760081 3345077 := bbase (se 5 (by rfl) ⟨156800, by rfl⟩ : syracuseStep 3345077 = 313601) (by norm_num)
theorem B2640581 : Blo 1760081 2640581 := bbase (se 4 (by rfl) ⟨247554, by rfl⟩ : syracuseStep 2640581 = 495109) (by norm_num)
theorem B8915669 : Blo 1760081 8915669 := bbase (se 7 (by rfl) ⟨104480, by rfl⟩ : syracuseStep 8915669 = 208961) (by norm_num)
theorem B2640605 : Blo 1760081 2640605 := bbase (se 3 (by rfl) ⟨495113, by rfl⟩ : syracuseStep 2640605 = 990227) (by norm_num)
theorem B2640629 : Blo 1760081 2640629 := bbase (se 5 (by rfl) ⟨123779, by rfl⟩ : syracuseStep 2640629 = 247559) (by norm_num)
theorem B2640653 : Blo 1760081 2640653 := bbase (se 3 (by rfl) ⟨495122, by rfl⟩ : syracuseStep 2640653 = 990245) (by norm_num)
theorem B3762973 : Blo 1760081 3762973 := bbase (se 3 (by rfl) ⟨705557, by rfl⟩ : syracuseStep 3762973 = 1411115) (by norm_num)
theorem B2640677 : Blo 1760081 2640677 := bbase (se 4 (by rfl) ⟨247563, by rfl⟩ : syracuseStep 2640677 = 495127) (by norm_num)
theorem B2640701 : Blo 1760081 2640701 := bbase (se 3 (by rfl) ⟨495131, by rfl⟩ : syracuseStep 2640701 = 990263) (by norm_num)
theorem B4459333 : Blo 1760081 4459333 := bbase (se 4 (by rfl) ⟨418062, by rfl⟩ : syracuseStep 4459333 = 836125) (by norm_num)
theorem B2640725 : Blo 1760081 2640725 := bbase (se 9 (by rfl) ⟨7736, by rfl⟩ : syracuseStep 2640725 = 15473) (by norm_num)
theorem B2640749 : Blo 1760081 2640749 := bbase (se 3 (by rfl) ⟨495140, by rfl⟩ : syracuseStep 2640749 = 990281) (by norm_num)
theorem B8465269 : Blo 1760081 8465269 := bbase (se 5 (by rfl) ⟨396809, by rfl⟩ : syracuseStep 8465269 = 793619) (by norm_num)
theorem B2640773 : Blo 1760081 2640773 := bbase (se 4 (by rfl) ⟨247572, by rfl⟩ : syracuseStep 2640773 = 495145) (by norm_num)
theorem B8031109 : Blo 1760081 8031109 := bbase (se 4 (by rfl) ⟨752916, by rfl⟩ : syracuseStep 8031109 = 1505833) (by norm_num)
theorem B3763093 : Blo 1760081 3763093 := bbase (se 6 (by rfl) ⟨88197, by rfl⟩ : syracuseStep 3763093 = 176395) (by norm_num)
theorem B2640797 : Blo 1760081 2640797 := bbase (se 3 (by rfl) ⟨495149, by rfl⟩ : syracuseStep 2640797 = 990299) (by norm_num)
theorem B2640821 : Blo 1760081 2640821 := bbase (se 5 (by rfl) ⟨123788, by rfl⟩ : syracuseStep 2640821 = 247577) (by norm_num)
theorem B4459445 : Blo 1760081 4459445 := bbase (se 5 (by rfl) ⟨209036, by rfl⟩ : syracuseStep 4459445 = 418073) (by norm_num)
theorem B5942213 : Blo 1760081 5942213 := bbase (se 4 (by rfl) ⟨557082, by rfl⟩ : syracuseStep 5942213 = 1114165) (by norm_num)
theorem B2640845 : Blo 1760081 2640845 := bbase (se 3 (by rfl) ⟨495158, by rfl⟩ : syracuseStep 2640845 = 990317) (by norm_num)
theorem B2640869 : Blo 1760081 2640869 := bbase (se 4 (by rfl) ⟨247581, by rfl⟩ : syracuseStep 2640869 = 495163) (by norm_num)
theorem B2640893 : Blo 1760081 2640893 := bbase (se 3 (by rfl) ⟨495167, by rfl⟩ : syracuseStep 2640893 = 990335) (by norm_num)
theorem B2640917 : Blo 1760081 2640917 := bbase (se 6 (by rfl) ⟨61896, by rfl⟩ : syracuseStep 2640917 = 123793) (by norm_num)
theorem B2116649 : Blo 1760081 2116649 := bbase (se 2 (by rfl) ⟨793743, by rfl⟩ : syracuseStep 2116649 = 1587487) (by norm_num)
theorem B2640941 : Blo 1760081 2640941 := bbase (se 3 (by rfl) ⟨495176, by rfl⟩ : syracuseStep 2640941 = 990353) (by norm_num)
theorem B2640965 : Blo 1760081 2640965 := bbase (se 4 (by rfl) ⟨247590, by rfl⟩ : syracuseStep 2640965 = 495181) (by norm_num)
theorem B2821205 : Blo 1760081 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B2640989 : Blo 1760081 2640989 := bbase (se 3 (by rfl) ⟨495185, by rfl⟩ : syracuseStep 2640989 = 990371) (by norm_num)
theorem B2641013 : Blo 1760081 2641013 := bbase (se 5 (by rfl) ⟨123797, by rfl⟩ : syracuseStep 2641013 = 247595) (by norm_num)
theorem B4459637 : Blo 1760081 4459637 := bbase (se 5 (by rfl) ⟨209045, by rfl⟩ : syracuseStep 4459637 = 418091) (by norm_num)
theorem B2641037 : Blo 1760081 2641037 := bbase (se 3 (by rfl) ⟨495194, by rfl⟩ : syracuseStep 2641037 = 990389) (by norm_num)
theorem B3763349 : Blo 1760081 3763349 := bbase (se 6 (by rfl) ⟨88203, by rfl⟩ : syracuseStep 3763349 = 176407) (by norm_num)
theorem B2641061 : Blo 1760081 2641061 := bbase (se 4 (by rfl) ⟨247599, by rfl⟩ : syracuseStep 2641061 = 495199) (by norm_num)
theorem B2641085 : Blo 1760081 2641085 := bbase (se 3 (by rfl) ⟨495203, by rfl⟩ : syracuseStep 2641085 = 990407) (by norm_num)
theorem B2641109 : Blo 1760081 2641109 := bbase (se 7 (by rfl) ⟨30950, by rfl⟩ : syracuseStep 2641109 = 61901) (by norm_num)
theorem B2821333 : Blo 1760081 2821333 := bbase (se 7 (by rfl) ⟨33062, by rfl⟩ : syracuseStep 2821333 = 66125) (by norm_num)
theorem B2641133 : Blo 1760081 2641133 := bbase (se 3 (by rfl) ⟨495212, by rfl⟩ : syracuseStep 2641133 = 990425) (by norm_num)
theorem B2641157 : Blo 1760081 2641157 := bbase (se 4 (by rfl) ⟨247608, by rfl⟩ : syracuseStep 2641157 = 495217) (by norm_num)
theorem B2821397 : Blo 1760081 2821397 := bbase (se 6 (by rfl) ⟨66126, by rfl⟩ : syracuseStep 2821397 = 132253) (by norm_num)
theorem B2641181 : Blo 1760081 2641181 := bbase (se 3 (by rfl) ⟨495221, by rfl⟩ : syracuseStep 2641181 = 990443) (by norm_num)
theorem B2641205 : Blo 1760081 2641205 := bbase (se 5 (by rfl) ⟨123806, by rfl⟩ : syracuseStep 2641205 = 247613) (by norm_num)
theorem B2714941 : Blo 1760081 2714941 := bbase (se 3 (by rfl) ⟨509051, by rfl⟩ : syracuseStep 2714941 = 1018103) (by norm_num)
theorem B2641229 : Blo 1760081 2641229 := bbase (se 3 (by rfl) ⟨495230, by rfl⟩ : syracuseStep 2641229 = 990461) (by norm_num)
theorem B6344021 : Blo 1760081 6344021 := bbase (se 11 (by rfl) ⟨4646, by rfl⟩ : syracuseStep 6344021 = 9293) (by norm_num)
theorem B9522517 : Blo 1760081 9522517 := bbase (se 11 (by rfl) ⟨6974, by rfl⟩ : syracuseStep 9522517 = 13949) (by norm_num)
theorem B4517221 : Blo 1760081 4517221 := bbase (se 4 (by rfl) ⟨423489, by rfl⟩ : syracuseStep 4517221 = 846979) (by norm_num)
theorem B2641253 : Blo 1760081 2641253 := bbase (se 4 (by rfl) ⟨247617, by rfl⟩ : syracuseStep 2641253 = 495235) (by norm_num)
theorem B5942645 : Blo 1760081 5942645 := bbase (se 5 (by rfl) ⟨278561, by rfl⟩ : syracuseStep 5942645 = 557123) (by norm_num)
theorem B2641277 : Blo 1760081 2641277 := bbase (se 3 (by rfl) ⟨495239, by rfl⟩ : syracuseStep 2641277 = 990479) (by norm_num)
theorem B3960197 : Blo 1760081 3960197 := bbase (se 4 (by rfl) ⟨371268, by rfl⟩ : syracuseStep 3960197 = 742537) (by norm_num)
theorem B2641301 : Blo 1760081 2641301 := bbase (se 6 (by rfl) ⟨61905, by rfl⟩ : syracuseStep 2641301 = 123811) (by norm_num)
theorem B2035109 : Blo 1760081 2035109 := bbase (se 4 (by rfl) ⟨190791, by rfl⟩ : syracuseStep 2035109 = 381583) (by norm_num)
theorem B2379181 : Blo 1760081 2379181 := bbase (se 3 (by rfl) ⟨446096, by rfl⟩ : syracuseStep 2379181 = 892193) (by norm_num)
theorem B2641325 : Blo 1760081 2641325 := bbase (se 3 (by rfl) ⟨495248, by rfl⟩ : syracuseStep 2641325 = 990497) (by norm_num)
theorem B2641349 : Blo 1760081 2641349 := bbase (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) (by norm_num)
theorem B3960269 : Blo 1760081 3960269 := bbase (se 3 (by rfl) ⟨742550, by rfl⟩ : syracuseStep 3960269 = 1485101) (by norm_num)
theorem B4459981 : Blo 1760081 4459981 := bbase (se 3 (by rfl) ⟨836246, by rfl⟩ : syracuseStep 4459981 = 1672493) (by norm_num)
theorem B2641373 : Blo 1760081 2641373 := bbase (se 3 (by rfl) ⟨495257, by rfl⟩ : syracuseStep 2641373 = 990515) (by norm_num)
theorem B2641397 : Blo 1760081 2641397 := bbase (se 5 (by rfl) ⟨123815, by rfl⟩ : syracuseStep 2641397 = 247631) (by norm_num)
theorem B2641421 : Blo 1760081 2641421 := bbase (se 3 (by rfl) ⟨495266, by rfl⟩ : syracuseStep 2641421 = 990533) (by norm_num)
theorem B1879573 : Blo 1760081 1879573 := bbase (se 6 (by rfl) ⟨44052, by rfl⟩ : syracuseStep 1879573 = 88105) (by norm_num)
theorem B3960341 : Blo 1760081 3960341 := bbase (se 6 (by rfl) ⟨92820, by rfl⟩ : syracuseStep 3960341 = 185641) (by norm_num)
theorem B2641445 : Blo 1760081 2641445 := bbase (se 4 (by rfl) ⟨247635, by rfl⟩ : syracuseStep 2641445 = 495271) (by norm_num)
theorem B2641469 : Blo 1760081 2641469 := bbase (se 3 (by rfl) ⟨495275, by rfl⟩ : syracuseStep 2641469 = 990551) (by norm_num)
theorem B4460093 : Blo 1760081 4460093 := bbase (se 3 (by rfl) ⟨836267, by rfl⟩ : syracuseStep 4460093 = 1672535) (by norm_num)
theorem B1879633 : Blo 1760081 1879633 := bbase (se 2 (by rfl) ⟨704862, by rfl⟩ : syracuseStep 1879633 = 1409725) (by norm_num)
theorem B2641493 : Blo 1760081 2641493 := bbase (se 8 (by rfl) ⟨15477, by rfl⟩ : syracuseStep 2641493 = 30955) (by norm_num)
theorem B3960413 : Blo 1760081 3960413 := bbase (se 3 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 3960413 = 1485155) (by norm_num)
theorem B2641517 : Blo 1760081 2641517 := bbase (se 3 (by rfl) ⟨495284, by rfl⟩ : syracuseStep 2641517 = 990569) (by norm_num)
theorem B2641541 : Blo 1760081 2641541 := bbase (se 4 (by rfl) ⟨247644, by rfl⟩ : syracuseStep 2641541 = 495289) (by norm_num)
theorem B2641565 : Blo 1760081 2641565 := bbase (se 3 (by rfl) ⟨495293, by rfl⟩ : syracuseStep 2641565 = 990587) (by norm_num)
theorem B3960485 : Blo 1760081 3960485 := bbase (se 4 (by rfl) ⟨371295, by rfl⟩ : syracuseStep 3960485 = 742591) (by norm_num)
theorem B2641589 : Blo 1760081 2641589 := bbase (se 5 (by rfl) ⟨123824, by rfl⟩ : syracuseStep 2641589 = 247649) (by norm_num)
theorem B6688453 : Blo 1760081 6688453 := bbase (se 4 (by rfl) ⟨627042, by rfl⟩ : syracuseStep 6688453 = 1254085) (by norm_num)
theorem B2641613 : Blo 1760081 2641613 := bbase (se 3 (by rfl) ⟨495302, by rfl⟩ : syracuseStep 2641613 = 990605) (by norm_num)
theorem B2641637 : Blo 1760081 2641637 := bbase (se 4 (by rfl) ⟨247653, by rfl⟩ : syracuseStep 2641637 = 495307) (by norm_num)
theorem B3960557 : Blo 1760081 3960557 := bbase (se 3 (by rfl) ⟨742604, by rfl⟩ : syracuseStep 3960557 = 1485209) (by norm_num)
theorem B2641661 : Blo 1760081 2641661 := bbase (se 3 (by rfl) ⟨495311, by rfl⟩ : syracuseStep 2641661 = 990623) (by norm_num)
theorem B6344453 : Blo 1760081 6344453 := bbase (se 4 (by rfl) ⟨594792, by rfl⟩ : syracuseStep 6344453 = 1189585) (by norm_num)
theorem B2641685 : Blo 1760081 2641685 := bbase (se 6 (by rfl) ⟨61914, by rfl⟩ : syracuseStep 2641685 = 123829) (by norm_num)
theorem B5943077 : Blo 1760081 5943077 := bbase (se 4 (by rfl) ⟨557163, by rfl⟩ : syracuseStep 5943077 = 1114327) (by norm_num)
theorem B2641709 : Blo 1760081 2641709 := bbase (se 3 (by rfl) ⟨495320, by rfl⟩ : syracuseStep 2641709 = 990641) (by norm_num)
theorem B3960629 : Blo 1760081 3960629 := bbase (se 5 (by rfl) ⟨185654, by rfl⟩ : syracuseStep 3960629 = 371309) (by norm_num)
theorem B5639989 : Blo 1760081 5639989 := bbase (se 5 (by rfl) ⟨264374, by rfl⟩ : syracuseStep 5639989 = 528749) (by norm_num)
theorem B2641733 : Blo 1760081 2641733 := bbase (se 4 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 2641733 = 495325) (by norm_num)
theorem B28946261 : Blo 1760081 28946261 := bbase (se 9 (by rfl) ⟨84803, by rfl⟩ : syracuseStep 28946261 = 169607) (by norm_num)
theorem B2641757 : Blo 1760081 2641757 := bbase (se 3 (by rfl) ⟨495329, by rfl⟩ : syracuseStep 2641757 = 990659) (by norm_num)
theorem B2641781 : Blo 1760081 2641781 := bbase (se 5 (by rfl) ⟨123833, by rfl⟩ : syracuseStep 2641781 = 247667) (by norm_num)
theorem B3960701 : Blo 1760081 3960701 := bbase (se 3 (by rfl) ⟨742631, by rfl⟩ : syracuseStep 3960701 = 1485263) (by norm_num)
theorem B6188933 : Blo 1760081 6188933 := bbase (se 4 (by rfl) ⟨580212, by rfl⟩ : syracuseStep 6188933 = 1160425) (by norm_num)
theorem B1879949 : Blo 1760081 1879949 := bbase (se 3 (by rfl) ⟨352490, by rfl⟩ : syracuseStep 1879949 = 704981) (by norm_num)
theorem B2641805 : Blo 1760081 2641805 := bbase (se 3 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 2641805 = 990677) (by norm_num)
theorem B2641829 : Blo 1760081 2641829 := bbase (se 4 (by rfl) ⟨247671, by rfl⟩ : syracuseStep 2641829 = 495343) (by norm_num)
theorem B3174317 : Blo 1760081 3174317 := bbase (se 3 (by rfl) ⟨595184, by rfl⟩ : syracuseStep 3174317 = 1190369) (by norm_num)
theorem B2641853 : Blo 1760081 2641853 := bbase (se 3 (by rfl) ⟨495347, by rfl⟩ : syracuseStep 2641853 = 990695) (by norm_num)
theorem B3960773 : Blo 1760081 3960773 := bbase (se 4 (by rfl) ⟨371322, by rfl⟩ : syracuseStep 3960773 = 742645) (by norm_num)
theorem B2641877 : Blo 1760081 2641877 := bbase (se 7 (by rfl) ⟨30959, by rfl⟩ : syracuseStep 2641877 = 61919) (by norm_num)
theorem B8916965 : Blo 1760081 8916965 := bbase (se 4 (by rfl) ⟨835965, by rfl⟩ : syracuseStep 8916965 = 1671931) (by norm_num)
theorem B2641901 : Blo 1760081 2641901 := bbase (se 3 (by rfl) ⟨495356, by rfl⟩ : syracuseStep 2641901 = 990713) (by norm_num)
theorem B6688757 : Blo 1760081 6688757 := bbase (se 5 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 6688757 = 627071) (by norm_num)
theorem B2641925 : Blo 1760081 2641925 := bbase (se 4 (by rfl) ⟨247680, by rfl⟩ : syracuseStep 2641925 = 495361) (by norm_num)
theorem B3960845 : Blo 1760081 3960845 := bbase (se 3 (by rfl) ⟨742658, by rfl⟩ : syracuseStep 3960845 = 1485317) (by norm_num)
theorem B2641949 : Blo 1760081 2641949 := bbase (se 3 (by rfl) ⟨495365, by rfl⟩ : syracuseStep 2641949 = 990731) (by norm_num)
theorem B2641973 : Blo 1760081 2641973 := bbase (se 5 (by rfl) ⟨123842, by rfl⟩ : syracuseStep 2641973 = 247685) (by norm_num)
theorem B2641997 : Blo 1760081 2641997 := bbase (se 3 (by rfl) ⟨495374, by rfl⟩ : syracuseStep 2641997 = 990749) (by norm_num)
theorem B3960917 : Blo 1760081 3960917 := bbase (se 8 (by rfl) ⟨23208, by rfl⟩ : syracuseStep 3960917 = 46417) (by norm_num)
theorem B2642021 : Blo 1760081 2642021 := bbase (se 4 (by rfl) ⟨247689, by rfl⟩ : syracuseStep 2642021 = 495379) (by norm_num)
theorem B2642045 : Blo 1760081 2642045 := bbase (se 3 (by rfl) ⟨495383, by rfl⟩ : syracuseStep 2642045 = 990767) (by norm_num)
theorem B2642069 : Blo 1760081 2642069 := bbase (se 6 (by rfl) ⟨61923, by rfl⟩ : syracuseStep 2642069 = 123847) (by norm_num)
theorem B20066453 : Blo 1760081 20066453 := bbase (se 6 (by rfl) ⟨470307, by rfl⟩ : syracuseStep 20066453 = 940615) (by norm_num)
theorem B3960989 : Blo 1760081 3960989 := bbase (se 3 (by rfl) ⟨742685, by rfl⟩ : syracuseStep 3960989 = 1485371) (by norm_num)
theorem B2642093 : Blo 1760081 2642093 := bbase (se 3 (by rfl) ⟨495392, by rfl⟩ : syracuseStep 2642093 = 990785) (by norm_num)
theorem B2642117 : Blo 1760081 2642117 := bbase (se 4 (by rfl) ⟨247698, by rfl⟩ : syracuseStep 2642117 = 495397) (by norm_num)
theorem B5943509 : Blo 1760081 5943509 := bbase (se 7 (by rfl) ⟨69650, by rfl⟩ : syracuseStep 5943509 = 139301) (by norm_num)
theorem B2642141 : Blo 1760081 2642141 := bbase (se 3 (by rfl) ⟨495401, by rfl⟩ : syracuseStep 2642141 = 990803) (by norm_num)
theorem B3961061 : Blo 1760081 3961061 := bbase (se 4 (by rfl) ⟨371349, by rfl⟩ : syracuseStep 3961061 = 742699) (by norm_num)
theorem B2642165 : Blo 1760081 2642165 := bbase (se 5 (by rfl) ⟨123851, by rfl⟩ : syracuseStep 2642165 = 247703) (by norm_num)
theorem B2642189 : Blo 1760081 2642189 := bbase (se 3 (by rfl) ⟨495410, by rfl⟩ : syracuseStep 2642189 = 990821) (by norm_num)
theorem B4231453 : Blo 1760081 4231453 := bbase (se 3 (by rfl) ⟨793397, by rfl⟩ : syracuseStep 4231453 = 1586795) (by norm_num)
theorem B2642213 : Blo 1760081 2642213 := bbase (se 4 (by rfl) ⟨247707, by rfl⟩ : syracuseStep 2642213 = 495415) (by norm_num)
theorem B3961133 : Blo 1760081 3961133 := bbase (se 3 (by rfl) ⟨742712, by rfl⟩ : syracuseStep 3961133 = 1485425) (by norm_num)
theorem B2642237 : Blo 1760081 2642237 := bbase (se 3 (by rfl) ⟨495419, by rfl⟩ : syracuseStep 2642237 = 990839) (by norm_num)
theorem B1880393 : Blo 1760081 1880393 := bbase (se 2 (by rfl) ⟨705147, by rfl⟩ : syracuseStep 1880393 = 1410295) (by norm_num)
theorem B2642261 : Blo 1760081 2642261 := bbase (se 10 (by rfl) ⟨3870, by rfl⟩ : syracuseStep 2642261 = 7741) (by norm_num)
theorem B9163109 : Blo 1760081 9163109 := bbase (se 4 (by rfl) ⟨859041, by rfl⟩ : syracuseStep 9163109 = 1718083) (by norm_num)
theorem B2642285 : Blo 1760081 2642285 := bbase (se 3 (by rfl) ⟨495428, by rfl⟩ : syracuseStep 2642285 = 990857) (by norm_num)
theorem B3961205 : Blo 1760081 3961205 := bbase (se 5 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 3961205 = 371363) (by norm_num)
theorem B6025589 : Blo 1760081 6025589 := bbase (se 5 (by rfl) ⟨282449, by rfl⟩ : syracuseStep 6025589 = 564899) (by norm_num)
theorem B1880453 : Blo 1760081 1880453 := bbase (se 4 (by rfl) ⟨176292, by rfl⟩ : syracuseStep 1880453 = 352585) (by norm_num)
theorem B2642309 : Blo 1760081 2642309 := bbase (se 4 (by rfl) ⟨247716, by rfl⟩ : syracuseStep 2642309 = 495433) (by norm_num)
theorem B2642333 : Blo 1760081 2642333 := bbase (se 3 (by rfl) ⟨495437, by rfl⟩ : syracuseStep 2642333 = 990875) (by norm_num)
theorem B2576821 : Blo 1760081 2576821 := bbase (se 5 (by rfl) ⟨120788, by rfl⟩ : syracuseStep 2576821 = 241577) (by norm_num)
theorem B2642357 : Blo 1760081 2642357 := bbase (se 5 (by rfl) ⟨123860, by rfl⟩ : syracuseStep 2642357 = 247721) (by norm_num)
theorem B3961277 : Blo 1760081 3961277 := bbase (se 3 (by rfl) ⟨742739, by rfl⟩ : syracuseStep 3961277 = 1485479) (by norm_num)
theorem B2642381 : Blo 1760081 2642381 := bbase (se 3 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 2642381 = 990893) (by norm_num)
theorem B2642405 : Blo 1760081 2642405 := bbase (se 4 (by rfl) ⟨247725, by rfl⟩ : syracuseStep 2642405 = 495451) (by norm_num)
theorem B2642429 : Blo 1760081 2642429 := bbase (se 3 (by rfl) ⟨495455, by rfl⟩ : syracuseStep 2642429 = 990911) (by norm_num)
theorem B3961349 : Blo 1760081 3961349 := bbase (se 4 (by rfl) ⟨371376, by rfl⟩ : syracuseStep 3961349 = 742753) (by norm_num)
theorem B1880581 : Blo 1760081 1880581 := bbase (se 4 (by rfl) ⟨176304, by rfl⟩ : syracuseStep 1880581 = 352609) (by norm_num)
theorem B4018693 : Blo 1760081 4018693 := bbase (se 4 (by rfl) ⟨376752, by rfl⟩ : syracuseStep 4018693 = 753505) (by norm_num)
theorem B2642453 : Blo 1760081 2642453 := bbase (se 6 (by rfl) ⟨61932, by rfl⟩ : syracuseStep 2642453 = 123865) (by norm_num)
theorem B2642477 : Blo 1760081 2642477 := bbase (se 3 (by rfl) ⟨495464, by rfl⟩ : syracuseStep 2642477 = 990929) (by norm_num)
theorem B2642501 : Blo 1760081 2642501 := bbase (se 4 (by rfl) ⟨247734, by rfl⟩ : syracuseStep 2642501 = 495469) (by norm_num)
theorem B3961421 : Blo 1760081 3961421 := bbase (se 3 (by rfl) ⟨742766, by rfl⟩ : syracuseStep 3961421 = 1485533) (by norm_num)
theorem B2642525 : Blo 1760081 2642525 := bbase (se 3 (by rfl) ⟨495473, by rfl⟩ : syracuseStep 2642525 = 990947) (by norm_num)
theorem B2970229 : Blo 1760081 2970229 := bbase (se 5 (by rfl) ⟨139229, by rfl⟩ : syracuseStep 2970229 = 278459) (by norm_num)
theorem B2642549 : Blo 1760081 2642549 := bbase (se 5 (by rfl) ⟨123869, by rfl⟩ : syracuseStep 2642549 = 247739) (by norm_num)
theorem B5943941 : Blo 1760081 5943941 := bbase (se 4 (by rfl) ⟨557244, by rfl⟩ : syracuseStep 5943941 = 1114489) (by norm_num)
theorem B2642573 : Blo 1760081 2642573 := bbase (se 3 (by rfl) ⟨495482, by rfl⟩ : syracuseStep 2642573 = 990965) (by norm_num)
theorem B3961493 : Blo 1760081 3961493 := bbase (se 6 (by rfl) ⟨92847, by rfl⟩ : syracuseStep 3961493 = 185695) (by norm_num)
theorem B2642597 : Blo 1760081 2642597 := bbase (se 4 (by rfl) ⟨247743, by rfl⟩ : syracuseStep 2642597 = 495487) (by norm_num)
theorem B4289213 : Blo 1760081 4289213 := bbase (se 3 (by rfl) ⟨804227, by rfl⟩ : syracuseStep 4289213 = 1608455) (by norm_num)
theorem B2642621 : Blo 1760081 2642621 := bbase (se 3 (by rfl) ⟨495491, by rfl⟩ : syracuseStep 2642621 = 990983) (by norm_num)
theorem B2970317 : Blo 1760081 2970317 := bbase (se 3 (by rfl) ⟨556934, by rfl⟩ : syracuseStep 2970317 = 1113869) (by norm_num)
theorem B6869717 : Blo 1760081 6869717 := bbase (se 7 (by rfl) ⟨80504, by rfl⟩ : syracuseStep 6869717 = 161009) (by norm_num)
theorem B2642645 : Blo 1760081 2642645 := bbase (se 7 (by rfl) ⟨30968, by rfl⟩ : syracuseStep 2642645 = 61937) (by norm_num)
theorem B3961565 : Blo 1760081 3961565 := bbase (se 3 (by rfl) ⟨742793, by rfl⟩ : syracuseStep 3961565 = 1485587) (by norm_num)
theorem B2642669 : Blo 1760081 2642669 := bbase (se 3 (by rfl) ⟨495500, by rfl⟩ : syracuseStep 2642669 = 991001) (by norm_num)
theorem B2642693 : Blo 1760081 2642693 := bbase (se 4 (by rfl) ⟨247752, by rfl⟩ : syracuseStep 2642693 = 495505) (by norm_num)
theorem B2642717 : Blo 1760081 2642717 := bbase (se 3 (by rfl) ⟨495509, by rfl⟩ : syracuseStep 2642717 = 991019) (by norm_num)
theorem B3961637 : Blo 1760081 3961637 := bbase (se 4 (by rfl) ⟨371403, by rfl⟩ : syracuseStep 3961637 = 742807) (by norm_num)
theorem B2642741 : Blo 1760081 2642741 := bbase (se 5 (by rfl) ⟨123878, by rfl⟩ : syracuseStep 2642741 = 247757) (by norm_num)
theorem B2970445 : Blo 1760081 2970445 := bbase (se 3 (by rfl) ⟨556958, by rfl⟩ : syracuseStep 2970445 = 1113917) (by norm_num)
theorem B2642765 : Blo 1760081 2642765 := bbase (se 3 (by rfl) ⟨495518, by rfl⟩ : syracuseStep 2642765 = 991037) (by norm_num)
theorem B2642789 : Blo 1760081 2642789 := bbase (se 4 (by rfl) ⟨247761, by rfl⟩ : syracuseStep 2642789 = 495523) (by norm_num)
theorem B3961709 : Blo 1760081 3961709 := bbase (se 3 (by rfl) ⟨742820, by rfl⟩ : syracuseStep 3961709 = 1485641) (by norm_num)
theorem B2642813 : Blo 1760081 2642813 := bbase (se 3 (by rfl) ⟨495527, by rfl⟩ : syracuseStep 2642813 = 991055) (by norm_num)
theorem B2642837 : Blo 1760081 2642837 := bbase (se 6 (by rfl) ⟨61941, by rfl⟩ : syracuseStep 2642837 = 123883) (by norm_num)
theorem B2970533 : Blo 1760081 2970533 := bbase (se 4 (by rfl) ⟨278487, by rfl⟩ : syracuseStep 2970533 = 556975) (by norm_num)
theorem B2642861 : Blo 1760081 2642861 := bbase (se 3 (by rfl) ⟨495536, by rfl⟩ : syracuseStep 2642861 = 991073) (by norm_num)
theorem B3961781 : Blo 1760081 3961781 := bbase (se 5 (by rfl) ⟨185708, by rfl⟩ : syracuseStep 3961781 = 371417) (by norm_num)
theorem B1881025 : Blo 1760081 1881025 := bbase (se 2 (by rfl) ⟨705384, by rfl⟩ : syracuseStep 1881025 = 1410769) (by norm_num)
theorem B2642885 : Blo 1760081 2642885 := bbase (se 4 (by rfl) ⟨247770, by rfl⟩ : syracuseStep 2642885 = 495541) (by norm_num)
theorem B14275541 : Blo 1760081 14275541 := bbase (se 7 (by rfl) ⟨167291, by rfl⟩ : syracuseStep 14275541 = 334583) (by norm_num)
theorem B2642909 : Blo 1760081 2642909 := bbase (se 3 (by rfl) ⟨495545, by rfl⟩ : syracuseStep 2642909 = 991091) (by norm_num)
theorem B2642933 : Blo 1760081 2642933 := bbase (se 5 (by rfl) ⟨123887, by rfl⟩ : syracuseStep 2642933 = 247775) (by norm_num)
theorem B3961853 : Blo 1760081 3961853 := bbase (se 3 (by rfl) ⟨742847, by rfl⟩ : syracuseStep 3961853 = 1485695) (by norm_num)
theorem B2642957 : Blo 1760081 2642957 := bbase (se 3 (by rfl) ⟨495554, by rfl⟩ : syracuseStep 2642957 = 991109) (by norm_num)
theorem B2970661 : Blo 1760081 2970661 := bbase (se 4 (by rfl) ⟨278499, by rfl⟩ : syracuseStep 2970661 = 556999) (by norm_num)
theorem B2642981 : Blo 1760081 2642981 := bbase (se 4 (by rfl) ⟨247779, by rfl⟩ : syracuseStep 2642981 = 495559) (by norm_num)
theorem B5944373 : Blo 1760081 5944373 := bbase (se 5 (by rfl) ⟨278642, by rfl⟩ : syracuseStep 5944373 = 557285) (by norm_num)
theorem B1881145 : Blo 1760081 1881145 := bbase (se 2 (by rfl) ⟨705429, by rfl⟩ : syracuseStep 1881145 = 1410859) (by norm_num)
theorem B2643005 : Blo 1760081 2643005 := bbase (se 3 (by rfl) ⟨495563, by rfl⟩ : syracuseStep 2643005 = 991127) (by norm_num)
theorem B3961925 : Blo 1760081 3961925 := bbase (se 4 (by rfl) ⟨371430, by rfl⟩ : syracuseStep 3961925 = 742861) (by norm_num)
theorem B2643029 : Blo 1760081 2643029 := bbase (se 8 (by rfl) ⟨15486, by rfl⟩ : syracuseStep 2643029 = 30973) (by norm_num)
theorem B2643053 : Blo 1760081 2643053 := bbase (se 3 (by rfl) ⟨495572, by rfl⟩ : syracuseStep 2643053 = 991145) (by norm_num)
theorem B2970749 : Blo 1760081 2970749 := bbase (se 3 (by rfl) ⟨557015, by rfl⟩ : syracuseStep 2970749 = 1114031) (by norm_num)
theorem B2643077 : Blo 1760081 2643077 := bbase (se 4 (by rfl) ⟨247788, by rfl⟩ : syracuseStep 2643077 = 495577) (by norm_num)
theorem B3961997 : Blo 1760081 3961997 := bbase (se 3 (by rfl) ⟨742874, by rfl⟩ : syracuseStep 3961997 = 1485749) (by norm_num)
theorem B4519061 : Blo 1760081 4519061 := bbase (se 6 (by rfl) ⟨105915, by rfl⟩ : syracuseStep 4519061 = 211831) (by norm_num)
theorem B2643101 : Blo 1760081 2643101 := bbase (se 3 (by rfl) ⟨495581, by rfl⟩ : syracuseStep 2643101 = 991163) (by norm_num)
theorem B3962069 : Blo 1760081 3962069 := bbase (se 7 (by rfl) ⟨46430, by rfl⟩ : syracuseStep 3962069 = 92861) (by norm_num)
theorem B8918261 : Blo 1760081 8918261 := bbase (se 5 (by rfl) ⟨418043, by rfl⟩ : syracuseStep 8918261 = 836087) (by norm_num)
theorem B2970877 : Blo 1760081 2970877 := bbase (se 3 (by rfl) ⟨557039, by rfl⟩ : syracuseStep 2970877 = 1114079) (by norm_num)
theorem B3306773 : Blo 1760081 3306773 := bbase (se 6 (by rfl) ⟨77502, by rfl⟩ : syracuseStep 3306773 = 155005) (by norm_num)
theorem B3962141 : Blo 1760081 3962141 := bbase (se 3 (by rfl) ⟨742901, by rfl⟩ : syracuseStep 3962141 = 1485803) (by norm_num)
theorem B1881397 : Blo 1760081 1881397 := bbase (se 5 (by rfl) ⟨88190, by rfl⟩ : syracuseStep 1881397 = 176381) (by norm_num)
theorem B1881401 : Blo 1760081 1881401 := bbase (se 2 (by rfl) ⟨705525, by rfl⟩ : syracuseStep 1881401 = 1411051) (by norm_num)
theorem B2970965 : Blo 1760081 2970965 := bbase (se 19 (by rfl) ⟨8, by rfl⟩ : syracuseStep 2970965 = 17) (by norm_num)
theorem B3962213 : Blo 1760081 3962213 := bbase (se 4 (by rfl) ⟨371457, by rfl⟩ : syracuseStep 3962213 = 742915) (by norm_num)
theorem B5641589 : Blo 1760081 5641589 := bbase (se 5 (by rfl) ⟨264449, by rfl⟩ : syracuseStep 5641589 = 528899) (by norm_num)
theorem B3962285 : Blo 1760081 3962285 := bbase (se 3 (by rfl) ⟨742928, by rfl⟩ : syracuseStep 3962285 = 1485857) (by norm_num)
theorem B1906097 : Blo 1760081 1906097 := bbase (se 2 (by rfl) ⟨714786, by rfl⟩ : syracuseStep 1906097 = 1429573) (by norm_num)
theorem B2971093 : Blo 1760081 2971093 := bbase (se 7 (by rfl) ⟨34817, by rfl⟩ : syracuseStep 2971093 = 69635) (by norm_num)
theorem B5944805 : Blo 1760081 5944805 := bbase (se 4 (by rfl) ⟨557325, by rfl⟩ : syracuseStep 5944805 = 1114651) (by norm_num)
theorem B3962357 : Blo 1760081 3962357 := bbase (se 5 (by rfl) ⟨185735, by rfl⟩ : syracuseStep 3962357 = 371471) (by norm_num)
theorem B2258425 : Blo 1760081 2258425 := bbase (se 2 (by rfl) ⟨846909, by rfl⟩ : syracuseStep 2258425 = 1693819) (by norm_num)
theorem B2971181 : Blo 1760081 2971181 := bbase (se 3 (by rfl) ⟨557096, by rfl⟩ : syracuseStep 2971181 = 1114193) (by norm_num)
theorem B3962429 : Blo 1760081 3962429 := bbase (se 3 (by rfl) ⟨742955, by rfl⟩ : syracuseStep 3962429 = 1485911) (by norm_num)
theorem B3217013 : Blo 1760081 3217013 := bbase (se 5 (by rfl) ⟨150797, by rfl⟩ : syracuseStep 3217013 = 301595) (by norm_num)
theorem B3962501 : Blo 1760081 3962501 := bbase (se 4 (by rfl) ⟨371484, by rfl⟩ : syracuseStep 3962501 = 742969) (by norm_num)
theorem B4232837 : Blo 1760081 4232837 := bbase (se 4 (by rfl) ⟨396828, by rfl⟩ : syracuseStep 4232837 = 793657) (by norm_num)
theorem B4232845 : Blo 1760081 4232845 := bbase (se 3 (by rfl) ⟨793658, by rfl⟩ : syracuseStep 4232845 = 1587317) (by norm_num)
theorem B8910485 : Blo 1760081 8910485 := bbase (se 6 (by rfl) ⟨208839, by rfl⟩ : syracuseStep 8910485 = 417679) (by norm_num)
theorem B2971309 : Blo 1760081 2971309 := bbase (se 3 (by rfl) ⟨557120, by rfl⟩ : syracuseStep 2971309 = 1114241) (by norm_num)
theorem B7239365 : Blo 1760081 7239365 := bbase (se 4 (by rfl) ⟨678690, by rfl⟩ : syracuseStep 7239365 = 1357381) (by norm_num)
theorem B3962573 : Blo 1760081 3962573 := bbase (se 3 (by rfl) ⟨742982, by rfl⟩ : syracuseStep 3962573 = 1485965) (by norm_num)
theorem B10024661 : Blo 1760081 10024661 := bbase (se 7 (by rfl) ⟨117476, by rfl⟩ : syracuseStep 10024661 = 234953) (by norm_num)
theorem B1980121 : Blo 1760081 1980121 := bbase (se 2 (by rfl) ⟨742545, by rfl⟩ : syracuseStep 1980121 = 1485091) (by norm_num)
theorem B1980157 : Blo 1760081 1980157 := bbase (se 3 (by rfl) ⟨371279, by rfl⟩ : syracuseStep 1980157 = 742559) (by norm_num)
theorem B2971397 : Blo 1760081 2971397 := bbase (se 4 (by rfl) ⟨278568, by rfl⟩ : syracuseStep 2971397 = 557137) (by norm_num)
theorem B20330261 : Blo 1760081 20330261 := bbase (se 6 (by rfl) ⟨476490, by rfl⟩ : syracuseStep 20330261 = 952981) (by norm_num)
theorem B3962645 : Blo 1760081 3962645 := bbase (se 6 (by rfl) ⟨92874, by rfl⟩ : syracuseStep 3962645 = 185749) (by norm_num)
theorem B1980193 : Blo 1760081 1980193 := bbase (se 2 (by rfl) ⟨742572, by rfl⟩ : syracuseStep 1980193 = 1485145) (by norm_num)
theorem B1980229 : Blo 1760081 1980229 := bbase (se 4 (by rfl) ⟨185646, by rfl⟩ : syracuseStep 1980229 = 371293) (by norm_num)
theorem B3962717 : Blo 1760081 3962717 := bbase (se 3 (by rfl) ⟨743009, by rfl⟩ : syracuseStep 3962717 = 1486019) (by norm_num)
theorem B1980265 : Blo 1760081 1980265 := bbase (se 2 (by rfl) ⟨742599, by rfl⟩ : syracuseStep 1980265 = 1485199) (by norm_num)
theorem B2971525 : Blo 1760081 2971525 := bbase (se 4 (by rfl) ⟨278580, by rfl⟩ : syracuseStep 2971525 = 557161) (by norm_num)
theorem B1980301 : Blo 1760081 1980301 := bbase (se 3 (by rfl) ⟨371306, by rfl⟩ : syracuseStep 1980301 = 742613) (by norm_num)
theorem B5945237 : Blo 1760081 5945237 := bbase (se 6 (by rfl) ⟨139341, by rfl⟩ : syracuseStep 5945237 = 278683) (by norm_num)
theorem B3962789 : Blo 1760081 3962789 := bbase (se 4 (by rfl) ⟨371511, by rfl⟩ : syracuseStep 3962789 = 743023) (by norm_num)
theorem B6027173 : Blo 1760081 6027173 := bbase (se 4 (by rfl) ⟨565047, by rfl⟩ : syracuseStep 6027173 = 1130095) (by norm_num)
theorem B1980337 : Blo 1760081 1980337 := bbase (se 2 (by rfl) ⟨742626, by rfl⟩ : syracuseStep 1980337 = 1485253) (by norm_num)
theorem B1980373 : Blo 1760081 1980373 := bbase (se 7 (by rfl) ⟨23207, by rfl⟩ : syracuseStep 1980373 = 46415) (by norm_num)
theorem B7526357 : Blo 1760081 7526357 := bbase (se 7 (by rfl) ⟨88199, by rfl⟩ : syracuseStep 7526357 = 176399) (by norm_num)
theorem B2676701 : Blo 1760081 2676701 := bbase (se 3 (by rfl) ⟨501881, by rfl⟩ : syracuseStep 2676701 = 1003763) (by norm_num)
theorem B2971613 : Blo 1760081 2971613 := bbase (se 3 (by rfl) ⟨557177, by rfl⟩ : syracuseStep 2971613 = 1114355) (by norm_num)
theorem B3962861 : Blo 1760081 3962861 := bbase (se 3 (by rfl) ⟨743036, by rfl⟩ : syracuseStep 3962861 = 1486073) (by norm_num)
theorem B1980409 : Blo 1760081 1980409 := bbase (se 2 (by rfl) ⟨742653, by rfl⟩ : syracuseStep 1980409 = 1485307) (by norm_num)
theorem B1980445 : Blo 1760081 1980445 := bbase (se 3 (by rfl) ⟨371333, by rfl⟩ : syracuseStep 1980445 = 742667) (by norm_num)
theorem B2676773 : Blo 1760081 2676773 := bbase (se 4 (by rfl) ⟨250947, by rfl⟩ : syracuseStep 2676773 = 501895) (by norm_num)
theorem B3962933 : Blo 1760081 3962933 := bbase (se 5 (by rfl) ⟨185762, by rfl⟩ : syracuseStep 3962933 = 371525) (by norm_num)
theorem B1980481 : Blo 1760081 1980481 := bbase (se 2 (by rfl) ⟨742680, by rfl⟩ : syracuseStep 1980481 = 1485361) (by norm_num)
theorem B2971741 : Blo 1760081 2971741 := bbase (se 3 (by rfl) ⟨557201, by rfl⟩ : syracuseStep 2971741 = 1114403) (by norm_num)
theorem B1980517 : Blo 1760081 1980517 := bbase (se 4 (by rfl) ⟨185673, by rfl⟩ : syracuseStep 1980517 = 371347) (by norm_num)
theorem B3963005 : Blo 1760081 3963005 := bbase (se 3 (by rfl) ⟨743063, by rfl⟩ : syracuseStep 3963005 = 1486127) (by norm_num)
theorem B1980553 : Blo 1760081 1980553 := bbase (se 2 (by rfl) ⟨742707, by rfl⟩ : syracuseStep 1980553 = 1485415) (by norm_num)
theorem B1980589 : Blo 1760081 1980589 := bbase (se 3 (by rfl) ⟨371360, by rfl⟩ : syracuseStep 1980589 = 742721) (by norm_num)
theorem B2971829 : Blo 1760081 2971829 := bbase (se 5 (by rfl) ⟨139304, by rfl⟩ : syracuseStep 2971829 = 278609) (by norm_num)
theorem B3963077 : Blo 1760081 3963077 := bbase (se 4 (by rfl) ⟨371538, by rfl⟩ : syracuseStep 3963077 = 743077) (by norm_num)
theorem B1980625 : Blo 1760081 1980625 := bbase (se 2 (by rfl) ⟨742734, by rfl⟩ : syracuseStep 1980625 = 1485469) (by norm_num)
theorem B1980661 : Blo 1760081 1980661 := bbase (se 5 (by rfl) ⟨92843, by rfl⟩ : syracuseStep 1980661 = 185687) (by norm_num)
theorem B3012869 : Blo 1760081 3012869 := bbase (se 4 (by rfl) ⟨282456, by rfl⟩ : syracuseStep 3012869 = 564913) (by norm_num)
theorem B3963149 : Blo 1760081 3963149 := bbase (se 3 (by rfl) ⟨743090, by rfl⟩ : syracuseStep 3963149 = 1486181) (by norm_num)
theorem B1980697 : Blo 1760081 1980697 := bbase (se 2 (by rfl) ⟨742761, by rfl⟩ : syracuseStep 1980697 = 1485523) (by norm_num)
theorem B2971957 : Blo 1760081 2971957 := bbase (se 5 (by rfl) ⟨139310, by rfl⟩ : syracuseStep 2971957 = 278621) (by norm_num)
theorem B1980733 : Blo 1760081 1980733 := bbase (se 3 (by rfl) ⟨371387, by rfl⟩ : syracuseStep 1980733 = 742775) (by norm_num)
theorem B5945669 : Blo 1760081 5945669 := bbase (se 4 (by rfl) ⟨557406, by rfl⟩ : syracuseStep 5945669 = 1114813) (by norm_num)
theorem B3963221 : Blo 1760081 3963221 := bbase (se 10 (by rfl) ⟨5805, by rfl⟩ : syracuseStep 3963221 = 11611) (by norm_num)
theorem B1980769 : Blo 1760081 1980769 := bbase (se 2 (by rfl) ⟨742788, by rfl⟩ : syracuseStep 1980769 = 1485577) (by norm_num)
theorem B1980805 : Blo 1760081 1980805 := bbase (se 4 (by rfl) ⟨185700, by rfl⟩ : syracuseStep 1980805 = 371401) (by norm_num)
theorem B2898317 : Blo 1760081 2898317 := bbase (se 3 (by rfl) ⟨543434, by rfl⟩ : syracuseStep 2898317 = 1086869) (by norm_num)
theorem B2972045 : Blo 1760081 2972045 := bbase (se 3 (by rfl) ⟨557258, by rfl⟩ : syracuseStep 2972045 = 1114517) (by norm_num)
theorem B32135573 : Blo 1760081 32135573 := bbase (se 6 (by rfl) ⟨753177, by rfl⟩ : syracuseStep 32135573 = 1506355) (by norm_num)
theorem B3963293 : Blo 1760081 3963293 := bbase (se 3 (by rfl) ⟨743117, by rfl⟩ : syracuseStep 3963293 = 1486235) (by norm_num)
theorem B1980841 : Blo 1760081 1980841 := bbase (se 2 (by rfl) ⟨742815, by rfl⟩ : syracuseStep 1980841 = 1485631) (by norm_num)
theorem B5642693 : Blo 1760081 5642693 := bbase (se 4 (by rfl) ⟨529002, by rfl⟩ : syracuseStep 5642693 = 1058005) (by norm_num)
theorem B1980877 : Blo 1760081 1980877 := bbase (se 3 (by rfl) ⟨371414, by rfl⟩ : syracuseStep 1980877 = 742829) (by norm_num)
theorem B6683093 : Blo 1760081 6683093 := bbase (se 7 (by rfl) ⟨78317, by rfl⟩ : syracuseStep 6683093 = 156635) (by norm_num)
theorem B3963365 : Blo 1760081 3963365 := bbase (se 4 (by rfl) ⟨371565, by rfl⟩ : syracuseStep 3963365 = 743131) (by norm_num)
theorem B1784305 : Blo 1760081 1784305 := bbase (se 2 (by rfl) ⟨669114, by rfl⟩ : syracuseStep 1784305 = 1338229) (by norm_num)
theorem B1980913 : Blo 1760081 1980913 := bbase (se 2 (by rfl) ⟨742842, by rfl⟩ : syracuseStep 1980913 = 1485685) (by norm_num)
theorem B7141877 : Blo 1760081 7141877 := bbase (se 5 (by rfl) ⟨334775, by rfl⟩ : syracuseStep 7141877 = 669551) (by norm_num)
theorem B8919557 : Blo 1760081 8919557 := bbase (se 4 (by rfl) ⟨836208, by rfl⟩ : syracuseStep 8919557 = 1672417) (by norm_num)
theorem B2972173 : Blo 1760081 2972173 := bbase (se 3 (by rfl) ⟨557282, by rfl⟩ : syracuseStep 2972173 = 1114565) (by norm_num)
theorem B1980949 : Blo 1760081 1980949 := bbase (se 6 (by rfl) ⟨46428, by rfl⟩ : syracuseStep 1980949 = 92857) (by norm_num)
theorem B3963437 : Blo 1760081 3963437 := bbase (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) (by norm_num)
theorem B1980985 : Blo 1760081 1980985 := bbase (se 2 (by rfl) ⟨742869, by rfl⟩ : syracuseStep 1980985 = 1485739) (by norm_num)
theorem B1981021 : Blo 1760081 1981021 := bbase (se 3 (by rfl) ⟨371441, by rfl⟩ : syracuseStep 1981021 = 742883) (by norm_num)
theorem B2972261 : Blo 1760081 2972261 := bbase (se 4 (by rfl) ⟨278649, by rfl⟩ : syracuseStep 2972261 = 557299) (by norm_num)
theorem B3963509 : Blo 1760081 3963509 := bbase (se 5 (by rfl) ⟨185789, by rfl⟩ : syracuseStep 3963509 = 371579) (by norm_num)
theorem B1981057 : Blo 1760081 1981057 := bbase (se 2 (by rfl) ⟨742896, by rfl⟩ : syracuseStep 1981057 = 1485793) (by norm_num)
theorem B4291213 : Blo 1760081 4291213 := bbase (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) (by norm_num)
theorem B1981093 : Blo 1760081 1981093 := bbase (se 4 (by rfl) ⟨185727, by rfl⟩ : syracuseStep 1981093 = 371455) (by norm_num)
theorem B3963581 : Blo 1760081 3963581 := bbase (se 3 (by rfl) ⟨743171, by rfl⟩ : syracuseStep 3963581 = 1486343) (by norm_num)
theorem B1981129 : Blo 1760081 1981129 := bbase (se 2 (by rfl) ⟨742923, by rfl⟩ : syracuseStep 1981129 = 1485847) (by norm_num)
theorem B2972389 : Blo 1760081 2972389 := bbase (se 4 (by rfl) ⟨278661, by rfl⟩ : syracuseStep 2972389 = 557323) (by norm_num)
theorem B1981165 : Blo 1760081 1981165 := bbase (se 3 (by rfl) ⟨371468, by rfl⟩ : syracuseStep 1981165 = 742937) (by norm_num)
theorem B6683381 : Blo 1760081 6683381 := bbase (se 5 (by rfl) ⟨313283, by rfl⟩ : syracuseStep 6683381 = 626567) (by norm_num)
theorem B5946101 : Blo 1760081 5946101 := bbase (se 5 (by rfl) ⟨278723, by rfl⟩ : syracuseStep 5946101 = 557447) (by norm_num)
theorem B3963653 : Blo 1760081 3963653 := bbase (se 4 (by rfl) ⟨371592, by rfl⟩ : syracuseStep 3963653 = 743185) (by norm_num)
theorem B1981201 : Blo 1760081 1981201 := bbase (se 2 (by rfl) ⟨742950, by rfl⟩ : syracuseStep 1981201 = 1485901) (by norm_num)
theorem B1981237 : Blo 1760081 1981237 := bbase (se 5 (by rfl) ⟨92870, by rfl⟩ : syracuseStep 1981237 = 185741) (by norm_num)
theorem B2972477 : Blo 1760081 2972477 := bbase (se 3 (by rfl) ⟨557339, by rfl⟩ : syracuseStep 2972477 = 1114679) (by norm_num)
theorem B3963725 : Blo 1760081 3963725 := bbase (se 3 (by rfl) ⟨743198, by rfl⟩ : syracuseStep 3963725 = 1486397) (by norm_num)
theorem B1981273 : Blo 1760081 1981273 := bbase (se 2 (by rfl) ⟨742977, by rfl⟩ : syracuseStep 1981273 = 1485955) (by norm_num)
theorem B1981309 : Blo 1760081 1981309 := bbase (se 3 (by rfl) ⟨371495, by rfl⟩ : syracuseStep 1981309 = 742991) (by norm_num)
theorem B3963797 : Blo 1760081 3963797 := bbase (se 6 (by rfl) ⟨92901, by rfl⟩ : syracuseStep 3963797 = 185803) (by norm_num)
theorem B1981345 : Blo 1760081 1981345 := bbase (se 2 (by rfl) ⟨743004, by rfl⟩ : syracuseStep 1981345 = 1486009) (by norm_num)
theorem B8911781 : Blo 1760081 8911781 := bbase (se 4 (by rfl) ⟨835479, by rfl⟩ : syracuseStep 8911781 = 1670959) (by norm_num)
theorem B2972605 : Blo 1760081 2972605 := bbase (se 3 (by rfl) ⟨557363, by rfl⟩ : syracuseStep 2972605 = 1114727) (by norm_num)
theorem B1981381 : Blo 1760081 1981381 := bbase (se 4 (by rfl) ⟨185754, by rfl⟩ : syracuseStep 1981381 = 371509) (by norm_num)
theorem B3963869 : Blo 1760081 3963869 := bbase (se 3 (by rfl) ⟨743225, by rfl⟩ : syracuseStep 3963869 = 1486451) (by norm_num)
theorem B1981417 : Blo 1760081 1981417 := bbase (se 2 (by rfl) ⟨743031, by rfl⟩ : syracuseStep 1981417 = 1486063) (by norm_num)
theorem B1981453 : Blo 1760081 1981453 := bbase (se 3 (by rfl) ⟨371522, by rfl⟩ : syracuseStep 1981453 = 743045) (by norm_num)
theorem B4455445 : Blo 1760081 4455445 := bbase (se 6 (by rfl) ⟨104424, by rfl⟩ : syracuseStep 4455445 = 208849) (by norm_num)
theorem B2972693 : Blo 1760081 2972693 := bbase (se 6 (by rfl) ⟨69672, by rfl⟩ : syracuseStep 2972693 = 139345) (by norm_num)
theorem B3963941 : Blo 1760081 3963941 := bbase (se 4 (by rfl) ⟨371619, by rfl⟩ : syracuseStep 3963941 = 743239) (by norm_num)
theorem B3013669 : Blo 1760081 3013669 := bbase (se 4 (by rfl) ⟨282531, by rfl⟩ : syracuseStep 3013669 = 565063) (by norm_num)
theorem B1981489 : Blo 1760081 1981489 := bbase (se 2 (by rfl) ⟨743058, by rfl⟩ : syracuseStep 1981489 = 1486117) (by norm_num)
theorem B7519301 : Blo 1760081 7519301 := bbase (se 4 (by rfl) ⟨704934, by rfl⟩ : syracuseStep 7519301 = 1409869) (by norm_num)
theorem B5356613 : Blo 1760081 5356613 := bbase (se 4 (by rfl) ⟨502182, by rfl⟩ : syracuseStep 5356613 = 1004365) (by norm_num)
theorem B4242509 : Blo 1760081 4242509 := bbase (se 3 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 4242509 = 1590941) (by norm_num)
theorem B1981525 : Blo 1760081 1981525 := bbase (se 8 (by rfl) ⟨11610, by rfl⟩ : syracuseStep 1981525 = 23221) (by norm_num)
theorem B2145377 : Blo 1760081 2145377 := bbase (se 2 (by rfl) ⟨804516, by rfl⟩ : syracuseStep 2145377 = 1609033) (by norm_num)
theorem B3964013 : Blo 1760081 3964013 := bbase (se 3 (by rfl) ⟨743252, by rfl⟩ : syracuseStep 3964013 = 1486505) (by norm_num)
theorem B1981561 : Blo 1760081 1981561 := bbase (se 2 (by rfl) ⟨743085, by rfl⟩ : syracuseStep 1981561 = 1486171) (by norm_num)
theorem B4455557 : Blo 1760081 4455557 := bbase (se 4 (by rfl) ⟨417708, by rfl⟩ : syracuseStep 4455557 = 835417) (by norm_num)
theorem B2972821 : Blo 1760081 2972821 := bbase (se 6 (by rfl) ⟨69675, by rfl⟩ : syracuseStep 2972821 = 139351) (by norm_num)
theorem B1981597 : Blo 1760081 1981597 := bbase (se 3 (by rfl) ⟨371549, by rfl⟩ : syracuseStep 1981597 = 743099) (by norm_num)
theorem B5946533 : Blo 1760081 5946533 := bbase (se 4 (by rfl) ⟨557487, by rfl⟩ : syracuseStep 5946533 = 1114975) (by norm_num)
theorem B3964085 : Blo 1760081 3964085 := bbase (se 5 (by rfl) ⟨185816, by rfl⟩ : syracuseStep 3964085 = 371633) (by norm_num)
theorem B1981633 : Blo 1760081 1981633 := bbase (se 2 (by rfl) ⟨743112, by rfl⟩ : syracuseStep 1981633 = 1486225) (by norm_num)
theorem B1981669 : Blo 1760081 1981669 := bbase (se 4 (by rfl) ⟨185781, by rfl⟩ : syracuseStep 1981669 = 371563) (by norm_num)
theorem B2972909 : Blo 1760081 2972909 := bbase (se 3 (by rfl) ⟨557420, by rfl⟩ : syracuseStep 2972909 = 1114841) (by norm_num)
theorem B3964157 : Blo 1760081 3964157 := bbase (se 3 (by rfl) ⟨743279, by rfl⟩ : syracuseStep 3964157 = 1486559) (by norm_num)
theorem B5012741 : Blo 1760081 5012741 := bbase (se 4 (by rfl) ⟨469944, by rfl⟩ : syracuseStep 5012741 = 939889) (by norm_num)
theorem B1981705 : Blo 1760081 1981705 := bbase (se 2 (by rfl) ⟨743139, by rfl⟩ : syracuseStep 1981705 = 1486279) (by norm_num)
theorem B1981741 : Blo 1760081 1981741 := bbase (se 3 (by rfl) ⟨371576, by rfl⟩ : syracuseStep 1981741 = 743153) (by norm_num)
theorem B16932149 : Blo 1760081 16932149 := bbase (se 5 (by rfl) ⟨793694, by rfl⟩ : syracuseStep 16932149 = 1587389) (by norm_num)
theorem B4455749 : Blo 1760081 4455749 := bbase (se 4 (by rfl) ⟨417726, by rfl⟩ : syracuseStep 4455749 = 835453) (by norm_num)
theorem B3964229 : Blo 1760081 3964229 := bbase (se 4 (by rfl) ⟨371646, by rfl⟩ : syracuseStep 3964229 = 743293) (by norm_num)
theorem B3341645 : Blo 1760081 3341645 := bbase (se 3 (by rfl) ⟨626558, by rfl⟩ : syracuseStep 3341645 = 1253117) (by norm_num)
theorem B1981777 : Blo 1760081 1981777 := bbase (se 2 (by rfl) ⟨743166, by rfl⟩ : syracuseStep 1981777 = 1486333) (by norm_num)
theorem B2506069 : Blo 1760081 2506069 := bbase (se 11 (by rfl) ⟨1835, by rfl⟩ : syracuseStep 2506069 = 3671) (by norm_num)
theorem B48192853 : Blo 1760081 48192853 := bbase (se 11 (by rfl) ⟨35297, by rfl⟩ : syracuseStep 48192853 = 70595) (by norm_num)
theorem B2973037 : Blo 1760081 2973037 := bbase (se 3 (by rfl) ⟨557444, by rfl⟩ : syracuseStep 2973037 = 1114889) (by norm_num)
theorem B1981813 : Blo 1760081 1981813 := bbase (se 5 (by rfl) ⟨92897, by rfl⟩ : syracuseStep 1981813 = 185795) (by norm_num)
theorem B10034549 : Blo 1760081 10034549 := bbase (se 5 (by rfl) ⟨470369, by rfl⟩ : syracuseStep 10034549 = 940739) (by norm_num)
theorem B3964301 : Blo 1760081 3964301 := bbase (se 3 (by rfl) ⟨743306, by rfl⟩ : syracuseStep 3964301 = 1486613) (by norm_num)
theorem B1981849 : Blo 1760081 1981849 := bbase (se 2 (by rfl) ⟨743193, by rfl⟩ : syracuseStep 1981849 = 1486387) (by norm_num)
theorem B1785245 : Blo 1760081 1785245 := bbase (se 3 (by rfl) ⟨334733, by rfl⟩ : syracuseStep 1785245 = 669467) (by norm_num)
theorem B1981885 : Blo 1760081 1981885 := bbase (se 3 (by rfl) ⟨371603, by rfl⟩ : syracuseStep 1981885 = 743207) (by norm_num)
theorem B2973125 : Blo 1760081 2973125 := bbase (se 4 (by rfl) ⟨278730, by rfl⟩ : syracuseStep 2973125 = 557461) (by norm_num)
theorem B2227657 : Blo 1760081 2227657 := bbase (se 2 (by rfl) ⟨835371, by rfl⟩ : syracuseStep 2227657 = 1670743) (by norm_num)
theorem B3964373 : Blo 1760081 3964373 := bbase (se 7 (by rfl) ⟨46457, by rfl⟩ : syracuseStep 3964373 = 92915) (by norm_num)
theorem B1981921 : Blo 1760081 1981921 := bbase (se 2 (by rfl) ⟨743220, by rfl⟩ : syracuseStep 1981921 = 1486441) (by norm_num)
theorem B1981957 : Blo 1760081 1981957 := bbase (se 4 (by rfl) ⟨185808, by rfl⟩ : syracuseStep 1981957 = 371617) (by norm_num)
theorem B2260489 : Blo 1760081 2260489 := bbase (se 2 (by rfl) ⟨847683, by rfl⟩ : syracuseStep 2260489 = 1695367) (by norm_num)
theorem B3964445 : Blo 1760081 3964445 := bbase (se 3 (by rfl) ⟨743333, by rfl⟩ : syracuseStep 3964445 = 1486667) (by norm_num)
theorem B2227753 : Blo 1760081 2227753 := bbase (se 2 (by rfl) ⟨835407, by rfl⟩ : syracuseStep 2227753 = 1670815) (by norm_num)
theorem B1981993 : Blo 1760081 1981993 := bbase (se 2 (by rfl) ⟨743247, by rfl⟩ : syracuseStep 1981993 = 1486495) (by norm_num)
theorem B2973253 : Blo 1760081 2973253 := bbase (se 4 (by rfl) ⟨278742, by rfl⟩ : syracuseStep 2973253 = 557485) (by norm_num)
theorem B1982029 : Blo 1760081 1982029 := bbase (se 3 (by rfl) ⟨371630, by rfl⟩ : syracuseStep 1982029 = 743261) (by norm_num)
theorem B5946965 : Blo 1760081 5946965 := bbase (se 8 (by rfl) ⟨34845, by rfl⟩ : syracuseStep 5946965 = 69691) (by norm_num)
theorem B3964517 : Blo 1760081 3964517 := bbase (se 4 (by rfl) ⟨371673, by rfl⟩ : syracuseStep 3964517 = 743347) (by norm_num)
theorem B1982065 : Blo 1760081 1982065 := bbase (se 2 (by rfl) ⟨743274, by rfl⟩ : syracuseStep 1982065 = 1486549) (by norm_num)
theorem B1982101 : Blo 1760081 1982101 := bbase (se 6 (by rfl) ⟨46455, by rfl⟩ : syracuseStep 1982101 = 92911) (by norm_num)
theorem B4456093 : Blo 1760081 4456093 := bbase (se 3 (by rfl) ⟨835517, by rfl⟩ : syracuseStep 4456093 = 1671035) (by norm_num)
theorem B2973341 : Blo 1760081 2973341 := bbase (se 3 (by rfl) ⟨557501, by rfl⟩ : syracuseStep 2973341 = 1115003) (by norm_num)
theorem B2506405 : Blo 1760081 2506405 := bbase (se 4 (by rfl) ⟨234975, by rfl⟩ : syracuseStep 2506405 = 469951) (by norm_num)
theorem B3964589 : Blo 1760081 3964589 := bbase (se 3 (by rfl) ⟨743360, by rfl⟩ : syracuseStep 3964589 = 1486721) (by norm_num)
theorem B12689077 : Blo 1760081 12689077 := bbase (se 5 (by rfl) ⟨594800, by rfl⟩ : syracuseStep 12689077 = 1189601) (by norm_num)
theorem B1982137 : Blo 1760081 1982137 := bbase (se 2 (by rfl) ⟨743301, by rfl⟩ : syracuseStep 1982137 = 1486603) (by norm_num)
theorem B2227925 : Blo 1760081 2227925 := bbase (se 7 (by rfl) ⟨26108, by rfl⟩ : syracuseStep 2227925 = 52217) (by norm_num)
theorem B1982173 : Blo 1760081 1982173 := bbase (se 3 (by rfl) ⟨371657, by rfl⟩ : syracuseStep 1982173 = 743315) (by norm_num)
theorem B3964661 : Blo 1760081 3964661 := bbase (se 5 (by rfl) ⟨185843, by rfl⟩ : syracuseStep 3964661 = 371687) (by norm_num)
theorem B1982209 : Blo 1760081 1982209 := bbase (se 2 (by rfl) ⟨743328, by rfl⟩ : syracuseStep 1982209 = 1486657) (by norm_num)
theorem B2227981 : Blo 1760081 2227981 := bbase (se 3 (by rfl) ⟨417746, by rfl⟩ : syracuseStep 2227981 = 835493) (by norm_num)
theorem B4456205 : Blo 1760081 4456205 := bbase (se 3 (by rfl) ⟨835538, by rfl⟩ : syracuseStep 4456205 = 1671077) (by norm_num)
theorem B2973469 : Blo 1760081 2973469 := bbase (se 3 (by rfl) ⟨557525, by rfl⟩ : syracuseStep 2973469 = 1115051) (by norm_num)
theorem B1982245 : Blo 1760081 1982245 := bbase (se 4 (by rfl) ⟨185835, by rfl⟩ : syracuseStep 1982245 = 371671) (by norm_num)
theorem B11280181 : Blo 1760081 11280181 := bbase (se 5 (by rfl) ⟨528758, by rfl⟩ : syracuseStep 11280181 = 1057517) (by norm_num)
theorem B7143221 : Blo 1760081 7143221 := bbase (se 5 (by rfl) ⟨334838, by rfl⟩ : syracuseStep 7143221 = 669677) (by norm_num)
theorem B1982281 : Blo 1760081 1982281 := bbase (se 2 (by rfl) ⟨743355, by rfl⟩ : syracuseStep 1982281 = 1486711) (by norm_num)
theorem B3759949 : Blo 1760081 3759949 := bbase (se 3 (by rfl) ⟨704990, by rfl⟩ : syracuseStep 3759949 = 1409981) (by norm_num)
theorem B16916309 : Blo 1760081 16916309 := bbase (se 9 (by rfl) ⟨49559, by rfl⟩ : syracuseStep 16916309 = 99119) (by norm_num)
theorem B2228077 : Blo 1760081 2228077 := bbase (se 3 (by rfl) ⟨417764, by rfl⟩ : syracuseStep 2228077 = 835529) (by norm_num)
theorem B1982317 : Blo 1760081 1982317 := bbase (se 3 (by rfl) ⟨371684, by rfl⟩ : syracuseStep 1982317 = 743369) (by norm_num)
theorem B2506621 : Blo 1760081 2506621 := bbase (se 3 (by rfl) ⟨469991, by rfl⟩ : syracuseStep 2506621 = 939983) (by norm_num)
theorem B6684565 : Blo 1760081 6684565 := bbase (se 6 (by rfl) ⟨156669, by rfl⟩ : syracuseStep 6684565 = 313339) (by norm_num)
theorem B4456397 : Blo 1760081 4456397 := bbase (se 3 (by rfl) ⟨835574, by rfl⟩ : syracuseStep 4456397 = 1671149) (by norm_num)
theorem B1761283 : Blo 1760081 1761283 := bstep (se 1 (by rfl) ⟨1320962, by rfl⟩ : syracuseStep 1761283 = 2641925) B2641925
theorem B1761299 : Blo 1760081 1761299 := bstep (se 1 (by rfl) ⟨1320974, by rfl⟩ : syracuseStep 1761299 = 2641949) B2641949
theorem B5013539 : Blo 1760081 5013539 := bstep (se 1 (by rfl) ⟨3760154, by rfl⟩ : syracuseStep 5013539 = 7520309) B7520309
theorem B1761315 : Blo 1760081 1761315 := bstep (se 1 (by rfl) ⟨1320986, by rfl⟩ : syracuseStep 1761315 = 2641973) B2641973
theorem B1761331 : Blo 1760081 1761331 := bstep (se 1 (by rfl) ⟨1320998, by rfl⟩ : syracuseStep 1761331 = 2641997) B2641997
theorem B1761347 : Blo 1760081 1761347 := bstep (se 1 (by rfl) ⟨1321010, by rfl⟩ : syracuseStep 1761347 = 2642021) B2642021
theorem B4456529 : Blo 1760081 4456529 := bstep (se 2 (by rfl) ⟨1671198, by rfl⟩ : syracuseStep 4456529 = 3342397) B3342397
theorem B1761363 : Blo 1760081 1761363 := bstep (se 1 (by rfl) ⟨1321022, by rfl⟩ : syracuseStep 1761363 = 2642045) B2642045
theorem B1761379 : Blo 1760081 1761379 := bstep (se 1 (by rfl) ⟨1321034, by rfl⟩ : syracuseStep 1761379 = 2642069) B2642069
theorem B13377635 : Blo 1760081 13377635 := bstep (se 1 (by rfl) ⟨10033226, by rfl⟩ : syracuseStep 13377635 = 20066453) B20066453
theorem B5644397 : Blo 1760081 5644397 := bstep (se 3 (by rfl) ⟨1058324, by rfl⟩ : syracuseStep 5644397 = 2116649) B2116649
theorem B1761395 : Blo 1760081 1761395 := bstep (se 1 (by rfl) ⟨1321046, by rfl⟩ : syracuseStep 1761395 = 2642093) B2642093
theorem B4456579 : Blo 1760081 4456579 := bstep (se 1 (by rfl) ⟨3342434, by rfl⟩ : syracuseStep 4456579 = 6684869) B6684869
theorem B1761411 : Blo 1760081 1761411 := bstep (se 1 (by rfl) ⟨1321058, by rfl⟩ : syracuseStep 1761411 = 2642117) B2642117
theorem B3760273 : Blo 1760081 3760273 := bstep (se 2 (by rfl) ⟨1410102, by rfl⟩ : syracuseStep 3760273 = 2820205) B2820205
theorem B1761427 : Blo 1760081 1761427 := bstep (se 1 (by rfl) ⟨1321070, by rfl⟩ : syracuseStep 1761427 = 2642141) B2642141
theorem B1761443 : Blo 1760081 1761443 := bstep (se 1 (by rfl) ⟨1321082, by rfl⟩ : syracuseStep 1761443 = 2642165) B2642165
theorem B1761459 : Blo 1760081 1761459 := bstep (se 1 (by rfl) ⟨1321094, by rfl⟩ : syracuseStep 1761459 = 2642189) B2642189
theorem B1761475 : Blo 1760081 1761475 := bstep (se 1 (by rfl) ⟨1321106, by rfl⟩ : syracuseStep 1761475 = 2642213) B2642213
theorem B16072901 : Blo 1760081 16072901 := bstep (se 4 (by rfl) ⟨1506834, by rfl⟩ : syracuseStep 16072901 = 3013669) B3013669
theorem B2506963 : Blo 1760081 2506963 := bstep (se 1 (by rfl) ⟨1880222, by rfl⟩ : syracuseStep 2506963 = 3760445) B3760445
theorem B1761491 : Blo 1760081 1761491 := bstep (se 1 (by rfl) ⟨1321118, by rfl⟩ : syracuseStep 1761491 = 2642237) B2642237
theorem B1761507 : Blo 1760081 1761507 := bstep (se 1 (by rfl) ⟨1321130, by rfl⟩ : syracuseStep 1761507 = 2642261) B2642261
theorem B2228467 : Blo 1760081 2228467 := bstep (se 1 (by rfl) ⟨1671350, by rfl⟩ : syracuseStep 2228467 = 3342701) B3342701
theorem B1761523 : Blo 1760081 1761523 := bstep (se 1 (by rfl) ⟨1321142, by rfl⟩ : syracuseStep 1761523 = 2642285) B2642285
theorem B1761539 : Blo 1760081 1761539 := bstep (se 1 (by rfl) ⟨1321154, by rfl⟩ : syracuseStep 1761539 = 2642309) B2642309
theorem B4456721 : Blo 1760081 4456721 := bstep (se 2 (by rfl) ⟨1671270, by rfl⟩ : syracuseStep 4456721 = 3342541) B3342541
theorem B1761555 : Blo 1760081 1761555 := bstep (se 1 (by rfl) ⟨1321166, by rfl⟩ : syracuseStep 1761555 = 2642333) B2642333
theorem B1761571 : Blo 1760081 1761571 := bstep (se 1 (by rfl) ⟨1321178, by rfl⟩ : syracuseStep 1761571 = 2642357) B2642357
theorem B1761587 : Blo 1760081 1761587 := bstep (se 1 (by rfl) ⟨1321190, by rfl⟩ : syracuseStep 1761587 = 2642381) B2642381
theorem B1761603 : Blo 1760081 1761603 := bstep (se 1 (by rfl) ⟨1321202, by rfl⟩ : syracuseStep 1761603 = 2642405) B2642405
theorem B2228563 : Blo 1760081 2228563 := bstep (se 1 (by rfl) ⟨1671422, by rfl⟩ : syracuseStep 2228563 = 3342845) B3342845
theorem B1761619 : Blo 1760081 1761619 := bstep (se 1 (by rfl) ⟨1321214, by rfl⟩ : syracuseStep 1761619 = 2642429) B2642429
theorem B1761635 : Blo 1760081 1761635 := bstep (se 1 (by rfl) ⟨1321226, by rfl⟩ : syracuseStep 1761635 = 2642453) B2642453
theorem B1761651 : Blo 1760081 1761651 := bstep (se 1 (by rfl) ⟨1321238, by rfl⟩ : syracuseStep 1761651 = 2642477) B2642477
theorem B1761667 : Blo 1760081 1761667 := bstep (se 1 (by rfl) ⟨1321250, by rfl⟩ : syracuseStep 1761667 = 2642501) B2642501
theorem B1761683 : Blo 1760081 1761683 := bstep (se 1 (by rfl) ⟨1321262, by rfl⟩ : syracuseStep 1761683 = 2642525) B2642525
theorem B1761699 : Blo 1760081 1761699 := bstep (se 1 (by rfl) ⟨1321274, by rfl⟩ : syracuseStep 1761699 = 2642549) B2642549
theorem B1761715 : Blo 1760081 1761715 := bstep (se 1 (by rfl) ⟨1321286, by rfl⟩ : syracuseStep 1761715 = 2642573) B2642573
theorem B1761731 : Blo 1760081 1761731 := bstep (se 1 (by rfl) ⟨1321298, by rfl⟩ : syracuseStep 1761731 = 2642597) B2642597
theorem B2859475 : Blo 1760081 2859475 := bstep (se 1 (by rfl) ⟨2144606, by rfl⟩ : syracuseStep 2859475 = 4289213) B4289213
theorem B1761747 : Blo 1760081 1761747 := bstep (se 1 (by rfl) ⟨1321310, by rfl⟩ : syracuseStep 1761747 = 2642621) B2642621
theorem B4579811 : Blo 1760081 4579811 := bstep (se 1 (by rfl) ⟨3434858, by rfl⟩ : syracuseStep 4579811 = 6869717) B6869717
theorem B1761763 : Blo 1760081 1761763 := bstep (se 1 (by rfl) ⟨1321322, by rfl⟩ : syracuseStep 1761763 = 2642645) B2642645
theorem B1761779 : Blo 1760081 1761779 := bstep (se 1 (by rfl) ⟨1321334, by rfl⟩ : syracuseStep 1761779 = 2642669) B2642669
theorem B1761795 : Blo 1760081 1761795 := bstep (se 1 (by rfl) ⟨1321346, by rfl⟩ : syracuseStep 1761795 = 2642693) B2642693
theorem B1761811 : Blo 1760081 1761811 := bstep (se 1 (by rfl) ⟨1321358, by rfl⟩ : syracuseStep 1761811 = 2642717) B2642717
theorem B3342883 : Blo 1760081 3342883 := bstep (se 1 (by rfl) ⟨2507162, by rfl⟩ : syracuseStep 3342883 = 5014325) B5014325
theorem B1761827 : Blo 1760081 1761827 := bstep (se 1 (by rfl) ⟨1321370, by rfl⟩ : syracuseStep 1761827 = 2642741) B2642741
theorem B1761843 : Blo 1760081 1761843 := bstep (se 1 (by rfl) ⟨1321382, by rfl⟩ : syracuseStep 1761843 = 2642765) B2642765
theorem B1761859 : Blo 1760081 1761859 := bstep (se 1 (by rfl) ⟨1321394, by rfl⟩ : syracuseStep 1761859 = 2642789) B2642789
theorem B1761875 : Blo 1760081 1761875 := bstep (se 1 (by rfl) ⟨1321406, by rfl⟩ : syracuseStep 1761875 = 2642813) B2642813
theorem B1761891 : Blo 1760081 1761891 := bstep (se 1 (by rfl) ⟨1321418, by rfl⟩ : syracuseStep 1761891 = 2642837) B2642837
theorem B1761907 : Blo 1760081 1761907 := bstep (se 1 (by rfl) ⟨1321430, by rfl⟩ : syracuseStep 1761907 = 2642861) B2642861
theorem B1761923 : Blo 1760081 1761923 := bstep (se 1 (by rfl) ⟨1321442, by rfl⟩ : syracuseStep 1761923 = 2642885) B2642885
theorem B6685325 : Blo 1760081 6685325 := bstep (se 3 (by rfl) ⟨1253498, by rfl⟩ : syracuseStep 6685325 = 2506997) B2506997
theorem B1761939 : Blo 1760081 1761939 := bstep (se 1 (by rfl) ⟨1321454, by rfl⟩ : syracuseStep 1761939 = 2642909) B2642909
theorem B1761955 : Blo 1760081 1761955 := bstep (se 1 (by rfl) ⟨1321466, by rfl⟩ : syracuseStep 1761955 = 2642933) B2642933
theorem B2507441 : Blo 1760081 2507441 := bstep (se 2 (by rfl) ⟨940290, by rfl⟩ : syracuseStep 2507441 = 1880581) B1880581
theorem B5358257 : Blo 1760081 5358257 := bstep (se 2 (by rfl) ⟨2009346, by rfl⟩ : syracuseStep 5358257 = 4018693) B4018693
theorem B1761971 : Blo 1760081 1761971 := bstep (se 1 (by rfl) ⟨1321478, by rfl⟩ : syracuseStep 1761971 = 2642957) B2642957
theorem B1761987 : Blo 1760081 1761987 := bstep (se 1 (by rfl) ⟨1321490, by rfl⟩ : syracuseStep 1761987 = 2642981) B2642981
theorem B1762003 : Blo 1760081 1762003 := bstep (se 1 (by rfl) ⟨1321502, by rfl⟩ : syracuseStep 1762003 = 2643005) B2643005
theorem B1762019 : Blo 1760081 1762019 := bstep (se 1 (by rfl) ⟨1321514, by rfl⟩ : syracuseStep 1762019 = 2643029) B2643029
theorem B1762035 : Blo 1760081 1762035 := bstep (se 1 (by rfl) ⟨1321526, by rfl⟩ : syracuseStep 1762035 = 2643053) B2643053
theorem B1762051 : Blo 1760081 1762051 := bstep (se 1 (by rfl) ⟨1321538, by rfl⟩ : syracuseStep 1762051 = 2643077) B2643077
theorem B1762067 : Blo 1760081 1762067 := bstep (se 1 (by rfl) ⟨1321550, by rfl⟩ : syracuseStep 1762067 = 2643101) B2643101
theorem B2507555 : Blo 1760081 2507555 := bstep (se 1 (by rfl) ⟨1880666, by rfl⟩ : syracuseStep 2507555 = 3761333) B3761333
theorem B2229059 : Blo 1760081 2229059 := bstep (se 1 (by rfl) ⟨1671794, by rfl⟩ : syracuseStep 2229059 = 3343589) B3343589
theorem B2204515 : Blo 1760081 2204515 := bstep (se 1 (by rfl) ⟨1653386, by rfl⟩ : syracuseStep 2204515 = 3306773) B3306773
theorem B5014381 : Blo 1760081 5014381 := bstep (se 3 (by rfl) ⟨940196, by rfl⟩ : syracuseStep 5014381 = 1880393) B1880393
theorem B2507635 : Blo 1760081 2507635 := bstep (se 1 (by rfl) ⟨1880726, by rfl⟩ : syracuseStep 2507635 = 3761453) B3761453
theorem B3343331 : Blo 1760081 3343331 := bstep (se 1 (by rfl) ⟨2507498, by rfl⟩ : syracuseStep 3343331 = 5014997) B5014997
theorem B5014541 : Blo 1760081 5014541 := bstep (se 3 (by rfl) ⟨940226, by rfl⟩ : syracuseStep 5014541 = 1880453) B1880453
theorem B5940323 : Blo 1760081 5940323 := bstep (se 1 (by rfl) ⟨4455242, by rfl⟩ : syracuseStep 5940323 = 8910485) B8910485
theorem B4826243 : Blo 1760081 4826243 := bstep (se 1 (by rfl) ⟨3619682, by rfl⟩ : syracuseStep 4826243 = 7239365) B7239365
theorem B12698765 : Blo 1760081 12698765 := bstep (se 3 (by rfl) ⟨2381018, by rfl⟩ : syracuseStep 12698765 = 4762037) B4762037
theorem B10708145 : Blo 1760081 10708145 := bstep (se 2 (by rfl) ⟨4015554, by rfl⟩ : syracuseStep 10708145 = 8031109) B8031109
theorem B5014723 : Blo 1760081 5014723 := bstep (se 1 (by rfl) ⟨3761042, by rfl⟩ : syracuseStep 5014723 = 7522085) B7522085
theorem B4457713 : Blo 1760081 4457713 := bstep (se 2 (by rfl) ⟨1671642, by rfl⟩ : syracuseStep 4457713 = 3343285) B3343285
theorem B3343619 : Blo 1760081 3343619 := bstep (se 1 (by rfl) ⟨2507714, by rfl⟩ : syracuseStep 3343619 = 5015429) B5015429
theorem B8914211 : Blo 1760081 8914211 := bstep (se 1 (by rfl) ⟨6685658, by rfl⟩ : syracuseStep 8914211 = 13371317) B13371317
theorem B5940593 : Blo 1760081 5940593 := bstep (se 2 (by rfl) ⟨2227722, by rfl⟩ : syracuseStep 5940593 = 4455445) B4455445
theorem B2508193 : Blo 1760081 2508193 := bstep (se 2 (by rfl) ⟨940572, by rfl⟩ : syracuseStep 2508193 = 1881145) B1881145
theorem B2819539 : Blo 1760081 2819539 := bstep (se 1 (by rfl) ⟨2114654, by rfl⟩ : syracuseStep 2819539 = 4229309) B4229309
theorem B2819585 : Blo 1760081 2819585 := bstep (se 2 (by rfl) ⟨1057344, by rfl⟩ : syracuseStep 2819585 = 2114689) B2114689
theorem B4457987 : Blo 1760081 4457987 := bstep (se 1 (by rfl) ⟨3343490, by rfl⟩ : syracuseStep 4457987 = 6686981) B6686981
theorem B2229763 : Blo 1760081 2229763 := bstep (se 1 (by rfl) ⟨1672322, by rfl⟩ : syracuseStep 2229763 = 3344645) B3344645
theorem B2229859 : Blo 1760081 2229859 := bstep (se 1 (by rfl) ⟨1672394, by rfl⟩ : syracuseStep 2229859 = 3344789) B3344789
theorem B3761777 : Blo 1760081 3761777 := bstep (se 2 (by rfl) ⟨1410666, by rfl⟩ : syracuseStep 3761777 = 2821333) B2821333
theorem B3761795 : Blo 1760081 3761795 := bstep (se 1 (by rfl) ⟨2821346, by rfl⟩ : syracuseStep 3761795 = 5642693) B5642693
theorem B4761251 : Blo 1760081 4761251 := bstep (se 1 (by rfl) ⟨3570938, by rfl⟩ : syracuseStep 4761251 = 7141877) B7141877
theorem B4458179 : Blo 1760081 4458179 := bstep (se 1 (by rfl) ⟨3343634, by rfl⟩ : syracuseStep 4458179 = 6687269) B6687269
theorem B6022961 : Blo 1760081 6022961 := bstep (se 2 (by rfl) ⟨2258610, by rfl⟩ : syracuseStep 6022961 = 4517221) B4517221
theorem B5941133 : Blo 1760081 5941133 := bstep (se 3 (by rfl) ⟨1113962, by rfl⟩ : syracuseStep 5941133 = 2227925) B2227925
theorem B3172241 : Blo 1760081 3172241 := bstep (se 2 (by rfl) ⟨1189590, by rfl⟩ : syracuseStep 3172241 = 2379181) B2379181
theorem B5941187 : Blo 1760081 5941187 := bstep (se 1 (by rfl) ⟨4455890, by rfl⟩ : syracuseStep 5941187 = 8911781) B8911781
theorem B16918541 : Blo 1760081 16918541 := bstep (se 3 (by rfl) ⟨3172226, by rfl⟩ : syracuseStep 16918541 = 6344453) B6344453
theorem B2828339 : Blo 1760081 2828339 := bstep (se 1 (by rfl) ⟨2121254, by rfl⟩ : syracuseStep 2828339 = 4242509) B4242509
theorem B8915021 : Blo 1760081 8915021 := bstep (se 3 (by rfl) ⟨1671566, by rfl⟩ : syracuseStep 8915021 = 3343133) B3343133
theorem B2508899 : Blo 1760081 2508899 := bstep (se 1 (by rfl) ⟨1881674, by rfl⟩ : syracuseStep 2508899 = 3763349) B3763349
theorem B3344561 : Blo 1760081 3344561 := bstep (se 2 (by rfl) ⟨1254210, by rfl⟩ : syracuseStep 3344561 = 2508421) B2508421
theorem B5941457 : Blo 1760081 5941457 := bstep (se 2 (by rfl) ⟨2228046, by rfl⟩ : syracuseStep 5941457 = 4456093) B4456093
theorem B4229347 : Blo 1760081 4229347 := bstep (se 1 (by rfl) ⟨3172010, by rfl⟩ : syracuseStep 4229347 = 6344021) B6344021
theorem B16918769 : Blo 1760081 16918769 := bstep (se 2 (by rfl) ⟨6344538, by rfl⟩ : syracuseStep 16918769 = 12689077) B12689077
theorem B2640131 : Blo 1760081 2640131 := bstep (se 1 (by rfl) ⟨1980098, by rfl⟩ : syracuseStep 2640131 = 3960197) B3960197
theorem B2640161 : Blo 1760081 2640161 := bstep (se 2 (by rfl) ⟨990060, by rfl⟩ : syracuseStep 2640161 = 1980121) B1980121
theorem B2640179 : Blo 1760081 2640179 := bstep (se 1 (by rfl) ⟨1980134, by rfl⟩ : syracuseStep 2640179 = 3960269) B3960269
theorem B2640209 : Blo 1760081 2640209 := bstep (se 2 (by rfl) ⟨990078, by rfl⟩ : syracuseStep 2640209 = 1980157) B1980157
theorem B2640227 : Blo 1760081 2640227 := bstep (se 1 (by rfl) ⟨1980170, by rfl⟩ : syracuseStep 2640227 = 3960341) B3960341
theorem B2640257 : Blo 1760081 2640257 := bstep (se 2 (by rfl) ⟨990096, by rfl⟩ : syracuseStep 2640257 = 1980193) B1980193
theorem B2640275 : Blo 1760081 2640275 := bstep (se 1 (by rfl) ⟨1980206, by rfl⟩ : syracuseStep 2640275 = 3960413) B3960413
theorem B2640305 : Blo 1760081 2640305 := bstep (se 2 (by rfl) ⟨990114, by rfl⟩ : syracuseStep 2640305 = 1980229) B1980229
theorem B2640323 : Blo 1760081 2640323 := bstep (se 1 (by rfl) ⟨1980242, by rfl⟩ : syracuseStep 2640323 = 3960485) B3960485
theorem B2820577 : Blo 1760081 2820577 := bstep (se 2 (by rfl) ⟨1057716, by rfl⟩ : syracuseStep 2820577 = 2115433) B2115433
theorem B2640353 : Blo 1760081 2640353 := bstep (se 2 (by rfl) ⟨990132, by rfl⟩ : syracuseStep 2640353 = 1980265) B1980265
theorem B2640371 : Blo 1760081 2640371 := bstep (se 1 (by rfl) ⟨1980278, by rfl⟩ : syracuseStep 2640371 = 3960557) B3960557
theorem B2640401 : Blo 1760081 2640401 := bstep (se 2 (by rfl) ⟨990150, by rfl⟩ : syracuseStep 2640401 = 1980301) B1980301
theorem B2640419 : Blo 1760081 2640419 := bstep (se 1 (by rfl) ⟨1980314, by rfl⟩ : syracuseStep 2640419 = 3960629) B3960629
theorem B4762147 : Blo 1760081 4762147 := bstep (se 1 (by rfl) ⟨3571610, by rfl⟩ : syracuseStep 4762147 = 7143221) B7143221
theorem B5016113 : Blo 1760081 5016113 := bstep (se 2 (by rfl) ⟨1881042, by rfl⟩ : syracuseStep 5016113 = 3762085) B3762085
theorem B2640449 : Blo 1760081 2640449 := bstep (se 2 (by rfl) ⟨990168, by rfl⟩ : syracuseStep 2640449 = 1980337) B1980337
theorem B2640467 : Blo 1760081 2640467 := bstep (se 1 (by rfl) ⟨1980350, by rfl⟩ : syracuseStep 2640467 = 3960701) B3960701
theorem B2640497 : Blo 1760081 2640497 := bstep (se 2 (by rfl) ⟨990186, by rfl⟩ : syracuseStep 2640497 = 1980373) B1980373
theorem B4459121 : Blo 1760081 4459121 := bstep (se 2 (by rfl) ⟨1672170, by rfl⟩ : syracuseStep 4459121 = 3344341) B3344341
theorem B2116211 : Blo 1760081 2116211 := bstep (se 1 (by rfl) ⟨1587158, by rfl⟩ : syracuseStep 2116211 = 3174317) B3174317
theorem B2640515 : Blo 1760081 2640515 := bstep (se 1 (by rfl) ⟨1980386, by rfl⟩ : syracuseStep 2640515 = 3960773) B3960773
theorem B12044933 : Blo 1760081 12044933 := bstep (se 4 (by rfl) ⟨1129212, by rfl⟩ : syracuseStep 12044933 = 2258425) B2258425
theorem B2640545 : Blo 1760081 2640545 := bstep (se 2 (by rfl) ⟨990204, by rfl⟩ : syracuseStep 2640545 = 1980409) B1980409
theorem B4459171 : Blo 1760081 4459171 := bstep (se 1 (by rfl) ⟨3344378, by rfl⟩ : syracuseStep 4459171 = 6688757) B6688757
theorem B2640563 : Blo 1760081 2640563 := bstep (se 1 (by rfl) ⟨1980422, by rfl⟩ : syracuseStep 2640563 = 3960845) B3960845
theorem B2640593 : Blo 1760081 2640593 := bstep (se 2 (by rfl) ⟨990222, by rfl⟩ : syracuseStep 2640593 = 1980445) B1980445
theorem B2640611 : Blo 1760081 2640611 := bstep (se 1 (by rfl) ⟨1980458, by rfl⟩ : syracuseStep 2640611 = 3960917) B3960917
theorem B20064995 : Blo 1760081 20064995 := bstep (se 1 (by rfl) ⟨15048746, by rfl⟩ : syracuseStep 20064995 = 30097493) B30097493
theorem B5941997 : Blo 1760081 5941997 := bstep (se 3 (by rfl) ⟨1114124, by rfl⟩ : syracuseStep 5941997 = 2228249) B2228249
theorem B2640641 : Blo 1760081 2640641 := bstep (se 2 (by rfl) ⟨990240, by rfl⟩ : syracuseStep 2640641 = 1980481) B1980481
theorem B7138061 : Blo 1760081 7138061 := bstep (se 3 (by rfl) ⟨1338386, by rfl⟩ : syracuseStep 7138061 = 2676773) B2676773
theorem B2640659 : Blo 1760081 2640659 := bstep (se 1 (by rfl) ⟨1980494, by rfl⟩ : syracuseStep 2640659 = 3960989) B3960989
theorem B5942051 : Blo 1760081 5942051 := bstep (se 1 (by rfl) ⟨4456538, by rfl⟩ : syracuseStep 5942051 = 8913077) B8913077
theorem B2640689 : Blo 1760081 2640689 := bstep (se 2 (by rfl) ⟨990258, by rfl⟩ : syracuseStep 2640689 = 1980517) B1980517
theorem B4459313 : Blo 1760081 4459313 := bstep (se 2 (by rfl) ⟨1672242, by rfl⟩ : syracuseStep 4459313 = 3344485) B3344485
theorem B2640707 : Blo 1760081 2640707 := bstep (se 1 (by rfl) ⟨1980530, by rfl⟩ : syracuseStep 2640707 = 3961061) B3961061
theorem B2640737 : Blo 1760081 2640737 := bstep (se 2 (by rfl) ⟨990276, by rfl⟩ : syracuseStep 2640737 = 1980553) B1980553
theorem B2640755 : Blo 1760081 2640755 := bstep (se 1 (by rfl) ⟨1980566, by rfl⟩ : syracuseStep 2640755 = 3961133) B3961133
theorem B2640785 : Blo 1760081 2640785 := bstep (se 2 (by rfl) ⟨990294, by rfl⟩ : syracuseStep 2640785 = 1980589) B1980589
theorem B2821025 : Blo 1760081 2821025 := bstep (se 2 (by rfl) ⟨1057884, by rfl⟩ : syracuseStep 2821025 = 2115769) B2115769
theorem B2640803 : Blo 1760081 2640803 := bstep (se 1 (by rfl) ⟨1980602, by rfl⟩ : syracuseStep 2640803 = 3961205) B3961205
theorem B4017059 : Blo 1760081 4017059 := bstep (se 1 (by rfl) ⟨3012794, by rfl⟩ : syracuseStep 4017059 = 6025589) B6025589
theorem B5721005 : Blo 1760081 5721005 := bstep (se 3 (by rfl) ⟨1072688, by rfl⟩ : syracuseStep 5721005 = 2145377) B2145377
theorem B2640833 : Blo 1760081 2640833 := bstep (se 2 (by rfl) ⟨990312, by rfl⟩ : syracuseStep 2640833 = 1980625) B1980625
theorem B2640851 : Blo 1760081 2640851 := bstep (se 1 (by rfl) ⟨1980638, by rfl⟩ : syracuseStep 2640851 = 3961277) B3961277
theorem B5499875 : Blo 1760081 5499875 := bstep (se 1 (by rfl) ⟨4124906, by rfl⟩ : syracuseStep 5499875 = 8249813) B8249813
theorem B2640881 : Blo 1760081 2640881 := bstep (se 2 (by rfl) ⟨990330, by rfl⟩ : syracuseStep 2640881 = 1980661) B1980661
theorem B2640899 : Blo 1760081 2640899 := bstep (se 1 (by rfl) ⟨1980674, by rfl⟩ : syracuseStep 2640899 = 3961349) B3961349
theorem B2640929 : Blo 1760081 2640929 := bstep (se 2 (by rfl) ⟨990348, by rfl⟩ : syracuseStep 2640929 = 1980697) B1980697
theorem B5942321 : Blo 1760081 5942321 := bstep (se 2 (by rfl) ⟨2228370, by rfl⟩ : syracuseStep 5942321 = 4456741) B4456741
theorem B2640947 : Blo 1760081 2640947 := bstep (se 1 (by rfl) ⟨1980710, by rfl⟩ : syracuseStep 2640947 = 3961421) B3961421
theorem B2640977 : Blo 1760081 2640977 := bstep (se 2 (by rfl) ⟨990366, by rfl⟩ : syracuseStep 2640977 = 1980733) B1980733
theorem B2640995 : Blo 1760081 2640995 := bstep (se 1 (by rfl) ⟨1980746, by rfl⟩ : syracuseStep 2640995 = 3961493) B3961493
theorem B2641025 : Blo 1760081 2641025 := bstep (se 2 (by rfl) ⟨990384, by rfl⟩ : syracuseStep 2641025 = 1980769) B1980769
theorem B2641043 : Blo 1760081 2641043 := bstep (se 1 (by rfl) ⟨1980782, by rfl⟩ : syracuseStep 2641043 = 3961565) B3961565
theorem B3173539 : Blo 1760081 3173539 := bstep (se 1 (by rfl) ⟨2380154, by rfl⟩ : syracuseStep 3173539 = 4760309) B4760309
theorem B2641073 : Blo 1760081 2641073 := bstep (se 2 (by rfl) ⟨990402, by rfl⟩ : syracuseStep 2641073 = 1980805) B1980805
theorem B2641091 : Blo 1760081 2641091 := bstep (se 1 (by rfl) ⟨1980818, by rfl⟩ : syracuseStep 2641091 = 3961637) B3961637
theorem B2641121 : Blo 1760081 2641121 := bstep (se 2 (by rfl) ⟨990420, by rfl⟩ : syracuseStep 2641121 = 1980841) B1980841
theorem B3435761 : Blo 1760081 3435761 := bstep (se 2 (by rfl) ⟨1288410, by rfl⟩ : syracuseStep 3435761 = 2576821) B2576821
theorem B2641139 : Blo 1760081 2641139 := bstep (se 1 (by rfl) ⟨1980854, by rfl⟩ : syracuseStep 2641139 = 3961709) B3961709
theorem B2641169 : Blo 1760081 2641169 := bstep (se 2 (by rfl) ⟨990438, by rfl⟩ : syracuseStep 2641169 = 1980877) B1980877
theorem B2641187 : Blo 1760081 2641187 := bstep (se 1 (by rfl) ⟨1980890, by rfl⟩ : syracuseStep 2641187 = 3961781) B3961781
theorem B2288947 : Blo 1760081 2288947 := bstep (se 1 (by rfl) ⟨1716710, by rfl⟩ : syracuseStep 2288947 = 3433421) B3433421
theorem B2379073 : Blo 1760081 2379073 := bstep (se 2 (by rfl) ⟨892152, by rfl⟩ : syracuseStep 2379073 = 1784305) B1784305
theorem B2641217 : Blo 1760081 2641217 := bstep (se 2 (by rfl) ⟨990456, by rfl⟩ : syracuseStep 2641217 = 1980913) B1980913
theorem B2641235 : Blo 1760081 2641235 := bstep (se 1 (by rfl) ⟨1980926, by rfl⟩ : syracuseStep 2641235 = 3961853) B3961853
theorem B4762979 : Blo 1760081 4762979 := bstep (se 1 (by rfl) ⟨3572234, by rfl⟩ : syracuseStep 4762979 = 7144469) B7144469
theorem B2641265 : Blo 1760081 2641265 := bstep (se 2 (by rfl) ⟨990474, by rfl⟩ : syracuseStep 2641265 = 1980949) B1980949
theorem B2641283 : Blo 1760081 2641283 := bstep (se 1 (by rfl) ⟨1980962, by rfl⟩ : syracuseStep 2641283 = 3961925) B3961925
theorem B7523725 : Blo 1760081 7523725 := bstep (se 3 (by rfl) ⟨1410698, by rfl⟩ : syracuseStep 7523725 = 2821397) B2821397
theorem B2641313 : Blo 1760081 2641313 := bstep (se 2 (by rfl) ⟨990492, by rfl⟩ : syracuseStep 2641313 = 1980985) B1980985
theorem B4230577 : Blo 1760081 4230577 := bstep (se 2 (by rfl) ⟨1586466, by rfl⟩ : syracuseStep 4230577 = 3172933) B3172933
theorem B2641331 : Blo 1760081 2641331 := bstep (se 1 (by rfl) ⟨1980998, by rfl⟩ : syracuseStep 2641331 = 3961997) B3961997
theorem B2641361 : Blo 1760081 2641361 := bstep (se 2 (by rfl) ⟨990510, by rfl⟩ : syracuseStep 2641361 = 1981021) B1981021
theorem B2641379 : Blo 1760081 2641379 := bstep (se 1 (by rfl) ⟨1981034, by rfl⟩ : syracuseStep 2641379 = 3962069) B3962069
theorem B24440291 : Blo 1760081 24440291 := bstep (se 1 (by rfl) ⟨18330218, by rfl⟩ : syracuseStep 24440291 = 36660437) B36660437
theorem B5017069 : Blo 1760081 5017069 := bstep (se 3 (by rfl) ⟨940700, by rfl⟩ : syracuseStep 5017069 = 1881401) B1881401
theorem B3960305 : Blo 1760081 3960305 := bstep (se 2 (by rfl) ⟨1485114, by rfl⟩ : syracuseStep 3960305 = 2970229) B2970229
theorem B6688241 : Blo 1760081 6688241 := bstep (se 2 (by rfl) ⟨2508090, by rfl⟩ : syracuseStep 6688241 = 5016181) B5016181
theorem B2641409 : Blo 1760081 2641409 := bstep (se 2 (by rfl) ⟨990528, by rfl⟩ : syracuseStep 2641409 = 1981057) B1981057
theorem B3960323 : Blo 1760081 3960323 := bstep (se 1 (by rfl) ⟨2970242, by rfl⟩ : syracuseStep 3960323 = 5940485) B5940485
theorem B15052301 : Blo 1760081 15052301 := bstep (se 3 (by rfl) ⟨2822306, by rfl⟩ : syracuseStep 15052301 = 5644613) B5644613
theorem B5721617 : Blo 1760081 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B2641427 : Blo 1760081 2641427 := bstep (se 1 (by rfl) ⟨1981070, by rfl⟩ : syracuseStep 2641427 = 3962141) B3962141
theorem B2641457 : Blo 1760081 2641457 := bstep (se 2 (by rfl) ⟨990546, by rfl⟩ : syracuseStep 2641457 = 1981093) B1981093
theorem B2641475 : Blo 1760081 2641475 := bstep (se 1 (by rfl) ⟨1981106, by rfl⟩ : syracuseStep 2641475 = 3962213) B3962213
theorem B5942861 : Blo 1760081 5942861 := bstep (se 3 (by rfl) ⟨1114286, by rfl⟩ : syracuseStep 5942861 = 2228573) B2228573
theorem B2641505 : Blo 1760081 2641505 := bstep (se 2 (by rfl) ⟨990564, by rfl⟩ : syracuseStep 2641505 = 1981129) B1981129
theorem B2641523 : Blo 1760081 2641523 := bstep (se 1 (by rfl) ⟨1981142, by rfl⟩ : syracuseStep 2641523 = 3962285) B3962285
theorem B4517507 : Blo 1760081 4517507 := bstep (se 1 (by rfl) ⟨3388130, by rfl⟩ : syracuseStep 4517507 = 6776261) B6776261
theorem B5942915 : Blo 1760081 5942915 := bstep (se 1 (by rfl) ⟨4457186, by rfl⟩ : syracuseStep 5942915 = 8914373) B8914373
theorem B15044237 : Blo 1760081 15044237 := bstep (se 3 (by rfl) ⟨2820794, by rfl⟩ : syracuseStep 15044237 = 5641589) B5641589
theorem B2641553 : Blo 1760081 2641553 := bstep (se 2 (by rfl) ⟨990582, by rfl⟩ : syracuseStep 2641553 = 1981165) B1981165
theorem B2641571 : Blo 1760081 2641571 := bstep (se 1 (by rfl) ⟨1981178, by rfl⟩ : syracuseStep 2641571 = 3962357) B3962357
theorem B2641601 : Blo 1760081 2641601 := bstep (se 2 (by rfl) ⟨990600, by rfl⟩ : syracuseStep 2641601 = 1981201) B1981201
theorem B5017297 : Blo 1760081 5017297 := bstep (se 2 (by rfl) ⟨1881486, by rfl⟩ : syracuseStep 5017297 = 3762973) B3762973
theorem B2641619 : Blo 1760081 2641619 := bstep (se 1 (by rfl) ⟨1981214, by rfl⟩ : syracuseStep 2641619 = 3962429) B3962429
theorem B3174115 : Blo 1760081 3174115 := bstep (se 1 (by rfl) ⟨2380586, by rfl⟩ : syracuseStep 3174115 = 4761173) B4761173
theorem B2641649 : Blo 1760081 2641649 := bstep (se 2 (by rfl) ⟨990618, by rfl⟩ : syracuseStep 2641649 = 1981237) B1981237
theorem B1879795 : Blo 1760081 1879795 := bstep (se 1 (by rfl) ⟨1409846, by rfl⟩ : syracuseStep 1879795 = 2819693) B2819693
theorem B2641667 : Blo 1760081 2641667 := bstep (se 1 (by rfl) ⟨1981250, by rfl⟩ : syracuseStep 2641667 = 3962501) B3962501
theorem B2821891 : Blo 1760081 2821891 := bstep (se 1 (by rfl) ⟨2116418, by rfl⟩ : syracuseStep 2821891 = 4232837) B4232837
theorem B5426957 : Blo 1760081 5426957 := bstep (se 3 (by rfl) ⟨1017554, by rfl⟩ : syracuseStep 5426957 = 2035109) B2035109
theorem B3960593 : Blo 1760081 3960593 := bstep (se 2 (by rfl) ⟨1485222, by rfl⟩ : syracuseStep 3960593 = 2970445) B2970445
theorem B2641697 : Blo 1760081 2641697 := bstep (se 2 (by rfl) ⟨990636, by rfl⟩ : syracuseStep 2641697 = 1981273) B1981273
theorem B3960611 : Blo 1760081 3960611 := bstep (se 1 (by rfl) ⟨2970458, by rfl⟩ : syracuseStep 3960611 = 5940917) B5940917
theorem B5082925 : Blo 1760081 5082925 := bstep (se 3 (by rfl) ⟨953048, by rfl⟩ : syracuseStep 5082925 = 1906097) B1906097
theorem B2641715 : Blo 1760081 2641715 := bstep (se 1 (by rfl) ⟨1981286, by rfl⟩ : syracuseStep 2641715 = 3962573) B3962573
theorem B13553477 : Blo 1760081 13553477 := bstep (se 4 (by rfl) ⟨1270638, by rfl⟩ : syracuseStep 13553477 = 2541277) B2541277
theorem B15249221 : Blo 1760081 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B2641745 : Blo 1760081 2641745 := bstep (se 2 (by rfl) ⟨990654, by rfl⟩ : syracuseStep 2641745 = 1981309) B1981309
theorem B13553507 : Blo 1760081 13553507 := bstep (se 1 (by rfl) ⟨10165130, by rfl⟩ : syracuseStep 13553507 = 20330261) B20330261
theorem B2641763 : Blo 1760081 2641763 := bstep (se 1 (by rfl) ⟨1981322, by rfl⟩ : syracuseStep 2641763 = 3962645) B3962645
theorem B5017457 : Blo 1760081 5017457 := bstep (se 2 (by rfl) ⟨1881546, by rfl⟩ : syracuseStep 5017457 = 3763093) B3763093
theorem B2641793 : Blo 1760081 2641793 := bstep (se 2 (by rfl) ⟨990672, by rfl⟩ : syracuseStep 2641793 = 1981345) B1981345
theorem B5943185 : Blo 1760081 5943185 := bstep (se 2 (by rfl) ⟨2228694, by rfl⟩ : syracuseStep 5943185 = 4457389) B4457389
theorem B2641811 : Blo 1760081 2641811 := bstep (se 1 (by rfl) ⟨1981358, by rfl⟩ : syracuseStep 2641811 = 3962717) B3962717
theorem B2641841 : Blo 1760081 2641841 := bstep (se 2 (by rfl) ⟨990690, by rfl⟩ : syracuseStep 2641841 = 1981381) B1981381
theorem B2641859 : Blo 1760081 2641859 := bstep (se 1 (by rfl) ⟨1981394, by rfl⟩ : syracuseStep 2641859 = 3962789) B3962789
theorem B4018115 : Blo 1760081 4018115 := bstep (se 1 (by rfl) ⟨3013586, by rfl⟩ : syracuseStep 4018115 = 6027173) B6027173
theorem B2641889 : Blo 1760081 2641889 := bstep (se 2 (by rfl) ⟨990708, by rfl⟩ : syracuseStep 2641889 = 1981417) B1981417
theorem B5017571 : Blo 1760081 5017571 := bstep (se 1 (by rfl) ⟨3763178, by rfl⟩ : syracuseStep 5017571 = 7526357) B7526357
theorem B2641907 : Blo 1760081 2641907 := bstep (se 1 (by rfl) ⟨1981430, by rfl⟩ : syracuseStep 2641907 = 3962861) B3962861
theorem B5640205 : Blo 1760081 5640205 := bstep (se 3 (by rfl) ⟨1057538, by rfl⟩ : syracuseStep 5640205 = 2115077) B2115077
theorem B2641937 : Blo 1760081 2641937 := bstep (se 2 (by rfl) ⟨990726, by rfl⟩ : syracuseStep 2641937 = 1981453) B1981453
theorem B2641955 : Blo 1760081 2641955 := bstep (se 1 (by rfl) ⟨1981466, by rfl⟩ : syracuseStep 2641955 = 3962933) B3962933
theorem B3960881 : Blo 1760081 3960881 := bstep (se 2 (by rfl) ⟨1485330, by rfl⟩ : syracuseStep 3960881 = 2970661) B2970661
theorem B2641985 : Blo 1760081 2641985 := bstep (se 2 (by rfl) ⟨990744, by rfl⟩ : syracuseStep 2641985 = 1981489) B1981489
theorem B3960899 : Blo 1760081 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B2642003 : Blo 1760081 2642003 := bstep (se 1 (by rfl) ⟨1981502, by rfl⟩ : syracuseStep 2642003 = 3963005) B3963005
theorem B15036515 : Blo 1760081 15036515 := bstep (se 1 (by rfl) ⟨11277386, by rfl⟩ : syracuseStep 15036515 = 22554773) B22554773
theorem B2642033 : Blo 1760081 2642033 := bstep (se 2 (by rfl) ⟨990762, by rfl⟩ : syracuseStep 2642033 = 1981525) B1981525
theorem B2642051 : Blo 1760081 2642051 := bstep (se 1 (by rfl) ⟨1981538, by rfl⟩ : syracuseStep 2642051 = 3963077) B3963077
theorem B2642081 : Blo 1760081 2642081 := bstep (se 2 (by rfl) ⟨990780, by rfl⟩ : syracuseStep 2642081 = 1981561) B1981561
theorem B2642099 : Blo 1760081 2642099 := bstep (se 1 (by rfl) ⟨1981574, by rfl⟩ : syracuseStep 2642099 = 3963149) B3963149
theorem B2642129 : Blo 1760081 2642129 := bstep (se 2 (by rfl) ⟨990798, by rfl⟩ : syracuseStep 2642129 = 1981597) B1981597
theorem B2642147 : Blo 1760081 2642147 := bstep (se 1 (by rfl) ⟨1981610, by rfl⟩ : syracuseStep 2642147 = 3963221) B3963221
theorem B2642177 : Blo 1760081 2642177 := bstep (se 2 (by rfl) ⟨990816, by rfl⟩ : syracuseStep 2642177 = 1981633) B1981633
theorem B2642195 : Blo 1760081 2642195 := bstep (se 1 (by rfl) ⟨1981646, by rfl⟩ : syracuseStep 2642195 = 3963293) B3963293
theorem B2642225 : Blo 1760081 2642225 := bstep (se 2 (by rfl) ⟨990834, by rfl⟩ : syracuseStep 2642225 = 1981669) B1981669
theorem B19042613 : Blo 1760081 19042613 := bstep (se 5 (by rfl) ⟨892622, by rfl⟩ : syracuseStep 19042613 = 1785245) B1785245
theorem B2642243 : Blo 1760081 2642243 := bstep (se 1 (by rfl) ⟨1981682, by rfl⟩ : syracuseStep 2642243 = 3963365) B3963365
theorem B3961169 : Blo 1760081 3961169 := bstep (se 2 (by rfl) ⟨1485438, by rfl⟩ : syracuseStep 3961169 = 2970877) B2970877
theorem B2642273 : Blo 1760081 2642273 := bstep (se 2 (by rfl) ⟨990852, by rfl⟩ : syracuseStep 2642273 = 1981705) B1981705
theorem B3961187 : Blo 1760081 3961187 := bstep (se 1 (by rfl) ⟨2970890, by rfl⟩ : syracuseStep 3961187 = 5941781) B5941781
theorem B2642291 : Blo 1760081 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B2642321 : Blo 1760081 2642321 := bstep (se 2 (by rfl) ⟨990870, by rfl⟩ : syracuseStep 2642321 = 1981741) B1981741
theorem B2642339 : Blo 1760081 2642339 := bstep (se 1 (by rfl) ⟨1981754, by rfl⟩ : syracuseStep 2642339 = 3963509) B3963509
theorem B5943725 : Blo 1760081 5943725 := bstep (se 3 (by rfl) ⟨1114448, by rfl⟩ : syracuseStep 5943725 = 2228897) B2228897
theorem B2642369 : Blo 1760081 2642369 := bstep (se 2 (by rfl) ⟨990888, by rfl⟩ : syracuseStep 2642369 = 1981777) B1981777
theorem B2642387 : Blo 1760081 2642387 := bstep (se 1 (by rfl) ⟨1981790, by rfl⟩ : syracuseStep 2642387 = 3963581) B3963581
theorem B5943779 : Blo 1760081 5943779 := bstep (se 1 (by rfl) ⟨4457834, by rfl⟩ : syracuseStep 5943779 = 8915669) B8915669
theorem B2642417 : Blo 1760081 2642417 := bstep (se 2 (by rfl) ⟨990906, by rfl⟩ : syracuseStep 2642417 = 1981813) B1981813
theorem B2642435 : Blo 1760081 2642435 := bstep (se 1 (by rfl) ⟨1981826, by rfl⟩ : syracuseStep 2642435 = 3963653) B3963653
theorem B2642465 : Blo 1760081 2642465 := bstep (se 2 (by rfl) ⟨990924, by rfl⟩ : syracuseStep 2642465 = 1981849) B1981849
theorem B2642483 : Blo 1760081 2642483 := bstep (se 1 (by rfl) ⟨1981862, by rfl⟩ : syracuseStep 2642483 = 3963725) B3963725
theorem B6107729 : Blo 1760081 6107729 := bstep (se 2 (by rfl) ⟨2290398, by rfl⟩ : syracuseStep 6107729 = 4580797) B4580797
theorem B2642513 : Blo 1760081 2642513 := bstep (se 2 (by rfl) ⟨990942, by rfl⟩ : syracuseStep 2642513 = 1981885) B1981885
theorem B2970209 : Blo 1760081 2970209 := bstep (se 2 (by rfl) ⟨1113828, by rfl⟩ : syracuseStep 2970209 = 2227657) B2227657
theorem B2642531 : Blo 1760081 2642531 := bstep (se 1 (by rfl) ⟨1981898, by rfl⟩ : syracuseStep 2642531 = 3963797) B3963797
theorem B3961457 : Blo 1760081 3961457 := bstep (se 2 (by rfl) ⟨1485546, by rfl⟩ : syracuseStep 3961457 = 2971093) B2971093
theorem B2642561 : Blo 1760081 2642561 := bstep (se 2 (by rfl) ⟨990960, by rfl⟩ : syracuseStep 2642561 = 1981921) B1981921
theorem B3961475 : Blo 1760081 3961475 := bstep (se 1 (by rfl) ⟨2971106, by rfl⟩ : syracuseStep 3961475 = 5942213) B5942213
theorem B2642579 : Blo 1760081 2642579 := bstep (se 1 (by rfl) ⟨1981934, by rfl⟩ : syracuseStep 2642579 = 3963869) B3963869
theorem B2642609 : Blo 1760081 2642609 := bstep (se 2 (by rfl) ⟨990978, by rfl⟩ : syracuseStep 2642609 = 1981957) B1981957
theorem B2642627 : Blo 1760081 2642627 := bstep (se 1 (by rfl) ⟨1981970, by rfl⟩ : syracuseStep 2642627 = 3963941) B3963941
theorem B2970337 : Blo 1760081 2970337 := bstep (se 2 (by rfl) ⟨1113876, by rfl⟩ : syracuseStep 2970337 = 2227753) B2227753
theorem B2642657 : Blo 1760081 2642657 := bstep (se 2 (by rfl) ⟨990996, by rfl⟩ : syracuseStep 2642657 = 1981993) B1981993
theorem B1880803 : Blo 1760081 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B5944049 : Blo 1760081 5944049 := bstep (se 2 (by rfl) ⟨2229018, by rfl⟩ : syracuseStep 5944049 = 4458037) B4458037
theorem B2642675 : Blo 1760081 2642675 := bstep (se 1 (by rfl) ⟨1982006, by rfl⟩ : syracuseStep 2642675 = 3964013) B3964013
theorem B2970371 : Blo 1760081 2970371 := bstep (se 1 (by rfl) ⟨2227778, by rfl⟩ : syracuseStep 2970371 = 4455557) B4455557
theorem B2642705 : Blo 1760081 2642705 := bstep (se 2 (by rfl) ⟨991014, by rfl⟩ : syracuseStep 2642705 = 1982029) B1982029
theorem B2642723 : Blo 1760081 2642723 := bstep (se 1 (by rfl) ⟨1982042, by rfl⟩ : syracuseStep 2642723 = 3964085) B3964085
theorem B2642753 : Blo 1760081 2642753 := bstep (se 2 (by rfl) ⟨991032, by rfl⟩ : syracuseStep 2642753 = 1982065) B1982065
theorem B2642771 : Blo 1760081 2642771 := bstep (se 1 (by rfl) ⟨1982078, by rfl⟩ : syracuseStep 2642771 = 3964157) B3964157
theorem B2642801 : Blo 1760081 2642801 := bstep (se 2 (by rfl) ⟨991050, by rfl⟩ : syracuseStep 2642801 = 1982101) B1982101
theorem B2970499 : Blo 1760081 2970499 := bstep (se 1 (by rfl) ⟨2227874, by rfl⟩ : syracuseStep 2970499 = 4455749) B4455749
theorem B2642819 : Blo 1760081 2642819 := bstep (se 1 (by rfl) ⟨1982114, by rfl⟩ : syracuseStep 2642819 = 3964229) B3964229
theorem B77190029 : Blo 1760081 77190029 := bstep (se 3 (by rfl) ⟨14473130, by rfl⟩ : syracuseStep 77190029 = 28946261) B28946261
theorem B3961745 : Blo 1760081 3961745 := bstep (se 2 (by rfl) ⟨1485654, by rfl⟩ : syracuseStep 3961745 = 2971309) B2971309
theorem B2642849 : Blo 1760081 2642849 := bstep (se 2 (by rfl) ⟨991068, by rfl⟩ : syracuseStep 2642849 = 1982137) B1982137
theorem B3961763 : Blo 1760081 3961763 := bstep (se 1 (by rfl) ⟨2971322, by rfl⟩ : syracuseStep 3961763 = 5942645) B5942645
theorem B6689699 : Blo 1760081 6689699 := bstep (se 1 (by rfl) ⟨5017274, by rfl⟩ : syracuseStep 6689699 = 10034549) B10034549
theorem B8917937 : Blo 1760081 8917937 := bstep (se 2 (by rfl) ⟨3344226, by rfl⟩ : syracuseStep 8917937 = 6688453) B6688453
theorem B2642867 : Blo 1760081 2642867 := bstep (se 1 (by rfl) ⟨1982150, by rfl⟩ : syracuseStep 2642867 = 3964301) B3964301
theorem B2642897 : Blo 1760081 2642897 := bstep (se 2 (by rfl) ⟨991086, by rfl⟩ : syracuseStep 2642897 = 1982173) B1982173
theorem B2642915 : Blo 1760081 2642915 := bstep (se 1 (by rfl) ⟨1982186, by rfl⟩ : syracuseStep 2642915 = 3964373) B3964373
theorem B2642945 : Blo 1760081 2642945 := bstep (se 2 (by rfl) ⟨991104, by rfl⟩ : syracuseStep 2642945 = 1982209) B1982209
theorem B10032133 : Blo 1760081 10032133 := bstep (se 4 (by rfl) ⟨940512, by rfl⟩ : syracuseStep 10032133 = 1881025) B1881025
theorem B16503821 : Blo 1760081 16503821 := bstep (se 3 (by rfl) ⟨3094466, by rfl⟩ : syracuseStep 16503821 = 6188933) B6188933
theorem B2970641 : Blo 1760081 2970641 := bstep (se 2 (by rfl) ⟨1113990, by rfl⟩ : syracuseStep 2970641 = 2227981) B2227981
theorem B2642963 : Blo 1760081 2642963 := bstep (se 1 (by rfl) ⟨1982222, by rfl⟩ : syracuseStep 2642963 = 3964445) B3964445
theorem B2642993 : Blo 1760081 2642993 := bstep (se 2 (by rfl) ⟨991122, by rfl⟩ : syracuseStep 2642993 = 1982245) B1982245
theorem B2643011 : Blo 1760081 2643011 := bstep (se 1 (by rfl) ⟨1982258, by rfl⟩ : syracuseStep 2643011 = 3964517) B3964517
theorem B2643041 : Blo 1760081 2643041 := bstep (se 2 (by rfl) ⟨991140, by rfl⟩ : syracuseStep 2643041 = 1982281) B1982281
theorem B2643059 : Blo 1760081 2643059 := bstep (se 1 (by rfl) ⟨1982294, by rfl⟩ : syracuseStep 2643059 = 3964589) B3964589
theorem B2970769 : Blo 1760081 2970769 := bstep (se 2 (by rfl) ⟨1114038, by rfl⟩ : syracuseStep 2970769 = 2228077) B2228077
theorem B2643089 : Blo 1760081 2643089 := bstep (se 2 (by rfl) ⟨991158, by rfl⟩ : syracuseStep 2643089 = 1982317) B1982317
theorem B2643107 : Blo 1760081 2643107 := bstep (se 1 (by rfl) ⟨1982330, by rfl⟩ : syracuseStep 2643107 = 3964661) B3964661
theorem B3962033 : Blo 1760081 3962033 := bstep (se 2 (by rfl) ⟨1485762, by rfl⟩ : syracuseStep 3962033 = 2971525) B2971525
theorem B8139953 : Blo 1760081 8139953 := bstep (se 2 (by rfl) ⟨3052482, by rfl⟩ : syracuseStep 8139953 = 6104965) B6104965
theorem B2970803 : Blo 1760081 2970803 := bstep (se 1 (by rfl) ⟨2228102, by rfl⟩ : syracuseStep 2970803 = 4456205) B4456205
theorem B3962051 : Blo 1760081 3962051 := bstep (se 1 (by rfl) ⟨2971538, by rfl⟩ : syracuseStep 3962051 = 5943077) B5943077
theorem B11277539 : Blo 1760081 11277539 := bstep (se 1 (by rfl) ⟨8458154, by rfl⟩ : syracuseStep 11277539 = 16916309) B16916309
theorem B5944589 : Blo 1760081 5944589 := bstep (se 3 (by rfl) ⟨1114610, by rfl⟩ : syracuseStep 5944589 = 2229221) B2229221
theorem B2970931 : Blo 1760081 2970931 := bstep (se 1 (by rfl) ⟨2228198, by rfl⟩ : syracuseStep 2970931 = 4456397) B4456397
theorem B5944643 : Blo 1760081 5944643 := bstep (se 1 (by rfl) ⟨4458482, by rfl⟩ : syracuseStep 5944643 = 8916965) B8916965
theorem B6346097 : Blo 1760081 6346097 := bstep (se 2 (by rfl) ⟨2379786, by rfl⟩ : syracuseStep 6346097 = 4759573) B4759573
theorem B2971073 : Blo 1760081 2971073 := bstep (se 2 (by rfl) ⟨1114152, by rfl⟩ : syracuseStep 2971073 = 2228305) B2228305
theorem B42866117 : Blo 1760081 42866117 := bstep (se 4 (by rfl) ⟨4018698, by rfl⟩ : syracuseStep 42866117 = 8037397) B8037397
theorem B5354957 : Blo 1760081 5354957 := bstep (se 3 (by rfl) ⟨1004054, by rfl⟩ : syracuseStep 5354957 = 2008109) B2008109
theorem B3962321 : Blo 1760081 3962321 := bstep (se 2 (by rfl) ⟨1485870, by rfl⟩ : syracuseStep 3962321 = 2971741) B2971741
theorem B3962339 : Blo 1760081 3962339 := bstep (se 1 (by rfl) ⟨2971754, by rfl⟩ : syracuseStep 3962339 = 5943509) B5943509
theorem B2971201 : Blo 1760081 2971201 := bstep (se 2 (by rfl) ⟨1114200, by rfl⟩ : syracuseStep 2971201 = 2228401) B2228401
theorem B6108739 : Blo 1760081 6108739 := bstep (se 1 (by rfl) ⟨4581554, by rfl⟩ : syracuseStep 6108739 = 9163109) B9163109
theorem B5944913 : Blo 1760081 5944913 := bstep (se 2 (by rfl) ⟨2229342, by rfl⟩ : syracuseStep 5944913 = 4458685) B4458685
theorem B2971235 : Blo 1760081 2971235 := bstep (se 1 (by rfl) ⟨2228426, by rfl⟩ : syracuseStep 2971235 = 4456853) B4456853
theorem B5641937 : Blo 1760081 5641937 := bstep (se 2 (by rfl) ⟨2115726, by rfl⟩ : syracuseStep 5641937 = 4231453) B4231453
theorem B2971363 : Blo 1760081 2971363 := bstep (se 1 (by rfl) ⟨2228522, by rfl⟩ : syracuseStep 2971363 = 4457045) B4457045
theorem B3962609 : Blo 1760081 3962609 := bstep (se 2 (by rfl) ⟨1485978, by rfl⟩ : syracuseStep 3962609 = 2971957) B2971957
theorem B3962627 : Blo 1760081 3962627 := bstep (se 1 (by rfl) ⟨2971970, by rfl⟩ : syracuseStep 3962627 = 5943941) B5943941
theorem B1980211 : Blo 1760081 1980211 := bstep (se 1 (by rfl) ⟨1485158, by rfl⟩ : syracuseStep 1980211 = 2970317) B2970317
theorem B2971505 : Blo 1760081 2971505 := bstep (se 2 (by rfl) ⟨1114314, by rfl⟩ : syracuseStep 2971505 = 2228629) B2228629
theorem B1980355 : Blo 1760081 1980355 := bstep (se 1 (by rfl) ⟨1485266, by rfl⟩ : syracuseStep 1980355 = 2970533) B2970533
theorem B8574947 : Blo 1760081 8574947 := bstep (se 1 (by rfl) ⟨6431210, by rfl⟩ : syracuseStep 8574947 = 12862421) B12862421
theorem B9517027 : Blo 1760081 9517027 := bstep (se 1 (by rfl) ⟨7137770, by rfl⟩ : syracuseStep 9517027 = 14275541) B14275541
theorem B2971633 : Blo 1760081 2971633 := bstep (se 2 (by rfl) ⟨1114362, by rfl⟩ : syracuseStep 2971633 = 2228725) B2228725
theorem B8034317 : Blo 1760081 8034317 := bstep (se 3 (by rfl) ⟨1506434, by rfl⟩ : syracuseStep 8034317 = 3012869) B3012869
theorem B3962897 : Blo 1760081 3962897 := bstep (se 2 (by rfl) ⟨1486086, by rfl⟩ : syracuseStep 3962897 = 2972173) B2972173
theorem B2971667 : Blo 1760081 2971667 := bstep (se 1 (by rfl) ⟨2228750, by rfl⟩ : syracuseStep 2971667 = 4457501) B4457501
theorem B3962915 : Blo 1760081 3962915 := bstep (se 1 (by rfl) ⟨2972186, by rfl⟩ : syracuseStep 3962915 = 5944373) B5944373
theorem B1980499 : Blo 1760081 1980499 := bstep (se 1 (by rfl) ⟨1485374, by rfl⟩ : syracuseStep 1980499 = 2970749) B2970749
theorem B3012707 : Blo 1760081 3012707 := bstep (se 1 (by rfl) ⟨2259530, by rfl⟩ : syracuseStep 3012707 = 4519061) B4519061
theorem B5945453 : Blo 1760081 5945453 := bstep (se 3 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 5945453 = 2229545) B2229545
theorem B2971795 : Blo 1760081 2971795 := bstep (se 1 (by rfl) ⟨2228846, by rfl⟩ : syracuseStep 2971795 = 4457693) B4457693
theorem B5945507 : Blo 1760081 5945507 := bstep (se 1 (by rfl) ⟨4459130, by rfl⟩ : syracuseStep 5945507 = 8918261) B8918261
theorem B11278541 : Blo 1760081 11278541 := bstep (se 3 (by rfl) ⟨2114726, by rfl⟩ : syracuseStep 11278541 = 4229453) B4229453
theorem B1980643 : Blo 1760081 1980643 := bstep (se 1 (by rfl) ⟨1485482, by rfl⟩ : syracuseStep 1980643 = 2970965) B2970965
theorem B2971937 : Blo 1760081 2971937 := bstep (se 2 (by rfl) ⟨1114476, by rfl⟩ : syracuseStep 2971937 = 2228953) B2228953
theorem B3963185 : Blo 1760081 3963185 := bstep (se 2 (by rfl) ⟨1486194, by rfl⟩ : syracuseStep 3963185 = 2972389) B2972389
theorem B5642563 : Blo 1760081 5642563 := bstep (se 1 (by rfl) ⟨4231922, by rfl⟩ : syracuseStep 5642563 = 8463845) B8463845
theorem B3963203 : Blo 1760081 3963203 := bstep (se 1 (by rfl) ⟨2972402, by rfl⟩ : syracuseStep 3963203 = 5944805) B5944805
theorem B8919395 : Blo 1760081 8919395 := bstep (se 1 (by rfl) ⟨6689546, by rfl⟩ : syracuseStep 8919395 = 13379093) B13379093
theorem B1980787 : Blo 1760081 1980787 := bstep (se 1 (by rfl) ⟨1485590, by rfl⟩ : syracuseStep 1980787 = 2971181) B2971181
theorem B85694861 : Blo 1760081 85694861 := bstep (se 3 (by rfl) ⟨16067786, by rfl⟩ : syracuseStep 85694861 = 32135573) B32135573
theorem B2677139 : Blo 1760081 2677139 := bstep (se 1 (by rfl) ⟨2007854, by rfl⟩ : syracuseStep 2677139 = 4015709) B4015709
theorem B2972065 : Blo 1760081 2972065 := bstep (se 2 (by rfl) ⟨1114524, by rfl⟩ : syracuseStep 2972065 = 2229049) B2229049
theorem B2144675 : Blo 1760081 2144675 := bstep (se 1 (by rfl) ⟨1608506, by rfl⟩ : syracuseStep 2144675 = 3217013) B3217013
theorem B5945777 : Blo 1760081 5945777 := bstep (se 2 (by rfl) ⟨2229666, by rfl⟩ : syracuseStep 5945777 = 4459333) B4459333
theorem B2972099 : Blo 1760081 2972099 := bstep (se 1 (by rfl) ⟨2229074, by rfl⟩ : syracuseStep 2972099 = 4458149) B4458149
theorem B6683107 : Blo 1760081 6683107 := bstep (se 1 (by rfl) ⟨5012330, by rfl⟩ : syracuseStep 6683107 = 10024661) B10024661
theorem B11287025 : Blo 1760081 11287025 := bstep (se 2 (by rfl) ⟨4232634, by rfl⟩ : syracuseStep 11287025 = 8465269) B8465269
theorem B1980931 : Blo 1760081 1980931 := bstep (se 1 (by rfl) ⟨1485698, by rfl⟩ : syracuseStep 1980931 = 2971397) B2971397
theorem B2972227 : Blo 1760081 2972227 := bstep (se 1 (by rfl) ⟨2229170, by rfl⟩ : syracuseStep 2972227 = 4458341) B4458341
theorem B3963473 : Blo 1760081 3963473 := bstep (se 2 (by rfl) ⟨1486302, by rfl⟩ : syracuseStep 3963473 = 2972605) B2972605
theorem B3963491 : Blo 1760081 3963491 := bstep (se 1 (by rfl) ⟨2972618, by rfl⟩ : syracuseStep 3963491 = 5945237) B5945237
theorem B1784467 : Blo 1760081 1784467 := bstep (se 1 (by rfl) ⟨1338350, by rfl⟩ : syracuseStep 1784467 = 2676701) B2676701
theorem B1981075 : Blo 1760081 1981075 := bstep (se 1 (by rfl) ⟨1485806, by rfl⟩ : syracuseStep 1981075 = 2971613) B2971613
theorem B12049073 : Blo 1760081 12049073 := bstep (se 2 (by rfl) ⟨4518402, by rfl⟩ : syracuseStep 12049073 = 9036805) B9036805
theorem B2972369 : Blo 1760081 2972369 := bstep (se 2 (by rfl) ⟨1114638, by rfl⟩ : syracuseStep 2972369 = 2229277) B2229277
theorem B1981219 : Blo 1760081 1981219 := bstep (se 1 (by rfl) ⟨1485914, by rfl⟩ : syracuseStep 1981219 = 2971829) B2971829
theorem B2972497 : Blo 1760081 2972497 := bstep (se 2 (by rfl) ⟨1114686, by rfl⟩ : syracuseStep 2972497 = 2229373) B2229373
theorem B1760083 : Blo 1760081 1760083 := bstep (se 1 (by rfl) ⟨1320062, by rfl⟩ : syracuseStep 1760083 = 2640125) B2640125
theorem B1760099 : Blo 1760081 1760099 := bstep (se 1 (by rfl) ⟨1320074, by rfl⟩ : syracuseStep 1760099 = 2640149) B2640149
theorem B3963761 : Blo 1760081 3963761 := bstep (se 2 (by rfl) ⟨1486410, by rfl⟩ : syracuseStep 3963761 = 2972821) B2972821
theorem B1760115 : Blo 1760081 1760115 := bstep (se 1 (by rfl) ⟨1320086, by rfl⟩ : syracuseStep 1760115 = 2640173) B2640173
theorem B2677619 : Blo 1760081 2677619 := bstep (se 1 (by rfl) ⟨2008214, by rfl⟩ : syracuseStep 2677619 = 4016429) B4016429
theorem B2972531 : Blo 1760081 2972531 := bstep (se 1 (by rfl) ⟨2229398, by rfl⟩ : syracuseStep 2972531 = 4458797) B4458797
theorem B1760131 : Blo 1760081 1760131 := bstep (se 1 (by rfl) ⟨1320098, by rfl⟩ : syracuseStep 1760131 = 2640197) B2640197
theorem B3963779 : Blo 1760081 3963779 := bstep (se 1 (by rfl) ⟨2972834, by rfl⟩ : syracuseStep 3963779 = 5945669) B5945669
theorem B1760147 : Blo 1760081 1760147 := bstep (se 1 (by rfl) ⟨1320110, by rfl⟩ : syracuseStep 1760147 = 2640221) B2640221
theorem B1760163 : Blo 1760081 1760163 := bstep (se 1 (by rfl) ⟨1320122, by rfl⟩ : syracuseStep 1760163 = 2640245) B2640245
theorem B1760179 : Blo 1760081 1760179 := bstep (se 1 (by rfl) ⟨1320134, by rfl⟩ : syracuseStep 1760179 = 2640269) B2640269
theorem B1932211 : Blo 1760081 1932211 := bstep (se 1 (by rfl) ⟨1449158, by rfl⟩ : syracuseStep 1932211 = 2898317) B2898317
theorem B1981363 : Blo 1760081 1981363 := bstep (se 1 (by rfl) ⟨1486022, by rfl⟩ : syracuseStep 1981363 = 2972045) B2972045
theorem B1760195 : Blo 1760081 1760195 := bstep (se 1 (by rfl) ⟨1320146, by rfl⟩ : syracuseStep 1760195 = 2640293) B2640293
theorem B10034117 : Blo 1760081 10034117 := bstep (se 4 (by rfl) ⟨940698, by rfl⟩ : syracuseStep 10034117 = 1881397) B1881397
theorem B5946317 : Blo 1760081 5946317 := bstep (se 3 (by rfl) ⟨1114934, by rfl⟩ : syracuseStep 5946317 = 2229869) B2229869
theorem B1760211 : Blo 1760081 1760211 := bstep (se 1 (by rfl) ⟨1320158, by rfl⟩ : syracuseStep 1760211 = 2640317) B2640317
theorem B4455395 : Blo 1760081 4455395 := bstep (se 1 (by rfl) ⟨3341546, by rfl⟩ : syracuseStep 4455395 = 6683093) B6683093
theorem B1760227 : Blo 1760081 1760227 := bstep (se 1 (by rfl) ⟨1320170, by rfl⟩ : syracuseStep 1760227 = 2640341) B2640341
theorem B1760243 : Blo 1760081 1760243 := bstep (se 1 (by rfl) ⟨1320182, by rfl⟩ : syracuseStep 1760243 = 2640365) B2640365
theorem B2972659 : Blo 1760081 2972659 := bstep (se 1 (by rfl) ⟨2229494, by rfl⟩ : syracuseStep 2972659 = 4458989) B4458989
theorem B1760259 : Blo 1760081 1760259 := bstep (se 1 (by rfl) ⟨1320194, by rfl⟩ : syracuseStep 1760259 = 2640389) B2640389
theorem B5946371 : Blo 1760081 5946371 := bstep (se 1 (by rfl) ⟨4459778, by rfl⟩ : syracuseStep 5946371 = 8919557) B8919557
theorem B1760275 : Blo 1760081 1760275 := bstep (se 1 (by rfl) ⟨1320206, by rfl⟩ : syracuseStep 1760275 = 2640413) B2640413
theorem B1760291 : Blo 1760081 1760291 := bstep (se 1 (by rfl) ⟨1320218, by rfl⟩ : syracuseStep 1760291 = 2640437) B2640437
theorem B1760307 : Blo 1760081 1760307 := bstep (se 1 (by rfl) ⟨1320230, by rfl⟩ : syracuseStep 1760307 = 2640461) B2640461
theorem B1760323 : Blo 1760081 1760323 := bstep (se 1 (by rfl) ⟨1320242, by rfl⟩ : syracuseStep 1760323 = 2640485) B2640485
theorem B1981507 : Blo 1760081 1981507 := bstep (se 1 (by rfl) ⟨1486130, by rfl⟩ : syracuseStep 1981507 = 2972261) B2972261
theorem B3619921 : Blo 1760081 3619921 := bstep (se 2 (by rfl) ⟨1357470, by rfl⟩ : syracuseStep 3619921 = 2714941) B2714941
theorem B1760339 : Blo 1760081 1760339 := bstep (se 1 (by rfl) ⟨1320254, by rfl⟩ : syracuseStep 1760339 = 2640509) B2640509
theorem B1760355 : Blo 1760081 1760355 := bstep (se 1 (by rfl) ⟨1320266, by rfl⟩ : syracuseStep 1760355 = 2640533) B2640533
theorem B3341425 : Blo 1760081 3341425 := bstep (se 2 (by rfl) ⟨1253034, by rfl⟩ : syracuseStep 3341425 = 2506069) B2506069
theorem B64257137 : Blo 1760081 64257137 := bstep (se 2 (by rfl) ⟨24096426, by rfl⟩ : syracuseStep 64257137 = 48192853) B48192853
theorem B1760371 : Blo 1760081 1760371 := bstep (se 1 (by rfl) ⟨1320278, by rfl⟩ : syracuseStep 1760371 = 2640557) B2640557
theorem B12696689 : Blo 1760081 12696689 := bstep (se 2 (by rfl) ⟨4761258, by rfl⟩ : syracuseStep 12696689 = 9522517) B9522517
theorem B2972801 : Blo 1760081 2972801 := bstep (se 2 (by rfl) ⟨1114800, by rfl⟩ : syracuseStep 2972801 = 2229601) B2229601
theorem B1760387 : Blo 1760081 1760387 := bstep (se 1 (by rfl) ⟨1320290, by rfl⟩ : syracuseStep 1760387 = 2640581) B2640581
theorem B8920205 : Blo 1760081 8920205 := bstep (se 3 (by rfl) ⟨1672538, by rfl⟩ : syracuseStep 8920205 = 3345077) B3345077
theorem B3964049 : Blo 1760081 3964049 := bstep (se 2 (by rfl) ⟨1486518, by rfl⟩ : syracuseStep 3964049 = 2973037) B2973037
theorem B1760403 : Blo 1760081 1760403 := bstep (se 1 (by rfl) ⟨1320302, by rfl⟩ : syracuseStep 1760403 = 2640605) B2640605
theorem B4455587 : Blo 1760081 4455587 := bstep (se 1 (by rfl) ⟨3341690, by rfl⟩ : syracuseStep 4455587 = 6683381) B6683381
theorem B1760419 : Blo 1760081 1760419 := bstep (se 1 (by rfl) ⟨1320314, by rfl⟩ : syracuseStep 1760419 = 2640629) B2640629
theorem B3964067 : Blo 1760081 3964067 := bstep (se 1 (by rfl) ⟨2973050, by rfl⟩ : syracuseStep 3964067 = 5946101) B5946101
theorem B1760435 : Blo 1760081 1760435 := bstep (se 1 (by rfl) ⟨1320326, by rfl⟩ : syracuseStep 1760435 = 2640653) B2640653
theorem B1760451 : Blo 1760081 1760451 := bstep (se 1 (by rfl) ⟨1320338, by rfl⟩ : syracuseStep 1760451 = 2640677) B2640677
theorem B1760467 : Blo 1760081 1760467 := bstep (se 1 (by rfl) ⟨1320350, by rfl⟩ : syracuseStep 1760467 = 2640701) B2640701
theorem B1981651 : Blo 1760081 1981651 := bstep (se 1 (by rfl) ⟨1486238, by rfl⟩ : syracuseStep 1981651 = 2972477) B2972477
theorem B1760483 : Blo 1760081 1760483 := bstep (se 1 (by rfl) ⟨1320362, by rfl⟩ : syracuseStep 1760483 = 2640725) B2640725
theorem B1760499 : Blo 1760081 1760499 := bstep (se 1 (by rfl) ⟨1320374, by rfl⟩ : syracuseStep 1760499 = 2640749) B2640749
theorem B2972929 : Blo 1760081 2972929 := bstep (se 2 (by rfl) ⟨1114848, by rfl⟩ : syracuseStep 2972929 = 2229697) B2229697
theorem B1760515 : Blo 1760081 1760515 := bstep (se 1 (by rfl) ⟨1320386, by rfl⟩ : syracuseStep 1760515 = 2640773) B2640773
theorem B5946641 : Blo 1760081 5946641 := bstep (se 2 (by rfl) ⟨2229990, by rfl⟩ : syracuseStep 5946641 = 4459981) B4459981
theorem B1760531 : Blo 1760081 1760531 := bstep (se 1 (by rfl) ⟨1320398, by rfl⟩ : syracuseStep 1760531 = 2640797) B2640797
theorem B1760547 : Blo 1760081 1760547 := bstep (se 1 (by rfl) ⟨1320410, by rfl⟩ : syracuseStep 1760547 = 2640821) B2640821
theorem B2972963 : Blo 1760081 2972963 := bstep (se 1 (by rfl) ⟨2229722, by rfl⟩ : syracuseStep 2972963 = 4459445) B4459445
theorem B1760563 : Blo 1760081 1760563 := bstep (se 1 (by rfl) ⟨1320422, by rfl⟩ : syracuseStep 1760563 = 2640845) B2640845
theorem B1760579 : Blo 1760081 1760579 := bstep (se 1 (by rfl) ⟨1320434, by rfl⟩ : syracuseStep 1760579 = 2640869) B2640869
theorem B1760595 : Blo 1760081 1760595 := bstep (se 1 (by rfl) ⟨1320446, by rfl⟩ : syracuseStep 1760595 = 2640893) B2640893
theorem B3013985 : Blo 1760081 3013985 := bstep (se 2 (by rfl) ⟨1130244, by rfl⟩ : syracuseStep 3013985 = 2260489) B2260489
theorem B1760611 : Blo 1760081 1760611 := bstep (se 1 (by rfl) ⟨1320458, by rfl⟩ : syracuseStep 1760611 = 2640917) B2640917
theorem B1981795 : Blo 1760081 1981795 := bstep (se 1 (by rfl) ⟨1486346, by rfl⟩ : syracuseStep 1981795 = 2972693) B2972693
theorem B2506097 : Blo 1760081 2506097 := bstep (se 2 (by rfl) ⟨939786, by rfl⟩ : syracuseStep 2506097 = 1879573) B1879573
theorem B1760627 : Blo 1760081 1760627 := bstep (se 1 (by rfl) ⟨1320470, by rfl⟩ : syracuseStep 1760627 = 2640941) B2640941
theorem B5012867 : Blo 1760081 5012867 := bstep (se 1 (by rfl) ⟨3759650, by rfl⟩ : syracuseStep 5012867 = 7519301) B7519301
theorem B1760643 : Blo 1760081 1760643 := bstep (se 1 (by rfl) ⟨1320482, by rfl⟩ : syracuseStep 1760643 = 2640965) B2640965
theorem B3571075 : Blo 1760081 3571075 := bstep (se 1 (by rfl) ⟨2678306, by rfl⟩ : syracuseStep 3571075 = 5356613) B5356613
theorem B1760659 : Blo 1760081 1760659 := bstep (se 1 (by rfl) ⟨1320494, by rfl⟩ : syracuseStep 1760659 = 2640989) B2640989
theorem B1760675 : Blo 1760081 1760675 := bstep (se 1 (by rfl) ⟨1320506, by rfl⟩ : syracuseStep 1760675 = 2641013) B2641013
theorem B2973091 : Blo 1760081 2973091 := bstep (se 1 (by rfl) ⟨2229818, by rfl⟩ : syracuseStep 2973091 = 4459637) B4459637
theorem B3964337 : Blo 1760081 3964337 := bstep (se 2 (by rfl) ⟨1486626, by rfl⟩ : syracuseStep 3964337 = 2973253) B2973253
theorem B1760691 : Blo 1760081 1760691 := bstep (se 1 (by rfl) ⟨1320518, by rfl⟩ : syracuseStep 1760691 = 2641037) B2641037
theorem B2506177 : Blo 1760081 2506177 := bstep (se 2 (by rfl) ⟨939816, by rfl⟩ : syracuseStep 2506177 = 1879633) B1879633
theorem B1760707 : Blo 1760081 1760707 := bstep (se 1 (by rfl) ⟨1320530, by rfl⟩ : syracuseStep 1760707 = 2641061) B2641061
theorem B3964355 : Blo 1760081 3964355 := bstep (se 1 (by rfl) ⟨2973266, by rfl⟩ : syracuseStep 3964355 = 5946533) B5946533
theorem B1760723 : Blo 1760081 1760723 := bstep (se 1 (by rfl) ⟨1320542, by rfl⟩ : syracuseStep 1760723 = 2641085) B2641085
theorem B1760739 : Blo 1760081 1760739 := bstep (se 1 (by rfl) ⟨1320554, by rfl⟩ : syracuseStep 1760739 = 2641109) B2641109
theorem B1760755 : Blo 1760081 1760755 := bstep (se 1 (by rfl) ⟨1320566, by rfl⟩ : syracuseStep 1760755 = 2641133) B2641133
theorem B1981939 : Blo 1760081 1981939 := bstep (se 1 (by rfl) ⟨1486454, by rfl⟩ : syracuseStep 1981939 = 2972909) B2972909
theorem B3341827 : Blo 1760081 3341827 := bstep (se 1 (by rfl) ⟨2506370, by rfl⟩ : syracuseStep 3341827 = 5012741) B5012741
theorem B1760771 : Blo 1760081 1760771 := bstep (se 1 (by rfl) ⟨1320578, by rfl⟩ : syracuseStep 1760771 = 2641157) B2641157
theorem B5643793 : Blo 1760081 5643793 := bstep (se 2 (by rfl) ⟨2116422, by rfl⟩ : syracuseStep 5643793 = 4232845) B4232845
theorem B1760787 : Blo 1760081 1760787 := bstep (se 1 (by rfl) ⟨1320590, by rfl⟩ : syracuseStep 1760787 = 2641181) B2641181
theorem B1760803 : Blo 1760081 1760803 := bstep (se 1 (by rfl) ⟨1320602, by rfl⟩ : syracuseStep 1760803 = 2641205) B2641205
theorem B11288099 : Blo 1760081 11288099 := bstep (se 1 (by rfl) ⟨8466074, by rfl⟩ : syracuseStep 11288099 = 16932149) B16932149
theorem B3341873 : Blo 1760081 3341873 := bstep (se 2 (by rfl) ⟨1253202, by rfl⟩ : syracuseStep 3341873 = 2506405) B2506405
theorem B2973233 : Blo 1760081 2973233 := bstep (se 2 (by rfl) ⟨1114962, by rfl⟩ : syracuseStep 2973233 = 2229925) B2229925
theorem B2227763 : Blo 1760081 2227763 := bstep (se 1 (by rfl) ⟨1670822, by rfl⟩ : syracuseStep 2227763 = 3341645) B3341645
theorem B1760819 : Blo 1760081 1760819 := bstep (se 1 (by rfl) ⟨1320614, by rfl⟩ : syracuseStep 1760819 = 2641229) B2641229
theorem B1760835 : Blo 1760081 1760835 := bstep (se 1 (by rfl) ⟨1320626, by rfl⟩ : syracuseStep 1760835 = 2641253) B2641253
theorem B1760851 : Blo 1760081 1760851 := bstep (se 1 (by rfl) ⟨1320638, by rfl⟩ : syracuseStep 1760851 = 2641277) B2641277
theorem B1760867 : Blo 1760081 1760867 := bstep (se 1 (by rfl) ⟨1320650, by rfl⟩ : syracuseStep 1760867 = 2641301) B2641301
theorem B1760883 : Blo 1760081 1760883 := bstep (se 1 (by rfl) ⟨1320662, by rfl⟩ : syracuseStep 1760883 = 2641325) B2641325
theorem B1760899 : Blo 1760081 1760899 := bstep (se 1 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 1760899 = 2641349) B2641349
theorem B1982083 : Blo 1760081 1982083 := bstep (se 1 (by rfl) ⟨1486562, by rfl⟩ : syracuseStep 1982083 = 2973125) B2973125
theorem B1760915 : Blo 1760081 1760915 := bstep (se 1 (by rfl) ⟨1320686, by rfl⟩ : syracuseStep 1760915 = 2641373) B2641373
theorem B1760931 : Blo 1760081 1760931 := bstep (se 1 (by rfl) ⟨1320698, by rfl⟩ : syracuseStep 1760931 = 2641397) B2641397
theorem B2973361 : Blo 1760081 2973361 := bstep (se 2 (by rfl) ⟨1115010, by rfl⟩ : syracuseStep 2973361 = 2230021) B2230021
theorem B1760947 : Blo 1760081 1760947 := bstep (se 1 (by rfl) ⟨1320710, by rfl⟩ : syracuseStep 1760947 = 2641421) B2641421
theorem B1760963 : Blo 1760081 1760963 := bstep (se 1 (by rfl) ⟨1320722, by rfl⟩ : syracuseStep 1760963 = 2641445) B2641445
theorem B5013197 : Blo 1760081 5013197 := bstep (se 3 (by rfl) ⟨939974, by rfl⟩ : syracuseStep 5013197 = 1879949) B1879949
theorem B3964625 : Blo 1760081 3964625 := bstep (se 2 (by rfl) ⟨1486734, by rfl⟩ : syracuseStep 3964625 = 2973469) B2973469
theorem B1760979 : Blo 1760081 1760979 := bstep (se 1 (by rfl) ⟨1320734, by rfl⟩ : syracuseStep 1760979 = 2641469) B2641469
theorem B2973395 : Blo 1760081 2973395 := bstep (se 1 (by rfl) ⟨2230046, by rfl⟩ : syracuseStep 2973395 = 4460093) B4460093
theorem B1760995 : Blo 1760081 1760995 := bstep (se 1 (by rfl) ⟨1320746, by rfl⟩ : syracuseStep 1760995 = 2641493) B2641493
theorem B3964643 : Blo 1760081 3964643 := bstep (se 1 (by rfl) ⟨2973482, by rfl⟩ : syracuseStep 3964643 = 5946965) B5946965
theorem B7519985 : Blo 1760081 7519985 := bstep (se 2 (by rfl) ⟨2819994, by rfl⟩ : syracuseStep 7519985 = 5639989) B5639989
theorem B15040241 : Blo 1760081 15040241 := bstep (se 2 (by rfl) ⟨5640090, by rfl⟩ : syracuseStep 15040241 = 11280181) B11280181
theorem B1761011 : Blo 1760081 1761011 := bstep (se 1 (by rfl) ⟨1320758, by rfl⟩ : syracuseStep 1761011 = 2641517) B2641517
theorem B2678513 : Blo 1760081 2678513 := bstep (se 2 (by rfl) ⟨1004442, by rfl⟩ : syracuseStep 2678513 = 2008885) B2008885
theorem B1761027 : Blo 1760081 1761027 := bstep (se 1 (by rfl) ⟨1320770, by rfl⟩ : syracuseStep 1761027 = 2641541) B2641541
theorem B12697357 : Blo 1760081 12697357 := bstep (se 3 (by rfl) ⟨2380754, by rfl⟩ : syracuseStep 12697357 = 4761509) B4761509
theorem B5013265 : Blo 1760081 5013265 := bstep (se 2 (by rfl) ⟨1879974, by rfl⟩ : syracuseStep 5013265 = 3759949) B3759949
theorem B1761043 : Blo 1760081 1761043 := bstep (se 1 (by rfl) ⟨1320782, by rfl⟩ : syracuseStep 1761043 = 2641565) B2641565
theorem B1982227 : Blo 1760081 1982227 := bstep (se 1 (by rfl) ⟨1486670, by rfl⟩ : syracuseStep 1982227 = 2973341) B2973341
theorem B1761059 : Blo 1760081 1761059 := bstep (se 1 (by rfl) ⟨1320794, by rfl⟩ : syracuseStep 1761059 = 2641589) B2641589
theorem B1761075 : Blo 1760081 1761075 := bstep (se 1 (by rfl) ⟨1320806, by rfl⟩ : syracuseStep 1761075 = 2641613) B2641613
theorem B1761091 : Blo 1760081 1761091 := bstep (se 1 (by rfl) ⟨1320818, by rfl⟩ : syracuseStep 1761091 = 2641637) B2641637
theorem B3342161 : Blo 1760081 3342161 := bstep (se 2 (by rfl) ⟨1253310, by rfl⟩ : syracuseStep 3342161 = 2506621) B2506621
theorem B1761107 : Blo 1760081 1761107 := bstep (se 1 (by rfl) ⟨1320830, by rfl⟩ : syracuseStep 1761107 = 2641661) B2641661
theorem B1761123 : Blo 1760081 1761123 := bstep (se 1 (by rfl) ⟨1320842, by rfl⟩ : syracuseStep 1761123 = 2641685) B2641685
theorem B8912753 : Blo 1760081 8912753 := bstep (se 2 (by rfl) ⟨3342282, by rfl⟩ : syracuseStep 8912753 = 6684565) B6684565
theorem B1761139 : Blo 1760081 1761139 := bstep (se 1 (by rfl) ⟨1320854, by rfl⟩ : syracuseStep 1761139 = 2641709) B2641709
theorem B1761155 : Blo 1760081 1761155 := bstep (se 1 (by rfl) ⟨1320866, by rfl⟩ : syracuseStep 1761155 = 2641733) B2641733
theorem B1761171 : Blo 1760081 1761171 := bstep (se 1 (by rfl) ⟨1320878, by rfl⟩ : syracuseStep 1761171 = 2641757) B2641757
theorem B1761187 : Blo 1760081 1761187 := bstep (se 1 (by rfl) ⟨1320890, by rfl⟩ : syracuseStep 1761187 = 2641781) B2641781
theorem B1761203 : Blo 1760081 1761203 := bstep (se 1 (by rfl) ⟨1320902, by rfl⟩ : syracuseStep 1761203 = 2641805) B2641805
theorem B1761219 : Blo 1760081 1761219 := bstep (se 1 (by rfl) ⟨1320914, by rfl⟩ : syracuseStep 1761219 = 2641829) B2641829
theorem B1761235 : Blo 1760081 1761235 := bstep (se 1 (by rfl) ⟨1320926, by rfl⟩ : syracuseStep 1761235 = 2641853) B2641853
theorem B1761251 : Blo 1760081 1761251 := bstep (se 1 (by rfl) ⟨1320938, by rfl⟩ : syracuseStep 1761251 = 2641877) B2641877
theorem B1761267 : Blo 1760081 1761267 := bstep (se 1 (by rfl) ⟨1320950, by rfl⟩ : syracuseStep 1761267 = 2641901) B2641901
theorem B1761291 : Blo 1760081 1761291 := bstep (se 1 (by rfl) ⟨1320968, by rfl⟩ : syracuseStep 1761291 = 2641937) B2641937
theorem B7520273 : Blo 1760081 7520273 := bstep (se 2 (by rfl) ⟨2820102, by rfl⟩ : syracuseStep 7520273 = 5640205) B5640205
theorem B3342359 : Blo 1760081 3342359 := bstep (se 1 (by rfl) ⟨2506769, by rfl⟩ : syracuseStep 3342359 = 5013539) B5013539
theorem B1761303 : Blo 1760081 1761303 := bstep (se 1 (by rfl) ⟨1320977, by rfl⟩ : syracuseStep 1761303 = 2641955) B2641955
theorem B1761323 : Blo 1760081 1761323 := bstep (se 1 (by rfl) ⟨1320992, by rfl⟩ : syracuseStep 1761323 = 2641985) B2641985
theorem B1761335 : Blo 1760081 1761335 := bstep (se 1 (by rfl) ⟨1321001, by rfl⟩ : syracuseStep 1761335 = 2642003) B2642003
theorem B1761355 : Blo 1760081 1761355 := bstep (se 1 (by rfl) ⟨1321016, by rfl⟩ : syracuseStep 1761355 = 2642033) B2642033
theorem B1761367 : Blo 1760081 1761367 := bstep (se 1 (by rfl) ⟨1321025, by rfl⟩ : syracuseStep 1761367 = 2642051) B2642051
theorem B1761387 : Blo 1760081 1761387 := bstep (se 1 (by rfl) ⟨1321040, by rfl⟩ : syracuseStep 1761387 = 2642081) B2642081
theorem B1761399 : Blo 1760081 1761399 := bstep (se 1 (by rfl) ⟨1321049, by rfl⟩ : syracuseStep 1761399 = 2642099) B2642099
theorem B10715267 : Blo 1760081 10715267 := bstep (se 1 (by rfl) ⟨8036450, by rfl⟩ : syracuseStep 10715267 = 16072901) B16072901
theorem B1761419 : Blo 1760081 1761419 := bstep (se 1 (by rfl) ⟨1321064, by rfl⟩ : syracuseStep 1761419 = 2642129) B2642129
theorem B1761431 : Blo 1760081 1761431 := bstep (se 1 (by rfl) ⟨1321073, by rfl⟩ : syracuseStep 1761431 = 2642147) B2642147
theorem B1761451 : Blo 1760081 1761451 := bstep (se 1 (by rfl) ⟨1321088, by rfl⟩ : syracuseStep 1761451 = 2642177) B2642177
theorem B1761463 : Blo 1760081 1761463 := bstep (se 1 (by rfl) ⟨1321097, by rfl⟩ : syracuseStep 1761463 = 2642195) B2642195
theorem B1761483 : Blo 1760081 1761483 := bstep (se 1 (by rfl) ⟨1321112, by rfl⟩ : syracuseStep 1761483 = 2642225) B2642225
theorem B1761495 : Blo 1760081 1761495 := bstep (se 1 (by rfl) ⟨1321121, by rfl⟩ : syracuseStep 1761495 = 2642243) B2642243
theorem B1761515 : Blo 1760081 1761515 := bstep (se 1 (by rfl) ⟨1321136, by rfl⟩ : syracuseStep 1761515 = 2642273) B2642273
theorem B1761527 : Blo 1760081 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B1761547 : Blo 1760081 1761547 := bstep (se 1 (by rfl) ⟨1321160, by rfl⟩ : syracuseStep 1761547 = 2642321) B2642321
theorem B1761559 : Blo 1760081 1761559 := bstep (se 1 (by rfl) ⟨1321169, by rfl⟩ : syracuseStep 1761559 = 2642339) B2642339
theorem B3342617 : Blo 1760081 3342617 := bstep (se 2 (by rfl) ⟨1253481, by rfl⟩ : syracuseStep 3342617 = 2506963) B2506963
theorem B1761579 : Blo 1760081 1761579 := bstep (se 1 (by rfl) ⟨1321184, by rfl⟩ : syracuseStep 1761579 = 2642369) B2642369
theorem B33857837 : Blo 1760081 33857837 := bstep (se 3 (by rfl) ⟨6348344, by rfl⟩ : syracuseStep 33857837 = 12696689) B12696689
theorem B1761591 : Blo 1760081 1761591 := bstep (se 1 (by rfl) ⟨1321193, by rfl⟩ : syracuseStep 1761591 = 2642387) B2642387
theorem B1761611 : Blo 1760081 1761611 := bstep (se 1 (by rfl) ⟨1321208, by rfl⟩ : syracuseStep 1761611 = 2642417) B2642417
theorem B1761623 : Blo 1760081 1761623 := bstep (se 1 (by rfl) ⟨1321217, by rfl⟩ : syracuseStep 1761623 = 2642435) B2642435
theorem B32579941 : Blo 1760081 32579941 := bstep (se 4 (by rfl) ⟨3054369, by rfl⟩ : syracuseStep 32579941 = 6108739) B6108739
theorem B1761643 : Blo 1760081 1761643 := bstep (se 1 (by rfl) ⟨1321232, by rfl⟩ : syracuseStep 1761643 = 2642465) B2642465
theorem B1761655 : Blo 1760081 1761655 := bstep (se 1 (by rfl) ⟨1321241, by rfl⟩ : syracuseStep 1761655 = 2642483) B2642483
theorem B1761675 : Blo 1760081 1761675 := bstep (se 1 (by rfl) ⟨1321256, by rfl⟩ : syracuseStep 1761675 = 2642513) B2642513
theorem B1761687 : Blo 1760081 1761687 := bstep (se 1 (by rfl) ⟨1321265, by rfl⟩ : syracuseStep 1761687 = 2642531) B2642531
theorem B1761707 : Blo 1760081 1761707 := bstep (se 1 (by rfl) ⟨1321280, by rfl⟩ : syracuseStep 1761707 = 2642561) B2642561
theorem B4456883 : Blo 1760081 4456883 := bstep (se 1 (by rfl) ⟨3342662, by rfl⟩ : syracuseStep 4456883 = 6685325) B6685325
theorem B1761719 : Blo 1760081 1761719 := bstep (se 1 (by rfl) ⟨1321289, by rfl⟩ : syracuseStep 1761719 = 2642579) B2642579
theorem B1761739 : Blo 1760081 1761739 := bstep (se 1 (by rfl) ⟨1321304, by rfl⟩ : syracuseStep 1761739 = 2642609) B2642609
theorem B3572171 : Blo 1760081 3572171 := bstep (se 1 (by rfl) ⟨2679128, by rfl⟩ : syracuseStep 3572171 = 5358257) B5358257
theorem B1761751 : Blo 1760081 1761751 := bstep (se 1 (by rfl) ⟨1321313, by rfl⟩ : syracuseStep 1761751 = 2642627) B2642627
theorem B1761771 : Blo 1760081 1761771 := bstep (se 1 (by rfl) ⟨1321328, by rfl⟩ : syracuseStep 1761771 = 2642657) B2642657
theorem B1761783 : Blo 1760081 1761783 := bstep (se 1 (by rfl) ⟨1321337, by rfl⟩ : syracuseStep 1761783 = 2642675) B2642675
theorem B1761803 : Blo 1760081 1761803 := bstep (se 1 (by rfl) ⟨1321352, by rfl⟩ : syracuseStep 1761803 = 2642705) B2642705
theorem B1761815 : Blo 1760081 1761815 := bstep (se 1 (by rfl) ⟨1321361, by rfl⟩ : syracuseStep 1761815 = 2642723) B2642723
theorem B1761835 : Blo 1760081 1761835 := bstep (se 1 (by rfl) ⟨1321376, by rfl⟩ : syracuseStep 1761835 = 2642753) B2642753
theorem B1761847 : Blo 1760081 1761847 := bstep (se 1 (by rfl) ⟨1321385, by rfl⟩ : syracuseStep 1761847 = 2642771) B2642771
theorem B1761867 : Blo 1760081 1761867 := bstep (se 1 (by rfl) ⟨1321400, by rfl⟩ : syracuseStep 1761867 = 2642801) B2642801
theorem B1761879 : Blo 1760081 1761879 := bstep (se 1 (by rfl) ⟨1321409, by rfl⟩ : syracuseStep 1761879 = 2642819) B2642819
theorem B1761899 : Blo 1760081 1761899 := bstep (se 1 (by rfl) ⟨1321424, by rfl⟩ : syracuseStep 1761899 = 2642849) B2642849
theorem B1761911 : Blo 1760081 1761911 := bstep (se 1 (by rfl) ⟨1321433, by rfl⟩ : syracuseStep 1761911 = 2642867) B2642867
theorem B3760769 : Blo 1760081 3760769 := bstep (se 2 (by rfl) ⟨1410288, by rfl⟩ : syracuseStep 3760769 = 2820577) B2820577
theorem B1761931 : Blo 1760081 1761931 := bstep (se 1 (by rfl) ⟨1321448, by rfl⟩ : syracuseStep 1761931 = 2642897) B2642897
theorem B2228887 : Blo 1760081 2228887 := bstep (se 1 (by rfl) ⟨1671665, by rfl⟩ : syracuseStep 2228887 = 3343331) B3343331
theorem B1761943 : Blo 1760081 1761943 := bstep (se 1 (by rfl) ⟨1321457, by rfl⟩ : syracuseStep 1761943 = 2642915) B2642915
theorem B1761963 : Blo 1760081 1761963 := bstep (se 1 (by rfl) ⟨1321472, by rfl⟩ : syracuseStep 1761963 = 2642945) B2642945
theorem B11002547 : Blo 1760081 11002547 := bstep (se 1 (by rfl) ⟨8251910, by rfl⟩ : syracuseStep 11002547 = 16503821) B16503821
theorem B3343027 : Blo 1760081 3343027 := bstep (se 1 (by rfl) ⟨2507270, by rfl⟩ : syracuseStep 3343027 = 5014541) B5014541
theorem B1761975 : Blo 1760081 1761975 := bstep (se 1 (by rfl) ⟨1321481, by rfl⟩ : syracuseStep 1761975 = 2642963) B2642963
theorem B1761995 : Blo 1760081 1761995 := bstep (se 1 (by rfl) ⟨1321496, by rfl⟩ : syracuseStep 1761995 = 2642993) B2642993
theorem B1762007 : Blo 1760081 1762007 := bstep (se 1 (by rfl) ⟨1321505, by rfl⟩ : syracuseStep 1762007 = 2643011) B2643011
theorem B4457177 : Blo 1760081 4457177 := bstep (se 2 (by rfl) ⟨1671441, by rfl⟩ : syracuseStep 4457177 = 3342883) B3342883
theorem B6349529 : Blo 1760081 6349529 := bstep (se 2 (by rfl) ⟨2381073, by rfl⟩ : syracuseStep 6349529 = 4762147) B4762147
theorem B1762027 : Blo 1760081 1762027 := bstep (se 1 (by rfl) ⟨1321520, by rfl⟩ : syracuseStep 1762027 = 2643041) B2643041
theorem B1762039 : Blo 1760081 1762039 := bstep (se 1 (by rfl) ⟨1321529, by rfl⟩ : syracuseStep 1762039 = 2643059) B2643059
theorem B20054789 : Blo 1760081 20054789 := bstep (se 4 (by rfl) ⟨1880136, by rfl⟩ : syracuseStep 20054789 = 3760273) B3760273
theorem B1762059 : Blo 1760081 1762059 := bstep (se 1 (by rfl) ⟨1321544, by rfl⟩ : syracuseStep 1762059 = 2643089) B2643089
theorem B1762071 : Blo 1760081 1762071 := bstep (se 1 (by rfl) ⟨1321553, by rfl⟩ : syracuseStep 1762071 = 2643107) B2643107
theorem B2507851 : Blo 1760081 2507851 := bstep (se 1 (by rfl) ⟨1880888, by rfl⟩ : syracuseStep 2507851 = 3761777) B3761777
theorem B2507863 : Blo 1760081 2507863 := bstep (se 1 (by rfl) ⟨1880897, by rfl⟩ : syracuseStep 2507863 = 3761795) B3761795
theorem B5719133 : Blo 1760081 5719133 := bstep (se 3 (by rfl) ⟨1072337, by rfl⟩ : syracuseStep 5719133 = 2144675) B2144675
theorem B3761291 : Blo 1760081 3761291 := bstep (se 1 (by rfl) ⟨2820968, by rfl⟩ : syracuseStep 3761291 = 5641937) B5641937
theorem B6685841 : Blo 1760081 6685841 := bstep (se 2 (by rfl) ⟨2507190, by rfl⟩ : syracuseStep 6685841 = 5014381) B5014381
theorem B3343513 : Blo 1760081 3343513 := bstep (se 2 (by rfl) ⟨1253817, by rfl⟩ : syracuseStep 3343513 = 2507635) B2507635
theorem B4015307 : Blo 1760081 4015307 := bstep (se 1 (by rfl) ⟨3011480, by rfl⟩ : syracuseStep 4015307 = 6022961) B6022961
theorem B14279885 : Blo 1760081 14279885 := bstep (se 3 (by rfl) ⟨2677478, by rfl⟩ : syracuseStep 14279885 = 5354957) B5354957
theorem B1885559 : Blo 1760081 1885559 := bstep (se 1 (by rfl) ⟨1414169, by rfl⟩ : syracuseStep 1885559 = 2828339) B2828339
theorem B2008471 : Blo 1760081 2008471 := bstep (se 1 (by rfl) ⟨1506353, by rfl⟩ : syracuseStep 2008471 = 3012707) B3012707
theorem B4826561 : Blo 1760081 4826561 := bstep (se 2 (by rfl) ⟨1809960, by rfl⟩ : syracuseStep 4826561 = 3619921) B3619921
theorem B2229707 : Blo 1760081 2229707 := bstep (se 1 (by rfl) ⟨1672280, by rfl⟩ : syracuseStep 2229707 = 3344561) B3344561
theorem B5940701 : Blo 1760081 5940701 := bstep (se 3 (by rfl) ⟨1113881, by rfl⟩ : syracuseStep 5940701 = 2227763) B2227763
theorem B16287277 : Blo 1760081 16287277 := bstep (se 3 (by rfl) ⟨3053864, by rfl⟩ : syracuseStep 16287277 = 6107729) B6107729
theorem B6686297 : Blo 1760081 6686297 := bstep (se 2 (by rfl) ⟨2507361, by rfl⟩ : syracuseStep 6686297 = 5014723) B5014723
theorem B3344075 : Blo 1760081 3344075 := bstep (se 1 (by rfl) ⟨2508056, by rfl⟩ : syracuseStep 3344075 = 5016113) B5016113
theorem B3172097 : Blo 1760081 3172097 := bstep (se 2 (by rfl) ⟨1189536, by rfl⟩ : syracuseStep 3172097 = 2379073) B2379073
theorem B8029955 : Blo 1760081 8029955 := bstep (se 1 (by rfl) ⟨6022466, by rfl⟩ : syracuseStep 8029955 = 12044933) B12044933
theorem B6686509 : Blo 1760081 6686509 := bstep (se 3 (by rfl) ⟨1253720, by rfl⟩ : syracuseStep 6686509 = 2507441) B2507441
theorem B4761433 : Blo 1760081 4761433 := bstep (se 2 (by rfl) ⟨1785537, by rfl⟩ : syracuseStep 4761433 = 3571075) B3571075
theorem B11757413 : Blo 1760081 11757413 := bstep (se 4 (by rfl) ⟨1102257, by rfl⟩ : syracuseStep 11757413 = 2204515) B2204515
theorem B3344257 : Blo 1760081 3344257 := bstep (se 2 (by rfl) ⟨1254096, by rfl⟩ : syracuseStep 3344257 = 2508193) B2508193
theorem B42838091 : Blo 1760081 42838091 := bstep (se 1 (by rfl) ⟨32128568, by rfl⟩ : syracuseStep 42838091 = 64257137) B64257137
theorem B6686813 : Blo 1760081 6686813 := bstep (se 3 (by rfl) ⟨1253777, by rfl⟩ : syracuseStep 6686813 = 2507555) B2507555
theorem B2009323 : Blo 1760081 2009323 := bstep (se 1 (by rfl) ⟨1506992, by rfl⟩ : syracuseStep 2009323 = 3013985) B3013985
theorem B2640203 : Blo 1760081 2640203 := bstep (se 1 (by rfl) ⟨1980152, by rfl⟩ : syracuseStep 2640203 = 3960305) B3960305
theorem B4458827 : Blo 1760081 4458827 := bstep (se 1 (by rfl) ⟨3344120, by rfl⟩ : syracuseStep 4458827 = 6688241) B6688241
theorem B2640215 : Blo 1760081 2640215 := bstep (se 1 (by rfl) ⟨1980161, by rfl⟩ : syracuseStep 2640215 = 3960323) B3960323
theorem B3762521 : Blo 1760081 3762521 := bstep (se 2 (by rfl) ⟨1410945, by rfl⟩ : syracuseStep 3762521 = 2821891) B2821891
theorem B6777233 : Blo 1760081 6777233 := bstep (se 2 (by rfl) ⟨2541462, by rfl⟩ : syracuseStep 6777233 = 5082925) B5082925
theorem B2640281 : Blo 1760081 2640281 := bstep (se 2 (by rfl) ⟨990105, by rfl⟩ : syracuseStep 2640281 = 1980211) B1980211
theorem B7522733 : Blo 1760081 7522733 := bstep (se 3 (by rfl) ⟨1410512, by rfl⟩ : syracuseStep 7522733 = 2821025) B2821025
theorem B10029491 : Blo 1760081 10029491 := bstep (se 1 (by rfl) ⟨7522118, by rfl⟩ : syracuseStep 10029491 = 15044237) B15044237
theorem B2640395 : Blo 1760081 2640395 := bstep (se 1 (by rfl) ⟨1980296, by rfl⟩ : syracuseStep 2640395 = 3960593) B3960593
theorem B2640407 : Blo 1760081 2640407 := bstep (se 1 (by rfl) ⟨1980305, by rfl⟩ : syracuseStep 2640407 = 3960611) B3960611
theorem B5941835 : Blo 1760081 5941835 := bstep (se 1 (by rfl) ⟨4456376, by rfl⟩ : syracuseStep 5941835 = 8912753) B8912753
theorem B3344971 : Blo 1760081 3344971 := bstep (se 1 (by rfl) ⟨2508728, by rfl⟩ : syracuseStep 3344971 = 5017457) B5017457
theorem B2640473 : Blo 1760081 2640473 := bstep (se 2 (by rfl) ⟨990177, by rfl⟩ : syracuseStep 2640473 = 1980355) B1980355
theorem B3345047 : Blo 1760081 3345047 := bstep (se 1 (by rfl) ⟨2508785, by rfl⟩ : syracuseStep 3345047 = 5017571) B5017571
theorem B2640587 : Blo 1760081 2640587 := bstep (se 1 (by rfl) ⟨1980440, by rfl⟩ : syracuseStep 2640587 = 3960881) B3960881
theorem B2640599 : Blo 1760081 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B3762931 : Blo 1760081 3762931 := bstep (se 1 (by rfl) ⟨2822198, by rfl⟩ : syracuseStep 3762931 = 5644397) B5644397
theorem B2640665 : Blo 1760081 2640665 := bstep (se 2 (by rfl) ⟨990249, by rfl⟩ : syracuseStep 2640665 = 1980499) B1980499
theorem B5942105 : Blo 1760081 5942105 := bstep (se 2 (by rfl) ⟨2228289, by rfl⟩ : syracuseStep 5942105 = 4456579) B4456579
theorem B2640779 : Blo 1760081 2640779 := bstep (se 1 (by rfl) ⟨1980584, by rfl⟩ : syracuseStep 2640779 = 3961169) B3961169
theorem B2640791 : Blo 1760081 2640791 := bstep (se 1 (by rfl) ⟨1980593, by rfl⟩ : syracuseStep 2640791 = 3961187) B3961187
theorem B5639129 : Blo 1760081 5639129 := bstep (se 2 (by rfl) ⟨2114673, by rfl⟩ : syracuseStep 5639129 = 4229347) B4229347
theorem B2640857 : Blo 1760081 2640857 := bstep (se 2 (by rfl) ⟨990321, by rfl⟩ : syracuseStep 2640857 = 1980643) B1980643
theorem B2640971 : Blo 1760081 2640971 := bstep (se 1 (by rfl) ⟨1980728, by rfl⟩ : syracuseStep 2640971 = 3961457) B3961457
theorem B2640983 : Blo 1760081 2640983 := bstep (se 1 (by rfl) ⟨1980737, by rfl⟩ : syracuseStep 2640983 = 3961475) B3961475
theorem B7523417 : Blo 1760081 7523417 := bstep (se 2 (by rfl) ⟨2821281, by rfl⟩ : syracuseStep 7523417 = 5642563) B5642563
theorem B2641049 : Blo 1760081 2641049 := bstep (se 2 (by rfl) ⟨990393, by rfl⟩ : syracuseStep 2641049 = 1980787) B1980787
theorem B2641163 : Blo 1760081 2641163 := bstep (se 1 (by rfl) ⟨1980872, by rfl⟩ : syracuseStep 2641163 = 3961745) B3961745
theorem B2641175 : Blo 1760081 2641175 := bstep (se 1 (by rfl) ⟨1980881, by rfl⟩ : syracuseStep 2641175 = 3961763) B3961763
theorem B4459799 : Blo 1760081 4459799 := bstep (se 1 (by rfl) ⟨3344849, by rfl⟩ : syracuseStep 4459799 = 6689699) B6689699
theorem B3812633 : Blo 1760081 3812633 := bstep (se 2 (by rfl) ⟨1429737, by rfl⟩ : syracuseStep 3812633 = 2859475) B2859475
theorem B2641241 : Blo 1760081 2641241 := bstep (se 2 (by rfl) ⟨990465, by rfl⟩ : syracuseStep 2641241 = 1980931) B1980931
theorem B8916317 : Blo 1760081 8916317 := bstep (se 3 (by rfl) ⟨1671809, by rfl⟩ : syracuseStep 8916317 = 3343619) B3343619
theorem B3960215 : Blo 1760081 3960215 := bstep (se 1 (by rfl) ⟨2970161, by rfl⟩ : syracuseStep 3960215 = 5940323) B5940323
theorem B8465843 : Blo 1760081 8465843 := bstep (se 1 (by rfl) ⟨6349382, by rfl⟩ : syracuseStep 8465843 = 12698765) B12698765
theorem B5426635 : Blo 1760081 5426635 := bstep (se 1 (by rfl) ⟨4069976, by rfl⟩ : syracuseStep 5426635 = 8139953) B8139953
theorem B7138763 : Blo 1760081 7138763 := bstep (se 1 (by rfl) ⟨5354072, by rfl⟩ : syracuseStep 7138763 = 10708145) B10708145
theorem B2641355 : Blo 1760081 2641355 := bstep (se 1 (by rfl) ⟨1981016, by rfl⟩ : syracuseStep 2641355 = 3962033) B3962033
theorem B2641367 : Blo 1760081 2641367 := bstep (se 1 (by rfl) ⟨1981025, by rfl⟩ : syracuseStep 2641367 = 3962051) B3962051
theorem B5942807 : Blo 1760081 5942807 := bstep (se 1 (by rfl) ⟨4457105, by rfl⟩ : syracuseStep 5942807 = 8914211) B8914211
theorem B2379289 : Blo 1760081 2379289 := bstep (se 2 (by rfl) ⟨892233, by rfl⟩ : syracuseStep 2379289 = 1784467) B1784467
theorem B2641433 : Blo 1760081 2641433 := bstep (se 2 (by rfl) ⟨990537, by rfl⟩ : syracuseStep 2641433 = 1981075) B1981075
theorem B3960395 : Blo 1760081 3960395 := bstep (se 1 (by rfl) ⟨2970296, by rfl⟩ : syracuseStep 3960395 = 5940593) B5940593
theorem B4230731 : Blo 1760081 4230731 := bstep (se 1 (by rfl) ⟨3173048, by rfl⟩ : syracuseStep 4230731 = 6346097) B6346097
theorem B3960449 : Blo 1760081 3960449 := bstep (se 2 (by rfl) ⟨1485168, by rfl⟩ : syracuseStep 3960449 = 2970337) B2970337
theorem B28577411 : Blo 1760081 28577411 := bstep (se 1 (by rfl) ⟨21433058, by rfl⟩ : syracuseStep 28577411 = 42866117) B42866117
theorem B2641547 : Blo 1760081 2641547 := bstep (se 1 (by rfl) ⟨1981160, by rfl⟩ : syracuseStep 2641547 = 3962321) B3962321
theorem B2641559 : Blo 1760081 2641559 := bstep (se 1 (by rfl) ⟨1981169, by rfl⟩ : syracuseStep 2641559 = 3962339) B3962339
theorem B1879723 : Blo 1760081 1879723 := bstep (se 1 (by rfl) ⟨1409792, by rfl⟩ : syracuseStep 1879723 = 2819585) B2819585
theorem B228519629 : Blo 1760081 228519629 := bstep (se 3 (by rfl) ⟨42847430, by rfl⟩ : syracuseStep 228519629 = 85694861) B85694861
theorem B2641625 : Blo 1760081 2641625 := bstep (se 2 (by rfl) ⟨990609, by rfl⟩ : syracuseStep 2641625 = 1981219) B1981219
theorem B3174167 : Blo 1760081 3174167 := bstep (se 1 (by rfl) ⟨2380625, by rfl⟩ : syracuseStep 3174167 = 4761251) B4761251
theorem B2641739 : Blo 1760081 2641739 := bstep (se 1 (by rfl) ⟨1981304, by rfl⟩ : syracuseStep 2641739 = 3962609) B3962609
theorem B2641751 : Blo 1760081 2641751 := bstep (se 1 (by rfl) ⟨1981313, by rfl⟩ : syracuseStep 2641751 = 3962627) B3962627
theorem B3960665 : Blo 1760081 3960665 := bstep (se 2 (by rfl) ⟨1485249, by rfl⟩ : syracuseStep 3960665 = 2970499) B2970499
theorem B10030949 : Blo 1760081 10030949 := bstep (se 4 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 10030949 = 1880803) B1880803
theorem B22572917 : Blo 1760081 22572917 := bstep (se 5 (by rfl) ⟨1058105, by rfl⟩ : syracuseStep 22572917 = 2116211) B2116211
theorem B2576281 : Blo 1760081 2576281 := bstep (se 2 (by rfl) ⟨966105, by rfl⟩ : syracuseStep 2576281 = 1932211) B1932211
theorem B2641817 : Blo 1760081 2641817 := bstep (se 2 (by rfl) ⟨990681, by rfl⟩ : syracuseStep 2641817 = 1981363) B1981363
theorem B3960755 : Blo 1760081 3960755 := bstep (se 1 (by rfl) ⟨2970566, by rfl⟩ : syracuseStep 3960755 = 5941133) B5941133
theorem B3960791 : Blo 1760081 3960791 := bstep (se 1 (by rfl) ⟨2970593, by rfl⟩ : syracuseStep 3960791 = 5941187) B5941187
theorem B2641931 : Blo 1760081 2641931 := bstep (se 1 (by rfl) ⟨1981448, by rfl⟩ : syracuseStep 2641931 = 3962897) B3962897
theorem B2641943 : Blo 1760081 2641943 := bstep (se 1 (by rfl) ⟨1981457, by rfl⟩ : syracuseStep 2641943 = 3962915) B3962915
theorem B5943347 : Blo 1760081 5943347 := bstep (se 1 (by rfl) ⟨4457510, by rfl⟩ : syracuseStep 5943347 = 8915021) B8915021
theorem B2642009 : Blo 1760081 2642009 := bstep (se 2 (by rfl) ⟨990753, by rfl⟩ : syracuseStep 2642009 = 1981507) B1981507
theorem B3960971 : Blo 1760081 3960971 := bstep (se 1 (by rfl) ⟨2970728, by rfl⟩ : syracuseStep 3960971 = 5941457) B5941457
theorem B3961025 : Blo 1760081 3961025 := bstep (se 2 (by rfl) ⟨1485384, by rfl⟩ : syracuseStep 3961025 = 2970769) B2970769
theorem B2642123 : Blo 1760081 2642123 := bstep (se 1 (by rfl) ⟨1981592, by rfl⟩ : syracuseStep 2642123 = 3963185) B3963185
theorem B2642135 : Blo 1760081 2642135 := bstep (se 1 (by rfl) ⟨1981601, by rfl⟩ : syracuseStep 2642135 = 3963203) B3963203
theorem B4231385 : Blo 1760081 4231385 := bstep (se 2 (by rfl) ⟨1586769, by rfl⟩ : syracuseStep 4231385 = 3173539) B3173539
theorem B2642201 : Blo 1760081 2642201 := bstep (se 2 (by rfl) ⟨990825, by rfl⟩ : syracuseStep 2642201 = 1981651) B1981651
theorem B5943617 : Blo 1760081 5943617 := bstep (se 2 (by rfl) ⟨2228856, by rfl⟩ : syracuseStep 5943617 = 4457713) B4457713
theorem B7524683 : Blo 1760081 7524683 := bstep (se 1 (by rfl) ⟨5643512, by rfl⟩ : syracuseStep 7524683 = 11287025) B11287025
theorem B2642315 : Blo 1760081 2642315 := bstep (se 1 (by rfl) ⟨1981736, by rfl⟩ : syracuseStep 2642315 = 3963473) B3963473
theorem B2642327 : Blo 1760081 2642327 := bstep (se 1 (by rfl) ⟨1981745, by rfl⟩ : syracuseStep 2642327 = 3963491) B3963491
theorem B3051929 : Blo 1760081 3051929 := bstep (se 2 (by rfl) ⟨1144473, by rfl⟩ : syracuseStep 3051929 = 2288947) B2288947
theorem B3961241 : Blo 1760081 3961241 := bstep (se 2 (by rfl) ⟨1485465, by rfl⟩ : syracuseStep 3961241 = 2970931) B2970931
theorem B8032715 : Blo 1760081 8032715 := bstep (se 1 (by rfl) ⟨6024536, by rfl⟩ : syracuseStep 8032715 = 12049073) B12049073
theorem B2642393 : Blo 1760081 2642393 := bstep (se 2 (by rfl) ⟨990897, by rfl⟩ : syracuseStep 2642393 = 1981795) B1981795
theorem B3961331 : Blo 1760081 3961331 := bstep (se 1 (by rfl) ⟨2970998, by rfl⟩ : syracuseStep 3961331 = 5941997) B5941997
theorem B10031633 : Blo 1760081 10031633 := bstep (se 2 (by rfl) ⟨3761862, by rfl⟩ : syracuseStep 10031633 = 7523725) B7523725
theorem B3961367 : Blo 1760081 3961367 := bstep (se 1 (by rfl) ⟨2971025, by rfl⟩ : syracuseStep 3961367 = 5942051) B5942051
theorem B5640769 : Blo 1760081 5640769 := bstep (se 2 (by rfl) ⟨2115288, by rfl⟩ : syracuseStep 5640769 = 4230577) B4230577
theorem B2642507 : Blo 1760081 2642507 := bstep (se 1 (by rfl) ⟨1981880, by rfl⟩ : syracuseStep 2642507 = 3963761) B3963761
theorem B2642519 : Blo 1760081 2642519 := bstep (se 1 (by rfl) ⟨1981889, by rfl⟩ : syracuseStep 2642519 = 3963779) B3963779
theorem B3814003 : Blo 1760081 3814003 := bstep (se 1 (by rfl) ⟨2860502, by rfl⟩ : syracuseStep 3814003 = 5721005) B5721005
theorem B6689411 : Blo 1760081 6689411 := bstep (se 1 (by rfl) ⟨5017058, by rfl⟩ : syracuseStep 6689411 = 10034117) B10034117
theorem B6689425 : Blo 1760081 6689425 := bstep (se 2 (by rfl) ⟨2508534, by rfl⟩ : syracuseStep 6689425 = 5017069) B5017069
theorem B2970263 : Blo 1760081 2970263 := bstep (se 1 (by rfl) ⟨2227697, by rfl⟩ : syracuseStep 2970263 = 4455395) B4455395
theorem B3666583 : Blo 1760081 3666583 := bstep (se 1 (by rfl) ⟨2749937, by rfl⟩ : syracuseStep 3666583 = 5499875) B5499875
theorem B2642585 : Blo 1760081 2642585 := bstep (se 2 (by rfl) ⟨990969, by rfl⟩ : syracuseStep 2642585 = 1981939) B1981939
theorem B7525057 : Blo 1760081 7525057 := bstep (se 2 (by rfl) ⟨2821896, by rfl⟩ : syracuseStep 7525057 = 5643793) B5643793
theorem B3961547 : Blo 1760081 3961547 := bstep (se 1 (by rfl) ⟨2971160, by rfl⟩ : syracuseStep 3961547 = 5942321) B5942321
theorem B14471885 : Blo 1760081 14471885 := bstep (se 3 (by rfl) ⟨2713478, by rfl⟩ : syracuseStep 14471885 = 5426957) B5426957
theorem B3961601 : Blo 1760081 3961601 := bstep (se 2 (by rfl) ⟨1485600, by rfl⟩ : syracuseStep 3961601 = 2971201) B2971201
theorem B2642699 : Blo 1760081 2642699 := bstep (se 1 (by rfl) ⟨1982024, by rfl⟩ : syracuseStep 2642699 = 3964049) B3964049
theorem B2970391 : Blo 1760081 2970391 := bstep (se 1 (by rfl) ⟨2227793, by rfl⟩ : syracuseStep 2970391 = 4455587) B4455587
theorem B2642711 : Blo 1760081 2642711 := bstep (se 1 (by rfl) ⟨1982033, by rfl⟩ : syracuseStep 2642711 = 3964067) B3964067
theorem B2290507 : Blo 1760081 2290507 := bstep (se 1 (by rfl) ⟨1717880, by rfl⟩ : syracuseStep 2290507 = 3435761) B3435761
theorem B2642777 : Blo 1760081 2642777 := bstep (se 2 (by rfl) ⟨991041, by rfl⟩ : syracuseStep 2642777 = 1982083) B1982083
theorem B5944157 : Blo 1760081 5944157 := bstep (se 3 (by rfl) ⟨1114529, by rfl⟩ : syracuseStep 5944157 = 2229059) B2229059
theorem B3175319 : Blo 1760081 3175319 := bstep (se 1 (by rfl) ⟨2381489, by rfl⟩ : syracuseStep 3175319 = 4762979) B4762979
theorem B6689729 : Blo 1760081 6689729 := bstep (se 2 (by rfl) ⟨2508648, by rfl⟩ : syracuseStep 6689729 = 5017297) B5017297
theorem B2642891 : Blo 1760081 2642891 := bstep (se 1 (by rfl) ⟨1982168, by rfl⟩ : syracuseStep 2642891 = 3964337) B3964337
theorem B2642903 : Blo 1760081 2642903 := bstep (se 1 (by rfl) ⟨1982177, by rfl⟩ : syracuseStep 2642903 = 3964355) B3964355
theorem B3961817 : Blo 1760081 3961817 := bstep (se 2 (by rfl) ⟨1485681, by rfl⟩ : syracuseStep 3961817 = 2971363) B2971363
theorem B4232153 : Blo 1760081 4232153 := bstep (se 2 (by rfl) ⟨1587057, by rfl⟩ : syracuseStep 4232153 = 3174115) B3174115
theorem B3814411 : Blo 1760081 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B16929809 : Blo 1760081 16929809 := bstep (se 2 (by rfl) ⟨6348678, by rfl⟩ : syracuseStep 16929809 = 12697357) B12697357
theorem B7525399 : Blo 1760081 7525399 := bstep (se 1 (by rfl) ⟨5644049, by rfl⟩ : syracuseStep 7525399 = 11288099) B11288099
theorem B2642969 : Blo 1760081 2642969 := bstep (se 2 (by rfl) ⟨991113, by rfl⟩ : syracuseStep 2642969 = 1982227) B1982227
theorem B8459309 : Blo 1760081 8459309 := bstep (se 3 (by rfl) ⟨1586120, by rfl⟩ : syracuseStep 8459309 = 3172241) B3172241
theorem B3961907 : Blo 1760081 3961907 := bstep (se 1 (by rfl) ⟨2971430, by rfl⟩ : syracuseStep 3961907 = 5942861) B5942861
theorem B3011671 : Blo 1760081 3011671 := bstep (se 1 (by rfl) ⟨2258753, by rfl⟩ : syracuseStep 3011671 = 4517507) B4517507
theorem B3961943 : Blo 1760081 3961943 := bstep (se 1 (by rfl) ⟨2971457, by rfl⟩ : syracuseStep 3961943 = 5942915) B5942915
theorem B2643083 : Blo 1760081 2643083 := bstep (se 1 (by rfl) ⟨1982312, by rfl⟩ : syracuseStep 2643083 = 3964625) B3964625
theorem B2643095 : Blo 1760081 2643095 := bstep (se 1 (by rfl) ⟨1982321, by rfl⟩ : syracuseStep 2643095 = 3964643) B3964643
theorem B3962123 : Blo 1760081 3962123 := bstep (se 1 (by rfl) ⟨2971592, by rfl⟩ : syracuseStep 3962123 = 5943185) B5943185
theorem B3962177 : Blo 1760081 3962177 := bstep (se 2 (by rfl) ⟨1485816, by rfl⟩ : syracuseStep 3962177 = 2971633) B2971633
theorem B2971019 : Blo 1760081 2971019 := bstep (se 1 (by rfl) ⟨2228264, by rfl⟩ : syracuseStep 2971019 = 4456529) B4456529
theorem B10024343 : Blo 1760081 10024343 := bstep (se 1 (by rfl) ⟨7518257, by rfl⟩ : syracuseStep 10024343 = 15036515) B15036515
theorem B8918423 : Blo 1760081 8918423 := bstep (se 1 (by rfl) ⟨6688817, by rfl⟩ : syracuseStep 8918423 = 13377635) B13377635
theorem B2971147 : Blo 1760081 2971147 := bstep (se 1 (by rfl) ⟨2228360, by rfl⟩ : syracuseStep 2971147 = 4456721) B4456721
theorem B3962393 : Blo 1760081 3962393 := bstep (se 2 (by rfl) ⟨1485897, by rfl⟩ : syracuseStep 3962393 = 2971795) B2971795
theorem B12695075 : Blo 1760081 12695075 := bstep (se 1 (by rfl) ⟨9521306, by rfl⟩ : syracuseStep 12695075 = 19042613) B19042613
theorem B6690397 : Blo 1760081 6690397 := bstep (se 3 (by rfl) ⟨1254449, by rfl⟩ : syracuseStep 6690397 = 2508899) B2508899
theorem B3962483 : Blo 1760081 3962483 := bstep (se 1 (by rfl) ⟨2971862, by rfl⟩ : syracuseStep 3962483 = 5943725) B5943725
theorem B3053207 : Blo 1760081 3053207 := bstep (se 1 (by rfl) ⟨2289905, by rfl⟩ : syracuseStep 3053207 = 4579811) B4579811
theorem B3962519 : Blo 1760081 3962519 := bstep (se 1 (by rfl) ⟨2971889, by rfl⟩ : syracuseStep 3962519 = 5943779) B5943779
theorem B2971289 : Blo 1760081 2971289 := bstep (se 2 (by rfl) ⟨1114233, by rfl⟩ : syracuseStep 2971289 = 2228467) B2228467
theorem B1980139 : Blo 1760081 1980139 := bstep (se 1 (by rfl) ⟨1485104, by rfl⟩ : syracuseStep 1980139 = 2970209) B2970209
theorem B2971417 : Blo 1760081 2971417 := bstep (se 2 (by rfl) ⟨1114281, by rfl⟩ : syracuseStep 2971417 = 2228563) B2228563
theorem B3962699 : Blo 1760081 3962699 := bstep (se 1 (by rfl) ⟨2972024, by rfl⟩ : syracuseStep 3962699 = 5944049) B5944049
theorem B1980247 : Blo 1760081 1980247 := bstep (se 1 (by rfl) ⟨1485185, by rfl⟩ : syracuseStep 1980247 = 2970371) B2970371
theorem B3962753 : Blo 1760081 3962753 := bstep (se 2 (by rfl) ⟨1486032, by rfl⟩ : syracuseStep 3962753 = 2972065) B2972065
theorem B51460019 : Blo 1760081 51460019 := bstep (se 1 (by rfl) ⟨38595014, by rfl⟩ : syracuseStep 51460019 = 77190029) B77190029
theorem B5945291 : Blo 1760081 5945291 := bstep (se 1 (by rfl) ⟨4458968, by rfl⟩ : syracuseStep 5945291 = 8917937) B8917937
theorem B8910809 : Blo 1760081 8910809 := bstep (se 2 (by rfl) ⟨3341553, by rfl⟩ : syracuseStep 8910809 = 6683107) B6683107
theorem B1980427 : Blo 1760081 1980427 := bstep (se 1 (by rfl) ⟨1485320, by rfl⟩ : syracuseStep 1980427 = 2970641) B2970641
theorem B3217495 : Blo 1760081 3217495 := bstep (se 1 (by rfl) ⟨2413121, by rfl⟩ : syracuseStep 3217495 = 4826243) B4826243
theorem B3962969 : Blo 1760081 3962969 := bstep (se 2 (by rfl) ⟨1486113, by rfl⟩ : syracuseStep 3962969 = 2972227) B2972227
theorem B1980535 : Blo 1760081 1980535 := bstep (se 1 (by rfl) ⟨1485401, by rfl⟩ : syracuseStep 1980535 = 2970803) B2970803
theorem B7518359 : Blo 1760081 7518359 := bstep (se 1 (by rfl) ⟨5638769, by rfl⟩ : syracuseStep 7518359 = 11277539) B11277539
theorem B3963059 : Blo 1760081 3963059 := bstep (se 1 (by rfl) ⟨2972294, by rfl⟩ : syracuseStep 3963059 = 5944589) B5944589
theorem B3963095 : Blo 1760081 3963095 := bstep (se 1 (by rfl) ⟨2972321, by rfl⟩ : syracuseStep 3963095 = 5944643) B5944643
theorem B5945561 : Blo 1760081 5945561 := bstep (se 2 (by rfl) ⟨2229585, by rfl⟩ : syracuseStep 5945561 = 4459171) B4459171
theorem B1980715 : Blo 1760081 1980715 := bstep (se 1 (by rfl) ⟨1485536, by rfl⟩ : syracuseStep 1980715 = 2971073) B2971073
theorem B6682925 : Blo 1760081 6682925 := bstep (se 3 (by rfl) ⟨1253048, by rfl⟩ : syracuseStep 6682925 = 2506097) B2506097
theorem B2971991 : Blo 1760081 2971991 := bstep (se 1 (by rfl) ⟨2228993, by rfl⟩ : syracuseStep 2971991 = 4457987) B4457987
theorem B3963275 : Blo 1760081 3963275 := bstep (se 1 (by rfl) ⟨2972456, by rfl⟩ : syracuseStep 3963275 = 5944913) B5944913
theorem B1980823 : Blo 1760081 1980823 := bstep (se 1 (by rfl) ⟨1485617, by rfl⟩ : syracuseStep 1980823 = 2971235) B2971235
theorem B3963329 : Blo 1760081 3963329 := bstep (se 2 (by rfl) ⟨1486248, by rfl⟩ : syracuseStep 3963329 = 2972497) B2972497
theorem B2972119 : Blo 1760081 2972119 := bstep (se 1 (by rfl) ⟨2229089, by rfl⟩ : syracuseStep 2972119 = 4458179) B4458179
theorem B1981003 : Blo 1760081 1981003 := bstep (se 1 (by rfl) ⟨1485752, by rfl⟩ : syracuseStep 1981003 = 2971505) B2971505
theorem B5716631 : Blo 1760081 5716631 := bstep (se 1 (by rfl) ⟨4287473, by rfl⟩ : syracuseStep 5716631 = 8574947) B8574947
theorem B3963545 : Blo 1760081 3963545 := bstep (se 2 (by rfl) ⟨1486329, by rfl⟩ : syracuseStep 3963545 = 2972659) B2972659
theorem B13376177 : Blo 1760081 13376177 := bstep (se 2 (by rfl) ⟨5016066, by rfl⟩ : syracuseStep 13376177 = 10032133) B10032133
theorem B11279027 : Blo 1760081 11279027 := bstep (se 1 (by rfl) ⟨8459270, by rfl⟩ : syracuseStep 11279027 = 16918541) B16918541
theorem B5356211 : Blo 1760081 5356211 := bstep (se 1 (by rfl) ⟨4017158, by rfl⟩ : syracuseStep 5356211 = 8034317) B8034317
theorem B1981111 : Blo 1760081 1981111 := bstep (se 1 (by rfl) ⟨1485833, by rfl⟩ : syracuseStep 1981111 = 2971667) B2971667
theorem B3963635 : Blo 1760081 3963635 := bstep (se 1 (by rfl) ⟨2972726, by rfl⟩ : syracuseStep 3963635 = 5945453) B5945453
theorem B3963671 : Blo 1760081 3963671 := bstep (se 1 (by rfl) ⟨2972753, by rfl⟩ : syracuseStep 3963671 = 5945507) B5945507
theorem B7519027 : Blo 1760081 7519027 := bstep (se 1 (by rfl) ⟨5639270, by rfl⟩ : syracuseStep 7519027 = 11278541) B11278541
theorem B4455233 : Blo 1760081 4455233 := bstep (se 2 (by rfl) ⟨1670712, by rfl⟩ : syracuseStep 4455233 = 3341425) B3341425
theorem B11279179 : Blo 1760081 11279179 := bstep (se 1 (by rfl) ⟨8459384, by rfl⟩ : syracuseStep 11279179 = 16918769) B16918769
theorem B1760087 : Blo 1760081 1760087 := bstep (se 1 (by rfl) ⟨1320065, by rfl⟩ : syracuseStep 1760087 = 2640131) B2640131
theorem B1760107 : Blo 1760081 1760107 := bstep (se 1 (by rfl) ⟨1320080, by rfl⟩ : syracuseStep 1760107 = 2640161) B2640161
theorem B1981291 : Blo 1760081 1981291 := bstep (se 1 (by rfl) ⟨1485968, by rfl⟩ : syracuseStep 1981291 = 2971937) B2971937
theorem B1760119 : Blo 1760081 1760119 := bstep (se 1 (by rfl) ⟨1320089, by rfl⟩ : syracuseStep 1760119 = 2640179) B2640179
theorem B1760139 : Blo 1760081 1760139 := bstep (se 1 (by rfl) ⟨1320104, by rfl⟩ : syracuseStep 1760139 = 2640209) B2640209
theorem B1760151 : Blo 1760081 1760151 := bstep (se 1 (by rfl) ⟨1320113, by rfl⟩ : syracuseStep 1760151 = 2640227) B2640227
theorem B5946263 : Blo 1760081 5946263 := bstep (se 1 (by rfl) ⟨4459697, by rfl⟩ : syracuseStep 5946263 = 8919395) B8919395
theorem B1760171 : Blo 1760081 1760171 := bstep (se 1 (by rfl) ⟨1320128, by rfl⟩ : syracuseStep 1760171 = 2640257) B2640257
theorem B1760183 : Blo 1760081 1760183 := bstep (se 1 (by rfl) ⟨1320137, by rfl⟩ : syracuseStep 1760183 = 2640275) B2640275
theorem B1784759 : Blo 1760081 1784759 := bstep (se 1 (by rfl) ⟨1338569, by rfl⟩ : syracuseStep 1784759 = 2677139) B2677139
theorem B1760203 : Blo 1760081 1760203 := bstep (se 1 (by rfl) ⟨1320152, by rfl⟩ : syracuseStep 1760203 = 2640305) B2640305
theorem B3963851 : Blo 1760081 3963851 := bstep (se 1 (by rfl) ⟨2972888, by rfl⟩ : syracuseStep 3963851 = 5945777) B5945777
theorem B1760215 : Blo 1760081 1760215 := bstep (se 1 (by rfl) ⟨1320161, by rfl⟩ : syracuseStep 1760215 = 2640323) B2640323
theorem B1981399 : Blo 1760081 1981399 := bstep (se 1 (by rfl) ⟨1486049, by rfl⟩ : syracuseStep 1981399 = 2972099) B2972099
theorem B1760235 : Blo 1760081 1760235 := bstep (se 1 (by rfl) ⟨1320176, by rfl⟩ : syracuseStep 1760235 = 2640353) B2640353
theorem B1760247 : Blo 1760081 1760247 := bstep (se 1 (by rfl) ⟨1320185, by rfl⟩ : syracuseStep 1760247 = 2640371) B2640371
theorem B3963905 : Blo 1760081 3963905 := bstep (se 2 (by rfl) ⟨1486464, by rfl⟩ : syracuseStep 3963905 = 2972929) B2972929
theorem B1760267 : Blo 1760081 1760267 := bstep (se 1 (by rfl) ⟨1320200, by rfl⟩ : syracuseStep 1760267 = 2640401) B2640401
theorem B1760279 : Blo 1760081 1760279 := bstep (se 1 (by rfl) ⟨1320209, by rfl⟩ : syracuseStep 1760279 = 2640419) B2640419
theorem B1760299 : Blo 1760081 1760299 := bstep (se 1 (by rfl) ⟨1320224, by rfl⟩ : syracuseStep 1760299 = 2640449) B2640449
theorem B1760311 : Blo 1760081 1760311 := bstep (se 1 (by rfl) ⟨1320233, by rfl⟩ : syracuseStep 1760311 = 2640467) B2640467
theorem B1760331 : Blo 1760081 1760331 := bstep (se 1 (by rfl) ⟨1320248, by rfl⟩ : syracuseStep 1760331 = 2640497) B2640497
theorem B2972747 : Blo 1760081 2972747 := bstep (se 1 (by rfl) ⟨2229560, by rfl⟩ : syracuseStep 2972747 = 4459121) B4459121
theorem B1760343 : Blo 1760081 1760343 := bstep (se 1 (by rfl) ⟨1320257, by rfl⟩ : syracuseStep 1760343 = 2640515) B2640515
theorem B1760363 : Blo 1760081 1760363 := bstep (se 1 (by rfl) ⟨1320272, by rfl⟩ : syracuseStep 1760363 = 2640545) B2640545
theorem B1760375 : Blo 1760081 1760375 := bstep (se 1 (by rfl) ⟨1320281, by rfl⟩ : syracuseStep 1760375 = 2640563) B2640563
theorem B1760395 : Blo 1760081 1760395 := bstep (se 1 (by rfl) ⟨1320296, by rfl⟩ : syracuseStep 1760395 = 2640593) B2640593
theorem B1981579 : Blo 1760081 1981579 := bstep (se 1 (by rfl) ⟨1486184, by rfl⟩ : syracuseStep 1981579 = 2972369) B2972369
theorem B1760407 : Blo 1760081 1760407 := bstep (se 1 (by rfl) ⟨1320305, by rfl⟩ : syracuseStep 1760407 = 2640611) B2640611
theorem B13376663 : Blo 1760081 13376663 := bstep (se 1 (by rfl) ⟨10032497, by rfl⟩ : syracuseStep 13376663 = 20064995) B20064995
theorem B1760427 : Blo 1760081 1760427 := bstep (se 1 (by rfl) ⟨1320320, by rfl⟩ : syracuseStep 1760427 = 2640641) B2640641
theorem B4758707 : Blo 1760081 4758707 := bstep (se 1 (by rfl) ⟨3569030, by rfl⟩ : syracuseStep 4758707 = 7138061) B7138061
theorem B1760439 : Blo 1760081 1760439 := bstep (se 1 (by rfl) ⟨1320329, by rfl⟩ : syracuseStep 1760439 = 2640659) B2640659
theorem B1760459 : Blo 1760081 1760459 := bstep (se 1 (by rfl) ⟨1320344, by rfl⟩ : syracuseStep 1760459 = 2640689) B2640689
theorem B2972875 : Blo 1760081 2972875 := bstep (se 1 (by rfl) ⟨2229656, by rfl⟩ : syracuseStep 2972875 = 4459313) B4459313
theorem B1760471 : Blo 1760081 1760471 := bstep (se 1 (by rfl) ⟨1320353, by rfl⟩ : syracuseStep 1760471 = 2640707) B2640707
theorem B3964121 : Blo 1760081 3964121 := bstep (se 2 (by rfl) ⟨1486545, by rfl⟩ : syracuseStep 3964121 = 2973091) B2973091
theorem B1760491 : Blo 1760081 1760491 := bstep (se 1 (by rfl) ⟨1320368, by rfl⟩ : syracuseStep 1760491 = 2640737) B2640737
theorem B1760503 : Blo 1760081 1760503 := bstep (se 1 (by rfl) ⟨1320377, by rfl⟩ : syracuseStep 1760503 = 2640755) B2640755
theorem B1785079 : Blo 1760081 1785079 := bstep (se 1 (by rfl) ⟨1338809, by rfl⟩ : syracuseStep 1785079 = 2677619) B2677619
theorem B1981687 : Blo 1760081 1981687 := bstep (se 1 (by rfl) ⟨1486265, by rfl⟩ : syracuseStep 1981687 = 2972531) B2972531
theorem B3341569 : Blo 1760081 3341569 := bstep (se 2 (by rfl) ⟨1253088, by rfl⟩ : syracuseStep 3341569 = 2506177) B2506177
theorem B1760523 : Blo 1760081 1760523 := bstep (se 1 (by rfl) ⟨1320392, by rfl⟩ : syracuseStep 1760523 = 2640785) B2640785
theorem B1760535 : Blo 1760081 1760535 := bstep (se 1 (by rfl) ⟨1320401, by rfl⟩ : syracuseStep 1760535 = 2640803) B2640803
theorem B2678039 : Blo 1760081 2678039 := bstep (se 1 (by rfl) ⟨2008529, by rfl⟩ : syracuseStep 2678039 = 4017059) B4017059
theorem B3759385 : Blo 1760081 3759385 := bstep (se 2 (by rfl) ⟨1409769, by rfl⟩ : syracuseStep 3759385 = 2819539) B2819539
theorem B1760555 : Blo 1760081 1760555 := bstep (se 1 (by rfl) ⟨1320416, by rfl⟩ : syracuseStep 1760555 = 2640833) B2640833
theorem B7142701 : Blo 1760081 7142701 := bstep (se 3 (by rfl) ⟨1339256, by rfl⟩ : syracuseStep 7142701 = 2678513) B2678513
theorem B3964211 : Blo 1760081 3964211 := bstep (se 1 (by rfl) ⟨2973158, by rfl⟩ : syracuseStep 3964211 = 5946317) B5946317
theorem B1760567 : Blo 1760081 1760567 := bstep (se 1 (by rfl) ⟨1320425, by rfl⟩ : syracuseStep 1760567 = 2640851) B2640851
theorem B1760587 : Blo 1760081 1760587 := bstep (se 1 (by rfl) ⟨1320440, by rfl⟩ : syracuseStep 1760587 = 2640881) B2640881
theorem B1760599 : Blo 1760081 1760599 := bstep (se 1 (by rfl) ⟨1320449, by rfl⟩ : syracuseStep 1760599 = 2640899) B2640899
theorem B3964247 : Blo 1760081 3964247 := bstep (se 1 (by rfl) ⟨2973185, by rfl⟩ : syracuseStep 3964247 = 5946371) B5946371
theorem B4455769 : Blo 1760081 4455769 := bstep (se 2 (by rfl) ⟨1670913, by rfl⟩ : syracuseStep 4455769 = 3341827) B3341827
theorem B2973017 : Blo 1760081 2973017 := bstep (se 2 (by rfl) ⟨1114881, by rfl⟩ : syracuseStep 2973017 = 2229763) B2229763
theorem B1760619 : Blo 1760081 1760619 := bstep (se 1 (by rfl) ⟨1320464, by rfl⟩ : syracuseStep 1760619 = 2640929) B2640929
theorem B1760631 : Blo 1760081 1760631 := bstep (se 1 (by rfl) ⟨1320473, by rfl⟩ : syracuseStep 1760631 = 2640947) B2640947
theorem B1760651 : Blo 1760081 1760651 := bstep (se 1 (by rfl) ⟨1320488, by rfl⟩ : syracuseStep 1760651 = 2640977) B2640977
theorem B1760663 : Blo 1760081 1760663 := bstep (se 1 (by rfl) ⟨1320497, by rfl⟩ : syracuseStep 1760663 = 2640995) B2640995
theorem B1760683 : Blo 1760081 1760683 := bstep (se 1 (by rfl) ⟨1320512, by rfl⟩ : syracuseStep 1760683 = 2641025) B2641025
theorem B1981867 : Blo 1760081 1981867 := bstep (se 1 (by rfl) ⟨1486400, by rfl⟩ : syracuseStep 1981867 = 2972801) B2972801
theorem B5946803 : Blo 1760081 5946803 := bstep (se 1 (by rfl) ⟨4460102, by rfl⟩ : syracuseStep 5946803 = 8920205) B8920205
theorem B1760695 : Blo 1760081 1760695 := bstep (se 1 (by rfl) ⟨1320521, by rfl⟩ : syracuseStep 1760695 = 2641043) B2641043
theorem B1760715 : Blo 1760081 1760715 := bstep (se 1 (by rfl) ⟨1320536, by rfl⟩ : syracuseStep 1760715 = 2641073) B2641073
theorem B1760727 : Blo 1760081 1760727 := bstep (se 1 (by rfl) ⟨1320545, by rfl⟩ : syracuseStep 1760727 = 2641091) B2641091
theorem B2973145 : Blo 1760081 2973145 := bstep (se 2 (by rfl) ⟨1114929, by rfl⟩ : syracuseStep 2973145 = 2229859) B2229859
theorem B1760747 : Blo 1760081 1760747 := bstep (se 1 (by rfl) ⟨1320560, by rfl⟩ : syracuseStep 1760747 = 2641121) B2641121
theorem B1760759 : Blo 1760081 1760759 := bstep (se 1 (by rfl) ⟨1320569, by rfl⟩ : syracuseStep 1760759 = 2641139) B2641139
theorem B1760779 : Blo 1760081 1760779 := bstep (se 1 (by rfl) ⟨1320584, by rfl⟩ : syracuseStep 1760779 = 2641169) B2641169
theorem B3964427 : Blo 1760081 3964427 := bstep (se 1 (by rfl) ⟨2973320, by rfl⟩ : syracuseStep 3964427 = 5946641) B5946641
theorem B1760791 : Blo 1760081 1760791 := bstep (se 1 (by rfl) ⟨1320593, by rfl⟩ : syracuseStep 1760791 = 2641187) B2641187
theorem B1981975 : Blo 1760081 1981975 := bstep (se 1 (by rfl) ⟨1486481, by rfl⟩ : syracuseStep 1981975 = 2972963) B2972963
theorem B1760811 : Blo 1760081 1760811 := bstep (se 1 (by rfl) ⟨1320608, by rfl⟩ : syracuseStep 1760811 = 2641217) B2641217
theorem B8912429 : Blo 1760081 8912429 := bstep (se 3 (by rfl) ⟨1671080, by rfl⟩ : syracuseStep 8912429 = 3342161) B3342161
theorem B1760823 : Blo 1760081 1760823 := bstep (se 1 (by rfl) ⟨1320617, by rfl⟩ : syracuseStep 1760823 = 2641235) B2641235
theorem B3964481 : Blo 1760081 3964481 := bstep (se 2 (by rfl) ⟨1486680, by rfl⟩ : syracuseStep 3964481 = 2973361) B2973361
theorem B1760843 : Blo 1760081 1760843 := bstep (se 1 (by rfl) ⟨1320632, by rfl⟩ : syracuseStep 1760843 = 2641265) B2641265
theorem B3341911 : Blo 1760081 3341911 := bstep (se 1 (by rfl) ⟨2506433, by rfl⟩ : syracuseStep 3341911 = 5012867) B5012867
theorem B1760855 : Blo 1760081 1760855 := bstep (se 1 (by rfl) ⟨1320641, by rfl⟩ : syracuseStep 1760855 = 2641283) B2641283
theorem B1760875 : Blo 1760081 1760875 := bstep (se 1 (by rfl) ⟨1320656, by rfl⟩ : syracuseStep 1760875 = 2641313) B2641313
theorem B1760887 : Blo 1760081 1760887 := bstep (se 1 (by rfl) ⟨1320665, by rfl⟩ : syracuseStep 1760887 = 2641331) B2641331
theorem B1760907 : Blo 1760081 1760907 := bstep (se 1 (by rfl) ⟨1320680, by rfl⟩ : syracuseStep 1760907 = 2641361) B2641361
theorem B1760919 : Blo 1760081 1760919 := bstep (se 1 (by rfl) ⟨1320689, by rfl⟩ : syracuseStep 1760919 = 2641379) B2641379
theorem B16293527 : Blo 1760081 16293527 := bstep (se 1 (by rfl) ⟨12220145, by rfl⟩ : syracuseStep 16293527 = 24440291) B24440291
theorem B2506393 : Blo 1760081 2506393 := bstep (se 2 (by rfl) ⟨939897, by rfl⟩ : syracuseStep 2506393 = 1879795) B1879795
theorem B1760939 : Blo 1760081 1760939 := bstep (se 1 (by rfl) ⟨1320704, by rfl⟩ : syracuseStep 1760939 = 2641409) B2641409
theorem B10034867 : Blo 1760081 10034867 := bstep (se 1 (by rfl) ⟨7526150, by rfl⟩ : syracuseStep 10034867 = 15052301) B15052301
theorem B1760951 : Blo 1760081 1760951 := bstep (se 1 (by rfl) ⟨1320713, by rfl⟩ : syracuseStep 1760951 = 2641427) B2641427
theorem B6684353 : Blo 1760081 6684353 := bstep (se 2 (by rfl) ⟨2506632, by rfl⟩ : syracuseStep 6684353 = 5013265) B5013265
theorem B2227915 : Blo 1760081 2227915 := bstep (se 1 (by rfl) ⟨1670936, by rfl⟩ : syracuseStep 2227915 = 3341873) B3341873
theorem B1760971 : Blo 1760081 1760971 := bstep (se 1 (by rfl) ⟨1320728, by rfl⟩ : syracuseStep 1760971 = 2641457) B2641457
theorem B1982155 : Blo 1760081 1982155 := bstep (se 1 (by rfl) ⟨1486616, by rfl⟩ : syracuseStep 1982155 = 2973233) B2973233
theorem B1760983 : Blo 1760081 1760983 := bstep (se 1 (by rfl) ⟨1320737, by rfl⟩ : syracuseStep 1760983 = 2641475) B2641475
theorem B1761003 : Blo 1760081 1761003 := bstep (se 1 (by rfl) ⟨1320752, by rfl⟩ : syracuseStep 1761003 = 2641505) B2641505
theorem B1761015 : Blo 1760081 1761015 := bstep (se 1 (by rfl) ⟨1320761, by rfl⟩ : syracuseStep 1761015 = 2641523) B2641523
theorem B1761035 : Blo 1760081 1761035 := bstep (se 1 (by rfl) ⟨1320776, by rfl⟩ : syracuseStep 1761035 = 2641553) B2641553
theorem B1761047 : Blo 1760081 1761047 := bstep (se 1 (by rfl) ⟨1320785, by rfl⟩ : syracuseStep 1761047 = 2641571) B2641571
theorem B1761067 : Blo 1760081 1761067 := bstep (se 1 (by rfl) ⟨1320800, by rfl⟩ : syracuseStep 1761067 = 2641601) B2641601
theorem B3342131 : Blo 1760081 3342131 := bstep (se 1 (by rfl) ⟨2506598, by rfl⟩ : syracuseStep 3342131 = 5013197) B5013197
theorem B1761079 : Blo 1760081 1761079 := bstep (se 1 (by rfl) ⟨1320809, by rfl⟩ : syracuseStep 1761079 = 2641619) B2641619
theorem B1982263 : Blo 1760081 1982263 := bstep (se 1 (by rfl) ⟨1486697, by rfl⟩ : syracuseStep 1982263 = 2973395) B2973395
theorem B5013323 : Blo 1760081 5013323 := bstep (se 1 (by rfl) ⟨3759992, by rfl⟩ : syracuseStep 5013323 = 7519985) B7519985
theorem B10026827 : Blo 1760081 10026827 := bstep (se 1 (by rfl) ⟨7520120, by rfl⟩ : syracuseStep 10026827 = 15040241) B15040241
theorem B1761099 : Blo 1760081 1761099 := bstep (se 1 (by rfl) ⟨1320824, by rfl⟩ : syracuseStep 1761099 = 2641649) B2641649
theorem B1761111 : Blo 1760081 1761111 := bstep (se 1 (by rfl) ⟨1320833, by rfl⟩ : syracuseStep 1761111 = 2641667) B2641667
theorem B1761131 : Blo 1760081 1761131 := bstep (se 1 (by rfl) ⟨1320848, by rfl⟩ : syracuseStep 1761131 = 2641697) B2641697
theorem B1761143 : Blo 1760081 1761143 := bstep (se 1 (by rfl) ⟨1320857, by rfl⟩ : syracuseStep 1761143 = 2641715) B2641715
theorem B9035651 : Blo 1760081 9035651 := bstep (se 1 (by rfl) ⟨6776738, by rfl⟩ : syracuseStep 9035651 = 13553477) B13553477
theorem B10166147 : Blo 1760081 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B1761163 : Blo 1760081 1761163 := bstep (se 1 (by rfl) ⟨1320872, by rfl⟩ : syracuseStep 1761163 = 2641745) B2641745
theorem B9035671 : Blo 1760081 9035671 := bstep (se 1 (by rfl) ⟨6776753, by rfl⟩ : syracuseStep 9035671 = 13553507) B13553507
theorem B1761175 : Blo 1760081 1761175 := bstep (se 1 (by rfl) ⟨1320881, by rfl⟩ : syracuseStep 1761175 = 2641763) B2641763
theorem B1761195 : Blo 1760081 1761195 := bstep (se 1 (by rfl) ⟨1320896, by rfl⟩ : syracuseStep 1761195 = 2641793) B2641793
theorem B1761207 : Blo 1760081 1761207 := bstep (se 1 (by rfl) ⟨1320905, by rfl⟩ : syracuseStep 1761207 = 2641811) B2641811
theorem B1761227 : Blo 1760081 1761227 := bstep (se 1 (by rfl) ⟨1320920, by rfl⟩ : syracuseStep 1761227 = 2641841) B2641841
theorem B1761239 : Blo 1760081 1761239 := bstep (se 1 (by rfl) ⟨1320929, by rfl⟩ : syracuseStep 1761239 = 2641859) B2641859
theorem B2678743 : Blo 1760081 2678743 := bstep (se 1 (by rfl) ⟨2009057, by rfl⟩ : syracuseStep 2678743 = 4018115) B4018115
theorem B12689369 : Blo 1760081 12689369 := bstep (se 2 (by rfl) ⟨4758513, by rfl⟩ : syracuseStep 12689369 = 9517027) B9517027
theorem B1761259 : Blo 1760081 1761259 := bstep (se 1 (by rfl) ⟨1320944, by rfl⟩ : syracuseStep 1761259 = 2641889) B2641889
theorem B1761271 : Blo 1760081 1761271 := bstep (se 1 (by rfl) ⟨1320953, by rfl⟩ : syracuseStep 1761271 = 2641907) B2641907
theorem B1761287 : Blo 1760081 1761287 := bstep (se 1 (by rfl) ⟨1320965, by rfl⟩ : syracuseStep 1761287 = 2641931) B2641931
theorem B5013515 : Blo 1760081 5013515 := bstep (se 1 (by rfl) ⟨3760136, by rfl⟩ : syracuseStep 5013515 = 7520273) B7520273
theorem B2228239 : Blo 1760081 2228239 := bstep (se 1 (by rfl) ⟨1671179, by rfl⟩ : syracuseStep 2228239 = 3342359) B3342359
theorem B1761295 : Blo 1760081 1761295 := bstep (se 1 (by rfl) ⟨1320971, by rfl⟩ : syracuseStep 1761295 = 2641943) B2641943
theorem B1761339 : Blo 1760081 1761339 := bstep (se 1 (by rfl) ⟨1321004, by rfl⟩ : syracuseStep 1761339 = 2642009) B2642009
theorem B1761415 : Blo 1760081 1761415 := bstep (se 1 (by rfl) ⟨1321061, by rfl⟩ : syracuseStep 1761415 = 2642123) B2642123
theorem B1761423 : Blo 1760081 1761423 := bstep (se 1 (by rfl) ⟨1321067, by rfl⟩ : syracuseStep 1761423 = 2642135) B2642135
theorem B2228411 : Blo 1760081 2228411 := bstep (se 1 (by rfl) ⟨1671308, by rfl⟩ : syracuseStep 2228411 = 3342617) B3342617
theorem B1761467 : Blo 1760081 1761467 := bstep (se 1 (by rfl) ⟨1321100, by rfl⟩ : syracuseStep 1761467 = 2642201) B2642201
theorem B1761543 : Blo 1760081 1761543 := bstep (se 1 (by rfl) ⟨1321157, by rfl⟩ : syracuseStep 1761543 = 2642315) B2642315
theorem B1761551 : Blo 1760081 1761551 := bstep (se 1 (by rfl) ⟨1321163, by rfl⟩ : syracuseStep 1761551 = 2642327) B2642327
theorem B2679097 : Blo 1760081 2679097 := bstep (se 2 (by rfl) ⟨1004661, by rfl⟩ : syracuseStep 2679097 = 2009323) B2009323
theorem B1761595 : Blo 1760081 1761595 := bstep (se 1 (by rfl) ⟨1321196, by rfl⟩ : syracuseStep 1761595 = 2642393) B2642393
theorem B28574045 : Blo 1760081 28574045 := bstep (se 3 (by rfl) ⟨5357633, by rfl⟩ : syracuseStep 28574045 = 10715267) B10715267
theorem B1761671 : Blo 1760081 1761671 := bstep (se 1 (by rfl) ⟨1321253, by rfl⟩ : syracuseStep 1761671 = 2642507) B2642507
theorem B1761679 : Blo 1760081 1761679 := bstep (se 1 (by rfl) ⟨1321259, by rfl⟩ : syracuseStep 1761679 = 2642519) B2642519
theorem B1761723 : Blo 1760081 1761723 := bstep (se 1 (by rfl) ⟨1321292, by rfl⟩ : syracuseStep 1761723 = 2642585) B2642585
theorem B12689885 : Blo 1760081 12689885 := bstep (se 3 (by rfl) ⟨2379353, by rfl⟩ : syracuseStep 12689885 = 4758707) B4758707
theorem B13369859 : Blo 1760081 13369859 := bstep (se 1 (by rfl) ⟨10027394, by rfl⟩ : syracuseStep 13369859 = 20054789) B20054789
theorem B1761799 : Blo 1760081 1761799 := bstep (se 1 (by rfl) ⟨1321349, by rfl⟩ : syracuseStep 1761799 = 2642699) B2642699
theorem B1761807 : Blo 1760081 1761807 := bstep (se 1 (by rfl) ⟨1321355, by rfl⟩ : syracuseStep 1761807 = 2642711) B2642711
theorem B1761851 : Blo 1760081 1761851 := bstep (se 1 (by rfl) ⟨1321388, by rfl⟩ : syracuseStep 1761851 = 2642777) B2642777
theorem B1761927 : Blo 1760081 1761927 := bstep (se 1 (by rfl) ⟨1321445, by rfl⟩ : syracuseStep 1761927 = 2642891) B2642891
theorem B1761935 : Blo 1760081 1761935 := bstep (se 1 (by rfl) ⟨1321451, by rfl⟩ : syracuseStep 1761935 = 2642903) B2642903
theorem B1761979 : Blo 1760081 1761979 := bstep (se 1 (by rfl) ⟨1321484, by rfl⟩ : syracuseStep 1761979 = 2642969) B2642969
theorem B7521025 : Blo 1760081 7521025 := bstep (se 2 (by rfl) ⟨2820384, by rfl⟩ : syracuseStep 7521025 = 5640769) B5640769
theorem B2507527 : Blo 1760081 2507527 := bstep (se 1 (by rfl) ⟨1880645, by rfl⟩ : syracuseStep 2507527 = 3761291) B3761291
theorem B1762055 : Blo 1760081 1762055 := bstep (se 1 (by rfl) ⟨1321541, by rfl⟩ : syracuseStep 1762055 = 2643083) B2643083
theorem B4457227 : Blo 1760081 4457227 := bstep (se 1 (by rfl) ⟨3342920, by rfl⟩ : syracuseStep 4457227 = 6685841) B6685841
theorem B1762063 : Blo 1760081 1762063 := bstep (se 1 (by rfl) ⟨1321547, by rfl⟩ : syracuseStep 1762063 = 2643095) B2643095
theorem B9519923 : Blo 1760081 9519923 := bstep (se 1 (by rfl) ⟨7139942, by rfl⟩ : syracuseStep 9519923 = 14279885) B14279885
theorem B4457369 : Blo 1760081 4457369 := bstep (se 2 (by rfl) ⟨1671513, by rfl⟩ : syracuseStep 4457369 = 3343027) B3343027
theorem B8463383 : Blo 1760081 8463383 := bstep (se 1 (by rfl) ⟨6347537, by rfl⟩ : syracuseStep 8463383 = 12695075) B12695075
theorem B4457531 : Blo 1760081 4457531 := bstep (se 1 (by rfl) ⟨3343148, by rfl⟩ : syracuseStep 4457531 = 6686297) B6686297
theorem B2229383 : Blo 1760081 2229383 := bstep (se 1 (by rfl) ⟨1672037, by rfl⟩ : syracuseStep 2229383 = 3344075) B3344075
theorem B2114731 : Blo 1760081 2114731 := bstep (se 1 (by rfl) ⟨1586048, by rfl⟩ : syracuseStep 2114731 = 3172097) B3172097
theorem B12870829 : Blo 1760081 12870829 := bstep (se 3 (by rfl) ⟨2413280, by rfl⟩ : syracuseStep 12870829 = 4826561) B4826561
theorem B9520421 : Blo 1760081 9520421 := bstep (se 4 (by rfl) ⟨892539, by rfl⟩ : syracuseStep 9520421 = 1785079) B1785079
theorem B5940539 : Blo 1760081 5940539 := bstep (se 1 (by rfl) ⟨4455404, by rfl⟩ : syracuseStep 5940539 = 8910809) B8910809
theorem B28558727 : Blo 1760081 28558727 := bstep (se 1 (by rfl) ⟨21419045, by rfl⟩ : syracuseStep 28558727 = 42838091) B42838091
theorem B4457875 : Blo 1760081 4457875 := bstep (se 1 (by rfl) ⟨3343406, by rfl⟩ : syracuseStep 4457875 = 6686813) B6686813
theorem B3343817 : Blo 1760081 3343817 := bstep (se 2 (by rfl) ⟨1253931, by rfl⟩ : syracuseStep 3343817 = 2507863) B2507863
theorem B11281949 : Blo 1760081 11281949 := bstep (se 3 (by rfl) ⟨2115365, by rfl⟩ : syracuseStep 11281949 = 4230731) B4230731
theorem B4458017 : Blo 1760081 4458017 := bstep (se 2 (by rfl) ⟨1671756, by rfl⟩ : syracuseStep 4458017 = 3343513) B3343513
theorem B2508347 : Blo 1760081 2508347 := bstep (se 1 (by rfl) ⟨1881260, by rfl⟩ : syracuseStep 2508347 = 3762521) B3762521
theorem B6686327 : Blo 1760081 6686327 := bstep (se 1 (by rfl) ⟨5014745, by rfl⟩ : syracuseStep 6686327 = 10029491) B10029491
theorem B10028717 : Blo 1760081 10028717 := bstep (se 3 (by rfl) ⟨1880384, by rfl⟩ : syracuseStep 10028717 = 3760769) B3760769
theorem B12216037 : Blo 1760081 12216037 := bstep (se 4 (by rfl) ⟨1145253, by rfl⟩ : syracuseStep 12216037 = 2290507) B2290507
theorem B3811087 : Blo 1760081 3811087 := bstep (se 1 (by rfl) ⟨2858315, by rfl⟩ : syracuseStep 3811087 = 5716631) B5716631
theorem B2230031 : Blo 1760081 2230031 := bstep (se 1 (by rfl) ⟨1672523, by rfl⟩ : syracuseStep 2230031 = 3345047) B3345047
theorem B5941025 : Blo 1760081 5941025 := bstep (se 2 (by rfl) ⟨2227884, by rfl⟩ : syracuseStep 5941025 = 4455769) B4455769
theorem B7235513 : Blo 1760081 7235513 := bstep (se 2 (by rfl) ⟨2713317, by rfl⟩ : syracuseStep 7235513 = 5426635) B5426635
theorem B3172385 : Blo 1760081 3172385 := bstep (se 2 (by rfl) ⟨1189644, by rfl⟩ : syracuseStep 3172385 = 2379289) B2379289
theorem B5015611 : Blo 1760081 5015611 := bstep (se 1 (by rfl) ⟨3761708, by rfl⟩ : syracuseStep 5015611 = 7523417) B7523417
theorem B31353101 : Blo 1760081 31353101 := bstep (se 3 (by rfl) ⟨5878706, by rfl⟩ : syracuseStep 31353101 = 11757413) B11757413
theorem B2640143 : Blo 1760081 2640143 := bstep (se 1 (by rfl) ⟨1980107, by rfl⟩ : syracuseStep 2640143 = 3960215) B3960215
theorem B2640185 : Blo 1760081 2640185 := bstep (se 2 (by rfl) ⟨990069, by rfl⟩ : syracuseStep 2640185 = 1980139) B1980139
theorem B24095069 : Blo 1760081 24095069 := bstep (se 3 (by rfl) ⟨4517825, by rfl⟩ : syracuseStep 24095069 = 9035651) B9035651
theorem B5941619 : Blo 1760081 5941619 := bstep (se 1 (by rfl) ⟨4456214, by rfl⟩ : syracuseStep 5941619 = 8912429) B8912429
theorem B2640263 : Blo 1760081 2640263 := bstep (se 1 (by rfl) ⟨1980197, by rfl⟩ : syracuseStep 2640263 = 3960395) B3960395
theorem B8915345 : Blo 1760081 8915345 := bstep (se 2 (by rfl) ⟨3343254, by rfl⟩ : syracuseStep 8915345 = 6686509) B6686509
theorem B2640299 : Blo 1760081 2640299 := bstep (se 1 (by rfl) ⟨1980224, by rfl⟩ : syracuseStep 2640299 = 3960449) B3960449
theorem B2640329 : Blo 1760081 2640329 := bstep (se 2 (by rfl) ⟨990123, by rfl⟩ : syracuseStep 2640329 = 1980247) B1980247
theorem B4459009 : Blo 1760081 4459009 := bstep (se 2 (by rfl) ⟨1672128, by rfl⟩ : syracuseStep 4459009 = 3344257) B3344257
theorem B2116111 : Blo 1760081 2116111 := bstep (se 1 (by rfl) ⟨1587083, by rfl⟩ : syracuseStep 2116111 = 3174167) B3174167
theorem B3435041 : Blo 1760081 3435041 := bstep (se 2 (by rfl) ⟨1288140, by rfl⟩ : syracuseStep 3435041 = 2576281) B2576281
theorem B2640443 : Blo 1760081 2640443 := bstep (se 1 (by rfl) ⟨1980332, by rfl⟩ : syracuseStep 2640443 = 3960665) B3960665
theorem B6687299 : Blo 1760081 6687299 := bstep (se 1 (by rfl) ⟨5015474, by rfl⟩ : syracuseStep 6687299 = 10030949) B10030949
theorem B6777431 : Blo 1760081 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B2640503 : Blo 1760081 2640503 := bstep (se 1 (by rfl) ⟨1980377, by rfl⟩ : syracuseStep 2640503 = 3960755) B3960755
theorem B2640527 : Blo 1760081 2640527 := bstep (se 1 (by rfl) ⟨1980395, by rfl⟩ : syracuseStep 2640527 = 3960791) B3960791
theorem B2640569 : Blo 1760081 2640569 := bstep (se 2 (by rfl) ⟨990213, by rfl⟩ : syracuseStep 2640569 = 1980427) B1980427
theorem B2640647 : Blo 1760081 2640647 := bstep (se 1 (by rfl) ⟨1980485, by rfl⟩ : syracuseStep 2640647 = 3960971) B3960971
theorem B2640683 : Blo 1760081 2640683 := bstep (se 1 (by rfl) ⟨1980512, by rfl⟩ : syracuseStep 2640683 = 3961025) B3961025
theorem B2820923 : Blo 1760081 2820923 := bstep (se 1 (by rfl) ⟨2115692, by rfl⟩ : syracuseStep 2820923 = 4231385) B4231385
theorem B2640713 : Blo 1760081 2640713 := bstep (se 2 (by rfl) ⟨990267, by rfl⟩ : syracuseStep 2640713 = 1980535) B1980535
theorem B22571891 : Blo 1760081 22571891 := bstep (se 1 (by rfl) ⟨16928918, by rfl⟩ : syracuseStep 22571891 = 33857837) B33857837
theorem B5016455 : Blo 1760081 5016455 := bstep (se 1 (by rfl) ⟨3762341, by rfl⟩ : syracuseStep 5016455 = 7524683) B7524683
theorem B40668085 : Blo 1760081 40668085 := bstep (se 5 (by rfl) ⟨1906316, by rfl⟩ : syracuseStep 40668085 = 3812633) B3812633
theorem B2640827 : Blo 1760081 2640827 := bstep (se 1 (by rfl) ⟨1980620, by rfl⟩ : syracuseStep 2640827 = 3961241) B3961241
theorem B2640887 : Blo 1760081 2640887 := bstep (se 1 (by rfl) ⟨1980665, by rfl⟩ : syracuseStep 2640887 = 3961331) B3961331
theorem B6687755 : Blo 1760081 6687755 := bstep (se 1 (by rfl) ⟨5015816, by rfl⟩ : syracuseStep 6687755 = 10031633) B10031633
theorem B2640911 : Blo 1760081 2640911 := bstep (se 1 (by rfl) ⟨1980683, by rfl⟩ : syracuseStep 2640911 = 3961367) B3961367
theorem B2640953 : Blo 1760081 2640953 := bstep (se 2 (by rfl) ⟨990357, by rfl⟩ : syracuseStep 2640953 = 1980715) B1980715
theorem B20048957 : Blo 1760081 20048957 := bstep (se 3 (by rfl) ⟨3759179, by rfl⟩ : syracuseStep 20048957 = 7518359) B7518359
theorem B4459607 : Blo 1760081 4459607 := bstep (se 1 (by rfl) ⟨3344705, by rfl⟩ : syracuseStep 4459607 = 6689411) B6689411
theorem B7335031 : Blo 1760081 7335031 := bstep (se 1 (by rfl) ⟨5501273, by rfl⟩ : syracuseStep 7335031 = 11002547) B11002547
theorem B2641031 : Blo 1760081 2641031 := bstep (se 1 (by rfl) ⟨1980773, by rfl⟩ : syracuseStep 2641031 = 3961547) B3961547
theorem B2641067 : Blo 1760081 2641067 := bstep (se 1 (by rfl) ⟨1980800, by rfl⟩ : syracuseStep 2641067 = 3961601) B3961601
theorem B2641097 : Blo 1760081 2641097 := bstep (se 2 (by rfl) ⟨990411, by rfl⟩ : syracuseStep 2641097 = 1980823) B1980823
theorem B4459819 : Blo 1760081 4459819 := bstep (se 1 (by rfl) ⟨3344864, by rfl⟩ : syracuseStep 4459819 = 6689729) B6689729
theorem B2641211 : Blo 1760081 2641211 := bstep (se 1 (by rfl) ⟨1980908, by rfl⟩ : syracuseStep 2641211 = 3961817) B3961817
theorem B2821435 : Blo 1760081 2821435 := bstep (se 1 (by rfl) ⟨2116076, by rfl⟩ : syracuseStep 2821435 = 4232153) B4232153
theorem B5639539 : Blo 1760081 5639539 := bstep (se 1 (by rfl) ⟨4229654, by rfl⟩ : syracuseStep 5639539 = 8459309) B8459309
theorem B2641271 : Blo 1760081 2641271 := bstep (se 1 (by rfl) ⟨1980953, by rfl⟩ : syracuseStep 2641271 = 3961907) B3961907
theorem B2641295 : Blo 1760081 2641295 := bstep (se 1 (by rfl) ⟨1980971, by rfl⟩ : syracuseStep 2641295 = 3961943) B3961943
theorem B3812755 : Blo 1760081 3812755 := bstep (se 1 (by rfl) ⟨2859566, by rfl⟩ : syracuseStep 3812755 = 5719133) B5719133
theorem B2641337 : Blo 1760081 2641337 := bstep (se 2 (by rfl) ⟨990501, by rfl⟩ : syracuseStep 2641337 = 1981003) B1981003
theorem B4459961 : Blo 1760081 4459961 := bstep (se 2 (by rfl) ⟨1672485, by rfl⟩ : syracuseStep 4459961 = 3344971) B3344971
theorem B2641415 : Blo 1760081 2641415 := bstep (se 1 (by rfl) ⟨1981061, by rfl⟩ : syracuseStep 2641415 = 3962123) B3962123
theorem B2641451 : Blo 1760081 2641451 := bstep (se 1 (by rfl) ⟨1981088, by rfl⟩ : syracuseStep 2641451 = 3962177) B3962177
theorem B2641481 : Blo 1760081 2641481 := bstep (se 2 (by rfl) ⟨990555, by rfl⟩ : syracuseStep 2641481 = 1981111) B1981111
theorem B3960467 : Blo 1760081 3960467 := bstep (se 1 (by rfl) ⟨2970350, by rfl⟩ : syracuseStep 3960467 = 5940701) B5940701
theorem B5017241 : Blo 1760081 5017241 := bstep (se 2 (by rfl) ⟨1881465, by rfl⟩ : syracuseStep 5017241 = 3762931) B3762931
theorem B2641595 : Blo 1760081 2641595 := bstep (se 1 (by rfl) ⟨1981196, by rfl⟩ : syracuseStep 2641595 = 3962393) B3962393
theorem B3960521 : Blo 1760081 3960521 := bstep (se 2 (by rfl) ⟨1485195, by rfl⟩ : syracuseStep 3960521 = 2970391) B2970391
theorem B8138477 : Blo 1760081 8138477 := bstep (se 3 (by rfl) ⟨1525964, by rfl⟩ : syracuseStep 8138477 = 3051929) B3051929
theorem B2641655 : Blo 1760081 2641655 := bstep (se 1 (by rfl) ⟨1981241, by rfl⟩ : syracuseStep 2641655 = 3962483) B3962483
theorem B2035471 : Blo 1760081 2035471 := bstep (se 1 (by rfl) ⟨1526603, by rfl⟩ : syracuseStep 2035471 = 3053207) B3053207
theorem B2641679 : Blo 1760081 2641679 := bstep (se 1 (by rfl) ⟨1981259, by rfl⟩ : syracuseStep 2641679 = 3962519) B3962519
theorem B2641721 : Blo 1760081 2641721 := bstep (se 2 (by rfl) ⟨990645, by rfl⟩ : syracuseStep 2641721 = 1981291) B1981291
theorem B5353303 : Blo 1760081 5353303 := bstep (se 1 (by rfl) ⟨4014977, by rfl⟩ : syracuseStep 5353303 = 8029955) B8029955
theorem B2641799 : Blo 1760081 2641799 := bstep (se 1 (by rfl) ⟨1981349, by rfl⟩ : syracuseStep 2641799 = 3962699) B3962699
theorem B2641835 : Blo 1760081 2641835 := bstep (se 1 (by rfl) ⟨1981376, by rfl⟩ : syracuseStep 2641835 = 3962753) B3962753
theorem B2641865 : Blo 1760081 2641865 := bstep (se 2 (by rfl) ⟨990699, by rfl⟩ : syracuseStep 2641865 = 1981399) B1981399
theorem B2641979 : Blo 1760081 2641979 := bstep (se 1 (by rfl) ⟨1981484, by rfl⟩ : syracuseStep 2641979 = 3962969) B3962969
theorem B2642039 : Blo 1760081 2642039 := bstep (se 1 (by rfl) ⟨1981529, by rfl⟩ : syracuseStep 2642039 = 3963059) B3963059
theorem B2642063 : Blo 1760081 2642063 := bstep (se 1 (by rfl) ⟨1981547, by rfl⟩ : syracuseStep 2642063 = 3963095) B3963095
theorem B2642105 : Blo 1760081 2642105 := bstep (se 2 (by rfl) ⟨990789, by rfl⟩ : syracuseStep 2642105 = 1981579) B1981579
theorem B2642183 : Blo 1760081 2642183 := bstep (se 1 (by rfl) ⟨1981637, by rfl⟩ : syracuseStep 2642183 = 3963275) B3963275
theorem B4518155 : Blo 1760081 4518155 := bstep (se 1 (by rfl) ⟨3388616, by rfl⟩ : syracuseStep 4518155 = 6777233) B6777233
theorem B2642219 : Blo 1760081 2642219 := bstep (se 1 (by rfl) ⟨1981664, by rfl⟩ : syracuseStep 2642219 = 3963329) B3963329
theorem B2642249 : Blo 1760081 2642249 := bstep (se 2 (by rfl) ⟨990843, by rfl⟩ : syracuseStep 2642249 = 1981687) B1981687
theorem B3961223 : Blo 1760081 3961223 := bstep (se 1 (by rfl) ⟨2970917, by rfl⟩ : syracuseStep 3961223 = 5941835) B5941835
theorem B9523601 : Blo 1760081 9523601 := bstep (se 2 (by rfl) ⟨3571350, by rfl⟩ : syracuseStep 9523601 = 7142701) B7142701
theorem B2642363 : Blo 1760081 2642363 := bstep (se 1 (by rfl) ⟨1981772, by rfl⟩ : syracuseStep 2642363 = 3963545) B3963545
theorem B8917451 : Blo 1760081 8917451 := bstep (se 1 (by rfl) ⟨6688088, by rfl⟩ : syracuseStep 8917451 = 13376177) B13376177
theorem B14283229 : Blo 1760081 14283229 := bstep (se 3 (by rfl) ⟨2678105, by rfl⟩ : syracuseStep 14283229 = 5356211) B5356211
theorem B2642423 : Blo 1760081 2642423 := bstep (se 1 (by rfl) ⟨1981817, by rfl⟩ : syracuseStep 2642423 = 3963635) B3963635
theorem B2642447 : Blo 1760081 2642447 := bstep (se 1 (by rfl) ⟨1981835, by rfl⟩ : syracuseStep 2642447 = 3963671) B3963671
theorem B2970155 : Blo 1760081 2970155 := bstep (se 1 (by rfl) ⟨2227616, by rfl⟩ : syracuseStep 2970155 = 4455233) B4455233
theorem B2642489 : Blo 1760081 2642489 := bstep (se 2 (by rfl) ⟨990933, by rfl⟩ : syracuseStep 2642489 = 1981867) B1981867
theorem B3961403 : Blo 1760081 3961403 := bstep (se 1 (by rfl) ⟨2971052, by rfl⟩ : syracuseStep 3961403 = 5942105) B5942105
theorem B2642567 : Blo 1760081 2642567 := bstep (se 1 (by rfl) ⟨1981925, by rfl⟩ : syracuseStep 2642567 = 3963851) B3963851
theorem B2642603 : Blo 1760081 2642603 := bstep (se 1 (by rfl) ⟨1981952, by rfl⟩ : syracuseStep 2642603 = 3963905) B3963905
theorem B3961529 : Blo 1760081 3961529 := bstep (se 2 (by rfl) ⟨1485573, by rfl⟩ : syracuseStep 3961529 = 2971147) B2971147
theorem B2642633 : Blo 1760081 2642633 := bstep (se 2 (by rfl) ⟨990987, by rfl⟩ : syracuseStep 2642633 = 1981975) B1981975
theorem B8917775 : Blo 1760081 8917775 := bstep (se 1 (by rfl) ⟨6688331, by rfl⟩ : syracuseStep 8917775 = 13376663) B13376663
theorem B2642747 : Blo 1760081 2642747 := bstep (se 1 (by rfl) ⟨1982060, by rfl⟩ : syracuseStep 2642747 = 3964121) B3964121
theorem B2642807 : Blo 1760081 2642807 := bstep (se 1 (by rfl) ⟨1982105, by rfl⟩ : syracuseStep 2642807 = 3964211) B3964211
theorem B2642831 : Blo 1760081 2642831 := bstep (se 1 (by rfl) ⟨1982123, by rfl⟩ : syracuseStep 2642831 = 3964247) B3964247
theorem B5944211 : Blo 1760081 5944211 := bstep (se 1 (by rfl) ⟨4458158, by rfl⟩ : syracuseStep 5944211 = 8916317) B8916317
theorem B2970553 : Blo 1760081 2970553 := bstep (se 2 (by rfl) ⟨1113957, by rfl⟩ : syracuseStep 2970553 = 2227915) B2227915
theorem B2642873 : Blo 1760081 2642873 := bstep (se 2 (by rfl) ⟨991077, by rfl⟩ : syracuseStep 2642873 = 1982155) B1982155
theorem B2642951 : Blo 1760081 2642951 := bstep (se 1 (by rfl) ⟨1982213, by rfl⟩ : syracuseStep 2642951 = 3964427) B3964427
theorem B3961871 : Blo 1760081 3961871 := bstep (se 1 (by rfl) ⟨2971403, by rfl⟩ : syracuseStep 3961871 = 5942807) B5942807
theorem B3961889 : Blo 1760081 3961889 := bstep (se 2 (by rfl) ⟨1485708, by rfl⟩ : syracuseStep 3961889 = 2971417) B2971417
theorem B2642987 : Blo 1760081 2642987 := bstep (se 1 (by rfl) ⟨1982240, by rfl⟩ : syracuseStep 2642987 = 3964481) B3964481
theorem B8467517 : Blo 1760081 8467517 := bstep (se 3 (by rfl) ⟨1587659, by rfl⟩ : syracuseStep 8467517 = 3175319) B3175319
theorem B2643017 : Blo 1760081 2643017 := bstep (se 2 (by rfl) ⟨991131, by rfl⟩ : syracuseStep 2643017 = 1982263) B1982263
theorem B19051607 : Blo 1760081 19051607 := bstep (se 1 (by rfl) ⟨14288705, by rfl⟩ : syracuseStep 19051607 = 28577411) B28577411
theorem B6689911 : Blo 1760081 6689911 := bstep (se 1 (by rfl) ⟨5017433, by rfl⟩ : syracuseStep 6689911 = 10034867) B10034867
theorem B12047561 : Blo 1760081 12047561 := bstep (se 2 (by rfl) ⟨4517835, by rfl⟩ : syracuseStep 12047561 = 9035671) B9035671
theorem B8459579 : Blo 1760081 8459579 := bstep (se 1 (by rfl) ⟨6344684, by rfl⟩ : syracuseStep 8459579 = 12689369) B12689369
theorem B3962231 : Blo 1760081 3962231 := bstep (se 1 (by rfl) ⟨2971673, by rfl⟩ : syracuseStep 3962231 = 5943347) B5943347
theorem B4289993 : Blo 1760081 4289993 := bstep (se 2 (by rfl) ⟨1608747, by rfl⟩ : syracuseStep 4289993 = 3217495) B3217495
theorem B3962411 : Blo 1760081 3962411 := bstep (se 1 (by rfl) ⟨2971808, by rfl⟩ : syracuseStep 3962411 = 5943617) B5943617
theorem B2971255 : Blo 1760081 2971255 := bstep (se 1 (by rfl) ⟨2228441, by rfl⟩ : syracuseStep 2971255 = 4456883) B4456883
theorem B5355143 : Blo 1760081 5355143 := bstep (se 1 (by rfl) ⟨4016357, by rfl⟩ : syracuseStep 5355143 = 8032715) B8032715
theorem B2381447 : Blo 1760081 2381447 := bstep (se 1 (by rfl) ⟨1786085, by rfl⟩ : syracuseStep 2381447 = 3572171) B3572171
theorem B13375205 : Blo 1760081 13375205 := bstep (se 4 (by rfl) ⟨1253925, by rfl⟩ : syracuseStep 13375205 = 2507851) B2507851
theorem B1980175 : Blo 1760081 1980175 := bstep (se 1 (by rfl) ⟨1485131, by rfl⟩ : syracuseStep 1980175 = 2970263) B2970263
theorem B16062245 : Blo 1760081 16062245 := bstep (se 4 (by rfl) ⟨1505835, by rfl⟩ : syracuseStep 16062245 = 3011671) B3011671
theorem B43439921 : Blo 1760081 43439921 := bstep (se 2 (by rfl) ⟨16289970, by rfl⟩ : syracuseStep 43439921 = 32579941) B32579941
theorem B9647923 : Blo 1760081 9647923 := bstep (se 1 (by rfl) ⟨7235942, by rfl⟩ : syracuseStep 9647923 = 14471885) B14471885
theorem B2971451 : Blo 1760081 2971451 := bstep (se 1 (by rfl) ⟨2228588, by rfl⟩ : syracuseStep 2971451 = 4457177) B4457177
theorem B4233019 : Blo 1760081 4233019 := bstep (se 1 (by rfl) ⟨3174764, by rfl⟩ : syracuseStep 4233019 = 6349529) B6349529
theorem B3962771 : Blo 1760081 3962771 := bstep (se 1 (by rfl) ⟨2972078, by rfl⟩ : syracuseStep 3962771 = 5944157) B5944157
theorem B3962825 : Blo 1760081 3962825 := bstep (se 2 (by rfl) ⟨1486059, by rfl⟩ : syracuseStep 3962825 = 2972119) B2972119
theorem B11286539 : Blo 1760081 11286539 := bstep (se 1 (by rfl) ⟨8464904, by rfl⟩ : syracuseStep 11286539 = 16929809) B16929809
theorem B13367429 : Blo 1760081 13367429 := bstep (se 4 (by rfl) ⟨1253196, by rfl⟩ : syracuseStep 13367429 = 2506393) B2506393
theorem B2676871 : Blo 1760081 2676871 := bstep (se 1 (by rfl) ⟨2007653, by rfl⟩ : syracuseStep 2676871 = 4015307) B4015307
theorem B5085337 : Blo 1760081 5085337 := bstep (se 2 (by rfl) ⟨1907001, by rfl⟩ : syracuseStep 5085337 = 3814003) B3814003
theorem B8919233 : Blo 1760081 8919233 := bstep (se 2 (by rfl) ⟨3344712, by rfl⟩ : syracuseStep 8919233 = 6689425) B6689425
theorem B4888777 : Blo 1760081 4888777 := bstep (se 2 (by rfl) ⟨1833291, by rfl⟩ : syracuseStep 4888777 = 3666583) B3666583
theorem B2971849 : Blo 1760081 2971849 := bstep (se 2 (by rfl) ⟨1114443, by rfl⟩ : syracuseStep 2971849 = 2228887) B2228887
theorem B10033409 : Blo 1760081 10033409 := bstep (se 2 (by rfl) ⟨3762528, by rfl⟩ : syracuseStep 10033409 = 7525057) B7525057
theorem B1980679 : Blo 1760081 1980679 := bstep (se 1 (by rfl) ⟨1485509, by rfl⟩ : syracuseStep 1980679 = 2971019) B2971019
theorem B6682895 : Blo 1760081 6682895 := bstep (se 1 (by rfl) ⟨5012171, by rfl⟩ : syracuseStep 6682895 = 10024343) B10024343
theorem B5945615 : Blo 1760081 5945615 := bstep (se 1 (by rfl) ⟨4459211, by rfl⟩ : syracuseStep 5945615 = 8918423) B8918423
theorem B5028157 : Blo 1760081 5028157 := bstep (se 3 (by rfl) ⟨942779, by rfl⟩ : syracuseStep 5028157 = 1885559) B1885559
theorem B10025369 : Blo 1760081 10025369 := bstep (se 2 (by rfl) ⟨3759513, by rfl⟩ : syracuseStep 10025369 = 7519027) B7519027
theorem B15038905 : Blo 1760081 15038905 := bstep (se 2 (by rfl) ⟨5639589, by rfl⟩ : syracuseStep 15038905 = 11279179) B11279179
theorem B1980859 : Blo 1760081 1980859 := bstep (se 1 (by rfl) ⟨1485644, by rfl⟩ : syracuseStep 1980859 = 2971289) B2971289
theorem B20060621 : Blo 1760081 20060621 := bstep (se 3 (by rfl) ⟨3761366, by rfl⟩ : syracuseStep 20060621 = 7522733) B7522733
theorem B22575581 : Blo 1760081 22575581 := bstep (se 3 (by rfl) ⟨4232921, by rfl⟩ : syracuseStep 22575581 = 8465843) B8465843
theorem B5945885 : Blo 1760081 5945885 := bstep (se 3 (by rfl) ⟨1114853, by rfl⟩ : syracuseStep 5945885 = 2229707) B2229707
theorem B34306679 : Blo 1760081 34306679 := bstep (se 1 (by rfl) ⟨25730009, by rfl⟩ : syracuseStep 34306679 = 51460019) B51460019
theorem B3963527 : Blo 1760081 3963527 := bstep (se 1 (by rfl) ⟨2972645, by rfl⟩ : syracuseStep 3963527 = 5945291) B5945291
theorem B5085881 : Blo 1760081 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B10033865 : Blo 1760081 10033865 := bstep (se 2 (by rfl) ⟨3762699, by rfl⟩ : syracuseStep 10033865 = 7525399) B7525399
theorem B3963707 : Blo 1760081 3963707 := bstep (se 1 (by rfl) ⟨2972780, by rfl⟩ : syracuseStep 3963707 = 5945561) B5945561
theorem B4455283 : Blo 1760081 4455283 := bstep (se 1 (by rfl) ⟨3341462, by rfl⟩ : syracuseStep 4455283 = 6682925) B6682925
theorem B1760135 : Blo 1760081 1760135 := bstep (se 1 (by rfl) ⟨1320101, by rfl⟩ : syracuseStep 1760135 = 2640203) B2640203
theorem B2972551 : Blo 1760081 2972551 := bstep (se 1 (by rfl) ⟨2229413, by rfl⟩ : syracuseStep 2972551 = 4458827) B4458827
theorem B1760143 : Blo 1760081 1760143 := bstep (se 1 (by rfl) ⟨1320107, by rfl⟩ : syracuseStep 1760143 = 2640215) B2640215
theorem B1981327 : Blo 1760081 1981327 := bstep (se 1 (by rfl) ⟨1485995, by rfl⟩ : syracuseStep 1981327 = 2971991) B2971991
theorem B3963833 : Blo 1760081 3963833 := bstep (se 2 (by rfl) ⟨1486437, by rfl⟩ : syracuseStep 3963833 = 2972875) B2972875
theorem B1760187 : Blo 1760081 1760187 := bstep (se 1 (by rfl) ⟨1320140, by rfl⟩ : syracuseStep 1760187 = 2640281) B2640281
theorem B4455425 : Blo 1760081 4455425 := bstep (se 2 (by rfl) ⟨1670784, by rfl⟩ : syracuseStep 4455425 = 3341569) B3341569
theorem B1760263 : Blo 1760081 1760263 := bstep (se 1 (by rfl) ⟨1320197, by rfl⟩ : syracuseStep 1760263 = 2640395) B2640395
theorem B1760271 : Blo 1760081 1760271 := bstep (se 1 (by rfl) ⟨1320203, by rfl⟩ : syracuseStep 1760271 = 2640407) B2640407
theorem B5012513 : Blo 1760081 5012513 := bstep (se 2 (by rfl) ⟨1879692, by rfl⟩ : syracuseStep 5012513 = 3759385) B3759385
theorem B1760315 : Blo 1760081 1760315 := bstep (se 1 (by rfl) ⟨1320236, by rfl⟩ : syracuseStep 1760315 = 2640473) B2640473
theorem B7519351 : Blo 1760081 7519351 := bstep (se 1 (by rfl) ⟨5639513, by rfl⟩ : syracuseStep 7519351 = 11279027) B11279027
theorem B1760391 : Blo 1760081 1760391 := bstep (se 1 (by rfl) ⟨1320293, by rfl⟩ : syracuseStep 1760391 = 2640587) B2640587
theorem B1760399 : Blo 1760081 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B1760443 : Blo 1760081 1760443 := bstep (se 1 (by rfl) ⟨1320332, by rfl⟩ : syracuseStep 1760443 = 2640665) B2640665
theorem B2677961 : Blo 1760081 2677961 := bstep (se 2 (by rfl) ⟨1004235, by rfl⟩ : syracuseStep 2677961 = 2008471) B2008471
theorem B1760519 : Blo 1760081 1760519 := bstep (se 1 (by rfl) ⟨1320389, by rfl⟩ : syracuseStep 1760519 = 2640779) B2640779
theorem B1760527 : Blo 1760081 1760527 := bstep (se 1 (by rfl) ⟨1320395, by rfl⟩ : syracuseStep 1760527 = 2640791) B2640791
theorem B3964175 : Blo 1760081 3964175 := bstep (se 1 (by rfl) ⟨2973131, by rfl⟩ : syracuseStep 3964175 = 5946263) B5946263
theorem B3964193 : Blo 1760081 3964193 := bstep (se 2 (by rfl) ⟨1486572, by rfl⟩ : syracuseStep 3964193 = 2973145) B2973145
theorem B3759419 : Blo 1760081 3759419 := bstep (se 1 (by rfl) ⟨2819564, by rfl⟩ : syracuseStep 3759419 = 5639129) B5639129
theorem B1760571 : Blo 1760081 1760571 := bstep (se 1 (by rfl) ⟨1320428, by rfl⟩ : syracuseStep 1760571 = 2640857) B2640857
theorem B1760647 : Blo 1760081 1760647 := bstep (se 1 (by rfl) ⟨1320485, by rfl⟩ : syracuseStep 1760647 = 2640971) B2640971
theorem B1981831 : Blo 1760081 1981831 := bstep (se 1 (by rfl) ⟨1486373, by rfl⟩ : syracuseStep 1981831 = 2972747) B2972747
theorem B1760655 : Blo 1760081 1760655 := bstep (se 1 (by rfl) ⟨1320491, by rfl⟩ : syracuseStep 1760655 = 2640983) B2640983
theorem B21716369 : Blo 1760081 21716369 := bstep (se 2 (by rfl) ⟨8143638, by rfl⟩ : syracuseStep 21716369 = 16287277) B16287277
theorem B1760699 : Blo 1760081 1760699 := bstep (se 1 (by rfl) ⟨1320524, by rfl⟩ : syracuseStep 1760699 = 2641049) B2641049
theorem B4455881 : Blo 1760081 4455881 := bstep (se 2 (by rfl) ⟨1670955, by rfl⟩ : syracuseStep 4455881 = 3341911) B3341911
theorem B8920529 : Blo 1760081 8920529 := bstep (se 2 (by rfl) ⟨3345198, by rfl⟩ : syracuseStep 8920529 = 6690397) B6690397
theorem B1760775 : Blo 1760081 1760775 := bstep (se 1 (by rfl) ⟨1320581, by rfl⟩ : syracuseStep 1760775 = 2641163) B2641163
theorem B1760783 : Blo 1760081 1760783 := bstep (se 1 (by rfl) ⟨1320587, by rfl⟩ : syracuseStep 1760783 = 2641175) B2641175
theorem B1785359 : Blo 1760081 1785359 := bstep (se 1 (by rfl) ⟨1339019, by rfl⟩ : syracuseStep 1785359 = 2678039) B2678039
theorem B2973199 : Blo 1760081 2973199 := bstep (se 1 (by rfl) ⟨2229899, by rfl⟩ : syracuseStep 2973199 = 4459799) B4459799
theorem B2506297 : Blo 1760081 2506297 := bstep (se 2 (by rfl) ⟨939861, by rfl⟩ : syracuseStep 2506297 = 1879723) B1879723
theorem B1760827 : Blo 1760081 1760827 := bstep (se 1 (by rfl) ⟨1320620, by rfl⟩ : syracuseStep 1760827 = 2641241) B2641241
theorem B1982011 : Blo 1760081 1982011 := bstep (se 1 (by rfl) ⟨1486508, by rfl⟩ : syracuseStep 1982011 = 2973017) B2973017
theorem B3964535 : Blo 1760081 3964535 := bstep (se 1 (by rfl) ⟨2973401, by rfl⟩ : syracuseStep 3964535 = 5946803) B5946803
theorem B4759175 : Blo 1760081 4759175 := bstep (se 1 (by rfl) ⟨3569381, by rfl⟩ : syracuseStep 4759175 = 7138763) B7138763
theorem B1760903 : Blo 1760081 1760903 := bstep (se 1 (by rfl) ⟨1320677, by rfl⟩ : syracuseStep 1760903 = 2641355) B2641355
theorem B1760911 : Blo 1760081 1760911 := bstep (se 1 (by rfl) ⟨1320683, by rfl⟩ : syracuseStep 1760911 = 2641367) B2641367
theorem B1760955 : Blo 1760081 1760955 := bstep (se 1 (by rfl) ⟨1320716, by rfl⟩ : syracuseStep 1760955 = 2641433) B2641433
theorem B1761031 : Blo 1760081 1761031 := bstep (se 1 (by rfl) ⟨1320773, by rfl⟩ : syracuseStep 1761031 = 2641547) B2641547
theorem B1761039 : Blo 1760081 1761039 := bstep (se 1 (by rfl) ⟨1320779, by rfl⟩ : syracuseStep 1761039 = 2641559) B2641559
theorem B10862351 : Blo 1760081 10862351 := bstep (se 1 (by rfl) ⟨8146763, by rfl⟩ : syracuseStep 10862351 = 16293527) B16293527
theorem B6348577 : Blo 1760081 6348577 := bstep (se 2 (by rfl) ⟨2380716, by rfl⟩ : syracuseStep 6348577 = 4761433) B4761433
theorem B14286629 : Blo 1760081 14286629 := bstep (se 4 (by rfl) ⟨1339371, by rfl⟩ : syracuseStep 14286629 = 2678743) B2678743
theorem B4456235 : Blo 1760081 4456235 := bstep (se 1 (by rfl) ⟨3342176, by rfl⟩ : syracuseStep 4456235 = 6684353) B6684353
theorem B152346419 : Blo 1760081 152346419 := bstep (se 1 (by rfl) ⟨114259814, by rfl⟩ : syracuseStep 152346419 = 228519629) B228519629
theorem B1761083 : Blo 1760081 1761083 := bstep (se 1 (by rfl) ⟨1320812, by rfl⟩ : syracuseStep 1761083 = 2641625) B2641625
theorem B4759357 : Blo 1760081 4759357 := bstep (se 3 (by rfl) ⟨892379, by rfl⟩ : syracuseStep 4759357 = 1784759) B1784759
theorem B2228087 : Blo 1760081 2228087 := bstep (se 1 (by rfl) ⟨1671065, by rfl⟩ : syracuseStep 2228087 = 3342131) B3342131
theorem B3342215 : Blo 1760081 3342215 := bstep (se 1 (by rfl) ⟨2506661, by rfl⟩ : syracuseStep 3342215 = 5013323) B5013323
theorem B6684551 : Blo 1760081 6684551 := bstep (se 1 (by rfl) ⟨5013413, by rfl⟩ : syracuseStep 6684551 = 10026827) B10026827
theorem B1761159 : Blo 1760081 1761159 := bstep (se 1 (by rfl) ⟨1320869, by rfl⟩ : syracuseStep 1761159 = 2641739) B2641739
theorem B1761167 : Blo 1760081 1761167 := bstep (se 1 (by rfl) ⟨1320875, by rfl⟩ : syracuseStep 1761167 = 2641751) B2641751
theorem B15048611 : Blo 1760081 15048611 := bstep (se 1 (by rfl) ⟨11286458, by rfl⟩ : syracuseStep 15048611 = 22572917) B22572917
theorem B1761211 : Blo 1760081 1761211 := bstep (se 1 (by rfl) ⟨1320908, by rfl⟩ : syracuseStep 1761211 = 2641817) B2641817
theorem B13369373 : Blo 1760081 13369373 := bstep (se 3 (by rfl) ⟨2506757, by rfl⟩ : syracuseStep 13369373 = 5013515) B5013515
theorem B1761319 : Blo 1760081 1761319 := bstep (se 1 (by rfl) ⟨1320989, by rfl⟩ : syracuseStep 1761319 = 2641979) B2641979
theorem B1761359 : Blo 1760081 1761359 := bstep (se 1 (by rfl) ⟨1321019, by rfl⟩ : syracuseStep 1761359 = 2642039) B2642039
theorem B1761375 : Blo 1760081 1761375 := bstep (se 1 (by rfl) ⟨1321031, by rfl⟩ : syracuseStep 1761375 = 2642063) B2642063
theorem B1761403 : Blo 1760081 1761403 := bstep (se 1 (by rfl) ⟨1321052, by rfl⟩ : syracuseStep 1761403 = 2642105) B2642105
theorem B1761455 : Blo 1760081 1761455 := bstep (se 1 (by rfl) ⟨1321091, by rfl⟩ : syracuseStep 1761455 = 2642183) B2642183
theorem B1761479 : Blo 1760081 1761479 := bstep (se 1 (by rfl) ⟨1321109, by rfl⟩ : syracuseStep 1761479 = 2642219) B2642219
theorem B1761499 : Blo 1760081 1761499 := bstep (se 1 (by rfl) ⟨1321124, by rfl⟩ : syracuseStep 1761499 = 2642249) B2642249
theorem B6349067 : Blo 1760081 6349067 := bstep (se 1 (by rfl) ⟨4761800, by rfl⟩ : syracuseStep 6349067 = 9523601) B9523601
theorem B1761575 : Blo 1760081 1761575 := bstep (se 1 (by rfl) ⟨1321181, by rfl⟩ : syracuseStep 1761575 = 2642363) B2642363
theorem B1761615 : Blo 1760081 1761615 := bstep (se 1 (by rfl) ⟨1321211, by rfl⟩ : syracuseStep 1761615 = 2642423) B2642423
theorem B8913239 : Blo 1760081 8913239 := bstep (se 1 (by rfl) ⟨6684929, by rfl⟩ : syracuseStep 8913239 = 13369859) B13369859
theorem B1761631 : Blo 1760081 1761631 := bstep (se 1 (by rfl) ⟨1321223, by rfl⟩ : syracuseStep 1761631 = 2642447) B2642447
theorem B1761659 : Blo 1760081 1761659 := bstep (se 1 (by rfl) ⟨1321244, by rfl⟩ : syracuseStep 1761659 = 2642489) B2642489
theorem B3572129 : Blo 1760081 3572129 := bstep (se 2 (by rfl) ⟨1339548, by rfl⟩ : syracuseStep 3572129 = 2679097) B2679097
theorem B1761711 : Blo 1760081 1761711 := bstep (se 1 (by rfl) ⟨1321283, by rfl⟩ : syracuseStep 1761711 = 2642567) B2642567
theorem B1761735 : Blo 1760081 1761735 := bstep (se 1 (by rfl) ⟨1321301, by rfl⟩ : syracuseStep 1761735 = 2642603) B2642603
theorem B1761755 : Blo 1760081 1761755 := bstep (se 1 (by rfl) ⟨1321316, by rfl⟩ : syracuseStep 1761755 = 2642633) B2642633
theorem B1761831 : Blo 1760081 1761831 := bstep (se 1 (by rfl) ⟨1321373, by rfl⟩ : syracuseStep 1761831 = 2642747) B2642747
theorem B1761871 : Blo 1760081 1761871 := bstep (se 1 (by rfl) ⟨1321403, by rfl⟩ : syracuseStep 1761871 = 2642807) B2642807
theorem B1761887 : Blo 1760081 1761887 := bstep (se 1 (by rfl) ⟨1321415, by rfl⟩ : syracuseStep 1761887 = 2642831) B2642831
theorem B1761915 : Blo 1760081 1761915 := bstep (se 1 (by rfl) ⟨1321436, by rfl⟩ : syracuseStep 1761915 = 2642873) B2642873
theorem B1761967 : Blo 1760081 1761967 := bstep (se 1 (by rfl) ⟨1321475, by rfl⟩ : syracuseStep 1761967 = 2642951) B2642951
theorem B1761991 : Blo 1760081 1761991 := bstep (se 1 (by rfl) ⟨1321493, by rfl⟩ : syracuseStep 1761991 = 2642987) B2642987
theorem B1762011 : Blo 1760081 1762011 := bstep (se 1 (by rfl) ⟨1321508, by rfl⟩ : syracuseStep 1762011 = 2643017) B2643017
theorem B25387789 : Blo 1760081 25387789 := bstep (se 3 (by rfl) ⟨4760210, by rfl⟩ : syracuseStep 25387789 = 9520421) B9520421
theorem B19039151 : Blo 1760081 19039151 := bstep (se 1 (by rfl) ⟨14279363, by rfl⟩ : syracuseStep 19039151 = 28558727) B28558727
theorem B2229211 : Blo 1760081 2229211 := bstep (se 1 (by rfl) ⟨1671908, by rfl⟩ : syracuseStep 2229211 = 3343817) B3343817
theorem B2859995 : Blo 1760081 2859995 := bstep (se 1 (by rfl) ⟨2144996, by rfl⟩ : syracuseStep 2859995 = 4289993) B4289993
theorem B10028033 : Blo 1760081 10028033 := bstep (se 2 (by rfl) ⟨3760512, by rfl⟩ : syracuseStep 10028033 = 7521025) B7521025
theorem B3343369 : Blo 1760081 3343369 := bstep (se 2 (by rfl) ⟨1253763, by rfl⟩ : syracuseStep 3343369 = 2507527) B2507527
theorem B7521299 : Blo 1760081 7521299 := bstep (se 1 (by rfl) ⟨5640974, by rfl⟩ : syracuseStep 7521299 = 11281949) B11281949
theorem B4457551 : Blo 1760081 4457551 := bstep (se 1 (by rfl) ⟨3343163, by rfl⟩ : syracuseStep 4457551 = 6686327) B6686327
theorem B6685811 : Blo 1760081 6685811 := bstep (se 1 (by rfl) ⟨5014358, by rfl⟩ : syracuseStep 6685811 = 10028717) B10028717
theorem B5940377 : Blo 1760081 5940377 := bstep (se 2 (by rfl) ⟨2227641, by rfl⟩ : syracuseStep 5940377 = 4455283) B4455283
theorem B10708163 : Blo 1760081 10708163 := bstep (se 1 (by rfl) ⟨8031122, by rfl⟩ : syracuseStep 10708163 = 16062245) B16062245
theorem B28959947 : Blo 1760081 28959947 := bstep (se 1 (by rfl) ⟨21719960, by rfl⟩ : syracuseStep 28959947 = 43439921) B43439921
theorem B54224113 : Blo 1760081 54224113 := bstep (se 2 (by rfl) ⟨20334042, by rfl⟩ : syracuseStep 54224113 = 40668085) B40668085
theorem B4760957 : Blo 1760081 4760957 := bstep (se 3 (by rfl) ⟨892679, by rfl⟩ : syracuseStep 4760957 = 1785359) B1785359
theorem B9160109 : Blo 1760081 9160109 := bstep (se 3 (by rfl) ⟨1717520, by rfl⟩ : syracuseStep 9160109 = 3435041) B3435041
theorem B15050387 : Blo 1760081 15050387 := bstep (se 1 (by rfl) ⟨11287790, by rfl⟩ : syracuseStep 15050387 = 22575581) B22575581
theorem B6350525 : Blo 1760081 6350525 := bstep (se 3 (by rfl) ⟨1190723, by rfl⟩ : syracuseStep 6350525 = 2381447) B2381447
theorem B4458199 : Blo 1760081 4458199 := bstep (se 1 (by rfl) ⟨3343649, by rfl⟩ : syracuseStep 4458199 = 6687299) B6687299
theorem B3344303 : Blo 1760081 3344303 := bstep (se 1 (by rfl) ⟨2508227, by rfl⟩ : syracuseStep 3344303 = 5016455) B5016455
theorem B4458503 : Blo 1760081 4458503 := bstep (se 1 (by rfl) ⟨3343877, by rfl⟩ : syracuseStep 4458503 = 6687755) B6687755
theorem B14477579 : Blo 1760081 14477579 := bstep (se 1 (by rfl) ⟨10858184, by rfl⟩ : syracuseStep 14477579 = 21716369) B21716369
theorem B16288049 : Blo 1760081 16288049 := bstep (se 2 (by rfl) ⟨6108018, by rfl⟩ : syracuseStep 16288049 = 12216037) B12216037
theorem B5941565 : Blo 1760081 5941565 := bstep (se 3 (by rfl) ⟨1114043, by rfl⟩ : syracuseStep 5941565 = 2228087) B2228087
theorem B2640233 : Blo 1760081 2640233 := bstep (se 2 (by rfl) ⟨990087, by rfl⟩ : syracuseStep 2640233 = 1980175) B1980175
theorem B5081449 : Blo 1760081 5081449 := bstep (se 2 (by rfl) ⟨1905543, by rfl⟩ : syracuseStep 5081449 = 3811087) B3811087
theorem B2713961 : Blo 1760081 2713961 := bstep (se 2 (by rfl) ⟨1017735, by rfl⟩ : syracuseStep 2713961 = 2035471) B2035471
theorem B8464769 : Blo 1760081 8464769 := bstep (se 2 (by rfl) ⟨3174288, by rfl⟩ : syracuseStep 8464769 = 6348577) B6348577
theorem B12863897 : Blo 1760081 12863897 := bstep (se 2 (by rfl) ⟨4823961, by rfl⟩ : syracuseStep 12863897 = 9647923) B9647923
theorem B3172783 : Blo 1760081 3172783 := bstep (se 1 (by rfl) ⟨2379587, by rfl⟩ : syracuseStep 3172783 = 4759175) B4759175
theorem B2640311 : Blo 1760081 2640311 := bstep (se 1 (by rfl) ⟨1980233, by rfl⟩ : syracuseStep 2640311 = 3960467) B3960467
theorem B3344827 : Blo 1760081 3344827 := bstep (se 1 (by rfl) ⟨2508620, by rfl⟩ : syracuseStep 3344827 = 5017241) B5017241
theorem B7137737 : Blo 1760081 7137737 := bstep (se 2 (by rfl) ⟨2676651, by rfl⟩ : syracuseStep 7137737 = 5353303) B5353303
theorem B2640347 : Blo 1760081 2640347 := bstep (se 1 (by rfl) ⟨1980260, by rfl⟩ : syracuseStep 2640347 = 3960521) B3960521
theorem B5425651 : Blo 1760081 5425651 := bstep (se 1 (by rfl) ⟨4069238, by rfl⟩ : syracuseStep 5425651 = 8138477) B8138477
theorem B6687481 : Blo 1760081 6687481 := bstep (se 2 (by rfl) ⟨2507805, by rfl⟩ : syracuseStep 6687481 = 5015611) B5015611
theorem B22580045 : Blo 1760081 22580045 := bstep (se 3 (by rfl) ⟨4233758, by rfl⟩ : syracuseStep 22580045 = 8467517) B8467517
theorem B19049363 : Blo 1760081 19049363 := bstep (se 1 (by rfl) ⟨14287022, by rfl⟩ : syracuseStep 19049363 = 28574045) B28574045
theorem B2640815 : Blo 1760081 2640815 := bstep (se 1 (by rfl) ⟨1980611, by rfl⟩ : syracuseStep 2640815 = 3961223) B3961223
theorem B2640905 : Blo 1760081 2640905 := bstep (se 2 (by rfl) ⟨990339, by rfl⟩ : syracuseStep 2640905 = 1980679) B1980679
theorem B2640935 : Blo 1760081 2640935 := bstep (se 1 (by rfl) ⟨1980701, by rfl⟩ : syracuseStep 2640935 = 3961403) B3961403
theorem B6704209 : Blo 1760081 6704209 := bstep (se 2 (by rfl) ⟨2514078, by rfl⟩ : syracuseStep 6704209 = 5028157) B5028157
theorem B2641019 : Blo 1760081 2641019 := bstep (se 1 (by rfl) ⟨1980764, by rfl⟩ : syracuseStep 2641019 = 3961529) B3961529
theorem B5942429 : Blo 1760081 5942429 := bstep (se 3 (by rfl) ⟨1114205, by rfl⟩ : syracuseStep 5942429 = 2228411) B2228411
theorem B2641145 : Blo 1760081 2641145 := bstep (se 2 (by rfl) ⟨990429, by rfl⟩ : syracuseStep 2641145 = 1980859) B1980859
theorem B2641247 : Blo 1760081 2641247 := bstep (se 1 (by rfl) ⟨1980935, by rfl⟩ : syracuseStep 2641247 = 3961871) B3961871
theorem B2821481 : Blo 1760081 2821481 := bstep (se 2 (by rfl) ⟨1058055, by rfl⟩ : syracuseStep 2821481 = 2116111) B2116111
theorem B2641259 : Blo 1760081 2641259 := bstep (se 1 (by rfl) ⟨1980944, by rfl⟩ : syracuseStep 2641259 = 3961889) B3961889
theorem B12701071 : Blo 1760081 12701071 := bstep (se 1 (by rfl) ⟨9525803, by rfl⟩ : syracuseStep 12701071 = 19051607) B19051607
theorem B8031707 : Blo 1760081 8031707 := bstep (se 1 (by rfl) ⟨6023780, by rfl⟩ : syracuseStep 8031707 = 12047561) B12047561
theorem B3960359 : Blo 1760081 3960359 := bstep (se 1 (by rfl) ⟨2970269, by rfl⟩ : syracuseStep 3960359 = 5940539) B5940539
theorem B5639719 : Blo 1760081 5639719 := bstep (se 1 (by rfl) ⟨4229789, by rfl⟩ : syracuseStep 5639719 = 8459579) B8459579
theorem B2641487 : Blo 1760081 2641487 := bstep (se 1 (by rfl) ⟨1981115, by rfl⟩ : syracuseStep 2641487 = 3962231) B3962231
theorem B5942969 : Blo 1760081 5942969 := bstep (se 2 (by rfl) ⟨2228613, by rfl⟩ : syracuseStep 5942969 = 4457227) B4457227
theorem B2641607 : Blo 1760081 2641607 := bstep (se 1 (by rfl) ⟨1981205, by rfl⟩ : syracuseStep 2641607 = 3962411) B3962411
theorem B8916803 : Blo 1760081 8916803 := bstep (se 1 (by rfl) ⟨6687602, by rfl⟩ : syracuseStep 8916803 = 13375205) B13375205
theorem B2641769 : Blo 1760081 2641769 := bstep (se 2 (by rfl) ⟨990663, by rfl⟩ : syracuseStep 2641769 = 1981327) B1981327
theorem B3960683 : Blo 1760081 3960683 := bstep (se 1 (by rfl) ⟨2970512, by rfl⟩ : syracuseStep 3960683 = 5941025) B5941025
theorem B3960737 : Blo 1760081 3960737 := bstep (se 2 (by rfl) ⟨1485276, by rfl⟩ : syracuseStep 3960737 = 2970553) B2970553
theorem B2641847 : Blo 1760081 2641847 := bstep (se 1 (by rfl) ⟨1981385, by rfl⟩ : syracuseStep 2641847 = 3962771) B3962771
theorem B2641883 : Blo 1760081 2641883 := bstep (se 1 (by rfl) ⟨1981412, by rfl⟩ : syracuseStep 2641883 = 3962825) B3962825
theorem B7524359 : Blo 1760081 7524359 := bstep (se 1 (by rfl) ⟨5643269, by rfl⟩ : syracuseStep 7524359 = 11286539) B11286539
theorem B6688925 : Blo 1760081 6688925 := bstep (se 3 (by rfl) ⟨1254173, by rfl⟩ : syracuseStep 6688925 = 2508347) B2508347
theorem B6688939 : Blo 1760081 6688939 := bstep (se 1 (by rfl) ⟨5016704, by rfl⟩ : syracuseStep 6688939 = 10033409) B10033409
theorem B20902067 : Blo 1760081 20902067 := bstep (se 1 (by rfl) ⟨15676550, by rfl⟩ : syracuseStep 20902067 = 31353101) B31353101
theorem B3961079 : Blo 1760081 3961079 := bstep (se 1 (by rfl) ⟨2970809, by rfl⟩ : syracuseStep 3961079 = 5941619) B5941619
theorem B5943563 : Blo 1760081 5943563 := bstep (se 1 (by rfl) ⟨4457672, by rfl⟩ : syracuseStep 5943563 = 8915345) B8915345
theorem B13373747 : Blo 1760081 13373747 := bstep (se 1 (by rfl) ⟨10030310, by rfl⟩ : syracuseStep 13373747 = 20060621) B20060621
theorem B4518287 : Blo 1760081 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B2642351 : Blo 1760081 2642351 := bstep (se 1 (by rfl) ⟨1981763, by rfl⟩ : syracuseStep 2642351 = 3963527) B3963527
theorem B6689243 : Blo 1760081 6689243 := bstep (se 1 (by rfl) ⟨5016932, by rfl⟩ : syracuseStep 6689243 = 10033865) B10033865
theorem B2642441 : Blo 1760081 2642441 := bstep (se 2 (by rfl) ⟨990915, by rfl⟩ : syracuseStep 2642441 = 1981831) B1981831
theorem B5943833 : Blo 1760081 5943833 := bstep (se 2 (by rfl) ⟨2228937, by rfl⟩ : syracuseStep 5943833 = 4457875) B4457875
theorem B5083673 : Blo 1760081 5083673 := bstep (se 2 (by rfl) ⟨1906377, by rfl⟩ : syracuseStep 5083673 = 3812755) B3812755
theorem B1880615 : Blo 1760081 1880615 := bstep (se 1 (by rfl) ⟨1410461, by rfl⟩ : syracuseStep 1880615 = 2820923) B2820923
theorem B2642471 : Blo 1760081 2642471 := bstep (se 1 (by rfl) ⟨1981853, by rfl⟩ : syracuseStep 2642471 = 3963707) B3963707
theorem B2642555 : Blo 1760081 2642555 := bstep (se 1 (by rfl) ⟨1981916, by rfl⟩ : syracuseStep 2642555 = 3963833) B3963833
theorem B2970283 : Blo 1760081 2970283 := bstep (se 1 (by rfl) ⟨2227712, by rfl⟩ : syracuseStep 2970283 = 4455425) B4455425
theorem B13365971 : Blo 1760081 13365971 := bstep (se 1 (by rfl) ⟨10024478, by rfl⟩ : syracuseStep 13365971 = 20048957) B20048957
theorem B2642681 : Blo 1760081 2642681 := bstep (se 2 (by rfl) ⟨991005, by rfl⟩ : syracuseStep 2642681 = 1982011) B1982011
theorem B38097677 : Blo 1760081 38097677 := bstep (se 3 (by rfl) ⟨7143314, by rfl⟩ : syracuseStep 38097677 = 14286629) B14286629
theorem B3961673 : Blo 1760081 3961673 := bstep (se 2 (by rfl) ⟨1485627, by rfl⟩ : syracuseStep 3961673 = 2971255) B2971255
theorem B2642783 : Blo 1760081 2642783 := bstep (se 1 (by rfl) ⟨1982087, by rfl⟩ : syracuseStep 2642783 = 3964175) B3964175
theorem B2642795 : Blo 1760081 2642795 := bstep (se 1 (by rfl) ⟨1982096, by rfl⟩ : syracuseStep 2642795 = 3964193) B3964193
theorem B2970587 : Blo 1760081 2970587 := bstep (se 1 (by rfl) ⟨2227940, by rfl⟩ : syracuseStep 2970587 = 4455881) B4455881
theorem B2643023 : Blo 1760081 2643023 := bstep (se 1 (by rfl) ⟨1982267, by rfl⟩ : syracuseStep 2643023 = 3964535) B3964535
theorem B6345809 : Blo 1760081 6345809 := bstep (se 2 (by rfl) ⟨2379678, by rfl⟩ : syracuseStep 6345809 = 4759357) B4759357
theorem B2970823 : Blo 1760081 2970823 := bstep (se 1 (by rfl) ⟨2228117, by rfl⟩ : syracuseStep 2970823 = 4456235) B4456235
theorem B10032407 : Blo 1760081 10032407 := bstep (se 1 (by rfl) ⟨7524305, by rfl⟩ : syracuseStep 10032407 = 15048611) B15048611
theorem B2970985 : Blo 1760081 2970985 := bstep (se 2 (by rfl) ⟨1114119, by rfl⟩ : syracuseStep 2970985 = 2228239) B2228239
theorem B8459693 : Blo 1760081 8459693 := bstep (se 3 (by rfl) ⟨1586192, by rfl⟩ : syracuseStep 8459693 = 3172385) B3172385
theorem B3012103 : Blo 1760081 3012103 := bstep (se 1 (by rfl) ⟨2259077, by rfl⟩ : syracuseStep 3012103 = 4518155) B4518155
theorem B6780449 : Blo 1760081 6780449 := bstep (se 2 (by rfl) ⟨2542668, by rfl⟩ : syracuseStep 6780449 = 5085337) B5085337
theorem B6518369 : Blo 1760081 6518369 := bstep (se 2 (by rfl) ⟨2444388, by rfl⟩ : syracuseStep 6518369 = 4888777) B4888777
theorem B3962465 : Blo 1760081 3962465 := bstep (se 2 (by rfl) ⟨1485924, by rfl⟩ : syracuseStep 3962465 = 2971849) B2971849
theorem B5944967 : Blo 1760081 5944967 := bstep (se 1 (by rfl) ⟨4458725, by rfl⟩ : syracuseStep 5944967 = 8917451) B8917451
theorem B5945021 : Blo 1760081 5945021 := bstep (se 3 (by rfl) ⟨1114691, by rfl⟩ : syracuseStep 5945021 = 2229383) B2229383
theorem B1980103 : Blo 1760081 1980103 := bstep (se 1 (by rfl) ⟨1485077, by rfl⟩ : syracuseStep 1980103 = 2970155) B2970155
theorem B5945183 : Blo 1760081 5945183 := bstep (se 1 (by rfl) ⟨4458887, by rfl⟩ : syracuseStep 5945183 = 8917775) B8917775
theorem B7141229 : Blo 1760081 7141229 := bstep (se 3 (by rfl) ⟨1338980, by rfl⟩ : syracuseStep 7141229 = 2677961) B2677961
theorem B6346615 : Blo 1760081 6346615 := bstep (se 1 (by rfl) ⟨4759961, by rfl⟩ : syracuseStep 6346615 = 9519923) B9519923
theorem B20051873 : Blo 1760081 20051873 := bstep (se 2 (by rfl) ⟨7519452, by rfl⟩ : syracuseStep 20051873 = 15038905) B15038905
theorem B3962807 : Blo 1760081 3962807 := bstep (se 1 (by rfl) ⟨2972105, by rfl⟩ : syracuseStep 3962807 = 5944211) B5944211
theorem B2971579 : Blo 1760081 2971579 := bstep (se 1 (by rfl) ⟨2228684, by rfl⟩ : syracuseStep 2971579 = 4457369) B4457369
theorem B19044305 : Blo 1760081 19044305 := bstep (se 2 (by rfl) ⟨7141614, by rfl⟩ : syracuseStep 19044305 = 14283229) B14283229
theorem B5945345 : Blo 1760081 5945345 := bstep (se 2 (by rfl) ⟨2229504, by rfl⟩ : syracuseStep 5945345 = 4459009) B4459009
theorem B5642255 : Blo 1760081 5642255 := bstep (se 1 (by rfl) ⟨4231691, by rfl⟩ : syracuseStep 5642255 = 8463383) B8463383
theorem B14276645 : Blo 1760081 14276645 := bstep (se 4 (by rfl) ⟨1338435, by rfl⟩ : syracuseStep 14276645 = 2676871) B2676871
theorem B2971687 : Blo 1760081 2971687 := bstep (se 1 (by rfl) ⟨2228765, by rfl⟩ : syracuseStep 2971687 = 4457531) B4457531
theorem B10025117 : Blo 1760081 10025117 := bstep (se 3 (by rfl) ⟨1879709, by rfl⟩ : syracuseStep 10025117 = 3759419) B3759419
theorem B11278565 : Blo 1760081 11278565 := bstep (se 4 (by rfl) ⟨1057365, by rfl⟩ : syracuseStep 11278565 = 2114731) B2114731
theorem B2972011 : Blo 1760081 2972011 := bstep (se 1 (by rfl) ⟨2229008, by rfl⟩ : syracuseStep 2972011 = 4458017) B4458017
theorem B3570095 : Blo 1760081 3570095 := bstep (se 1 (by rfl) ⟨2677571, by rfl⟩ : syracuseStep 3570095 = 5355143) B5355143
theorem B3963401 : Blo 1760081 3963401 := bstep (se 2 (by rfl) ⟨1486275, by rfl⟩ : syracuseStep 3963401 = 2972551) B2972551
theorem B1980967 : Blo 1760081 1980967 := bstep (se 1 (by rfl) ⟨1485725, by rfl⟩ : syracuseStep 1980967 = 2971451) B2971451
theorem B33839693 : Blo 1760081 33839693 := bstep (se 3 (by rfl) ⟨6344942, by rfl⟩ : syracuseStep 33839693 = 12689885) B12689885
theorem B4823675 : Blo 1760081 4823675 := bstep (se 1 (by rfl) ⟨3617756, by rfl⟩ : syracuseStep 4823675 = 7235513) B7235513
theorem B8911619 : Blo 1760081 8911619 := bstep (se 1 (by rfl) ⟨6683714, by rfl⟩ : syracuseStep 8911619 = 13367429) B13367429
theorem B5946155 : Blo 1760081 5946155 := bstep (se 1 (by rfl) ⟨4459616, by rfl⟩ : syracuseStep 5946155 = 8919233) B8919233
theorem B10025801 : Blo 1760081 10025801 := bstep (se 2 (by rfl) ⟨3759675, by rfl⟩ : syracuseStep 10025801 = 7519351) B7519351
theorem B9780041 : Blo 1760081 9780041 := bstep (se 2 (by rfl) ⟨3667515, by rfl⟩ : syracuseStep 9780041 = 7335031) B7335031
theorem B8919881 : Blo 1760081 8919881 := bstep (se 2 (by rfl) ⟨3344955, by rfl⟩ : syracuseStep 8919881 = 6689911) B6689911
theorem B1760095 : Blo 1760081 1760095 := bstep (se 1 (by rfl) ⟨1320071, by rfl⟩ : syracuseStep 1760095 = 2640143) B2640143
theorem B4455263 : Blo 1760081 4455263 := bstep (se 1 (by rfl) ⟨3341447, by rfl⟩ : syracuseStep 4455263 = 6682895) B6682895
theorem B3963743 : Blo 1760081 3963743 := bstep (se 1 (by rfl) ⟨2972807, by rfl⟩ : syracuseStep 3963743 = 5945615) B5945615
theorem B1760123 : Blo 1760081 1760123 := bstep (se 1 (by rfl) ⟨1320092, by rfl⟩ : syracuseStep 1760123 = 2640185) B2640185
theorem B17161105 : Blo 1760081 17161105 := bstep (se 2 (by rfl) ⟨6435414, by rfl⟩ : syracuseStep 17161105 = 12870829) B12870829
theorem B16063379 : Blo 1760081 16063379 := bstep (se 1 (by rfl) ⟨12047534, by rfl⟩ : syracuseStep 16063379 = 24095069) B24095069
theorem B1760175 : Blo 1760081 1760175 := bstep (se 1 (by rfl) ⟨1320131, by rfl⟩ : syracuseStep 1760175 = 2640263) B2640263
theorem B6683579 : Blo 1760081 6683579 := bstep (se 1 (by rfl) ⟨5012684, by rfl⟩ : syracuseStep 6683579 = 10025369) B10025369
theorem B1760199 : Blo 1760081 1760199 := bstep (se 1 (by rfl) ⟨1320149, by rfl⟩ : syracuseStep 1760199 = 2640299) B2640299
theorem B1760219 : Blo 1760081 1760219 := bstep (se 1 (by rfl) ⟨1320164, by rfl⟩ : syracuseStep 1760219 = 2640329) B2640329
theorem B15047653 : Blo 1760081 15047653 := bstep (se 4 (by rfl) ⟨1410717, by rfl⟩ : syracuseStep 15047653 = 2821435) B2821435
theorem B3963923 : Blo 1760081 3963923 := bstep (se 1 (by rfl) ⟨2972942, by rfl⟩ : syracuseStep 3963923 = 5945885) B5945885
theorem B1760295 : Blo 1760081 1760295 := bstep (se 1 (by rfl) ⟨1320221, by rfl⟩ : syracuseStep 1760295 = 2640443) B2640443
theorem B5946425 : Blo 1760081 5946425 := bstep (se 2 (by rfl) ⟨2229909, by rfl⟩ : syracuseStep 5946425 = 4459819) B4459819
theorem B1760335 : Blo 1760081 1760335 := bstep (se 1 (by rfl) ⟨1320251, by rfl⟩ : syracuseStep 1760335 = 2640503) B2640503
theorem B22871119 : Blo 1760081 22871119 := bstep (se 1 (by rfl) ⟨17153339, by rfl⟩ : syracuseStep 22871119 = 34306679) B34306679
theorem B1760351 : Blo 1760081 1760351 := bstep (se 1 (by rfl) ⟨1320263, by rfl⟩ : syracuseStep 1760351 = 2640527) B2640527
theorem B1760379 : Blo 1760081 1760379 := bstep (se 1 (by rfl) ⟨1320284, by rfl⟩ : syracuseStep 1760379 = 2640569) B2640569
theorem B3390587 : Blo 1760081 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B7519385 : Blo 1760081 7519385 := bstep (se 2 (by rfl) ⟨2819769, by rfl⟩ : syracuseStep 7519385 = 5639539) B5639539
theorem B1760431 : Blo 1760081 1760431 := bstep (se 1 (by rfl) ⟨1320323, by rfl⟩ : syracuseStep 1760431 = 2640647) B2640647
theorem B1760455 : Blo 1760081 1760455 := bstep (se 1 (by rfl) ⟨1320341, by rfl⟩ : syracuseStep 1760455 = 2640683) B2640683
theorem B1760475 : Blo 1760081 1760475 := bstep (se 1 (by rfl) ⟨1320356, by rfl⟩ : syracuseStep 1760475 = 2640713) B2640713
theorem B15047927 : Blo 1760081 15047927 := bstep (se 1 (by rfl) ⟨11285945, by rfl⟩ : syracuseStep 15047927 = 22571891) B22571891
theorem B1760551 : Blo 1760081 1760551 := bstep (se 1 (by rfl) ⟨1320413, by rfl⟩ : syracuseStep 1760551 = 2640827) B2640827
theorem B1760591 : Blo 1760081 1760591 := bstep (se 1 (by rfl) ⟨1320443, by rfl⟩ : syracuseStep 1760591 = 2640887) B2640887
theorem B1760607 : Blo 1760081 1760607 := bstep (se 1 (by rfl) ⟨1320455, by rfl⟩ : syracuseStep 1760607 = 2640911) B2640911
theorem B3964265 : Blo 1760081 3964265 := bstep (se 2 (by rfl) ⟨1486599, by rfl⟩ : syracuseStep 3964265 = 2973199) B2973199
theorem B3341675 : Blo 1760081 3341675 := bstep (se 1 (by rfl) ⟨2506256, by rfl⟩ : syracuseStep 3341675 = 5012513) B5012513
theorem B1760635 : Blo 1760081 1760635 := bstep (se 1 (by rfl) ⟨1320476, by rfl⟩ : syracuseStep 1760635 = 2640953) B2640953
theorem B5946749 : Blo 1760081 5946749 := bstep (se 3 (by rfl) ⟨1115015, by rfl⟩ : syracuseStep 5946749 = 2230031) B2230031
theorem B2973071 : Blo 1760081 2973071 := bstep (se 1 (by rfl) ⟨2229803, by rfl⟩ : syracuseStep 2973071 = 4459607) B4459607
theorem B3341729 : Blo 1760081 3341729 := bstep (se 2 (by rfl) ⟨1253148, by rfl⟩ : syracuseStep 3341729 = 2506297) B2506297
theorem B1760687 : Blo 1760081 1760687 := bstep (se 1 (by rfl) ⟨1320515, by rfl⟩ : syracuseStep 1760687 = 2641031) B2641031
theorem B1760711 : Blo 1760081 1760711 := bstep (se 1 (by rfl) ⟨1320533, by rfl⟩ : syracuseStep 1760711 = 2641067) B2641067
theorem B1760731 : Blo 1760081 1760731 := bstep (se 1 (by rfl) ⟨1320548, by rfl⟩ : syracuseStep 1760731 = 2641097) B2641097
theorem B1760807 : Blo 1760081 1760807 := bstep (se 1 (by rfl) ⟨1320605, by rfl⟩ : syracuseStep 1760807 = 2641211) B2641211
theorem B1760847 : Blo 1760081 1760847 := bstep (se 1 (by rfl) ⟨1320635, by rfl⟩ : syracuseStep 1760847 = 2641271) B2641271
theorem B1760863 : Blo 1760081 1760863 := bstep (se 1 (by rfl) ⟨1320647, by rfl⟩ : syracuseStep 1760863 = 2641295) B2641295
theorem B1760891 : Blo 1760081 1760891 := bstep (se 1 (by rfl) ⟨1320668, by rfl⟩ : syracuseStep 1760891 = 2641337) B2641337
theorem B2973307 : Blo 1760081 2973307 := bstep (se 1 (by rfl) ⟨2229980, by rfl⟩ : syracuseStep 2973307 = 4459961) B4459961
theorem B5947019 : Blo 1760081 5947019 := bstep (se 1 (by rfl) ⟨4460264, by rfl⟩ : syracuseStep 5947019 = 8920529) B8920529
theorem B1760943 : Blo 1760081 1760943 := bstep (se 1 (by rfl) ⟨1320707, by rfl⟩ : syracuseStep 1760943 = 2641415) B2641415
theorem B1760967 : Blo 1760081 1760967 := bstep (se 1 (by rfl) ⟨1320725, by rfl⟩ : syracuseStep 1760967 = 2641451) B2641451
theorem B1760987 : Blo 1760081 1760987 := bstep (se 1 (by rfl) ⟨1320740, by rfl⟩ : syracuseStep 1760987 = 2641481) B2641481
theorem B5644025 : Blo 1760081 5644025 := bstep (se 2 (by rfl) ⟨2116509, by rfl⟩ : syracuseStep 5644025 = 4233019) B4233019
theorem B1761063 : Blo 1760081 1761063 := bstep (se 1 (by rfl) ⟨1320797, by rfl⟩ : syracuseStep 1761063 = 2641595) B2641595
theorem B1761103 : Blo 1760081 1761103 := bstep (se 1 (by rfl) ⟨1320827, by rfl⟩ : syracuseStep 1761103 = 2641655) B2641655
theorem B1761119 : Blo 1760081 1761119 := bstep (se 1 (by rfl) ⟨1320839, by rfl⟩ : syracuseStep 1761119 = 2641679) B2641679
theorem B7241567 : Blo 1760081 7241567 := bstep (se 1 (by rfl) ⟨5431175, by rfl⟩ : syracuseStep 7241567 = 10862351) B10862351
theorem B101564279 : Blo 1760081 101564279 := bstep (se 1 (by rfl) ⟨76173209, by rfl⟩ : syracuseStep 101564279 = 152346419) B152346419
theorem B1761147 : Blo 1760081 1761147 := bstep (se 1 (by rfl) ⟨1320860, by rfl⟩ : syracuseStep 1761147 = 2641721) B2641721
theorem B2228143 : Blo 1760081 2228143 := bstep (se 1 (by rfl) ⟨1671107, by rfl⟩ : syracuseStep 2228143 = 3342215) B3342215
theorem B4456367 : Blo 1760081 4456367 := bstep (se 1 (by rfl) ⟨3342275, by rfl⟩ : syracuseStep 4456367 = 6684551) B6684551
theorem B1761199 : Blo 1760081 1761199 := bstep (se 1 (by rfl) ⟨1320899, by rfl⟩ : syracuseStep 1761199 = 2641799) B2641799
theorem B1761223 : Blo 1760081 1761223 := bstep (se 1 (by rfl) ⟨1320917, by rfl⟩ : syracuseStep 1761223 = 2641835) B2641835
theorem B1761243 : Blo 1760081 1761243 := bstep (se 1 (by rfl) ⟨1320932, by rfl⟩ : syracuseStep 1761243 = 2641865) B2641865
theorem B8912915 : Blo 1760081 8912915 := bstep (se 1 (by rfl) ⟨6684686, by rfl⟩ : syracuseStep 8912915 = 13369373) B13369373
theorem B13934711 : Blo 1760081 13934711 := bstep (se 1 (by rfl) ⟨10451033, by rfl⟩ : syracuseStep 13934711 = 20902067) B20902067
theorem B1761567 : Blo 1760081 1761567 := bstep (se 1 (by rfl) ⟨1321175, by rfl⟩ : syracuseStep 1761567 = 2642351) B2642351
theorem B1761627 : Blo 1760081 1761627 := bstep (se 1 (by rfl) ⟨1321220, by rfl⟩ : syracuseStep 1761627 = 2642441) B2642441
theorem B1761647 : Blo 1760081 1761647 := bstep (se 1 (by rfl) ⟨1321235, by rfl⟩ : syracuseStep 1761647 = 2642471) B2642471
theorem B1761703 : Blo 1760081 1761703 := bstep (se 1 (by rfl) ⟨1321277, by rfl⟩ : syracuseStep 1761703 = 2642555) B2642555
theorem B6775265 : Blo 1760081 6775265 := bstep (se 2 (by rfl) ⟨2540724, by rfl⟩ : syracuseStep 6775265 = 5081449) B5081449
theorem B1761787 : Blo 1760081 1761787 := bstep (se 1 (by rfl) ⟨1321340, by rfl⟩ : syracuseStep 1761787 = 2642681) B2642681
theorem B1761855 : Blo 1760081 1761855 := bstep (se 1 (by rfl) ⟨1321391, by rfl⟩ : syracuseStep 1761855 = 2642783) B2642783
theorem B1761863 : Blo 1760081 1761863 := bstep (se 1 (by rfl) ⟨1321397, by rfl⟩ : syracuseStep 1761863 = 2642795) B2642795
theorem B7234201 : Blo 1760081 7234201 := bstep (se 2 (by rfl) ⟨2712825, by rfl⟩ : syracuseStep 7234201 = 5425651) B5425651
theorem B6685355 : Blo 1760081 6685355 := bstep (se 1 (by rfl) ⟨5014016, by rfl⟩ : syracuseStep 6685355 = 10028033) B10028033
theorem B5014199 : Blo 1760081 5014199 := bstep (se 1 (by rfl) ⟨3760649, by rfl⟩ : syracuseStep 5014199 = 7521299) B7521299
theorem B1762015 : Blo 1760081 1762015 := bstep (se 1 (by rfl) ⟨1321511, by rfl⟩ : syracuseStep 1762015 = 2643023) B2643023
theorem B4457207 : Blo 1760081 4457207 := bstep (se 1 (by rfl) ⟨3342905, by rfl⟩ : syracuseStep 4457207 = 6685811) B6685811
theorem B33850385 : Blo 1760081 33850385 := bstep (se 2 (by rfl) ⟨12693894, by rfl⟩ : syracuseStep 33850385 = 25387789) B25387789
theorem B9520253 : Blo 1760081 9520253 := bstep (se 3 (by rfl) ⟨1785047, by rfl⟩ : syracuseStep 9520253 = 3570095) B3570095
theorem B22881473 : Blo 1760081 22881473 := bstep (se 2 (by rfl) ⟨8580552, by rfl⟩ : syracuseStep 22881473 = 17161105) B17161105
theorem B4760819 : Blo 1760081 4760819 := bstep (se 1 (by rfl) ⟨3570614, by rfl⟩ : syracuseStep 4760819 = 7141229) B7141229
theorem B2229535 : Blo 1760081 2229535 := bstep (se 1 (by rfl) ⟨1672151, by rfl⟩ : syracuseStep 2229535 = 3344303) B3344303
theorem B20063537 : Blo 1760081 20063537 := bstep (se 2 (by rfl) ⟨7523826, by rfl⟩ : syracuseStep 20063537 = 15047653) B15047653
theorem B4457825 : Blo 1760081 4457825 := bstep (se 2 (by rfl) ⟨1671684, by rfl⟩ : syracuseStep 4457825 = 3343369) B3343369
theorem B5014973 : Blo 1760081 5014973 := bstep (se 3 (by rfl) ⟨940307, by rfl⟩ : syracuseStep 5014973 = 1880615) B1880615
theorem B8938945 : Blo 1760081 8938945 := bstep (se 2 (by rfl) ⟨3352104, by rfl⟩ : syracuseStep 8938945 = 6704209) B6704209
theorem B9651719 : Blo 1760081 9651719 := bstep (se 1 (by rfl) ⟨7238789, by rfl⟩ : syracuseStep 9651719 = 14477579) B14477579
theorem B5941079 : Blo 1760081 5941079 := bstep (se 1 (by rfl) ⟨4455809, by rfl⟩ : syracuseStep 5941079 = 8911619) B8911619
theorem B16934761 : Blo 1760081 16934761 := bstep (se 2 (by rfl) ⟨6350535, by rfl⟩ : syracuseStep 16934761 = 12701071) B12701071
theorem B10708919 : Blo 1760081 10708919 := bstep (se 1 (by rfl) ⟨8031689, by rfl⟩ : syracuseStep 10708919 = 16063379) B16063379
theorem B12699575 : Blo 1760081 12699575 := bstep (se 1 (by rfl) ⟨9524681, by rfl⟩ : syracuseStep 12699575 = 19049363) B19049363
theorem B4016137 : Blo 1760081 4016137 := bstep (se 2 (by rfl) ⟨1506051, by rfl⟩ : syracuseStep 4016137 = 3012103) B3012103
theorem B19310845 : Blo 1760081 19310845 := bstep (se 3 (by rfl) ⟨3620783, by rfl⟩ : syracuseStep 19310845 = 7241567) B7241567
theorem B2640137 : Blo 1760081 2640137 := bstep (se 2 (by rfl) ⟨990051, by rfl⟩ : syracuseStep 2640137 = 1980103) B1980103
theorem B2640239 : Blo 1760081 2640239 := bstep (se 1 (by rfl) ⟨1980179, by rfl⟩ : syracuseStep 2640239 = 3960359) B3960359
theorem B3762683 : Blo 1760081 3762683 := bstep (se 1 (by rfl) ⟨2822012, by rfl⟩ : syracuseStep 3762683 = 5644025) B5644025
theorem B2640455 : Blo 1760081 2640455 := bstep (se 1 (by rfl) ⟨1980341, by rfl⟩ : syracuseStep 2640455 = 3960683) B3960683
theorem B67709519 : Blo 1760081 67709519 := bstep (se 1 (by rfl) ⟨50782139, by rfl⟩ : syracuseStep 67709519 = 101564279) B101564279
theorem B2640491 : Blo 1760081 2640491 := bstep (se 1 (by rfl) ⟨1980368, by rfl⟩ : syracuseStep 2640491 = 3960737) B3960737
theorem B5016239 : Blo 1760081 5016239 := bstep (se 1 (by rfl) ⟨3762179, by rfl⟩ : syracuseStep 5016239 = 7524359) B7524359
theorem B4459283 : Blo 1760081 4459283 := bstep (se 1 (by rfl) ⟨3344462, by rfl⟩ : syracuseStep 4459283 = 6688925) B6688925
theorem B2640719 : Blo 1760081 2640719 := bstep (se 1 (by rfl) ⟨1980539, by rfl⟩ : syracuseStep 2640719 = 3961079) B3961079
theorem B8915831 : Blo 1760081 8915831 := bstep (se 1 (by rfl) ⟨6686873, by rfl⟩ : syracuseStep 8915831 = 13373747) B13373747
theorem B5942159 : Blo 1760081 5942159 := bstep (se 1 (by rfl) ⟨4456619, by rfl⟩ : syracuseStep 5942159 = 8913239) B8913239
theorem B54225845 : Blo 1760081 54225845 := bstep (se 5 (by rfl) ⟨2541836, by rfl⟩ : syracuseStep 54225845 = 5083673) B5083673
theorem B4459495 : Blo 1760081 4459495 := bstep (se 1 (by rfl) ⟨3344621, by rfl⟩ : syracuseStep 4459495 = 6689243) B6689243
theorem B25398451 : Blo 1760081 25398451 := bstep (se 1 (by rfl) ⟨19048838, by rfl⟩ : syracuseStep 25398451 = 38097677) B38097677
theorem B2641115 : Blo 1760081 2641115 := bstep (se 1 (by rfl) ⟨1980836, by rfl⟩ : syracuseStep 2641115 = 3961673) B3961673
theorem B4230377 : Blo 1760081 4230377 := bstep (se 2 (by rfl) ⟨1586391, by rfl⟩ : syracuseStep 4230377 = 3172783) B3172783
theorem B4459769 : Blo 1760081 4459769 := bstep (se 2 (by rfl) ⟨1672413, by rfl⟩ : syracuseStep 4459769 = 3344827) B3344827
theorem B2641289 : Blo 1760081 2641289 := bstep (se 2 (by rfl) ⟨990483, by rfl⟩ : syracuseStep 2641289 = 1980967) B1980967
theorem B4230539 : Blo 1760081 4230539 := bstep (se 1 (by rfl) ⟨3172904, by rfl⟩ : syracuseStep 4230539 = 6345809) B6345809
theorem B3960251 : Blo 1760081 3960251 := bstep (se 1 (by rfl) ⟨2970188, by rfl⟩ : syracuseStep 3960251 = 5940377) B5940377
theorem B7138775 : Blo 1760081 7138775 := bstep (se 1 (by rfl) ⟨5354081, by rfl⟩ : syracuseStep 7138775 = 10708163) B10708163
theorem B6688271 : Blo 1760081 6688271 := bstep (se 1 (by rfl) ⟨5016203, by rfl⟩ : syracuseStep 6688271 = 10032407) B10032407
theorem B3960377 : Blo 1760081 3960377 := bstep (se 2 (by rfl) ⟨1485141, by rfl⟩ : syracuseStep 3960377 = 2970283) B2970283
theorem B5639795 : Blo 1760081 5639795 := bstep (se 1 (by rfl) ⟨4229846, by rfl⟩ : syracuseStep 5639795 = 8459693) B8459693
theorem B6106739 : Blo 1760081 6106739 := bstep (se 1 (by rfl) ⟨4580054, by rfl⟩ : syracuseStep 6106739 = 9160109) B9160109
theorem B8916641 : Blo 1760081 8916641 := bstep (se 2 (by rfl) ⟨3343740, by rfl⟩ : syracuseStep 8916641 = 6687481) B6687481
theorem B4345579 : Blo 1760081 4345579 := bstep (se 1 (by rfl) ⟨3259184, by rfl⟩ : syracuseStep 4345579 = 6518369) B6518369
theorem B2641643 : Blo 1760081 2641643 := bstep (se 1 (by rfl) ⟨1981232, by rfl⟩ : syracuseStep 2641643 = 3962465) B3962465
theorem B2641871 : Blo 1760081 2641871 := bstep (se 1 (by rfl) ⟨1981403, by rfl⟩ : syracuseStep 2641871 = 3962807) B3962807
theorem B30494825 : Blo 1760081 30494825 := bstep (se 2 (by rfl) ⟨11435559, by rfl⟩ : syracuseStep 30494825 = 22871119) B22871119
theorem B5943401 : Blo 1760081 5943401 := bstep (se 2 (by rfl) ⟨2228775, by rfl⟩ : syracuseStep 5943401 = 4457551) B4457551
theorem B10858699 : Blo 1760081 10858699 := bstep (se 1 (by rfl) ⟨8144024, by rfl⟩ : syracuseStep 10858699 = 16288049) B16288049
theorem B3961043 : Blo 1760081 3961043 := bstep (se 1 (by rfl) ⟨2970782, by rfl⟩ : syracuseStep 3961043 = 5941565) B5941565
theorem B3961097 : Blo 1760081 3961097 := bstep (se 2 (by rfl) ⟨1485411, by rfl⟩ : syracuseStep 3961097 = 2970823) B2970823
theorem B72298817 : Blo 1760081 72298817 := bstep (se 2 (by rfl) ⟨27112056, by rfl⟩ : syracuseStep 72298817 = 54224113) B54224113
theorem B2642267 : Blo 1760081 2642267 := bstep (se 1 (by rfl) ⟨1981700, by rfl⟩ : syracuseStep 2642267 = 3963401) B3963401
theorem B3961313 : Blo 1760081 3961313 := bstep (se 2 (by rfl) ⟨1485492, by rfl⟩ : syracuseStep 3961313 = 2970985) B2970985
theorem B15053363 : Blo 1760081 15053363 := bstep (se 1 (by rfl) ⟨11290022, by rfl⟩ : syracuseStep 15053363 = 22580045) B22580045
theorem B2970175 : Blo 1760081 2970175 := bstep (se 1 (by rfl) ⟨2227631, by rfl⟩ : syracuseStep 2970175 = 4455263) B4455263
theorem B2642495 : Blo 1760081 2642495 := bstep (se 1 (by rfl) ⟨1981871, by rfl⟩ : syracuseStep 2642495 = 3963743) B3963743
theorem B2642615 : Blo 1760081 2642615 := bstep (se 1 (by rfl) ⟨1981961, by rfl⟩ : syracuseStep 2642615 = 3963923) B3963923
theorem B3961619 : Blo 1760081 3961619 := bstep (se 1 (by rfl) ⟨2971214, by rfl⟩ : syracuseStep 3961619 = 5942429) B5942429
theorem B10031951 : Blo 1760081 10031951 := bstep (se 1 (by rfl) ⟨7523963, by rfl⟩ : syracuseStep 10031951 = 15047927) B15047927
theorem B1880987 : Blo 1760081 1880987 := bstep (se 1 (by rfl) ⟨1410740, by rfl⟩ : syracuseStep 1880987 = 2821481) B2821481
theorem B2642843 : Blo 1760081 2642843 := bstep (se 1 (by rfl) ⟨1982132, by rfl⟩ : syracuseStep 2642843 = 3964265) B3964265
theorem B5944265 : Blo 1760081 5944265 := bstep (se 2 (by rfl) ⟨2229099, by rfl⟩ : syracuseStep 5944265 = 4458199) B4458199
theorem B5354471 : Blo 1760081 5354471 := bstep (se 1 (by rfl) ⟨4015853, by rfl⟩ : syracuseStep 5354471 = 8031707) B8031707
theorem B3961979 : Blo 1760081 3961979 := bstep (se 1 (by rfl) ⟨2971484, by rfl⟩ : syracuseStep 3961979 = 5942969) B5942969
theorem B50771069 : Blo 1760081 50771069 := bstep (se 3 (by rfl) ⟨9519575, by rfl⟩ : syracuseStep 50771069 = 19039151) B19039151
theorem B5944535 : Blo 1760081 5944535 := bstep (se 1 (by rfl) ⟨4458401, by rfl⟩ : syracuseStep 5944535 = 8916803) B8916803
theorem B2970857 : Blo 1760081 2970857 := bstep (se 2 (by rfl) ⟨1114071, by rfl⟩ : syracuseStep 2970857 = 2228143) B2228143
theorem B3962105 : Blo 1760081 3962105 := bstep (se 2 (by rfl) ⟨1485789, by rfl⟩ : syracuseStep 3962105 = 2971579) B2971579
theorem B2970911 : Blo 1760081 2970911 := bstep (se 1 (by rfl) ⟨2228183, by rfl⟩ : syracuseStep 2970911 = 4456367) B4456367
theorem B15046013 : Blo 1760081 15046013 := bstep (se 3 (by rfl) ⟨2821127, by rfl⟩ : syracuseStep 15046013 = 5642255) B5642255
theorem B3962249 : Blo 1760081 3962249 := bstep (se 2 (by rfl) ⟨1485843, by rfl⟩ : syracuseStep 3962249 = 2971687) B2971687
theorem B3962375 : Blo 1760081 3962375 := bstep (se 1 (by rfl) ⟨2971781, by rfl⟩ : syracuseStep 3962375 = 5943563) B5943563
theorem B4232711 : Blo 1760081 4232711 := bstep (se 1 (by rfl) ⟨3174533, by rfl⟩ : syracuseStep 4232711 = 6349067) B6349067
theorem B8918585 : Blo 1760081 8918585 := bstep (se 2 (by rfl) ⟨3344469, by rfl⟩ : syracuseStep 8918585 = 6688939) B6688939
theorem B3012191 : Blo 1760081 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B2381419 : Blo 1760081 2381419 := bstep (se 1 (by rfl) ⟨1786064, by rfl⟩ : syracuseStep 2381419 = 3572129) B3572129
theorem B3962555 : Blo 1760081 3962555 := bstep (se 1 (by rfl) ⟨2971916, by rfl⟩ : syracuseStep 3962555 = 5943833) B5943833
theorem B8910647 : Blo 1760081 8910647 := bstep (se 1 (by rfl) ⟨6682985, by rfl⟩ : syracuseStep 8910647 = 13365971) B13365971
theorem B3962681 : Blo 1760081 3962681 := bstep (se 2 (by rfl) ⟨1486005, by rfl⟩ : syracuseStep 3962681 = 2972011) B2972011
theorem B1980391 : Blo 1760081 1980391 := bstep (se 1 (by rfl) ⟨1485293, by rfl⟩ : syracuseStep 1980391 = 2970587) B2970587
theorem B19306631 : Blo 1760081 19306631 := bstep (se 1 (by rfl) ⟨14479973, by rfl⟩ : syracuseStep 19306631 = 28959947) B28959947
theorem B8911133 : Blo 1760081 8911133 := bstep (se 3 (by rfl) ⟨1670837, by rfl⟩ : syracuseStep 8911133 = 3341675) B3341675
theorem B12695885 : Blo 1760081 12695885 := bstep (se 3 (by rfl) ⟨2380478, by rfl⟩ : syracuseStep 12695885 = 4760957) B4760957
theorem B4520299 : Blo 1760081 4520299 := bstep (se 1 (by rfl) ⟨3390224, by rfl⟩ : syracuseStep 4520299 = 6780449) B6780449
theorem B3963311 : Blo 1760081 3963311 := bstep (se 1 (by rfl) ⟨2972483, by rfl⟩ : syracuseStep 3963311 = 5944967) B5944967
theorem B10033591 : Blo 1760081 10033591 := bstep (se 1 (by rfl) ⟨7525193, by rfl⟩ : syracuseStep 10033591 = 15050387) B15050387
theorem B3963347 : Blo 1760081 3963347 := bstep (se 1 (by rfl) ⟨2972510, by rfl⟩ : syracuseStep 3963347 = 5945021) B5945021
theorem B4233683 : Blo 1760081 4233683 := bstep (se 1 (by rfl) ⟨3175262, by rfl⟩ : syracuseStep 4233683 = 6350525) B6350525
theorem B3963455 : Blo 1760081 3963455 := bstep (se 1 (by rfl) ⟨2972591, by rfl⟩ : syracuseStep 3963455 = 5945183) B5945183
theorem B13367915 : Blo 1760081 13367915 := bstep (se 1 (by rfl) ⟨10025936, by rfl⟩ : syracuseStep 13367915 = 20051873) B20051873
theorem B51452533 : Blo 1760081 51452533 := bstep (se 5 (by rfl) ⟨2411837, by rfl⟩ : syracuseStep 51452533 = 4823675) B4823675
theorem B2972281 : Blo 1760081 2972281 := bstep (se 2 (by rfl) ⟨1114605, by rfl⟩ : syracuseStep 2972281 = 2229211) B2229211
theorem B12696203 : Blo 1760081 12696203 := bstep (se 1 (by rfl) ⟨9522152, by rfl⟩ : syracuseStep 12696203 = 19044305) B19044305
theorem B3963563 : Blo 1760081 3963563 := bstep (se 1 (by rfl) ⟨2972672, by rfl⟩ : syracuseStep 3963563 = 5945345) B5945345
theorem B2972335 : Blo 1760081 2972335 := bstep (se 1 (by rfl) ⟨2229251, by rfl⟩ : syracuseStep 2972335 = 4458503) B4458503
theorem B9517763 : Blo 1760081 9517763 := bstep (se 1 (by rfl) ⟨7138322, by rfl⟩ : syracuseStep 9517763 = 14276645) B14276645
theorem B6683411 : Blo 1760081 6683411 := bstep (se 1 (by rfl) ⟨5012558, by rfl⟩ : syracuseStep 6683411 = 10025117) B10025117
theorem B7519043 : Blo 1760081 7519043 := bstep (se 1 (by rfl) ⟨5639282, by rfl⟩ : syracuseStep 7519043 = 11278565) B11278565
theorem B1760155 : Blo 1760081 1760155 := bstep (se 1 (by rfl) ⟨1320116, by rfl⟩ : syracuseStep 1760155 = 2640233) B2640233
theorem B1809307 : Blo 1760081 1809307 := bstep (se 1 (by rfl) ⟨1356980, by rfl⟩ : syracuseStep 1809307 = 2713961) B2713961
theorem B5643179 : Blo 1760081 5643179 := bstep (se 1 (by rfl) ⟨4232384, by rfl⟩ : syracuseStep 5643179 = 8464769) B8464769
theorem B8575931 : Blo 1760081 8575931 := bstep (se 1 (by rfl) ⟨6431948, by rfl⟩ : syracuseStep 8575931 = 12863897) B12863897
theorem B1760207 : Blo 1760081 1760207 := bstep (se 1 (by rfl) ⟨1320155, by rfl⟩ : syracuseStep 1760207 = 2640311) B2640311
theorem B4758491 : Blo 1760081 4758491 := bstep (se 1 (by rfl) ⟨3568868, by rfl⟩ : syracuseStep 4758491 = 7137737) B7137737
theorem B1760231 : Blo 1760081 1760231 := bstep (se 1 (by rfl) ⟨1320173, by rfl⟩ : syracuseStep 1760231 = 2640347) B2640347
theorem B22559795 : Blo 1760081 22559795 := bstep (se 1 (by rfl) ⟨16919846, by rfl⟩ : syracuseStep 22559795 = 33839693) B33839693
theorem B3964103 : Blo 1760081 3964103 := bstep (se 1 (by rfl) ⟨2973077, by rfl⟩ : syracuseStep 3964103 = 5946155) B5946155
theorem B6683867 : Blo 1760081 6683867 := bstep (se 1 (by rfl) ⟨5012900, by rfl⟩ : syracuseStep 6683867 = 10025801) B10025801
theorem B6520027 : Blo 1760081 6520027 := bstep (se 1 (by rfl) ⟨4890020, by rfl⟩ : syracuseStep 6520027 = 9780041) B9780041
theorem B5946587 : Blo 1760081 5946587 := bstep (se 1 (by rfl) ⟨4459940, by rfl⟩ : syracuseStep 5946587 = 8919881) B8919881
theorem B1760543 : Blo 1760081 1760543 := bstep (se 1 (by rfl) ⟨1320407, by rfl⟩ : syracuseStep 1760543 = 2640815) B2640815
theorem B4455719 : Blo 1760081 4455719 := bstep (se 1 (by rfl) ⟨3341789, by rfl⟩ : syracuseStep 4455719 = 6683579) B6683579
theorem B1760603 : Blo 1760081 1760603 := bstep (se 1 (by rfl) ⟨1320452, by rfl⟩ : syracuseStep 1760603 = 2640905) B2640905
theorem B1760623 : Blo 1760081 1760623 := bstep (se 1 (by rfl) ⟨1320467, by rfl⟩ : syracuseStep 1760623 = 2640935) B2640935
theorem B3964283 : Blo 1760081 3964283 := bstep (se 1 (by rfl) ⟨2973212, by rfl⟩ : syracuseStep 3964283 = 5946425) B5946425
theorem B7519625 : Blo 1760081 7519625 := bstep (se 2 (by rfl) ⟨2819859, by rfl⟩ : syracuseStep 7519625 = 5639719) B5639719
theorem B1760679 : Blo 1760081 1760679 := bstep (se 1 (by rfl) ⟨1320509, by rfl⟩ : syracuseStep 1760679 = 2641019) B2641019
theorem B2260391 : Blo 1760081 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B5012923 : Blo 1760081 5012923 := bstep (se 1 (by rfl) ⟨3759692, by rfl⟩ : syracuseStep 5012923 = 7519385) B7519385
theorem B3964409 : Blo 1760081 3964409 := bstep (se 2 (by rfl) ⟨1486653, by rfl⟩ : syracuseStep 3964409 = 2973307) B2973307
theorem B1760763 : Blo 1760081 1760763 := bstep (se 1 (by rfl) ⟨1320572, by rfl⟩ : syracuseStep 1760763 = 2641145) B2641145
theorem B1760831 : Blo 1760081 1760831 := bstep (se 1 (by rfl) ⟨1320623, by rfl⟩ : syracuseStep 1760831 = 2641247) B2641247
theorem B1760839 : Blo 1760081 1760839 := bstep (se 1 (by rfl) ⟨1320629, by rfl⟩ : syracuseStep 1760839 = 2641259) B2641259
theorem B3964499 : Blo 1760081 3964499 := bstep (se 1 (by rfl) ⟨2973374, by rfl⟩ : syracuseStep 3964499 = 5946749) B5946749
theorem B1982047 : Blo 1760081 1982047 := bstep (se 1 (by rfl) ⟨1486535, by rfl⟩ : syracuseStep 1982047 = 2973071) B2973071
theorem B2227819 : Blo 1760081 2227819 := bstep (se 1 (by rfl) ⟨1670864, by rfl⟩ : syracuseStep 2227819 = 3341729) B3341729
theorem B1760991 : Blo 1760081 1760991 := bstep (se 1 (by rfl) ⟨1320743, by rfl⟩ : syracuseStep 1760991 = 2641487) B2641487
theorem B3964679 : Blo 1760081 3964679 := bstep (se 1 (by rfl) ⟨2973509, by rfl⟩ : syracuseStep 3964679 = 5947019) B5947019
theorem B1761071 : Blo 1760081 1761071 := bstep (se 1 (by rfl) ⟨1320803, by rfl⟩ : syracuseStep 1761071 = 2641607) B2641607
theorem B8462153 : Blo 1760081 8462153 := bstep (se 2 (by rfl) ⟨3173307, by rfl⟩ : syracuseStep 8462153 = 6346615) B6346615
theorem B1761179 : Blo 1760081 1761179 := bstep (se 1 (by rfl) ⟨1320884, by rfl⟩ : syracuseStep 1761179 = 2641769) B2641769
theorem B7626653 : Blo 1760081 7626653 := bstep (se 3 (by rfl) ⟨1429997, by rfl⟩ : syracuseStep 7626653 = 2859995) B2859995
theorem B1761231 : Blo 1760081 1761231 := bstep (se 1 (by rfl) ⟨1320923, by rfl⟩ : syracuseStep 1761231 = 2641847) B2641847
theorem B1761255 : Blo 1760081 1761255 := bstep (se 1 (by rfl) ⟨1320941, by rfl⟩ : syracuseStep 1761255 = 2641883) B2641883
theorem B1761511 : Blo 1760081 1761511 := bstep (se 1 (by rfl) ⟨1321133, by rfl⟩ : syracuseStep 1761511 = 2642267) B2642267
theorem B37159229 : Blo 1760081 37159229 := bstep (se 3 (by rfl) ⟨6967355, by rfl⟩ : syracuseStep 37159229 = 13934711) B13934711
theorem B25747793 : Blo 1760081 25747793 := bstep (se 2 (by rfl) ⟨9655422, by rfl⟩ : syracuseStep 25747793 = 19310845) B19310845
theorem B10035575 : Blo 1760081 10035575 := bstep (se 1 (by rfl) ⟨7526681, by rfl⟩ : syracuseStep 10035575 = 15053363) B15053363
theorem B1761663 : Blo 1760081 1761663 := bstep (se 1 (by rfl) ⟨1321247, by rfl⟩ : syracuseStep 1761663 = 2642495) B2642495
theorem B4456903 : Blo 1760081 4456903 := bstep (se 1 (by rfl) ⟨3342677, by rfl⟩ : syracuseStep 4456903 = 6685355) B6685355
theorem B3342799 : Blo 1760081 3342799 := bstep (se 1 (by rfl) ⟨2507099, by rfl⟩ : syracuseStep 3342799 = 5014199) B5014199
theorem B1761743 : Blo 1760081 1761743 := bstep (se 1 (by rfl) ⟨1321307, by rfl⟩ : syracuseStep 1761743 = 2642615) B2642615
theorem B13378121 : Blo 1760081 13378121 := bstep (se 2 (by rfl) ⟨5016795, by rfl⟩ : syracuseStep 13378121 = 10033591) B10033591
theorem B1761895 : Blo 1760081 1761895 := bstep (se 1 (by rfl) ⟨1321421, by rfl⟩ : syracuseStep 1761895 = 2642843) B2642843
theorem B15254315 : Blo 1760081 15254315 := bstep (se 1 (by rfl) ⟨11440736, by rfl⟩ : syracuseStep 15254315 = 22881473) B22881473
theorem B32130037 : Blo 1760081 32130037 := bstep (se 5 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 32130037 = 3012191) B3012191
theorem B5940431 : Blo 1760081 5940431 := bstep (se 1 (by rfl) ⟨4455323, by rfl⟩ : syracuseStep 5940431 = 8910647) B8910647
theorem B5940755 : Blo 1760081 5940755 := bstep (se 1 (by rfl) ⟨4455566, by rfl⟩ : syracuseStep 5940755 = 8911133) B8911133
theorem B8463923 : Blo 1760081 8463923 := bstep (se 1 (by rfl) ⟨6347942, by rfl⟩ : syracuseStep 8463923 = 12695885) B12695885
theorem B8693369 : Blo 1760081 8693369 := bstep (se 2 (by rfl) ⟨3260013, by rfl⟩ : syracuseStep 8693369 = 6520027) B6520027
theorem B2508455 : Blo 1760081 2508455 := bstep (se 1 (by rfl) ⟨1881341, by rfl⟩ : syracuseStep 2508455 = 3762683) B3762683
theorem B45139679 : Blo 1760081 45139679 := bstep (se 1 (by rfl) ⟨33854759, by rfl⟩ : syracuseStep 45139679 = 67709519) B67709519
theorem B8464135 : Blo 1760081 8464135 := bstep (se 1 (by rfl) ⟨6348101, by rfl⟩ : syracuseStep 8464135 = 12696203) B12696203
theorem B3344159 : Blo 1760081 3344159 := bstep (se 1 (by rfl) ⟨2508119, by rfl⟩ : syracuseStep 3344159 = 5016239) B5016239
theorem B3762119 : Blo 1760081 3762119 := bstep (se 1 (by rfl) ⟨2821589, by rfl⟩ : syracuseStep 3762119 = 5643179) B5643179
theorem B3172327 : Blo 1760081 3172327 := bstep (se 1 (by rfl) ⟨2379245, by rfl⟩ : syracuseStep 3172327 = 4758491) B4758491
theorem B2820251 : Blo 1760081 2820251 := bstep (se 1 (by rfl) ⟨2115188, by rfl⟩ : syracuseStep 2820251 = 4230377) B4230377
theorem B2820359 : Blo 1760081 2820359 := bstep (se 1 (by rfl) ⟨2115269, by rfl⟩ : syracuseStep 2820359 = 4230539) B4230539
theorem B2640167 : Blo 1760081 2640167 := bstep (se 1 (by rfl) ⟨1980125, by rfl⟩ : syracuseStep 2640167 = 3960251) B3960251
theorem B5794105 : Blo 1760081 5794105 := bstep (se 2 (by rfl) ⟨2172789, by rfl⟩ : syracuseStep 5794105 = 4345579) B4345579
theorem B4458847 : Blo 1760081 4458847 := bstep (se 1 (by rfl) ⟨3344135, by rfl⟩ : syracuseStep 4458847 = 6688271) B6688271
theorem B2640251 : Blo 1760081 2640251 := bstep (se 1 (by rfl) ⟨1980188, by rfl⟩ : syracuseStep 2640251 = 3960377) B3960377
theorem B5015965 : Blo 1760081 5015965 := bstep (se 3 (by rfl) ⟨940493, by rfl⟩ : syracuseStep 5015965 = 1880987) B1880987
theorem B22579681 : Blo 1760081 22579681 := bstep (se 2 (by rfl) ⟨8467380, by rfl⟩ : syracuseStep 22579681 = 16934761) B16934761
theorem B2640521 : Blo 1760081 2640521 := bstep (se 2 (by rfl) ⟨990195, by rfl⟩ : syracuseStep 2640521 = 1980391) B1980391
theorem B5941943 : Blo 1760081 5941943 := bstep (se 1 (by rfl) ⟨4456457, by rfl⟩ : syracuseStep 5941943 = 8912915) B8912915
theorem B2640695 : Blo 1760081 2640695 := bstep (se 1 (by rfl) ⟨1980521, by rfl⟩ : syracuseStep 2640695 = 3961043) B3961043
theorem B2640731 : Blo 1760081 2640731 := bstep (se 1 (by rfl) ⟨1980548, by rfl⟩ : syracuseStep 2640731 = 3961097) B3961097
theorem B14478265 : Blo 1760081 14478265 := bstep (se 2 (by rfl) ⟨5429349, by rfl⟩ : syracuseStep 14478265 = 10858699) B10858699
theorem B4516843 : Blo 1760081 4516843 := bstep (se 1 (by rfl) ⟨3387632, by rfl⟩ : syracuseStep 4516843 = 6775265) B6775265
theorem B2640875 : Blo 1760081 2640875 := bstep (se 1 (by rfl) ⟨1980656, by rfl⟩ : syracuseStep 2640875 = 3961313) B3961313
theorem B2641079 : Blo 1760081 2641079 := bstep (se 1 (by rfl) ⟨1980809, by rfl⟩ : syracuseStep 2641079 = 3961619) B3961619
theorem B6687967 : Blo 1760081 6687967 := bstep (se 1 (by rfl) ⟨5015975, by rfl⟩ : syracuseStep 6687967 = 10031951) B10031951
theorem B12700901 : Blo 1760081 12700901 := bstep (se 4 (by rfl) ⟨1190709, by rfl⟩ : syracuseStep 12700901 = 2381419) B2381419
theorem B2641319 : Blo 1760081 2641319 := bstep (se 1 (by rfl) ⟨1980989, by rfl⟩ : syracuseStep 2641319 = 3961979) B3961979
theorem B3960233 : Blo 1760081 3960233 := bstep (se 2 (by rfl) ⟨1485087, by rfl⟩ : syracuseStep 3960233 = 2970175) B2970175
theorem B68603377 : Blo 1760081 68603377 := bstep (se 2 (by rfl) ⟨25726266, by rfl⟩ : syracuseStep 68603377 = 51452533) B51452533
theorem B3173879 : Blo 1760081 3173879 := bstep (se 1 (by rfl) ⟨2380409, by rfl⟩ : syracuseStep 3173879 = 4760819) B4760819
theorem B2641403 : Blo 1760081 2641403 := bstep (se 1 (by rfl) ⟨1981052, by rfl⟩ : syracuseStep 2641403 = 3962105) B3962105
theorem B9645601 : Blo 1760081 9645601 := bstep (se 2 (by rfl) ⟨3617100, by rfl⟩ : syracuseStep 9645601 = 7234201) B7234201
theorem B10030675 : Blo 1760081 10030675 := bstep (se 1 (by rfl) ⟨7523006, by rfl⟩ : syracuseStep 10030675 = 15046013) B15046013
theorem B2641499 : Blo 1760081 2641499 := bstep (se 1 (by rfl) ⟨1981124, by rfl⟩ : syracuseStep 2641499 = 3962249) B3962249
theorem B2641583 : Blo 1760081 2641583 := bstep (se 1 (by rfl) ⟨1981187, by rfl⟩ : syracuseStep 2641583 = 3962375) B3962375
theorem B6434479 : Blo 1760081 6434479 := bstep (se 1 (by rfl) ⟨4825859, by rfl⟩ : syracuseStep 6434479 = 9651719) B9651719
theorem B2821807 : Blo 1760081 2821807 := bstep (se 1 (by rfl) ⟨2116355, by rfl⟩ : syracuseStep 2821807 = 4232711) B4232711
theorem B2641703 : Blo 1760081 2641703 := bstep (se 1 (by rfl) ⟨1981277, by rfl⟩ : syracuseStep 2641703 = 3962555) B3962555
theorem B13373261 : Blo 1760081 13373261 := bstep (se 3 (by rfl) ⟨2507486, by rfl⟩ : syracuseStep 13373261 = 5014973) B5014973
theorem B2641787 : Blo 1760081 2641787 := bstep (se 1 (by rfl) ⟨1981340, by rfl⟩ : syracuseStep 2641787 = 3962681) B3962681
theorem B3960719 : Blo 1760081 3960719 := bstep (se 1 (by rfl) ⟨2970539, by rfl⟩ : syracuseStep 3960719 = 5941079) B5941079
theorem B7139279 : Blo 1760081 7139279 := bstep (se 1 (by rfl) ⟨5354459, by rfl⟩ : syracuseStep 7139279 = 10708919) B10708919
theorem B8466383 : Blo 1760081 8466383 := bstep (se 1 (by rfl) ⟨6349787, by rfl⟩ : syracuseStep 8466383 = 12699575) B12699575
theorem B2642207 : Blo 1760081 2642207 := bstep (se 1 (by rfl) ⟨1981655, by rfl⟩ : syracuseStep 2642207 = 3963311) B3963311
theorem B2642231 : Blo 1760081 2642231 := bstep (se 1 (by rfl) ⟨1981673, by rfl⟩ : syracuseStep 2642231 = 3963347) B3963347
theorem B2822455 : Blo 1760081 2822455 := bstep (se 1 (by rfl) ⟨2116841, by rfl⟩ : syracuseStep 2822455 = 4233683) B4233683
theorem B2642303 : Blo 1760081 2642303 := bstep (se 1 (by rfl) ⟨1981727, by rfl⟩ : syracuseStep 2642303 = 3963455) B3963455
theorem B2642375 : Blo 1760081 2642375 := bstep (se 1 (by rfl) ⟨1981781, by rfl⟩ : syracuseStep 2642375 = 3963563) B3963563
theorem B6345175 : Blo 1760081 6345175 := bstep (se 1 (by rfl) ⟨4758881, by rfl⟩ : syracuseStep 6345175 = 9517763) B9517763
theorem B5943887 : Blo 1760081 5943887 := bstep (se 1 (by rfl) ⟨4457915, by rfl⟩ : syracuseStep 5943887 = 8915831) B8915831
theorem B3961439 : Blo 1760081 3961439 := bstep (se 1 (by rfl) ⟨2971079, by rfl⟩ : syracuseStep 3961439 = 5942159) B5942159
theorem B2642729 : Blo 1760081 2642729 := bstep (se 2 (by rfl) ⟨991023, by rfl⟩ : syracuseStep 2642729 = 1982047) B1982047
theorem B2642735 : Blo 1760081 2642735 := bstep (se 1 (by rfl) ⟨1982051, by rfl⟩ : syracuseStep 2642735 = 3964103) B3964103
theorem B2970425 : Blo 1760081 2970425 := bstep (se 2 (by rfl) ⟨1113909, by rfl⟩ : syracuseStep 2970425 = 2227819) B2227819
theorem B2970479 : Blo 1760081 2970479 := bstep (se 1 (by rfl) ⟨2227859, by rfl⟩ : syracuseStep 2970479 = 4455719) B4455719
theorem B2642855 : Blo 1760081 2642855 := bstep (se 1 (by rfl) ⟨1982141, by rfl⟩ : syracuseStep 2642855 = 3964283) B3964283
theorem B2642939 : Blo 1760081 2642939 := bstep (se 1 (by rfl) ⟨1982204, by rfl⟩ : syracuseStep 2642939 = 3964409) B3964409
theorem B2642999 : Blo 1760081 2642999 := bstep (se 1 (by rfl) ⟨1982249, by rfl⟩ : syracuseStep 2642999 = 3964499) B3964499
theorem B5944427 : Blo 1760081 5944427 := bstep (se 1 (by rfl) ⟨4458320, by rfl⟩ : syracuseStep 5944427 = 8916641) B8916641
theorem B2643119 : Blo 1760081 2643119 := bstep (se 1 (by rfl) ⟨1982339, by rfl⟩ : syracuseStep 2643119 = 3964679) B3964679
theorem B5641435 : Blo 1760081 5641435 := bstep (se 1 (by rfl) ⟨4231076, by rfl⟩ : syracuseStep 5641435 = 8462153) B8462153
theorem B5084435 : Blo 1760081 5084435 := bstep (se 1 (by rfl) ⟨3813326, by rfl⟩ : syracuseStep 5084435 = 7626653) B7626653
theorem B5354849 : Blo 1760081 5354849 := bstep (se 2 (by rfl) ⟨2008068, by rfl⟩ : syracuseStep 5354849 = 4016137) B4016137
theorem B20329883 : Blo 1760081 20329883 := bstep (se 1 (by rfl) ⟨15247412, by rfl⟩ : syracuseStep 20329883 = 30494825) B30494825
theorem B3962267 : Blo 1760081 3962267 := bstep (se 1 (by rfl) ⟨2971700, by rfl⟩ : syracuseStep 3962267 = 5943401) B5943401
theorem B48199211 : Blo 1760081 48199211 := bstep (se 1 (by rfl) ⟨36149408, by rfl⟩ : syracuseStep 48199211 = 72298817) B72298817
theorem B51484349 : Blo 1760081 51484349 := bstep (se 3 (by rfl) ⟨9653315, by rfl⟩ : syracuseStep 51484349 = 19306631) B19306631
theorem B6027065 : Blo 1760081 6027065 := bstep (se 2 (by rfl) ⟨2260149, by rfl⟩ : syracuseStep 6027065 = 4520299) B4520299
theorem B2971471 : Blo 1760081 2971471 := bstep (se 1 (by rfl) ⟨2228603, by rfl⟩ : syracuseStep 2971471 = 4457207) B4457207
theorem B3962843 : Blo 1760081 3962843 := bstep (se 1 (by rfl) ⟨2972132, by rfl⟩ : syracuseStep 3962843 = 5944265) B5944265
theorem B22566923 : Blo 1760081 22566923 := bstep (se 1 (by rfl) ⟨16925192, by rfl⟩ : syracuseStep 22566923 = 33850385) B33850385
theorem B33847379 : Blo 1760081 33847379 := bstep (se 1 (by rfl) ⟨25385534, by rfl⟩ : syracuseStep 33847379 = 50771069) B50771069
theorem B6346835 : Blo 1760081 6346835 := bstep (se 1 (by rfl) ⟨4760126, by rfl⟩ : syracuseStep 6346835 = 9520253) B9520253
theorem B3963023 : Blo 1760081 3963023 := bstep (se 1 (by rfl) ⟨2972267, by rfl⟩ : syracuseStep 3963023 = 5944535) B5944535
theorem B1980571 : Blo 1760081 1980571 := bstep (se 1 (by rfl) ⟨1485428, by rfl⟩ : syracuseStep 1980571 = 2970857) B2970857
theorem B3963041 : Blo 1760081 3963041 := bstep (se 2 (by rfl) ⟨1486140, by rfl⟩ : syracuseStep 3963041 = 2972281) B2972281
theorem B1980607 : Blo 1760081 1980607 := bstep (se 1 (by rfl) ⟨1485455, by rfl⟩ : syracuseStep 1980607 = 2970911) B2970911
theorem B13375691 : Blo 1760081 13375691 := bstep (se 1 (by rfl) ⟨10031768, by rfl⟩ : syracuseStep 13375691 = 20063537) B20063537
theorem B3963113 : Blo 1760081 3963113 := bstep (se 2 (by rfl) ⟨1486167, by rfl⟩ : syracuseStep 3963113 = 2972335) B2972335
theorem B2971883 : Blo 1760081 2971883 := bstep (se 1 (by rfl) ⟨2228912, by rfl⟩ : syracuseStep 2971883 = 4457825) B4457825
theorem B5945723 : Blo 1760081 5945723 := bstep (se 1 (by rfl) ⟨4459292, by rfl⟩ : syracuseStep 5945723 = 8918585) B8918585
theorem B6027709 : Blo 1760081 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B5945993 : Blo 1760081 5945993 := bstep (se 2 (by rfl) ⟨2229747, by rfl⟩ : syracuseStep 5945993 = 4459495) B4459495
theorem B1760091 : Blo 1760081 1760091 := bstep (se 1 (by rfl) ⟨1320068, by rfl⟩ : syracuseStep 1760091 = 2640137) B2640137
theorem B33864601 : Blo 1760081 33864601 := bstep (se 2 (by rfl) ⟨12699225, by rfl⟩ : syracuseStep 33864601 = 25398451) B25398451
theorem B1760159 : Blo 1760081 1760159 := bstep (se 1 (by rfl) ⟨1320119, by rfl⟩ : syracuseStep 1760159 = 2640239) B2640239
theorem B16284637 : Blo 1760081 16284637 := bstep (se 3 (by rfl) ⟨3053369, by rfl⟩ : syracuseStep 16284637 = 6106739) B6106739
theorem B2972713 : Blo 1760081 2972713 := bstep (se 2 (by rfl) ⟨1114767, by rfl⟩ : syracuseStep 2972713 = 2229535) B2229535
theorem B1760303 : Blo 1760081 1760303 := bstep (se 1 (by rfl) ⟨1320227, by rfl⟩ : syracuseStep 1760303 = 2640455) B2640455
theorem B1760327 : Blo 1760081 1760327 := bstep (se 1 (by rfl) ⟨1320245, by rfl⟩ : syracuseStep 1760327 = 2640491) B2640491
theorem B8911943 : Blo 1760081 8911943 := bstep (se 1 (by rfl) ⟨6683957, by rfl⟩ : syracuseStep 8911943 = 13367915) B13367915
theorem B4455607 : Blo 1760081 4455607 := bstep (se 1 (by rfl) ⟨3341705, by rfl⟩ : syracuseStep 4455607 = 6683411) B6683411
theorem B2972855 : Blo 1760081 2972855 := bstep (se 1 (by rfl) ⟨2229641, by rfl⟩ : syracuseStep 2972855 = 4459283) B4459283
theorem B5012695 : Blo 1760081 5012695 := bstep (se 1 (by rfl) ⟨3759521, by rfl⟩ : syracuseStep 5012695 = 7519043) B7519043
theorem B1760479 : Blo 1760081 1760479 := bstep (se 1 (by rfl) ⟨1320359, by rfl⟩ : syracuseStep 1760479 = 2640719) B2640719
theorem B6683897 : Blo 1760081 6683897 := bstep (se 2 (by rfl) ⟨2506461, by rfl⟩ : syracuseStep 6683897 = 5012923) B5012923
theorem B11918593 : Blo 1760081 11918593 := bstep (se 2 (by rfl) ⟨4469472, by rfl⟩ : syracuseStep 11918593 = 8938945) B8938945
theorem B36150563 : Blo 1760081 36150563 := bstep (se 1 (by rfl) ⟨27112922, by rfl⟩ : syracuseStep 36150563 = 54225845) B54225845
theorem B5717287 : Blo 1760081 5717287 := bstep (se 1 (by rfl) ⟨4287965, by rfl⟩ : syracuseStep 5717287 = 8575931) B8575931
theorem B15039863 : Blo 1760081 15039863 := bstep (se 1 (by rfl) ⟨11279897, by rfl⟩ : syracuseStep 15039863 = 22559795) B22559795
theorem B9649637 : Blo 1760081 9649637 := bstep (se 4 (by rfl) ⟨904653, by rfl⟩ : syracuseStep 9649637 = 1809307) B1809307
theorem B4455911 : Blo 1760081 4455911 := bstep (se 1 (by rfl) ⟨3341933, by rfl⟩ : syracuseStep 4455911 = 6683867) B6683867
theorem B1760743 : Blo 1760081 1760743 := bstep (se 1 (by rfl) ⟨1320557, by rfl⟩ : syracuseStep 1760743 = 2641115) B2641115
theorem B3964391 : Blo 1760081 3964391 := bstep (se 1 (by rfl) ⟨2973293, by rfl⟩ : syracuseStep 3964391 = 5946587) B5946587
theorem B2973179 : Blo 1760081 2973179 := bstep (se 1 (by rfl) ⟨2229884, by rfl⟩ : syracuseStep 2973179 = 4459769) B4459769
theorem B5013083 : Blo 1760081 5013083 := bstep (se 1 (by rfl) ⟨3759812, by rfl⟩ : syracuseStep 5013083 = 7519625) B7519625
theorem B1760859 : Blo 1760081 1760859 := bstep (se 1 (by rfl) ⟨1320644, by rfl⟩ : syracuseStep 1760859 = 2641289) B2641289
theorem B4759183 : Blo 1760081 4759183 := bstep (se 1 (by rfl) ⟨3569387, by rfl⟩ : syracuseStep 4759183 = 7138775) B7138775
theorem B3759863 : Blo 1760081 3759863 := bstep (se 1 (by rfl) ⟨2819897, by rfl⟩ : syracuseStep 3759863 = 5639795) B5639795
theorem B1761095 : Blo 1760081 1761095 := bstep (se 1 (by rfl) ⟨1320821, by rfl⟩ : syracuseStep 1761095 = 2641643) B2641643
theorem B14278589 : Blo 1760081 14278589 := bstep (se 3 (by rfl) ⟨2677235, by rfl⟩ : syracuseStep 14278589 = 5354471) B5354471
theorem B1761247 : Blo 1760081 1761247 := bstep (se 1 (by rfl) ⟨1320935, by rfl⟩ : syracuseStep 1761247 = 2641871) B2641871
theorem B1761471 : Blo 1760081 1761471 := bstep (se 1 (by rfl) ⟨1321103, by rfl⟩ : syracuseStep 1761471 = 2642207) B2642207
theorem B1761487 : Blo 1760081 1761487 := bstep (se 1 (by rfl) ⟨1321115, by rfl⟩ : syracuseStep 1761487 = 2642231) B2642231
theorem B1761535 : Blo 1760081 1761535 := bstep (se 1 (by rfl) ⟨1321151, by rfl⟩ : syracuseStep 1761535 = 2642303) B2642303
theorem B1761583 : Blo 1760081 1761583 := bstep (se 1 (by rfl) ⟨1321187, by rfl⟩ : syracuseStep 1761583 = 2642375) B2642375
theorem B7725473 : Blo 1760081 7725473 := bstep (se 2 (by rfl) ⟨2897052, by rfl⟩ : syracuseStep 7725473 = 5794105) B5794105
theorem B1761819 : Blo 1760081 1761819 := bstep (se 1 (by rfl) ⟨1321364, by rfl⟩ : syracuseStep 1761819 = 2642729) B2642729
theorem B1761823 : Blo 1760081 1761823 := bstep (se 1 (by rfl) ⟨1321367, by rfl⟩ : syracuseStep 1761823 = 2642735) B2642735
theorem B8036945 : Blo 1760081 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B4457065 : Blo 1760081 4457065 := bstep (se 2 (by rfl) ⟨1671399, by rfl⟩ : syracuseStep 4457065 = 3342799) B3342799
theorem B1761903 : Blo 1760081 1761903 := bstep (se 1 (by rfl) ⟨1321427, by rfl⟩ : syracuseStep 1761903 = 2642855) B2642855
theorem B30106241 : Blo 1760081 30106241 := bstep (se 2 (by rfl) ⟨11289840, by rfl⟩ : syracuseStep 30106241 = 22579681) B22579681
theorem B1761959 : Blo 1760081 1761959 := bstep (se 1 (by rfl) ⟨1321469, by rfl⟩ : syracuseStep 1761959 = 2642939) B2642939
theorem B7520957 : Blo 1760081 7520957 := bstep (se 3 (by rfl) ⟨1410179, by rfl⟩ : syracuseStep 7520957 = 2820359) B2820359
theorem B1761999 : Blo 1760081 1761999 := bstep (se 1 (by rfl) ⟨1321499, by rfl⟩ : syracuseStep 1761999 = 2642999) B2642999
theorem B13558493 : Blo 1760081 13558493 := bstep (se 3 (by rfl) ⟨2542217, by rfl⟩ : syracuseStep 13558493 = 5084435) B5084435
theorem B1762079 : Blo 1760081 1762079 := bstep (se 1 (by rfl) ⟨1321559, by rfl⟩ : syracuseStep 1762079 = 2643119) B2643119
theorem B99091277 : Blo 1760081 99091277 := bstep (se 3 (by rfl) ⟨18579614, by rfl⟩ : syracuseStep 99091277 = 37159229) B37159229
theorem B15049637 : Blo 1760081 15049637 := bstep (se 4 (by rfl) ⟨1410903, by rfl⟩ : syracuseStep 15049637 = 2821807) B2821807
theorem B14279597 : Blo 1760081 14279597 := bstep (se 3 (by rfl) ⟨2677424, by rfl⟩ : syracuseStep 14279597 = 5354849) B5354849
theorem B2229439 : Blo 1760081 2229439 := bstep (se 1 (by rfl) ⟨1672079, by rfl⟩ : syracuseStep 2229439 = 3344159) B3344159
theorem B2508079 : Blo 1760081 2508079 := bstep (se 1 (by rfl) ⟨1881059, by rfl⟩ : syracuseStep 2508079 = 3762119) B3762119
theorem B6022457 : Blo 1760081 6022457 := bstep (se 2 (by rfl) ⟨2258421, by rfl⟩ : syracuseStep 6022457 = 4516843) B4516843
theorem B30492197 : Blo 1760081 30492197 := bstep (se 4 (by rfl) ⟨2858643, by rfl⟩ : syracuseStep 30492197 = 5717287) B5717287
theorem B5940809 : Blo 1760081 5940809 := bstep (se 2 (by rfl) ⟨2227803, by rfl⟩ : syracuseStep 5940809 = 4455607) B4455607
theorem B7521913 : Blo 1760081 7521913 := bstep (se 2 (by rfl) ⟨2820717, by rfl⟩ : syracuseStep 7521913 = 5641435) B5641435
theorem B5941295 : Blo 1760081 5941295 := bstep (se 1 (by rfl) ⟨4455971, by rfl⟩ : syracuseStep 5941295 = 8911943) B8911943
theorem B8579305 : Blo 1760081 8579305 := bstep (se 2 (by rfl) ⟨3217239, by rfl⟩ : syracuseStep 8579305 = 6434479) B6434479
theorem B2640155 : Blo 1760081 2640155 := bstep (se 1 (by rfl) ⟨1980116, by rfl⟩ : syracuseStep 2640155 = 3960233) B3960233
theorem B6433091 : Blo 1760081 6433091 := bstep (se 1 (by rfl) ⟨4824818, by rfl⟩ : syracuseStep 6433091 = 9649637) B9649637
theorem B2115919 : Blo 1760081 2115919 := bstep (se 1 (by rfl) ⟨1586939, by rfl⟩ : syracuseStep 2115919 = 3173879) B3173879
theorem B16919077 : Blo 1760081 16919077 := bstep (se 4 (by rfl) ⟨1586163, by rfl⟩ : syracuseStep 16919077 = 3172327) B3172327
theorem B8915507 : Blo 1760081 8915507 := bstep (se 1 (by rfl) ⟨6686630, by rfl⟩ : syracuseStep 8915507 = 13373261) B13373261
theorem B2640479 : Blo 1760081 2640479 := bstep (se 1 (by rfl) ⟨1980359, by rfl⟩ : syracuseStep 2640479 = 3960719) B3960719
theorem B2640761 : Blo 1760081 2640761 := bstep (se 2 (by rfl) ⟨990285, by rfl⟩ : syracuseStep 2640761 = 1980571) B1980571
theorem B17165195 : Blo 1760081 17165195 := bstep (se 1 (by rfl) ⟨12873896, by rfl⟩ : syracuseStep 17165195 = 25747793) B25747793
theorem B2640809 : Blo 1760081 2640809 := bstep (se 2 (by rfl) ⟨990303, by rfl⟩ : syracuseStep 2640809 = 1980607) B1980607
theorem B2640959 : Blo 1760081 2640959 := bstep (se 1 (by rfl) ⟨1980719, by rfl⟩ : syracuseStep 2640959 = 3961439) B3961439
theorem B3763273 : Blo 1760081 3763273 := bstep (se 2 (by rfl) ⟨1411227, by rfl⟩ : syracuseStep 3763273 = 2822455) B2822455
theorem B10169543 : Blo 1760081 10169543 := bstep (se 1 (by rfl) ⟨7627157, by rfl⟩ : syracuseStep 10169543 = 15254315) B15254315
theorem B6687953 : Blo 1760081 6687953 := bstep (se 2 (by rfl) ⟨2507982, by rfl⟩ : syracuseStep 6687953 = 5015965) B5015965
theorem B5942537 : Blo 1760081 5942537 := bstep (se 2 (by rfl) ⟨2228451, by rfl⟩ : syracuseStep 5942537 = 4456903) B4456903
theorem B3960287 : Blo 1760081 3960287 := bstep (se 1 (by rfl) ⟨2970215, by rfl⟩ : syracuseStep 3960287 = 5940431) B5940431
theorem B13553255 : Blo 1760081 13553255 := bstep (se 1 (by rfl) ⟨10164941, by rfl⟩ : syracuseStep 13553255 = 20329883) B20329883
theorem B2641511 : Blo 1760081 2641511 := bstep (se 1 (by rfl) ⟨1981133, by rfl⟩ : syracuseStep 2641511 = 3962267) B3962267
theorem B3960503 : Blo 1760081 3960503 := bstep (se 1 (by rfl) ⟨2970377, by rfl⟩ : syracuseStep 3960503 = 5940755) B5940755
theorem B32132807 : Blo 1760081 32132807 := bstep (se 1 (by rfl) ⟨24099605, by rfl⟩ : syracuseStep 32132807 = 48199211) B48199211
theorem B5795579 : Blo 1760081 5795579 := bstep (se 1 (by rfl) ⟨4346684, by rfl⟩ : syracuseStep 5795579 = 8693369) B8693369
theorem B30093119 : Blo 1760081 30093119 := bstep (se 1 (by rfl) ⟨22569839, by rfl⟩ : syracuseStep 30093119 = 45139679) B45139679
theorem B4018043 : Blo 1760081 4018043 := bstep (se 1 (by rfl) ⟨3013532, by rfl⟩ : syracuseStep 4018043 = 6027065) B6027065
theorem B19304353 : Blo 1760081 19304353 := bstep (se 2 (by rfl) ⟨7239132, by rfl⟩ : syracuseStep 19304353 = 14478265) B14478265
theorem B2641895 : Blo 1760081 2641895 := bstep (se 1 (by rfl) ⟨1981421, by rfl⟩ : syracuseStep 2641895 = 3962843) B3962843
theorem B42840049 : Blo 1760081 42840049 := bstep (se 2 (by rfl) ⟨16065018, by rfl⟩ : syracuseStep 42840049 = 32130037) B32130037
theorem B63565829 : Blo 1760081 63565829 := bstep (se 4 (by rfl) ⟨5959296, by rfl⟩ : syracuseStep 63565829 = 11918593) B11918593
theorem B15044615 : Blo 1760081 15044615 := bstep (se 1 (by rfl) ⟨11283461, by rfl⟩ : syracuseStep 15044615 = 22566923) B22566923
theorem B22564919 : Blo 1760081 22564919 := bstep (se 1 (by rfl) ⟨16923689, by rfl⟩ : syracuseStep 22564919 = 33847379) B33847379
theorem B4231223 : Blo 1760081 4231223 := bstep (se 1 (by rfl) ⟨3173417, by rfl⟩ : syracuseStep 4231223 = 6346835) B6346835
theorem B2642015 : Blo 1760081 2642015 := bstep (se 1 (by rfl) ⟨1981511, by rfl⟩ : syracuseStep 2642015 = 3963023) B3963023
theorem B1880167 : Blo 1760081 1880167 := bstep (se 1 (by rfl) ⟨1410125, by rfl⟩ : syracuseStep 1880167 = 2820251) B2820251
theorem B2642027 : Blo 1760081 2642027 := bstep (se 1 (by rfl) ⟨1981520, by rfl⟩ : syracuseStep 2642027 = 3963041) B3963041
theorem B8917127 : Blo 1760081 8917127 := bstep (se 1 (by rfl) ⟨6687845, by rfl⟩ : syracuseStep 8917127 = 13375691) B13375691
theorem B2642075 : Blo 1760081 2642075 := bstep (se 1 (by rfl) ⟨1981556, by rfl⟩ : syracuseStep 2642075 = 3963113) B3963113
theorem B8917289 : Blo 1760081 8917289 := bstep (se 2 (by rfl) ⟨3343983, by rfl⟩ : syracuseStep 8917289 = 6687967) B6687967
theorem B6689213 : Blo 1760081 6689213 := bstep (se 3 (by rfl) ⟨1254227, by rfl⟩ : syracuseStep 6689213 = 2508455) B2508455
theorem B3961295 : Blo 1760081 3961295 := bstep (se 1 (by rfl) ⟨2970971, by rfl⟩ : syracuseStep 3961295 = 5941943) B5941943
theorem B13374233 : Blo 1760081 13374233 := bstep (se 2 (by rfl) ⟨5015337, by rfl⟩ : syracuseStep 13374233 = 10030675) B10030675
theorem B8467267 : Blo 1760081 8467267 := bstep (se 1 (by rfl) ⟨6350450, by rfl⟩ : syracuseStep 8467267 = 12700901) B12700901
theorem B6345577 : Blo 1760081 6345577 := bstep (se 2 (by rfl) ⟨2379591, by rfl⟩ : syracuseStep 6345577 = 4759183) B4759183
theorem B2970607 : Blo 1760081 2970607 := bstep (se 1 (by rfl) ⟨2227955, by rfl⟩ : syracuseStep 2970607 = 4455911) B4455911
theorem B2642927 : Blo 1760081 2642927 := bstep (se 1 (by rfl) ⟨1982195, by rfl⟩ : syracuseStep 2642927 = 3964391) B3964391
theorem B11285513 : Blo 1760081 11285513 := bstep (se 2 (by rfl) ⟨4232067, by rfl⟩ : syracuseStep 11285513 = 8464135) B8464135
theorem B3961961 : Blo 1760081 3961961 := bstep (se 2 (by rfl) ⟨1485735, by rfl⟩ : syracuseStep 3961961 = 2971471) B2971471
theorem B6690383 : Blo 1760081 6690383 := bstep (se 1 (by rfl) ⟨5017787, by rfl⟩ : syracuseStep 6690383 = 10035575) B10035575
theorem B8918747 : Blo 1760081 8918747 := bstep (se 1 (by rfl) ⟨6689060, by rfl⟩ : syracuseStep 8918747 = 13378121) B13378121
theorem B3962591 : Blo 1760081 3962591 := bstep (se 1 (by rfl) ⟨2971943, by rfl⟩ : syracuseStep 3962591 = 5943887) B5943887
theorem B5945129 : Blo 1760081 5945129 := bstep (se 2 (by rfl) ⟨2229423, by rfl⟩ : syracuseStep 5945129 = 4458847) B4458847
theorem B1980283 : Blo 1760081 1980283 := bstep (se 1 (by rfl) ⟨1485212, by rfl⟩ : syracuseStep 1980283 = 2970425) B2970425
theorem B1980319 : Blo 1760081 1980319 := bstep (se 1 (by rfl) ⟨1485239, by rfl⟩ : syracuseStep 1980319 = 2970479) B2970479
theorem B8460233 : Blo 1760081 8460233 := bstep (se 2 (by rfl) ⟨3172587, by rfl⟩ : syracuseStep 8460233 = 6345175) B6345175
theorem B3962951 : Blo 1760081 3962951 := bstep (se 1 (by rfl) ⟨2972213, by rfl⟩ : syracuseStep 3962951 = 5944427) B5944427
theorem B5642615 : Blo 1760081 5642615 := bstep (se 1 (by rfl) ⟨4231961, by rfl⟩ : syracuseStep 5642615 = 8463923) B8463923
theorem B34322899 : Blo 1760081 34322899 := bstep (se 1 (by rfl) ⟨25742174, by rfl⟩ : syracuseStep 34322899 = 51484349) B51484349
theorem B45152801 : Blo 1760081 45152801 := bstep (se 2 (by rfl) ⟨16932300, by rfl⟩ : syracuseStep 45152801 = 33864601) B33864601
theorem B3963617 : Blo 1760081 3963617 := bstep (se 2 (by rfl) ⟨1486356, by rfl⟩ : syracuseStep 3963617 = 2972713) B2972713
theorem B1981255 : Blo 1760081 1981255 := bstep (se 1 (by rfl) ⟨1485941, by rfl⟩ : syracuseStep 1981255 = 2971883) B2971883
theorem B1760111 : Blo 1760081 1760111 := bstep (se 1 (by rfl) ⟨1320083, by rfl⟩ : syracuseStep 1760111 = 2640167) B2640167
theorem B1760167 : Blo 1760081 1760167 := bstep (se 1 (by rfl) ⟨1320125, by rfl⟩ : syracuseStep 1760167 = 2640251) B2640251
theorem B3963815 : Blo 1760081 3963815 := bstep (se 1 (by rfl) ⟨2972861, by rfl⟩ : syracuseStep 3963815 = 5945723) B5945723
theorem B6683593 : Blo 1760081 6683593 := bstep (se 2 (by rfl) ⟨2506347, by rfl⟩ : syracuseStep 6683593 = 5012695) B5012695
theorem B1760347 : Blo 1760081 1760347 := bstep (se 1 (by rfl) ⟨1320260, by rfl⟩ : syracuseStep 1760347 = 2640521) B2640521
theorem B3963995 : Blo 1760081 3963995 := bstep (se 1 (by rfl) ⟨2972996, by rfl⟩ : syracuseStep 3963995 = 5945993) B5945993
theorem B1760463 : Blo 1760081 1760463 := bstep (se 1 (by rfl) ⟨1320347, by rfl⟩ : syracuseStep 1760463 = 2640695) B2640695
theorem B1760487 : Blo 1760081 1760487 := bstep (se 1 (by rfl) ⟨1320365, by rfl⟩ : syracuseStep 1760487 = 2640731) B2640731
theorem B10026301 : Blo 1760081 10026301 := bstep (se 3 (by rfl) ⟨1879931, by rfl⟩ : syracuseStep 10026301 = 3759863) B3759863
theorem B91471169 : Blo 1760081 91471169 := bstep (se 2 (by rfl) ⟨34301688, by rfl⟩ : syracuseStep 91471169 = 68603377) B68603377
theorem B1760583 : Blo 1760081 1760583 := bstep (se 1 (by rfl) ⟨1320437, by rfl⟩ : syracuseStep 1760583 = 2640875) B2640875
theorem B12860801 : Blo 1760081 12860801 := bstep (se 2 (by rfl) ⟨4822800, by rfl⟩ : syracuseStep 12860801 = 9645601) B9645601
theorem B1760719 : Blo 1760081 1760719 := bstep (se 1 (by rfl) ⟨1320539, by rfl⟩ : syracuseStep 1760719 = 2641079) B2641079
theorem B1981903 : Blo 1760081 1981903 := bstep (se 1 (by rfl) ⟨1486427, by rfl⟩ : syracuseStep 1981903 = 2972855) B2972855
theorem B4455931 : Blo 1760081 4455931 := bstep (se 1 (by rfl) ⟨3341948, by rfl⟩ : syracuseStep 4455931 = 6683897) B6683897
theorem B24100375 : Blo 1760081 24100375 := bstep (se 1 (by rfl) ⟨18075281, by rfl⟩ : syracuseStep 24100375 = 36150563) B36150563
theorem B10026575 : Blo 1760081 10026575 := bstep (se 1 (by rfl) ⟨7519931, by rfl⟩ : syracuseStep 10026575 = 15039863) B15039863
theorem B1760879 : Blo 1760081 1760879 := bstep (se 1 (by rfl) ⟨1320659, by rfl⟩ : syracuseStep 1760879 = 2641319) B2641319
theorem B1760935 : Blo 1760081 1760935 := bstep (se 1 (by rfl) ⟨1320701, by rfl⟩ : syracuseStep 1760935 = 2641403) B2641403
theorem B1982119 : Blo 1760081 1982119 := bstep (se 1 (by rfl) ⟨1486589, by rfl⟩ : syracuseStep 1982119 = 2973179) B2973179
theorem B3342055 : Blo 1760081 3342055 := bstep (se 1 (by rfl) ⟨2506541, by rfl⟩ : syracuseStep 3342055 = 5013083) B5013083
theorem B1760999 : Blo 1760081 1760999 := bstep (se 1 (by rfl) ⟨1320749, by rfl⟩ : syracuseStep 1760999 = 2641499) B2641499
theorem B1761055 : Blo 1760081 1761055 := bstep (se 1 (by rfl) ⟨1320791, by rfl⟩ : syracuseStep 1761055 = 2641583) B2641583
theorem B86851397 : Blo 1760081 86851397 := bstep (se 4 (by rfl) ⟨8142318, by rfl⟩ : syracuseStep 86851397 = 16284637) B16284637
theorem B1761135 : Blo 1760081 1761135 := bstep (se 1 (by rfl) ⟨1320851, by rfl⟩ : syracuseStep 1761135 = 2641703) B2641703
theorem B19038077 : Blo 1760081 19038077 := bstep (se 3 (by rfl) ⟨3569639, by rfl⟩ : syracuseStep 19038077 = 7139279) B7139279
theorem B1761191 : Blo 1760081 1761191 := bstep (se 1 (by rfl) ⟨1320893, by rfl⟩ : syracuseStep 1761191 = 2641787) B2641787
theorem B9519059 : Blo 1760081 9519059 := bstep (se 1 (by rfl) ⟨7139294, by rfl⟩ : syracuseStep 9519059 = 14278589) B14278589
theorem B5644255 : Blo 1760081 5644255 := bstep (se 1 (by rfl) ⟨4233191, by rfl⟩ : syracuseStep 5644255 = 8466383) B8466383
theorem B42377219 : Blo 1760081 42377219 := bstep (se 1 (by rfl) ⟨31782914, by rfl⟩ : syracuseStep 42377219 = 63565829) B63565829
theorem B1761343 : Blo 1760081 1761343 := bstep (se 1 (by rfl) ⟨1321007, by rfl⟩ : syracuseStep 1761343 = 2642015) B2642015
theorem B1761351 : Blo 1760081 1761351 := bstep (se 1 (by rfl) ⟨1321013, by rfl⟩ : syracuseStep 1761351 = 2642027) B2642027
theorem B1761383 : Blo 1760081 1761383 := bstep (se 1 (by rfl) ⟨1321037, by rfl⟩ : syracuseStep 1761383 = 2642075) B2642075
theorem B2506889 : Blo 1760081 2506889 := bstep (se 2 (by rfl) ⟨940083, by rfl⟩ : syracuseStep 2506889 = 1880167) B1880167
theorem B5357963 : Blo 1760081 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B20070827 : Blo 1760081 20070827 := bstep (se 1 (by rfl) ⟨15053120, by rfl⟩ : syracuseStep 20070827 = 30106241) B30106241
theorem B5013971 : Blo 1760081 5013971 := bstep (se 1 (by rfl) ⟨3760478, by rfl⟩ : syracuseStep 5013971 = 7520957) B7520957
theorem B66060851 : Blo 1760081 66060851 := bstep (se 1 (by rfl) ⟨49545638, by rfl⟩ : syracuseStep 66060851 = 99091277) B99091277
theorem B9519731 : Blo 1760081 9519731 := bstep (se 1 (by rfl) ⟨7139798, by rfl⟩ : syracuseStep 9519731 = 14279597) B14279597
theorem B1761951 : Blo 1760081 1761951 := bstep (se 1 (by rfl) ⟨1321463, by rfl⟩ : syracuseStep 1761951 = 2642927) B2642927
theorem B4014971 : Blo 1760081 4014971 := bstep (se 1 (by rfl) ⟨3011228, by rfl⟩ : syracuseStep 4014971 = 6022457) B6022457
theorem B11289689 : Blo 1760081 11289689 := bstep (se 2 (by rfl) ⟨4233633, by rfl⟩ : syracuseStep 11289689 = 8467267) B8467267
theorem B3761743 : Blo 1760081 3761743 := bstep (se 1 (by rfl) ⟨2821307, by rfl⟩ : syracuseStep 3761743 = 5642615) B5642615
theorem B3344105 : Blo 1760081 3344105 := bstep (se 2 (by rfl) ⟨1254039, by rfl⟩ : syracuseStep 3344105 = 2508079) B2508079
theorem B5941241 : Blo 1760081 5941241 := bstep (se 2 (by rfl) ⟨2227965, by rfl⟩ : syracuseStep 5941241 = 4455931) B4455931
theorem B4458635 : Blo 1760081 4458635 := bstep (se 1 (by rfl) ⟨3343976, by rfl⟩ : syracuseStep 4458635 = 6687953) B6687953
theorem B10029217 : Blo 1760081 10029217 := bstep (se 2 (by rfl) ⟨3760956, by rfl⟩ : syracuseStep 10029217 = 7521913) B7521913
theorem B2640191 : Blo 1760081 2640191 := bstep (se 1 (by rfl) ⟨1980143, by rfl⟩ : syracuseStep 2640191 = 3960287) B3960287
theorem B2640335 : Blo 1760081 2640335 := bstep (se 1 (by rfl) ⟨1980251, by rfl⟩ : syracuseStep 2640335 = 3960503) B3960503
theorem B2640377 : Blo 1760081 2640377 := bstep (se 2 (by rfl) ⟨990141, by rfl⟩ : syracuseStep 2640377 = 1980283) B1980283
theorem B2640425 : Blo 1760081 2640425 := bstep (se 2 (by rfl) ⟨990159, by rfl⟩ : syracuseStep 2640425 = 1980319) B1980319
theorem B12692051 : Blo 1760081 12692051 := bstep (se 1 (by rfl) ⟨9519038, by rfl⟩ : syracuseStep 12692051 = 19038077) B19038077
theorem B10029743 : Blo 1760081 10029743 := bstep (se 1 (by rfl) ⟨7522307, by rfl⟩ : syracuseStep 10029743 = 15044615) B15044615
theorem B15043279 : Blo 1760081 15043279 := bstep (se 1 (by rfl) ⟨11282459, by rfl⟩ : syracuseStep 15043279 = 22564919) B22564919
theorem B2820815 : Blo 1760081 2820815 := bstep (se 1 (by rfl) ⟨2115611, by rfl⟩ : syracuseStep 2820815 = 4231223) B4231223
theorem B4459475 : Blo 1760081 4459475 := bstep (se 1 (by rfl) ⟨3344606, by rfl⟩ : syracuseStep 4459475 = 6689213) B6689213
theorem B2640863 : Blo 1760081 2640863 := bstep (se 1 (by rfl) ⟨1980647, by rfl⟩ : syracuseStep 2640863 = 3961295) B3961295
theorem B11439073 : Blo 1760081 11439073 := bstep (se 2 (by rfl) ⟨4289652, by rfl⟩ : syracuseStep 11439073 = 8579305) B8579305
theorem B2821225 : Blo 1760081 2821225 := bstep (se 2 (by rfl) ⟨1057959, by rfl⟩ : syracuseStep 2821225 = 2115919) B2115919
theorem B9038995 : Blo 1760081 9038995 := bstep (se 1 (by rfl) ⟨6779246, by rfl⟩ : syracuseStep 9038995 = 13558493) B13558493
theorem B8916155 : Blo 1760081 8916155 := bstep (se 1 (by rfl) ⟨6687116, by rfl⟩ : syracuseStep 8916155 = 13374233) B13374233
theorem B45763865 : Blo 1760081 45763865 := bstep (se 2 (by rfl) ⟨17161449, by rfl⟩ : syracuseStep 45763865 = 34322899) B34322899
theorem B7523675 : Blo 1760081 7523675 := bstep (se 1 (by rfl) ⟨5642756, by rfl⟩ : syracuseStep 7523675 = 11285513) B11285513
theorem B2641307 : Blo 1760081 2641307 := bstep (se 1 (by rfl) ⟨1980980, by rfl⟩ : syracuseStep 2641307 = 3961961) B3961961
theorem B5942753 : Blo 1760081 5942753 := bstep (se 2 (by rfl) ⟨2228532, by rfl⟩ : syracuseStep 5942753 = 4457065) B4457065
theorem B20328131 : Blo 1760081 20328131 := bstep (se 1 (by rfl) ⟨15246098, by rfl⟩ : syracuseStep 20328131 = 30492197) B30492197
theorem B3960539 : Blo 1760081 3960539 := bstep (se 1 (by rfl) ⟨2970404, by rfl⟩ : syracuseStep 3960539 = 5940809) B5940809
theorem B4460255 : Blo 1760081 4460255 := bstep (se 1 (by rfl) ⟨3345191, by rfl⟩ : syracuseStep 4460255 = 6690383) B6690383
theorem B2641673 : Blo 1760081 2641673 := bstep (se 2 (by rfl) ⟨990627, by rfl⟩ : syracuseStep 2641673 = 1981255) B1981255
theorem B2641727 : Blo 1760081 2641727 := bstep (se 1 (by rfl) ⟨1981295, by rfl⟩ : syracuseStep 2641727 = 3962591) B3962591
theorem B5640155 : Blo 1760081 5640155 := bstep (se 1 (by rfl) ⟨4230116, by rfl⟩ : syracuseStep 5640155 = 8460233) B8460233
theorem B3960809 : Blo 1760081 3960809 := bstep (se 2 (by rfl) ⟨1485303, by rfl⟩ : syracuseStep 3960809 = 2970607) B2970607
theorem B3960863 : Blo 1760081 3960863 := bstep (se 1 (by rfl) ⟨2970647, by rfl⟩ : syracuseStep 3960863 = 5941295) B5941295
theorem B2641967 : Blo 1760081 2641967 := bstep (se 1 (by rfl) ⟨1981475, by rfl⟩ : syracuseStep 2641967 = 3962951) B3962951
theorem B5017697 : Blo 1760081 5017697 := bstep (se 2 (by rfl) ⟨1881636, by rfl⟩ : syracuseStep 5017697 = 3763273) B3763273
theorem B4288727 : Blo 1760081 4288727 := bstep (se 1 (by rfl) ⟨3216545, by rfl⟩ : syracuseStep 4288727 = 6433091) B6433091
theorem B30101867 : Blo 1760081 30101867 := bstep (se 1 (by rfl) ⟨22576400, by rfl⟩ : syracuseStep 30101867 = 45152801) B45152801
theorem B5943671 : Blo 1760081 5943671 := bstep (se 1 (by rfl) ⟨4457753, by rfl⟩ : syracuseStep 5943671 = 8915507) B8915507
theorem B2642411 : Blo 1760081 2642411 := bstep (se 1 (by rfl) ⟨1981808, by rfl⟩ : syracuseStep 2642411 = 3963617) B3963617
theorem B2642537 : Blo 1760081 2642537 := bstep (se 2 (by rfl) ⟨990951, by rfl⟩ : syracuseStep 2642537 = 1981903) B1981903
theorem B2642543 : Blo 1760081 2642543 := bstep (se 1 (by rfl) ⟨1981907, by rfl⟩ : syracuseStep 2642543 = 3963815) B3963815
theorem B32133833 : Blo 1760081 32133833 := bstep (se 2 (by rfl) ⟨12050187, by rfl⟩ : syracuseStep 32133833 = 24100375) B24100375
theorem B2642663 : Blo 1760081 2642663 := bstep (se 1 (by rfl) ⟨1981997, by rfl⟩ : syracuseStep 2642663 = 3963995) B3963995
theorem B6779695 : Blo 1760081 6779695 := bstep (se 1 (by rfl) ⟨5084771, by rfl⟩ : syracuseStep 6779695 = 10169543) B10169543
theorem B3961691 : Blo 1760081 3961691 := bstep (se 1 (by rfl) ⟨2971268, by rfl⟩ : syracuseStep 3961691 = 5942537) B5942537
theorem B2642825 : Blo 1760081 2642825 := bstep (se 2 (by rfl) ⟨991059, by rfl⟩ : syracuseStep 2642825 = 1982119) B1982119
theorem B8573867 : Blo 1760081 8573867 := bstep (se 1 (by rfl) ⟨6430400, by rfl⟩ : syracuseStep 8573867 = 12860801) B12860801
theorem B3863719 : Blo 1760081 3863719 := bstep (se 1 (by rfl) ⟨2897789, by rfl⟩ : syracuseStep 3863719 = 5795579) B5795579
theorem B7525673 : Blo 1760081 7525673 := bstep (se 2 (by rfl) ⟨2822127, by rfl⟩ : syracuseStep 7525673 = 5644255) B5644255
theorem B6346039 : Blo 1760081 6346039 := bstep (se 1 (by rfl) ⟨4759529, by rfl⟩ : syracuseStep 6346039 = 9519059) B9519059
theorem B57120065 : Blo 1760081 57120065 := bstep (se 2 (by rfl) ⟨21420024, by rfl⟩ : syracuseStep 57120065 = 42840049) B42840049
theorem B5944751 : Blo 1760081 5944751 := bstep (se 1 (by rfl) ⟨4458563, by rfl⟩ : syracuseStep 5944751 = 8917127) B8917127
theorem B5944859 : Blo 1760081 5944859 := bstep (se 1 (by rfl) ⟨4458644, by rfl⟩ : syracuseStep 5944859 = 8917289) B8917289
theorem B5150315 : Blo 1760081 5150315 := bstep (se 1 (by rfl) ⟨3862736, by rfl⟩ : syracuseStep 5150315 = 7725473) B7725473
theorem B10033091 : Blo 1760081 10033091 := bstep (se 1 (by rfl) ⟨7524818, by rfl⟩ : syracuseStep 10033091 = 15049637) B15049637
theorem B22558769 : Blo 1760081 22558769 := bstep (se 2 (by rfl) ⟨8459538, by rfl⟩ : syracuseStep 22558769 = 16919077) B16919077
theorem B8460769 : Blo 1760081 8460769 := bstep (se 2 (by rfl) ⟨3172788, by rfl⟩ : syracuseStep 8460769 = 6345577) B6345577
theorem B5945831 : Blo 1760081 5945831 := bstep (se 1 (by rfl) ⟨4459373, by rfl⟩ : syracuseStep 5945831 = 8918747) B8918747
theorem B3963419 : Blo 1760081 3963419 := bstep (se 1 (by rfl) ⟨2972564, by rfl⟩ : syracuseStep 3963419 = 5945129) B5945129
theorem B8911457 : Blo 1760081 8911457 := bstep (se 2 (by rfl) ⟨3341796, by rfl⟩ : syracuseStep 8911457 = 6683593) B6683593
theorem B1760103 : Blo 1760081 1760103 := bstep (se 1 (by rfl) ⟨1320077, by rfl⟩ : syracuseStep 1760103 = 2640155) B2640155
theorem B2972585 : Blo 1760081 2972585 := bstep (se 2 (by rfl) ⟨1114719, by rfl⟩ : syracuseStep 2972585 = 2229439) B2229439
theorem B36142013 : Blo 1760081 36142013 := bstep (se 3 (by rfl) ⟨6776627, by rfl⟩ : syracuseStep 36142013 = 13553255) B13553255
theorem B1760319 : Blo 1760081 1760319 := bstep (se 1 (by rfl) ⟨1320239, by rfl⟩ : syracuseStep 1760319 = 2640479) B2640479
theorem B13368401 : Blo 1760081 13368401 := bstep (se 2 (by rfl) ⟨5013150, by rfl⟩ : syracuseStep 13368401 = 10026301) B10026301
theorem B1760507 : Blo 1760081 1760507 := bstep (se 1 (by rfl) ⟨1320380, by rfl⟩ : syracuseStep 1760507 = 2640761) B2640761
theorem B11443463 : Blo 1760081 11443463 := bstep (se 1 (by rfl) ⟨8582597, by rfl⟩ : syracuseStep 11443463 = 17165195) B17165195
theorem B1760539 : Blo 1760081 1760539 := bstep (se 1 (by rfl) ⟨1320404, by rfl⟩ : syracuseStep 1760539 = 2640809) B2640809
theorem B1760639 : Blo 1760081 1760639 := bstep (se 1 (by rfl) ⟨1320479, by rfl⟩ : syracuseStep 1760639 = 2640959) B2640959
theorem B231603725 : Blo 1760081 231603725 := bstep (se 3 (by rfl) ⟨43425698, by rfl⟩ : syracuseStep 231603725 = 86851397) B86851397
theorem B60980779 : Blo 1760081 60980779 := bstep (se 1 (by rfl) ⟨45735584, by rfl⟩ : syracuseStep 60980779 = 91471169) B91471169
theorem B4456073 : Blo 1760081 4456073 := bstep (se 2 (by rfl) ⟨1671027, by rfl⟩ : syracuseStep 4456073 = 3342055) B3342055
theorem B10714781 : Blo 1760081 10714781 := bstep (se 3 (by rfl) ⟨2009021, by rfl⟩ : syracuseStep 10714781 = 4018043) B4018043
theorem B6684383 : Blo 1760081 6684383 := bstep (se 1 (by rfl) ⟨5013287, by rfl⟩ : syracuseStep 6684383 = 10026575) B10026575
theorem B1761007 : Blo 1760081 1761007 := bstep (se 1 (by rfl) ⟨1320755, by rfl⟩ : syracuseStep 1761007 = 2641511) B2641511
theorem B21421871 : Blo 1760081 21421871 := bstep (se 1 (by rfl) ⟨16066403, by rfl⟩ : syracuseStep 21421871 = 32132807) B32132807
theorem B20062079 : Blo 1760081 20062079 := bstep (se 1 (by rfl) ⟨15046559, by rfl⟩ : syracuseStep 20062079 = 30093119) B30093119
theorem B25739137 : Blo 1760081 25739137 := bstep (se 2 (by rfl) ⟨9652176, by rfl⟩ : syracuseStep 25739137 = 19304353) B19304353
theorem B1761263 : Blo 1760081 1761263 := bstep (se 1 (by rfl) ⟨1320947, by rfl⟩ : syracuseStep 1761263 = 2641895) B2641895
theorem B1761311 : Blo 1760081 1761311 := bstep (se 1 (by rfl) ⟨1320983, by rfl⟩ : syracuseStep 1761311 = 2641967) B2641967
theorem B2859151 : Blo 1760081 2859151 := bstep (se 1 (by rfl) ⟨2144363, by rfl⟩ : syracuseStep 2859151 = 4288727) B4288727
theorem B325230821 : Blo 1760081 325230821 := bstep (se 4 (by rfl) ⟨30490389, by rfl⟩ : syracuseStep 325230821 = 60980779) B60980779
theorem B3571975 : Blo 1760081 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B3342647 : Blo 1760081 3342647 := bstep (se 1 (by rfl) ⟨2506985, by rfl⟩ : syracuseStep 3342647 = 5013971) B5013971
theorem B1761607 : Blo 1760081 1761607 := bstep (se 1 (by rfl) ⟨1321205, by rfl⟩ : syracuseStep 1761607 = 2642411) B2642411
theorem B6685037 : Blo 1760081 6685037 := bstep (se 3 (by rfl) ⟨1253444, by rfl⟩ : syracuseStep 6685037 = 2506889) B2506889
theorem B1761691 : Blo 1760081 1761691 := bstep (se 1 (by rfl) ⟨1321268, by rfl⟩ : syracuseStep 1761691 = 2642537) B2642537
theorem B1761695 : Blo 1760081 1761695 := bstep (se 1 (by rfl) ⟨1321271, by rfl⟩ : syracuseStep 1761695 = 2642543) B2642543
theorem B21422555 : Blo 1760081 21422555 := bstep (se 1 (by rfl) ⟨16066916, by rfl⟩ : syracuseStep 21422555 = 32133833) B32133833
theorem B1761775 : Blo 1760081 1761775 := bstep (se 1 (by rfl) ⟨1321331, by rfl⟩ : syracuseStep 1761775 = 2642663) B2642663
theorem B1761883 : Blo 1760081 1761883 := bstep (se 1 (by rfl) ⟨1321412, by rfl⟩ : syracuseStep 1761883 = 2642825) B2642825
theorem B11281025 : Blo 1760081 11281025 := bstep (se 2 (by rfl) ⟨4230384, by rfl⟩ : syracuseStep 11281025 = 8460769) B8460769
theorem B3761633 : Blo 1760081 3761633 := bstep (se 2 (by rfl) ⟨1410612, by rfl⟩ : syracuseStep 3761633 = 2821225) B2821225
theorem B5940971 : Blo 1760081 5940971 := bstep (se 1 (by rfl) ⟨4455728, by rfl⟩ : syracuseStep 5940971 = 8911457) B8911457
theorem B6686495 : Blo 1760081 6686495 := bstep (se 1 (by rfl) ⟨5014871, by rfl⟩ : syracuseStep 6686495 = 10029743) B10029743
theorem B54208349 : Blo 1760081 54208349 := bstep (se 3 (by rfl) ⟨10164065, by rfl⟩ : syracuseStep 54208349 = 20328131) B20328131
theorem B24094675 : Blo 1760081 24094675 := bstep (se 1 (by rfl) ⟨18071006, by rfl⟩ : syracuseStep 24094675 = 36142013) B36142013
theorem B5015657 : Blo 1760081 5015657 := bstep (se 2 (by rfl) ⟨1880871, by rfl⟩ : syracuseStep 5015657 = 3761743) B3761743
theorem B7628975 : Blo 1760081 7628975 := bstep (se 1 (by rfl) ⟨5721731, by rfl⟩ : syracuseStep 7628975 = 11443463) B11443463
theorem B30509243 : Blo 1760081 30509243 := bstep (se 1 (by rfl) ⟨22881932, by rfl⟩ : syracuseStep 30509243 = 45763865) B45763865
theorem B5015783 : Blo 1760081 5015783 := bstep (se 1 (by rfl) ⟨3761837, by rfl⟩ : syracuseStep 5015783 = 7523675) B7523675
theorem B2640359 : Blo 1760081 2640359 := bstep (se 1 (by rfl) ⟨1980269, by rfl⟩ : syracuseStep 2640359 = 3960539) B3960539
theorem B34318849 : Blo 1760081 34318849 := bstep (se 2 (by rfl) ⟨12869568, by rfl⟩ : syracuseStep 34318849 = 25739137) B25739137
theorem B14281247 : Blo 1760081 14281247 := bstep (se 1 (by rfl) ⟨10710935, by rfl⟩ : syracuseStep 14281247 = 21421871) B21421871
theorem B2640539 : Blo 1760081 2640539 := bstep (se 1 (by rfl) ⟨1980404, by rfl⟩ : syracuseStep 2640539 = 3960809) B3960809
theorem B2640575 : Blo 1760081 2640575 := bstep (se 1 (by rfl) ⟨1980431, by rfl⟩ : syracuseStep 2640575 = 3960863) B3960863
theorem B3345131 : Blo 1760081 3345131 := bstep (se 1 (by rfl) ⟨2508848, by rfl⟩ : syracuseStep 3345131 = 5017697) B5017697
theorem B13372289 : Blo 1760081 13372289 := bstep (se 2 (by rfl) ⟨5014608, by rfl⟩ : syracuseStep 13372289 = 10029217) B10029217
theorem B13380551 : Blo 1760081 13380551 := bstep (se 1 (by rfl) ⟨10035413, by rfl⟩ : syracuseStep 13380551 = 20070827) B20070827
theorem B2641127 : Blo 1760081 2641127 := bstep (se 1 (by rfl) ⟨1980845, by rfl⟩ : syracuseStep 2641127 = 3961691) B3961691
theorem B5017115 : Blo 1760081 5017115 := bstep (se 1 (by rfl) ⟨3762836, by rfl⟩ : syracuseStep 5017115 = 7525673) B7525673
theorem B20606501 : Blo 1760081 20606501 := bstep (se 4 (by rfl) ⟨1931859, by rfl⟩ : syracuseStep 20606501 = 3863719) B3863719
theorem B38080043 : Blo 1760081 38080043 := bstep (se 1 (by rfl) ⟨28560032, by rfl⟩ : syracuseStep 38080043 = 57120065) B57120065
theorem B20057705 : Blo 1760081 20057705 := bstep (se 2 (by rfl) ⟨7521639, by rfl⟩ : syracuseStep 20057705 = 15043279) B15043279
theorem B9039593 : Blo 1760081 9039593 := bstep (se 2 (by rfl) ⟨3389847, by rfl⟩ : syracuseStep 9039593 = 6779695) B6779695
theorem B6688727 : Blo 1760081 6688727 := bstep (se 1 (by rfl) ⟨5016545, by rfl⟩ : syracuseStep 6688727 = 10033091) B10033091
theorem B3960827 : Blo 1760081 3960827 := bstep (se 1 (by rfl) ⟨2970620, by rfl⟩ : syracuseStep 3960827 = 5941241) B5941241
theorem B13734173 : Blo 1760081 13734173 := bstep (se 3 (by rfl) ⟨2575157, by rfl⟩ : syracuseStep 13734173 = 5150315) B5150315
theorem B2642279 : Blo 1760081 2642279 := bstep (se 1 (by rfl) ⟨1981709, by rfl⟩ : syracuseStep 2642279 = 3963419) B3963419
theorem B1880543 : Blo 1760081 1880543 := bstep (se 1 (by rfl) ⟨1410407, by rfl⟩ : syracuseStep 1880543 = 2820815) B2820815
theorem B8917613 : Blo 1760081 8917613 := bstep (se 3 (by rfl) ⟨1672052, by rfl⟩ : syracuseStep 8917613 = 3344105) B3344105
theorem B5944103 : Blo 1760081 5944103 := bstep (se 1 (by rfl) ⟨4458077, by rfl⟩ : syracuseStep 5944103 = 8916155) B8916155
theorem B3961835 : Blo 1760081 3961835 := bstep (se 1 (by rfl) ⟨2971376, by rfl⟩ : syracuseStep 3961835 = 5942753) B5942753
theorem B2970715 : Blo 1760081 2970715 := bstep (se 1 (by rfl) ⟨2228036, by rfl⟩ : syracuseStep 2970715 = 4456073) B4456073
theorem B13374719 : Blo 1760081 13374719 := bstep (se 1 (by rfl) ⟨10031039, by rfl⟩ : syracuseStep 13374719 = 20062079) B20062079
theorem B28251479 : Blo 1760081 28251479 := bstep (se 1 (by rfl) ⟨21188609, by rfl⟩ : syracuseStep 28251479 = 42377219) B42377219
theorem B20067911 : Blo 1760081 20067911 := bstep (se 1 (by rfl) ⟨15050933, by rfl⟩ : syracuseStep 20067911 = 30101867) B30101867
theorem B3962447 : Blo 1760081 3962447 := bstep (se 1 (by rfl) ⟨2971835, by rfl⟩ : syracuseStep 3962447 = 5943671) B5943671
theorem B6346487 : Blo 1760081 6346487 := bstep (se 1 (by rfl) ⟨4759865, by rfl⟩ : syracuseStep 6346487 = 9519731) B9519731
theorem B704649077 : Blo 1760081 704649077 := bstep (se 5 (by rfl) ⟨33030425, by rfl⟩ : syracuseStep 704649077 = 66060851) B66060851
theorem B2676647 : Blo 1760081 2676647 := bstep (se 1 (by rfl) ⟨2007485, by rfl⟩ : syracuseStep 2676647 = 4014971) B4014971
theorem B5715911 : Blo 1760081 5715911 := bstep (se 1 (by rfl) ⟨4286933, by rfl⟩ : syracuseStep 5715911 = 8573867) B8573867
theorem B7526459 : Blo 1760081 7526459 := bstep (se 1 (by rfl) ⟨5644844, by rfl⟩ : syracuseStep 7526459 = 11289689) B11289689
theorem B48207973 : Blo 1760081 48207973 := bstep (se 4 (by rfl) ⟨4519497, by rfl⟩ : syracuseStep 48207973 = 9038995) B9038995
theorem B3963167 : Blo 1760081 3963167 := bstep (se 1 (by rfl) ⟨2972375, by rfl⟩ : syracuseStep 3963167 = 5944751) B5944751
theorem B3963239 : Blo 1760081 3963239 := bstep (se 1 (by rfl) ⟨2972429, by rfl⟩ : syracuseStep 3963239 = 5944859) B5944859
theorem B15252097 : Blo 1760081 15252097 := bstep (se 2 (by rfl) ⟨5719536, by rfl⟩ : syracuseStep 15252097 = 11439073) B11439073
theorem B15039179 : Blo 1760081 15039179 := bstep (se 1 (by rfl) ⟨11279384, by rfl⟩ : syracuseStep 15039179 = 22558769) B22558769
theorem B2972423 : Blo 1760081 2972423 := bstep (se 1 (by rfl) ⟨2229317, by rfl⟩ : syracuseStep 2972423 = 4458635) B4458635
theorem B1760127 : Blo 1760081 1760127 := bstep (se 1 (by rfl) ⟨1320095, by rfl⟩ : syracuseStep 1760127 = 2640191) B2640191
theorem B1760223 : Blo 1760081 1760223 := bstep (se 1 (by rfl) ⟨1320167, by rfl⟩ : syracuseStep 1760223 = 2640335) B2640335
theorem B3963887 : Blo 1760081 3963887 := bstep (se 1 (by rfl) ⟨2972915, by rfl⟩ : syracuseStep 3963887 = 5945831) B5945831
theorem B1760251 : Blo 1760081 1760251 := bstep (se 1 (by rfl) ⟨1320188, by rfl⟩ : syracuseStep 1760251 = 2640377) B2640377
theorem B1760283 : Blo 1760081 1760283 := bstep (se 1 (by rfl) ⟨1320212, by rfl⟩ : syracuseStep 1760283 = 2640425) B2640425
theorem B8461367 : Blo 1760081 8461367 := bstep (se 1 (by rfl) ⟨6346025, by rfl⟩ : syracuseStep 8461367 = 12692051) B12692051
theorem B8461385 : Blo 1760081 8461385 := bstep (se 2 (by rfl) ⟨3173019, by rfl⟩ : syracuseStep 8461385 = 6346039) B6346039
theorem B1981723 : Blo 1760081 1981723 := bstep (se 1 (by rfl) ⟨1486292, by rfl⟩ : syracuseStep 1981723 = 2972585) B2972585
theorem B2972983 : Blo 1760081 2972983 := bstep (se 1 (by rfl) ⟨2229737, by rfl⟩ : syracuseStep 2972983 = 4459475) B4459475
theorem B1760575 : Blo 1760081 1760575 := bstep (se 1 (by rfl) ⟨1320431, by rfl⟩ : syracuseStep 1760575 = 2640863) B2640863
theorem B8912267 : Blo 1760081 8912267 := bstep (se 1 (by rfl) ⟨6684200, by rfl⟩ : syracuseStep 8912267 = 13368401) B13368401
theorem B1760871 : Blo 1760081 1760871 := bstep (se 1 (by rfl) ⟨1320653, by rfl⟩ : syracuseStep 1760871 = 2641307) B2641307
theorem B154402483 : Blo 1760081 154402483 := bstep (se 1 (by rfl) ⟨115801862, by rfl⟩ : syracuseStep 154402483 = 231603725) B231603725
theorem B7143187 : Blo 1760081 7143187 := bstep (se 1 (by rfl) ⟨5357390, by rfl⟩ : syracuseStep 7143187 = 10714781) B10714781
theorem B4456255 : Blo 1760081 4456255 := bstep (se 1 (by rfl) ⟨3342191, by rfl⟩ : syracuseStep 4456255 = 6684383) B6684383
theorem B2973503 : Blo 1760081 2973503 := bstep (se 1 (by rfl) ⟨2230127, by rfl⟩ : syracuseStep 2973503 = 4460255) B4460255
theorem B1761115 : Blo 1760081 1761115 := bstep (se 1 (by rfl) ⟨1320836, by rfl⟩ : syracuseStep 1761115 = 2641673) B2641673
theorem B1761151 : Blo 1760081 1761151 := bstep (se 1 (by rfl) ⟨1320863, by rfl⟩ : syracuseStep 1761151 = 2641727) B2641727
theorem B3760103 : Blo 1760081 3760103 := bstep (se 1 (by rfl) ⟨2820077, by rfl⟩ : syracuseStep 3760103 = 5640155) B5640155
theorem B1761519 : Blo 1760081 1761519 := bstep (se 1 (by rfl) ⟨1321139, by rfl⟩ : syracuseStep 1761519 = 2642279) B2642279
theorem B4456691 : Blo 1760081 4456691 := bstep (se 1 (by rfl) ⟨3342518, by rfl⟩ : syracuseStep 4456691 = 6685037) B6685037
theorem B7520683 : Blo 1760081 7520683 := bstep (se 1 (by rfl) ⟨5640512, by rfl⟩ : syracuseStep 7520683 = 11281025) B11281025
theorem B8913725 : Blo 1760081 8913725 := bstep (se 3 (by rfl) ⟨1671323, by rfl⟩ : syracuseStep 8913725 = 3342647) B3342647
theorem B18834319 : Blo 1760081 18834319 := bstep (se 1 (by rfl) ⟨14125739, by rfl⟩ : syracuseStep 18834319 = 28251479) B28251479
theorem B2507755 : Blo 1760081 2507755 := bstep (se 1 (by rfl) ⟨1880816, by rfl⟩ : syracuseStep 2507755 = 3761633) B3761633
theorem B13378607 : Blo 1760081 13378607 := bstep (se 1 (by rfl) ⟨10033955, by rfl⟩ : syracuseStep 13378607 = 20067911) B20067911
theorem B4457663 : Blo 1760081 4457663 := bstep (se 1 (by rfl) ⟨3343247, by rfl⟩ : syracuseStep 4457663 = 6686495) B6686495
theorem B5014781 : Blo 1760081 5014781 := bstep (se 3 (by rfl) ⟨940271, by rfl⟩ : syracuseStep 5014781 = 1880543) B1880543
theorem B3810607 : Blo 1760081 3810607 := bstep (se 1 (by rfl) ⟨2857955, by rfl⟩ : syracuseStep 3810607 = 5715911) B5715911
theorem B3343771 : Blo 1760081 3343771 := bstep (se 1 (by rfl) ⟨2507828, by rfl⟩ : syracuseStep 3343771 = 5015657) B5015657
theorem B3343855 : Blo 1760081 3343855 := bstep (se 1 (by rfl) ⟨2507891, by rfl⟩ : syracuseStep 3343855 = 5015783) B5015783
theorem B9520831 : Blo 1760081 9520831 := bstep (se 1 (by rfl) ⟨7140623, by rfl⟩ : syracuseStep 9520831 = 14281247) B14281247
theorem B2230087 : Blo 1760081 2230087 := bstep (se 1 (by rfl) ⟨1672565, by rfl⟩ : syracuseStep 2230087 = 3345131) B3345131
theorem B8914859 : Blo 1760081 8914859 := bstep (se 1 (by rfl) ⟨6686144, by rfl⟩ : syracuseStep 8914859 = 13372289) B13372289
theorem B5941511 : Blo 1760081 5941511 := bstep (se 1 (by rfl) ⟨4456133, by rfl⟩ : syracuseStep 5941511 = 8912267) B8912267
theorem B3344743 : Blo 1760081 3344743 := bstep (se 1 (by rfl) ⟨2508557, by rfl⟩ : syracuseStep 3344743 = 5017115) B5017115
theorem B13371803 : Blo 1760081 13371803 := bstep (se 1 (by rfl) ⟨10028852, by rfl⟩ : syracuseStep 13371803 = 20057705) B20057705
theorem B5941673 : Blo 1760081 5941673 := bstep (se 2 (by rfl) ⟨2228127, by rfl⟩ : syracuseStep 5941673 = 4456255) B4456255
theorem B4459151 : Blo 1760081 4459151 := bstep (se 1 (by rfl) ⟨3344363, by rfl⟩ : syracuseStep 4459151 = 6688727) B6688727
theorem B2640551 : Blo 1760081 2640551 := bstep (se 1 (by rfl) ⟨1980413, by rfl⟩ : syracuseStep 2640551 = 3960827) B3960827
theorem B64277297 : Blo 1760081 64277297 := bstep (se 2 (by rfl) ⟨24103986, by rfl⟩ : syracuseStep 64277297 = 48207973) B48207973
theorem B216820547 : Blo 1760081 216820547 := bstep (se 1 (by rfl) ⟨162615410, by rfl⟩ : syracuseStep 216820547 = 325230821) B325230821
theorem B3812201 : Blo 1760081 3812201 := bstep (se 2 (by rfl) ⟨1429575, by rfl⟩ : syracuseStep 3812201 = 2859151) B2859151
theorem B14281703 : Blo 1760081 14281703 := bstep (se 1 (by rfl) ⟨10711277, by rfl⟩ : syracuseStep 14281703 = 21422555) B21422555
theorem B4762633 : Blo 1760081 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B2641223 : Blo 1760081 2641223 := bstep (se 1 (by rfl) ⟨1980917, by rfl⟩ : syracuseStep 2641223 = 3961835) B3961835
theorem B8916479 : Blo 1760081 8916479 := bstep (se 1 (by rfl) ⟨6687359, by rfl⟩ : syracuseStep 8916479 = 13374719) B13374719
theorem B20336129 : Blo 1760081 20336129 := bstep (se 2 (by rfl) ⟨7626048, by rfl⟩ : syracuseStep 20336129 = 15252097) B15252097
theorem B2641631 : Blo 1760081 2641631 := bstep (se 1 (by rfl) ⟨1981223, by rfl⟩ : syracuseStep 2641631 = 3962447) B3962447
theorem B3960647 : Blo 1760081 3960647 := bstep (se 1 (by rfl) ⟨2970485, by rfl⟩ : syracuseStep 3960647 = 5940971) B5940971
theorem B4230991 : Blo 1760081 4230991 := bstep (se 1 (by rfl) ⟨3173243, by rfl⟩ : syracuseStep 4230991 = 6346487) B6346487
theorem B36138899 : Blo 1760081 36138899 := bstep (se 1 (by rfl) ⟨27104174, by rfl⟩ : syracuseStep 36138899 = 54208349) B54208349
theorem B469766051 : Blo 1760081 469766051 := bstep (se 1 (by rfl) ⟨352324538, by rfl⟩ : syracuseStep 469766051 = 704649077) B704649077
theorem B5017639 : Blo 1760081 5017639 := bstep (se 1 (by rfl) ⟨3763229, by rfl⟩ : syracuseStep 5017639 = 7526459) B7526459
theorem B3960953 : Blo 1760081 3960953 := bstep (se 2 (by rfl) ⟨1485357, by rfl⟩ : syracuseStep 3960953 = 2970715) B2970715
theorem B2642111 : Blo 1760081 2642111 := bstep (se 1 (by rfl) ⟨1981583, by rfl⟩ : syracuseStep 2642111 = 3963167) B3963167
theorem B2642159 : Blo 1760081 2642159 := bstep (se 1 (by rfl) ⟨1981619, by rfl⟩ : syracuseStep 2642159 = 3963239) B3963239
theorem B2642297 : Blo 1760081 2642297 := bstep (se 2 (by rfl) ⟨990861, by rfl⟩ : syracuseStep 2642297 = 1981723) B1981723
theorem B2642591 : Blo 1760081 2642591 := bstep (se 1 (by rfl) ⟨1981943, by rfl⟩ : syracuseStep 2642591 = 3963887) B3963887
theorem B5640911 : Blo 1760081 5640911 := bstep (se 1 (by rfl) ⟨4230683, by rfl⟩ : syracuseStep 5640911 = 8461367) B8461367
theorem B5640923 : Blo 1760081 5640923 := bstep (se 1 (by rfl) ⟨4230692, by rfl⟩ : syracuseStep 5640923 = 8461385) B8461385
theorem B205869977 : Blo 1760081 205869977 := bstep (se 2 (by rfl) ⟨77201241, by rfl⟩ : syracuseStep 205869977 = 154402483) B154402483
theorem B9524249 : Blo 1760081 9524249 := bstep (se 2 (by rfl) ⟨3571593, by rfl⟩ : syracuseStep 9524249 = 7143187) B7143187
theorem B6026395 : Blo 1760081 6026395 := bstep (se 1 (by rfl) ⟨4519796, by rfl⟩ : syracuseStep 6026395 = 9039593) B9039593
theorem B32126233 : Blo 1760081 32126233 := bstep (se 2 (by rfl) ⟨12047337, by rfl⟩ : syracuseStep 32126233 = 24094675) B24094675
theorem B9156115 : Blo 1760081 9156115 := bstep (se 1 (by rfl) ⟨6867086, by rfl⟩ : syracuseStep 9156115 = 13734173) B13734173
theorem B5945075 : Blo 1760081 5945075 := bstep (se 1 (by rfl) ⟨4458806, by rfl⟩ : syracuseStep 5945075 = 8917613) B8917613
theorem B3962735 : Blo 1760081 3962735 := bstep (se 1 (by rfl) ⟨2972051, by rfl⟩ : syracuseStep 3962735 = 5944103) B5944103
theorem B45758465 : Blo 1760081 45758465 := bstep (se 2 (by rfl) ⟨17159424, by rfl⟩ : syracuseStep 45758465 = 34318849) B34318849
theorem B1784431 : Blo 1760081 1784431 := bstep (se 1 (by rfl) ⟨1338323, by rfl⟩ : syracuseStep 1784431 = 2676647) B2676647
theorem B54950669 : Blo 1760081 54950669 := bstep (se 3 (by rfl) ⟨10303250, by rfl⟩ : syracuseStep 54950669 = 20606501) B20606501
theorem B5085983 : Blo 1760081 5085983 := bstep (se 1 (by rfl) ⟨3814487, by rfl⟩ : syracuseStep 5085983 = 7628975) B7628975
theorem B20339495 : Blo 1760081 20339495 := bstep (se 1 (by rfl) ⟨15254621, by rfl⟩ : syracuseStep 20339495 = 30509243) B30509243
theorem B1760239 : Blo 1760081 1760239 := bstep (se 1 (by rfl) ⟨1320179, by rfl⟩ : syracuseStep 1760239 = 2640359) B2640359
theorem B3963977 : Blo 1760081 3963977 := bstep (se 2 (by rfl) ⟨1486491, by rfl⟩ : syracuseStep 3963977 = 2972983) B2972983
theorem B1760359 : Blo 1760081 1760359 := bstep (se 1 (by rfl) ⟨1320269, by rfl⟩ : syracuseStep 1760359 = 2640539) B2640539
theorem B1760383 : Blo 1760081 1760383 := bstep (se 1 (by rfl) ⟨1320287, by rfl⟩ : syracuseStep 1760383 = 2640575) B2640575
theorem B10026119 : Blo 1760081 10026119 := bstep (se 1 (by rfl) ⟨7519589, by rfl⟩ : syracuseStep 10026119 = 15039179) B15039179
theorem B1981615 : Blo 1760081 1981615 := bstep (se 1 (by rfl) ⟨1486211, by rfl⟩ : syracuseStep 1981615 = 2972423) B2972423
theorem B8920367 : Blo 1760081 8920367 := bstep (se 1 (by rfl) ⟨6690275, by rfl⟩ : syracuseStep 8920367 = 13380551) B13380551
theorem B1760751 : Blo 1760081 1760751 := bstep (se 1 (by rfl) ⟨1320563, by rfl⟩ : syracuseStep 1760751 = 2641127) B2641127
theorem B25386695 : Blo 1760081 25386695 := bstep (se 1 (by rfl) ⟨19040021, by rfl⟩ : syracuseStep 25386695 = 38080043) B38080043
theorem B1982335 : Blo 1760081 1982335 := bstep (se 1 (by rfl) ⟨1486751, by rfl⟩ : syracuseStep 1982335 = 2973503) B2973503
theorem B2506735 : Blo 1760081 2506735 := bstep (se 1 (by rfl) ⟨1880051, by rfl⟩ : syracuseStep 2506735 = 3760103) B3760103
theorem B1761407 : Blo 1760081 1761407 := bstep (se 1 (by rfl) ⟨1321055, by rfl⟩ : syracuseStep 1761407 = 2642111) B2642111
theorem B1761439 : Blo 1760081 1761439 := bstep (se 1 (by rfl) ⟨1321079, by rfl⟩ : syracuseStep 1761439 = 2642159) B2642159
theorem B1761531 : Blo 1760081 1761531 := bstep (se 1 (by rfl) ⟨1321148, by rfl⟩ : syracuseStep 1761531 = 2642297) B2642297
theorem B1761727 : Blo 1760081 1761727 := bstep (se 1 (by rfl) ⟨1321295, by rfl⟩ : syracuseStep 1761727 = 2642591) B2642591
theorem B3760607 : Blo 1760081 3760607 := bstep (se 1 (by rfl) ⟨2820455, by rfl⟩ : syracuseStep 3760607 = 5640911) B5640911
theorem B3760615 : Blo 1760081 3760615 := bstep (se 1 (by rfl) ⟨2820461, by rfl⟩ : syracuseStep 3760615 = 5640923) B5640923
theorem B10027577 : Blo 1760081 10027577 := bstep (se 2 (by rfl) ⟨3760341, by rfl⟩ : syracuseStep 10027577 = 7520683) B7520683
theorem B6349499 : Blo 1760081 6349499 := bstep (se 1 (by rfl) ⟨4762124, by rfl⟩ : syracuseStep 6349499 = 9524249) B9524249
theorem B3343187 : Blo 1760081 3343187 := bstep (se 1 (by rfl) ⟨2507390, by rfl⟩ : syracuseStep 3343187 = 5014781) B5014781
theorem B3343673 : Blo 1760081 3343673 := bstep (se 2 (by rfl) ⟨1253877, by rfl⟩ : syracuseStep 3343673 = 2507755) B2507755
theorem B6350177 : Blo 1760081 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B8914535 : Blo 1760081 8914535 := bstep (se 1 (by rfl) ⟨6685901, by rfl⟩ : syracuseStep 8914535 = 13371803) B13371803
theorem B13559663 : Blo 1760081 13559663 := bstep (se 1 (by rfl) ⟨10169747, by rfl⟩ : syracuseStep 13559663 = 20339495) B20339495
theorem B4458361 : Blo 1760081 4458361 := bstep (se 2 (by rfl) ⟨1671885, by rfl⟩ : syracuseStep 4458361 = 3343771) B3343771
theorem B2541467 : Blo 1760081 2541467 := bstep (se 1 (by rfl) ⟨1906100, by rfl⟩ : syracuseStep 2541467 = 3812201) B3812201
theorem B4458473 : Blo 1760081 4458473 := bstep (se 2 (by rfl) ⟨1671927, by rfl⟩ : syracuseStep 4458473 = 3343855) B3343855
theorem B9521135 : Blo 1760081 9521135 := bstep (se 1 (by rfl) ⟨7140851, by rfl⟩ : syracuseStep 9521135 = 14281703) B14281703
theorem B12208153 : Blo 1760081 12208153 := bstep (se 2 (by rfl) ⟨4578057, by rfl⟩ : syracuseStep 12208153 = 9156115) B9156115
theorem B2640431 : Blo 1760081 2640431 := bstep (se 1 (by rfl) ⟨1980323, by rfl⟩ : syracuseStep 2640431 = 3960647) B3960647
theorem B2640635 : Blo 1760081 2640635 := bstep (se 1 (by rfl) ⟨1980476, by rfl⟩ : syracuseStep 2640635 = 3960953) B3960953
theorem B4459657 : Blo 1760081 4459657 := bstep (se 2 (by rfl) ⟨1672371, by rfl⟩ : syracuseStep 4459657 = 3344743) B3344743
theorem B5942483 : Blo 1760081 5942483 := bstep (se 1 (by rfl) ⟨4456862, by rfl⟩ : syracuseStep 5942483 = 8913725) B8913725
theorem B2379241 : Blo 1760081 2379241 := bstep (se 2 (by rfl) ⟨892215, by rfl⟩ : syracuseStep 2379241 = 1784431) B1784431
theorem B50777765 : Blo 1760081 50777765 := bstep (se 4 (by rfl) ⟨4760415, by rfl⟩ : syracuseStep 50777765 = 9520831) B9520831
theorem B25112425 : Blo 1760081 25112425 := bstep (se 2 (by rfl) ⟨9417159, by rfl⟩ : syracuseStep 25112425 = 18834319) B18834319
theorem B2641823 : Blo 1760081 2641823 := bstep (se 1 (by rfl) ⟨1981367, by rfl⟩ : syracuseStep 2641823 = 3962735) B3962735
theorem B5943239 : Blo 1760081 5943239 := bstep (se 1 (by rfl) ⟨4457429, by rfl⟩ : syracuseStep 5943239 = 8914859) B8914859
theorem B3961007 : Blo 1760081 3961007 := bstep (se 1 (by rfl) ⟨2970755, by rfl⟩ : syracuseStep 3961007 = 5941511) B5941511
theorem B2642153 : Blo 1760081 2642153 := bstep (se 2 (by rfl) ⟨990807, by rfl⟩ : syracuseStep 2642153 = 1981615) B1981615
theorem B3961115 : Blo 1760081 3961115 := bstep (se 1 (by rfl) ⟨2970836, by rfl⟩ : syracuseStep 3961115 = 5941673) B5941673
theorem B2642651 : Blo 1760081 2642651 := bstep (se 1 (by rfl) ⟨1981988, by rfl⟩ : syracuseStep 2642651 = 3963977) B3963977
theorem B5944319 : Blo 1760081 5944319 := bstep (se 1 (by rfl) ⟨4458239, by rfl⟩ : syracuseStep 5944319 = 8916479) B8916479
theorem B5641321 : Blo 1760081 5641321 := bstep (se 2 (by rfl) ⟨2115495, by rfl⟩ : syracuseStep 5641321 = 4230991) B4230991
theorem B2643113 : Blo 1760081 2643113 := bstep (se 2 (by rfl) ⟨991167, by rfl⟩ : syracuseStep 2643113 = 1982335) B1982335
theorem B313177367 : Blo 1760081 313177367 := bstep (se 1 (by rfl) ⟨234883025, by rfl⟩ : syracuseStep 313177367 = 469766051) B469766051
theorem B6690185 : Blo 1760081 6690185 := bstep (se 2 (by rfl) ⟨2508819, by rfl⟩ : syracuseStep 6690185 = 5017639) B5017639
theorem B2971127 : Blo 1760081 2971127 := bstep (se 1 (by rfl) ⟨2228345, by rfl⟩ : syracuseStep 2971127 = 4456691) B4456691
theorem B137246651 : Blo 1760081 137246651 := bstep (se 1 (by rfl) ⟨102934988, by rfl⟩ : syracuseStep 137246651 = 205869977) B205869977
theorem B8919071 : Blo 1760081 8919071 := bstep (se 1 (by rfl) ⟨6689303, by rfl⟩ : syracuseStep 8919071 = 13378607) B13378607
theorem B2971775 : Blo 1760081 2971775 := bstep (se 1 (by rfl) ⟨2228831, by rfl⟩ : syracuseStep 2971775 = 4457663) B4457663
theorem B3963383 : Blo 1760081 3963383 := bstep (se 1 (by rfl) ⟨2972537, by rfl⟩ : syracuseStep 3963383 = 5945075) B5945075
theorem B30505643 : Blo 1760081 30505643 := bstep (se 1 (by rfl) ⟨22879232, by rfl⟩ : syracuseStep 30505643 = 45758465) B45758465
theorem B8035193 : Blo 1760081 8035193 := bstep (se 2 (by rfl) ⟨3013197, by rfl⟩ : syracuseStep 8035193 = 6026395) B6026395
theorem B20323237 : Blo 1760081 20323237 := bstep (se 4 (by rfl) ⟨1905303, by rfl⟩ : syracuseStep 20323237 = 3810607) B3810607
theorem B42834977 : Blo 1760081 42834977 := bstep (se 2 (by rfl) ⟨16063116, by rfl⟩ : syracuseStep 42834977 = 32126233) B32126233
theorem B2972767 : Blo 1760081 2972767 := bstep (se 1 (by rfl) ⟨2229575, by rfl⟩ : syracuseStep 2972767 = 4459151) B4459151
theorem B1760367 : Blo 1760081 1760367 := bstep (se 1 (by rfl) ⟨1320275, by rfl⟩ : syracuseStep 1760367 = 2640551) B2640551
theorem B36633779 : Blo 1760081 36633779 := bstep (se 1 (by rfl) ⟨27475334, by rfl⟩ : syracuseStep 36633779 = 54950669) B54950669
theorem B3390655 : Blo 1760081 3390655 := bstep (se 1 (by rfl) ⟨2542991, by rfl⟩ : syracuseStep 3390655 = 5085983) B5085983
theorem B42851531 : Blo 1760081 42851531 := bstep (se 1 (by rfl) ⟨32138648, by rfl⟩ : syracuseStep 42851531 = 64277297) B64277297
theorem B144547031 : Blo 1760081 144547031 := bstep (se 1 (by rfl) ⟨108410273, by rfl⟩ : syracuseStep 144547031 = 216820547) B216820547
theorem B6684079 : Blo 1760081 6684079 := bstep (se 1 (by rfl) ⟨5013059, by rfl⟩ : syracuseStep 6684079 = 10026119) B10026119
theorem B5946911 : Blo 1760081 5946911 := bstep (se 1 (by rfl) ⟨4460183, by rfl⟩ : syracuseStep 5946911 = 8920367) B8920367
theorem B1760815 : Blo 1760081 1760815 := bstep (se 1 (by rfl) ⟨1320611, by rfl⟩ : syracuseStep 1760815 = 2641223) B2641223
theorem B13557419 : Blo 1760081 13557419 := bstep (se 1 (by rfl) ⟨10168064, by rfl⟩ : syracuseStep 13557419 = 20336129) B20336129
theorem B96370397 : Blo 1760081 96370397 := bstep (se 3 (by rfl) ⟨18069449, by rfl⟩ : syracuseStep 96370397 = 36138899) B36138899
theorem B2973449 : Blo 1760081 2973449 := bstep (se 2 (by rfl) ⟨1115043, by rfl⟩ : syracuseStep 2973449 = 2230087) B2230087
theorem B16924463 : Blo 1760081 16924463 := bstep (se 1 (by rfl) ⟨12693347, by rfl⟩ : syracuseStep 16924463 = 25386695) B25386695
theorem B1761087 : Blo 1760081 1761087 := bstep (se 1 (by rfl) ⟨1320815, by rfl⟩ : syracuseStep 1761087 = 2641631) B2641631
theorem B3342313 : Blo 1760081 3342313 := bstep (se 2 (by rfl) ⟨1253367, by rfl⟩ : syracuseStep 3342313 = 2506735) B2506735
theorem B16277537 : Blo 1760081 16277537 := bstep (se 2 (by rfl) ⟨6104076, by rfl⟩ : syracuseStep 16277537 = 12208153) B12208153
theorem B1761435 : Blo 1760081 1761435 := bstep (se 1 (by rfl) ⟨1321076, by rfl⟩ : syracuseStep 1761435 = 2642153) B2642153
theorem B6685051 : Blo 1760081 6685051 := bstep (se 1 (by rfl) ⟨5013788, by rfl⟩ : syracuseStep 6685051 = 10027577) B10027577
theorem B1761767 : Blo 1760081 1761767 := bstep (se 1 (by rfl) ⟨1321325, by rfl⟩ : syracuseStep 1761767 = 2642651) B2642651
theorem B2228791 : Blo 1760081 2228791 := bstep (se 1 (by rfl) ⟨1671593, by rfl⟩ : syracuseStep 2228791 = 3343187) B3343187
theorem B5014153 : Blo 1760081 5014153 := bstep (se 2 (by rfl) ⟨1880307, by rfl⟩ : syracuseStep 5014153 = 3760615) B3760615
theorem B1762075 : Blo 1760081 1762075 := bstep (se 1 (by rfl) ⟨1321556, by rfl⟩ : syracuseStep 1762075 = 2643113) B2643113
theorem B2229115 : Blo 1760081 2229115 := bstep (se 1 (by rfl) ⟨1671836, by rfl⟩ : syracuseStep 2229115 = 3343673) B3343673
theorem B16933805 : Blo 1760081 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B10028285 : Blo 1760081 10028285 := bstep (se 3 (by rfl) ⟨1880303, by rfl⟩ : syracuseStep 10028285 = 3760607) B3760607
theorem B91497767 : Blo 1760081 91497767 := bstep (se 1 (by rfl) ⟨68623325, by rfl⟩ : syracuseStep 91497767 = 137246651) B137246651
theorem B7521761 : Blo 1760081 7521761 := bstep (se 2 (by rfl) ⟨2820660, by rfl⟩ : syracuseStep 7521761 = 5641321) B5641321
theorem B3172321 : Blo 1760081 3172321 := bstep (se 2 (by rfl) ⟨1189620, by rfl⟩ : syracuseStep 3172321 = 2379241) B2379241
theorem B24422519 : Blo 1760081 24422519 := bstep (se 1 (by rfl) ⟨18316889, by rfl⟩ : syracuseStep 24422519 = 36633779) B36633779
theorem B28567687 : Blo 1760081 28567687 := bstep (se 1 (by rfl) ⟨21425765, by rfl⟩ : syracuseStep 28567687 = 42851531) B42851531
theorem B96364687 : Blo 1760081 96364687 := bstep (se 1 (by rfl) ⟨72273515, by rfl⟩ : syracuseStep 96364687 = 144547031) B144547031
theorem B6777245 : Blo 1760081 6777245 := bstep (se 3 (by rfl) ⟨1270733, by rfl⟩ : syracuseStep 6777245 = 2541467) B2541467
theorem B33851843 : Blo 1760081 33851843 := bstep (se 1 (by rfl) ⟨25388882, by rfl⟩ : syracuseStep 33851843 = 50777765) B50777765
theorem B9038279 : Blo 1760081 9038279 := bstep (se 1 (by rfl) ⟨6778709, by rfl⟩ : syracuseStep 9038279 = 13557419) B13557419
theorem B33483233 : Blo 1760081 33483233 := bstep (se 2 (by rfl) ⟨12556212, by rfl⟩ : syracuseStep 33483233 = 25112425) B25112425
theorem B11282975 : Blo 1760081 11282975 := bstep (se 1 (by rfl) ⟨8462231, by rfl⟩ : syracuseStep 11282975 = 16924463) B16924463
theorem B2640671 : Blo 1760081 2640671 := bstep (se 1 (by rfl) ⟨1980503, by rfl⟩ : syracuseStep 2640671 = 3961007) B3961007
theorem B2640743 : Blo 1760081 2640743 := bstep (se 1 (by rfl) ⟨1980557, by rfl⟩ : syracuseStep 2640743 = 3961115) B3961115
theorem B4460123 : Blo 1760081 4460123 := bstep (se 1 (by rfl) ⟨3345092, by rfl⟩ : syracuseStep 4460123 = 6690185) B6690185
theorem B5943023 : Blo 1760081 5943023 := bstep (se 1 (by rfl) ⟨4457267, by rfl⟩ : syracuseStep 5943023 = 8914535) B8914535
theorem B9039775 : Blo 1760081 9039775 := bstep (se 1 (by rfl) ⟨6779831, by rfl⟩ : syracuseStep 9039775 = 13559663) B13559663
theorem B2642255 : Blo 1760081 2642255 := bstep (se 1 (by rfl) ⟨1981691, by rfl⟩ : syracuseStep 2642255 = 3963383) B3963383
theorem B20337095 : Blo 1760081 20337095 := bstep (se 1 (by rfl) ⟨15252821, by rfl⟩ : syracuseStep 20337095 = 30505643) B30505643
theorem B3961655 : Blo 1760081 3961655 := bstep (se 1 (by rfl) ⟨2971241, by rfl⟩ : syracuseStep 3961655 = 5942483) B5942483
theorem B64246931 : Blo 1760081 64246931 := bstep (se 1 (by rfl) ⟨48185198, by rfl⟩ : syracuseStep 64246931 = 96370397) B96370397
theorem B5944481 : Blo 1760081 5944481 := bstep (se 2 (by rfl) ⟨2229180, by rfl⟩ : syracuseStep 5944481 = 4458361) B4458361
theorem B3962159 : Blo 1760081 3962159 := bstep (se 1 (by rfl) ⟨2971619, by rfl⟩ : syracuseStep 3962159 = 5943239) B5943239
theorem B4232999 : Blo 1760081 4232999 := bstep (se 1 (by rfl) ⟨3174749, by rfl⟩ : syracuseStep 4232999 = 6349499) B6349499
theorem B3962879 : Blo 1760081 3962879 := bstep (se 1 (by rfl) ⟨2972159, by rfl⟩ : syracuseStep 3962879 = 5944319) B5944319
theorem B835139645 : Blo 1760081 835139645 := bstep (se 3 (by rfl) ⟨156588683, by rfl⟩ : syracuseStep 835139645 = 313177367) B313177367
theorem B1980751 : Blo 1760081 1980751 := bstep (se 1 (by rfl) ⟨1485563, by rfl⟩ : syracuseStep 1980751 = 2971127) B2971127
theorem B27097649 : Blo 1760081 27097649 := bstep (se 2 (by rfl) ⟨10161618, by rfl⟩ : syracuseStep 27097649 = 20323237) B20323237
theorem B2972315 : Blo 1760081 2972315 := bstep (se 1 (by rfl) ⟨2229236, by rfl⟩ : syracuseStep 2972315 = 4458473) B4458473
theorem B6347423 : Blo 1760081 6347423 := bstep (se 1 (by rfl) ⟨4760567, by rfl⟩ : syracuseStep 6347423 = 9521135) B9521135
theorem B5946047 : Blo 1760081 5946047 := bstep (se 1 (by rfl) ⟨4459535, by rfl⟩ : syracuseStep 5946047 = 8919071) B8919071
theorem B1981183 : Blo 1760081 1981183 := bstep (se 1 (by rfl) ⟨1485887, by rfl⟩ : syracuseStep 1981183 = 2971775) B2971775
theorem B3963689 : Blo 1760081 3963689 := bstep (se 2 (by rfl) ⟨1486383, by rfl⟩ : syracuseStep 3963689 = 2972767) B2972767
theorem B5946209 : Blo 1760081 5946209 := bstep (se 2 (by rfl) ⟨2229828, by rfl⟩ : syracuseStep 5946209 = 4459657) B4459657
theorem B4520873 : Blo 1760081 4520873 := bstep (se 2 (by rfl) ⟨1695327, by rfl⟩ : syracuseStep 4520873 = 3390655) B3390655
theorem B1760287 : Blo 1760081 1760287 := bstep (se 1 (by rfl) ⟨1320215, by rfl⟩ : syracuseStep 1760287 = 2640431) B2640431
theorem B1760423 : Blo 1760081 1760423 := bstep (se 1 (by rfl) ⟨1320317, by rfl⟩ : syracuseStep 1760423 = 2640635) B2640635
theorem B8912105 : Blo 1760081 8912105 := bstep (se 2 (by rfl) ⟨3342039, by rfl⟩ : syracuseStep 8912105 = 6684079) B6684079
theorem B5356795 : Blo 1760081 5356795 := bstep (se 1 (by rfl) ⟨4017596, by rfl⟩ : syracuseStep 5356795 = 8035193) B8035193
theorem B28556651 : Blo 1760081 28556651 := bstep (se 1 (by rfl) ⟨21417488, by rfl⟩ : syracuseStep 28556651 = 42834977) B42834977
theorem B3964607 : Blo 1760081 3964607 := bstep (se 1 (by rfl) ⟨2973455, by rfl⟩ : syracuseStep 3964607 = 5946911) B5946911
theorem B1982299 : Blo 1760081 1982299 := bstep (se 1 (by rfl) ⟨1486724, by rfl⟩ : syracuseStep 1982299 = 2973449) B2973449
theorem B1761215 : Blo 1760081 1761215 := bstep (se 1 (by rfl) ⟨1320911, by rfl⟩ : syracuseStep 1761215 = 2641823) B2641823
theorem B4456417 : Blo 1760081 4456417 := bstep (se 2 (by rfl) ⟨1671156, by rfl⟩ : syracuseStep 4456417 = 3342313) B3342313
theorem B1761503 : Blo 1760081 1761503 := bstep (se 1 (by rfl) ⟨1321127, by rfl⟩ : syracuseStep 1761503 = 2642255) B2642255
theorem B13558063 : Blo 1760081 13558063 := bstep (se 1 (by rfl) ⟨10168547, by rfl⟩ : syracuseStep 13558063 = 20337095) B20337095
theorem B65126717 : Blo 1760081 65126717 := bstep (se 3 (by rfl) ⟨12211259, by rfl⟩ : syracuseStep 65126717 = 24422519) B24422519
theorem B8913401 : Blo 1760081 8913401 := bstep (se 2 (by rfl) ⟨3342525, by rfl⟩ : syracuseStep 8913401 = 6685051) B6685051
theorem B11289203 : Blo 1760081 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B6685523 : Blo 1760081 6685523 := bstep (se 1 (by rfl) ⟨5014142, by rfl⟩ : syracuseStep 6685523 = 10028285) B10028285
theorem B6685537 : Blo 1760081 6685537 := bstep (se 2 (by rfl) ⟨2507076, by rfl⟩ : syracuseStep 6685537 = 5014153) B5014153
theorem B5014507 : Blo 1760081 5014507 := bstep (se 1 (by rfl) ⟨3760880, by rfl⟩ : syracuseStep 5014507 = 7521761) B7521761
theorem B7521983 : Blo 1760081 7521983 := bstep (se 1 (by rfl) ⟨5641487, by rfl⟩ : syracuseStep 7521983 = 11282975) B11282975
theorem B18065099 : Blo 1760081 18065099 := bstep (se 1 (by rfl) ⟨13548824, by rfl⟩ : syracuseStep 18065099 = 27097649) B27097649
theorem B5941403 : Blo 1760081 5941403 := bstep (se 1 (by rfl) ⟨4456052, by rfl⟩ : syracuseStep 5941403 = 8912105) B8912105
theorem B12053033 : Blo 1760081 12053033 := bstep (se 2 (by rfl) ⟨4519887, by rfl⟩ : syracuseStep 12053033 = 9039775) B9039775
theorem B4229761 : Blo 1760081 4229761 := bstep (se 2 (by rfl) ⟨1586160, by rfl⟩ : syracuseStep 4229761 = 3172321) B3172321
theorem B5941889 : Blo 1760081 5941889 := bstep (se 2 (by rfl) ⟨2228208, by rfl⟩ : syracuseStep 5941889 = 4456417) B4456417
theorem B128486249 : Blo 1760081 128486249 := bstep (se 2 (by rfl) ⟨48182343, by rfl⟩ : syracuseStep 128486249 = 96364687) B96364687
theorem B2641001 : Blo 1760081 2641001 := bstep (se 2 (by rfl) ⟨990375, by rfl⟩ : syracuseStep 2641001 = 1980751) B1980751
theorem B2641103 : Blo 1760081 2641103 := bstep (se 1 (by rfl) ⟨1980827, by rfl⟩ : syracuseStep 2641103 = 3961655) B3961655
theorem B42831287 : Blo 1760081 42831287 := bstep (se 1 (by rfl) ⟨32123465, by rfl⟩ : syracuseStep 42831287 = 64246931) B64246931
theorem B243994045 : Blo 1760081 243994045 := bstep (se 3 (by rfl) ⟨45748883, by rfl⟩ : syracuseStep 243994045 = 91497767) B91497767
theorem B2641439 : Blo 1760081 2641439 := bstep (se 1 (by rfl) ⟨1981079, by rfl⟩ : syracuseStep 2641439 = 3962159) B3962159
theorem B2641577 : Blo 1760081 2641577 := bstep (se 2 (by rfl) ⟨990591, by rfl⟩ : syracuseStep 2641577 = 1981183) B1981183
theorem B2641919 : Blo 1760081 2641919 := bstep (se 1 (by rfl) ⟨1981439, by rfl⟩ : syracuseStep 2641919 = 3962879) B3962879
theorem B4518163 : Blo 1760081 4518163 := bstep (se 1 (by rfl) ⟨3388622, by rfl⟩ : syracuseStep 4518163 = 6777245) B6777245
theorem B6025519 : Blo 1760081 6025519 := bstep (se 1 (by rfl) ⟨4519139, by rfl⟩ : syracuseStep 6025519 = 9038279) B9038279
theorem B4231615 : Blo 1760081 4231615 := bstep (se 1 (by rfl) ⟨3173711, by rfl⟩ : syracuseStep 4231615 = 6347423) B6347423
theorem B2642459 : Blo 1760081 2642459 := bstep (se 1 (by rfl) ⟨1981844, by rfl⟩ : syracuseStep 2642459 = 3963689) B3963689
theorem B12055661 : Blo 1760081 12055661 := bstep (se 3 (by rfl) ⟨2260436, by rfl⟩ : syracuseStep 12055661 = 4520873) B4520873
theorem B2643065 : Blo 1760081 2643065 := bstep (se 2 (by rfl) ⟨991149, by rfl⟩ : syracuseStep 2643065 = 1982299) B1982299
theorem B2643071 : Blo 1760081 2643071 := bstep (se 1 (by rfl) ⟨1982303, by rfl⟩ : syracuseStep 2643071 = 3964607) B3964607
theorem B3962015 : Blo 1760081 3962015 := bstep (se 1 (by rfl) ⟨2971511, by rfl⟩ : syracuseStep 3962015 = 5943023) B5943023
theorem B10851691 : Blo 1760081 10851691 := bstep (se 1 (by rfl) ⟨8138768, by rfl⟩ : syracuseStep 10851691 = 16277537) B16277537
theorem B38090249 : Blo 1760081 38090249 := bstep (se 2 (by rfl) ⟨14283843, by rfl⟩ : syracuseStep 38090249 = 28567687) B28567687
theorem B2971721 : Blo 1760081 2971721 := bstep (se 2 (by rfl) ⟨1114395, by rfl⟩ : syracuseStep 2971721 = 2228791) B2228791
theorem B3962987 : Blo 1760081 3962987 := bstep (se 1 (by rfl) ⟨2972240, by rfl⟩ : syracuseStep 3962987 = 5944481) B5944481
theorem B2972153 : Blo 1760081 2972153 := bstep (se 2 (by rfl) ⟨1114557, by rfl⟩ : syracuseStep 2972153 = 2229115) B2229115
theorem B556759763 : Blo 1760081 556759763 := bstep (se 1 (by rfl) ⟨417569822, by rfl⟩ : syracuseStep 556759763 = 835139645) B835139645
theorem B22567895 : Blo 1760081 22567895 := bstep (se 1 (by rfl) ⟨16925921, by rfl⟩ : syracuseStep 22567895 = 33851843) B33851843
theorem B22322155 : Blo 1760081 22322155 := bstep (se 1 (by rfl) ⟨16741616, by rfl⟩ : syracuseStep 22322155 = 33483233) B33483233
theorem B7142393 : Blo 1760081 7142393 := bstep (se 2 (by rfl) ⟨2678397, by rfl⟩ : syracuseStep 7142393 = 5356795) B5356795
theorem B1981543 : Blo 1760081 1981543 := bstep (se 1 (by rfl) ⟨1486157, by rfl⟩ : syracuseStep 1981543 = 2972315) B2972315
theorem B3964031 : Blo 1760081 3964031 := bstep (se 1 (by rfl) ⟨2973023, by rfl⟩ : syracuseStep 3964031 = 5946047) B5946047
theorem B1760447 : Blo 1760081 1760447 := bstep (se 1 (by rfl) ⟨1320335, by rfl⟩ : syracuseStep 1760447 = 2640671) B2640671
theorem B3964139 : Blo 1760081 3964139 := bstep (se 1 (by rfl) ⟨2973104, by rfl⟩ : syracuseStep 3964139 = 5946209) B5946209
theorem B1760495 : Blo 1760081 1760495 := bstep (se 1 (by rfl) ⟨1320371, by rfl⟩ : syracuseStep 1760495 = 2640743) B2640743
theorem B11287997 : Blo 1760081 11287997 := bstep (se 3 (by rfl) ⟨2116499, by rfl⟩ : syracuseStep 11287997 = 4232999) B4232999
theorem B19037767 : Blo 1760081 19037767 := bstep (se 1 (by rfl) ⟨14278325, by rfl⟩ : syracuseStep 19037767 = 28556651) B28556651
theorem B2973415 : Blo 1760081 2973415 := bstep (se 1 (by rfl) ⟨2230061, by rfl⟩ : syracuseStep 2973415 = 4460123) B4460123
theorem B43417811 : Blo 1760081 43417811 := bstep (se 1 (by rfl) ⟨32563358, by rfl⟩ : syracuseStep 43417811 = 65126717) B65126717
theorem B1761639 : Blo 1760081 1761639 := bstep (se 1 (by rfl) ⟨1321229, by rfl⟩ : syracuseStep 1761639 = 2642459) B2642459
theorem B4457015 : Blo 1760081 4457015 := bstep (se 1 (by rfl) ⟨3342761, by rfl⟩ : syracuseStep 4457015 = 6685523) B6685523
theorem B8037107 : Blo 1760081 8037107 := bstep (se 1 (by rfl) ⟨6027830, by rfl⟩ : syracuseStep 8037107 = 12055661) B12055661
theorem B1762043 : Blo 1760081 1762043 := bstep (se 1 (by rfl) ⟨1321532, by rfl⟩ : syracuseStep 1762043 = 2643065) B2643065
theorem B1762047 : Blo 1760081 1762047 := bstep (se 1 (by rfl) ⟨1321535, by rfl⟩ : syracuseStep 1762047 = 2643071) B2643071
theorem B5014655 : Blo 1760081 5014655 := bstep (se 1 (by rfl) ⟨3760991, by rfl⟩ : syracuseStep 5014655 = 7521983) B7521983
theorem B8914049 : Blo 1760081 8914049 := bstep (se 2 (by rfl) ⟨3342768, by rfl⟩ : syracuseStep 8914049 = 6685537) B6685537
theorem B12043399 : Blo 1760081 12043399 := bstep (se 1 (by rfl) ⟨9032549, by rfl⟩ : syracuseStep 12043399 = 18065099) B18065099
theorem B6686009 : Blo 1760081 6686009 := bstep (se 2 (by rfl) ⟨2507253, by rfl⟩ : syracuseStep 6686009 = 5014507) B5014507
theorem B29762873 : Blo 1760081 29762873 := bstep (se 2 (by rfl) ⟨11161077, by rfl⟩ : syracuseStep 29762873 = 22322155) B22322155
theorem B371173175 : Blo 1760081 371173175 := bstep (se 1 (by rfl) ⟨278379881, by rfl⟩ : syracuseStep 371173175 = 556759763) B556759763
theorem B14468921 : Blo 1760081 14468921 := bstep (se 2 (by rfl) ⟨5425845, by rfl⟩ : syracuseStep 14468921 = 10851691) B10851691
theorem B85657499 : Blo 1760081 85657499 := bstep (se 1 (by rfl) ⟨64243124, by rfl⟩ : syracuseStep 85657499 = 128486249) B128486249
theorem B4761595 : Blo 1760081 4761595 := bstep (se 1 (by rfl) ⟨3571196, by rfl⟩ : syracuseStep 4761595 = 7142393) B7142393
theorem B5942267 : Blo 1760081 5942267 := bstep (se 1 (by rfl) ⟨4456700, by rfl⟩ : syracuseStep 5942267 = 8913401) B8913401
theorem B6024217 : Blo 1760081 6024217 := bstep (se 2 (by rfl) ⟨2259081, by rfl⟩ : syracuseStep 6024217 = 4518163) B4518163
theorem B2641343 : Blo 1760081 2641343 := bstep (se 1 (by rfl) ⟨1981007, by rfl⟩ : syracuseStep 2641343 = 3962015) B3962015
theorem B5639681 : Blo 1760081 5639681 := bstep (se 2 (by rfl) ⟨2114880, by rfl⟩ : syracuseStep 5639681 = 4229761) B4229761
theorem B2641991 : Blo 1760081 2641991 := bstep (se 1 (by rfl) ⟨1981493, by rfl⟩ : syracuseStep 2641991 = 3962987) B3962987
theorem B3960935 : Blo 1760081 3960935 := bstep (se 1 (by rfl) ⟨2970701, by rfl⟩ : syracuseStep 3960935 = 5941403) B5941403
theorem B2642057 : Blo 1760081 2642057 := bstep (se 2 (by rfl) ⟨990771, by rfl⟩ : syracuseStep 2642057 = 1981543) B1981543
theorem B3961259 : Blo 1760081 3961259 := bstep (se 1 (by rfl) ⟨2970944, by rfl⟩ : syracuseStep 3961259 = 5941889) B5941889
theorem B325325393 : Blo 1760081 325325393 := bstep (se 2 (by rfl) ⟨121997022, by rfl⟩ : syracuseStep 325325393 = 243994045) B243994045
theorem B15045263 : Blo 1760081 15045263 := bstep (se 1 (by rfl) ⟨11283947, by rfl⟩ : syracuseStep 15045263 = 22567895) B22567895
theorem B2642687 : Blo 1760081 2642687 := bstep (se 1 (by rfl) ⟨1982015, by rfl⟩ : syracuseStep 2642687 = 3964031) B3964031
theorem B25383689 : Blo 1760081 25383689 := bstep (se 2 (by rfl) ⟨9518883, by rfl⟩ : syracuseStep 25383689 = 19037767) B19037767
theorem B2642759 : Blo 1760081 2642759 := bstep (se 1 (by rfl) ⟨1982069, by rfl⟩ : syracuseStep 2642759 = 3964139) B3964139
theorem B28554191 : Blo 1760081 28554191 := bstep (se 1 (by rfl) ⟨21415643, by rfl⟩ : syracuseStep 28554191 = 42831287) B42831287
theorem B7525331 : Blo 1760081 7525331 := bstep (se 1 (by rfl) ⟨5643998, by rfl⟩ : syracuseStep 7525331 = 11287997) B11287997
theorem B8034025 : Blo 1760081 8034025 := bstep (se 2 (by rfl) ⟨3012759, by rfl⟩ : syracuseStep 8034025 = 6025519) B6025519
theorem B18077417 : Blo 1760081 18077417 := bstep (se 2 (by rfl) ⟨6779031, by rfl⟩ : syracuseStep 18077417 = 13558063) B13558063
theorem B7526135 : Blo 1760081 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B5642153 : Blo 1760081 5642153 := bstep (se 2 (by rfl) ⟨2115807, by rfl⟩ : syracuseStep 5642153 = 4231615) B4231615
theorem B25393499 : Blo 1760081 25393499 := bstep (se 1 (by rfl) ⟨19045124, by rfl⟩ : syracuseStep 25393499 = 38090249) B38090249
theorem B1981147 : Blo 1760081 1981147 := bstep (se 1 (by rfl) ⟨1485860, by rfl⟩ : syracuseStep 1981147 = 2971721) B2971721
theorem B1981435 : Blo 1760081 1981435 := bstep (se 1 (by rfl) ⟨1486076, by rfl⟩ : syracuseStep 1981435 = 2972153) B2972153
theorem B8035355 : Blo 1760081 8035355 := bstep (se 1 (by rfl) ⟨6026516, by rfl⟩ : syracuseStep 8035355 = 12053033) B12053033
theorem B1760667 : Blo 1760081 1760667 := bstep (se 1 (by rfl) ⟨1320500, by rfl⟩ : syracuseStep 1760667 = 2641001) B2641001
theorem B1760735 : Blo 1760081 1760735 := bstep (se 1 (by rfl) ⟨1320551, by rfl⟩ : syracuseStep 1760735 = 2641103) B2641103
theorem B3964553 : Blo 1760081 3964553 := bstep (se 2 (by rfl) ⟨1486707, by rfl⟩ : syracuseStep 3964553 = 2973415) B2973415
theorem B1760959 : Blo 1760081 1760959 := bstep (se 1 (by rfl) ⟨1320719, by rfl⟩ : syracuseStep 1760959 = 2641439) B2641439
theorem B1761051 : Blo 1760081 1761051 := bstep (se 1 (by rfl) ⟨1320788, by rfl⟩ : syracuseStep 1761051 = 2641577) B2641577
theorem B1761279 : Blo 1760081 1761279 := bstep (se 1 (by rfl) ⟨1320959, by rfl⟩ : syracuseStep 1761279 = 2641919) B2641919
theorem B1761327 : Blo 1760081 1761327 := bstep (se 1 (by rfl) ⟨1320995, by rfl⟩ : syracuseStep 1761327 = 2641991) B2641991
theorem B1761371 : Blo 1760081 1761371 := bstep (se 1 (by rfl) ⟨1321028, by rfl⟩ : syracuseStep 1761371 = 2642057) B2642057
theorem B216883595 : Blo 1760081 216883595 := bstep (se 1 (by rfl) ⟨162662696, by rfl⟩ : syracuseStep 216883595 = 325325393) B325325393
theorem B5358071 : Blo 1760081 5358071 := bstep (se 1 (by rfl) ⟨4018553, by rfl⟩ : syracuseStep 5358071 = 8037107) B8037107
theorem B1761791 : Blo 1760081 1761791 := bstep (se 1 (by rfl) ⟨1321343, by rfl⟩ : syracuseStep 1761791 = 2642687) B2642687
theorem B1761839 : Blo 1760081 1761839 := bstep (se 1 (by rfl) ⟨1321379, by rfl⟩ : syracuseStep 1761839 = 2642759) B2642759
theorem B3343103 : Blo 1760081 3343103 := bstep (se 1 (by rfl) ⟨2507327, by rfl⟩ : syracuseStep 3343103 = 5014655) B5014655
theorem B4457339 : Blo 1760081 4457339 := bstep (se 1 (by rfl) ⟨3343004, by rfl⟩ : syracuseStep 4457339 = 6686009) B6686009
theorem B19841915 : Blo 1760081 19841915 := bstep (se 1 (by rfl) ⟨14881436, by rfl⟩ : syracuseStep 19841915 = 29762873) B29762873
theorem B12051611 : Blo 1760081 12051611 := bstep (se 1 (by rfl) ⟨9038708, by rfl⟩ : syracuseStep 12051611 = 18077417) B18077417
theorem B247448783 : Blo 1760081 247448783 := bstep (se 1 (by rfl) ⟨185586587, by rfl⟩ : syracuseStep 247448783 = 371173175) B371173175
theorem B3761435 : Blo 1760081 3761435 := bstep (se 1 (by rfl) ⟨2821076, by rfl⟩ : syracuseStep 3761435 = 5642153) B5642153
theorem B16057865 : Blo 1760081 16057865 := bstep (se 2 (by rfl) ⟨6021699, by rfl⟩ : syracuseStep 16057865 = 12043399) B12043399
theorem B2640623 : Blo 1760081 2640623 := bstep (se 1 (by rfl) ⟨1980467, by rfl⟩ : syracuseStep 2640623 = 3960935) B3960935
theorem B28945207 : Blo 1760081 28945207 := bstep (se 1 (by rfl) ⟨21708905, by rfl⟩ : syracuseStep 28945207 = 43417811) B43417811
theorem B2640839 : Blo 1760081 2640839 := bstep (se 1 (by rfl) ⟨1980629, by rfl⟩ : syracuseStep 2640839 = 3961259) B3961259
theorem B10030175 : Blo 1760081 10030175 := bstep (se 1 (by rfl) ⟨7522631, by rfl⟩ : syracuseStep 10030175 = 15045263) B15045263
theorem B5016887 : Blo 1760081 5016887 := bstep (se 1 (by rfl) ⟨3762665, by rfl⟩ : syracuseStep 5016887 = 7525331) B7525331
theorem B5942699 : Blo 1760081 5942699 := bstep (se 1 (by rfl) ⟨4457024, by rfl⟩ : syracuseStep 5942699 = 8914049) B8914049
theorem B2641529 : Blo 1760081 2641529 := bstep (se 2 (by rfl) ⟨990573, by rfl⟩ : syracuseStep 2641529 = 1981147) B1981147
theorem B5017423 : Blo 1760081 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B9645947 : Blo 1760081 9645947 := bstep (se 1 (by rfl) ⟨7234460, by rfl⟩ : syracuseStep 9645947 = 14468921) B14468921
theorem B2641913 : Blo 1760081 2641913 := bstep (se 2 (by rfl) ⟨990717, by rfl⟩ : syracuseStep 2641913 = 1981435) B1981435
theorem B8032289 : Blo 1760081 8032289 := bstep (se 2 (by rfl) ⟨3012108, by rfl⟩ : syracuseStep 8032289 = 6024217) B6024217
theorem B16928999 : Blo 1760081 16928999 := bstep (se 1 (by rfl) ⟨12696749, by rfl⟩ : syracuseStep 16928999 = 25393499) B25393499
theorem B3961511 : Blo 1760081 3961511 := bstep (se 1 (by rfl) ⟨2971133, by rfl⟩ : syracuseStep 3961511 = 5942267) B5942267
theorem B10712033 : Blo 1760081 10712033 := bstep (se 2 (by rfl) ⟨4017012, by rfl⟩ : syracuseStep 10712033 = 8034025) B8034025
theorem B2643035 : Blo 1760081 2643035 := bstep (se 1 (by rfl) ⟨1982276, by rfl⟩ : syracuseStep 2643035 = 3964553) B3964553
theorem B2971343 : Blo 1760081 2971343 := bstep (se 1 (by rfl) ⟨2228507, by rfl⟩ : syracuseStep 2971343 = 4457015) B4457015
theorem B16922459 : Blo 1760081 16922459 := bstep (se 1 (by rfl) ⟨12691844, by rfl⟩ : syracuseStep 16922459 = 25383689) B25383689
theorem B19036127 : Blo 1760081 19036127 := bstep (se 1 (by rfl) ⟨14277095, by rfl⟩ : syracuseStep 19036127 = 28554191) B28554191
theorem B57104999 : Blo 1760081 57104999 := bstep (se 1 (by rfl) ⟨42828749, by rfl⟩ : syracuseStep 57104999 = 85657499) B85657499
theorem B5356903 : Blo 1760081 5356903 := bstep (se 1 (by rfl) ⟨4017677, by rfl⟩ : syracuseStep 5356903 = 8035355) B8035355
theorem B1760895 : Blo 1760081 1760895 := bstep (se 1 (by rfl) ⟨1320671, by rfl⟩ : syracuseStep 1760895 = 2641343) B2641343
theorem B3759787 : Blo 1760081 3759787 := bstep (se 1 (by rfl) ⟨2819840, by rfl⟩ : syracuseStep 3759787 = 5639681) B5639681
theorem B6348793 : Blo 1760081 6348793 := bstep (se 2 (by rfl) ⟨2380797, by rfl⟩ : syracuseStep 6348793 = 4761595) B4761595
theorem B144589063 : Blo 1760081 144589063 := bstep (se 1 (by rfl) ⟨108441797, by rfl⟩ : syracuseStep 144589063 = 216883595) B216883595
theorem B3572047 : Blo 1760081 3572047 := bstep (se 1 (by rfl) ⟨2679035, by rfl⟩ : syracuseStep 3572047 = 5358071) B5358071
theorem B2228735 : Blo 1760081 2228735 := bstep (se 1 (by rfl) ⟨1671551, by rfl⟩ : syracuseStep 2228735 = 3343103) B3343103
theorem B1762023 : Blo 1760081 1762023 := bstep (se 1 (by rfl) ⟨1321517, by rfl⟩ : syracuseStep 1762023 = 2643035) B2643035
theorem B12690751 : Blo 1760081 12690751 := bstep (se 1 (by rfl) ⟨9518063, by rfl⟩ : syracuseStep 12690751 = 19036127) B19036127
theorem B38069999 : Blo 1760081 38069999 := bstep (se 1 (by rfl) ⟨28552499, by rfl⟩ : syracuseStep 38069999 = 57104999) B57104999
theorem B6686783 : Blo 1760081 6686783 := bstep (se 1 (by rfl) ⟨5015087, by rfl⟩ : syracuseStep 6686783 = 10030175) B10030175
theorem B3344591 : Blo 1760081 3344591 := bstep (se 1 (by rfl) ⟨2508443, by rfl⟩ : syracuseStep 3344591 = 5016887) B5016887
theorem B8465057 : Blo 1760081 8465057 := bstep (se 2 (by rfl) ⟨3174396, by rfl⟩ : syracuseStep 8465057 = 6348793) B6348793
theorem B2641007 : Blo 1760081 2641007 := bstep (se 1 (by rfl) ⟨1980755, by rfl⟩ : syracuseStep 2641007 = 3961511) B3961511
theorem B10030493 : Blo 1760081 10030493 := bstep (se 3 (by rfl) ⟨1880717, by rfl⟩ : syracuseStep 10030493 = 3761435) B3761435
theorem B164965855 : Blo 1760081 164965855 := bstep (se 1 (by rfl) ⟨123724391, by rfl⟩ : syracuseStep 164965855 = 247448783) B247448783
theorem B154374437 : Blo 1760081 154374437 := bstep (se 4 (by rfl) ⟨14472603, by rfl⟩ : syracuseStep 154374437 = 28945207) B28945207
theorem B45126557 : Blo 1760081 45126557 := bstep (se 3 (by rfl) ⟨8461229, by rfl⟩ : syracuseStep 45126557 = 16922459) B16922459
theorem B3961799 : Blo 1760081 3961799 := bstep (se 1 (by rfl) ⟨2971349, by rfl⟩ : syracuseStep 3961799 = 5942699) B5942699
theorem B6689897 : Blo 1760081 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B21419437 : Blo 1760081 21419437 := bstep (se 3 (by rfl) ⟨4016144, by rfl⟩ : syracuseStep 21419437 = 8032289) B8032289
theorem B11285999 : Blo 1760081 11285999 := bstep (se 1 (by rfl) ⟨8464499, by rfl⟩ : syracuseStep 11285999 = 16928999) B16928999
theorem B2971559 : Blo 1760081 2971559 := bstep (se 1 (by rfl) ⟨2228669, by rfl⟩ : syracuseStep 2971559 = 4457339) B4457339
theorem B13227943 : Blo 1760081 13227943 := bstep (se 1 (by rfl) ⟨9920957, by rfl⟩ : syracuseStep 13227943 = 19841915) B19841915
theorem B7141355 : Blo 1760081 7141355 := bstep (se 1 (by rfl) ⟨5356016, by rfl⟩ : syracuseStep 7141355 = 10712033) B10712033
theorem B8034407 : Blo 1760081 8034407 := bstep (se 1 (by rfl) ⟨6025805, by rfl⟩ : syracuseStep 8034407 = 12051611) B12051611
theorem B10705243 : Blo 1760081 10705243 := bstep (se 1 (by rfl) ⟨8028932, by rfl⟩ : syracuseStep 10705243 = 16057865) B16057865
theorem B1980895 : Blo 1760081 1980895 := bstep (se 1 (by rfl) ⟨1485671, by rfl⟩ : syracuseStep 1980895 = 2971343) B2971343
theorem B7142537 : Blo 1760081 7142537 := bstep (se 2 (by rfl) ⟨2678451, by rfl⟩ : syracuseStep 7142537 = 5356903) B5356903
theorem B1760415 : Blo 1760081 1760415 := bstep (se 1 (by rfl) ⟨1320311, by rfl⟩ : syracuseStep 1760415 = 2640623) B2640623
theorem B1760559 : Blo 1760081 1760559 := bstep (se 1 (by rfl) ⟨1320419, by rfl⟩ : syracuseStep 1760559 = 2640839) B2640839
theorem B5013049 : Blo 1760081 5013049 := bstep (se 2 (by rfl) ⟨1879893, by rfl⟩ : syracuseStep 5013049 = 3759787) B3759787
theorem B1761019 : Blo 1760081 1761019 := bstep (se 1 (by rfl) ⟨1320764, by rfl⟩ : syracuseStep 1761019 = 2641529) B2641529
theorem B6430631 : Blo 1760081 6430631 := bstep (se 1 (by rfl) ⟨4822973, by rfl⟩ : syracuseStep 6430631 = 9645947) B9645947
theorem B1761275 : Blo 1760081 1761275 := bstep (se 1 (by rfl) ⟨1320956, by rfl⟩ : syracuseStep 1761275 = 2641913) B2641913
theorem B102916291 : Blo 1760081 102916291 := bstep (se 1 (by rfl) ⟨77187218, by rfl⟩ : syracuseStep 102916291 = 154374437) B154374437
theorem B19046765 : Blo 1760081 19046765 := bstep (se 3 (by rfl) ⟨3571268, by rfl⟩ : syracuseStep 19046765 = 7142537) B7142537
theorem B25379999 : Blo 1760081 25379999 := bstep (se 1 (by rfl) ⟨19034999, by rfl⟩ : syracuseStep 25379999 = 38069999) B38069999
theorem B4760903 : Blo 1760081 4760903 := bstep (se 1 (by rfl) ⟨3570677, by rfl⟩ : syracuseStep 4760903 = 7141355) B7141355
theorem B4457855 : Blo 1760081 4457855 := bstep (se 1 (by rfl) ⟨3343391, by rfl⟩ : syracuseStep 4457855 = 6686783) B6686783
theorem B68593397 : Blo 1760081 68593397 := bstep (se 5 (by rfl) ⟨3215315, by rfl⟩ : syracuseStep 68593397 = 6430631) B6430631
theorem B28559249 : Blo 1760081 28559249 := bstep (se 2 (by rfl) ⟨10709718, by rfl⟩ : syracuseStep 28559249 = 21419437) B21419437
theorem B6686995 : Blo 1760081 6686995 := bstep (se 1 (by rfl) ⟨5015246, by rfl⟩ : syracuseStep 6686995 = 10030493) B10030493
theorem B192785417 : Blo 1760081 192785417 := bstep (se 2 (by rfl) ⟨72294531, by rfl⟩ : syracuseStep 192785417 = 144589063) B144589063
theorem B4762729 : Blo 1760081 4762729 := bstep (se 2 (by rfl) ⟨1786023, by rfl⟩ : syracuseStep 4762729 = 3572047) B3572047
theorem B14273657 : Blo 1760081 14273657 := bstep (se 2 (by rfl) ⟨5352621, by rfl⟩ : syracuseStep 14273657 = 10705243) B10705243
theorem B30084371 : Blo 1760081 30084371 := bstep (se 1 (by rfl) ⟨22563278, by rfl⟩ : syracuseStep 30084371 = 45126557) B45126557
theorem B2641193 : Blo 1760081 2641193 := bstep (se 2 (by rfl) ⟨990447, by rfl⟩ : syracuseStep 2641193 = 1980895) B1980895
theorem B2641199 : Blo 1760081 2641199 := bstep (se 1 (by rfl) ⟨1980899, by rfl⟩ : syracuseStep 2641199 = 3961799) B3961799
theorem B4459931 : Blo 1760081 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B7523999 : Blo 1760081 7523999 := bstep (se 1 (by rfl) ⟨5642999, by rfl⟩ : syracuseStep 7523999 = 11285999) B11285999
theorem B5943293 : Blo 1760081 5943293 := bstep (se 3 (by rfl) ⟨1114367, by rfl⟩ : syracuseStep 5943293 = 2228735) B2228735
theorem B16921001 : Blo 1760081 16921001 := bstep (se 2 (by rfl) ⟨6345375, by rfl⟩ : syracuseStep 16921001 = 12690751) B12690751
theorem B8918909 : Blo 1760081 8918909 := bstep (se 3 (by rfl) ⟨1672295, by rfl⟩ : syracuseStep 8918909 = 3344591) B3344591
theorem B1981039 : Blo 1760081 1981039 := bstep (se 1 (by rfl) ⟨1485779, by rfl⟩ : syracuseStep 1981039 = 2971559) B2971559
theorem B5356271 : Blo 1760081 5356271 := bstep (se 1 (by rfl) ⟨4017203, by rfl⟩ : syracuseStep 5356271 = 8034407) B8034407
theorem B5643371 : Blo 1760081 5643371 := bstep (se 1 (by rfl) ⟨4232528, by rfl⟩ : syracuseStep 5643371 = 8465057) B8465057
theorem B219954473 : Blo 1760081 219954473 := bstep (se 2 (by rfl) ⟨82482927, by rfl⟩ : syracuseStep 219954473 = 164965855) B164965855
theorem B1760671 : Blo 1760081 1760671 := bstep (se 1 (by rfl) ⟨1320503, by rfl⟩ : syracuseStep 1760671 = 2641007) B2641007
theorem B6684065 : Blo 1760081 6684065 := bstep (se 2 (by rfl) ⟨2506524, by rfl⟩ : syracuseStep 6684065 = 5013049) B5013049
theorem B17637257 : Blo 1760081 17637257 := bstep (se 2 (by rfl) ⟨6613971, by rfl⟩ : syracuseStep 17637257 = 13227943) B13227943
theorem B12697843 : Blo 1760081 12697843 := bstep (se 1 (by rfl) ⟨9523382, by rfl⟩ : syracuseStep 12697843 = 19046765) B19046765
theorem B11280667 : Blo 1760081 11280667 := bstep (se 1 (by rfl) ⟨8460500, by rfl⟩ : syracuseStep 11280667 = 16921001) B16921001
theorem B15048989 : Blo 1760081 15048989 := bstep (se 3 (by rfl) ⟨2821685, by rfl⟩ : syracuseStep 15048989 = 5643371) B5643371
theorem B19039499 : Blo 1760081 19039499 := bstep (se 1 (by rfl) ⟨14279624, by rfl⟩ : syracuseStep 19039499 = 28559249) B28559249
theorem B20056247 : Blo 1760081 20056247 := bstep (se 1 (by rfl) ⟨15042185, by rfl⟩ : syracuseStep 20056247 = 30084371) B30084371
theorem B5015999 : Blo 1760081 5015999 := bstep (se 1 (by rfl) ⟨3761999, by rfl⟩ : syracuseStep 5015999 = 7523999) B7523999
theorem B731662901 : Blo 1760081 731662901 := bstep (se 5 (by rfl) ⟨34296698, by rfl⟩ : syracuseStep 731662901 = 68593397) B68593397
theorem B11758171 : Blo 1760081 11758171 := bstep (se 1 (by rfl) ⟨8818628, by rfl⟩ : syracuseStep 11758171 = 17637257) B17637257
theorem B8915993 : Blo 1760081 8915993 := bstep (se 2 (by rfl) ⟨3343497, by rfl⟩ : syracuseStep 8915993 = 6686995) B6686995
theorem B16919999 : Blo 1760081 16919999 := bstep (se 1 (by rfl) ⟨12689999, by rfl⟩ : syracuseStep 16919999 = 25379999) B25379999
theorem B2641385 : Blo 1760081 2641385 := bstep (se 2 (by rfl) ⟨990519, by rfl⟩ : syracuseStep 2641385 = 1981039) B1981039
theorem B9515771 : Blo 1760081 9515771 := bstep (se 1 (by rfl) ⟨7136828, by rfl⟩ : syracuseStep 9515771 = 14273657) B14273657
theorem B3962195 : Blo 1760081 3962195 := bstep (se 1 (by rfl) ⟨2971646, by rfl⟩ : syracuseStep 3962195 = 5943293) B5943293
theorem B137221721 : Blo 1760081 137221721 := bstep (se 2 (by rfl) ⟨51458145, by rfl⟩ : syracuseStep 137221721 = 102916291) B102916291
theorem B25401221 : Blo 1760081 25401221 := bstep (se 4 (by rfl) ⟨2381364, by rfl⟩ : syracuseStep 25401221 = 4762729) B4762729
theorem B12695741 : Blo 1760081 12695741 := bstep (se 3 (by rfl) ⟨2380451, by rfl⟩ : syracuseStep 12695741 = 4760903) B4760903
theorem B2971903 : Blo 1760081 2971903 := bstep (se 1 (by rfl) ⟨2228927, by rfl⟩ : syracuseStep 2971903 = 4457855) B4457855
theorem B5945939 : Blo 1760081 5945939 := bstep (se 1 (by rfl) ⟨4459454, by rfl⟩ : syracuseStep 5945939 = 8918909) B8918909
theorem B3570847 : Blo 1760081 3570847 := bstep (se 1 (by rfl) ⟨2678135, by rfl⟩ : syracuseStep 3570847 = 5356271) B5356271
theorem B128523611 : Blo 1760081 128523611 := bstep (se 1 (by rfl) ⟨96392708, by rfl⟩ : syracuseStep 128523611 = 192785417) B192785417
theorem B1760795 : Blo 1760081 1760795 := bstep (se 1 (by rfl) ⟨1320596, by rfl⟩ : syracuseStep 1760795 = 2641193) B2641193
theorem B146636315 : Blo 1760081 146636315 := bstep (se 1 (by rfl) ⟨109977236, by rfl⟩ : syracuseStep 146636315 = 219954473) B219954473
theorem B1760799 : Blo 1760081 1760799 := bstep (se 1 (by rfl) ⟨1320599, by rfl⟩ : syracuseStep 1760799 = 2641199) B2641199
theorem B2973287 : Blo 1760081 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B4456043 : Blo 1760081 4456043 := bstep (se 1 (by rfl) ⟨3342032, by rfl⟩ : syracuseStep 4456043 = 6684065) B6684065
theorem B15040889 : Blo 1760081 15040889 := bstep (se 2 (by rfl) ⟨5640333, by rfl⟩ : syracuseStep 15040889 = 11280667) B11280667
theorem B91481147 : Blo 1760081 91481147 := bstep (se 1 (by rfl) ⟨68610860, by rfl⟩ : syracuseStep 91481147 = 137221721) B137221721
theorem B16934147 : Blo 1760081 16934147 := bstep (se 1 (by rfl) ⟨12700610, by rfl⟩ : syracuseStep 16934147 = 25401221) B25401221
theorem B13370831 : Blo 1760081 13370831 := bstep (se 1 (by rfl) ⟨10028123, by rfl⟩ : syracuseStep 13370831 = 20056247) B20056247
theorem B8463827 : Blo 1760081 8463827 := bstep (se 1 (by rfl) ⟨6347870, by rfl⟩ : syracuseStep 8463827 = 12695741) B12695741
theorem B3343999 : Blo 1760081 3343999 := bstep (se 1 (by rfl) ⟨2507999, by rfl⟩ : syracuseStep 3343999 = 5015999) B5015999
theorem B85682407 : Blo 1760081 85682407 := bstep (se 1 (by rfl) ⟨64261805, by rfl⟩ : syracuseStep 85682407 = 128523611) B128523611
theorem B97757543 : Blo 1760081 97757543 := bstep (se 1 (by rfl) ⟨73318157, by rfl⟩ : syracuseStep 97757543 = 146636315) B146636315
theorem B6343847 : Blo 1760081 6343847 := bstep (se 1 (by rfl) ⟨4757885, by rfl⟩ : syracuseStep 6343847 = 9515771) B9515771
theorem B12692999 : Blo 1760081 12692999 := bstep (se 1 (by rfl) ⟨9519749, by rfl⟩ : syracuseStep 12692999 = 19039499) B19039499
theorem B2641463 : Blo 1760081 2641463 := bstep (se 1 (by rfl) ⟨1981097, by rfl⟩ : syracuseStep 2641463 = 3962195) B3962195
theorem B5943995 : Blo 1760081 5943995 := bstep (se 1 (by rfl) ⟨4457996, by rfl⟩ : syracuseStep 5943995 = 8915993) B8915993
theorem B2970695 : Blo 1760081 2970695 := bstep (se 1 (by rfl) ⟨2228021, by rfl⟩ : syracuseStep 2970695 = 4456043) B4456043
theorem B10032659 : Blo 1760081 10032659 := bstep (se 1 (by rfl) ⟨7524494, by rfl⟩ : syracuseStep 10032659 = 15048989) B15048989
theorem B16930457 : Blo 1760081 16930457 := bstep (se 2 (by rfl) ⟨6348921, by rfl⟩ : syracuseStep 16930457 = 12697843) B12697843
theorem B3962537 : Blo 1760081 3962537 := bstep (se 2 (by rfl) ⟨1485951, by rfl⟩ : syracuseStep 3962537 = 2971903) B2971903
theorem B15677561 : Blo 1760081 15677561 := bstep (se 2 (by rfl) ⟨5879085, by rfl⟩ : syracuseStep 15677561 = 11758171) B11758171
theorem B19044517 : Blo 1760081 19044517 := bstep (se 4 (by rfl) ⟨1785423, by rfl⟩ : syracuseStep 19044517 = 3570847) B3570847
theorem B487775267 : Blo 1760081 487775267 := bstep (se 1 (by rfl) ⟨365831450, by rfl⟩ : syracuseStep 487775267 = 731662901) B731662901
theorem B3963959 : Blo 1760081 3963959 := bstep (se 1 (by rfl) ⟨2972969, by rfl⟩ : syracuseStep 3963959 = 5945939) B5945939
theorem B11279999 : Blo 1760081 11279999 := bstep (se 1 (by rfl) ⟨8459999, by rfl⟩ : syracuseStep 11279999 = 16919999) B16919999
theorem B1760923 : Blo 1760081 1760923 := bstep (se 1 (by rfl) ⟨1320692, by rfl⟩ : syracuseStep 1760923 = 2641385) B2641385
theorem B1982191 : Blo 1760081 1982191 := bstep (se 1 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 1982191 = 2973287) B2973287
theorem B10027259 : Blo 1760081 10027259 := bstep (se 1 (by rfl) ⟨7520444, by rfl⟩ : syracuseStep 10027259 = 15040889) B15040889
theorem B11289431 : Blo 1760081 11289431 := bstep (se 1 (by rfl) ⟨8467073, by rfl⟩ : syracuseStep 11289431 = 16934147) B16934147
theorem B8913887 : Blo 1760081 8913887 := bstep (se 1 (by rfl) ⟨6685415, by rfl⟩ : syracuseStep 8913887 = 13370831) B13370831
theorem B325183511 : Blo 1760081 325183511 := bstep (se 1 (by rfl) ⟨243887633, by rfl⟩ : syracuseStep 325183511 = 487775267) B487775267
theorem B4229231 : Blo 1760081 4229231 := bstep (se 1 (by rfl) ⟨3171923, by rfl⟩ : syracuseStep 4229231 = 6343847) B6343847
theorem B4458665 : Blo 1760081 4458665 := bstep (se 2 (by rfl) ⟨1671999, by rfl⟩ : syracuseStep 4458665 = 3343999) B3343999
theorem B41806829 : Blo 1760081 41806829 := bstep (se 3 (by rfl) ⟨7838780, by rfl⟩ : syracuseStep 41806829 = 15677561) B15677561
theorem B6688439 : Blo 1760081 6688439 := bstep (se 1 (by rfl) ⟨5016329, by rfl⟩ : syracuseStep 6688439 = 10032659) B10032659
theorem B2641691 : Blo 1760081 2641691 := bstep (se 1 (by rfl) ⟨1981268, by rfl⟩ : syracuseStep 2641691 = 3962537) B3962537
theorem B65171695 : Blo 1760081 65171695 := bstep (se 1 (by rfl) ⟨48878771, by rfl⟩ : syracuseStep 65171695 = 97757543) B97757543
theorem B2642639 : Blo 1760081 2642639 := bstep (se 1 (by rfl) ⟨1981979, by rfl⟩ : syracuseStep 2642639 = 3963959) B3963959
theorem B2642921 : Blo 1760081 2642921 := bstep (se 2 (by rfl) ⟨991095, by rfl⟩ : syracuseStep 2642921 = 1982191) B1982191
theorem B25392689 : Blo 1760081 25392689 := bstep (se 2 (by rfl) ⟨9522258, by rfl⟩ : syracuseStep 25392689 = 19044517) B19044517
theorem B114243209 : Blo 1760081 114243209 := bstep (se 2 (by rfl) ⟨42841203, by rfl⟩ : syracuseStep 114243209 = 85682407) B85682407
theorem B3962663 : Blo 1760081 3962663 := bstep (se 1 (by rfl) ⟨2971997, by rfl⟩ : syracuseStep 3962663 = 5943995) B5943995
theorem B60987431 : Blo 1760081 60987431 := bstep (se 1 (by rfl) ⟨45740573, by rfl⟩ : syracuseStep 60987431 = 91481147) B91481147
theorem B1980463 : Blo 1760081 1980463 := bstep (se 1 (by rfl) ⟨1485347, by rfl⟩ : syracuseStep 1980463 = 2970695) B2970695
theorem B5642551 : Blo 1760081 5642551 := bstep (se 1 (by rfl) ⟨4231913, by rfl⟩ : syracuseStep 5642551 = 8463827) B8463827
theorem B11286971 : Blo 1760081 11286971 := bstep (se 1 (by rfl) ⟨8465228, by rfl⟩ : syracuseStep 11286971 = 16930457) B16930457
theorem B30079997 : Blo 1760081 30079997 := bstep (se 3 (by rfl) ⟨5639999, by rfl⟩ : syracuseStep 30079997 = 11279999) B11279999
theorem B8461999 : Blo 1760081 8461999 := bstep (se 1 (by rfl) ⟨6346499, by rfl⟩ : syracuseStep 8461999 = 12692999) B12692999
theorem B1760975 : Blo 1760081 1760975 := bstep (se 1 (by rfl) ⟨1320731, by rfl⟩ : syracuseStep 1760975 = 2641463) B2641463
theorem B6684839 : Blo 1760081 6684839 := bstep (se 1 (by rfl) ⟨5013629, by rfl⟩ : syracuseStep 6684839 = 10027259) B10027259
theorem B1761759 : Blo 1760081 1761759 := bstep (se 1 (by rfl) ⟨1321319, by rfl⟩ : syracuseStep 1761759 = 2642639) B2642639
theorem B1761947 : Blo 1760081 1761947 := bstep (se 1 (by rfl) ⟨1321460, by rfl⟩ : syracuseStep 1761947 = 2642921) B2642921
theorem B76162139 : Blo 1760081 76162139 := bstep (se 1 (by rfl) ⟨57121604, by rfl⟩ : syracuseStep 76162139 = 114243209) B114243209
theorem B40658287 : Blo 1760081 40658287 := bstep (se 1 (by rfl) ⟨30493715, by rfl⟩ : syracuseStep 40658287 = 60987431) B60987431
theorem B27871219 : Blo 1760081 27871219 := bstep (se 1 (by rfl) ⟨20903414, by rfl⟩ : syracuseStep 27871219 = 41806829) B41806829
theorem B11282665 : Blo 1760081 11282665 := bstep (se 2 (by rfl) ⟨4230999, by rfl⟩ : syracuseStep 11282665 = 8461999) B8461999
theorem B4458959 : Blo 1760081 4458959 := bstep (se 1 (by rfl) ⟨3344219, by rfl⟩ : syracuseStep 4458959 = 6688439) B6688439
theorem B2640617 : Blo 1760081 2640617 := bstep (se 2 (by rfl) ⟨990231, by rfl⟩ : syracuseStep 2640617 = 1980463) B1980463
theorem B86895593 : Blo 1760081 86895593 := bstep (se 2 (by rfl) ⟨32585847, by rfl⟩ : syracuseStep 86895593 = 65171695) B65171695
theorem B7523401 : Blo 1760081 7523401 := bstep (se 2 (by rfl) ⟨2821275, by rfl⟩ : syracuseStep 7523401 = 5642551) B5642551
theorem B5942591 : Blo 1760081 5942591 := bstep (se 1 (by rfl) ⟨4456943, by rfl⟩ : syracuseStep 5942591 = 8913887) B8913887
theorem B16928459 : Blo 1760081 16928459 := bstep (se 1 (by rfl) ⟨12696344, by rfl⟩ : syracuseStep 16928459 = 25392689) B25392689
theorem B2641775 : Blo 1760081 2641775 := bstep (se 1 (by rfl) ⟨1981331, by rfl⟩ : syracuseStep 2641775 = 3962663) B3962663
theorem B216789007 : Blo 1760081 216789007 := bstep (se 1 (by rfl) ⟨162591755, by rfl⟩ : syracuseStep 216789007 = 325183511) B325183511
theorem B7524647 : Blo 1760081 7524647 := bstep (se 1 (by rfl) ⟨5643485, by rfl⟩ : syracuseStep 7524647 = 11286971) B11286971
theorem B11277949 : Blo 1760081 11277949 := bstep (se 3 (by rfl) ⟨2114615, by rfl⟩ : syracuseStep 11277949 = 4229231) B4229231
theorem B7526287 : Blo 1760081 7526287 := bstep (se 1 (by rfl) ⟨5644715, by rfl⟩ : syracuseStep 7526287 = 11289431) B11289431
theorem B2972443 : Blo 1760081 2972443 := bstep (se 1 (by rfl) ⟨2229332, by rfl⟩ : syracuseStep 2972443 = 4458665) B4458665
theorem B20053331 : Blo 1760081 20053331 := bstep (se 1 (by rfl) ⟨15039998, by rfl⟩ : syracuseStep 20053331 = 30079997) B30079997
theorem B1761127 : Blo 1760081 1761127 := bstep (se 1 (by rfl) ⟨1320845, by rfl⟩ : syracuseStep 1761127 = 2641691) B2641691
theorem B4456559 : Blo 1760081 4456559 := bstep (se 1 (by rfl) ⟨3342419, by rfl⟩ : syracuseStep 4456559 = 6684839) B6684839
theorem B50774759 : Blo 1760081 50774759 := bstep (se 1 (by rfl) ⟨38081069, by rfl⟩ : syracuseStep 50774759 = 76162139) B76162139
theorem B37161625 : Blo 1760081 37161625 := bstep (se 2 (by rfl) ⟨13935609, by rfl⟩ : syracuseStep 37161625 = 27871219) B27871219
theorem B5016431 : Blo 1760081 5016431 := bstep (se 1 (by rfl) ⟨3762323, by rfl⟩ : syracuseStep 5016431 = 7524647) B7524647
theorem B15043553 : Blo 1760081 15043553 := bstep (se 2 (by rfl) ⟨5641332, by rfl⟩ : syracuseStep 15043553 = 11282665) B11282665
theorem B10031201 : Blo 1760081 10031201 := bstep (se 2 (by rfl) ⟨3761700, by rfl⟩ : syracuseStep 10031201 = 7523401) B7523401
theorem B54211049 : Blo 1760081 54211049 := bstep (se 2 (by rfl) ⟨20329143, by rfl⟩ : syracuseStep 54211049 = 40658287) B40658287
theorem B57930395 : Blo 1760081 57930395 := bstep (se 1 (by rfl) ⟨43447796, by rfl⟩ : syracuseStep 57930395 = 86895593) B86895593
theorem B15037265 : Blo 1760081 15037265 := bstep (se 2 (by rfl) ⟨5638974, by rfl⟩ : syracuseStep 15037265 = 11277949) B11277949
theorem B3961727 : Blo 1760081 3961727 := bstep (se 1 (by rfl) ⟨2971295, by rfl⟩ : syracuseStep 3961727 = 5942591) B5942591
theorem B11285639 : Blo 1760081 11285639 := bstep (se 1 (by rfl) ⟨8464229, by rfl⟩ : syracuseStep 11285639 = 16928459) B16928459
theorem B289052009 : Blo 1760081 289052009 := bstep (se 2 (by rfl) ⟨108394503, by rfl⟩ : syracuseStep 289052009 = 216789007) B216789007
theorem B3963257 : Blo 1760081 3963257 := bstep (se 2 (by rfl) ⟨1486221, by rfl⟩ : syracuseStep 3963257 = 2972443) B2972443
theorem B2972639 : Blo 1760081 2972639 := bstep (se 1 (by rfl) ⟨2229479, by rfl⟩ : syracuseStep 2972639 = 4458959) B4458959
theorem B1760411 : Blo 1760081 1760411 := bstep (se 1 (by rfl) ⟨1320308, by rfl⟩ : syracuseStep 1760411 = 2640617) B2640617
theorem B13368887 : Blo 1760081 13368887 := bstep (se 1 (by rfl) ⟨10026665, by rfl⟩ : syracuseStep 13368887 = 20053331) B20053331
theorem B10035049 : Blo 1760081 10035049 := bstep (se 2 (by rfl) ⟨3763143, by rfl⟩ : syracuseStep 10035049 = 7526287) B7526287
theorem B1761183 : Blo 1760081 1761183 := bstep (se 1 (by rfl) ⟨1320887, by rfl⟩ : syracuseStep 1761183 = 2641775) B2641775
theorem B33849839 : Blo 1760081 33849839 := bstep (se 1 (by rfl) ⟨25387379, by rfl⟩ : syracuseStep 33849839 = 50774759) B50774759
theorem B192701339 : Blo 1760081 192701339 := bstep (se 1 (by rfl) ⟨144526004, by rfl⟩ : syracuseStep 192701339 = 289052009) B289052009
theorem B10029035 : Blo 1760081 10029035 := bstep (se 1 (by rfl) ⟨7521776, by rfl⟩ : syracuseStep 10029035 = 15043553) B15043553
theorem B13380065 : Blo 1760081 13380065 := bstep (se 2 (by rfl) ⟨5017524, by rfl⟩ : syracuseStep 13380065 = 10035049) B10035049
theorem B6687467 : Blo 1760081 6687467 := bstep (se 1 (by rfl) ⟨5015600, by rfl⟩ : syracuseStep 6687467 = 10031201) B10031201
theorem B2641151 : Blo 1760081 2641151 := bstep (se 1 (by rfl) ⟨1980863, by rfl⟩ : syracuseStep 2641151 = 3961727) B3961727
theorem B7523759 : Blo 1760081 7523759 := bstep (se 1 (by rfl) ⟨5642819, by rfl⟩ : syracuseStep 7523759 = 11285639) B11285639
theorem B49548833 : Blo 1760081 49548833 := bstep (se 2 (by rfl) ⟨18580812, by rfl⟩ : syracuseStep 49548833 = 37161625) B37161625
theorem B2642171 : Blo 1760081 2642171 := bstep (se 1 (by rfl) ⟨1981628, by rfl⟩ : syracuseStep 2642171 = 3963257) B3963257
theorem B154481053 : Blo 1760081 154481053 := bstep (se 3 (by rfl) ⟨28965197, by rfl⟩ : syracuseStep 154481053 = 57930395) B57930395
theorem B2971039 : Blo 1760081 2971039 := bstep (se 1 (by rfl) ⟨2228279, by rfl⟩ : syracuseStep 2971039 = 4456559) B4456559
theorem B36140699 : Blo 1760081 36140699 := bstep (se 1 (by rfl) ⟨27105524, by rfl⟩ : syracuseStep 36140699 = 54211049) B54211049
theorem B10024843 : Blo 1760081 10024843 := bstep (se 1 (by rfl) ⟨7518632, by rfl⟩ : syracuseStep 10024843 = 15037265) B15037265
theorem B1981759 : Blo 1760081 1981759 := bstep (se 1 (by rfl) ⟨1486319, by rfl⟩ : syracuseStep 1981759 = 2972639) B2972639
theorem B13377149 : Blo 1760081 13377149 := bstep (se 3 (by rfl) ⟨2508215, by rfl⟩ : syracuseStep 13377149 = 5016431) B5016431
theorem B8912591 : Blo 1760081 8912591 := bstep (se 1 (by rfl) ⟨6684443, by rfl⟩ : syracuseStep 8912591 = 13368887) B13368887
theorem B1761447 : Blo 1760081 1761447 := bstep (se 1 (by rfl) ⟨1321085, by rfl⟩ : syracuseStep 1761447 = 2642171) B2642171
theorem B128467559 : Blo 1760081 128467559 := bstep (se 1 (by rfl) ⟨96350669, by rfl⟩ : syracuseStep 128467559 = 192701339) B192701339
theorem B6686023 : Blo 1760081 6686023 := bstep (se 1 (by rfl) ⟨5014517, by rfl⟩ : syracuseStep 6686023 = 10029035) B10029035
theorem B4458311 : Blo 1760081 4458311 := bstep (se 1 (by rfl) ⟨3343733, by rfl⟩ : syracuseStep 4458311 = 6687467) B6687467
theorem B5015839 : Blo 1760081 5015839 := bstep (se 1 (by rfl) ⟨3761879, by rfl⟩ : syracuseStep 5015839 = 7523759) B7523759
theorem B33032555 : Blo 1760081 33032555 := bstep (se 1 (by rfl) ⟨24774416, by rfl⟩ : syracuseStep 33032555 = 49548833) B49548833
theorem B5941727 : Blo 1760081 5941727 := bstep (se 1 (by rfl) ⟨4456295, by rfl⟩ : syracuseStep 5941727 = 8912591) B8912591
theorem B205974737 : Blo 1760081 205974737 := bstep (se 2 (by rfl) ⟨77240526, by rfl⟩ : syracuseStep 205974737 = 154481053) B154481053
theorem B96375197 : Blo 1760081 96375197 := bstep (se 3 (by rfl) ⟨18070349, by rfl⟩ : syracuseStep 96375197 = 36140699) B36140699
theorem B2642345 : Blo 1760081 2642345 := bstep (se 2 (by rfl) ⟨990879, by rfl⟩ : syracuseStep 2642345 = 1981759) B1981759
theorem B3961385 : Blo 1760081 3961385 := bstep (se 2 (by rfl) ⟨1485519, by rfl⟩ : syracuseStep 3961385 = 2971039) B2971039
theorem B8918099 : Blo 1760081 8918099 := bstep (se 1 (by rfl) ⟨6688574, by rfl⟩ : syracuseStep 8918099 = 13377149) B13377149
theorem B13366457 : Blo 1760081 13366457 := bstep (se 2 (by rfl) ⟨5012421, by rfl⟩ : syracuseStep 13366457 = 10024843) B10024843
theorem B22566559 : Blo 1760081 22566559 := bstep (se 1 (by rfl) ⟨16924919, by rfl⟩ : syracuseStep 22566559 = 33849839) B33849839
theorem B8920043 : Blo 1760081 8920043 := bstep (se 1 (by rfl) ⟨6690032, by rfl⟩ : syracuseStep 8920043 = 13380065) B13380065
theorem B1760767 : Blo 1760081 1760767 := bstep (se 1 (by rfl) ⟨1320575, by rfl⟩ : syracuseStep 1760767 = 2641151) B2641151
theorem B64250131 : Blo 1760081 64250131 := bstep (se 1 (by rfl) ⟨48187598, by rfl⟩ : syracuseStep 64250131 = 96375197) B96375197
theorem B1761563 : Blo 1760081 1761563 := bstep (se 1 (by rfl) ⟨1321172, by rfl⟩ : syracuseStep 1761563 = 2642345) B2642345
theorem B22021703 : Blo 1760081 22021703 := bstep (se 1 (by rfl) ⟨16516277, by rfl⟩ : syracuseStep 22021703 = 33032555) B33032555
theorem B8914697 : Blo 1760081 8914697 := bstep (se 2 (by rfl) ⟨3343011, by rfl⟩ : syracuseStep 8914697 = 6686023) B6686023
theorem B137316491 : Blo 1760081 137316491 := bstep (se 1 (by rfl) ⟨102987368, by rfl⟩ : syracuseStep 137316491 = 205974737) B205974737
theorem B2640923 : Blo 1760081 2640923 := bstep (se 1 (by rfl) ⟨1980692, by rfl⟩ : syracuseStep 2640923 = 3961385) B3961385
theorem B6687785 : Blo 1760081 6687785 := bstep (se 2 (by rfl) ⟨2507919, by rfl⟩ : syracuseStep 6687785 = 5015839) B5015839
theorem B3961151 : Blo 1760081 3961151 := bstep (se 1 (by rfl) ⟨2970863, by rfl⟩ : syracuseStep 3961151 = 5941727) B5941727
theorem B85645039 : Blo 1760081 85645039 := bstep (se 1 (by rfl) ⟨64233779, by rfl⟩ : syracuseStep 85645039 = 128467559) B128467559
theorem B5945399 : Blo 1760081 5945399 := bstep (se 1 (by rfl) ⟨4459049, by rfl⟩ : syracuseStep 5945399 = 8918099) B8918099
theorem B8910971 : Blo 1760081 8910971 := bstep (se 1 (by rfl) ⟨6683228, by rfl⟩ : syracuseStep 8910971 = 13366457) B13366457
theorem B2972207 : Blo 1760081 2972207 := bstep (se 1 (by rfl) ⟨2229155, by rfl⟩ : syracuseStep 2972207 = 4458311) B4458311
theorem B5946695 : Blo 1760081 5946695 := bstep (se 1 (by rfl) ⟨4460021, by rfl⟩ : syracuseStep 5946695 = 8920043) B8920043
theorem B30088745 : Blo 1760081 30088745 := bstep (se 2 (by rfl) ⟨11283279, by rfl⟩ : syracuseStep 30088745 = 22566559) B22566559
theorem B14681135 : Blo 1760081 14681135 := bstep (se 1 (by rfl) ⟨11010851, by rfl⟩ : syracuseStep 14681135 = 22021703) B22021703
theorem B5940647 : Blo 1760081 5940647 := bstep (se 1 (by rfl) ⟨4455485, by rfl⟩ : syracuseStep 5940647 = 8910971) B8910971
theorem B4458523 : Blo 1760081 4458523 := bstep (se 1 (by rfl) ⟨3343892, by rfl⟩ : syracuseStep 4458523 = 6687785) B6687785
theorem B2640767 : Blo 1760081 2640767 := bstep (se 1 (by rfl) ⟨1980575, by rfl⟩ : syracuseStep 2640767 = 3961151) B3961151
theorem B85666841 : Blo 1760081 85666841 := bstep (se 2 (by rfl) ⟨32125065, by rfl⟩ : syracuseStep 85666841 = 64250131) B64250131
theorem B5943131 : Blo 1760081 5943131 := bstep (se 1 (by rfl) ⟨4457348, by rfl⟩ : syracuseStep 5943131 = 8914697) B8914697
theorem B114193385 : Blo 1760081 114193385 := bstep (se 2 (by rfl) ⟨42822519, by rfl⟩ : syracuseStep 114193385 = 85645039) B85645039
theorem B20059163 : Blo 1760081 20059163 := bstep (se 1 (by rfl) ⟨15044372, by rfl⟩ : syracuseStep 20059163 = 30088745) B30088745
theorem B3963599 : Blo 1760081 3963599 := bstep (se 1 (by rfl) ⟨2972699, by rfl⟩ : syracuseStep 3963599 = 5945399) B5945399
theorem B91544327 : Blo 1760081 91544327 := bstep (se 1 (by rfl) ⟨68658245, by rfl⟩ : syracuseStep 91544327 = 137316491) B137316491
theorem B1981471 : Blo 1760081 1981471 := bstep (se 1 (by rfl) ⟨1486103, by rfl⟩ : syracuseStep 1981471 = 2972207) B2972207
theorem B1760615 : Blo 1760081 1760615 := bstep (se 1 (by rfl) ⟨1320461, by rfl⟩ : syracuseStep 1760615 = 2640923) B2640923
theorem B3964463 : Blo 1760081 3964463 := bstep (se 1 (by rfl) ⟨2973347, by rfl⟩ : syracuseStep 3964463 = 5946695) B5946695
theorem B39149693 : Blo 1760081 39149693 := bstep (se 3 (by rfl) ⟨7340567, by rfl⟩ : syracuseStep 39149693 = 14681135) B14681135
theorem B76128923 : Blo 1760081 76128923 := bstep (se 1 (by rfl) ⟨57096692, by rfl⟩ : syracuseStep 76128923 = 114193385) B114193385
theorem B13372775 : Blo 1760081 13372775 := bstep (se 1 (by rfl) ⟨10029581, by rfl⟩ : syracuseStep 13372775 = 20059163) B20059163
theorem B3960431 : Blo 1760081 3960431 := bstep (se 1 (by rfl) ⟨2970323, by rfl⟩ : syracuseStep 3960431 = 5940647) B5940647
theorem B2641961 : Blo 1760081 2641961 := bstep (se 2 (by rfl) ⟨990735, by rfl⟩ : syracuseStep 2641961 = 1981471) B1981471
theorem B2642399 : Blo 1760081 2642399 := bstep (se 1 (by rfl) ⟨1981799, by rfl⟩ : syracuseStep 2642399 = 3963599) B3963599
theorem B57111227 : Blo 1760081 57111227 := bstep (se 1 (by rfl) ⟨42833420, by rfl⟩ : syracuseStep 57111227 = 85666841) B85666841
theorem B2642975 : Blo 1760081 2642975 := bstep (se 1 (by rfl) ⟨1982231, by rfl⟩ : syracuseStep 2642975 = 3964463) B3964463
theorem B3962087 : Blo 1760081 3962087 := bstep (se 1 (by rfl) ⟨2971565, by rfl⟩ : syracuseStep 3962087 = 5943131) B5943131
theorem B5944697 : Blo 1760081 5944697 := bstep (se 2 (by rfl) ⟨2229261, by rfl⟩ : syracuseStep 5944697 = 4458523) B4458523
theorem B61029551 : Blo 1760081 61029551 := bstep (se 1 (by rfl) ⟨45772163, by rfl⟩ : syracuseStep 61029551 = 91544327) B91544327
theorem B1760511 : Blo 1760081 1760511 := bstep (se 1 (by rfl) ⟨1320383, by rfl⟩ : syracuseStep 1760511 = 2640767) B2640767
theorem B1761307 : Blo 1760081 1761307 := bstep (se 1 (by rfl) ⟨1320980, by rfl⟩ : syracuseStep 1761307 = 2641961) B2641961
theorem B26099795 : Blo 1760081 26099795 := bstep (se 1 (by rfl) ⟨19574846, by rfl⟩ : syracuseStep 26099795 = 39149693) B39149693
theorem B1761599 : Blo 1760081 1761599 := bstep (se 1 (by rfl) ⟨1321199, by rfl⟩ : syracuseStep 1761599 = 2642399) B2642399
theorem B1761983 : Blo 1760081 1761983 := bstep (se 1 (by rfl) ⟨1321487, by rfl⟩ : syracuseStep 1761983 = 2642975) B2642975
theorem B8915183 : Blo 1760081 8915183 := bstep (se 1 (by rfl) ⟨6686387, by rfl⟩ : syracuseStep 8915183 = 13372775) B13372775
theorem B2640287 : Blo 1760081 2640287 := bstep (se 1 (by rfl) ⟨1980215, by rfl⟩ : syracuseStep 2640287 = 3960431) B3960431
theorem B50752615 : Blo 1760081 50752615 := bstep (se 1 (by rfl) ⟨38064461, by rfl⟩ : syracuseStep 50752615 = 76128923) B76128923
theorem B162745469 : Blo 1760081 162745469 := bstep (se 3 (by rfl) ⟨30514775, by rfl⟩ : syracuseStep 162745469 = 61029551) B61029551
theorem B2641391 : Blo 1760081 2641391 := bstep (se 1 (by rfl) ⟨1981043, by rfl⟩ : syracuseStep 2641391 = 3962087) B3962087
theorem B38074151 : Blo 1760081 38074151 := bstep (se 1 (by rfl) ⟨28555613, by rfl⟩ : syracuseStep 38074151 = 57111227) B57111227
theorem B3963131 : Blo 1760081 3963131 := bstep (se 1 (by rfl) ⟨2972348, by rfl⟩ : syracuseStep 3963131 = 5944697) B5944697
theorem B17399863 : Blo 1760081 17399863 := bstep (se 1 (by rfl) ⟨13049897, by rfl⟩ : syracuseStep 17399863 = 26099795) B26099795
theorem B108496979 : Blo 1760081 108496979 := bstep (se 1 (by rfl) ⟨81372734, by rfl⟩ : syracuseStep 108496979 = 162745469) B162745469
theorem B25382767 : Blo 1760081 25382767 := bstep (se 1 (by rfl) ⟨19037075, by rfl⟩ : syracuseStep 25382767 = 38074151) B38074151
theorem B67670153 : Blo 1760081 67670153 := bstep (se 2 (by rfl) ⟨25376307, by rfl⟩ : syracuseStep 67670153 = 50752615) B50752615
theorem B5943455 : Blo 1760081 5943455 := bstep (se 1 (by rfl) ⟨4457591, by rfl⟩ : syracuseStep 5943455 = 8915183) B8915183
theorem B2642087 : Blo 1760081 2642087 := bstep (se 1 (by rfl) ⟨1981565, by rfl⟩ : syracuseStep 2642087 = 3963131) B3963131
theorem B1760191 : Blo 1760081 1760191 := bstep (se 1 (by rfl) ⟨1320143, by rfl⟩ : syracuseStep 1760191 = 2640287) B2640287
theorem B1760927 : Blo 1760081 1760927 := bstep (se 1 (by rfl) ⟨1320695, by rfl⟩ : syracuseStep 1760927 = 2641391) B2641391
theorem B23199817 : Blo 1760081 23199817 := bstep (se 2 (by rfl) ⟨8699931, by rfl⟩ : syracuseStep 23199817 = 17399863) B17399863
theorem B45113435 : Blo 1760081 45113435 := bstep (se 1 (by rfl) ⟨33835076, by rfl⟩ : syracuseStep 45113435 = 67670153) B67670153
theorem B1761391 : Blo 1760081 1761391 := bstep (se 1 (by rfl) ⟨1321043, by rfl⟩ : syracuseStep 1761391 = 2642087) B2642087
theorem B33843689 : Blo 1760081 33843689 := bstep (se 2 (by rfl) ⟨12691383, by rfl⟩ : syracuseStep 33843689 = 25382767) B25382767
theorem B72331319 : Blo 1760081 72331319 := bstep (se 1 (by rfl) ⟨54248489, by rfl⟩ : syracuseStep 72331319 = 108496979) B108496979
theorem B3962303 : Blo 1760081 3962303 := bstep (se 1 (by rfl) ⟨2971727, by rfl⟩ : syracuseStep 3962303 = 5943455) B5943455
theorem B30933089 : Blo 1760081 30933089 := bstep (se 2 (by rfl) ⟨11599908, by rfl⟩ : syracuseStep 30933089 = 23199817) B23199817
theorem B22562459 : Blo 1760081 22562459 := bstep (se 1 (by rfl) ⟨16921844, by rfl⟩ : syracuseStep 22562459 = 33843689) B33843689
theorem B48220879 : Blo 1760081 48220879 := bstep (se 1 (by rfl) ⟨36165659, by rfl⟩ : syracuseStep 48220879 = 72331319) B72331319
theorem B30075623 : Blo 1760081 30075623 := bstep (se 1 (by rfl) ⟨22556717, by rfl⟩ : syracuseStep 30075623 = 45113435) B45113435
theorem B2641535 : Blo 1760081 2641535 := bstep (se 1 (by rfl) ⟨1981151, by rfl⟩ : syracuseStep 2641535 = 3962303) B3962303
theorem B15041639 : Blo 1760081 15041639 := bstep (se 1 (by rfl) ⟨11281229, by rfl⟩ : syracuseStep 15041639 = 22562459) B22562459
theorem B20622059 : Blo 1760081 20622059 := bstep (se 1 (by rfl) ⟨15466544, by rfl⟩ : syracuseStep 20622059 = 30933089) B30933089
theorem B64294505 : Blo 1760081 64294505 := bstep (se 2 (by rfl) ⟨24110439, by rfl⟩ : syracuseStep 64294505 = 48220879) B48220879
theorem B20050415 : Blo 1760081 20050415 := bstep (se 1 (by rfl) ⟨15037811, by rfl⟩ : syracuseStep 20050415 = 30075623) B30075623
theorem B1761023 : Blo 1760081 1761023 := bstep (se 1 (by rfl) ⟨1320767, by rfl⟩ : syracuseStep 1761023 = 2641535) B2641535
theorem B10027759 : Blo 1760081 10027759 := bstep (se 1 (by rfl) ⟨7520819, by rfl⟩ : syracuseStep 10027759 = 15041639) B15041639
theorem B13748039 : Blo 1760081 13748039 := bstep (se 1 (by rfl) ⟨10311029, by rfl⟩ : syracuseStep 13748039 = 20622059) B20622059
theorem B42863003 : Blo 1760081 42863003 := bstep (se 1 (by rfl) ⟨32147252, by rfl⟩ : syracuseStep 42863003 = 64294505) B64294505
theorem B13366943 : Blo 1760081 13366943 := bstep (se 1 (by rfl) ⟨10025207, by rfl⟩ : syracuseStep 13366943 = 20050415) B20050415
theorem B13370345 : Blo 1760081 13370345 := bstep (se 2 (by rfl) ⟨5013879, by rfl⟩ : syracuseStep 13370345 = 10027759) B10027759
theorem B28575335 : Blo 1760081 28575335 := bstep (se 1 (by rfl) ⟨21431501, by rfl⟩ : syracuseStep 28575335 = 42863003) B42863003
theorem B8911295 : Blo 1760081 8911295 := bstep (se 1 (by rfl) ⟨6683471, by rfl⟩ : syracuseStep 8911295 = 13366943) B13366943
theorem B9165359 : Blo 1760081 9165359 := bstep (se 1 (by rfl) ⟨6874019, by rfl⟩ : syracuseStep 9165359 = 13748039) B13748039
theorem B8913563 : Blo 1760081 8913563 := bstep (se 1 (by rfl) ⟨6685172, by rfl⟩ : syracuseStep 8913563 = 13370345) B13370345
theorem B5940863 : Blo 1760081 5940863 := bstep (se 1 (by rfl) ⟨4455647, by rfl⟩ : syracuseStep 5940863 = 8911295) B8911295
theorem B19050223 : Blo 1760081 19050223 := bstep (se 1 (by rfl) ⟨14287667, by rfl⟩ : syracuseStep 19050223 = 28575335) B28575335
theorem B6110239 : Blo 1760081 6110239 := bstep (se 1 (by rfl) ⟨4582679, by rfl⟩ : syracuseStep 6110239 = 9165359) B9165359
theorem B5942375 : Blo 1760081 5942375 := bstep (se 1 (by rfl) ⟨4456781, by rfl⟩ : syracuseStep 5942375 = 8913563) B8913563
theorem B3960575 : Blo 1760081 3960575 := bstep (se 1 (by rfl) ⟨2970431, by rfl⟩ : syracuseStep 3960575 = 5940863) B5940863
theorem B8146985 : Blo 1760081 8146985 := bstep (se 2 (by rfl) ⟨3055119, by rfl⟩ : syracuseStep 8146985 = 6110239) B6110239
theorem B25400297 : Blo 1760081 25400297 := bstep (se 2 (by rfl) ⟨9525111, by rfl⟩ : syracuseStep 25400297 = 19050223) B19050223
theorem B21725293 : Blo 1760081 21725293 := bstep (se 3 (by rfl) ⟨4073492, by rfl⟩ : syracuseStep 21725293 = 8146985) B8146985
theorem B16933531 : Blo 1760081 16933531 := bstep (se 1 (by rfl) ⟨12700148, by rfl⟩ : syracuseStep 16933531 = 25400297) B25400297
theorem B2640383 : Blo 1760081 2640383 := bstep (se 1 (by rfl) ⟨1980287, by rfl⟩ : syracuseStep 2640383 = 3960575) B3960575
theorem B3961583 : Blo 1760081 3961583 := bstep (se 1 (by rfl) ⟨2971187, by rfl⟩ : syracuseStep 3961583 = 5942375) B5942375
theorem B28967057 : Blo 1760081 28967057 := bstep (se 2 (by rfl) ⟨10862646, by rfl⟩ : syracuseStep 28967057 = 21725293) B21725293
theorem B22578041 : Blo 1760081 22578041 := bstep (se 2 (by rfl) ⟨8466765, by rfl⟩ : syracuseStep 22578041 = 16933531) B16933531
theorem B2641055 : Blo 1760081 2641055 := bstep (se 1 (by rfl) ⟨1980791, by rfl⟩ : syracuseStep 2641055 = 3961583) B3961583
theorem B1760255 : Blo 1760081 1760255 := bstep (se 1 (by rfl) ⟨1320191, by rfl⟩ : syracuseStep 1760255 = 2640383) B2640383
theorem B19311371 : Blo 1760081 19311371 := bstep (se 1 (by rfl) ⟨14483528, by rfl⟩ : syracuseStep 19311371 = 28967057) B28967057
theorem B15052027 : Blo 1760081 15052027 := bstep (se 1 (by rfl) ⟨11289020, by rfl⟩ : syracuseStep 15052027 = 22578041) B22578041
theorem B1760703 : Blo 1760081 1760703 := bstep (se 1 (by rfl) ⟨1320527, by rfl⟩ : syracuseStep 1760703 = 2641055) B2641055
theorem B12874247 : Blo 1760081 12874247 := bstep (se 1 (by rfl) ⟨9655685, by rfl⟩ : syracuseStep 12874247 = 19311371) B19311371
theorem B20069369 : Blo 1760081 20069369 := bstep (se 2 (by rfl) ⟨7526013, by rfl⟩ : syracuseStep 20069369 = 15052027) B15052027
theorem B13379579 : Blo 1760081 13379579 := bstep (se 1 (by rfl) ⟨10034684, by rfl⟩ : syracuseStep 13379579 = 20069369) B20069369
theorem B8582831 : Blo 1760081 8582831 := bstep (se 1 (by rfl) ⟨6437123, by rfl⟩ : syracuseStep 8582831 = 12874247) B12874247
theorem B5721887 : Blo 1760081 5721887 := bstep (se 1 (by rfl) ⟨4291415, by rfl⟩ : syracuseStep 5721887 = 8582831) B8582831
theorem B8919719 : Blo 1760081 8919719 := bstep (se 1 (by rfl) ⟨6689789, by rfl⟩ : syracuseStep 8919719 = 13379579) B13379579
theorem B15258365 : Blo 1760081 15258365 := bstep (se 3 (by rfl) ⟨2860943, by rfl⟩ : syracuseStep 15258365 = 5721887) B5721887
theorem B5946479 : Blo 1760081 5946479 := bstep (se 1 (by rfl) ⟨4459859, by rfl⟩ : syracuseStep 5946479 = 8919719) B8919719
theorem B10172243 : Blo 1760081 10172243 := bstep (se 1 (by rfl) ⟨7629182, by rfl⟩ : syracuseStep 10172243 = 15258365) B15258365
theorem B3964319 : Blo 1760081 3964319 := bstep (se 1 (by rfl) ⟨2973239, by rfl⟩ : syracuseStep 3964319 = 5946479) B5946479
theorem B2642879 : Blo 1760081 2642879 := bstep (se 1 (by rfl) ⟨1982159, by rfl⟩ : syracuseStep 2642879 = 3964319) B3964319
theorem B6781495 : Blo 1760081 6781495 := bstep (se 1 (by rfl) ⟨5086121, by rfl⟩ : syracuseStep 6781495 = 10172243) B10172243
theorem B1761919 : Blo 1760081 1761919 := bstep (se 1 (by rfl) ⟨1321439, by rfl⟩ : syracuseStep 1761919 = 2642879) B2642879
theorem B9041993 : Blo 1760081 9041993 := bstep (se 2 (by rfl) ⟨3390747, by rfl⟩ : syracuseStep 9041993 = 6781495) B6781495
theorem B6027995 : Blo 1760081 6027995 := bstep (se 1 (by rfl) ⟨4520996, by rfl⟩ : syracuseStep 6027995 = 9041993) B9041993
theorem B4018663 : Blo 1760081 4018663 := bstep (se 1 (by rfl) ⟨3013997, by rfl⟩ : syracuseStep 4018663 = 6027995) B6027995
theorem B5358217 : Blo 1760081 5358217 := bstep (se 2 (by rfl) ⟨2009331, by rfl⟩ : syracuseStep 5358217 = 4018663) B4018663
theorem B7144289 : Blo 1760081 7144289 := bstep (se 2 (by rfl) ⟨2679108, by rfl⟩ : syracuseStep 7144289 = 5358217) B5358217
theorem B4762859 : Blo 1760081 4762859 := bstep (se 1 (by rfl) ⟨3572144, by rfl⟩ : syracuseStep 4762859 = 7144289) B7144289
theorem B12700957 : Blo 1760081 12700957 := bstep (se 3 (by rfl) ⟨2381429, by rfl⟩ : syracuseStep 12700957 = 4762859) B4762859
theorem B16934609 : Blo 1760081 16934609 := bstep (se 2 (by rfl) ⟨6350478, by rfl⟩ : syracuseStep 16934609 = 12700957) B12700957
theorem B11289739 : Blo 1760081 11289739 := bstep (se 1 (by rfl) ⟨8467304, by rfl⟩ : syracuseStep 11289739 = 16934609) B16934609
theorem B15052985 : Blo 1760081 15052985 := bstep (se 2 (by rfl) ⟨5644869, by rfl⟩ : syracuseStep 15052985 = 11289739) B11289739
theorem B10035323 : Blo 1760081 10035323 := bstep (se 1 (by rfl) ⟨7526492, by rfl⟩ : syracuseStep 10035323 = 15052985) B15052985
theorem B6690215 : Blo 1760081 6690215 := bstep (se 1 (by rfl) ⟨5017661, by rfl⟩ : syracuseStep 6690215 = 10035323) B10035323
theorem B4460143 : Blo 1760081 4460143 := bstep (se 1 (by rfl) ⟨3345107, by rfl⟩ : syracuseStep 4460143 = 6690215) B6690215
theorem B5946857 : Blo 1760081 5946857 := bstep (se 2 (by rfl) ⟨2230071, by rfl⟩ : syracuseStep 5946857 = 4460143) B4460143
theorem B3964571 : Blo 1760081 3964571 := bstep (se 1 (by rfl) ⟨2973428, by rfl⟩ : syracuseStep 3964571 = 5946857) B5946857
theorem B2643047 : Blo 1760081 2643047 := bstep (se 1 (by rfl) ⟨1982285, by rfl⟩ : syracuseStep 2643047 = 3964571) B3964571
theorem B1762031 : Blo 1760081 1762031 := bstep (se 1 (by rfl) ⟨1321523, by rfl⟩ : syracuseStep 1762031 = 2643047) B2643047

theorem C0 (j : ℕ) (h1 : 440020 ≤ j) (h2 : j ≤ 440519) : Blo 1760081 (4 * j + 3) := by
  interval_cases j
  · exact B1760083
  · exact B1760087
  · exact B1760091
  · exact B1760095
  · exact B1760099
  · exact B1760103
  · exact B1760107
  · exact B1760111
  · exact B1760115
  · exact B1760119
  · exact B1760123
  · exact B1760127
  · exact B1760131
  · exact B1760135
  · exact B1760139
  · exact B1760143
  · exact B1760147
  · exact B1760151
  · exact B1760155
  · exact B1760159
  · exact B1760163
  · exact B1760167
  · exact B1760171
  · exact B1760175
  · exact B1760179
  · exact B1760183
  · exact B1760187
  · exact B1760191
  · exact B1760195
  · exact B1760199
  · exact B1760203
  · exact B1760207
  · exact B1760211
  · exact B1760215
  · exact B1760219
  · exact B1760223
  · exact B1760227
  · exact B1760231
  · exact B1760235
  · exact B1760239
  · exact B1760243
  · exact B1760247
  · exact B1760251
  · exact B1760255
  · exact B1760259
  · exact B1760263
  · exact B1760267
  · exact B1760271
  · exact B1760275
  · exact B1760279
  · exact B1760283
  · exact B1760287
  · exact B1760291
  · exact B1760295
  · exact B1760299
  · exact B1760303
  · exact B1760307
  · exact B1760311
  · exact B1760315
  · exact B1760319
  · exact B1760323
  · exact B1760327
  · exact B1760331
  · exact B1760335
  · exact B1760339
  · exact B1760343
  · exact B1760347
  · exact B1760351
  · exact B1760355
  · exact B1760359
  · exact B1760363
  · exact B1760367
  · exact B1760371
  · exact B1760375
  · exact B1760379
  · exact B1760383
  · exact B1760387
  · exact B1760391
  · exact B1760395
  · exact B1760399
  · exact B1760403
  · exact B1760407
  · exact B1760411
  · exact B1760415
  · exact B1760419
  · exact B1760423
  · exact B1760427
  · exact B1760431
  · exact B1760435
  · exact B1760439
  · exact B1760443
  · exact B1760447
  · exact B1760451
  · exact B1760455
  · exact B1760459
  · exact B1760463
  · exact B1760467
  · exact B1760471
  · exact B1760475
  · exact B1760479
  · exact B1760483
  · exact B1760487
  · exact B1760491
  · exact B1760495
  · exact B1760499
  · exact B1760503
  · exact B1760507
  · exact B1760511
  · exact B1760515
  · exact B1760519
  · exact B1760523
  · exact B1760527
  · exact B1760531
  · exact B1760535
  · exact B1760539
  · exact B1760543
  · exact B1760547
  · exact B1760551
  · exact B1760555
  · exact B1760559
  · exact B1760563
  · exact B1760567
  · exact B1760571
  · exact B1760575
  · exact B1760579
  · exact B1760583
  · exact B1760587
  · exact B1760591
  · exact B1760595
  · exact B1760599
  · exact B1760603
  · exact B1760607
  · exact B1760611
  · exact B1760615
  · exact B1760619
  · exact B1760623
  · exact B1760627
  · exact B1760631
  · exact B1760635
  · exact B1760639
  · exact B1760643
  · exact B1760647
  · exact B1760651
  · exact B1760655
  · exact B1760659
  · exact B1760663
  · exact B1760667
  · exact B1760671
  · exact B1760675
  · exact B1760679
  · exact B1760683
  · exact B1760687
  · exact B1760691
  · exact B1760695
  · exact B1760699
  · exact B1760703
  · exact B1760707
  · exact B1760711
  · exact B1760715
  · exact B1760719
  · exact B1760723
  · exact B1760727
  · exact B1760731
  · exact B1760735
  · exact B1760739
  · exact B1760743
  · exact B1760747
  · exact B1760751
  · exact B1760755
  · exact B1760759
  · exact B1760763
  · exact B1760767
  · exact B1760771
  · exact B1760775
  · exact B1760779
  · exact B1760783
  · exact B1760787
  · exact B1760791
  · exact B1760795
  · exact B1760799
  · exact B1760803
  · exact B1760807
  · exact B1760811
  · exact B1760815
  · exact B1760819
  · exact B1760823
  · exact B1760827
  · exact B1760831
  · exact B1760835
  · exact B1760839
  · exact B1760843
  · exact B1760847
  · exact B1760851
  · exact B1760855
  · exact B1760859
  · exact B1760863
  · exact B1760867
  · exact B1760871
  · exact B1760875
  · exact B1760879
  · exact B1760883
  · exact B1760887
  · exact B1760891
  · exact B1760895
  · exact B1760899
  · exact B1760903
  · exact B1760907
  · exact B1760911
  · exact B1760915
  · exact B1760919
  · exact B1760923
  · exact B1760927
  · exact B1760931
  · exact B1760935
  · exact B1760939
  · exact B1760943
  · exact B1760947
  · exact B1760951
  · exact B1760955
  · exact B1760959
  · exact B1760963
  · exact B1760967
  · exact B1760971
  · exact B1760975
  · exact B1760979
  · exact B1760983
  · exact B1760987
  · exact B1760991
  · exact B1760995
  · exact B1760999
  · exact B1761003
  · exact B1761007
  · exact B1761011
  · exact B1761015
  · exact B1761019
  · exact B1761023
  · exact B1761027
  · exact B1761031
  · exact B1761035
  · exact B1761039
  · exact B1761043
  · exact B1761047
  · exact B1761051
  · exact B1761055
  · exact B1761059
  · exact B1761063
  · exact B1761067
  · exact B1761071
  · exact B1761075
  · exact B1761079
  · exact B1761083
  · exact B1761087
  · exact B1761091
  · exact B1761095
  · exact B1761099
  · exact B1761103
  · exact B1761107
  · exact B1761111
  · exact B1761115
  · exact B1761119
  · exact B1761123
  · exact B1761127
  · exact B1761131
  · exact B1761135
  · exact B1761139
  · exact B1761143
  · exact B1761147
  · exact B1761151
  · exact B1761155
  · exact B1761159
  · exact B1761163
  · exact B1761167
  · exact B1761171
  · exact B1761175
  · exact B1761179
  · exact B1761183
  · exact B1761187
  · exact B1761191
  · exact B1761195
  · exact B1761199
  · exact B1761203
  · exact B1761207
  · exact B1761211
  · exact B1761215
  · exact B1761219
  · exact B1761223
  · exact B1761227
  · exact B1761231
  · exact B1761235
  · exact B1761239
  · exact B1761243
  · exact B1761247
  · exact B1761251
  · exact B1761255
  · exact B1761259
  · exact B1761263
  · exact B1761267
  · exact B1761271
  · exact B1761275
  · exact B1761279
  · exact B1761283
  · exact B1761287
  · exact B1761291
  · exact B1761295
  · exact B1761299
  · exact B1761303
  · exact B1761307
  · exact B1761311
  · exact B1761315
  · exact B1761319
  · exact B1761323
  · exact B1761327
  · exact B1761331
  · exact B1761335
  · exact B1761339
  · exact B1761343
  · exact B1761347
  · exact B1761351
  · exact B1761355
  · exact B1761359
  · exact B1761363
  · exact B1761367
  · exact B1761371
  · exact B1761375
  · exact B1761379
  · exact B1761383
  · exact B1761387
  · exact B1761391
  · exact B1761395
  · exact B1761399
  · exact B1761403
  · exact B1761407
  · exact B1761411
  · exact B1761415
  · exact B1761419
  · exact B1761423
  · exact B1761427
  · exact B1761431
  · exact B1761435
  · exact B1761439
  · exact B1761443
  · exact B1761447
  · exact B1761451
  · exact B1761455
  · exact B1761459
  · exact B1761463
  · exact B1761467
  · exact B1761471
  · exact B1761475
  · exact B1761479
  · exact B1761483
  · exact B1761487
  · exact B1761491
  · exact B1761495
  · exact B1761499
  · exact B1761503
  · exact B1761507
  · exact B1761511
  · exact B1761515
  · exact B1761519
  · exact B1761523
  · exact B1761527
  · exact B1761531
  · exact B1761535
  · exact B1761539
  · exact B1761543
  · exact B1761547
  · exact B1761551
  · exact B1761555
  · exact B1761559
  · exact B1761563
  · exact B1761567
  · exact B1761571
  · exact B1761575
  · exact B1761579
  · exact B1761583
  · exact B1761587
  · exact B1761591
  · exact B1761595
  · exact B1761599
  · exact B1761603
  · exact B1761607
  · exact B1761611
  · exact B1761615
  · exact B1761619
  · exact B1761623
  · exact B1761627
  · exact B1761631
  · exact B1761635
  · exact B1761639
  · exact B1761643
  · exact B1761647
  · exact B1761651
  · exact B1761655
  · exact B1761659
  · exact B1761663
  · exact B1761667
  · exact B1761671
  · exact B1761675
  · exact B1761679
  · exact B1761683
  · exact B1761687
  · exact B1761691
  · exact B1761695
  · exact B1761699
  · exact B1761703
  · exact B1761707
  · exact B1761711
  · exact B1761715
  · exact B1761719
  · exact B1761723
  · exact B1761727
  · exact B1761731
  · exact B1761735
  · exact B1761739
  · exact B1761743
  · exact B1761747
  · exact B1761751
  · exact B1761755
  · exact B1761759
  · exact B1761763
  · exact B1761767
  · exact B1761771
  · exact B1761775
  · exact B1761779
  · exact B1761783
  · exact B1761787
  · exact B1761791
  · exact B1761795
  · exact B1761799
  · exact B1761803
  · exact B1761807
  · exact B1761811
  · exact B1761815
  · exact B1761819
  · exact B1761823
  · exact B1761827
  · exact B1761831
  · exact B1761835
  · exact B1761839
  · exact B1761843
  · exact B1761847
  · exact B1761851
  · exact B1761855
  · exact B1761859
  · exact B1761863
  · exact B1761867
  · exact B1761871
  · exact B1761875
  · exact B1761879
  · exact B1761883
  · exact B1761887
  · exact B1761891
  · exact B1761895
  · exact B1761899
  · exact B1761903
  · exact B1761907
  · exact B1761911
  · exact B1761915
  · exact B1761919
  · exact B1761923
  · exact B1761927
  · exact B1761931
  · exact B1761935
  · exact B1761939
  · exact B1761943
  · exact B1761947
  · exact B1761951
  · exact B1761955
  · exact B1761959
  · exact B1761963
  · exact B1761967
  · exact B1761971
  · exact B1761975
  · exact B1761979
  · exact B1761983
  · exact B1761987
  · exact B1761991
  · exact B1761995
  · exact B1761999
  · exact B1762003
  · exact B1762007
  · exact B1762011
  · exact B1762015
  · exact B1762019
  · exact B1762023
  · exact B1762027
  · exact B1762031
  · exact B1762035
  · exact B1762039
  · exact B1762043
  · exact B1762047
  · exact B1762051
  · exact B1762055
  · exact B1762059
  · exact B1762063
  · exact B1762067
  · exact B1762071
  · exact B1762075
  · exact B1762079

theorem solution (m : ℕ) (hlo : 1760081 ≤ m) (hhi : m ≤ 1762081) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 440020 ≤ j := by omega
    have hj2 : j ≤ 440519 := by omega
    have hb : Blo 1760081 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
