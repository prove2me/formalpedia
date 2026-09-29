-- Prove2me | solution 1 for syracuse_descends_range_1534464_1536464
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:51.633982+00:00
-- url     : https://prove2.me/submissions/37e0a5a1-6df8-4dba-8c83-4a1ce8bbe01e

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


theorem B1728517 : Blo 1534464 1728517 := bbase (se 4 (by rfl) ⟨162048, by rfl⟩ : syracuseStep 1728517 = 324097) (by norm_num)
theorem B2301965 : Blo 1534464 2301965 := bbase (se 3 (by rfl) ⟨431618, by rfl⟩ : syracuseStep 2301965 = 863237) (by norm_num)
theorem B3112973 : Blo 1534464 3112973 := bbase (se 3 (by rfl) ⟨583682, by rfl⟩ : syracuseStep 3112973 = 1167365) (by norm_num)
theorem B2301989 : Blo 1534464 2301989 := bbase (se 4 (by rfl) ⟨215811, by rfl⟩ : syracuseStep 2301989 = 431623) (by norm_num)
theorem B4431925 : Blo 1534464 4431925 := bbase (se 5 (by rfl) ⟨207746, by rfl⟩ : syracuseStep 4431925 = 415493) (by norm_num)
theorem B2302013 : Blo 1534464 2302013 := bbase (se 3 (by rfl) ⟨431627, by rfl⟩ : syracuseStep 2302013 = 863255) (by norm_num)
theorem B2302037 : Blo 1534464 2302037 := bbase (se 8 (by rfl) ⟨13488, by rfl⟩ : syracuseStep 2302037 = 26977) (by norm_num)
theorem B2302061 : Blo 1534464 2302061 := bbase (se 3 (by rfl) ⟨431636, by rfl⟩ : syracuseStep 2302061 = 863273) (by norm_num)
theorem B2302085 : Blo 1534464 2302085 := bbase (se 4 (by rfl) ⟨215820, by rfl⟩ : syracuseStep 2302085 = 431641) (by norm_num)
theorem B4374661 : Blo 1534464 4374661 := bbase (se 4 (by rfl) ⟨410124, by rfl⟩ : syracuseStep 4374661 = 820249) (by norm_num)
theorem B2302109 : Blo 1534464 2302109 := bbase (se 3 (by rfl) ⟨431645, by rfl⟩ : syracuseStep 2302109 = 863291) (by norm_num)
theorem B2302133 : Blo 1534464 2302133 := bbase (se 5 (by rfl) ⟨107912, by rfl⟩ : syracuseStep 2302133 = 215825) (by norm_num)
theorem B2302157 : Blo 1534464 2302157 := bbase (se 3 (by rfl) ⟨431654, by rfl⟩ : syracuseStep 2302157 = 863309) (by norm_num)
theorem B2302181 : Blo 1534464 2302181 := bbase (se 4 (by rfl) ⟨215829, by rfl⟩ : syracuseStep 2302181 = 431659) (by norm_num)
theorem B2302205 : Blo 1534464 2302205 := bbase (se 3 (by rfl) ⟨431663, by rfl⟩ : syracuseStep 2302205 = 863327) (by norm_num)
theorem B2302229 : Blo 1534464 2302229 := bbase (se 6 (by rfl) ⟨53958, by rfl⟩ : syracuseStep 2302229 = 107917) (by norm_num)
theorem B2302253 : Blo 1534464 2302253 := bbase (se 3 (by rfl) ⟨431672, by rfl⟩ : syracuseStep 2302253 = 863345) (by norm_num)
theorem B2916661 : Blo 1534464 2916661 := bbase (se 5 (by rfl) ⟨136718, by rfl⟩ : syracuseStep 2916661 = 273437) (by norm_num)
theorem B1638721 : Blo 1534464 1638721 := bbase (se 2 (by rfl) ⟨614520, by rfl⟩ : syracuseStep 1638721 = 1229041) (by norm_num)
theorem B2302277 : Blo 1534464 2302277 := bbase (se 4 (by rfl) ⟨215838, by rfl⟩ : syracuseStep 2302277 = 431677) (by norm_num)
theorem B2302301 : Blo 1534464 2302301 := bbase (se 3 (by rfl) ⟨431681, by rfl⟩ : syracuseStep 2302301 = 863363) (by norm_num)
theorem B2302325 : Blo 1534464 2302325 := bbase (se 5 (by rfl) ⟨107921, by rfl⟩ : syracuseStep 2302325 = 215843) (by norm_num)
theorem B5833093 : Blo 1534464 5833093 := bbase (se 4 (by rfl) ⟨546852, by rfl⟩ : syracuseStep 5833093 = 1093705) (by norm_num)
theorem B2302349 : Blo 1534464 2302349 := bbase (se 3 (by rfl) ⟨431690, by rfl⟩ : syracuseStep 2302349 = 863381) (by norm_num)
theorem B2187661 : Blo 1534464 2187661 := bbase (se 3 (by rfl) ⟨410186, by rfl⟩ : syracuseStep 2187661 = 820373) (by norm_num)
theorem B2302373 : Blo 1534464 2302373 := bbase (se 4 (by rfl) ⟨215847, by rfl⟩ : syracuseStep 2302373 = 431695) (by norm_num)
theorem B2302397 : Blo 1534464 2302397 := bbase (se 3 (by rfl) ⟨431699, by rfl⟩ : syracuseStep 2302397 = 863399) (by norm_num)
theorem B2916805 : Blo 1534464 2916805 := bbase (se 4 (by rfl) ⟨273450, by rfl⟩ : syracuseStep 2916805 = 546901) (by norm_num)
theorem B2302421 : Blo 1534464 2302421 := bbase (se 7 (by rfl) ⟨26981, by rfl⟩ : syracuseStep 2302421 = 53963) (by norm_num)
theorem B2302445 : Blo 1534464 2302445 := bbase (se 3 (by rfl) ⟨431708, by rfl⟩ : syracuseStep 2302445 = 863417) (by norm_num)
theorem B2302469 : Blo 1534464 2302469 := bbase (se 4 (by rfl) ⟨215856, by rfl⟩ : syracuseStep 2302469 = 431713) (by norm_num)
theorem B2302493 : Blo 1534464 2302493 := bbase (se 3 (by rfl) ⟨431717, by rfl⟩ : syracuseStep 2302493 = 863435) (by norm_num)
theorem B2302517 : Blo 1534464 2302517 := bbase (se 5 (by rfl) ⟨107930, by rfl⟩ : syracuseStep 2302517 = 215861) (by norm_num)
theorem B2302541 : Blo 1534464 2302541 := bbase (se 3 (by rfl) ⟨431726, by rfl⟩ : syracuseStep 2302541 = 863453) (by norm_num)
theorem B2302565 : Blo 1534464 2302565 := bbase (se 4 (by rfl) ⟨215865, by rfl⟩ : syracuseStep 2302565 = 431731) (by norm_num)
theorem B2302589 : Blo 1534464 2302589 := bbase (se 3 (by rfl) ⟨431735, by rfl⟩ : syracuseStep 2302589 = 863471) (by norm_num)
theorem B1942157 : Blo 1534464 1942157 := bbase (se 3 (by rfl) ⟨364154, by rfl⟩ : syracuseStep 1942157 = 728309) (by norm_num)
theorem B2302613 : Blo 1534464 2302613 := bbase (se 6 (by rfl) ⟨53967, by rfl⟩ : syracuseStep 2302613 = 107935) (by norm_num)
theorem B2302637 : Blo 1534464 2302637 := bbase (se 3 (by rfl) ⟨431744, by rfl⟩ : syracuseStep 2302637 = 863489) (by norm_num)
theorem B5833397 : Blo 1534464 5833397 := bbase (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) (by norm_num)
theorem B1942213 : Blo 1534464 1942213 := bbase (se 4 (by rfl) ⟨182082, by rfl⟩ : syracuseStep 1942213 = 364165) (by norm_num)
theorem B2302661 : Blo 1534464 2302661 := bbase (se 4 (by rfl) ⟨215874, by rfl⟩ : syracuseStep 2302661 = 431749) (by norm_num)
theorem B2302685 : Blo 1534464 2302685 := bbase (se 3 (by rfl) ⟨431753, by rfl⟩ : syracuseStep 2302685 = 863507) (by norm_num)
theorem B2589421 : Blo 1534464 2589421 := bbase (se 3 (by rfl) ⟨485516, by rfl⟩ : syracuseStep 2589421 = 971033) (by norm_num)
theorem B1639153 : Blo 1534464 1639153 := bbase (se 2 (by rfl) ⟨614682, by rfl⟩ : syracuseStep 1639153 = 1229365) (by norm_num)
theorem B8741621 : Blo 1534464 8741621 := bbase (se 5 (by rfl) ⟨409763, by rfl⟩ : syracuseStep 8741621 = 819527) (by norm_num)
theorem B2302709 : Blo 1534464 2302709 := bbase (se 5 (by rfl) ⟨107939, by rfl⟩ : syracuseStep 2302709 = 215879) (by norm_num)
theorem B1557245 : Blo 1534464 1557245 := bbase (se 3 (by rfl) ⟨291983, by rfl⟩ : syracuseStep 1557245 = 583967) (by norm_num)
theorem B2302733 : Blo 1534464 2302733 := bbase (se 3 (by rfl) ⟨431762, by rfl⟩ : syracuseStep 2302733 = 863525) (by norm_num)
theorem B1942309 : Blo 1534464 1942309 := bbase (se 4 (by rfl) ⟨182091, by rfl⟩ : syracuseStep 1942309 = 364183) (by norm_num)
theorem B2302757 : Blo 1534464 2302757 := bbase (se 4 (by rfl) ⟨215883, by rfl⟩ : syracuseStep 2302757 = 431767) (by norm_num)
theorem B1639225 : Blo 1534464 1639225 := bbase (se 2 (by rfl) ⟨614709, by rfl⟩ : syracuseStep 1639225 = 1229419) (by norm_num)
theorem B2302781 : Blo 1534464 2302781 := bbase (se 3 (by rfl) ⟨431771, by rfl⟩ : syracuseStep 2302781 = 863543) (by norm_num)
theorem B2589509 : Blo 1534464 2589509 := bbase (se 4 (by rfl) ⟨242766, by rfl⟩ : syracuseStep 2589509 = 485533) (by norm_num)
theorem B2302805 : Blo 1534464 2302805 := bbase (se 9 (by rfl) ⟨6746, by rfl⟩ : syracuseStep 2302805 = 13493) (by norm_num)
theorem B3687277 : Blo 1534464 3687277 := bbase (se 3 (by rfl) ⟨691364, by rfl⟩ : syracuseStep 3687277 = 1382729) (by norm_num)
theorem B2302829 : Blo 1534464 2302829 := bbase (se 3 (by rfl) ⟨431780, by rfl⟩ : syracuseStep 2302829 = 863561) (by norm_num)
theorem B2245493 : Blo 1534464 2245493 := bbase (se 5 (by rfl) ⟨105257, by rfl⟩ : syracuseStep 2245493 = 210515) (by norm_num)
theorem B2302853 : Blo 1534464 2302853 := bbase (se 4 (by rfl) ⟨215892, by rfl⟩ : syracuseStep 2302853 = 431785) (by norm_num)
theorem B2302877 : Blo 1534464 2302877 := bbase (se 3 (by rfl) ⟨431789, by rfl⟩ : syracuseStep 2302877 = 863579) (by norm_num)
theorem B2302901 : Blo 1534464 2302901 := bbase (se 5 (by rfl) ⟨107948, by rfl⟩ : syracuseStep 2302901 = 215897) (by norm_num)
theorem B2589637 : Blo 1534464 2589637 := bbase (se 4 (by rfl) ⟨242778, by rfl⟩ : syracuseStep 2589637 = 485557) (by norm_num)
theorem B3687373 : Blo 1534464 3687373 := bbase (se 3 (by rfl) ⟨691382, by rfl⟩ : syracuseStep 3687373 = 1382765) (by norm_num)
theorem B2302925 : Blo 1534464 2302925 := bbase (se 3 (by rfl) ⟨431798, by rfl⟩ : syracuseStep 2302925 = 863597) (by norm_num)
theorem B1942481 : Blo 1534464 1942481 := bbase (se 2 (by rfl) ⟨728430, by rfl⟩ : syracuseStep 1942481 = 1456861) (by norm_num)
theorem B7775189 : Blo 1534464 7775189 := bbase (se 7 (by rfl) ⟨91115, by rfl⟩ : syracuseStep 7775189 = 182231) (by norm_num)
theorem B2302949 : Blo 1534464 2302949 := bbase (se 4 (by rfl) ⟨215901, by rfl⟩ : syracuseStep 2302949 = 431803) (by norm_num)
theorem B9339893 : Blo 1534464 9339893 := bbase (se 5 (by rfl) ⟨437807, by rfl⟩ : syracuseStep 9339893 = 875615) (by norm_num)
theorem B2302973 : Blo 1534464 2302973 := bbase (se 3 (by rfl) ⟨431807, by rfl⟩ : syracuseStep 2302973 = 863615) (by norm_num)
theorem B1942537 : Blo 1534464 1942537 := bbase (se 2 (by rfl) ⟨728451, by rfl⟩ : syracuseStep 1942537 = 1456903) (by norm_num)
theorem B6554645 : Blo 1534464 6554645 := bbase (se 6 (by rfl) ⟨153624, by rfl⟩ : syracuseStep 6554645 = 307249) (by norm_num)
theorem B2302997 : Blo 1534464 2302997 := bbase (se 6 (by rfl) ⟨53976, by rfl⟩ : syracuseStep 2302997 = 107953) (by norm_num)
theorem B2589725 : Blo 1534464 2589725 := bbase (se 3 (by rfl) ⟨485573, by rfl⟩ : syracuseStep 2589725 = 971147) (by norm_num)
theorem B2303021 : Blo 1534464 2303021 := bbase (se 3 (by rfl) ⟨431816, by rfl⟩ : syracuseStep 2303021 = 863633) (by norm_num)
theorem B14754869 : Blo 1534464 14754869 := bbase (se 5 (by rfl) ⟨691634, by rfl⟩ : syracuseStep 14754869 = 1383269) (by norm_num)
theorem B2303045 : Blo 1534464 2303045 := bbase (se 4 (by rfl) ⟨215910, by rfl⟩ : syracuseStep 2303045 = 431821) (by norm_num)
theorem B2303069 : Blo 1534464 2303069 := bbase (se 3 (by rfl) ⟨431825, by rfl⟩ : syracuseStep 2303069 = 863651) (by norm_num)
theorem B1942633 : Blo 1534464 1942633 := bbase (se 2 (by rfl) ⟨728487, by rfl⟩ : syracuseStep 1942633 = 1456975) (by norm_num)
theorem B2303093 : Blo 1534464 2303093 := bbase (se 5 (by rfl) ⟨107957, by rfl⟩ : syracuseStep 2303093 = 215915) (by norm_num)
theorem B3114101 : Blo 1534464 3114101 := bbase (se 5 (by rfl) ⟨145973, by rfl⟩ : syracuseStep 3114101 = 291947) (by norm_num)
theorem B3687565 : Blo 1534464 3687565 := bbase (se 3 (by rfl) ⟨691418, by rfl⟩ : syracuseStep 3687565 = 1382837) (by norm_num)
theorem B2303117 : Blo 1534464 2303117 := bbase (se 3 (by rfl) ⟨431834, by rfl⟩ : syracuseStep 2303117 = 863669) (by norm_num)
theorem B2589853 : Blo 1534464 2589853 := bbase (se 3 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 2589853 = 971195) (by norm_num)
theorem B2303141 : Blo 1534464 2303141 := bbase (se 4 (by rfl) ⟨215919, by rfl⟩ : syracuseStep 2303141 = 431839) (by norm_num)
theorem B1639597 : Blo 1534464 1639597 := bbase (se 3 (by rfl) ⟨307424, by rfl⟩ : syracuseStep 1639597 = 614849) (by norm_num)
theorem B3884213 : Blo 1534464 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B9340085 : Blo 1534464 9340085 := bbase (se 5 (by rfl) ⟨437816, by rfl⟩ : syracuseStep 9340085 = 875633) (by norm_num)
theorem B2303165 : Blo 1534464 2303165 := bbase (se 3 (by rfl) ⟨431843, by rfl⟩ : syracuseStep 2303165 = 863687) (by norm_num)
theorem B1844417 : Blo 1534464 1844417 := bbase (se 2 (by rfl) ⟨691656, by rfl⟩ : syracuseStep 1844417 = 1383313) (by norm_num)
theorem B2303189 : Blo 1534464 2303189 := bbase (se 7 (by rfl) ⟨26990, by rfl⟩ : syracuseStep 2303189 = 53981) (by norm_num)
theorem B2303213 : Blo 1534464 2303213 := bbase (se 3 (by rfl) ⟨431852, by rfl⟩ : syracuseStep 2303213 = 863705) (by norm_num)
theorem B2589941 : Blo 1534464 2589941 := bbase (se 5 (by rfl) ⟨121403, by rfl⟩ : syracuseStep 2589941 = 242807) (by norm_num)
theorem B2303237 : Blo 1534464 2303237 := bbase (se 4 (by rfl) ⟨215928, by rfl⟩ : syracuseStep 2303237 = 431857) (by norm_num)
theorem B1942805 : Blo 1534464 1942805 := bbase (se 6 (by rfl) ⟨45534, by rfl⟩ : syracuseStep 1942805 = 91069) (by norm_num)
theorem B2303261 : Blo 1534464 2303261 := bbase (se 3 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 2303261 = 863723) (by norm_num)
theorem B2303285 : Blo 1534464 2303285 := bbase (se 5 (by rfl) ⟨107966, by rfl⟩ : syracuseStep 2303285 = 215933) (by norm_num)
theorem B1942861 : Blo 1534464 1942861 := bbase (se 3 (by rfl) ⟨364286, by rfl⟩ : syracuseStep 1942861 = 728573) (by norm_num)
theorem B2303309 : Blo 1534464 2303309 := bbase (se 3 (by rfl) ⟨431870, by rfl⟩ : syracuseStep 2303309 = 863741) (by norm_num)
theorem B2303333 : Blo 1534464 2303333 := bbase (se 4 (by rfl) ⟨215937, by rfl⟩ : syracuseStep 2303333 = 431875) (by norm_num)
theorem B2590069 : Blo 1534464 2590069 := bbase (se 5 (by rfl) ⟨121409, by rfl⟩ : syracuseStep 2590069 = 242819) (by norm_num)
theorem B2303357 : Blo 1534464 2303357 := bbase (se 3 (by rfl) ⟨431879, by rfl⟩ : syracuseStep 2303357 = 863759) (by norm_num)
theorem B2303381 : Blo 1534464 2303381 := bbase (se 6 (by rfl) ⟨53985, by rfl⟩ : syracuseStep 2303381 = 107971) (by norm_num)
theorem B3278245 : Blo 1534464 3278245 := bbase (se 4 (by rfl) ⟨307335, by rfl⟩ : syracuseStep 3278245 = 614671) (by norm_num)
theorem B1942957 : Blo 1534464 1942957 := bbase (se 3 (by rfl) ⟨364304, by rfl⟩ : syracuseStep 1942957 = 728609) (by norm_num)
theorem B2303405 : Blo 1534464 2303405 := bbase (se 3 (by rfl) ⟨431888, by rfl⟩ : syracuseStep 2303405 = 863777) (by norm_num)
theorem B2459069 : Blo 1534464 2459069 := bbase (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) (by norm_num)
theorem B2303429 : Blo 1534464 2303429 := bbase (se 4 (by rfl) ⟨215946, by rfl⟩ : syracuseStep 2303429 = 431893) (by norm_num)
theorem B2590157 : Blo 1534464 2590157 := bbase (se 3 (by rfl) ⟨485654, by rfl⟩ : syracuseStep 2590157 = 971309) (by norm_num)
theorem B3687893 : Blo 1534464 3687893 := bbase (se 7 (by rfl) ⟨43217, by rfl⟩ : syracuseStep 3687893 = 86435) (by norm_num)
theorem B13125077 : Blo 1534464 13125077 := bbase (se 7 (by rfl) ⟨153809, by rfl⟩ : syracuseStep 13125077 = 307619) (by norm_num)
theorem B2303453 : Blo 1534464 2303453 := bbase (se 3 (by rfl) ⟨431897, by rfl⟩ : syracuseStep 2303453 = 863795) (by norm_num)
theorem B1844705 : Blo 1534464 1844705 := bbase (se 2 (by rfl) ⟨691764, by rfl⟩ : syracuseStep 1844705 = 1383529) (by norm_num)
theorem B5178869 : Blo 1534464 5178869 := bbase (se 5 (by rfl) ⟨242759, by rfl⟩ : syracuseStep 5178869 = 485519) (by norm_num)
theorem B2303477 : Blo 1534464 2303477 := bbase (se 5 (by rfl) ⟨107975, by rfl⟩ : syracuseStep 2303477 = 215951) (by norm_num)
theorem B3884557 : Blo 1534464 3884557 := bbase (se 3 (by rfl) ⟨728354, by rfl⟩ : syracuseStep 3884557 = 1456709) (by norm_num)
theorem B2303501 : Blo 1534464 2303501 := bbase (se 3 (by rfl) ⟨431906, by rfl⟩ : syracuseStep 2303501 = 863813) (by norm_num)
theorem B2303525 : Blo 1534464 2303525 := bbase (se 4 (by rfl) ⟨215955, by rfl⟩ : syracuseStep 2303525 = 431911) (by norm_num)
theorem B1639973 : Blo 1534464 1639973 := bbase (se 4 (by rfl) ⟨153747, by rfl⟩ : syracuseStep 1639973 = 307495) (by norm_num)
theorem B2303549 : Blo 1534464 2303549 := bbase (se 3 (by rfl) ⟨431915, by rfl⟩ : syracuseStep 2303549 = 863831) (by norm_num)
theorem B2590285 : Blo 1534464 2590285 := bbase (se 3 (by rfl) ⟨485678, by rfl⟩ : syracuseStep 2590285 = 971357) (by norm_num)
theorem B2303573 : Blo 1534464 2303573 := bbase (se 8 (by rfl) ⟨13497, by rfl⟩ : syracuseStep 2303573 = 26995) (by norm_num)
theorem B1943129 : Blo 1534464 1943129 := bbase (se 2 (by rfl) ⟨728673, by rfl⟩ : syracuseStep 1943129 = 1457347) (by norm_num)
theorem B2303597 : Blo 1534464 2303597 := bbase (se 3 (by rfl) ⟨431924, by rfl⟩ : syracuseStep 2303597 = 863849) (by norm_num)
theorem B1640045 : Blo 1534464 1640045 := bbase (se 3 (by rfl) ⟨307508, by rfl⟩ : syracuseStep 1640045 = 615017) (by norm_num)
theorem B3884669 : Blo 1534464 3884669 := bbase (se 3 (by rfl) ⟨728375, by rfl⟩ : syracuseStep 3884669 = 1456751) (by norm_num)
theorem B2459261 : Blo 1534464 2459261 := bbase (se 3 (by rfl) ⟨461111, by rfl⟩ : syracuseStep 2459261 = 922223) (by norm_num)
theorem B1844869 : Blo 1534464 1844869 := bbase (se 4 (by rfl) ⟨172956, by rfl⟩ : syracuseStep 1844869 = 345913) (by norm_num)
theorem B2303621 : Blo 1534464 2303621 := bbase (se 4 (by rfl) ⟨215964, by rfl⟩ : syracuseStep 2303621 = 431929) (by norm_num)
theorem B1943185 : Blo 1534464 1943185 := bbase (se 2 (by rfl) ⟨728694, by rfl⟩ : syracuseStep 1943185 = 1457389) (by norm_num)
theorem B2303645 : Blo 1534464 2303645 := bbase (se 3 (by rfl) ⟨431933, by rfl⟩ : syracuseStep 2303645 = 863867) (by norm_num)
theorem B1844897 : Blo 1534464 1844897 := bbase (se 2 (by rfl) ⟨691836, by rfl⟩ : syracuseStep 1844897 = 1383673) (by norm_num)
theorem B2590373 : Blo 1534464 2590373 := bbase (se 4 (by rfl) ⟨242847, by rfl⟩ : syracuseStep 2590373 = 485695) (by norm_num)
theorem B2303669 : Blo 1534464 2303669 := bbase (se 5 (by rfl) ⟨107984, by rfl⟩ : syracuseStep 2303669 = 215969) (by norm_num)
theorem B5531333 : Blo 1534464 5531333 := bbase (se 4 (by rfl) ⟨518562, by rfl⟩ : syracuseStep 5531333 = 1037125) (by norm_num)
theorem B2303693 : Blo 1534464 2303693 := bbase (se 3 (by rfl) ⟨431942, by rfl⟩ : syracuseStep 2303693 = 863885) (by norm_num)
theorem B2303717 : Blo 1534464 2303717 := bbase (se 4 (by rfl) ⟨215973, by rfl⟩ : syracuseStep 2303717 = 431947) (by norm_num)
theorem B1943281 : Blo 1534464 1943281 := bbase (se 2 (by rfl) ⟨728730, by rfl⟩ : syracuseStep 1943281 = 1457461) (by norm_num)
theorem B2303741 : Blo 1534464 2303741 := bbase (se 3 (by rfl) ⟨431951, by rfl⟩ : syracuseStep 2303741 = 863903) (by norm_num)
theorem B1845013 : Blo 1534464 1845013 := bbase (se 6 (by rfl) ⟨43242, by rfl⟩ : syracuseStep 1845013 = 86485) (by norm_num)
theorem B2303765 : Blo 1534464 2303765 := bbase (se 6 (by rfl) ⟨53994, by rfl⟩ : syracuseStep 2303765 = 107989) (by norm_num)
theorem B2590501 : Blo 1534464 2590501 := bbase (se 4 (by rfl) ⟨242859, by rfl⟩ : syracuseStep 2590501 = 485719) (by norm_num)
theorem B1640233 : Blo 1534464 1640233 := bbase (se 2 (by rfl) ⟨615087, by rfl⟩ : syracuseStep 1640233 = 1230175) (by norm_num)
theorem B2303789 : Blo 1534464 2303789 := bbase (se 3 (by rfl) ⟨431960, by rfl⟩ : syracuseStep 2303789 = 863921) (by norm_num)
theorem B3884861 : Blo 1534464 3884861 := bbase (se 3 (by rfl) ⟨728411, by rfl⟩ : syracuseStep 3884861 = 1456823) (by norm_num)
theorem B2303813 : Blo 1534464 2303813 := bbase (se 4 (by rfl) ⟨215982, by rfl⟩ : syracuseStep 2303813 = 431965) (by norm_num)
theorem B3114821 : Blo 1534464 3114821 := bbase (se 4 (by rfl) ⟨292014, by rfl⟩ : syracuseStep 3114821 = 584029) (by norm_num)
theorem B1869649 : Blo 1534464 1869649 := bbase (se 2 (by rfl) ⟨701118, by rfl⟩ : syracuseStep 1869649 = 1402237) (by norm_num)
theorem B3499861 : Blo 1534464 3499861 := bbase (se 9 (by rfl) ⟨10253, by rfl⟩ : syracuseStep 3499861 = 20507) (by norm_num)
theorem B2303837 : Blo 1534464 2303837 := bbase (se 3 (by rfl) ⟨431969, by rfl⟩ : syracuseStep 2303837 = 863939) (by norm_num)
theorem B1845109 : Blo 1534464 1845109 := bbase (se 5 (by rfl) ⟨86489, by rfl⟩ : syracuseStep 1845109 = 172979) (by norm_num)
theorem B2303861 : Blo 1534464 2303861 := bbase (se 5 (by rfl) ⟨107993, by rfl⟩ : syracuseStep 2303861 = 215987) (by norm_num)
theorem B2590589 : Blo 1534464 2590589 := bbase (se 3 (by rfl) ⟨485735, by rfl⟩ : syracuseStep 2590589 = 971471) (by norm_num)
theorem B3688325 : Blo 1534464 3688325 := bbase (se 4 (by rfl) ⟨345780, by rfl⟩ : syracuseStep 3688325 = 691561) (by norm_num)
theorem B2303885 : Blo 1534464 2303885 := bbase (se 3 (by rfl) ⟨431978, by rfl⟩ : syracuseStep 2303885 = 863957) (by norm_num)
theorem B1943453 : Blo 1534464 1943453 := bbase (se 3 (by rfl) ⟨364397, by rfl⟩ : syracuseStep 1943453 = 728795) (by norm_num)
theorem B5179301 : Blo 1534464 5179301 := bbase (se 4 (by rfl) ⟨485559, by rfl⟩ : syracuseStep 5179301 = 971119) (by norm_num)
theorem B2303909 : Blo 1534464 2303909 := bbase (se 4 (by rfl) ⟨215991, by rfl⟩ : syracuseStep 2303909 = 431983) (by norm_num)
theorem B2303933 : Blo 1534464 2303933 := bbase (se 3 (by rfl) ⟨431987, by rfl⟩ : syracuseStep 2303933 = 863975) (by norm_num)
theorem B1943509 : Blo 1534464 1943509 := bbase (se 7 (by rfl) ⟨22775, by rfl⟩ : syracuseStep 1943509 = 45551) (by norm_num)
theorem B2303957 : Blo 1534464 2303957 := bbase (se 7 (by rfl) ⟨26999, by rfl⟩ : syracuseStep 2303957 = 53999) (by norm_num)
theorem B1640417 : Blo 1534464 1640417 := bbase (se 2 (by rfl) ⟨615156, by rfl⟩ : syracuseStep 1640417 = 1230313) (by norm_num)
theorem B6227941 : Blo 1534464 6227941 := bbase (se 4 (by rfl) ⟨583869, by rfl⟩ : syracuseStep 6227941 = 1167739) (by norm_num)
theorem B2303981 : Blo 1534464 2303981 := bbase (se 3 (by rfl) ⟨431996, by rfl⟩ : syracuseStep 2303981 = 863993) (by norm_num)
theorem B2590717 : Blo 1534464 2590717 := bbase (se 3 (by rfl) ⟨485759, by rfl⟩ : syracuseStep 2590717 = 971519) (by norm_num)
theorem B2304005 : Blo 1534464 2304005 := bbase (se 4 (by rfl) ⟨216000, by rfl⟩ : syracuseStep 2304005 = 432001) (by norm_num)
theorem B2304029 : Blo 1534464 2304029 := bbase (se 3 (by rfl) ⟨432005, by rfl⟩ : syracuseStep 2304029 = 864011) (by norm_num)
theorem B1943605 : Blo 1534464 1943605 := bbase (se 5 (by rfl) ⟨91106, by rfl⟩ : syracuseStep 1943605 = 182213) (by norm_num)
theorem B2304053 : Blo 1534464 2304053 := bbase (se 5 (by rfl) ⟨108002, by rfl⟩ : syracuseStep 2304053 = 216005) (by norm_num)
theorem B2304077 : Blo 1534464 2304077 := bbase (se 3 (by rfl) ⟨432014, by rfl⟩ : syracuseStep 2304077 = 864029) (by norm_num)
theorem B2590805 : Blo 1534464 2590805 := bbase (se 8 (by rfl) ⟨15180, by rfl⟩ : syracuseStep 2590805 = 30361) (by norm_num)
theorem B7383125 : Blo 1534464 7383125 := bbase (se 8 (by rfl) ⟨43260, by rfl⟩ : syracuseStep 7383125 = 86521) (by norm_num)
theorem B2304101 : Blo 1534464 2304101 := bbase (se 4 (by rfl) ⟨216009, by rfl⟩ : syracuseStep 2304101 = 432019) (by norm_num)
theorem B2304125 : Blo 1534464 2304125 := bbase (se 3 (by rfl) ⟨432023, by rfl⟩ : syracuseStep 2304125 = 864047) (by norm_num)
theorem B3885205 : Blo 1534464 3885205 := bbase (se 6 (by rfl) ⟨91059, by rfl⟩ : syracuseStep 3885205 = 182119) (by norm_num)
theorem B2304149 : Blo 1534464 2304149 := bbase (se 6 (by rfl) ⟨54003, by rfl⟩ : syracuseStep 2304149 = 108007) (by norm_num)
theorem B4671637 : Blo 1534464 4671637 := bbase (se 6 (by rfl) ⟨109491, by rfl⟩ : syracuseStep 4671637 = 218983) (by norm_num)
theorem B2304173 : Blo 1534464 2304173 := bbase (se 3 (by rfl) ⟨432032, by rfl⟩ : syracuseStep 2304173 = 864065) (by norm_num)
theorem B2304197 : Blo 1534464 2304197 := bbase (se 4 (by rfl) ⟨216018, by rfl⟩ : syracuseStep 2304197 = 432037) (by norm_num)
theorem B9832661 : Blo 1534464 9832661 := bbase (se 7 (by rfl) ⟨115226, by rfl⟩ : syracuseStep 9832661 = 230453) (by norm_num)
theorem B3688661 : Blo 1534464 3688661 := bbase (se 7 (by rfl) ⟨43226, by rfl⟩ : syracuseStep 3688661 = 86453) (by norm_num)
theorem B2590933 : Blo 1534464 2590933 := bbase (se 7 (by rfl) ⟨30362, by rfl⟩ : syracuseStep 2590933 = 60725) (by norm_num)
theorem B17500373 : Blo 1534464 17500373 := bbase (se 7 (by rfl) ⟨205082, by rfl⟩ : syracuseStep 17500373 = 410165) (by norm_num)
theorem B2304221 : Blo 1534464 2304221 := bbase (se 3 (by rfl) ⟨432041, by rfl⟩ : syracuseStep 2304221 = 864083) (by norm_num)
theorem B1943777 : Blo 1534464 1943777 := bbase (se 2 (by rfl) ⟨728916, by rfl⟩ : syracuseStep 1943777 = 1457833) (by norm_num)
theorem B7776485 : Blo 1534464 7776485 := bbase (se 4 (by rfl) ⟨729045, by rfl⟩ : syracuseStep 7776485 = 1458091) (by norm_num)
theorem B2304245 : Blo 1534464 2304245 := bbase (se 5 (by rfl) ⟨108011, by rfl⟩ : syracuseStep 2304245 = 216023) (by norm_num)
theorem B3885317 : Blo 1534464 3885317 := bbase (se 4 (by rfl) ⟨364248, by rfl⟩ : syracuseStep 3885317 = 728497) (by norm_num)
theorem B2304269 : Blo 1534464 2304269 := bbase (se 3 (by rfl) ⟨432050, by rfl⟩ : syracuseStep 2304269 = 864101) (by norm_num)
theorem B1943833 : Blo 1534464 1943833 := bbase (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) (by norm_num)
theorem B3279133 : Blo 1534464 3279133 := bbase (se 3 (by rfl) ⟨614837, by rfl⟩ : syracuseStep 3279133 = 1229675) (by norm_num)
theorem B2304293 : Blo 1534464 2304293 := bbase (se 4 (by rfl) ⟨216027, by rfl⟩ : syracuseStep 2304293 = 432055) (by norm_num)
theorem B2591021 : Blo 1534464 2591021 := bbase (se 3 (by rfl) ⟨485816, by rfl⟩ : syracuseStep 2591021 = 971633) (by norm_num)
theorem B2304317 : Blo 1534464 2304317 := bbase (se 3 (by rfl) ⟨432059, by rfl⟩ : syracuseStep 2304317 = 864119) (by norm_num)
theorem B5179733 : Blo 1534464 5179733 := bbase (se 10 (by rfl) ⟨7587, by rfl⟩ : syracuseStep 5179733 = 15175) (by norm_num)
theorem B2304341 : Blo 1534464 2304341 := bbase (se 10 (by rfl) ⟨3375, by rfl⟩ : syracuseStep 2304341 = 6751) (by norm_num)
theorem B1845589 : Blo 1534464 1845589 := bbase (se 10 (by rfl) ⟨2703, by rfl⟩ : syracuseStep 1845589 = 5407) (by norm_num)
theorem B2304365 : Blo 1534464 2304365 := bbase (se 3 (by rfl) ⟨432068, by rfl⟩ : syracuseStep 2304365 = 864137) (by norm_num)
theorem B1943929 : Blo 1534464 1943929 := bbase (se 2 (by rfl) ⟨728973, by rfl⟩ : syracuseStep 1943929 = 1457947) (by norm_num)
theorem B2304389 : Blo 1534464 2304389 := bbase (se 4 (by rfl) ⟨216036, by rfl⟩ : syracuseStep 2304389 = 432073) (by norm_num)
theorem B2304413 : Blo 1534464 2304413 := bbase (se 3 (by rfl) ⟨432077, by rfl⟩ : syracuseStep 2304413 = 864155) (by norm_num)
theorem B2591149 : Blo 1534464 2591149 := bbase (se 3 (by rfl) ⟨485840, by rfl⟩ : syracuseStep 2591149 = 971681) (by norm_num)
theorem B2304437 : Blo 1534464 2304437 := bbase (se 5 (by rfl) ⟨108020, by rfl⟩ : syracuseStep 2304437 = 216041) (by norm_num)
theorem B3885509 : Blo 1534464 3885509 := bbase (se 4 (by rfl) ⟨364266, by rfl⟩ : syracuseStep 3885509 = 728533) (by norm_num)
theorem B2304461 : Blo 1534464 2304461 := bbase (se 3 (by rfl) ⟨432086, by rfl⟩ : syracuseStep 2304461 = 864173) (by norm_num)
theorem B2304485 : Blo 1534464 2304485 := bbase (se 4 (by rfl) ⟨216045, by rfl⟩ : syracuseStep 2304485 = 432091) (by norm_num)
theorem B3500525 : Blo 1534464 3500525 := bbase (se 3 (by rfl) ⟨656348, by rfl⟩ : syracuseStep 3500525 = 1312697) (by norm_num)
theorem B2304509 : Blo 1534464 2304509 := bbase (se 3 (by rfl) ⟨432095, by rfl⟩ : syracuseStep 2304509 = 864191) (by norm_num)
theorem B2591237 : Blo 1534464 2591237 := bbase (se 4 (by rfl) ⟨242928, by rfl⟩ : syracuseStep 2591237 = 485857) (by norm_num)
theorem B2304533 : Blo 1534464 2304533 := bbase (se 6 (by rfl) ⟨54012, by rfl⟩ : syracuseStep 2304533 = 108025) (by norm_num)
theorem B1944101 : Blo 1534464 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B2304557 : Blo 1534464 2304557 := bbase (se 3 (by rfl) ⟨432104, by rfl⟩ : syracuseStep 2304557 = 864209) (by norm_num)
theorem B4917829 : Blo 1534464 4917829 := bbase (se 4 (by rfl) ⟨461046, by rfl⟩ : syracuseStep 4917829 = 922093) (by norm_num)
theorem B2304581 : Blo 1534464 2304581 := bbase (se 4 (by rfl) ⟨216054, by rfl⟩ : syracuseStep 2304581 = 432109) (by norm_num)
theorem B1944157 : Blo 1534464 1944157 := bbase (se 3 (by rfl) ⟨364529, by rfl⟩ : syracuseStep 1944157 = 729059) (by norm_num)
theorem B2304605 : Blo 1534464 2304605 := bbase (se 3 (by rfl) ⟨432113, by rfl⟩ : syracuseStep 2304605 = 864227) (by norm_num)
theorem B2304629 : Blo 1534464 2304629 := bbase (se 5 (by rfl) ⟨108029, by rfl⟩ : syracuseStep 2304629 = 216059) (by norm_num)
theorem B7768709 : Blo 1534464 7768709 := bbase (se 4 (by rfl) ⟨728316, by rfl⟩ : syracuseStep 7768709 = 1456633) (by norm_num)
theorem B2591365 : Blo 1534464 2591365 := bbase (se 4 (by rfl) ⟨242940, by rfl⟩ : syracuseStep 2591365 = 485881) (by norm_num)
theorem B2304653 : Blo 1534464 2304653 := bbase (se 3 (by rfl) ⟨432122, by rfl⟩ : syracuseStep 2304653 = 864245) (by norm_num)
theorem B2304677 : Blo 1534464 2304677 := bbase (se 4 (by rfl) ⟨216063, by rfl⟩ : syracuseStep 2304677 = 432127) (by norm_num)
theorem B1944253 : Blo 1534464 1944253 := bbase (se 3 (by rfl) ⟨364547, by rfl⟩ : syracuseStep 1944253 = 729095) (by norm_num)
theorem B2591453 : Blo 1534464 2591453 := bbase (se 3 (by rfl) ⟨485897, by rfl⟩ : syracuseStep 2591453 = 971795) (by norm_num)
theorem B1968881 : Blo 1534464 1968881 := bbase (se 2 (by rfl) ⟨738330, by rfl⟩ : syracuseStep 1968881 = 1476661) (by norm_num)
theorem B5180165 : Blo 1534464 5180165 := bbase (se 4 (by rfl) ⟨485640, by rfl⟩ : syracuseStep 5180165 = 971281) (by norm_num)
theorem B3279629 : Blo 1534464 3279629 := bbase (se 3 (by rfl) ⟨614930, by rfl⟩ : syracuseStep 3279629 = 1229861) (by norm_num)
theorem B3885853 : Blo 1534464 3885853 := bbase (se 3 (by rfl) ⟨728597, by rfl⟩ : syracuseStep 3885853 = 1457195) (by norm_num)
theorem B4918085 : Blo 1534464 4918085 := bbase (se 4 (by rfl) ⟨461070, by rfl⟩ : syracuseStep 4918085 = 922141) (by norm_num)
theorem B2591581 : Blo 1534464 2591581 := bbase (se 3 (by rfl) ⟨485921, by rfl⟩ : syracuseStep 2591581 = 971843) (by norm_num)
theorem B1944425 : Blo 1534464 1944425 := bbase (se 2 (by rfl) ⟨729159, by rfl⟩ : syracuseStep 1944425 = 1458319) (by norm_num)
theorem B3885965 : Blo 1534464 3885965 := bbase (se 3 (by rfl) ⟨728618, by rfl⟩ : syracuseStep 3885965 = 1457237) (by norm_num)
theorem B1944481 : Blo 1534464 1944481 := bbase (se 2 (by rfl) ⟨729180, by rfl⟩ : syracuseStep 1944481 = 1458361) (by norm_num)
theorem B2591669 : Blo 1534464 2591669 := bbase (se 5 (by rfl) ⟨121484, by rfl⟩ : syracuseStep 2591669 = 242969) (by norm_num)
theorem B4148165 : Blo 1534464 4148165 := bbase (se 4 (by rfl) ⟨388890, by rfl⟩ : syracuseStep 4148165 = 777781) (by norm_num)
theorem B1944577 : Blo 1534464 1944577 := bbase (se 2 (by rfl) ⟨729216, by rfl⟩ : syracuseStep 1944577 = 1458433) (by norm_num)
theorem B2460709 : Blo 1534464 2460709 := bbase (se 4 (by rfl) ⟨230691, by rfl⟩ : syracuseStep 2460709 = 461383) (by norm_num)
theorem B2591797 : Blo 1534464 2591797 := bbase (se 5 (by rfl) ⟨121490, by rfl⟩ : syracuseStep 2591797 = 242981) (by norm_num)
theorem B3886157 : Blo 1534464 3886157 := bbase (se 3 (by rfl) ⟨728654, by rfl⟩ : syracuseStep 3886157 = 1457309) (by norm_num)
theorem B2591885 : Blo 1534464 2591885 := bbase (se 3 (by rfl) ⟨485978, by rfl⟩ : syracuseStep 2591885 = 971957) (by norm_num)
theorem B5827733 : Blo 1534464 5827733 := bbase (se 6 (by rfl) ⟨136587, by rfl⟩ : syracuseStep 5827733 = 273175) (by norm_num)
theorem B3599509 : Blo 1534464 3599509 := bbase (se 6 (by rfl) ⟨84363, by rfl⟩ : syracuseStep 3599509 = 168727) (by norm_num)
theorem B5180597 : Blo 1534464 5180597 := bbase (se 5 (by rfl) ⟨242840, by rfl⟩ : syracuseStep 5180597 = 485681) (by norm_num)
theorem B3689717 : Blo 1534464 3689717 := bbase (se 5 (by rfl) ⟨172955, by rfl⟩ : syracuseStep 3689717 = 345911) (by norm_num)
theorem B2592013 : Blo 1534464 2592013 := bbase (se 3 (by rfl) ⟨486002, by rfl⟩ : syracuseStep 2592013 = 972005) (by norm_num)
theorem B8301845 : Blo 1534464 8301845 := bbase (se 6 (by rfl) ⟨194574, by rfl⟩ : syracuseStep 8301845 = 389149) (by norm_num)
theorem B4369717 : Blo 1534464 4369717 := bbase (se 5 (by rfl) ⟨204830, by rfl⟩ : syracuseStep 4369717 = 409661) (by norm_num)
theorem B11660597 : Blo 1534464 11660597 := bbase (se 5 (by rfl) ⟨546590, by rfl⟩ : syracuseStep 11660597 = 1093181) (by norm_num)
theorem B2592101 : Blo 1534464 2592101 := bbase (se 4 (by rfl) ⟨243009, by rfl⟩ : syracuseStep 2592101 = 486019) (by norm_num)
theorem B4148597 : Blo 1534464 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B3886501 : Blo 1534464 3886501 := bbase (se 4 (by rfl) ⟨364359, by rfl⟩ : syracuseStep 3886501 = 728719) (by norm_num)
theorem B5828021 : Blo 1534464 5828021 := bbase (se 5 (by rfl) ⟨273188, by rfl⟩ : syracuseStep 5828021 = 546377) (by norm_num)
theorem B7376341 : Blo 1534464 7376341 := bbase (se 7 (by rfl) ⟨86441, by rfl⟩ : syracuseStep 7376341 = 172883) (by norm_num)
theorem B2592229 : Blo 1534464 2592229 := bbase (se 4 (by rfl) ⟨243021, by rfl⟩ : syracuseStep 2592229 = 486043) (by norm_num)
theorem B7777781 : Blo 1534464 7777781 := bbase (se 5 (by rfl) ⟨364583, by rfl⟩ : syracuseStep 7777781 = 729167) (by norm_num)
theorem B3886613 : Blo 1534464 3886613 := bbase (se 6 (by rfl) ⟨91092, by rfl⟩ : syracuseStep 3886613 = 182185) (by norm_num)
theorem B2592317 : Blo 1534464 2592317 := bbase (se 3 (by rfl) ⟨486059, by rfl⟩ : syracuseStep 2592317 = 972119) (by norm_num)
theorem B5181029 : Blo 1534464 5181029 := bbase (se 4 (by rfl) ⟨485721, by rfl⟩ : syracuseStep 5181029 = 971443) (by norm_num)
theorem B3280493 : Blo 1534464 3280493 := bbase (se 3 (by rfl) ⟨615092, by rfl⟩ : syracuseStep 3280493 = 1230185) (by norm_num)
theorem B2625149 : Blo 1534464 2625149 := bbase (se 3 (by rfl) ⟨492215, by rfl⟩ : syracuseStep 2625149 = 984431) (by norm_num)
theorem B3452597 : Blo 1534464 3452597 := bbase (se 5 (by rfl) ⟨161840, by rfl⟩ : syracuseStep 3452597 = 323681) (by norm_num)
theorem B2592445 : Blo 1534464 2592445 := bbase (se 3 (by rfl) ⟨486083, by rfl⟩ : syracuseStep 2592445 = 972167) (by norm_num)
theorem B11652821 : Blo 1534464 11652821 := bbase (se 7 (by rfl) ⟨136556, by rfl⟩ : syracuseStep 11652821 = 273113) (by norm_num)
theorem B3886805 : Blo 1534464 3886805 := bbase (se 7 (by rfl) ⟨45548, by rfl⟩ : syracuseStep 3886805 = 91097) (by norm_num)
theorem B3452669 : Blo 1534464 3452669 := bbase (se 3 (by rfl) ⟨647375, by rfl⟩ : syracuseStep 3452669 = 1294751) (by norm_num)
theorem B3280637 : Blo 1534464 3280637 := bbase (se 3 (by rfl) ⟨615119, by rfl⟩ : syracuseStep 3280637 = 1230239) (by norm_num)
theorem B2592533 : Blo 1534464 2592533 := bbase (se 6 (by rfl) ⟨60762, by rfl⟩ : syracuseStep 2592533 = 121525) (by norm_num)
theorem B3452741 : Blo 1534464 3452741 := bbase (se 4 (by rfl) ⟨323694, by rfl⟩ : syracuseStep 3452741 = 647389) (by norm_num)
theorem B9596789 : Blo 1534464 9596789 := bbase (se 5 (by rfl) ⟨449849, by rfl⟩ : syracuseStep 9596789 = 899699) (by norm_num)
theorem B3501949 : Blo 1534464 3501949 := bbase (se 3 (by rfl) ⟨656615, by rfl⟩ : syracuseStep 3501949 = 1313231) (by norm_num)
theorem B3452813 : Blo 1534464 3452813 := bbase (se 3 (by rfl) ⟨647402, by rfl⟩ : syracuseStep 3452813 = 1294805) (by norm_num)
theorem B7770005 : Blo 1534464 7770005 := bbase (se 6 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 7770005 = 364219) (by norm_num)
theorem B2592661 : Blo 1534464 2592661 := bbase (se 6 (by rfl) ⟨60765, by rfl⟩ : syracuseStep 2592661 = 121531) (by norm_num)
theorem B3452885 : Blo 1534464 3452885 := bbase (se 7 (by rfl) ⟨40463, by rfl⟩ : syracuseStep 3452885 = 80927) (by norm_num)
theorem B2592749 : Blo 1534464 2592749 := bbase (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) (by norm_num)
theorem B5181461 : Blo 1534464 5181461 := bbase (se 6 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 5181461 = 242881) (by norm_num)
theorem B3452957 : Blo 1534464 3452957 := bbase (se 3 (by rfl) ⟨647429, by rfl⟩ : syracuseStep 3452957 = 1294859) (by norm_num)
theorem B3887149 : Blo 1534464 3887149 := bbase (se 3 (by rfl) ⟨728840, by rfl⟩ : syracuseStep 3887149 = 1457681) (by norm_num)
theorem B3453029 : Blo 1534464 3453029 := bbase (se 4 (by rfl) ⟨323721, by rfl⟩ : syracuseStep 3453029 = 647443) (by norm_num)
theorem B5533829 : Blo 1534464 5533829 := bbase (se 4 (by rfl) ⟨518796, by rfl⟩ : syracuseStep 5533829 = 1037593) (by norm_num)
theorem B4149397 : Blo 1534464 4149397 := bbase (se 6 (by rfl) ⟨97251, by rfl⟩ : syracuseStep 4149397 = 194503) (by norm_num)
theorem B3887261 : Blo 1534464 3887261 := bbase (se 3 (by rfl) ⟨728861, by rfl⟩ : syracuseStep 3887261 = 1457723) (by norm_num)
theorem B3453101 : Blo 1534464 3453101 := bbase (se 3 (by rfl) ⟨647456, by rfl⟩ : syracuseStep 3453101 = 1294913) (by norm_num)
theorem B1970401 : Blo 1534464 1970401 := bbase (se 2 (by rfl) ⟨738900, by rfl⟩ : syracuseStep 1970401 = 1477801) (by norm_num)
theorem B3453173 : Blo 1534464 3453173 := bbase (se 5 (by rfl) ⟨161867, by rfl⟩ : syracuseStep 3453173 = 323735) (by norm_num)
theorem B7000357 : Blo 1534464 7000357 := bbase (se 4 (by rfl) ⟨656283, by rfl⟩ : syracuseStep 7000357 = 1312567) (by norm_num)
theorem B3453245 : Blo 1534464 3453245 := bbase (se 3 (by rfl) ⟨647483, by rfl⟩ : syracuseStep 3453245 = 1294967) (by norm_num)
theorem B3887453 : Blo 1534464 3887453 := bbase (se 3 (by rfl) ⟨728897, by rfl⟩ : syracuseStep 3887453 = 1457795) (by norm_num)
theorem B3453317 : Blo 1534464 3453317 := bbase (se 4 (by rfl) ⟨323748, by rfl⟩ : syracuseStep 3453317 = 647497) (by norm_num)
theorem B5181893 : Blo 1534464 5181893 := bbase (se 4 (by rfl) ⟨485802, by rfl⟩ : syracuseStep 5181893 = 971605) (by norm_num)
theorem B3453389 : Blo 1534464 3453389 := bbase (se 3 (by rfl) ⟨647510, by rfl⟩ : syracuseStep 3453389 = 1295021) (by norm_num)
theorem B3281381 : Blo 1534464 3281381 := bbase (se 4 (by rfl) ⟨307629, by rfl⟩ : syracuseStep 3281381 = 615259) (by norm_num)
theorem B3453461 : Blo 1534464 3453461 := bbase (se 6 (by rfl) ⟨80940, by rfl⟩ : syracuseStep 3453461 = 161881) (by norm_num)
theorem B2765357 : Blo 1534464 2765357 := bbase (se 3 (by rfl) ⟨518504, by rfl⟩ : syracuseStep 2765357 = 1037009) (by norm_num)
theorem B5829205 : Blo 1534464 5829205 := bbase (se 8 (by rfl) ⟨34155, by rfl⟩ : syracuseStep 5829205 = 68311) (by norm_num)
theorem B3453533 : Blo 1534464 3453533 := bbase (se 3 (by rfl) ⟨647537, by rfl⟩ : syracuseStep 3453533 = 1295075) (by norm_num)
theorem B3453605 : Blo 1534464 3453605 := bbase (se 4 (by rfl) ⟨323775, by rfl⟩ : syracuseStep 3453605 = 647551) (by norm_num)
theorem B3887797 : Blo 1534464 3887797 := bbase (se 5 (by rfl) ⟨182240, by rfl⟩ : syracuseStep 3887797 = 364481) (by norm_num)
theorem B5534405 : Blo 1534464 5534405 := bbase (se 4 (by rfl) ⟨518850, by rfl⟩ : syracuseStep 5534405 = 1037701) (by norm_num)
theorem B11072213 : Blo 1534464 11072213 := bbase (se 7 (by rfl) ⟨129752, by rfl⟩ : syracuseStep 11072213 = 259505) (by norm_num)
theorem B3453677 : Blo 1534464 3453677 := bbase (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) (by norm_num)
theorem B4371221 : Blo 1534464 4371221 := bbase (se 6 (by rfl) ⟨102450, by rfl⟩ : syracuseStep 4371221 = 204901) (by norm_num)
theorem B3887909 : Blo 1534464 3887909 := bbase (se 4 (by rfl) ⟨364491, by rfl⟩ : syracuseStep 3887909 = 728983) (by norm_num)
theorem B3453749 : Blo 1534464 3453749 := bbase (se 5 (by rfl) ⟨161894, by rfl⟩ : syracuseStep 3453749 = 323789) (by norm_num)
theorem B5182325 : Blo 1534464 5182325 := bbase (se 5 (by rfl) ⟨242921, by rfl⟩ : syracuseStep 5182325 = 485843) (by norm_num)
theorem B3453821 : Blo 1534464 3453821 := bbase (se 3 (by rfl) ⟨647591, by rfl⟩ : syracuseStep 3453821 = 1295183) (by norm_num)
theorem B5829509 : Blo 1534464 5829509 := bbase (se 4 (by rfl) ⟨546516, by rfl⟩ : syracuseStep 5829509 = 1093033) (by norm_num)
theorem B9843605 : Blo 1534464 9843605 := bbase (se 6 (by rfl) ⟨230709, by rfl⟩ : syracuseStep 9843605 = 461419) (by norm_num)
theorem B2913221 : Blo 1534464 2913221 := bbase (se 4 (by rfl) ⟨273114, by rfl⟩ : syracuseStep 2913221 = 546229) (by norm_num)
theorem B3453893 : Blo 1534464 3453893 := bbase (se 4 (by rfl) ⟨323802, by rfl⟩ : syracuseStep 3453893 = 647605) (by norm_num)
theorem B6558677 : Blo 1534464 6558677 := bbase (se 7 (by rfl) ⟨76859, by rfl⟩ : syracuseStep 6558677 = 153719) (by norm_num)
theorem B1684453 : Blo 1534464 1684453 := bbase (se 4 (by rfl) ⟨157917, by rfl⟩ : syracuseStep 1684453 = 315835) (by norm_num)
theorem B3888101 : Blo 1534464 3888101 := bbase (se 4 (by rfl) ⟨364509, by rfl⟩ : syracuseStep 3888101 = 729019) (by norm_num)
theorem B1577965 : Blo 1534464 1577965 := bbase (se 3 (by rfl) ⟨295868, by rfl⟩ : syracuseStep 1577965 = 591737) (by norm_num)
theorem B3453965 : Blo 1534464 3453965 := bbase (se 3 (by rfl) ⟨647618, by rfl⟩ : syracuseStep 3453965 = 1295237) (by norm_num)
theorem B5395493 : Blo 1534464 5395493 := bbase (se 4 (by rfl) ⟨505827, by rfl⟩ : syracuseStep 5395493 = 1011655) (by norm_num)
theorem B3454037 : Blo 1534464 3454037 := bbase (se 8 (by rfl) ⟨20238, by rfl⟩ : syracuseStep 3454037 = 40477) (by norm_num)
theorem B2528365 : Blo 1534464 2528365 := bbase (se 3 (by rfl) ⟨474068, by rfl⟩ : syracuseStep 2528365 = 948137) (by norm_num)
theorem B5534837 : Blo 1534464 5534837 := bbase (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) (by norm_num)
theorem B3454109 : Blo 1534464 3454109 := bbase (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) (by norm_num)
theorem B7771301 : Blo 1534464 7771301 := bbase (se 4 (by rfl) ⟨728559, by rfl⟩ : syracuseStep 7771301 = 1457119) (by norm_num)
theorem B2913509 : Blo 1534464 2913509 := bbase (se 4 (by rfl) ⟨273141, by rfl⟩ : syracuseStep 2913509 = 546283) (by norm_num)
theorem B3454181 : Blo 1534464 3454181 := bbase (se 4 (by rfl) ⟨323829, by rfl⟩ : syracuseStep 3454181 = 647659) (by norm_num)
theorem B5182757 : Blo 1534464 5182757 := bbase (se 4 (by rfl) ⟨485883, by rfl⟩ : syracuseStep 5182757 = 971767) (by norm_num)
theorem B3454253 : Blo 1534464 3454253 := bbase (se 3 (by rfl) ⟨647672, by rfl⟩ : syracuseStep 3454253 = 1295345) (by norm_num)
theorem B3888445 : Blo 1534464 3888445 := bbase (se 3 (by rfl) ⟨729083, by rfl⟩ : syracuseStep 3888445 = 1458167) (by norm_num)
theorem B5051717 : Blo 1534464 5051717 := bbase (se 4 (by rfl) ⟨473598, by rfl⟩ : syracuseStep 5051717 = 947197) (by norm_num)
theorem B3454325 : Blo 1534464 3454325 := bbase (se 5 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 3454325 = 323843) (by norm_num)
theorem B2913661 : Blo 1534464 2913661 := bbase (se 3 (by rfl) ⟨546311, by rfl⟩ : syracuseStep 2913661 = 1092623) (by norm_num)
theorem B3888557 : Blo 1534464 3888557 := bbase (se 3 (by rfl) ⟨729104, by rfl⟩ : syracuseStep 3888557 = 1458209) (by norm_num)
theorem B3454397 : Blo 1534464 3454397 := bbase (se 3 (by rfl) ⟨647699, by rfl⟩ : syracuseStep 3454397 = 1295399) (by norm_num)
theorem B3454469 : Blo 1534464 3454469 := bbase (se 4 (by rfl) ⟨323856, by rfl⟩ : syracuseStep 3454469 = 647713) (by norm_num)
theorem B4920853 : Blo 1534464 4920853 := bbase (se 6 (by rfl) ⟨115332, by rfl⟩ : syracuseStep 4920853 = 230665) (by norm_num)
theorem B3454541 : Blo 1534464 3454541 := bbase (se 3 (by rfl) ⟨647726, by rfl⟩ : syracuseStep 3454541 = 1295453) (by norm_num)
theorem B28390997 : Blo 1534464 28390997 := bbase (se 8 (by rfl) ⟨166353, by rfl⟩ : syracuseStep 28390997 = 332707) (by norm_num)
theorem B3888749 : Blo 1534464 3888749 := bbase (se 3 (by rfl) ⟨729140, by rfl⟩ : syracuseStep 3888749 = 1458281) (by norm_num)
theorem B3454613 : Blo 1534464 3454613 := bbase (se 6 (by rfl) ⟨80967, by rfl⟩ : syracuseStep 3454613 = 161935) (by norm_num)
theorem B2913965 : Blo 1534464 2913965 := bbase (se 3 (by rfl) ⟨546368, by rfl⟩ : syracuseStep 2913965 = 1092737) (by norm_num)
theorem B29513429 : Blo 1534464 29513429 := bbase (se 7 (by rfl) ⟨345860, by rfl⟩ : syracuseStep 29513429 = 691721) (by norm_num)
theorem B7100117 : Blo 1534464 7100117 := bbase (se 7 (by rfl) ⟨83204, by rfl⟩ : syracuseStep 7100117 = 166409) (by norm_num)
theorem B5183189 : Blo 1534464 5183189 := bbase (se 7 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 5183189 = 121481) (by norm_num)
theorem B4495061 : Blo 1534464 4495061 := bbase (se 7 (by rfl) ⟨52676, by rfl⟩ : syracuseStep 4495061 = 105353) (by norm_num)
theorem B3454685 : Blo 1534464 3454685 := bbase (se 3 (by rfl) ⟨647753, by rfl⟩ : syracuseStep 3454685 = 1295507) (by norm_num)
theorem B8304373 : Blo 1534464 8304373 := bbase (se 5 (by rfl) ⟨389267, by rfl⟩ : syracuseStep 8304373 = 778535) (by norm_num)
theorem B3938053 : Blo 1534464 3938053 := bbase (se 4 (by rfl) ⟨369192, by rfl⟩ : syracuseStep 3938053 = 738385) (by norm_num)
theorem B3454757 : Blo 1534464 3454757 := bbase (se 4 (by rfl) ⟨323883, by rfl⟩ : syracuseStep 3454757 = 647767) (by norm_num)
theorem B1726285 : Blo 1534464 1726285 := bbase (se 3 (by rfl) ⟨323678, by rfl⟩ : syracuseStep 1726285 = 647357) (by norm_num)
theorem B3454829 : Blo 1534464 3454829 := bbase (se 3 (by rfl) ⟨647780, by rfl⟩ : syracuseStep 3454829 = 1295561) (by norm_num)
theorem B1726321 : Blo 1534464 1726321 := bbase (se 2 (by rfl) ⟨647370, by rfl⟩ : syracuseStep 1726321 = 1294741) (by norm_num)
theorem B1775473 : Blo 1534464 1775473 := bbase (se 2 (by rfl) ⟨665802, by rfl⟩ : syracuseStep 1775473 = 1331605) (by norm_num)
theorem B1726357 : Blo 1534464 1726357 := bbase (se 6 (by rfl) ⟨40461, by rfl⟩ : syracuseStep 1726357 = 80923) (by norm_num)
theorem B3454901 : Blo 1534464 3454901 := bbase (se 5 (by rfl) ⟨161948, by rfl⟩ : syracuseStep 3454901 = 323897) (by norm_num)
theorem B1726393 : Blo 1534464 1726393 := bbase (se 2 (by rfl) ⟨647397, by rfl⟩ : syracuseStep 1726393 = 1294795) (by norm_num)
theorem B3889093 : Blo 1534464 3889093 := bbase (se 4 (by rfl) ⟨364602, by rfl⟩ : syracuseStep 3889093 = 729205) (by norm_num)
theorem B1726429 : Blo 1534464 1726429 := bbase (se 3 (by rfl) ⟨323705, by rfl⟩ : syracuseStep 1726429 = 647411) (by norm_num)
theorem B7985141 : Blo 1534464 7985141 := bbase (se 5 (by rfl) ⟨374303, by rfl⟩ : syracuseStep 7985141 = 748607) (by norm_num)
theorem B3454973 : Blo 1534464 3454973 := bbase (se 3 (by rfl) ⟨647807, by rfl⟩ : syracuseStep 3454973 = 1295615) (by norm_num)
theorem B1726465 : Blo 1534464 1726465 := bbase (se 2 (by rfl) ⟨647424, by rfl⟩ : syracuseStep 1726465 = 1294849) (by norm_num)
theorem B1726501 : Blo 1534464 1726501 := bbase (se 4 (by rfl) ⟨161859, by rfl⟩ : syracuseStep 1726501 = 323719) (by norm_num)
theorem B8296501 : Blo 1534464 8296501 := bbase (se 5 (by rfl) ⟨388898, by rfl⟩ : syracuseStep 8296501 = 777797) (by norm_num)
theorem B3455045 : Blo 1534464 3455045 := bbase (se 4 (by rfl) ⟨323910, by rfl⟩ : syracuseStep 3455045 = 647821) (by norm_num)
theorem B2627653 : Blo 1534464 2627653 := bbase (se 4 (by rfl) ⟨246342, by rfl⟩ : syracuseStep 2627653 = 492685) (by norm_num)
theorem B1726537 : Blo 1534464 1726537 := bbase (se 2 (by rfl) ⟨647451, by rfl⟩ : syracuseStep 1726537 = 1294903) (by norm_num)
theorem B2185309 : Blo 1534464 2185309 := bbase (se 3 (by rfl) ⟨409745, by rfl⟩ : syracuseStep 2185309 = 819491) (by norm_num)
theorem B1726573 : Blo 1534464 1726573 := bbase (se 3 (by rfl) ⟨323732, by rfl⟩ : syracuseStep 1726573 = 647465) (by norm_num)
theorem B5183621 : Blo 1534464 5183621 := bbase (se 4 (by rfl) ⟨485964, by rfl⟩ : syracuseStep 5183621 = 971929) (by norm_num)
theorem B3455117 : Blo 1534464 3455117 := bbase (se 3 (by rfl) ⟨647834, by rfl⟩ : syracuseStep 3455117 = 1295669) (by norm_num)
theorem B1726609 : Blo 1534464 1726609 := bbase (se 2 (by rfl) ⟨647478, by rfl⟩ : syracuseStep 1726609 = 1294957) (by norm_num)
theorem B2627749 : Blo 1534464 2627749 := bbase (se 4 (by rfl) ⟨246351, by rfl⟩ : syracuseStep 2627749 = 492703) (by norm_num)
theorem B1726645 : Blo 1534464 1726645 := bbase (se 5 (by rfl) ⟨80936, by rfl⟩ : syracuseStep 1726645 = 161873) (by norm_num)
theorem B3938501 : Blo 1534464 3938501 := bbase (se 4 (by rfl) ⟨369234, by rfl⟩ : syracuseStep 3938501 = 738469) (by norm_num)
theorem B3455189 : Blo 1534464 3455189 := bbase (se 7 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 3455189 = 80981) (by norm_num)
theorem B1726681 : Blo 1534464 1726681 := bbase (se 2 (by rfl) ⟨647505, by rfl⟩ : syracuseStep 1726681 = 1295011) (by norm_num)
theorem B1726717 : Blo 1534464 1726717 := bbase (se 3 (by rfl) ⟨323759, by rfl⟩ : syracuseStep 1726717 = 647519) (by norm_num)
theorem B3455261 : Blo 1534464 3455261 := bbase (se 3 (by rfl) ⟨647861, by rfl⟩ : syracuseStep 3455261 = 1295723) (by norm_num)
theorem B1726753 : Blo 1534464 1726753 := bbase (se 2 (by rfl) ⟨647532, by rfl⟩ : syracuseStep 1726753 = 1295065) (by norm_num)
theorem B1726789 : Blo 1534464 1726789 := bbase (se 4 (by rfl) ⟨161886, by rfl⟩ : syracuseStep 1726789 = 323773) (by norm_num)
theorem B4372805 : Blo 1534464 4372805 := bbase (se 4 (by rfl) ⟨409950, by rfl⟩ : syracuseStep 4372805 = 819901) (by norm_num)
theorem B17733973 : Blo 1534464 17733973 := bbase (se 10 (by rfl) ⟨25977, by rfl⟩ : syracuseStep 17733973 = 51955) (by norm_num)
theorem B3455333 : Blo 1534464 3455333 := bbase (se 4 (by rfl) ⟨323937, by rfl⟩ : syracuseStep 3455333 = 647875) (by norm_num)
theorem B1726825 : Blo 1534464 1726825 := bbase (se 2 (by rfl) ⟨647559, by rfl⟩ : syracuseStep 1726825 = 1295119) (by norm_num)
theorem B1726861 : Blo 1534464 1726861 := bbase (se 3 (by rfl) ⟨323786, by rfl⟩ : syracuseStep 1726861 = 647573) (by norm_num)
theorem B2914717 : Blo 1534464 2914717 := bbase (se 3 (by rfl) ⟨546509, by rfl⟩ : syracuseStep 2914717 = 1093019) (by norm_num)
theorem B1661357 : Blo 1534464 1661357 := bbase (se 3 (by rfl) ⟨311504, by rfl⟩ : syracuseStep 1661357 = 623009) (by norm_num)
theorem B2185645 : Blo 1534464 2185645 := bbase (se 3 (by rfl) ⟨409808, by rfl⟩ : syracuseStep 2185645 = 819617) (by norm_num)
theorem B3455405 : Blo 1534464 3455405 := bbase (se 3 (by rfl) ⟨647888, by rfl⟩ : syracuseStep 3455405 = 1295777) (by norm_num)
theorem B1726897 : Blo 1534464 1726897 := bbase (se 2 (by rfl) ⟨647586, by rfl⟩ : syracuseStep 1726897 = 1295173) (by norm_num)
theorem B6224309 : Blo 1534464 6224309 := bbase (se 5 (by rfl) ⟨291764, by rfl⟩ : syracuseStep 6224309 = 583529) (by norm_num)
theorem B7772597 : Blo 1534464 7772597 := bbase (se 5 (by rfl) ⟨364340, by rfl⟩ : syracuseStep 7772597 = 728681) (by norm_num)
theorem B1726933 : Blo 1534464 1726933 := bbase (se 7 (by rfl) ⟨20237, by rfl⟩ : syracuseStep 1726933 = 40475) (by norm_num)
theorem B6224357 : Blo 1534464 6224357 := bbase (se 4 (by rfl) ⟨583533, by rfl⟩ : syracuseStep 6224357 = 1167067) (by norm_num)
theorem B3455477 : Blo 1534464 3455477 := bbase (se 5 (by rfl) ⟨161975, by rfl⟩ : syracuseStep 3455477 = 323951) (by norm_num)
theorem B1726969 : Blo 1534464 1726969 := bbase (se 2 (by rfl) ⟨647613, by rfl⟩ : syracuseStep 1726969 = 1295227) (by norm_num)
theorem B1727005 : Blo 1534464 1727005 := bbase (se 3 (by rfl) ⟨323813, by rfl⟩ : syracuseStep 1727005 = 647627) (by norm_num)
theorem B2914861 : Blo 1534464 2914861 := bbase (se 3 (by rfl) ⟨546536, by rfl⟩ : syracuseStep 2914861 = 1093073) (by norm_num)
theorem B5184053 : Blo 1534464 5184053 := bbase (se 5 (by rfl) ⟨243002, by rfl⟩ : syracuseStep 5184053 = 486005) (by norm_num)
theorem B3455549 : Blo 1534464 3455549 := bbase (se 3 (by rfl) ⟨647915, by rfl⟩ : syracuseStep 3455549 = 1295831) (by norm_num)
theorem B1727041 : Blo 1534464 1727041 := bbase (se 2 (by rfl) ⟨647640, by rfl⟩ : syracuseStep 1727041 = 1295281) (by norm_num)
theorem B8739413 : Blo 1534464 8739413 := bbase (se 8 (by rfl) ⟨51207, by rfl⟩ : syracuseStep 8739413 = 102415) (by norm_num)
theorem B1727077 : Blo 1534464 1727077 := bbase (se 4 (by rfl) ⟨161913, by rfl⟩ : syracuseStep 1727077 = 323827) (by norm_num)
theorem B2185861 : Blo 1534464 2185861 := bbase (se 4 (by rfl) ⟨204924, by rfl⟩ : syracuseStep 2185861 = 409849) (by norm_num)
theorem B3455621 : Blo 1534464 3455621 := bbase (se 4 (by rfl) ⟨323964, by rfl⟩ : syracuseStep 3455621 = 647929) (by norm_num)
theorem B1727113 : Blo 1534464 1727113 := bbase (se 2 (by rfl) ⟨647667, by rfl⟩ : syracuseStep 1727113 = 1295335) (by norm_num)
theorem B1727149 : Blo 1534464 1727149 := bbase (se 3 (by rfl) ⟨323840, by rfl⟩ : syracuseStep 1727149 = 647681) (by norm_num)
theorem B6560453 : Blo 1534464 6560453 := bbase (se 4 (by rfl) ⟨615042, by rfl⟩ : syracuseStep 6560453 = 1230085) (by norm_num)
theorem B2915021 : Blo 1534464 2915021 := bbase (se 3 (by rfl) ⟨546566, by rfl⟩ : syracuseStep 2915021 = 1093133) (by norm_num)
theorem B3455693 : Blo 1534464 3455693 := bbase (se 3 (by rfl) ⟨647942, by rfl⟩ : syracuseStep 3455693 = 1295885) (by norm_num)
theorem B1727185 : Blo 1534464 1727185 := bbase (se 2 (by rfl) ⟨647694, by rfl⟩ : syracuseStep 1727185 = 1295389) (by norm_num)
theorem B1727221 : Blo 1534464 1727221 := bbase (se 5 (by rfl) ⟨80963, by rfl⟩ : syracuseStep 1727221 = 161927) (by norm_num)
theorem B3455765 : Blo 1534464 3455765 := bbase (se 6 (by rfl) ⟨80994, by rfl⟩ : syracuseStep 3455765 = 161989) (by norm_num)
theorem B1727257 : Blo 1534464 1727257 := bbase (se 2 (by rfl) ⟨647721, by rfl⟩ : syracuseStep 1727257 = 1295443) (by norm_num)
theorem B1997617 : Blo 1534464 1997617 := bbase (se 2 (by rfl) ⟨749106, by rfl⟩ : syracuseStep 1997617 = 1498213) (by norm_num)
theorem B1727293 : Blo 1534464 1727293 := bbase (se 3 (by rfl) ⟨323867, by rfl⟩ : syracuseStep 1727293 = 647735) (by norm_num)
theorem B2915165 : Blo 1534464 2915165 := bbase (se 3 (by rfl) ⟨546593, by rfl⟩ : syracuseStep 2915165 = 1093187) (by norm_num)
theorem B3455837 : Blo 1534464 3455837 := bbase (se 3 (by rfl) ⟨647969, by rfl⟩ : syracuseStep 3455837 = 1295939) (by norm_num)
theorem B1727329 : Blo 1534464 1727329 := bbase (se 2 (by rfl) ⟨647748, by rfl⟩ : syracuseStep 1727329 = 1295497) (by norm_num)
theorem B3111805 : Blo 1534464 3111805 := bbase (se 3 (by rfl) ⟨583463, by rfl⟩ : syracuseStep 3111805 = 1166927) (by norm_num)
theorem B1727365 : Blo 1534464 1727365 := bbase (se 4 (by rfl) ⟨161940, by rfl⟩ : syracuseStep 1727365 = 323881) (by norm_num)
theorem B1751941 : Blo 1534464 1751941 := bbase (se 4 (by rfl) ⟨164244, by rfl⟩ : syracuseStep 1751941 = 328489) (by norm_num)
theorem B2767765 : Blo 1534464 2767765 := bbase (se 6 (by rfl) ⟨64869, by rfl⟩ : syracuseStep 2767765 = 129739) (by norm_num)
theorem B3455909 : Blo 1534464 3455909 := bbase (se 4 (by rfl) ⟨323991, by rfl⟩ : syracuseStep 3455909 = 647983) (by norm_num)
theorem B1727401 : Blo 1534464 1727401 := bbase (se 2 (by rfl) ⟨647775, by rfl⟩ : syracuseStep 1727401 = 1295551) (by norm_num)
theorem B5831621 : Blo 1534464 5831621 := bbase (se 4 (by rfl) ⟨546714, by rfl⟩ : syracuseStep 5831621 = 1093429) (by norm_num)
theorem B1727437 : Blo 1534464 1727437 := bbase (se 3 (by rfl) ⟨323894, by rfl⟩ : syracuseStep 1727437 = 647789) (by norm_num)
theorem B7003093 : Blo 1534464 7003093 := bbase (se 7 (by rfl) ⟨82067, by rfl⟩ : syracuseStep 7003093 = 164135) (by norm_num)
theorem B4373477 : Blo 1534464 4373477 := bbase (se 4 (by rfl) ⟨410013, by rfl⟩ : syracuseStep 4373477 = 820027) (by norm_num)
theorem B5184485 : Blo 1534464 5184485 := bbase (se 4 (by rfl) ⟨486045, by rfl⟩ : syracuseStep 5184485 = 972091) (by norm_num)
theorem B3455981 : Blo 1534464 3455981 := bbase (se 3 (by rfl) ⟨647996, by rfl⟩ : syracuseStep 3455981 = 1295993) (by norm_num)
theorem B1727473 : Blo 1534464 1727473 := bbase (se 2 (by rfl) ⟨647802, by rfl⟩ : syracuseStep 1727473 = 1295605) (by norm_num)
theorem B11066357 : Blo 1534464 11066357 := bbase (se 5 (by rfl) ⟨518735, by rfl⟩ : syracuseStep 11066357 = 1037471) (by norm_num)
theorem B2186237 : Blo 1534464 2186237 := bbase (se 3 (by rfl) ⟨409919, by rfl⟩ : syracuseStep 2186237 = 819839) (by norm_num)
theorem B1727509 : Blo 1534464 1727509 := bbase (se 6 (by rfl) ⟨40488, by rfl⟩ : syracuseStep 1727509 = 80977) (by norm_num)
theorem B3456053 : Blo 1534464 3456053 := bbase (se 5 (by rfl) ⟨162002, by rfl⟩ : syracuseStep 3456053 = 324005) (by norm_num)
theorem B1727545 : Blo 1534464 1727545 := bbase (se 2 (by rfl) ⟨647829, by rfl⟩ : syracuseStep 1727545 = 1295659) (by norm_num)
theorem B1555529 : Blo 1534464 1555529 := bbase (se 2 (by rfl) ⟨583323, by rfl⟩ : syracuseStep 1555529 = 1166647) (by norm_num)
theorem B1727581 : Blo 1534464 1727581 := bbase (se 3 (by rfl) ⟨323921, by rfl⟩ : syracuseStep 1727581 = 647843) (by norm_num)
theorem B2915453 : Blo 1534464 2915453 := bbase (se 3 (by rfl) ⟨546647, by rfl⟩ : syracuseStep 2915453 = 1093295) (by norm_num)
theorem B3456125 : Blo 1534464 3456125 := bbase (se 3 (by rfl) ⟨648023, by rfl⟩ : syracuseStep 3456125 = 1296047) (by norm_num)
theorem B1727617 : Blo 1534464 1727617 := bbase (se 2 (by rfl) ⟨647856, by rfl⟩ : syracuseStep 1727617 = 1295713) (by norm_num)
theorem B1727653 : Blo 1534464 1727653 := bbase (se 4 (by rfl) ⟨161967, by rfl⟩ : syracuseStep 1727653 = 323935) (by norm_num)
theorem B13327541 : Blo 1534464 13327541 := bbase (se 5 (by rfl) ⟨624728, by rfl⟩ : syracuseStep 13327541 = 1249457) (by norm_num)
theorem B3456197 : Blo 1534464 3456197 := bbase (se 4 (by rfl) ⟨324018, by rfl⟩ : syracuseStep 3456197 = 648037) (by norm_num)
theorem B1727689 : Blo 1534464 1727689 := bbase (se 2 (by rfl) ⟨647883, by rfl⟩ : syracuseStep 1727689 = 1295767) (by norm_num)
theorem B5831909 : Blo 1534464 5831909 := bbase (se 4 (by rfl) ⟨546741, by rfl⟩ : syracuseStep 5831909 = 1093483) (by norm_num)
theorem B1727725 : Blo 1534464 1727725 := bbase (se 3 (by rfl) ⟨323948, by rfl⟩ : syracuseStep 1727725 = 647897) (by norm_num)
theorem B3456269 : Blo 1534464 3456269 := bbase (se 3 (by rfl) ⟨648050, by rfl⟩ : syracuseStep 3456269 = 1296101) (by norm_num)
theorem B1727761 : Blo 1534464 1727761 := bbase (se 2 (by rfl) ⟨647910, by rfl⟩ : syracuseStep 1727761 = 1295821) (by norm_num)
theorem B1555733 : Blo 1534464 1555733 := bbase (se 6 (by rfl) ⟨36462, by rfl⟩ : syracuseStep 1555733 = 72925) (by norm_num)
theorem B2915605 : Blo 1534464 2915605 := bbase (se 6 (by rfl) ⟨68334, by rfl⟩ : syracuseStep 2915605 = 136669) (by norm_num)
theorem B1727797 : Blo 1534464 1727797 := bbase (se 5 (by rfl) ⟨80990, by rfl⟩ : syracuseStep 1727797 = 161981) (by norm_num)
theorem B3456341 : Blo 1534464 3456341 := bbase (se 11 (by rfl) ⟨2531, by rfl⟩ : syracuseStep 3456341 = 5063) (by norm_num)
theorem B1727833 : Blo 1534464 1727833 := bbase (se 2 (by rfl) ⟨647937, by rfl⟩ : syracuseStep 1727833 = 1295875) (by norm_num)
theorem B7380341 : Blo 1534464 7380341 := bbase (se 5 (by rfl) ⟨345953, by rfl⟩ : syracuseStep 7380341 = 691907) (by norm_num)
theorem B1727869 : Blo 1534464 1727869 := bbase (se 3 (by rfl) ⟨323975, by rfl⟩ : syracuseStep 1727869 = 647951) (by norm_num)
theorem B2768269 : Blo 1534464 2768269 := bbase (se 3 (by rfl) ⟨519050, by rfl⟩ : syracuseStep 2768269 = 1038101) (by norm_num)
theorem B4373909 : Blo 1534464 4373909 := bbase (se 6 (by rfl) ⟨102513, by rfl⟩ : syracuseStep 4373909 = 205027) (by norm_num)
theorem B5184917 : Blo 1534464 5184917 := bbase (se 6 (by rfl) ⟨121521, by rfl⟩ : syracuseStep 5184917 = 243043) (by norm_num)
theorem B3112349 : Blo 1534464 3112349 := bbase (se 3 (by rfl) ⟨583565, by rfl⟩ : syracuseStep 3112349 = 1167131) (by norm_num)
theorem B3456413 : Blo 1534464 3456413 := bbase (se 3 (by rfl) ⟨648077, by rfl⟩ : syracuseStep 3456413 = 1296155) (by norm_num)
theorem B1727905 : Blo 1534464 1727905 := bbase (se 2 (by rfl) ⟨647964, by rfl⟩ : syracuseStep 1727905 = 1295929) (by norm_num)
theorem B1727941 : Blo 1534464 1727941 := bbase (se 4 (by rfl) ⟨161994, by rfl⟩ : syracuseStep 1727941 = 323989) (by norm_num)
theorem B3456485 : Blo 1534464 3456485 := bbase (se 4 (by rfl) ⟨324045, by rfl⟩ : syracuseStep 3456485 = 648091) (by norm_num)
theorem B1727977 : Blo 1534464 1727977 := bbase (se 2 (by rfl) ⟨647991, by rfl⟩ : syracuseStep 1727977 = 1295983) (by norm_num)
theorem B1728013 : Blo 1534464 1728013 := bbase (se 3 (by rfl) ⟨324002, by rfl⟩ : syracuseStep 1728013 = 648005) (by norm_num)
theorem B13123093 : Blo 1534464 13123093 := bbase (se 6 (by rfl) ⟨307572, by rfl⟩ : syracuseStep 13123093 = 615145) (by norm_num)
theorem B3456557 : Blo 1534464 3456557 := bbase (se 3 (by rfl) ⟨648104, by rfl⟩ : syracuseStep 3456557 = 1296209) (by norm_num)
theorem B1728049 : Blo 1534464 1728049 := bbase (se 2 (by rfl) ⟨648018, by rfl⟩ : syracuseStep 1728049 = 1296037) (by norm_num)
theorem B2915909 : Blo 1534464 2915909 := bbase (se 4 (by rfl) ⟨273366, by rfl⟩ : syracuseStep 2915909 = 546733) (by norm_num)
theorem B1728085 : Blo 1534464 1728085 := bbase (se 8 (by rfl) ⟨10125, by rfl⟩ : syracuseStep 1728085 = 20251) (by norm_num)
theorem B3456629 : Blo 1534464 3456629 := bbase (se 5 (by rfl) ⟨162029, by rfl⟩ : syracuseStep 3456629 = 324059) (by norm_num)
theorem B1728121 : Blo 1534464 1728121 := bbase (se 2 (by rfl) ⟨648045, by rfl⟩ : syracuseStep 1728121 = 1296091) (by norm_num)
theorem B1728157 : Blo 1534464 1728157 := bbase (se 3 (by rfl) ⟨324029, by rfl⟩ : syracuseStep 1728157 = 648059) (by norm_num)
theorem B6561445 : Blo 1534464 6561445 := bbase (se 4 (by rfl) ⟨615135, by rfl⟩ : syracuseStep 6561445 = 1230271) (by norm_num)
theorem B3456701 : Blo 1534464 3456701 := bbase (se 3 (by rfl) ⟨648131, by rfl⟩ : syracuseStep 3456701 = 1296263) (by norm_num)
theorem B1728193 : Blo 1534464 1728193 := bbase (se 2 (by rfl) ⟨648072, by rfl⟩ : syracuseStep 1728193 = 1296145) (by norm_num)
theorem B7773893 : Blo 1534464 7773893 := bbase (se 4 (by rfl) ⟨728802, by rfl⟩ : syracuseStep 7773893 = 1457605) (by norm_num)
theorem B1728229 : Blo 1534464 1728229 := bbase (se 4 (by rfl) ⟨162021, by rfl⟩ : syracuseStep 1728229 = 324043) (by norm_num)
theorem B2301701 : Blo 1534464 2301701 := bbase (se 4 (by rfl) ⟨215784, by rfl⟩ : syracuseStep 2301701 = 431569) (by norm_num)
theorem B3456773 : Blo 1534464 3456773 := bbase (se 4 (by rfl) ⟨324072, by rfl⟩ : syracuseStep 3456773 = 648145) (by norm_num)
theorem B1728265 : Blo 1534464 1728265 := bbase (se 2 (by rfl) ⟨648099, by rfl⟩ : syracuseStep 1728265 = 1296199) (by norm_num)
theorem B2301725 : Blo 1534464 2301725 := bbase (se 3 (by rfl) ⟨431573, by rfl⟩ : syracuseStep 2301725 = 863147) (by norm_num)
theorem B1728301 : Blo 1534464 1728301 := bbase (se 3 (by rfl) ⟨324056, by rfl⟩ : syracuseStep 1728301 = 648113) (by norm_num)
theorem B2301749 : Blo 1534464 2301749 := bbase (se 5 (by rfl) ⟨107894, by rfl⟩ : syracuseStep 2301749 = 215789) (by norm_num)
theorem B5185349 : Blo 1534464 5185349 := bbase (se 4 (by rfl) ⟨486126, by rfl⟩ : syracuseStep 5185349 = 972253) (by norm_num)
theorem B2301773 : Blo 1534464 2301773 := bbase (se 3 (by rfl) ⟨431582, by rfl⟩ : syracuseStep 2301773 = 863165) (by norm_num)
theorem B3456845 : Blo 1534464 3456845 := bbase (se 3 (by rfl) ⟨648158, by rfl⟩ : syracuseStep 3456845 = 1296317) (by norm_num)
theorem B1728337 : Blo 1534464 1728337 := bbase (se 2 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 1728337 = 1296253) (by norm_num)
theorem B6225749 : Blo 1534464 6225749 := bbase (se 9 (by rfl) ⟨18239, by rfl⟩ : syracuseStep 6225749 = 36479) (by norm_num)
theorem B2301797 : Blo 1534464 2301797 := bbase (se 4 (by rfl) ⟨215793, by rfl⟩ : syracuseStep 2301797 = 431587) (by norm_num)
theorem B1728373 : Blo 1534464 1728373 := bbase (se 5 (by rfl) ⟨81017, by rfl⟩ : syracuseStep 1728373 = 162035) (by norm_num)
theorem B2301821 : Blo 1534464 2301821 := bbase (se 3 (by rfl) ⟨431591, by rfl⟩ : syracuseStep 2301821 = 863183) (by norm_num)
theorem B2301845 : Blo 1534464 2301845 := bbase (se 6 (by rfl) ⟨53949, by rfl⟩ : syracuseStep 2301845 = 107899) (by norm_num)
theorem B3456917 : Blo 1534464 3456917 := bbase (se 6 (by rfl) ⟨81021, by rfl⟩ : syracuseStep 3456917 = 162043) (by norm_num)
theorem B1728409 : Blo 1534464 1728409 := bbase (se 2 (by rfl) ⟨648153, by rfl⟩ : syracuseStep 1728409 = 1296307) (by norm_num)
theorem B2301869 : Blo 1534464 2301869 := bbase (se 3 (by rfl) ⟨431600, by rfl⟩ : syracuseStep 2301869 = 863201) (by norm_num)
theorem B1728445 : Blo 1534464 1728445 := bbase (se 3 (by rfl) ⟨324083, by rfl⟩ : syracuseStep 1728445 = 648167) (by norm_num)
theorem B2301893 : Blo 1534464 2301893 := bbase (se 4 (by rfl) ⟨215802, by rfl⟩ : syracuseStep 2301893 = 431605) (by norm_num)
theorem B2301917 : Blo 1534464 2301917 := bbase (se 3 (by rfl) ⟨431609, by rfl⟩ : syracuseStep 2301917 = 863219) (by norm_num)
theorem B3456989 : Blo 1534464 3456989 := bbase (se 3 (by rfl) ⟨648185, by rfl⟩ : syracuseStep 3456989 = 1296371) (by norm_num)
theorem B1728481 : Blo 1534464 1728481 := bbase (se 2 (by rfl) ⟨648180, by rfl⟩ : syracuseStep 1728481 = 1296361) (by norm_num)
theorem B3112933 : Blo 1534464 3112933 := bbase (se 4 (by rfl) ⟨291837, by rfl⟩ : syracuseStep 3112933 = 583675) (by norm_num)
theorem B2301941 : Blo 1534464 2301941 := bbase (se 5 (by rfl) ⟨107903, by rfl⟩ : syracuseStep 2301941 = 215807) (by norm_num)
theorem B2301953 : Blo 1534464 2301953 := bstep (se 2 (by rfl) ⟨863232, by rfl⟩ : syracuseStep 2301953 = 1726465) B1726465
theorem B2301971 : Blo 1534464 2301971 := bstep (se 1 (by rfl) ⟨1726478, by rfl⟩ : syracuseStep 2301971 = 3452957) B3452957
theorem B2302001 : Blo 1534464 2302001 := bstep (se 2 (by rfl) ⟨863250, by rfl⟩ : syracuseStep 2302001 = 1726501) B1726501
theorem B2302019 : Blo 1534464 2302019 := bstep (se 1 (by rfl) ⟨1726514, by rfl⟩ : syracuseStep 2302019 = 3453029) B3453029
theorem B2302049 : Blo 1534464 2302049 := bstep (se 2 (by rfl) ⟨863268, by rfl⟩ : syracuseStep 2302049 = 1726537) B1726537
theorem B2302067 : Blo 1534464 2302067 := bstep (se 1 (by rfl) ⟨1726550, by rfl⟩ : syracuseStep 2302067 = 3453101) B3453101
theorem B2302097 : Blo 1534464 2302097 := bstep (se 2 (by rfl) ⟨863286, by rfl⟩ : syracuseStep 2302097 = 1726573) B1726573
theorem B2302115 : Blo 1534464 2302115 := bstep (se 1 (by rfl) ⟨1726586, by rfl⟩ : syracuseStep 2302115 = 3453173) B3453173
theorem B5832881 : Blo 1534464 5832881 := bstep (se 2 (by rfl) ⟨2187330, by rfl⟩ : syracuseStep 5832881 = 4374661) B4374661
theorem B2302145 : Blo 1534464 2302145 := bstep (se 2 (by rfl) ⟨863304, by rfl⟩ : syracuseStep 2302145 = 1726609) B1726609
theorem B2302163 : Blo 1534464 2302163 := bstep (se 1 (by rfl) ⟨1726622, by rfl⟩ : syracuseStep 2302163 = 3453245) B3453245
theorem B2302193 : Blo 1534464 2302193 := bstep (se 2 (by rfl) ⟨863322, by rfl⟩ : syracuseStep 2302193 = 1726645) B1726645
theorem B2302211 : Blo 1534464 2302211 := bstep (se 1 (by rfl) ⟨1726658, by rfl⟩ : syracuseStep 2302211 = 3453317) B3453317
theorem B2302241 : Blo 1534464 2302241 := bstep (se 2 (by rfl) ⟨863340, by rfl⟩ : syracuseStep 2302241 = 1726681) B1726681
theorem B2302259 : Blo 1534464 2302259 := bstep (se 1 (by rfl) ⟨1726694, by rfl⟩ : syracuseStep 2302259 = 3453389) B3453389
theorem B2187587 : Blo 1534464 2187587 := bstep (se 1 (by rfl) ⟨1640690, by rfl⟩ : syracuseStep 2187587 = 3281381) B3281381
theorem B7774541 : Blo 1534464 7774541 := bstep (se 3 (by rfl) ⟨1457726, by rfl⟩ : syracuseStep 7774541 = 2915453) B2915453
theorem B2302289 : Blo 1534464 2302289 := bstep (se 2 (by rfl) ⟨863358, by rfl⟩ : syracuseStep 2302289 = 1726717) B1726717
theorem B2302307 : Blo 1534464 2302307 := bstep (se 1 (by rfl) ⟨1726730, by rfl⟩ : syracuseStep 2302307 = 3453461) B3453461
theorem B1843571 : Blo 1534464 1843571 := bstep (se 1 (by rfl) ⟨1382678, by rfl⟩ : syracuseStep 1843571 = 2765357) B2765357
theorem B2302337 : Blo 1534464 2302337 := bstep (se 2 (by rfl) ⟨863376, by rfl⟩ : syracuseStep 2302337 = 1726753) B1726753
theorem B2302355 : Blo 1534464 2302355 := bstep (se 1 (by rfl) ⟨1726766, by rfl⟩ : syracuseStep 2302355 = 3453533) B3453533
theorem B2302385 : Blo 1534464 2302385 := bstep (se 2 (by rfl) ⟨863394, by rfl⟩ : syracuseStep 2302385 = 1726789) B1726789
theorem B2302403 : Blo 1534464 2302403 := bstep (se 1 (by rfl) ⟨1726802, by rfl⟩ : syracuseStep 2302403 = 3453605) B3453605
theorem B2302433 : Blo 1534464 2302433 := bstep (se 2 (by rfl) ⟨863412, by rfl⟩ : syracuseStep 2302433 = 1726825) B1726825
theorem B7381475 : Blo 1534464 7381475 := bstep (se 1 (by rfl) ⟨5536106, by rfl⟩ : syracuseStep 7381475 = 11072213) B11072213
theorem B2302451 : Blo 1534464 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B10502669 : Blo 1534464 10502669 := bstep (se 3 (by rfl) ⟨1969250, by rfl⟩ : syracuseStep 10502669 = 3938501) B3938501
theorem B2302481 : Blo 1534464 2302481 := bstep (se 2 (by rfl) ⟨863430, by rfl⟩ : syracuseStep 2302481 = 1726861) B1726861
theorem B2916881 : Blo 1534464 2916881 := bstep (se 2 (by rfl) ⟨1093830, by rfl⟩ : syracuseStep 2916881 = 2187661) B2187661
theorem B2302499 : Blo 1534464 2302499 := bstep (se 1 (by rfl) ⟨1726874, by rfl⟩ : syracuseStep 2302499 = 3453749) B3453749
theorem B2302529 : Blo 1534464 2302529 := bstep (se 2 (by rfl) ⟨863448, by rfl⟩ : syracuseStep 2302529 = 1726897) B1726897
theorem B2302547 : Blo 1534464 2302547 := bstep (se 1 (by rfl) ⟨1726910, by rfl⟩ : syracuseStep 2302547 = 3453821) B3453821
theorem B6562403 : Blo 1534464 6562403 := bstep (se 1 (by rfl) ⟨4921802, by rfl⟩ : syracuseStep 6562403 = 9843605) B9843605
theorem B2302577 : Blo 1534464 2302577 := bstep (se 2 (by rfl) ⟨863466, by rfl⟩ : syracuseStep 2302577 = 1726933) B1726933
theorem B1942147 : Blo 1534464 1942147 := bstep (se 1 (by rfl) ⟨1456610, by rfl⟩ : syracuseStep 1942147 = 2913221) B2913221
theorem B2302595 : Blo 1534464 2302595 := bstep (se 1 (by rfl) ⟨1726946, by rfl⟩ : syracuseStep 2302595 = 3453893) B3453893
theorem B9839245 : Blo 1534464 9839245 := bstep (se 3 (by rfl) ⟨1844858, by rfl⟩ : syracuseStep 9839245 = 3689717) B3689717
theorem B2302625 : Blo 1534464 2302625 := bstep (se 2 (by rfl) ⟨863484, by rfl⟩ : syracuseStep 2302625 = 1726969) B1726969
theorem B6226595 : Blo 1534464 6226595 := bstep (se 1 (by rfl) ⟨4669946, by rfl⟩ : syracuseStep 6226595 = 9339893) B9339893
theorem B2302643 : Blo 1534464 2302643 := bstep (se 1 (by rfl) ⟨1726982, by rfl⟩ : syracuseStep 2302643 = 3453965) B3453965
theorem B3596995 : Blo 1534464 3596995 := bstep (se 1 (by rfl) ⟨2697746, by rfl⟩ : syracuseStep 3596995 = 5395493) B5395493
theorem B2302673 : Blo 1534464 2302673 := bstep (se 2 (by rfl) ⟨863502, by rfl⟩ : syracuseStep 2302673 = 1727005) B1727005
theorem B2302691 : Blo 1534464 2302691 := bstep (se 1 (by rfl) ⟨1727018, by rfl⟩ : syracuseStep 2302691 = 3454037) B3454037
theorem B2302721 : Blo 1534464 2302721 := bstep (se 2 (by rfl) ⟨863520, by rfl⟩ : syracuseStep 2302721 = 1727041) B1727041
theorem B2302739 : Blo 1534464 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B2589475 : Blo 1534464 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B6226723 : Blo 1534464 6226723 := bstep (se 1 (by rfl) ⟨4670042, by rfl⟩ : syracuseStep 6226723 = 9340085) B9340085
theorem B2302769 : Blo 1534464 2302769 := bstep (se 2 (by rfl) ⟨863538, by rfl⟩ : syracuseStep 2302769 = 1727077) B1727077
theorem B2302787 : Blo 1534464 2302787 := bstep (se 1 (by rfl) ⟨1727090, by rfl⟩ : syracuseStep 2302787 = 3454181) B3454181
theorem B2302817 : Blo 1534464 2302817 := bstep (se 2 (by rfl) ⟨863556, by rfl⟩ : syracuseStep 2302817 = 1727113) B1727113
theorem B2302835 : Blo 1534464 2302835 := bstep (se 1 (by rfl) ⟨1727126, by rfl⟩ : syracuseStep 2302835 = 3454253) B3454253
theorem B3367811 : Blo 1534464 3367811 := bstep (se 1 (by rfl) ⟨2525858, by rfl⟩ : syracuseStep 3367811 = 5051717) B5051717
theorem B2302865 : Blo 1534464 2302865 := bstep (se 2 (by rfl) ⟨863574, by rfl⟩ : syracuseStep 2302865 = 1727149) B1727149
theorem B2302883 : Blo 1534464 2302883 := bstep (se 1 (by rfl) ⟨1727162, by rfl⟩ : syracuseStep 2302883 = 3454325) B3454325
theorem B2589617 : Blo 1534464 2589617 := bstep (se 2 (by rfl) ⟨971106, by rfl⟩ : syracuseStep 2589617 = 1942213) B1942213
theorem B2302913 : Blo 1534464 2302913 := bstep (se 2 (by rfl) ⟨863592, by rfl⟩ : syracuseStep 2302913 = 1727185) B1727185
theorem B1639379 : Blo 1534464 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B2302931 : Blo 1534464 2302931 := bstep (se 1 (by rfl) ⟨1727198, by rfl⟩ : syracuseStep 2302931 = 3454397) B3454397
theorem B2458595 : Blo 1534464 2458595 := bstep (se 1 (by rfl) ⟨1843946, by rfl⟩ : syracuseStep 2458595 = 3687893) B3687893
theorem B8750051 : Blo 1534464 8750051 := bstep (se 1 (by rfl) ⟨6562538, by rfl⟩ : syracuseStep 8750051 = 13125077) B13125077
theorem B2302961 : Blo 1534464 2302961 := bstep (se 2 (by rfl) ⟨863610, by rfl⟩ : syracuseStep 2302961 = 1727221) B1727221
theorem B2302979 : Blo 1534464 2302979 := bstep (se 1 (by rfl) ⟨1727234, by rfl⟩ : syracuseStep 2302979 = 3454469) B3454469
theorem B2303009 : Blo 1534464 2303009 := bstep (se 2 (by rfl) ⟨863628, by rfl⟩ : syracuseStep 2303009 = 1727257) B1727257
theorem B2589745 : Blo 1534464 2589745 := bstep (se 2 (by rfl) ⟨971154, by rfl⟩ : syracuseStep 2589745 = 1942309) B1942309
theorem B2303027 : Blo 1534464 2303027 := bstep (se 1 (by rfl) ⟨1727270, by rfl⟩ : syracuseStep 2303027 = 3454541) B3454541
theorem B2663489 : Blo 1534464 2663489 := bstep (se 2 (by rfl) ⟨998808, by rfl⟩ : syracuseStep 2663489 = 1997617) B1997617
theorem B8299597 : Blo 1534464 8299597 := bstep (se 3 (by rfl) ⟨1556174, by rfl⟩ : syracuseStep 8299597 = 3112349) B3112349
theorem B2303057 : Blo 1534464 2303057 := bstep (se 2 (by rfl) ⟨863646, by rfl⟩ : syracuseStep 2303057 = 1727293) B1727293
theorem B2589779 : Blo 1534464 2589779 := bstep (se 1 (by rfl) ⟨1942334, by rfl⟩ : syracuseStep 2589779 = 3884669) B3884669
theorem B2303075 : Blo 1534464 2303075 := bstep (se 1 (by rfl) ⟨1727306, by rfl⟩ : syracuseStep 2303075 = 3454613) B3454613
theorem B1942643 : Blo 1534464 1942643 := bstep (se 1 (by rfl) ⟨1456982, by rfl⟩ : syracuseStep 1942643 = 2913965) B2913965
theorem B2303105 : Blo 1534464 2303105 := bstep (se 2 (by rfl) ⟨863664, by rfl⟩ : syracuseStep 2303105 = 1727329) B1727329
theorem B4916369 : Blo 1534464 4916369 := bstep (se 2 (by rfl) ⟨1843638, by rfl⟩ : syracuseStep 4916369 = 3687277) B3687277
theorem B2303123 : Blo 1534464 2303123 := bstep (se 1 (by rfl) ⟨1727342, by rfl⟩ : syracuseStep 2303123 = 3454685) B3454685
theorem B2303153 : Blo 1534464 2303153 := bstep (se 2 (by rfl) ⟨863682, by rfl⟩ : syracuseStep 2303153 = 1727365) B1727365
theorem B2335921 : Blo 1534464 2335921 := bstep (se 2 (by rfl) ⟨875970, by rfl⟩ : syracuseStep 2335921 = 1751941) B1751941
theorem B2303171 : Blo 1534464 2303171 := bstep (se 1 (by rfl) ⟨1727378, by rfl⟩ : syracuseStep 2303171 = 3454757) B3454757
theorem B2589907 : Blo 1534464 2589907 := bstep (se 1 (by rfl) ⟨1942430, by rfl⟩ : syracuseStep 2589907 = 3884861) B3884861
theorem B2303201 : Blo 1534464 2303201 := bstep (se 2 (by rfl) ⟨863700, by rfl⟩ : syracuseStep 2303201 = 1727401) B1727401
theorem B2303219 : Blo 1534464 2303219 := bstep (se 1 (by rfl) ⟨1727414, by rfl⟩ : syracuseStep 2303219 = 3454829) B3454829
theorem B2458883 : Blo 1534464 2458883 := bstep (se 1 (by rfl) ⟨1844162, by rfl⟩ : syracuseStep 2458883 = 3688325) B3688325
theorem B4916497 : Blo 1534464 4916497 := bstep (se 2 (by rfl) ⟨1843686, by rfl⟩ : syracuseStep 4916497 = 3687373) B3687373
theorem B2303249 : Blo 1534464 2303249 := bstep (se 2 (by rfl) ⟨863718, by rfl⟩ : syracuseStep 2303249 = 1727437) B1727437
theorem B2303267 : Blo 1534464 2303267 := bstep (se 1 (by rfl) ⟨1727450, by rfl⟩ : syracuseStep 2303267 = 3454901) B3454901
theorem B2245937 : Blo 1534464 2245937 := bstep (se 2 (by rfl) ⟨842226, by rfl⟩ : syracuseStep 2245937 = 1684453) B1684453
theorem B2303297 : Blo 1534464 2303297 := bstep (se 2 (by rfl) ⟨863736, by rfl⟩ : syracuseStep 2303297 = 1727473) B1727473
theorem B2303315 : Blo 1534464 2303315 := bstep (se 1 (by rfl) ⟨1727486, by rfl⟩ : syracuseStep 2303315 = 3454973) B3454973
theorem B2590049 : Blo 1534464 2590049 := bstep (se 2 (by rfl) ⟨971268, by rfl⟩ : syracuseStep 2590049 = 1942537) B1942537
theorem B2303345 : Blo 1534464 2303345 := bstep (se 2 (by rfl) ⟨863754, by rfl⟩ : syracuseStep 2303345 = 1727509) B1727509
theorem B2303363 : Blo 1534464 2303363 := bstep (se 1 (by rfl) ⟨1727522, by rfl⟩ : syracuseStep 2303363 = 3455045) B3455045
theorem B2303393 : Blo 1534464 2303393 := bstep (se 2 (by rfl) ⟨863772, by rfl⟩ : syracuseStep 2303393 = 1727545) B1727545
theorem B2303411 : Blo 1534464 2303411 := bstep (se 1 (by rfl) ⟨1727558, by rfl⟩ : syracuseStep 2303411 = 3455117) B3455117
theorem B2303441 : Blo 1534464 2303441 := bstep (se 2 (by rfl) ⟨863790, by rfl⟩ : syracuseStep 2303441 = 1727581) B1727581
theorem B2590177 : Blo 1534464 2590177 := bstep (se 2 (by rfl) ⟨971316, by rfl⟩ : syracuseStep 2590177 = 1942633) B1942633
theorem B6555107 : Blo 1534464 6555107 := bstep (se 1 (by rfl) ⟨4916330, by rfl⟩ : syracuseStep 6555107 = 9832661) B9832661
theorem B2459107 : Blo 1534464 2459107 := bstep (se 1 (by rfl) ⟨1844330, by rfl⟩ : syracuseStep 2459107 = 3688661) B3688661
theorem B2303459 : Blo 1534464 2303459 := bstep (se 1 (by rfl) ⟨1727594, by rfl⟩ : syracuseStep 2303459 = 3455189) B3455189
theorem B11666915 : Blo 1534464 11666915 := bstep (se 1 (by rfl) ⟨8750186, by rfl⟩ : syracuseStep 11666915 = 17500373) B17500373
theorem B2303489 : Blo 1534464 2303489 := bstep (se 2 (by rfl) ⟨863808, by rfl⟩ : syracuseStep 2303489 = 1727617) B1727617
theorem B2590211 : Blo 1534464 2590211 := bstep (se 1 (by rfl) ⟨1942658, by rfl⟩ : syracuseStep 2590211 = 3885317) B3885317
theorem B4916753 : Blo 1534464 4916753 := bstep (se 2 (by rfl) ⟨1843782, by rfl⟩ : syracuseStep 4916753 = 3687565) B3687565
theorem B2303507 : Blo 1534464 2303507 := bstep (se 1 (by rfl) ⟨1727630, by rfl⟩ : syracuseStep 2303507 = 3455261) B3455261
theorem B2303537 : Blo 1534464 2303537 := bstep (se 2 (by rfl) ⟨863826, by rfl⟩ : syracuseStep 2303537 = 1727653) B1727653
theorem B2303555 : Blo 1534464 2303555 := bstep (se 1 (by rfl) ⟨1727666, by rfl⟩ : syracuseStep 2303555 = 3455333) B3455333
theorem B2303585 : Blo 1534464 2303585 := bstep (se 2 (by rfl) ⟨863844, by rfl⟩ : syracuseStep 2303585 = 1727689) B1727689
theorem B2303603 : Blo 1534464 2303603 := bstep (se 1 (by rfl) ⟨1727702, by rfl⟩ : syracuseStep 2303603 = 3455405) B3455405
theorem B2590339 : Blo 1534464 2590339 := bstep (se 1 (by rfl) ⟨1942754, by rfl⟩ : syracuseStep 2590339 = 3885509) B3885509
theorem B2303633 : Blo 1534464 2303633 := bstep (se 2 (by rfl) ⟨863862, by rfl⟩ : syracuseStep 2303633 = 1727725) B1727725
theorem B2303651 : Blo 1534464 2303651 := bstep (se 1 (by rfl) ⟨1727738, by rfl⟩ : syracuseStep 2303651 = 3455477) B3455477
theorem B2303681 : Blo 1534464 2303681 := bstep (se 2 (by rfl) ⟨863880, by rfl⟩ : syracuseStep 2303681 = 1727761) B1727761
theorem B5179085 : Blo 1534464 5179085 := bstep (se 3 (by rfl) ⟨971078, by rfl⟩ : syracuseStep 5179085 = 1942157) B1942157
theorem B2303699 : Blo 1534464 2303699 := bstep (se 1 (by rfl) ⟨1727774, by rfl⟩ : syracuseStep 2303699 = 3455549) B3455549
theorem B5826275 : Blo 1534464 5826275 := bstep (se 1 (by rfl) ⟨4369706, by rfl⟩ : syracuseStep 5826275 = 8739413) B8739413
theorem B5826289 : Blo 1534464 5826289 := bstep (se 2 (by rfl) ⟨2184858, by rfl⟩ : syracuseStep 5826289 = 4369717) B4369717
theorem B2303729 : Blo 1534464 2303729 := bstep (se 2 (by rfl) ⟨863898, by rfl⟩ : syracuseStep 2303729 = 1727797) B1727797
theorem B5179139 : Blo 1534464 5179139 := bstep (se 1 (by rfl) ⟨3884354, by rfl⟩ : syracuseStep 5179139 = 7768709) B7768709
theorem B2303747 : Blo 1534464 2303747 := bstep (se 1 (by rfl) ⟨1727810, by rfl⟩ : syracuseStep 2303747 = 3455621) B3455621
theorem B9971461 : Blo 1534464 9971461 := bstep (se 4 (by rfl) ⟨934824, by rfl⟩ : syracuseStep 9971461 = 1869649) B1869649
theorem B2590481 : Blo 1534464 2590481 := bstep (se 2 (by rfl) ⟨971430, by rfl⟩ : syracuseStep 2590481 = 1942861) B1942861
theorem B2303777 : Blo 1534464 2303777 := bstep (se 2 (by rfl) ⟨863916, by rfl⟩ : syracuseStep 2303777 = 1727833) B1727833
theorem B1943347 : Blo 1534464 1943347 := bstep (se 1 (by rfl) ⟨1457510, by rfl⟩ : syracuseStep 1943347 = 2915021) B2915021
theorem B2303795 : Blo 1534464 2303795 := bstep (se 1 (by rfl) ⟨1727846, by rfl⟩ : syracuseStep 2303795 = 3455693) B3455693
theorem B3884881 : Blo 1534464 3884881 := bstep (se 2 (by rfl) ⟨1456830, by rfl⟩ : syracuseStep 3884881 = 2913661) B2913661
theorem B2303825 : Blo 1534464 2303825 := bstep (se 2 (by rfl) ⟨863934, by rfl⟩ : syracuseStep 2303825 = 1727869) B1727869
theorem B2303843 : Blo 1534464 2303843 := bstep (se 1 (by rfl) ⟨1727882, by rfl⟩ : syracuseStep 2303843 = 3455765) B3455765
theorem B2303873 : Blo 1534464 2303873 := bstep (se 2 (by rfl) ⟨863952, by rfl⟩ : syracuseStep 2303873 = 1727905) B1727905
theorem B3278723 : Blo 1534464 3278723 := bstep (se 1 (by rfl) ⟨2459042, by rfl⟩ : syracuseStep 3278723 = 4918085) B4918085
theorem B11986829 : Blo 1534464 11986829 := bstep (se 3 (by rfl) ⟨2247530, by rfl⟩ : syracuseStep 11986829 = 4495061) B4495061
theorem B2590609 : Blo 1534464 2590609 := bstep (se 2 (by rfl) ⟨971478, by rfl⟩ : syracuseStep 2590609 = 1942957) B1942957
theorem B1943443 : Blo 1534464 1943443 := bstep (se 1 (by rfl) ⟨1457582, by rfl⟩ : syracuseStep 1943443 = 2915165) B2915165
theorem B2303891 : Blo 1534464 2303891 := bstep (se 1 (by rfl) ⟨1727918, by rfl⟩ : syracuseStep 2303891 = 3455837) B3455837
theorem B2303921 : Blo 1534464 2303921 := bstep (se 2 (by rfl) ⟨863970, by rfl⟩ : syracuseStep 2303921 = 1727941) B1727941
theorem B2590643 : Blo 1534464 2590643 := bstep (se 1 (by rfl) ⟨1942982, by rfl⟩ : syracuseStep 2590643 = 3885965) B3885965
theorem B2303939 : Blo 1534464 2303939 := bstep (se 1 (by rfl) ⟨1727954, by rfl⟩ : syracuseStep 2303939 = 3455909) B3455909
theorem B2303969 : Blo 1534464 2303969 := bstep (se 2 (by rfl) ⟨863988, by rfl⟩ : syracuseStep 2303969 = 1727977) B1727977
theorem B2303987 : Blo 1534464 2303987 := bstep (se 1 (by rfl) ⟨1727990, by rfl⟩ : syracuseStep 2303987 = 3455981) B3455981
theorem B5179409 : Blo 1534464 5179409 := bstep (se 2 (by rfl) ⟨1942278, by rfl⟩ : syracuseStep 5179409 = 3884557) B3884557
theorem B2304017 : Blo 1534464 2304017 := bstep (se 2 (by rfl) ⟨864006, by rfl⟩ : syracuseStep 2304017 = 1728013) B1728013
theorem B2304035 : Blo 1534464 2304035 := bstep (se 1 (by rfl) ⟨1728026, by rfl⟩ : syracuseStep 2304035 = 3456053) B3456053
theorem B2590771 : Blo 1534464 2590771 := bstep (se 1 (by rfl) ⟨1943078, by rfl⟩ : syracuseStep 2590771 = 3886157) B3886157
theorem B2304065 : Blo 1534464 2304065 := bstep (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) B1728049
theorem B2304083 : Blo 1534464 2304083 := bstep (se 1 (by rfl) ⟨1728062, by rfl⟩ : syracuseStep 2304083 = 3456125) B3456125
theorem B3885155 : Blo 1534464 3885155 := bstep (se 1 (by rfl) ⟨2913866, by rfl⟩ : syracuseStep 3885155 = 5827733) B5827733
theorem B2304113 : Blo 1534464 2304113 := bstep (se 2 (by rfl) ⟨864042, by rfl⟩ : syracuseStep 2304113 = 1728085) B1728085
theorem B2304131 : Blo 1534464 2304131 := bstep (se 1 (by rfl) ⟨1728098, by rfl⟩ : syracuseStep 2304131 = 3456197) B3456197
theorem B2304161 : Blo 1534464 2304161 := bstep (se 2 (by rfl) ⟨864060, by rfl⟩ : syracuseStep 2304161 = 1728121) B1728121
theorem B2459825 : Blo 1534464 2459825 := bstep (se 2 (by rfl) ⟨922434, by rfl⟩ : syracuseStep 2459825 = 1844869) B1844869
theorem B2304179 : Blo 1534464 2304179 := bstep (se 1 (by rfl) ⟨1728134, by rfl⟩ : syracuseStep 2304179 = 3456269) B3456269
theorem B2590913 : Blo 1534464 2590913 := bstep (se 2 (by rfl) ⟨971592, by rfl⟩ : syracuseStep 2590913 = 1943185) B1943185
theorem B2304209 : Blo 1534464 2304209 := bstep (se 2 (by rfl) ⟨864078, by rfl⟩ : syracuseStep 2304209 = 1728157) B1728157
theorem B2304227 : Blo 1534464 2304227 := bstep (se 1 (by rfl) ⟨1728170, by rfl⟩ : syracuseStep 2304227 = 3456341) B3456341
theorem B2304257 : Blo 1534464 2304257 := bstep (se 2 (by rfl) ⟨864096, by rfl⟩ : syracuseStep 2304257 = 1728193) B1728193
theorem B2304275 : Blo 1534464 2304275 := bstep (se 1 (by rfl) ⟨1728206, by rfl⟩ : syracuseStep 2304275 = 3456413) B3456413
theorem B3885347 : Blo 1534464 3885347 := bstep (se 1 (by rfl) ⟨2914010, by rfl⟩ : syracuseStep 3885347 = 5828021) B5828021
theorem B2304305 : Blo 1534464 2304305 := bstep (se 2 (by rfl) ⟨864114, by rfl⟩ : syracuseStep 2304305 = 1728229) B1728229
theorem B2591041 : Blo 1534464 2591041 := bstep (se 2 (by rfl) ⟨971640, by rfl⟩ : syracuseStep 2591041 = 1943281) B1943281
theorem B2304323 : Blo 1534464 2304323 := bstep (se 1 (by rfl) ⟨1728242, by rfl⟩ : syracuseStep 2304323 = 3456485) B3456485
theorem B2304353 : Blo 1534464 2304353 := bstep (se 2 (by rfl) ⟨864132, by rfl⟩ : syracuseStep 2304353 = 1728265) B1728265
theorem B2591075 : Blo 1534464 2591075 := bstep (se 1 (by rfl) ⟨1943306, by rfl⟩ : syracuseStep 2591075 = 3886613) B3886613
theorem B2460017 : Blo 1534464 2460017 := bstep (se 2 (by rfl) ⟨922506, by rfl⟩ : syracuseStep 2460017 = 1845013) B1845013
theorem B2304371 : Blo 1534464 2304371 := bstep (se 1 (by rfl) ⟨1728278, by rfl⟩ : syracuseStep 2304371 = 3456557) B3456557
theorem B1943939 : Blo 1534464 1943939 := bstep (se 1 (by rfl) ⟨1457954, by rfl⟩ : syracuseStep 1943939 = 2915909) B2915909
theorem B2304401 : Blo 1534464 2304401 := bstep (se 2 (by rfl) ⟨864150, by rfl⟩ : syracuseStep 2304401 = 1728301) B1728301
theorem B2304419 : Blo 1534464 2304419 := bstep (se 1 (by rfl) ⟨1728314, by rfl⟩ : syracuseStep 2304419 = 3456629) B3456629
theorem B2304449 : Blo 1534464 2304449 := bstep (se 2 (by rfl) ⟨864168, by rfl⟩ : syracuseStep 2304449 = 1728337) B1728337
theorem B2304467 : Blo 1534464 2304467 := bstep (se 1 (by rfl) ⟨1728350, by rfl⟩ : syracuseStep 2304467 = 3456701) B3456701
theorem B7768547 : Blo 1534464 7768547 := bstep (se 1 (by rfl) ⟨5826410, by rfl⟩ : syracuseStep 7768547 = 11652821) B11652821
theorem B2591203 : Blo 1534464 2591203 := bstep (se 1 (by rfl) ⟨1943402, by rfl⟩ : syracuseStep 2591203 = 3886805) B3886805
theorem B2460145 : Blo 1534464 2460145 := bstep (se 2 (by rfl) ⟨922554, by rfl⟩ : syracuseStep 2460145 = 1845109) B1845109
theorem B2304497 : Blo 1534464 2304497 := bstep (se 2 (by rfl) ⟨864186, by rfl⟩ : syracuseStep 2304497 = 1728373) B1728373
theorem B1534467 : Blo 1534464 1534467 := bstep (se 1 (by rfl) ⟨1150850, by rfl⟩ : syracuseStep 1534467 = 2301701) B2301701
theorem B2304515 : Blo 1534464 2304515 := bstep (se 1 (by rfl) ⟨1728386, by rfl⟩ : syracuseStep 2304515 = 3456773) B3456773
theorem B1534483 : Blo 1534464 1534483 := bstep (se 1 (by rfl) ⟨1150862, by rfl⟩ : syracuseStep 1534483 = 2301725) B2301725
theorem B2304545 : Blo 1534464 2304545 := bstep (se 2 (by rfl) ⟨864204, by rfl⟩ : syracuseStep 2304545 = 1728409) B1728409
theorem B1534499 : Blo 1534464 1534499 := bstep (se 1 (by rfl) ⟨1150874, by rfl⟩ : syracuseStep 1534499 = 2301749) B2301749
theorem B5179949 : Blo 1534464 5179949 := bstep (se 3 (by rfl) ⟨971240, by rfl⟩ : syracuseStep 5179949 = 1942481) B1942481
theorem B1534515 : Blo 1534464 1534515 := bstep (se 1 (by rfl) ⟨1150886, by rfl⟩ : syracuseStep 1534515 = 2301773) B2301773
theorem B2304563 : Blo 1534464 2304563 := bstep (se 1 (by rfl) ⟨1728422, by rfl⟩ : syracuseStep 2304563 = 3456845) B3456845
theorem B1534531 : Blo 1534464 1534531 := bstep (se 1 (by rfl) ⟨1150898, by rfl⟩ : syracuseStep 1534531 = 2301797) B2301797
theorem B2304593 : Blo 1534464 2304593 := bstep (se 2 (by rfl) ⟨864222, by rfl⟩ : syracuseStep 2304593 = 1728445) B1728445
theorem B1534547 : Blo 1534464 1534547 := bstep (se 1 (by rfl) ⟨1150910, by rfl⟩ : syracuseStep 1534547 = 2301821) B2301821
theorem B1534563 : Blo 1534464 1534563 := bstep (se 1 (by rfl) ⟨1150922, by rfl⟩ : syracuseStep 1534563 = 2301845) B2301845
theorem B5180003 : Blo 1534464 5180003 := bstep (se 1 (by rfl) ⟨3885002, by rfl⟩ : syracuseStep 5180003 = 7770005) B7770005
theorem B2304611 : Blo 1534464 2304611 := bstep (se 1 (by rfl) ⟨1728458, by rfl⟩ : syracuseStep 2304611 = 3456917) B3456917
theorem B2591345 : Blo 1534464 2591345 := bstep (se 2 (by rfl) ⟨971754, by rfl⟩ : syracuseStep 2591345 = 1943509) B1943509
theorem B1534579 : Blo 1534464 1534579 := bstep (se 1 (by rfl) ⟨1150934, by rfl⟩ : syracuseStep 1534579 = 2301869) B2301869
theorem B2304641 : Blo 1534464 2304641 := bstep (se 2 (by rfl) ⟨864240, by rfl⟩ : syracuseStep 2304641 = 1728481) B1728481
theorem B1534595 : Blo 1534464 1534595 := bstep (se 1 (by rfl) ⟨1150946, by rfl⟩ : syracuseStep 1534595 = 2301893) B2301893
theorem B1534611 : Blo 1534464 1534611 := bstep (se 1 (by rfl) ⟨1150958, by rfl⟩ : syracuseStep 1534611 = 2301917) B2301917
theorem B2304659 : Blo 1534464 2304659 := bstep (se 1 (by rfl) ⟨1728494, by rfl⟩ : syracuseStep 2304659 = 3456989) B3456989
theorem B1534627 : Blo 1534464 1534627 := bstep (se 1 (by rfl) ⟨1150970, by rfl⟩ : syracuseStep 1534627 = 2301941) B2301941
theorem B2304689 : Blo 1534464 2304689 := bstep (se 2 (by rfl) ⟨864258, by rfl⟩ : syracuseStep 2304689 = 1728517) B1728517
theorem B1534643 : Blo 1534464 1534643 := bstep (se 1 (by rfl) ⟨1150982, by rfl⟩ : syracuseStep 1534643 = 2301965) B2301965
theorem B2075315 : Blo 1534464 2075315 := bstep (se 1 (by rfl) ⟨1556486, by rfl⟩ : syracuseStep 2075315 = 3112973) B3112973
theorem B1534659 : Blo 1534464 1534659 := bstep (se 1 (by rfl) ⟨1150994, by rfl⟩ : syracuseStep 1534659 = 2301989) B2301989
theorem B1534675 : Blo 1534464 1534675 := bstep (se 1 (by rfl) ⟨1151006, by rfl⟩ : syracuseStep 1534675 = 2302013) B2302013
theorem B1534691 : Blo 1534464 1534691 := bstep (se 1 (by rfl) ⟨1151018, by rfl⟩ : syracuseStep 1534691 = 2302037) B2302037
theorem B11062001 : Blo 1534464 11062001 := bstep (se 2 (by rfl) ⟨4148250, by rfl⟩ : syracuseStep 11062001 = 8296501) B8296501
theorem B1534707 : Blo 1534464 1534707 := bstep (se 1 (by rfl) ⟨1151030, by rfl⟩ : syracuseStep 1534707 = 2302061) B2302061
theorem B5909233 : Blo 1534464 5909233 := bstep (se 2 (by rfl) ⟨2215962, by rfl⟩ : syracuseStep 5909233 = 4431925) B4431925
theorem B2591473 : Blo 1534464 2591473 := bstep (se 2 (by rfl) ⟨971802, by rfl⟩ : syracuseStep 2591473 = 1943605) B1943605
theorem B1534723 : Blo 1534464 1534723 := bstep (se 1 (by rfl) ⟨1151042, by rfl⟩ : syracuseStep 1534723 = 2302085) B2302085
theorem B3689219 : Blo 1534464 3689219 := bstep (se 1 (by rfl) ⟨2766914, by rfl⟩ : syracuseStep 3689219 = 5533829) B5533829
theorem B1534739 : Blo 1534464 1534739 := bstep (se 1 (by rfl) ⟨1151054, by rfl⟩ : syracuseStep 1534739 = 2302109) B2302109
theorem B2591507 : Blo 1534464 2591507 := bstep (se 1 (by rfl) ⟨1943630, by rfl⟩ : syracuseStep 2591507 = 3887261) B3887261
theorem B1534755 : Blo 1534464 1534755 := bstep (se 1 (by rfl) ⟨1151066, by rfl⟩ : syracuseStep 1534755 = 2302133) B2302133
theorem B1534771 : Blo 1534464 1534771 := bstep (se 1 (by rfl) ⟨1151078, by rfl⟩ : syracuseStep 1534771 = 2302157) B2302157
theorem B1534787 : Blo 1534464 1534787 := bstep (se 1 (by rfl) ⟨1151090, by rfl⟩ : syracuseStep 1534787 = 2302181) B2302181
theorem B1534803 : Blo 1534464 1534803 := bstep (se 1 (by rfl) ⟨1151102, by rfl⟩ : syracuseStep 1534803 = 2302205) B2302205
theorem B1534819 : Blo 1534464 1534819 := bstep (se 1 (by rfl) ⟨1151114, by rfl⟩ : syracuseStep 1534819 = 2302229) B2302229
theorem B5180273 : Blo 1534464 5180273 := bstep (se 2 (by rfl) ⟨1942602, by rfl⟩ : syracuseStep 5180273 = 3885205) B3885205
theorem B1534835 : Blo 1534464 1534835 := bstep (se 1 (by rfl) ⟨1151126, by rfl⟩ : syracuseStep 1534835 = 2302253) B2302253
theorem B1534851 : Blo 1534464 1534851 := bstep (se 1 (by rfl) ⟨1151138, by rfl⟩ : syracuseStep 1534851 = 2302277) B2302277
theorem B1534867 : Blo 1534464 1534867 := bstep (se 1 (by rfl) ⟨1151150, by rfl⟩ : syracuseStep 1534867 = 2302301) B2302301
theorem B2591635 : Blo 1534464 2591635 := bstep (se 1 (by rfl) ⟨1943726, by rfl⟩ : syracuseStep 2591635 = 3887453) B3887453
theorem B1534883 : Blo 1534464 1534883 := bstep (se 1 (by rfl) ⟨1151162, by rfl⟩ : syracuseStep 1534883 = 2302325) B2302325
theorem B1534899 : Blo 1534464 1534899 := bstep (se 1 (by rfl) ⟨1151174, by rfl⟩ : syracuseStep 1534899 = 2302349) B2302349
theorem B1534915 : Blo 1534464 1534915 := bstep (se 1 (by rfl) ⟨1151186, by rfl⟩ : syracuseStep 1534915 = 2302373) B2302373
theorem B1534931 : Blo 1534464 1534931 := bstep (se 1 (by rfl) ⟨1151198, by rfl⟩ : syracuseStep 1534931 = 2302397) B2302397
theorem B1534947 : Blo 1534464 1534947 := bstep (se 1 (by rfl) ⟨1151210, by rfl⟩ : syracuseStep 1534947 = 2302421) B2302421
theorem B1534963 : Blo 1534464 1534963 := bstep (se 1 (by rfl) ⟨1151222, by rfl⟩ : syracuseStep 1534963 = 2302445) B2302445
theorem B1534979 : Blo 1534464 1534979 := bstep (se 1 (by rfl) ⟨1151234, by rfl⟩ : syracuseStep 1534979 = 2302469) B2302469
theorem B1534995 : Blo 1534464 1534995 := bstep (se 1 (by rfl) ⟨1151246, by rfl⟩ : syracuseStep 1534995 = 2302493) B2302493
theorem B2591777 : Blo 1534464 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B1535011 : Blo 1534464 1535011 := bstep (se 1 (by rfl) ⟨1151258, by rfl⟩ : syracuseStep 1535011 = 2302517) B2302517
theorem B9333809 : Blo 1534464 9333809 := bstep (se 2 (by rfl) ⟨3500178, by rfl⟩ : syracuseStep 9333809 = 7000357) B7000357
theorem B1535027 : Blo 1534464 1535027 := bstep (se 1 (by rfl) ⟨1151270, by rfl⟩ : syracuseStep 1535027 = 2302541) B2302541
theorem B1535043 : Blo 1534464 1535043 := bstep (se 1 (by rfl) ⟨1151282, by rfl⟩ : syracuseStep 1535043 = 2302565) B2302565
theorem B1535059 : Blo 1534464 1535059 := bstep (se 1 (by rfl) ⟨1151294, by rfl⟩ : syracuseStep 1535059 = 2302589) B2302589
theorem B1535075 : Blo 1534464 1535075 := bstep (se 1 (by rfl) ⟨1151306, by rfl⟩ : syracuseStep 1535075 = 2302613) B2302613
theorem B23645297 : Blo 1534464 23645297 := bstep (se 2 (by rfl) ⟨8866986, by rfl⟩ : syracuseStep 23645297 = 17733973) B17733973
theorem B2460785 : Blo 1534464 2460785 := bstep (se 2 (by rfl) ⟨922794, by rfl⟩ : syracuseStep 2460785 = 1845589) B1845589
theorem B1535091 : Blo 1534464 1535091 := bstep (se 1 (by rfl) ⟨1151318, by rfl⟩ : syracuseStep 1535091 = 2302637) B2302637
theorem B1535107 : Blo 1534464 1535107 := bstep (se 1 (by rfl) ⟨1151330, by rfl⟩ : syracuseStep 1535107 = 2302661) B2302661
theorem B3689603 : Blo 1534464 3689603 := bstep (se 1 (by rfl) ⟨2767202, by rfl⟩ : syracuseStep 3689603 = 5534405) B5534405
theorem B1535123 : Blo 1534464 1535123 := bstep (se 1 (by rfl) ⟨1151342, by rfl⟩ : syracuseStep 1535123 = 2302685) B2302685
theorem B2591905 : Blo 1534464 2591905 := bstep (se 2 (by rfl) ⟨971964, by rfl⟩ : syracuseStep 2591905 = 1943929) B1943929
theorem B5827747 : Blo 1534464 5827747 := bstep (se 1 (by rfl) ⟨4370810, by rfl⟩ : syracuseStep 5827747 = 8741621) B8741621
theorem B1535139 : Blo 1534464 1535139 := bstep (se 1 (by rfl) ⟨1151354, by rfl⟩ : syracuseStep 1535139 = 2302709) B2302709
theorem B4918445 : Blo 1534464 4918445 := bstep (se 3 (by rfl) ⟨922208, by rfl⟩ : syracuseStep 4918445 = 1844417) B1844417
theorem B7777457 : Blo 1534464 7777457 := bstep (se 2 (by rfl) ⟨2916546, by rfl⟩ : syracuseStep 7777457 = 5833093) B5833093
theorem B1535155 : Blo 1534464 1535155 := bstep (se 1 (by rfl) ⟨1151366, by rfl⟩ : syracuseStep 1535155 = 2302733) B2302733
theorem B1535171 : Blo 1534464 1535171 := bstep (se 1 (by rfl) ⟨1151378, by rfl⟩ : syracuseStep 1535171 = 2302757) B2302757
theorem B2591939 : Blo 1534464 2591939 := bstep (se 1 (by rfl) ⟨1943954, by rfl⟩ : syracuseStep 2591939 = 3887909) B3887909
theorem B3886289 : Blo 1534464 3886289 := bstep (se 2 (by rfl) ⟨1457358, by rfl⟩ : syracuseStep 3886289 = 2914717) B2914717
theorem B1535187 : Blo 1534464 1535187 := bstep (se 1 (by rfl) ⟨1151390, by rfl⟩ : syracuseStep 1535187 = 2302781) B2302781
theorem B1535203 : Blo 1534464 1535203 := bstep (se 1 (by rfl) ⟨1151402, by rfl⟩ : syracuseStep 1535203 = 2302805) B2302805
theorem B1535219 : Blo 1534464 1535219 := bstep (se 1 (by rfl) ⟨1151414, by rfl⟩ : syracuseStep 1535219 = 2302829) B2302829
theorem B1535235 : Blo 1534464 1535235 := bstep (se 1 (by rfl) ⟨1151426, by rfl⟩ : syracuseStep 1535235 = 2302853) B2302853
theorem B3886339 : Blo 1534464 3886339 := bstep (se 1 (by rfl) ⟨2914754, by rfl⟩ : syracuseStep 3886339 = 5829509) B5829509
theorem B7769357 : Blo 1534464 7769357 := bstep (se 3 (by rfl) ⟨1456754, by rfl⟩ : syracuseStep 7769357 = 2913509) B2913509
theorem B1535251 : Blo 1534464 1535251 := bstep (se 1 (by rfl) ⟨1151438, by rfl⟩ : syracuseStep 1535251 = 2302877) B2302877
theorem B1535267 : Blo 1534464 1535267 := bstep (se 1 (by rfl) ⟨1151450, by rfl⟩ : syracuseStep 1535267 = 2302901) B2302901
theorem B1535283 : Blo 1534464 1535283 := bstep (se 1 (by rfl) ⟨1151462, by rfl⟩ : syracuseStep 1535283 = 2302925) B2302925
theorem B1535299 : Blo 1534464 1535299 := bstep (se 1 (by rfl) ⟨1151474, by rfl⟩ : syracuseStep 1535299 = 2302949) B2302949
theorem B2592067 : Blo 1534464 2592067 := bstep (se 1 (by rfl) ⟨1944050, by rfl⟩ : syracuseStep 2592067 = 3888101) B3888101
theorem B1535315 : Blo 1534464 1535315 := bstep (se 1 (by rfl) ⟨1151486, by rfl⟩ : syracuseStep 1535315 = 2302973) B2302973
theorem B4369763 : Blo 1534464 4369763 := bstep (se 1 (by rfl) ⟨3277322, by rfl⟩ : syracuseStep 4369763 = 6554645) B6554645
theorem B1535331 : Blo 1534464 1535331 := bstep (se 1 (by rfl) ⟨1151498, by rfl⟩ : syracuseStep 1535331 = 2302997) B2302997
theorem B1535347 : Blo 1534464 1535347 := bstep (se 1 (by rfl) ⟨1151510, by rfl⟩ : syracuseStep 1535347 = 2303021) B2303021
theorem B1535363 : Blo 1534464 1535363 := bstep (se 1 (by rfl) ⟨1151522, by rfl⟩ : syracuseStep 1535363 = 2303045) B2303045
theorem B4148621 : Blo 1534464 4148621 := bstep (se 3 (by rfl) ⟨777866, by rfl⟩ : syracuseStep 4148621 = 1555733) B1555733
theorem B5180813 : Blo 1534464 5180813 := bstep (se 3 (by rfl) ⟨971402, by rfl⟩ : syracuseStep 5180813 = 1942805) B1942805
theorem B3886481 : Blo 1534464 3886481 := bstep (se 2 (by rfl) ⟨1457430, by rfl⟩ : syracuseStep 3886481 = 2914861) B2914861
theorem B1535379 : Blo 1534464 1535379 := bstep (se 1 (by rfl) ⟨1151534, by rfl⟩ : syracuseStep 1535379 = 2303069) B2303069
theorem B1535395 : Blo 1534464 1535395 := bstep (se 1 (by rfl) ⟨1151546, by rfl⟩ : syracuseStep 1535395 = 2303093) B2303093
theorem B3689891 : Blo 1534464 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B2076067 : Blo 1534464 2076067 := bstep (se 1 (by rfl) ⟨1557050, by rfl⟩ : syracuseStep 2076067 = 3114101) B3114101
theorem B6557105 : Blo 1534464 6557105 := bstep (se 2 (by rfl) ⟨2458914, by rfl⟩ : syracuseStep 6557105 = 4917829) B4917829
theorem B1535411 : Blo 1534464 1535411 := bstep (se 1 (by rfl) ⟨1151558, by rfl⟩ : syracuseStep 1535411 = 2303117) B2303117
theorem B16592309 : Blo 1534464 16592309 := bstep (se 5 (by rfl) ⟨777764, by rfl⟩ : syracuseStep 16592309 = 1555529) B1555529
theorem B5180867 : Blo 1534464 5180867 := bstep (se 1 (by rfl) ⟨3885650, by rfl⟩ : syracuseStep 5180867 = 7771301) B7771301
theorem B1535427 : Blo 1534464 1535427 := bstep (se 1 (by rfl) ⟨1151570, by rfl⟩ : syracuseStep 1535427 = 2303141) B2303141
theorem B22130117 : Blo 1534464 22130117 := bstep (se 4 (by rfl) ⟨2074698, by rfl⟩ : syracuseStep 22130117 = 4149397) B4149397
theorem B24915397 : Blo 1534464 24915397 := bstep (se 4 (by rfl) ⟨2335818, by rfl⟩ : syracuseStep 24915397 = 4671637) B4671637
theorem B1535443 : Blo 1534464 1535443 := bstep (se 1 (by rfl) ⟨1151582, by rfl⟩ : syracuseStep 1535443 = 2303165) B2303165
theorem B2592209 : Blo 1534464 2592209 := bstep (se 2 (by rfl) ⟨972078, by rfl⟩ : syracuseStep 2592209 = 1944157) B1944157
theorem B1535459 : Blo 1534464 1535459 := bstep (se 1 (by rfl) ⟨1151594, by rfl⟩ : syracuseStep 1535459 = 2303189) B2303189
theorem B1535475 : Blo 1534464 1535475 := bstep (se 1 (by rfl) ⟨1151606, by rfl⟩ : syracuseStep 1535475 = 2303213) B2303213
theorem B1535491 : Blo 1534464 1535491 := bstep (se 1 (by rfl) ⟨1151618, by rfl⟩ : syracuseStep 1535491 = 2303237) B2303237
theorem B1535507 : Blo 1534464 1535507 := bstep (se 1 (by rfl) ⟨1151630, by rfl⟩ : syracuseStep 1535507 = 2303261) B2303261
theorem B1535523 : Blo 1534464 1535523 := bstep (se 1 (by rfl) ⟨1151642, by rfl⟩ : syracuseStep 1535523 = 2303285) B2303285
theorem B1535539 : Blo 1534464 1535539 := bstep (se 1 (by rfl) ⟨1151654, by rfl⟩ : syracuseStep 1535539 = 2303309) B2303309
theorem B1535555 : Blo 1534464 1535555 := bstep (se 1 (by rfl) ⟨1151666, by rfl⟩ : syracuseStep 1535555 = 2303333) B2303333
theorem B2592337 : Blo 1534464 2592337 := bstep (se 2 (by rfl) ⟨972126, by rfl⟩ : syracuseStep 2592337 = 1944253) B1944253
theorem B1535571 : Blo 1534464 1535571 := bstep (se 1 (by rfl) ⟨1151678, by rfl⟩ : syracuseStep 1535571 = 2303357) B2303357
theorem B1535587 : Blo 1534464 1535587 := bstep (se 1 (by rfl) ⟨1151690, by rfl⟩ : syracuseStep 1535587 = 2303381) B2303381
theorem B1535603 : Blo 1534464 1535603 := bstep (se 1 (by rfl) ⟨1151702, by rfl⟩ : syracuseStep 1535603 = 2303405) B2303405
theorem B2592371 : Blo 1534464 2592371 := bstep (se 1 (by rfl) ⟨1944278, by rfl⟩ : syracuseStep 2592371 = 3888557) B3888557
theorem B1535619 : Blo 1534464 1535619 := bstep (se 1 (by rfl) ⟨1151714, by rfl⟩ : syracuseStep 1535619 = 2303429) B2303429
theorem B11062925 : Blo 1534464 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B3452561 : Blo 1534464 3452561 := bstep (se 2 (by rfl) ⟨1294710, by rfl⟩ : syracuseStep 3452561 = 2589421) B2589421
theorem B1535635 : Blo 1534464 1535635 := bstep (se 1 (by rfl) ⟨1151726, by rfl⟩ : syracuseStep 1535635 = 2303453) B2303453
theorem B3452579 : Blo 1534464 3452579 := bstep (se 1 (by rfl) ⟨2589434, by rfl⟩ : syracuseStep 3452579 = 5178869) B5178869
theorem B1535651 : Blo 1534464 1535651 := bstep (se 1 (by rfl) ⟨1151738, by rfl⟩ : syracuseStep 1535651 = 2303477) B2303477
theorem B1535667 : Blo 1534464 1535667 := bstep (se 1 (by rfl) ⟨1151750, by rfl⟩ : syracuseStep 1535667 = 2303501) B2303501
theorem B1535683 : Blo 1534464 1535683 := bstep (se 1 (by rfl) ⟨1151762, by rfl⟩ : syracuseStep 1535683 = 2303525) B2303525
theorem B5181137 : Blo 1534464 5181137 := bstep (se 2 (by rfl) ⟨1942926, by rfl⟩ : syracuseStep 5181137 = 3885853) B3885853
theorem B1535699 : Blo 1534464 1535699 := bstep (se 1 (by rfl) ⟨1151774, by rfl⟩ : syracuseStep 1535699 = 2303549) B2303549
theorem B1535715 : Blo 1534464 1535715 := bstep (se 1 (by rfl) ⟨1151786, by rfl⟩ : syracuseStep 1535715 = 2303573) B2303573
theorem B1535731 : Blo 1534464 1535731 := bstep (se 1 (by rfl) ⟨1151798, by rfl⟩ : syracuseStep 1535731 = 2303597) B2303597
theorem B2592499 : Blo 1534464 2592499 := bstep (se 1 (by rfl) ⟨1944374, by rfl⟩ : syracuseStep 2592499 = 3888749) B3888749
theorem B1535747 : Blo 1534464 1535747 := bstep (se 1 (by rfl) ⟨1151810, by rfl⟩ : syracuseStep 1535747 = 2303621) B2303621
theorem B1535763 : Blo 1534464 1535763 := bstep (se 1 (by rfl) ⟨1151822, by rfl⟩ : syracuseStep 1535763 = 2303645) B2303645
theorem B1535779 : Blo 1534464 1535779 := bstep (se 1 (by rfl) ⟨1151834, by rfl⟩ : syracuseStep 1535779 = 2303669) B2303669
theorem B1535795 : Blo 1534464 1535795 := bstep (se 1 (by rfl) ⟨1151846, by rfl⟩ : syracuseStep 1535795 = 2303693) B2303693
theorem B1535811 : Blo 1534464 1535811 := bstep (se 1 (by rfl) ⟨1151858, by rfl⟩ : syracuseStep 1535811 = 2303717) B2303717
theorem B4149073 : Blo 1534464 4149073 := bstep (se 2 (by rfl) ⟨1555902, by rfl⟩ : syracuseStep 4149073 = 3111805) B3111805
theorem B1535827 : Blo 1534464 1535827 := bstep (se 1 (by rfl) ⟨1151870, by rfl⟩ : syracuseStep 1535827 = 2303741) B2303741
theorem B1535843 : Blo 1534464 1535843 := bstep (se 1 (by rfl) ⟨1151882, by rfl⟩ : syracuseStep 1535843 = 2303765) B2303765
theorem B3690353 : Blo 1534464 3690353 := bstep (se 2 (by rfl) ⟨1383882, by rfl⟩ : syracuseStep 3690353 = 2767765) B2767765
theorem B1535859 : Blo 1534464 1535859 := bstep (se 1 (by rfl) ⟨1151894, by rfl⟩ : syracuseStep 1535859 = 2303789) B2303789
theorem B2592641 : Blo 1534464 2592641 := bstep (se 2 (by rfl) ⟨972240, by rfl⟩ : syracuseStep 2592641 = 1944481) B1944481
theorem B1535875 : Blo 1534464 1535875 := bstep (se 1 (by rfl) ⟨1151906, by rfl⟩ : syracuseStep 1535875 = 2303813) B2303813
theorem B1535891 : Blo 1534464 1535891 := bstep (se 1 (by rfl) ⟨1151918, by rfl⟩ : syracuseStep 1535891 = 2303837) B2303837
theorem B1535907 : Blo 1534464 1535907 := bstep (se 1 (by rfl) ⟨1151930, by rfl⟩ : syracuseStep 1535907 = 2303861) B2303861
theorem B4919213 : Blo 1534464 4919213 := bstep (se 3 (by rfl) ⟨922352, by rfl⟩ : syracuseStep 4919213 = 1844705) B1844705
theorem B3452849 : Blo 1534464 3452849 := bstep (se 2 (by rfl) ⟨1294818, by rfl⟩ : syracuseStep 3452849 = 2589637) B2589637
theorem B1535923 : Blo 1534464 1535923 := bstep (se 1 (by rfl) ⟨1151942, by rfl⟩ : syracuseStep 1535923 = 2303885) B2303885
theorem B3452867 : Blo 1534464 3452867 := bstep (se 1 (by rfl) ⟨2589650, by rfl⟩ : syracuseStep 3452867 = 5179301) B5179301
theorem B1535939 : Blo 1534464 1535939 := bstep (se 1 (by rfl) ⟨1151954, by rfl⟩ : syracuseStep 1535939 = 2303909) B2303909
theorem B1535955 : Blo 1534464 1535955 := bstep (se 1 (by rfl) ⟨1151966, by rfl⟩ : syracuseStep 1535955 = 2303933) B2303933
theorem B1535971 : Blo 1534464 1535971 := bstep (se 1 (by rfl) ⟨1151978, by rfl⟩ : syracuseStep 1535971 = 2303957) B2303957
theorem B1535987 : Blo 1534464 1535987 := bstep (se 1 (by rfl) ⟨1151990, by rfl⟩ : syracuseStep 1535987 = 2303981) B2303981
theorem B2592769 : Blo 1534464 2592769 := bstep (se 2 (by rfl) ⟨972288, by rfl⟩ : syracuseStep 2592769 = 1944577) B1944577
theorem B1536003 : Blo 1534464 1536003 := bstep (se 1 (by rfl) ⟨1152002, by rfl⟩ : syracuseStep 1536003 = 2304005) B2304005
theorem B1536019 : Blo 1534464 1536019 := bstep (se 1 (by rfl) ⟨1152014, by rfl⟩ : syracuseStep 1536019 = 2304029) B2304029
theorem B1536035 : Blo 1534464 1536035 := bstep (se 1 (by rfl) ⟨1152026, by rfl⟩ : syracuseStep 1536035 = 2304053) B2304053
theorem B3280945 : Blo 1534464 3280945 := bstep (se 2 (by rfl) ⟨1230354, by rfl⟩ : syracuseStep 3280945 = 2460709) B2460709
theorem B1536051 : Blo 1534464 1536051 := bstep (se 1 (by rfl) ⟨1152038, by rfl⟩ : syracuseStep 1536051 = 2304077) B2304077
theorem B1536067 : Blo 1534464 1536067 := bstep (se 1 (by rfl) ⟨1152050, by rfl⟩ : syracuseStep 1536067 = 2304101) B2304101
theorem B1536083 : Blo 1534464 1536083 := bstep (se 1 (by rfl) ⟨1152062, by rfl⟩ : syracuseStep 1536083 = 2304125) B2304125
theorem B1536099 : Blo 1534464 1536099 := bstep (se 1 (by rfl) ⟨1152074, by rfl⟩ : syracuseStep 1536099 = 2304149) B2304149
theorem B1536115 : Blo 1534464 1536115 := bstep (se 1 (by rfl) ⟨1152086, by rfl⟩ : syracuseStep 1536115 = 2304173) B2304173
theorem B1536131 : Blo 1534464 1536131 := bstep (se 1 (by rfl) ⟨1152098, by rfl⟩ : syracuseStep 1536131 = 2304197) B2304197
theorem B1536147 : Blo 1534464 1536147 := bstep (se 1 (by rfl) ⟨1152110, by rfl⟩ : syracuseStep 1536147 = 2304221) B2304221
theorem B3371153 : Blo 1534464 3371153 := bstep (se 2 (by rfl) ⟨1264182, by rfl⟩ : syracuseStep 3371153 = 2528365) B2528365
theorem B1536163 : Blo 1534464 1536163 := bstep (se 1 (by rfl) ⟨1152122, by rfl⟩ : syracuseStep 1536163 = 2304245) B2304245
theorem B1536179 : Blo 1534464 1536179 := bstep (se 1 (by rfl) ⟨1152134, by rfl⟩ : syracuseStep 1536179 = 2304269) B2304269
theorem B1536195 : Blo 1534464 1536195 := bstep (se 1 (by rfl) ⟨1152146, by rfl⟩ : syracuseStep 1536195 = 2304293) B2304293
theorem B3453137 : Blo 1534464 3453137 := bstep (se 2 (by rfl) ⟨1294926, by rfl⟩ : syracuseStep 3453137 = 2589853) B2589853
theorem B1536211 : Blo 1534464 1536211 := bstep (se 1 (by rfl) ⟨1152158, by rfl⟩ : syracuseStep 1536211 = 2304317) B2304317
theorem B3453155 : Blo 1534464 3453155 := bstep (se 1 (by rfl) ⟨2589866, by rfl⟩ : syracuseStep 3453155 = 5179733) B5179733
theorem B1536227 : Blo 1534464 1536227 := bstep (se 1 (by rfl) ⟨1152170, by rfl⟩ : syracuseStep 1536227 = 2304341) B2304341
theorem B5181677 : Blo 1534464 5181677 := bstep (se 3 (by rfl) ⟨971564, by rfl⟩ : syracuseStep 5181677 = 1943129) B1943129
theorem B1536243 : Blo 1534464 1536243 := bstep (se 1 (by rfl) ⟨1152182, by rfl⟩ : syracuseStep 1536243 = 2304365) B2304365
theorem B1536259 : Blo 1534464 1536259 := bstep (se 1 (by rfl) ⟨1152194, by rfl⟩ : syracuseStep 1536259 = 2304389) B2304389
theorem B1536275 : Blo 1534464 1536275 := bstep (se 1 (by rfl) ⟨1152206, by rfl⟩ : syracuseStep 1536275 = 2304413) B2304413
theorem B4149539 : Blo 1534464 4149539 := bstep (se 1 (by rfl) ⟨3112154, by rfl⟩ : syracuseStep 4149539 = 6224309) B6224309
theorem B5181731 : Blo 1534464 5181731 := bstep (se 1 (by rfl) ⟨3886298, by rfl⟩ : syracuseStep 5181731 = 7772597) B7772597
theorem B1536291 : Blo 1534464 1536291 := bstep (se 1 (by rfl) ⟨1152218, by rfl⟩ : syracuseStep 1536291 = 2304437) B2304437
theorem B1536307 : Blo 1534464 1536307 := bstep (se 1 (by rfl) ⟨1152230, by rfl⟩ : syracuseStep 1536307 = 2304461) B2304461
theorem B4149571 : Blo 1534464 4149571 := bstep (se 1 (by rfl) ⟨3112178, by rfl⟩ : syracuseStep 4149571 = 6224357) B6224357
theorem B1536323 : Blo 1534464 1536323 := bstep (se 1 (by rfl) ⟨1152242, by rfl⟩ : syracuseStep 1536323 = 2304485) B2304485
theorem B6558029 : Blo 1534464 6558029 := bstep (se 3 (by rfl) ⟨1229630, by rfl⟩ : syracuseStep 6558029 = 2459261) B2459261
theorem B1536339 : Blo 1534464 1536339 := bstep (se 1 (by rfl) ⟨1152254, by rfl⟩ : syracuseStep 1536339 = 2304509) B2304509
theorem B1536355 : Blo 1534464 1536355 := bstep (se 1 (by rfl) ⟨1152266, by rfl⟩ : syracuseStep 1536355 = 2304533) B2304533
theorem B3887473 : Blo 1534464 3887473 := bstep (se 2 (by rfl) ⟨1457802, by rfl⟩ : syracuseStep 3887473 = 2915605) B2915605
theorem B1536371 : Blo 1534464 1536371 := bstep (se 1 (by rfl) ⟨1152278, by rfl⟩ : syracuseStep 1536371 = 2304557) B2304557
theorem B1536387 : Blo 1534464 1536387 := bstep (se 1 (by rfl) ⟨1152290, by rfl⟩ : syracuseStep 1536387 = 2304581) B2304581
theorem B1536403 : Blo 1534464 1536403 := bstep (se 1 (by rfl) ⟨1152302, by rfl⟩ : syracuseStep 1536403 = 2304605) B2304605
theorem B1536419 : Blo 1534464 1536419 := bstep (se 1 (by rfl) ⟨1152314, by rfl⟩ : syracuseStep 1536419 = 2304629) B2304629
theorem B4919725 : Blo 1534464 4919725 := bstep (se 3 (by rfl) ⟨922448, by rfl⟩ : syracuseStep 4919725 = 1844897) B1844897
theorem B1536435 : Blo 1534464 1536435 := bstep (se 1 (by rfl) ⟨1152326, by rfl⟩ : syracuseStep 1536435 = 2304653) B2304653
theorem B1536451 : Blo 1534464 1536451 := bstep (se 1 (by rfl) ⟨1152338, by rfl⟩ : syracuseStep 1536451 = 2304677) B2304677
theorem B3453425 : Blo 1534464 3453425 := bstep (se 2 (by rfl) ⟨1295034, by rfl⟩ : syracuseStep 3453425 = 2590069) B2590069
theorem B3453443 : Blo 1534464 3453443 := bstep (se 1 (by rfl) ⟨2590082, by rfl⟩ : syracuseStep 3453443 = 5180165) B5180165
theorem B14750221 : Blo 1534464 14750221 := bstep (se 3 (by rfl) ⟨2765666, by rfl⟩ : syracuseStep 14750221 = 5531333) B5531333
theorem B17494541 : Blo 1534464 17494541 := bstep (se 3 (by rfl) ⟨3280226, by rfl⟩ : syracuseStep 17494541 = 6560453) B6560453
theorem B3691025 : Blo 1534464 3691025 := bstep (se 2 (by rfl) ⟨1384134, by rfl⟩ : syracuseStep 3691025 = 2768269) B2768269
theorem B4370993 : Blo 1534464 4370993 := bstep (se 2 (by rfl) ⟨1639122, by rfl⟩ : syracuseStep 4370993 = 3278245) B3278245
theorem B5182001 : Blo 1534464 5182001 := bstep (se 2 (by rfl) ⟨1943250, by rfl⟩ : syracuseStep 5182001 = 3886501) B3886501
theorem B9835121 : Blo 1534464 9835121 := bstep (se 2 (by rfl) ⟨3688170, by rfl⟩ : syracuseStep 9835121 = 7376341) B7376341
theorem B2765443 : Blo 1534464 2765443 := bstep (se 1 (by rfl) ⟨2074082, by rfl⟩ : syracuseStep 2765443 = 4148165) B4148165
theorem B3887747 : Blo 1534464 3887747 := bstep (se 1 (by rfl) ⟨2915810, by rfl⟩ : syracuseStep 3887747 = 5831621) B5831621
theorem B7377571 : Blo 1534464 7377571 := bstep (se 1 (by rfl) ⟨5533178, by rfl⟩ : syracuseStep 7377571 = 11066357) B11066357
theorem B8745677 : Blo 1534464 8745677 := bstep (se 3 (by rfl) ⟨1639814, by rfl⟩ : syracuseStep 8745677 = 3279629) B3279629
theorem B3453713 : Blo 1534464 3453713 := bstep (se 2 (by rfl) ⟨1295142, by rfl⟩ : syracuseStep 3453713 = 2590285) B2590285
theorem B3453731 : Blo 1534464 3453731 := bstep (se 1 (by rfl) ⟨2590298, by rfl⟩ : syracuseStep 3453731 = 5180597) B5180597
theorem B8885027 : Blo 1534464 8885027 := bstep (se 1 (by rfl) ⟨6663770, by rfl⟩ : syracuseStep 8885027 = 13327541) B13327541
theorem B3887939 : Blo 1534464 3887939 := bstep (se 1 (by rfl) ⟨2915954, by rfl⟩ : syracuseStep 3887939 = 5831909) B5831909
theorem B5534563 : Blo 1534464 5534563 := bstep (se 1 (by rfl) ⟨4150922, by rfl⟩ : syracuseStep 5534563 = 8301845) B8301845
theorem B4920227 : Blo 1534464 4920227 := bstep (se 1 (by rfl) ⟨3690170, by rfl⟩ : syracuseStep 4920227 = 7380341) B7380341
theorem B11072497 : Blo 1534464 11072497 := bstep (se 2 (by rfl) ⟨4152186, by rfl⟩ : syracuseStep 11072497 = 8304373) B8304373
theorem B3454001 : Blo 1534464 3454001 := bstep (se 2 (by rfl) ⟨1295250, by rfl⟩ : syracuseStep 3454001 = 2590501) B2590501
theorem B3454019 : Blo 1534464 3454019 := bstep (se 1 (by rfl) ⟨2590514, by rfl⟩ : syracuseStep 3454019 = 5181029) B5181029
theorem B5182541 : Blo 1534464 5182541 := bstep (se 3 (by rfl) ⟨971726, by rfl⟩ : syracuseStep 5182541 = 1943453) B1943453
theorem B1750099 : Blo 1534464 1750099 := bstep (se 1 (by rfl) ⟨1312574, by rfl⟩ : syracuseStep 1750099 = 2625149) B2625149
theorem B4666481 : Blo 1534464 4666481 := bstep (se 2 (by rfl) ⟨1749930, by rfl⟩ : syracuseStep 4666481 = 3499861) B3499861
theorem B5182595 : Blo 1534464 5182595 := bstep (se 1 (by rfl) ⟨3886946, by rfl⟩ : syracuseStep 5182595 = 7773893) B7773893
theorem B4150499 : Blo 1534464 4150499 := bstep (se 1 (by rfl) ⟨3112874, by rfl⟩ : syracuseStep 4150499 = 6225749) B6225749
theorem B4150577 : Blo 1534464 4150577 := bstep (se 2 (by rfl) ⟨1556466, by rfl⟩ : syracuseStep 4150577 = 3112933) B3112933
theorem B8303921 : Blo 1534464 8303921 := bstep (se 2 (by rfl) ⟨3113970, by rfl⟩ : syracuseStep 8303921 = 6227941) B6227941
theorem B5829965 : Blo 1534464 5829965 := bstep (se 3 (by rfl) ⟨1093118, by rfl⟩ : syracuseStep 5829965 = 2186237) B2186237
theorem B3454289 : Blo 1534464 3454289 := bstep (se 2 (by rfl) ⟨1295358, by rfl⟩ : syracuseStep 3454289 = 2590717) B2590717
theorem B3454307 : Blo 1534464 3454307 := bstep (se 1 (by rfl) ⟨2590730, by rfl⟩ : syracuseStep 3454307 = 5181461) B5181461
theorem B5182865 : Blo 1534464 5182865 := bstep (se 2 (by rfl) ⟨1943574, by rfl⟩ : syracuseStep 5182865 = 3887149) B3887149
theorem B3503537 : Blo 1534464 3503537 := bstep (se 2 (by rfl) ⟨1313826, by rfl⟩ : syracuseStep 3503537 = 2627653) B2627653
theorem B2913745 : Blo 1534464 2913745 := bstep (se 2 (by rfl) ⟨1092654, by rfl⟩ : syracuseStep 2913745 = 2185309) B2185309
theorem B3503665 : Blo 1534464 3503665 := bstep (se 2 (by rfl) ⟨1313874, by rfl⟩ : syracuseStep 3503665 = 2627749) B2627749
theorem B3454577 : Blo 1534464 3454577 := bstep (se 2 (by rfl) ⟨1295466, by rfl⟩ : syracuseStep 3454577 = 2590933) B2590933
theorem B2627201 : Blo 1534464 2627201 := bstep (se 2 (by rfl) ⟨985200, by rfl⟩ : syracuseStep 2627201 = 1970401) B1970401
theorem B3454595 : Blo 1534464 3454595 := bstep (se 1 (by rfl) ⟨2590946, by rfl⟩ : syracuseStep 3454595 = 5181893) B5181893
theorem B3888881 : Blo 1534464 3888881 := bstep (se 2 (by rfl) ⟨1458330, by rfl⟩ : syracuseStep 3888881 = 2916661) B2916661
theorem B3888931 : Blo 1534464 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B2914147 : Blo 1534464 2914147 := bstep (se 1 (by rfl) ⟨2185610, by rfl⟩ : syracuseStep 2914147 = 4371221) B4371221
theorem B1726339 : Blo 1534464 1726339 := bstep (se 1 (by rfl) ⟨1294754, by rfl⟩ : syracuseStep 1726339 = 2589509) B2589509
theorem B2914193 : Blo 1534464 2914193 := bstep (se 2 (by rfl) ⟨1092822, by rfl⟩ : syracuseStep 2914193 = 2185645) B2185645
theorem B3454865 : Blo 1534464 3454865 := bstep (se 2 (by rfl) ⟨1295574, by rfl⟩ : syracuseStep 3454865 = 2591149) B2591149
theorem B3454883 : Blo 1534464 3454883 := bstep (se 1 (by rfl) ⟨2591162, by rfl⟩ : syracuseStep 3454883 = 5182325) B5182325
theorem B5183405 : Blo 1534464 5183405 := bstep (se 3 (by rfl) ⟨971888, by rfl⟩ : syracuseStep 5183405 = 1943777) B1943777
theorem B3889073 : Blo 1534464 3889073 := bstep (se 2 (by rfl) ⟨1458402, by rfl⟩ : syracuseStep 3889073 = 2916805) B2916805
theorem B4372451 : Blo 1534464 4372451 := bstep (se 1 (by rfl) ⟨3279338, by rfl⟩ : syracuseStep 4372451 = 6558677) B6558677
theorem B5183459 : Blo 1534464 5183459 := bstep (se 1 (by rfl) ⟨3887594, by rfl⟩ : syracuseStep 5183459 = 7775189) B7775189
theorem B1726483 : Blo 1534464 1726483 := bstep (se 1 (by rfl) ⟨1294862, by rfl⟩ : syracuseStep 1726483 = 2589725) B2589725
theorem B9836579 : Blo 1534464 9836579 := bstep (se 1 (by rfl) ⟨7377434, by rfl⟩ : syracuseStep 9836579 = 14754869) B14754869
theorem B7772273 : Blo 1534464 7772273 := bstep (se 2 (by rfl) ⟨2914602, by rfl⟩ : syracuseStep 7772273 = 5829205) B5829205
theorem B1726627 : Blo 1534464 1726627 := bstep (se 1 (by rfl) ⟨1294970, by rfl⟩ : syracuseStep 1726627 = 2589941) B2589941
theorem B2914481 : Blo 1534464 2914481 := bstep (se 2 (by rfl) ⟨1092930, by rfl⟩ : syracuseStep 2914481 = 2185861) B2185861
theorem B3455153 : Blo 1534464 3455153 := bstep (se 2 (by rfl) ⟨1295682, by rfl⟩ : syracuseStep 3455153 = 2591365) B2591365
theorem B3455171 : Blo 1534464 3455171 := bstep (se 1 (by rfl) ⟨2591378, by rfl⟩ : syracuseStep 3455171 = 5182757) B5182757
theorem B5183729 : Blo 1534464 5183729 := bstep (se 2 (by rfl) ⟨1943898, by rfl⟩ : syracuseStep 5183729 = 3887797) B3887797
theorem B1726771 : Blo 1534464 1726771 := bstep (se 1 (by rfl) ⟨1295078, by rfl⟩ : syracuseStep 1726771 = 2590157) B2590157
theorem B2185537 : Blo 1534464 2185537 := bstep (se 2 (by rfl) ⟨819576, by rfl⟩ : syracuseStep 2185537 = 1639153) B1639153
theorem B2185633 : Blo 1534464 2185633 := bstep (se 2 (by rfl) ⟨819612, by rfl⟩ : syracuseStep 2185633 = 1639225) B1639225
theorem B1726915 : Blo 1534464 1726915 := bstep (se 1 (by rfl) ⟨1295186, by rfl⟩ : syracuseStep 1726915 = 2590373) B2590373
theorem B4430285 : Blo 1534464 4430285 := bstep (se 3 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 4430285 = 1661357) B1661357
theorem B3455441 : Blo 1534464 3455441 := bstep (se 2 (by rfl) ⟨1295790, by rfl⟩ : syracuseStep 3455441 = 2591581) B2591581
theorem B19675619 : Blo 1534464 19675619 := bstep (se 1 (by rfl) ⟨14756714, by rfl⟩ : syracuseStep 19675619 = 29513429) B29513429
theorem B4733411 : Blo 1534464 4733411 := bstep (se 1 (by rfl) ⟨3550058, by rfl⟩ : syracuseStep 4733411 = 7100117) B7100117
theorem B3455459 : Blo 1534464 3455459 := bstep (se 1 (by rfl) ⟨2591594, by rfl⟩ : syracuseStep 3455459 = 5183189) B5183189
theorem B1727059 : Blo 1534464 1727059 := bstep (se 1 (by rfl) ⟨1295294, by rfl⟩ : syracuseStep 1727059 = 2590589) B2590589
theorem B9337457 : Blo 1534464 9337457 := bstep (se 2 (by rfl) ⟨3501546, by rfl⟩ : syracuseStep 9337457 = 7003093) B7003093
theorem B2103953 : Blo 1534464 2103953 := bstep (se 2 (by rfl) ⟨788982, by rfl⟩ : syracuseStep 2103953 = 1577965) B1577965
theorem B5323427 : Blo 1534464 5323427 := bstep (se 1 (by rfl) ⟨3992570, by rfl⟩ : syracuseStep 5323427 = 7985141) B7985141
theorem B1727203 : Blo 1534464 1727203 := bstep (se 1 (by rfl) ⟨1295402, by rfl⟩ : syracuseStep 1727203 = 2590805) B2590805
theorem B4922083 : Blo 1534464 4922083 := bstep (se 1 (by rfl) ⟨3691562, by rfl⟩ : syracuseStep 4922083 = 7383125) B7383125
theorem B3455729 : Blo 1534464 3455729 := bstep (se 2 (by rfl) ⟨1295898, by rfl⟩ : syracuseStep 3455729 = 2591797) B2591797
theorem B3455747 : Blo 1534464 3455747 := bstep (se 1 (by rfl) ⟨2591810, by rfl⟩ : syracuseStep 3455747 = 5183621) B5183621
theorem B4373261 : Blo 1534464 4373261 := bstep (se 3 (by rfl) ⟨819986, by rfl⟩ : syracuseStep 4373261 = 1639973) B1639973
theorem B5184269 : Blo 1534464 5184269 := bstep (se 3 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 5184269 = 1944101) B1944101
theorem B5184323 : Blo 1534464 5184323 := bstep (se 1 (by rfl) ⟨3888242, by rfl⟩ : syracuseStep 5184323 = 7776485) B7776485
theorem B17488709 : Blo 1534464 17488709 := bstep (se 4 (by rfl) ⟨1639566, by rfl⟩ : syracuseStep 17488709 = 3279133) B3279133
theorem B4799345 : Blo 1534464 4799345 := bstep (se 2 (by rfl) ⟨1799754, by rfl⟩ : syracuseStep 4799345 = 3599509) B3599509
theorem B1727347 : Blo 1534464 1727347 := bstep (se 1 (by rfl) ⟨1295510, by rfl⟩ : syracuseStep 1727347 = 2591021) B2591021
theorem B2915203 : Blo 1534464 2915203 := bstep (se 1 (by rfl) ⟨2186402, by rfl⟩ : syracuseStep 2915203 = 4372805) B4372805
theorem B8747909 : Blo 1534464 8747909 := bstep (se 4 (by rfl) ⟨820116, by rfl⟩ : syracuseStep 8747909 = 1640233) B1640233
theorem B75709325 : Blo 1534464 75709325 := bstep (se 3 (by rfl) ⟨14195498, by rfl⟩ : syracuseStep 75709325 = 28390997) B28390997
theorem B2186129 : Blo 1534464 2186129 := bstep (se 2 (by rfl) ⟨819798, by rfl⟩ : syracuseStep 2186129 = 1639597) B1639597
theorem B4373453 : Blo 1534464 4373453 := bstep (se 3 (by rfl) ⟨820022, by rfl⟩ : syracuseStep 4373453 = 1640045) B1640045
theorem B2333683 : Blo 1534464 2333683 := bstep (se 1 (by rfl) ⟨1750262, by rfl⟩ : syracuseStep 2333683 = 3500525) B3500525
theorem B1727491 : Blo 1534464 1727491 := bstep (se 1 (by rfl) ⟨1295618, by rfl⟩ : syracuseStep 1727491 = 2591237) B2591237
theorem B8739845 : Blo 1534464 8739845 := bstep (se 4 (by rfl) ⟨819360, by rfl⟩ : syracuseStep 8739845 = 1638721) B1638721
theorem B3456017 : Blo 1534464 3456017 := bstep (se 2 (by rfl) ⟨1296006, by rfl⟩ : syracuseStep 3456017 = 2592013) B2592013
theorem B3456035 : Blo 1534464 3456035 := bstep (se 1 (by rfl) ⟨2592026, by rfl⟩ : syracuseStep 3456035 = 5184053) B5184053
theorem B5184593 : Blo 1534464 5184593 := bstep (se 2 (by rfl) ⟨1944222, by rfl⟩ : syracuseStep 5184593 = 3888445) B3888445
theorem B1727635 : Blo 1534464 1727635 := bstep (se 1 (by rfl) ⟨1295726, by rfl⟩ : syracuseStep 1727635 = 2591453) B2591453
theorem B9469189 : Blo 1534464 9469189 := bstep (se 4 (by rfl) ⟨887736, by rfl⟩ : syracuseStep 9469189 = 1775473) B1775473
theorem B1727779 : Blo 1534464 1727779 := bstep (se 1 (by rfl) ⟨1295834, by rfl⟩ : syracuseStep 1727779 = 2591669) B2591669
theorem B5250349 : Blo 1534464 5250349 := bstep (se 3 (by rfl) ⟨984440, by rfl⟩ : syracuseStep 5250349 = 1968881) B1968881
theorem B3456305 : Blo 1534464 3456305 := bstep (se 2 (by rfl) ⟨1296114, by rfl⟩ : syracuseStep 3456305 = 2592229) B2592229
theorem B2915651 : Blo 1534464 2915651 := bstep (se 1 (by rfl) ⟨2186738, by rfl⟩ : syracuseStep 2915651 = 4373477) B4373477
theorem B3456323 : Blo 1534464 3456323 := bstep (se 1 (by rfl) ⟨2592242, by rfl⟩ : syracuseStep 3456323 = 5184485) B5184485
theorem B4152653 : Blo 1534464 4152653 := bstep (se 3 (by rfl) ⟨778622, by rfl⟩ : syracuseStep 4152653 = 1557245) B1557245
theorem B6561137 : Blo 1534464 6561137 := bstep (se 2 (by rfl) ⟨2460426, by rfl⟩ : syracuseStep 6561137 = 4920853) B4920853
theorem B17497457 : Blo 1534464 17497457 := bstep (se 2 (by rfl) ⟨6561546, by rfl⟩ : syracuseStep 17497457 = 13123093) B13123093
theorem B1727923 : Blo 1534464 1727923 := bstep (se 1 (by rfl) ⟨1295942, by rfl⟩ : syracuseStep 1727923 = 2591885) B2591885
theorem B8306189 : Blo 1534464 8306189 := bstep (se 3 (by rfl) ⟨1557410, by rfl⟩ : syracuseStep 8306189 = 3114821) B3114821
theorem B7773731 : Blo 1534464 7773731 := bstep (se 1 (by rfl) ⟨5830298, by rfl⟩ : syracuseStep 7773731 = 11660597) B11660597
theorem B8748593 : Blo 1534464 8748593 := bstep (se 2 (by rfl) ⟨3280722, by rfl⟩ : syracuseStep 8748593 = 6561445) B6561445
theorem B1728067 : Blo 1534464 1728067 := bstep (se 1 (by rfl) ⟨1296050, by rfl⟩ : syracuseStep 1728067 = 2592101) B2592101
theorem B3456593 : Blo 1534464 3456593 := bstep (se 2 (by rfl) ⟨1296222, by rfl⟩ : syracuseStep 3456593 = 2592445) B2592445
theorem B2915939 : Blo 1534464 2915939 := bstep (se 1 (by rfl) ⟨2186954, by rfl⟩ : syracuseStep 2915939 = 4373909) B4373909
theorem B3456611 : Blo 1534464 3456611 := bstep (se 1 (by rfl) ⟨2592458, by rfl⟩ : syracuseStep 3456611 = 5184917) B5184917
theorem B5185133 : Blo 1534464 5185133 := bstep (se 3 (by rfl) ⟨972212, by rfl⟩ : syracuseStep 5185133 = 1944425) B1944425
theorem B5987981 : Blo 1534464 5987981 := bstep (se 3 (by rfl) ⟨1122746, by rfl⟩ : syracuseStep 5987981 = 2245493) B2245493
theorem B5185187 : Blo 1534464 5185187 := bstep (se 1 (by rfl) ⟨3888890, by rfl⟩ : syracuseStep 5185187 = 7777781) B7777781
theorem B5250737 : Blo 1534464 5250737 := bstep (se 2 (by rfl) ⟨1969026, by rfl⟩ : syracuseStep 5250737 = 3938053) B3938053
theorem B1728211 : Blo 1534464 1728211 := bstep (se 1 (by rfl) ⟨1296158, by rfl⟩ : syracuseStep 1728211 = 2592317) B2592317
theorem B2186995 : Blo 1534464 2186995 := bstep (se 1 (by rfl) ⟨1640246, by rfl⟩ : syracuseStep 2186995 = 3280493) B3280493
theorem B2301713 : Blo 1534464 2301713 := bstep (se 2 (by rfl) ⟨863142, by rfl⟩ : syracuseStep 2301713 = 1726285) B1726285
theorem B2301731 : Blo 1534464 2301731 := bstep (se 1 (by rfl) ⟨1726298, by rfl⟩ : syracuseStep 2301731 = 3452597) B3452597
theorem B2301761 : Blo 1534464 2301761 := bstep (se 2 (by rfl) ⟨863160, by rfl⟩ : syracuseStep 2301761 = 1726321) B1726321
theorem B4669265 : Blo 1534464 4669265 := bstep (se 2 (by rfl) ⟨1750974, by rfl⟩ : syracuseStep 4669265 = 3501949) B3501949
theorem B2301779 : Blo 1534464 2301779 := bstep (se 1 (by rfl) ⟨1726334, by rfl⟩ : syracuseStep 2301779 = 3452669) B3452669
theorem B2187091 : Blo 1534464 2187091 := bstep (se 1 (by rfl) ⟨1640318, by rfl⟩ : syracuseStep 2187091 = 3280637) B3280637
theorem B1728355 : Blo 1534464 1728355 := bstep (se 1 (by rfl) ⟨1296266, by rfl⟩ : syracuseStep 1728355 = 2592533) B2592533
theorem B2301809 : Blo 1534464 2301809 := bstep (se 2 (by rfl) ⟨863178, by rfl⟩ : syracuseStep 2301809 = 1726357) B1726357
theorem B3456881 : Blo 1534464 3456881 := bstep (se 2 (by rfl) ⟨1296330, by rfl⟩ : syracuseStep 3456881 = 2592661) B2592661
theorem B2301827 : Blo 1534464 2301827 := bstep (se 1 (by rfl) ⟨1726370, by rfl⟩ : syracuseStep 2301827 = 3452741) B3452741
theorem B3456899 : Blo 1534464 3456899 := bstep (se 1 (by rfl) ⟨2592674, by rfl⟩ : syracuseStep 3456899 = 5185349) B5185349
theorem B2301857 : Blo 1534464 2301857 := bstep (se 2 (by rfl) ⟨863196, by rfl⟩ : syracuseStep 2301857 = 1726393) B1726393
theorem B6397859 : Blo 1534464 6397859 := bstep (se 1 (by rfl) ⟨4798394, by rfl⟩ : syracuseStep 6397859 = 9596789) B9596789
theorem B4374445 : Blo 1534464 4374445 := bstep (se 3 (by rfl) ⟨820208, by rfl⟩ : syracuseStep 4374445 = 1640417) B1640417
theorem B5185457 : Blo 1534464 5185457 := bstep (se 2 (by rfl) ⟨1944546, by rfl⟩ : syracuseStep 5185457 = 3889093) B3889093
theorem B2301875 : Blo 1534464 2301875 := bstep (se 1 (by rfl) ⟨1726406, by rfl⟩ : syracuseStep 2301875 = 3452813) B3452813
theorem B2301905 : Blo 1534464 2301905 := bstep (se 2 (by rfl) ⟨863214, by rfl⟩ : syracuseStep 2301905 = 1726429) B1726429
theorem B2301923 : Blo 1534464 2301923 := bstep (se 1 (by rfl) ⟨1726442, by rfl⟩ : syracuseStep 2301923 = 3452885) B3452885
theorem B1728499 : Blo 1534464 1728499 := bstep (se 1 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 1728499 = 2592749) B2592749
theorem B3457025 : Blo 1534464 3457025 := bstep (se 2 (by rfl) ⟨1296384, by rfl⟩ : syracuseStep 3457025 = 2592769) B2592769
theorem B2301977 : Blo 1534464 2301977 := bstep (se 2 (by rfl) ⟨863241, by rfl⟩ : syracuseStep 2301977 = 1726483) B1726483
theorem B4374593 : Blo 1534464 4374593 := bstep (se 2 (by rfl) ⟨1640472, by rfl⟩ : syracuseStep 4374593 = 3280945) B3280945
theorem B26230877 : Blo 1534464 26230877 := bstep (se 3 (by rfl) ⟨4918289, by rfl⟩ : syracuseStep 26230877 = 9836579) B9836579
theorem B2302091 : Blo 1534464 2302091 := bstep (se 1 (by rfl) ⟨1726568, by rfl⟩ : syracuseStep 2302091 = 3453137) B3453137
theorem B2302103 : Blo 1534464 2302103 := bstep (se 1 (by rfl) ⟨1726577, by rfl⟩ : syracuseStep 2302103 = 3453155) B3453155
theorem B7102637 : Blo 1534464 7102637 := bstep (se 3 (by rfl) ⟨1331744, by rfl⟩ : syracuseStep 7102637 = 2663489) B2663489
theorem B2302169 : Blo 1534464 2302169 := bstep (se 2 (by rfl) ⟨863313, by rfl⟩ : syracuseStep 2302169 = 1726627) B1726627
theorem B2302283 : Blo 1534464 2302283 := bstep (se 1 (by rfl) ⟨1726712, by rfl⟩ : syracuseStep 2302283 = 3453425) B3453425
theorem B2302295 : Blo 1534464 2302295 := bstep (se 1 (by rfl) ⟨1726721, by rfl⟩ : syracuseStep 2302295 = 3453443) B3453443
theorem B4374935 : Blo 1534464 4374935 := bstep (se 1 (by rfl) ⟨3281201, by rfl⟩ : syracuseStep 4374935 = 6562403) B6562403
theorem B2302361 : Blo 1534464 2302361 := bstep (se 2 (by rfl) ⟨863385, by rfl⟩ : syracuseStep 2302361 = 1726771) B1726771
theorem B2302475 : Blo 1534464 2302475 := bstep (se 1 (by rfl) ⟨1726856, by rfl⟩ : syracuseStep 2302475 = 3453713) B3453713
theorem B2302487 : Blo 1534464 2302487 := bstep (se 1 (by rfl) ⟨1726865, by rfl⟩ : syracuseStep 2302487 = 3453731) B3453731
theorem B5923351 : Blo 1534464 5923351 := bstep (se 1 (by rfl) ⟨4442513, by rfl⟩ : syracuseStep 5923351 = 8885027) B8885027
theorem B2245207 : Blo 1534464 2245207 := bstep (se 1 (by rfl) ⟨1683905, by rfl⟩ : syracuseStep 2245207 = 3367811) B3367811
theorem B2302553 : Blo 1534464 2302553 := bstep (se 2 (by rfl) ⟨863457, by rfl⟩ : syracuseStep 2302553 = 1726915) B1726915
theorem B11067997 : Blo 1534464 11067997 := bstep (se 3 (by rfl) ⟨2075249, by rfl⟩ : syracuseStep 11067997 = 4150499) B4150499
theorem B1639063 : Blo 1534464 1639063 := bstep (se 1 (by rfl) ⟨1229297, by rfl⟩ : syracuseStep 1639063 = 2458595) B2458595
theorem B5833367 : Blo 1534464 5833367 := bstep (se 1 (by rfl) ⟨4375025, by rfl⟩ : syracuseStep 5833367 = 8750051) B8750051
theorem B2302667 : Blo 1534464 2302667 := bstep (se 1 (by rfl) ⟨1727000, by rfl⟩ : syracuseStep 2302667 = 3454001) B3454001
theorem B2302679 : Blo 1534464 2302679 := bstep (se 1 (by rfl) ⟨1727009, by rfl⟩ : syracuseStep 2302679 = 3454019) B3454019
theorem B3277579 : Blo 1534464 3277579 := bstep (se 1 (by rfl) ⟨2458184, by rfl⟩ : syracuseStep 3277579 = 4916369) B4916369
theorem B2302745 : Blo 1534464 2302745 := bstep (se 2 (by rfl) ⟨863529, by rfl⟩ : syracuseStep 2302745 = 1727059) B1727059
theorem B2589529 : Blo 1534464 2589529 := bstep (se 2 (by rfl) ⟨971073, by rfl⟩ : syracuseStep 2589529 = 1942147) B1942147
theorem B3687257 : Blo 1534464 3687257 := bstep (se 2 (by rfl) ⟨1382721, by rfl⟩ : syracuseStep 3687257 = 2765443) B2765443
theorem B5833565 : Blo 1534464 5833565 := bstep (se 3 (by rfl) ⟨1093793, by rfl⟩ : syracuseStep 5833565 = 2187587) B2187587
theorem B2302859 : Blo 1534464 2302859 := bstep (se 1 (by rfl) ⟨1727144, by rfl⟩ : syracuseStep 2302859 = 3454289) B3454289
theorem B2302871 : Blo 1534464 2302871 := bstep (se 1 (by rfl) ⟨1727153, by rfl⟩ : syracuseStep 2302871 = 3454307) B3454307
theorem B2335691 : Blo 1534464 2335691 := bstep (se 1 (by rfl) ⟨1751768, by rfl⟩ : syracuseStep 2335691 = 3503537) B3503537
theorem B2302937 : Blo 1534464 2302937 := bstep (se 2 (by rfl) ⟨863601, by rfl⟩ : syracuseStep 2302937 = 1727203) B1727203
theorem B6562777 : Blo 1534464 6562777 := bstep (se 2 (by rfl) ⟨2461041, by rfl⟩ : syracuseStep 6562777 = 4922083) B4922083
theorem B4916189 : Blo 1534464 4916189 := bstep (se 3 (by rfl) ⟨921785, by rfl⟩ : syracuseStep 4916189 = 1843571) B1843571
theorem B3277835 : Blo 1534464 3277835 := bstep (se 1 (by rfl) ⟨2458376, by rfl⟩ : syracuseStep 3277835 = 4916753) B4916753
theorem B49832981 : Blo 1534464 49832981 := bstep (se 6 (by rfl) ⟨1167960, by rfl⟩ : syracuseStep 49832981 = 2335921) B2335921
theorem B2303051 : Blo 1534464 2303051 := bstep (se 1 (by rfl) ⟨1727288, by rfl⟩ : syracuseStep 2303051 = 3454577) B3454577
theorem B2303063 : Blo 1534464 2303063 := bstep (se 1 (by rfl) ⟨1727297, by rfl⟩ : syracuseStep 2303063 = 3454595) B3454595
theorem B3884183 : Blo 1534464 3884183 := bstep (se 1 (by rfl) ⟨2913137, by rfl⟩ : syracuseStep 3884183 = 5826275) B5826275
theorem B2303129 : Blo 1534464 2303129 := bstep (se 2 (by rfl) ⟨863673, by rfl⟩ : syracuseStep 2303129 = 1727347) B1727347
theorem B26248373 : Blo 1534464 26248373 := bstep (se 5 (by rfl) ⟨1230392, by rfl⟩ : syracuseStep 26248373 = 2460785) B2460785
theorem B1942795 : Blo 1534464 1942795 := bstep (se 1 (by rfl) ⟨1457096, by rfl⟩ : syracuseStep 1942795 = 2914193) B2914193
theorem B2303243 : Blo 1534464 2303243 := bstep (se 1 (by rfl) ⟨1727432, by rfl⟩ : syracuseStep 2303243 = 3454865) B3454865
theorem B2303255 : Blo 1534464 2303255 := bstep (se 1 (by rfl) ⟨1727441, by rfl⟩ : syracuseStep 2303255 = 3454883) B3454883
theorem B14763329 : Blo 1534464 14763329 := bstep (se 2 (by rfl) ⟨5536248, by rfl⟩ : syracuseStep 14763329 = 11072497) B11072497
theorem B2303321 : Blo 1534464 2303321 := bstep (se 2 (by rfl) ⟨863745, by rfl⟩ : syracuseStep 2303321 = 1727491) B1727491
theorem B2590103 : Blo 1534464 2590103 := bstep (se 1 (by rfl) ⟨1942577, by rfl⟩ : syracuseStep 2590103 = 3885155) B3885155
theorem B2303435 : Blo 1534464 2303435 := bstep (se 1 (by rfl) ⟨1727576, by rfl⟩ : syracuseStep 2303435 = 3455153) B3455153
theorem B1639883 : Blo 1534464 1639883 := bstep (se 1 (by rfl) ⟨1229912, by rfl⟩ : syracuseStep 1639883 = 2459825) B2459825
theorem B2303447 : Blo 1534464 2303447 := bstep (se 1 (by rfl) ⟨1727585, by rfl⟩ : syracuseStep 2303447 = 3455171) B3455171
theorem B2590231 : Blo 1534464 2590231 := bstep (se 1 (by rfl) ⟨1942673, by rfl⟩ : syracuseStep 2590231 = 3885347) B3885347
theorem B2303513 : Blo 1534464 2303513 := bstep (se 2 (by rfl) ⟨863817, by rfl⟩ : syracuseStep 2303513 = 1727635) B1727635
theorem B28001861 : Blo 1534464 28001861 := bstep (se 4 (by rfl) ⟨2625174, by rfl⟩ : syracuseStep 28001861 = 5250349) B5250349
theorem B1640011 : Blo 1534464 1640011 := bstep (se 1 (by rfl) ⟨1230008, by rfl⟩ : syracuseStep 1640011 = 2460017) B2460017
theorem B7775837 : Blo 1534464 7775837 := bstep (se 3 (by rfl) ⟨1457969, by rfl⟩ : syracuseStep 7775837 = 2915939) B2915939
theorem B2303627 : Blo 1534464 2303627 := bstep (se 1 (by rfl) ⟨1727720, by rfl⟩ : syracuseStep 2303627 = 3455441) B3455441
theorem B5179031 : Blo 1534464 5179031 := bstep (se 1 (by rfl) ⟨3884273, by rfl⟩ : syracuseStep 5179031 = 7768547) B7768547
theorem B13117079 : Blo 1534464 13117079 := bstep (se 1 (by rfl) ⟨9837809, by rfl⟩ : syracuseStep 13117079 = 19675619) B19675619
theorem B2303639 : Blo 1534464 2303639 := bstep (se 1 (by rfl) ⟨1727729, by rfl⟩ : syracuseStep 2303639 = 3455459) B3455459
theorem B6555329 : Blo 1534464 6555329 := bstep (se 2 (by rfl) ⟨2458248, by rfl⟩ : syracuseStep 6555329 = 4916497) B4916497
theorem B2303705 : Blo 1534464 2303705 := bstep (se 2 (by rfl) ⟨863889, by rfl⟩ : syracuseStep 2303705 = 1727779) B1727779
theorem B3548951 : Blo 1534464 3548951 := bstep (se 1 (by rfl) ⟨2661713, by rfl⟩ : syracuseStep 3548951 = 5323427) B5323427
theorem B7374667 : Blo 1534464 7374667 := bstep (se 1 (by rfl) ⟨5531000, by rfl⟩ : syracuseStep 7374667 = 11062001) B11062001
theorem B2303819 : Blo 1534464 2303819 := bstep (se 1 (by rfl) ⟨1727864, by rfl⟩ : syracuseStep 2303819 = 3455729) B3455729
theorem B2459479 : Blo 1534464 2459479 := bstep (se 1 (by rfl) ⟨1844609, by rfl⟩ : syracuseStep 2459479 = 3689219) B3689219
theorem B2303831 : Blo 1534464 2303831 := bstep (se 1 (by rfl) ⟨1727873, by rfl⟩ : syracuseStep 2303831 = 3455747) B3455747
theorem B11659139 : Blo 1534464 11659139 := bstep (se 1 (by rfl) ⟨8744354, by rfl⟩ : syracuseStep 11659139 = 17488709) B17488709
theorem B2303897 : Blo 1534464 2303897 := bstep (se 2 (by rfl) ⟨863961, by rfl⟩ : syracuseStep 2303897 = 1727923) B1727923
theorem B33220529 : Blo 1534464 33220529 := bstep (se 2 (by rfl) ⟨12457698, by rfl⟩ : syracuseStep 33220529 = 24915397) B24915397
theorem B50472883 : Blo 1534464 50472883 := bstep (se 1 (by rfl) ⟨37854662, by rfl⟩ : syracuseStep 50472883 = 75709325) B75709325
theorem B3884993 : Blo 1534464 3884993 := bstep (se 2 (by rfl) ⟨1456872, by rfl⟩ : syracuseStep 3884993 = 2913745) B2913745
theorem B3278809 : Blo 1534464 3278809 := bstep (se 2 (by rfl) ⟨1229553, by rfl⟩ : syracuseStep 3278809 = 2459107) B2459107
theorem B5826563 : Blo 1534464 5826563 := bstep (se 1 (by rfl) ⟨4369922, by rfl⟩ : syracuseStep 5826563 = 8739845) B8739845
theorem B2304011 : Blo 1534464 2304011 := bstep (se 1 (by rfl) ⟨1728008, by rfl⟩ : syracuseStep 2304011 = 3456017) B3456017
theorem B2304023 : Blo 1534464 2304023 := bstep (se 1 (by rfl) ⟨1728017, by rfl⟩ : syracuseStep 2304023 = 3456035) B3456035
theorem B4671553 : Blo 1534464 4671553 := bstep (se 2 (by rfl) ⟨1751832, by rfl⟩ : syracuseStep 4671553 = 3503665) B3503665
theorem B15763531 : Blo 1534464 15763531 := bstep (se 1 (by rfl) ⟨11822648, by rfl⟩ : syracuseStep 15763531 = 23645297) B23645297
theorem B2459735 : Blo 1534464 2459735 := bstep (se 1 (by rfl) ⟨1844801, by rfl⟩ : syracuseStep 2459735 = 3689603) B3689603
theorem B2304089 : Blo 1534464 2304089 := bstep (se 2 (by rfl) ⟨864033, by rfl⟩ : syracuseStep 2304089 = 1728067) B1728067
theorem B3278963 : Blo 1534464 3278963 := bstep (se 1 (by rfl) ⟨2459222, by rfl⟩ : syracuseStep 3278963 = 4918445) B4918445
theorem B2590859 : Blo 1534464 2590859 := bstep (se 1 (by rfl) ⟨1943144, by rfl⟩ : syracuseStep 2590859 = 3886289) B3886289
theorem B5179571 : Blo 1534464 5179571 := bstep (se 1 (by rfl) ⟨3884678, by rfl⟩ : syracuseStep 5179571 = 7769357) B7769357
theorem B2304203 : Blo 1534464 2304203 := bstep (se 1 (by rfl) ⟨1728152, by rfl⟩ : syracuseStep 2304203 = 3456305) B3456305
theorem B1943767 : Blo 1534464 1943767 := bstep (se 1 (by rfl) ⟨1457825, by rfl⟩ : syracuseStep 1943767 = 2915651) B2915651
theorem B2304215 : Blo 1534464 2304215 := bstep (se 1 (by rfl) ⟨1728161, by rfl⟩ : syracuseStep 2304215 = 3456323) B3456323
theorem B2590987 : Blo 1534464 2590987 := bstep (se 1 (by rfl) ⟨1943240, by rfl⟩ : syracuseStep 2590987 = 3886481) B3886481
theorem B2459927 : Blo 1534464 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B2304281 : Blo 1534464 2304281 := bstep (se 2 (by rfl) ⟨864105, by rfl⟩ : syracuseStep 2304281 = 1728211) B1728211
theorem B11061539 : Blo 1534464 11061539 := bstep (se 1 (by rfl) ⟨8296154, by rfl⟩ : syracuseStep 11061539 = 16592309) B16592309
theorem B12798253 : Blo 1534464 12798253 := bstep (se 3 (by rfl) ⟨2399672, by rfl⟩ : syracuseStep 12798253 = 4799345) B4799345
theorem B7768385 : Blo 1534464 7768385 := bstep (se 2 (by rfl) ⟨2913144, by rfl⟩ : syracuseStep 7768385 = 5826289) B5826289
theorem B8743261 : Blo 1534464 8743261 := bstep (se 3 (by rfl) ⟨1639361, by rfl⟩ : syracuseStep 8743261 = 3278723) B3278723
theorem B2304395 : Blo 1534464 2304395 := bstep (se 1 (by rfl) ⟨1728296, by rfl⟩ : syracuseStep 2304395 = 3456593) B3456593
theorem B2304407 : Blo 1534464 2304407 := bstep (se 1 (by rfl) ⟨1728305, by rfl⟩ : syracuseStep 2304407 = 3456611) B3456611
theorem B2591129 : Blo 1534464 2591129 := bstep (se 2 (by rfl) ⟨971673, by rfl⟩ : syracuseStep 2591129 = 1943347) B1943347
theorem B7375283 : Blo 1534464 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B3991987 : Blo 1534464 3991987 := bstep (se 1 (by rfl) ⟨2993990, by rfl⟩ : syracuseStep 3991987 = 5987981) B5987981
theorem B5179841 : Blo 1534464 5179841 := bstep (se 2 (by rfl) ⟨1942440, by rfl⟩ : syracuseStep 5179841 = 3884881) B3884881
theorem B5532097 : Blo 1534464 5532097 := bstep (se 2 (by rfl) ⟨2074536, by rfl⟩ : syracuseStep 5532097 = 4149073) B4149073
theorem B3500491 : Blo 1534464 3500491 := bstep (se 1 (by rfl) ⟨2625368, by rfl⟩ : syracuseStep 3500491 = 5250737) B5250737
theorem B3885529 : Blo 1534464 3885529 := bstep (se 2 (by rfl) ⟨1457073, by rfl⟩ : syracuseStep 3885529 = 2914147) B2914147
theorem B2304473 : Blo 1534464 2304473 := bstep (se 2 (by rfl) ⟨864177, by rfl⟩ : syracuseStep 2304473 = 1728355) B1728355
theorem B1534475 : Blo 1534464 1534475 := bstep (se 1 (by rfl) ⟨1150856, by rfl⟩ : syracuseStep 1534475 = 2301713) B2301713
theorem B1534487 : Blo 1534464 1534487 := bstep (se 1 (by rfl) ⟨1150865, by rfl⟩ : syracuseStep 1534487 = 2301731) B2301731
theorem B2591257 : Blo 1534464 2591257 := bstep (se 2 (by rfl) ⟨971721, by rfl⟩ : syracuseStep 2591257 = 1943443) B1943443
theorem B1534507 : Blo 1534464 1534507 := bstep (se 1 (by rfl) ⟨1150880, by rfl⟩ : syracuseStep 1534507 = 2301761) B2301761
theorem B1534519 : Blo 1534464 1534519 := bstep (se 1 (by rfl) ⟨1150889, by rfl⟩ : syracuseStep 1534519 = 2301779) B2301779
theorem B1534539 : Blo 1534464 1534539 := bstep (se 1 (by rfl) ⟨1150904, by rfl⟩ : syracuseStep 1534539 = 2301809) B2301809
theorem B2460235 : Blo 1534464 2460235 := bstep (se 1 (by rfl) ⟨1845176, by rfl⟩ : syracuseStep 2460235 = 3690353) B3690353
theorem B2304587 : Blo 1534464 2304587 := bstep (se 1 (by rfl) ⟨1728440, by rfl⟩ : syracuseStep 2304587 = 3456881) B3456881
theorem B1534551 : Blo 1534464 1534551 := bstep (se 1 (by rfl) ⟨1150913, by rfl⟩ : syracuseStep 1534551 = 2301827) B2301827
theorem B2304599 : Blo 1534464 2304599 := bstep (se 1 (by rfl) ⟨1728449, by rfl⟩ : syracuseStep 2304599 = 3456899) B3456899
theorem B1534571 : Blo 1534464 1534571 := bstep (se 1 (by rfl) ⟨1150928, by rfl⟩ : syracuseStep 1534571 = 2301857) B2301857
theorem B3279475 : Blo 1534464 3279475 := bstep (se 1 (by rfl) ⟨2459606, by rfl⟩ : syracuseStep 3279475 = 4919213) B4919213
theorem B1534583 : Blo 1534464 1534583 := bstep (se 1 (by rfl) ⟨1150937, by rfl⟩ : syracuseStep 1534583 = 2301875) B2301875
theorem B1534603 : Blo 1534464 1534603 := bstep (se 1 (by rfl) ⟨1150952, by rfl⟩ : syracuseStep 1534603 = 2301905) B2301905
theorem B1534615 : Blo 1534464 1534615 := bstep (se 1 (by rfl) ⟨1150961, by rfl⟩ : syracuseStep 1534615 = 2301923) B2301923
theorem B2304665 : Blo 1534464 2304665 := bstep (se 2 (by rfl) ⟨864249, by rfl⟩ : syracuseStep 2304665 = 1728499) B1728499
theorem B1534635 : Blo 1534464 1534635 := bstep (se 1 (by rfl) ⟨1150976, by rfl⟩ : syracuseStep 1534635 = 2301953) B2301953
theorem B1534647 : Blo 1534464 1534647 := bstep (se 1 (by rfl) ⟨1150985, by rfl⟩ : syracuseStep 1534647 = 2301971) B2301971
theorem B1534667 : Blo 1534464 1534667 := bstep (se 1 (by rfl) ⟨1151000, by rfl⟩ : syracuseStep 1534667 = 2302001) B2302001
theorem B1534679 : Blo 1534464 1534679 := bstep (se 1 (by rfl) ⟨1151009, by rfl⟩ : syracuseStep 1534679 = 2302019) B2302019
theorem B1534699 : Blo 1534464 1534699 := bstep (se 1 (by rfl) ⟨1151024, by rfl⟩ : syracuseStep 1534699 = 2302049) B2302049
theorem B1534711 : Blo 1534464 1534711 := bstep (se 1 (by rfl) ⟨1151033, by rfl⟩ : syracuseStep 1534711 = 2302067) B2302067
theorem B1534731 : Blo 1534464 1534731 := bstep (se 1 (by rfl) ⟨1151048, by rfl⟩ : syracuseStep 1534731 = 2302097) B2302097
theorem B1534743 : Blo 1534464 1534743 := bstep (se 1 (by rfl) ⟨1151057, by rfl⟩ : syracuseStep 1534743 = 2302115) B2302115
theorem B1534763 : Blo 1534464 1534763 := bstep (se 1 (by rfl) ⟨1151072, by rfl⟩ : syracuseStep 1534763 = 2302145) B2302145
theorem B1534775 : Blo 1534464 1534775 := bstep (se 1 (by rfl) ⟨1151081, by rfl⟩ : syracuseStep 1534775 = 2302163) B2302163
theorem B1534795 : Blo 1534464 1534795 := bstep (se 1 (by rfl) ⟨1151096, by rfl⟩ : syracuseStep 1534795 = 2302193) B2302193
theorem B1534807 : Blo 1534464 1534807 := bstep (se 1 (by rfl) ⟨1151105, by rfl⟩ : syracuseStep 1534807 = 2302211) B2302211
theorem B1534827 : Blo 1534464 1534827 := bstep (se 1 (by rfl) ⟨1151120, by rfl⟩ : syracuseStep 1534827 = 2302241) B2302241
theorem B1534839 : Blo 1534464 1534839 := bstep (se 1 (by rfl) ⟨1151129, by rfl⟩ : syracuseStep 1534839 = 2302259) B2302259
theorem B1534859 : Blo 1534464 1534859 := bstep (se 1 (by rfl) ⟨1151144, by rfl⟩ : syracuseStep 1534859 = 2302289) B2302289
theorem B1534871 : Blo 1534464 1534871 := bstep (se 1 (by rfl) ⟨1151153, by rfl⟩ : syracuseStep 1534871 = 2302307) B2302307
theorem B1534891 : Blo 1534464 1534891 := bstep (se 1 (by rfl) ⟨1151168, by rfl⟩ : syracuseStep 1534891 = 2302337) B2302337
theorem B1534903 : Blo 1534464 1534903 := bstep (se 1 (by rfl) ⟨1151177, by rfl⟩ : syracuseStep 1534903 = 2302355) B2302355
theorem B1534923 : Blo 1534464 1534923 := bstep (se 1 (by rfl) ⟨1151192, by rfl⟩ : syracuseStep 1534923 = 2302385) B2302385
theorem B1534935 : Blo 1534464 1534935 := bstep (se 1 (by rfl) ⟨1151201, by rfl⟩ : syracuseStep 1534935 = 2302403) B2302403
theorem B5180381 : Blo 1534464 5180381 := bstep (se 3 (by rfl) ⟨971321, by rfl⟩ : syracuseStep 5180381 = 1942643) B1942643
theorem B1534955 : Blo 1534464 1534955 := bstep (se 1 (by rfl) ⟨1151216, by rfl⟩ : syracuseStep 1534955 = 2302433) B2302433
theorem B1534967 : Blo 1534464 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B1534987 : Blo 1534464 1534987 := bstep (se 1 (by rfl) ⟨1151240, by rfl⟩ : syracuseStep 1534987 = 2302481) B2302481
theorem B2460683 : Blo 1534464 2460683 := bstep (se 1 (by rfl) ⟨1845512, by rfl⟩ : syracuseStep 2460683 = 3691025) B3691025
theorem B1944587 : Blo 1534464 1944587 := bstep (se 1 (by rfl) ⟨1458440, by rfl⟩ : syracuseStep 1944587 = 2916881) B2916881
theorem B1534999 : Blo 1534464 1534999 := bstep (se 1 (by rfl) ⟨1151249, by rfl⟩ : syracuseStep 1534999 = 2302499) B2302499
theorem B1535019 : Blo 1534464 1535019 := bstep (se 1 (by rfl) ⟨1151264, by rfl⟩ : syracuseStep 1535019 = 2302529) B2302529
theorem B8989741 : Blo 1534464 8989741 := bstep (se 3 (by rfl) ⟨1685576, by rfl⟩ : syracuseStep 8989741 = 3371153) B3371153
theorem B1535031 : Blo 1534464 1535031 := bstep (se 1 (by rfl) ⟨1151273, by rfl⟩ : syracuseStep 1535031 = 2302547) B2302547
theorem B6556747 : Blo 1534464 6556747 := bstep (se 1 (by rfl) ⟨4917560, by rfl⟩ : syracuseStep 6556747 = 9835121) B9835121
theorem B1535051 : Blo 1534464 1535051 := bstep (se 1 (by rfl) ⟨1151288, by rfl⟩ : syracuseStep 1535051 = 2302577) B2302577
theorem B1535063 : Blo 1534464 1535063 := bstep (se 1 (by rfl) ⟨1151297, by rfl⟩ : syracuseStep 1535063 = 2302595) B2302595
theorem B2591831 : Blo 1534464 2591831 := bstep (se 1 (by rfl) ⟨1943873, by rfl⟩ : syracuseStep 2591831 = 3887747) B3887747
theorem B5532761 : Blo 1534464 5532761 := bstep (se 2 (by rfl) ⟨2074785, by rfl⟩ : syracuseStep 5532761 = 4149571) B4149571
theorem B1535083 : Blo 1534464 1535083 := bstep (se 1 (by rfl) ⟨1151312, by rfl⟩ : syracuseStep 1535083 = 2302625) B2302625
theorem B1535095 : Blo 1534464 1535095 := bstep (se 1 (by rfl) ⟨1151321, by rfl⟩ : syracuseStep 1535095 = 2302643) B2302643
theorem B1535115 : Blo 1534464 1535115 := bstep (se 1 (by rfl) ⟨1151336, by rfl⟩ : syracuseStep 1535115 = 2302673) B2302673
theorem B1535127 : Blo 1534464 1535127 := bstep (se 1 (by rfl) ⟨1151345, by rfl⟩ : syracuseStep 1535127 = 2302691) B2302691
theorem B1535147 : Blo 1534464 1535147 := bstep (se 1 (by rfl) ⟨1151360, by rfl⟩ : syracuseStep 1535147 = 2302721) B2302721
theorem B23956661 : Blo 1534464 23956661 := bstep (se 5 (by rfl) ⟨1122968, by rfl⟩ : syracuseStep 23956661 = 2245937) B2245937
theorem B1535159 : Blo 1534464 1535159 := bstep (se 1 (by rfl) ⟨1151369, by rfl⟩ : syracuseStep 1535159 = 2302739) B2302739
theorem B1535179 : Blo 1534464 1535179 := bstep (se 1 (by rfl) ⟨1151384, by rfl⟩ : syracuseStep 1535179 = 2302769) B2302769
theorem B1535191 : Blo 1534464 1535191 := bstep (se 1 (by rfl) ⟨1151393, by rfl⟩ : syracuseStep 1535191 = 2302787) B2302787
theorem B2591959 : Blo 1534464 2591959 := bstep (se 1 (by rfl) ⟨1943969, by rfl⟩ : syracuseStep 2591959 = 3887939) B3887939
theorem B1535211 : Blo 1534464 1535211 := bstep (se 1 (by rfl) ⟨1151408, by rfl⟩ : syracuseStep 1535211 = 2302817) B2302817
theorem B1535223 : Blo 1534464 1535223 := bstep (se 1 (by rfl) ⟨1151417, by rfl⟩ : syracuseStep 1535223 = 2302835) B2302835
theorem B1535243 : Blo 1534464 1535243 := bstep (se 1 (by rfl) ⟨1151432, by rfl⟩ : syracuseStep 1535243 = 2302865) B2302865
theorem B1535255 : Blo 1534464 1535255 := bstep (se 1 (by rfl) ⟨1151441, by rfl⟩ : syracuseStep 1535255 = 2302883) B2302883
theorem B3280151 : Blo 1534464 3280151 := bstep (se 1 (by rfl) ⟨2460113, by rfl⟩ : syracuseStep 3280151 = 4920227) B4920227
theorem B1535275 : Blo 1534464 1535275 := bstep (se 1 (by rfl) ⟨1151456, by rfl⟩ : syracuseStep 1535275 = 2302913) B2302913
theorem B1535287 : Blo 1534464 1535287 := bstep (se 1 (by rfl) ⟨1151465, by rfl⟩ : syracuseStep 1535287 = 2302931) B2302931
theorem B3280193 : Blo 1534464 3280193 := bstep (se 2 (by rfl) ⟨1230072, by rfl⟩ : syracuseStep 3280193 = 2460145) B2460145
theorem B1535307 : Blo 1534464 1535307 := bstep (se 1 (by rfl) ⟨1151480, by rfl⟩ : syracuseStep 1535307 = 2302961) B2302961
theorem B1535319 : Blo 1534464 1535319 := bstep (se 1 (by rfl) ⟨1151489, by rfl⟩ : syracuseStep 1535319 = 2302979) B2302979
theorem B6557021 : Blo 1534464 6557021 := bstep (se 3 (by rfl) ⟨1229441, by rfl⟩ : syracuseStep 6557021 = 2458883) B2458883
theorem B1535339 : Blo 1534464 1535339 := bstep (se 1 (by rfl) ⟨1151504, by rfl⟩ : syracuseStep 1535339 = 2303009) B2303009
theorem B1535351 : Blo 1534464 1535351 := bstep (se 1 (by rfl) ⟨1151513, by rfl⟩ : syracuseStep 1535351 = 2303027) B2303027
theorem B1535371 : Blo 1534464 1535371 := bstep (se 1 (by rfl) ⟨1151528, by rfl⟩ : syracuseStep 1535371 = 2303057) B2303057
theorem B1535383 : Blo 1534464 1535383 := bstep (se 1 (by rfl) ⟨1151537, by rfl⟩ : syracuseStep 1535383 = 2303075) B2303075
theorem B1535403 : Blo 1534464 1535403 := bstep (se 1 (by rfl) ⟨1151552, by rfl⟩ : syracuseStep 1535403 = 2303105) B2303105
theorem B1535415 : Blo 1534464 1535415 := bstep (se 1 (by rfl) ⟨1151561, by rfl⟩ : syracuseStep 1535415 = 2303123) B2303123
theorem B1535435 : Blo 1534464 1535435 := bstep (se 1 (by rfl) ⟨1151576, by rfl⟩ : syracuseStep 1535435 = 2303153) B2303153
theorem B1535447 : Blo 1534464 1535447 := bstep (se 1 (by rfl) ⟨1151585, by rfl⟩ : syracuseStep 1535447 = 2303171) B2303171
theorem B1535467 : Blo 1534464 1535467 := bstep (se 1 (by rfl) ⟨1151600, by rfl⟩ : syracuseStep 1535467 = 2303201) B2303201
theorem B1535479 : Blo 1534464 1535479 := bstep (se 1 (by rfl) ⟨1151609, by rfl⟩ : syracuseStep 1535479 = 2303219) B2303219
theorem B1535499 : Blo 1534464 1535499 := bstep (se 1 (by rfl) ⟨1151624, by rfl⟩ : syracuseStep 1535499 = 2303249) B2303249
theorem B13118993 : Blo 1534464 13118993 := bstep (se 2 (by rfl) ⟨4919622, by rfl⟩ : syracuseStep 13118993 = 9839245) B9839245
theorem B1535511 : Blo 1534464 1535511 := bstep (se 1 (by rfl) ⟨1151633, by rfl⟩ : syracuseStep 1535511 = 2303267) B2303267
theorem B1535531 : Blo 1534464 1535531 := bstep (se 1 (by rfl) ⟨1151648, by rfl⟩ : syracuseStep 1535531 = 2303297) B2303297
theorem B3886643 : Blo 1534464 3886643 := bstep (se 1 (by rfl) ⟨2914982, by rfl⟩ : syracuseStep 3886643 = 5829965) B5829965
theorem B1535543 : Blo 1534464 1535543 := bstep (se 1 (by rfl) ⟨1151657, by rfl⟩ : syracuseStep 1535543 = 2303315) B2303315
theorem B1535563 : Blo 1534464 1535563 := bstep (se 1 (by rfl) ⟨1151672, by rfl⟩ : syracuseStep 1535563 = 2303345) B2303345
theorem B1535575 : Blo 1534464 1535575 := bstep (se 1 (by rfl) ⟨1151681, by rfl⟩ : syracuseStep 1535575 = 2303363) B2303363
theorem B4795993 : Blo 1534464 4795993 := bstep (se 2 (by rfl) ⟨1798497, by rfl⟩ : syracuseStep 4795993 = 3596995) B3596995
theorem B1535595 : Blo 1534464 1535595 := bstep (se 1 (by rfl) ⟨1151696, by rfl⟩ : syracuseStep 1535595 = 2303393) B2303393
theorem B1535607 : Blo 1534464 1535607 := bstep (se 1 (by rfl) ⟨1151705, by rfl⟩ : syracuseStep 1535607 = 2303411) B2303411
theorem B1535627 : Blo 1534464 1535627 := bstep (se 1 (by rfl) ⟨1151720, by rfl⟩ : syracuseStep 1535627 = 2303441) B2303441
theorem B4370071 : Blo 1534464 4370071 := bstep (se 1 (by rfl) ⟨3277553, by rfl⟩ : syracuseStep 4370071 = 6555107) B6555107
theorem B1535639 : Blo 1534464 1535639 := bstep (se 1 (by rfl) ⟨1151729, by rfl⟩ : syracuseStep 1535639 = 2303459) B2303459
theorem B7777943 : Blo 1534464 7777943 := bstep (se 1 (by rfl) ⟨5833457, by rfl⟩ : syracuseStep 7777943 = 11666915) B11666915
theorem B1535659 : Blo 1534464 1535659 := bstep (se 1 (by rfl) ⟨1151744, by rfl⟩ : syracuseStep 1535659 = 2303489) B2303489
theorem B1535671 : Blo 1534464 1535671 := bstep (se 1 (by rfl) ⟨1151753, by rfl⟩ : syracuseStep 1535671 = 2303507) B2303507
theorem B1535691 : Blo 1534464 1535691 := bstep (se 1 (by rfl) ⟨1151768, by rfl⟩ : syracuseStep 1535691 = 2303537) B2303537
theorem B1535703 : Blo 1534464 1535703 := bstep (se 1 (by rfl) ⟨1151777, by rfl⟩ : syracuseStep 1535703 = 2303555) B2303555
theorem B3452633 : Blo 1534464 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B8302297 : Blo 1534464 8302297 := bstep (se 2 (by rfl) ⟨3113361, by rfl⟩ : syracuseStep 8302297 = 6226723) B6226723
theorem B1535723 : Blo 1534464 1535723 := bstep (se 1 (by rfl) ⟨1151792, by rfl⟩ : syracuseStep 1535723 = 2303585) B2303585
theorem B1535735 : Blo 1534464 1535735 := bstep (se 1 (by rfl) ⟨1151801, by rfl⟩ : syracuseStep 1535735 = 2303603) B2303603
theorem B1535755 : Blo 1534464 1535755 := bstep (se 1 (by rfl) ⟨1151816, by rfl⟩ : syracuseStep 1535755 = 2303633) B2303633
theorem B1535767 : Blo 1534464 1535767 := bstep (se 1 (by rfl) ⟨1151825, by rfl⟩ : syracuseStep 1535767 = 2303651) B2303651
theorem B1535787 : Blo 1534464 1535787 := bstep (se 1 (by rfl) ⟨1151840, by rfl⟩ : syracuseStep 1535787 = 2303681) B2303681
theorem B3452723 : Blo 1534464 3452723 := bstep (se 1 (by rfl) ⟨2589542, by rfl⟩ : syracuseStep 3452723 = 5179085) B5179085
theorem B1535799 : Blo 1534464 1535799 := bstep (se 1 (by rfl) ⟨1151849, by rfl⟩ : syracuseStep 1535799 = 2303699) B2303699
theorem B1535819 : Blo 1534464 1535819 := bstep (se 1 (by rfl) ⟨1151864, by rfl⟩ : syracuseStep 1535819 = 2303729) B2303729
theorem B2592587 : Blo 1534464 2592587 := bstep (se 1 (by rfl) ⟨1944440, by rfl⟩ : syracuseStep 2592587 = 3888881) B3888881
theorem B3452759 : Blo 1534464 3452759 := bstep (se 1 (by rfl) ⟨2589569, by rfl⟩ : syracuseStep 3452759 = 5179139) B5179139
theorem B3886937 : Blo 1534464 3886937 := bstep (se 2 (by rfl) ⟨1457601, by rfl⟩ : syracuseStep 3886937 = 2915203) B2915203
theorem B1535831 : Blo 1534464 1535831 := bstep (se 1 (by rfl) ⟨1151873, by rfl⟩ : syracuseStep 1535831 = 2303747) B2303747
theorem B1535851 : Blo 1534464 1535851 := bstep (se 1 (by rfl) ⟨1151888, by rfl⟩ : syracuseStep 1535851 = 2303777) B2303777
theorem B1535863 : Blo 1534464 1535863 := bstep (se 1 (by rfl) ⟨1151897, by rfl⟩ : syracuseStep 1535863 = 2303795) B2303795
theorem B1535883 : Blo 1534464 1535883 := bstep (se 1 (by rfl) ⟨1151912, by rfl⟩ : syracuseStep 1535883 = 2303825) B2303825
theorem B1535895 : Blo 1534464 1535895 := bstep (se 1 (by rfl) ⟨1151921, by rfl⟩ : syracuseStep 1535895 = 2303843) B2303843
theorem B1535915 : Blo 1534464 1535915 := bstep (se 1 (by rfl) ⟨1151936, by rfl⟩ : syracuseStep 1535915 = 2303873) B2303873
theorem B7991219 : Blo 1534464 7991219 := bstep (se 1 (by rfl) ⟨5993414, by rfl⟩ : syracuseStep 7991219 = 11986829) B11986829
theorem B1535927 : Blo 1534464 1535927 := bstep (se 1 (by rfl) ⟨1151945, by rfl⟩ : syracuseStep 1535927 = 2303891) B2303891
theorem B1535947 : Blo 1534464 1535947 := bstep (se 1 (by rfl) ⟨1151960, by rfl⟩ : syracuseStep 1535947 = 2303921) B2303921
theorem B2592715 : Blo 1534464 2592715 := bstep (se 1 (by rfl) ⟨1944536, by rfl⟩ : syracuseStep 2592715 = 3889073) B3889073
theorem B1535959 : Blo 1534464 1535959 := bstep (se 1 (by rfl) ⟨1151969, by rfl⟩ : syracuseStep 1535959 = 2303939) B2303939
theorem B1535979 : Blo 1534464 1535979 := bstep (se 1 (by rfl) ⟨1151984, by rfl⟩ : syracuseStep 1535979 = 2303969) B2303969
theorem B1535991 : Blo 1534464 1535991 := bstep (se 1 (by rfl) ⟨1151993, by rfl⟩ : syracuseStep 1535991 = 2303987) B2303987
theorem B3452939 : Blo 1534464 3452939 := bstep (se 1 (by rfl) ⟨2589704, by rfl⟩ : syracuseStep 3452939 = 5179409) B5179409
theorem B1536011 : Blo 1534464 1536011 := bstep (se 1 (by rfl) ⟨1152008, by rfl⟩ : syracuseStep 1536011 = 2304017) B2304017
theorem B1536023 : Blo 1534464 1536023 := bstep (se 1 (by rfl) ⟨1152017, by rfl⟩ : syracuseStep 1536023 = 2304035) B2304035
theorem B1536043 : Blo 1534464 1536043 := bstep (se 1 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 1536043 = 2304065) B2304065
theorem B1536055 : Blo 1534464 1536055 := bstep (se 1 (by rfl) ⟨1152041, by rfl⟩ : syracuseStep 1536055 = 2304083) B2304083
theorem B3452993 : Blo 1534464 3452993 := bstep (se 2 (by rfl) ⟨1294872, by rfl⟩ : syracuseStep 3452993 = 2589745) B2589745
theorem B5181515 : Blo 1534464 5181515 := bstep (se 1 (by rfl) ⟨3886136, by rfl⟩ : syracuseStep 5181515 = 7772273) B7772273
theorem B1536075 : Blo 1534464 1536075 := bstep (se 1 (by rfl) ⟨1152056, by rfl⟩ : syracuseStep 1536075 = 2304113) B2304113
theorem B1536087 : Blo 1534464 1536087 := bstep (se 1 (by rfl) ⟨1152065, by rfl⟩ : syracuseStep 1536087 = 2304131) B2304131
theorem B1536107 : Blo 1534464 1536107 := bstep (se 1 (by rfl) ⟨1152080, by rfl⟩ : syracuseStep 1536107 = 2304161) B2304161
theorem B1536119 : Blo 1534464 1536119 := bstep (se 1 (by rfl) ⟨1152089, by rfl⟩ : syracuseStep 1536119 = 2304179) B2304179
theorem B1536139 : Blo 1534464 1536139 := bstep (se 1 (by rfl) ⟨1152104, by rfl⟩ : syracuseStep 1536139 = 2304209) B2304209
theorem B1536151 : Blo 1534464 1536151 := bstep (se 1 (by rfl) ⟨1152113, by rfl⟩ : syracuseStep 1536151 = 2304227) B2304227
theorem B1536171 : Blo 1534464 1536171 := bstep (se 1 (by rfl) ⟨1152128, by rfl⟩ : syracuseStep 1536171 = 2304257) B2304257
theorem B1536183 : Blo 1534464 1536183 := bstep (se 1 (by rfl) ⟨1152137, by rfl⟩ : syracuseStep 1536183 = 2304275) B2304275
theorem B1536203 : Blo 1534464 1536203 := bstep (se 1 (by rfl) ⟨1152152, by rfl⟩ : syracuseStep 1536203 = 2304305) B2304305
theorem B1536215 : Blo 1534464 1536215 := bstep (se 1 (by rfl) ⟨1152161, by rfl⟩ : syracuseStep 1536215 = 2304323) B2304323
theorem B7770329 : Blo 1534464 7770329 := bstep (se 2 (by rfl) ⟨2913873, by rfl⟩ : syracuseStep 7770329 = 5827747) B5827747
theorem B1536235 : Blo 1534464 1536235 := bstep (se 1 (by rfl) ⟨1152176, by rfl⟩ : syracuseStep 1536235 = 2304353) B2304353
theorem B1536247 : Blo 1534464 1536247 := bstep (se 1 (by rfl) ⟨1152185, by rfl⟩ : syracuseStep 1536247 = 2304371) B2304371
theorem B1536267 : Blo 1534464 1536267 := bstep (se 1 (by rfl) ⟨1152200, by rfl⟩ : syracuseStep 1536267 = 2304401) B2304401
theorem B1536279 : Blo 1534464 1536279 := bstep (se 1 (by rfl) ⟨1152209, by rfl⟩ : syracuseStep 1536279 = 2304419) B2304419
theorem B3453209 : Blo 1534464 3453209 := bstep (se 2 (by rfl) ⟨1294953, by rfl⟩ : syracuseStep 3453209 = 2589907) B2589907
theorem B1536299 : Blo 1534464 1536299 := bstep (se 1 (by rfl) ⟨1152224, by rfl⟩ : syracuseStep 1536299 = 2304449) B2304449
theorem B24899885 : Blo 1534464 24899885 := bstep (se 3 (by rfl) ⟨4668728, by rfl⟩ : syracuseStep 24899885 = 9337457) B9337457
theorem B2953523 : Blo 1534464 2953523 := bstep (se 1 (by rfl) ⟨2215142, by rfl⟩ : syracuseStep 2953523 = 4430285) B4430285
theorem B1536311 : Blo 1534464 1536311 := bstep (se 1 (by rfl) ⟨1152233, by rfl⟩ : syracuseStep 1536311 = 2304467) B2304467
theorem B1536331 : Blo 1534464 1536331 := bstep (se 1 (by rfl) ⟨1152248, by rfl⟩ : syracuseStep 1536331 = 2304497) B2304497
theorem B1536343 : Blo 1534464 1536343 := bstep (se 1 (by rfl) ⟨1152257, by rfl⟩ : syracuseStep 1536343 = 2304515) B2304515
theorem B5181785 : Blo 1534464 5181785 := bstep (se 2 (by rfl) ⟨1943169, by rfl⟩ : syracuseStep 5181785 = 3886339) B3886339
theorem B1536363 : Blo 1534464 1536363 := bstep (se 1 (by rfl) ⟨1152272, by rfl⟩ : syracuseStep 1536363 = 2304545) B2304545
theorem B3453299 : Blo 1534464 3453299 := bstep (se 1 (by rfl) ⟨2589974, by rfl⟩ : syracuseStep 3453299 = 5179949) B5179949
theorem B1536375 : Blo 1534464 1536375 := bstep (se 1 (by rfl) ⟨1152281, by rfl⟩ : syracuseStep 1536375 = 2304563) B2304563
theorem B1536395 : Blo 1534464 1536395 := bstep (se 1 (by rfl) ⟨1152296, by rfl⟩ : syracuseStep 1536395 = 2304593) B2304593
theorem B3453335 : Blo 1534464 3453335 := bstep (se 1 (by rfl) ⟨2590001, by rfl⟩ : syracuseStep 3453335 = 5180003) B5180003
theorem B1536407 : Blo 1534464 1536407 := bstep (se 1 (by rfl) ⟨1152305, by rfl⟩ : syracuseStep 1536407 = 2304611) B2304611
theorem B1536427 : Blo 1534464 1536427 := bstep (se 1 (by rfl) ⟨1152320, by rfl⟩ : syracuseStep 1536427 = 2304641) B2304641
theorem B1536439 : Blo 1534464 1536439 := bstep (se 1 (by rfl) ⟨1152329, by rfl⟩ : syracuseStep 1536439 = 2304659) B2304659
theorem B1536459 : Blo 1534464 1536459 := bstep (se 1 (by rfl) ⟨1152344, by rfl⟩ : syracuseStep 1536459 = 2304689) B2304689
theorem B5534173 : Blo 1534464 5534173 := bstep (se 3 (by rfl) ⟨1037657, by rfl⟩ : syracuseStep 5534173 = 2075315) B2075315
theorem B3453515 : Blo 1534464 3453515 := bstep (se 1 (by rfl) ⟨2590136, by rfl⟩ : syracuseStep 3453515 = 5180273) B5180273
theorem B3453569 : Blo 1534464 3453569 := bstep (se 2 (by rfl) ⟨1295088, by rfl⟩ : syracuseStep 3453569 = 2590177) B2590177
theorem B6222539 : Blo 1534464 6222539 := bstep (se 1 (by rfl) ⟨4666904, by rfl⟩ : syracuseStep 6222539 = 9333809) B9333809
theorem B3453785 : Blo 1534464 3453785 := bstep (se 2 (by rfl) ⟨1295169, by rfl⟩ : syracuseStep 3453785 = 2590339) B2590339
theorem B2913175 : Blo 1534464 2913175 := bstep (se 1 (by rfl) ⟨2184881, by rfl⟩ : syracuseStep 2913175 = 4369763) B4369763
theorem B2765747 : Blo 1534464 2765747 := bstep (se 1 (by rfl) ⟨2074310, by rfl⟩ : syracuseStep 2765747 = 4148621) B4148621
theorem B3453875 : Blo 1534464 3453875 := bstep (se 1 (by rfl) ⟨2590406, by rfl⟩ : syracuseStep 3453875 = 5180813) B5180813
theorem B4371403 : Blo 1534464 4371403 := bstep (se 1 (by rfl) ⟨3278552, by rfl⟩ : syracuseStep 4371403 = 6557105) B6557105
theorem B3453911 : Blo 1534464 3453911 := bstep (se 1 (by rfl) ⟨2590433, by rfl⟩ : syracuseStep 3453911 = 5180867) B5180867
theorem B5182487 : Blo 1534464 5182487 := bstep (se 1 (by rfl) ⟨3886865, by rfl⟩ : syracuseStep 5182487 = 7773731) B7773731
theorem B5829677 : Blo 1534464 5829677 := bstep (se 3 (by rfl) ⟨1093064, by rfl⟩ : syracuseStep 5829677 = 2186129) B2186129
theorem B3454091 : Blo 1534464 3454091 := bstep (se 1 (by rfl) ⟨2590568, by rfl⟩ : syracuseStep 3454091 = 5181137) B5181137
theorem B3454145 : Blo 1534464 3454145 := bstep (se 2 (by rfl) ⟨1295304, by rfl⟩ : syracuseStep 3454145 = 2590609) B2590609
theorem B11662541 : Blo 1534464 11662541 := bstep (se 3 (by rfl) ⟨2186726, by rfl⟩ : syracuseStep 11662541 = 4373453) B4373453
theorem B4371677 : Blo 1534464 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B4265239 : Blo 1534464 4265239 := bstep (se 1 (by rfl) ⟨3198929, by rfl⟩ : syracuseStep 4265239 = 6397859) B6397859
theorem B3454361 : Blo 1534464 3454361 := bstep (se 2 (by rfl) ⟨1295385, by rfl⟩ : syracuseStep 3454361 = 2590771) B2590771
theorem B3888587 : Blo 1534464 3888587 := bstep (se 1 (by rfl) ⟨2916440, by rfl⟩ : syracuseStep 3888587 = 5832881) B5832881
theorem B3454451 : Blo 1534464 3454451 := bstep (se 1 (by rfl) ⟨2590838, by rfl⟩ : syracuseStep 3454451 = 5181677) B5181677
theorem B2766359 : Blo 1534464 2766359 := bstep (se 1 (by rfl) ⟨2074769, by rfl⟩ : syracuseStep 2766359 = 4149539) B4149539
theorem B3454487 : Blo 1534464 3454487 := bstep (se 1 (by rfl) ⟨2590865, by rfl⟩ : syracuseStep 3454487 = 5181731) B5181731
theorem B4372019 : Blo 1534464 4372019 := bstep (se 1 (by rfl) ⟨3279014, by rfl⟩ : syracuseStep 4372019 = 6558029) B6558029
theorem B5183027 : Blo 1534464 5183027 := bstep (se 1 (by rfl) ⟨3887270, by rfl⟩ : syracuseStep 5183027 = 7774541) B7774541
theorem B4920983 : Blo 1534464 4920983 := bstep (se 1 (by rfl) ⟨3690737, by rfl⟩ : syracuseStep 4920983 = 7381475) B7381475
theorem B11663027 : Blo 1534464 11663027 := bstep (se 1 (by rfl) ⟨8747270, by rfl⟩ : syracuseStep 11663027 = 17494541) B17494541
theorem B2913995 : Blo 1534464 2913995 := bstep (se 1 (by rfl) ⟨2185496, by rfl⟩ : syracuseStep 2913995 = 4370993) B4370993
theorem B3454667 : Blo 1534464 3454667 := bstep (se 1 (by rfl) ⟨2591000, by rfl⟩ : syracuseStep 3454667 = 5182001) B5182001
theorem B2914049 : Blo 1534464 2914049 := bstep (se 2 (by rfl) ⟨1092768, by rfl⟩ : syracuseStep 2914049 = 2185537) B2185537
theorem B3454721 : Blo 1534464 3454721 := bstep (se 2 (by rfl) ⟨1295520, by rfl⟩ : syracuseStep 3454721 = 2591041) B2591041
theorem B4151063 : Blo 1534464 4151063 := bstep (se 1 (by rfl) ⟨3113297, by rfl⟩ : syracuseStep 4151063 = 6226595) B6226595
theorem B7771949 : Blo 1534464 7771949 := bstep (se 3 (by rfl) ⟨1457240, by rfl⟩ : syracuseStep 7771949 = 2914481) B2914481
theorem B5830451 : Blo 1534464 5830451 := bstep (se 1 (by rfl) ⟨4372838, by rfl⟩ : syracuseStep 5830451 = 8745677) B8745677
theorem B5183297 : Blo 1534464 5183297 := bstep (se 2 (by rfl) ⟨1943736, by rfl⟩ : syracuseStep 5183297 = 3887473) B3887473
theorem B6559633 : Blo 1534464 6559633 := bstep (se 2 (by rfl) ⟨2459862, by rfl⟩ : syracuseStep 6559633 = 4919725) B4919725
theorem B1726411 : Blo 1534464 1726411 := bstep (se 1 (by rfl) ⟨1294808, by rfl⟩ : syracuseStep 1726411 = 2589617) B2589617
theorem B3454937 : Blo 1534464 3454937 := bstep (se 2 (by rfl) ⟨1295601, by rfl⟩ : syracuseStep 3454937 = 2591203) B2591203
theorem B19666961 : Blo 1534464 19666961 := bstep (se 2 (by rfl) ⟨7375110, by rfl⟩ : syracuseStep 19666961 = 14750221) B14750221
theorem B3455027 : Blo 1534464 3455027 := bstep (se 1 (by rfl) ⟨2591270, by rfl⟩ : syracuseStep 3455027 = 5182541) B5182541
theorem B1726519 : Blo 1534464 1726519 := bstep (se 1 (by rfl) ⟨1294889, by rfl⟩ : syracuseStep 1726519 = 2589779) B2589779
theorem B3110987 : Blo 1534464 3110987 := bstep (se 1 (by rfl) ⟨2333240, by rfl⟩ : syracuseStep 3110987 = 4666481) B4666481
theorem B3455063 : Blo 1534464 3455063 := bstep (se 1 (by rfl) ⟨2591297, by rfl⟩ : syracuseStep 3455063 = 5182595) B5182595
theorem B2767051 : Blo 1534464 2767051 := bstep (se 1 (by rfl) ⟨2075288, by rfl⟩ : syracuseStep 2767051 = 4150577) B4150577
theorem B5535947 : Blo 1534464 5535947 := bstep (se 1 (by rfl) ⟨4151960, by rfl⟩ : syracuseStep 5535947 = 8303921) B8303921
theorem B9836761 : Blo 1534464 9836761 := bstep (se 2 (by rfl) ⟨3688785, by rfl⟩ : syracuseStep 9836761 = 7377571) B7377571
theorem B1726699 : Blo 1534464 1726699 := bstep (se 1 (by rfl) ⟨1295024, by rfl⟩ : syracuseStep 1726699 = 2590049) B2590049
theorem B3455243 : Blo 1534464 3455243 := bstep (se 1 (by rfl) ⟨2591432, by rfl⟩ : syracuseStep 3455243 = 5182865) B5182865
theorem B7878977 : Blo 1534464 7878977 := bstep (se 2 (by rfl) ⟨2954616, by rfl⟩ : syracuseStep 7878977 = 5909233) B5909233
theorem B3455297 : Blo 1534464 3455297 := bstep (se 2 (by rfl) ⟨1295736, by rfl⟩ : syracuseStep 3455297 = 2591473) B2591473
theorem B1726807 : Blo 1534464 1726807 := bstep (se 1 (by rfl) ⟨1295105, by rfl⟩ : syracuseStep 1726807 = 2590211) B2590211
theorem B5183837 : Blo 1534464 5183837 := bstep (se 3 (by rfl) ⟨971969, by rfl⟩ : syracuseStep 5183837 = 1943939) B1943939
theorem B1751467 : Blo 1534464 1751467 := bstep (se 1 (by rfl) ⟨1313600, by rfl⟩ : syracuseStep 1751467 = 2627201) B2627201
theorem B7379417 : Blo 1534464 7379417 := bstep (se 2 (by rfl) ⟨2767281, by rfl⟩ : syracuseStep 7379417 = 5534563) B5534563
theorem B1726987 : Blo 1534464 1726987 := bstep (se 1 (by rfl) ⟨1295240, by rfl⟩ : syracuseStep 1726987 = 2590481) B2590481
theorem B3455513 : Blo 1534464 3455513 := bstep (se 2 (by rfl) ⟨1295817, by rfl⟩ : syracuseStep 3455513 = 2591635) B2591635
theorem B12622429 : Blo 1534464 12622429 := bstep (se 3 (by rfl) ⟨2366705, by rfl⟩ : syracuseStep 12622429 = 4733411) B4733411
theorem B3455603 : Blo 1534464 3455603 := bstep (se 1 (by rfl) ⟨2591702, by rfl⟩ : syracuseStep 3455603 = 5183405) B5183405
theorem B1727095 : Blo 1534464 1727095 := bstep (se 1 (by rfl) ⟨1295321, by rfl⟩ : syracuseStep 1727095 = 2590643) B2590643
theorem B2914967 : Blo 1534464 2914967 := bstep (se 1 (by rfl) ⟨2186225, by rfl⟩ : syracuseStep 2914967 = 4372451) B4372451
theorem B3455639 : Blo 1534464 3455639 := bstep (se 1 (by rfl) ⟨2591729, by rfl⟩ : syracuseStep 3455639 = 5183459) B5183459
theorem B3111577 : Blo 1534464 3111577 := bstep (se 2 (by rfl) ⟨1166841, by rfl⟩ : syracuseStep 3111577 = 2333683) B2333683
theorem B50502341 : Blo 1534464 50502341 := bstep (se 4 (by rfl) ⟨4734594, by rfl⟩ : syracuseStep 50502341 = 9469189) B9469189
theorem B28007117 : Blo 1534464 28007117 := bstep (se 3 (by rfl) ⟨5251334, by rfl⟩ : syracuseStep 28007117 = 10502669) B10502669
theorem B11066129 : Blo 1534464 11066129 := bstep (se 2 (by rfl) ⟨4149798, by rfl⟩ : syracuseStep 11066129 = 8299597) B8299597
theorem B2333465 : Blo 1534464 2333465 := bstep (se 2 (by rfl) ⟨875049, by rfl⟩ : syracuseStep 2333465 = 1750099) B1750099
theorem B1727275 : Blo 1534464 1727275 := bstep (se 1 (by rfl) ⟨1295456, by rfl⟩ : syracuseStep 1727275 = 2590913) B2590913
theorem B3455819 : Blo 1534464 3455819 := bstep (se 1 (by rfl) ⟨2591864, by rfl⟩ : syracuseStep 3455819 = 5183729) B5183729
theorem B3455873 : Blo 1534464 3455873 := bstep (se 2 (by rfl) ⟨1295952, by rfl⟩ : syracuseStep 3455873 = 2591905) B2591905
theorem B1727383 : Blo 1534464 1727383 := bstep (se 1 (by rfl) ⟨1295537, by rfl⟩ : syracuseStep 1727383 = 2591075) B2591075
theorem B5610541 : Blo 1534464 5610541 := bstep (se 3 (by rfl) ⟨1051976, by rfl⟩ : syracuseStep 5610541 = 2103953) B2103953
theorem B1727563 : Blo 1534464 1727563 := bstep (se 1 (by rfl) ⟨1295672, by rfl⟩ : syracuseStep 1727563 = 2591345) B2591345
theorem B3456089 : Blo 1534464 3456089 := bstep (se 2 (by rfl) ⟨1296033, by rfl⟩ : syracuseStep 3456089 = 2592067) B2592067
theorem B11664485 : Blo 1534464 11664485 := bstep (se 4 (by rfl) ⟨1093545, by rfl⟩ : syracuseStep 11664485 = 2187091) B2187091
theorem B2915507 : Blo 1534464 2915507 := bstep (se 1 (by rfl) ⟨2186630, by rfl⟩ : syracuseStep 2915507 = 4373261) B4373261
theorem B3456179 : Blo 1534464 3456179 := bstep (se 1 (by rfl) ⟨2592134, by rfl⟩ : syracuseStep 3456179 = 5184269) B5184269
theorem B1727671 : Blo 1534464 1727671 := bstep (se 1 (by rfl) ⟨1295753, by rfl⟩ : syracuseStep 1727671 = 2591507) B2591507
theorem B3456215 : Blo 1534464 3456215 := bstep (se 1 (by rfl) ⟨2592161, by rfl⟩ : syracuseStep 3456215 = 5184323) B5184323
theorem B2768089 : Blo 1534464 2768089 := bstep (se 2 (by rfl) ⟨1038033, by rfl⟩ : syracuseStep 2768089 = 2076067) B2076067
theorem B5831939 : Blo 1534464 5831939 := bstep (se 1 (by rfl) ⟨4373954, by rfl⟩ : syracuseStep 5831939 = 8747909) B8747909
theorem B1727851 : Blo 1534464 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B3456395 : Blo 1534464 3456395 := bstep (se 1 (by rfl) ⟨2592296, by rfl⟩ : syracuseStep 3456395 = 5184593) B5184593
theorem B3456449 : Blo 1534464 3456449 := bstep (se 2 (by rfl) ⟨1296168, by rfl⟩ : syracuseStep 3456449 = 2592337) B2592337
theorem B5184971 : Blo 1534464 5184971 := bstep (se 1 (by rfl) ⟨3888728, by rfl⟩ : syracuseStep 5184971 = 7777457) B7777457
theorem B1727959 : Blo 1534464 1727959 := bstep (se 1 (by rfl) ⟨1295969, by rfl⟩ : syracuseStep 1727959 = 2591939) B2591939
theorem B11656709 : Blo 1534464 11656709 := bstep (se 4 (by rfl) ⟨1092816, by rfl⟩ : syracuseStep 11656709 = 2185633) B2185633
theorem B2768435 : Blo 1534464 2768435 := bstep (se 1 (by rfl) ⟨2076326, by rfl⟩ : syracuseStep 2768435 = 4152653) B4152653
theorem B4374091 : Blo 1534464 4374091 := bstep (se 1 (by rfl) ⟨3280568, by rfl⟩ : syracuseStep 4374091 = 6561137) B6561137
theorem B11664971 : Blo 1534464 11664971 := bstep (se 1 (by rfl) ⟨8748728, by rfl⟩ : syracuseStep 11664971 = 17497457) B17497457
theorem B14753411 : Blo 1534464 14753411 := bstep (se 1 (by rfl) ⟨11065058, by rfl⟩ : syracuseStep 14753411 = 22130117) B22130117
theorem B1728139 : Blo 1534464 1728139 := bstep (se 1 (by rfl) ⟨1296104, by rfl⟩ : syracuseStep 1728139 = 2592209) B2592209
theorem B2915993 : Blo 1534464 2915993 := bstep (se 2 (by rfl) ⟨1093497, by rfl⟩ : syracuseStep 2915993 = 2186995) B2186995
theorem B3456665 : Blo 1534464 3456665 := bstep (se 2 (by rfl) ⟨1296249, by rfl⟩ : syracuseStep 3456665 = 2592499) B2592499
theorem B13295281 : Blo 1534464 13295281 := bstep (se 2 (by rfl) ⟨4985730, by rfl⟩ : syracuseStep 13295281 = 9971461) B9971461
theorem B5537459 : Blo 1534464 5537459 := bstep (se 1 (by rfl) ⟨4153094, by rfl⟩ : syracuseStep 5537459 = 8306189) B8306189
theorem B5832395 : Blo 1534464 5832395 := bstep (se 1 (by rfl) ⟨4374296, by rfl⟩ : syracuseStep 5832395 = 8748593) B8748593
theorem B5185241 : Blo 1534464 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B3456755 : Blo 1534464 3456755 := bstep (se 1 (by rfl) ⟨2592566, by rfl⟩ : syracuseStep 3456755 = 5185133) B5185133
theorem B1728247 : Blo 1534464 1728247 := bstep (se 1 (by rfl) ⟨1296185, by rfl⟩ : syracuseStep 1728247 = 2592371) B2592371
theorem B2301707 : Blo 1534464 2301707 := bstep (se 1 (by rfl) ⟨1726280, by rfl⟩ : syracuseStep 2301707 = 3452561) B3452561
theorem B2301719 : Blo 1534464 2301719 := bstep (se 1 (by rfl) ⟨1726289, by rfl⟩ : syracuseStep 2301719 = 3452579) B3452579
theorem B3456791 : Blo 1534464 3456791 := bstep (se 1 (by rfl) ⟨2592593, by rfl⟩ : syracuseStep 3456791 = 5185187) B5185187
theorem B2301785 : Blo 1534464 2301785 := bstep (se 2 (by rfl) ⟨863169, by rfl⟩ : syracuseStep 2301785 = 1726339) B1726339
theorem B3112843 : Blo 1534464 3112843 := bstep (se 1 (by rfl) ⟨2334632, by rfl⟩ : syracuseStep 3112843 = 4669265) B4669265
theorem B5832593 : Blo 1534464 5832593 := bstep (se 2 (by rfl) ⟨2187222, by rfl⟩ : syracuseStep 5832593 = 4374445) B4374445
theorem B1728427 : Blo 1534464 1728427 := bstep (se 1 (by rfl) ⟨1296320, by rfl⟩ : syracuseStep 1728427 = 2592641) B2592641
theorem B2301899 : Blo 1534464 2301899 := bstep (se 1 (by rfl) ⟨1726424, by rfl⟩ : syracuseStep 2301899 = 3452849) B3452849
theorem B3456971 : Blo 1534464 3456971 := bstep (se 1 (by rfl) ⟨2592728, by rfl⟩ : syracuseStep 3456971 = 5185457) B5185457
theorem B2301911 : Blo 1534464 2301911 := bstep (se 1 (by rfl) ⟨1726433, by rfl⟩ : syracuseStep 2301911 = 3452867) B3452867
theorem B2301959 : Blo 1534464 2301959 := bstep (se 1 (by rfl) ⟨1726469, by rfl⟩ : syracuseStep 2301959 = 3452939) B3452939
theorem B5185565 : Blo 1534464 5185565 := bstep (se 3 (by rfl) ⟨972293, by rfl⟩ : syracuseStep 5185565 = 1944587) B1944587
theorem B2301995 : Blo 1534464 2301995 := bstep (se 1 (by rfl) ⟨1726496, by rfl⟩ : syracuseStep 2301995 = 3452993) B3452993
theorem B2916395 : Blo 1534464 2916395 := bstep (se 1 (by rfl) ⟨2187296, by rfl⟩ : syracuseStep 2916395 = 4374593) B4374593
theorem B2302025 : Blo 1534464 2302025 := bstep (se 2 (by rfl) ⟨863259, by rfl⟩ : syracuseStep 2302025 = 1726519) B1726519
theorem B4735091 : Blo 1534464 4735091 := bstep (se 1 (by rfl) ⟨3551318, by rfl⟩ : syracuseStep 4735091 = 7102637) B7102637
theorem B2302139 : Blo 1534464 2302139 := bstep (se 1 (by rfl) ⟨1726604, by rfl⟩ : syracuseStep 2302139 = 3453209) B3453209
theorem B2302199 : Blo 1534464 2302199 := bstep (se 1 (by rfl) ⟨1726649, by rfl⟩ : syracuseStep 2302199 = 3453299) B3453299
theorem B2302223 : Blo 1534464 2302223 := bstep (se 1 (by rfl) ⟨1726667, by rfl⟩ : syracuseStep 2302223 = 3453335) B3453335
theorem B2916623 : Blo 1534464 2916623 := bstep (se 1 (by rfl) ⟨2187467, by rfl⟩ : syracuseStep 2916623 = 4374935) B4374935
theorem B13115681 : Blo 1534464 13115681 := bstep (se 2 (by rfl) ⟨4918380, by rfl⟩ : syracuseStep 13115681 = 9836761) B9836761
theorem B2302265 : Blo 1534464 2302265 := bstep (se 2 (by rfl) ⟨863349, by rfl⟩ : syracuseStep 2302265 = 1726699) B1726699
theorem B2302343 : Blo 1534464 2302343 := bstep (se 1 (by rfl) ⟨1726757, by rfl⟩ : syracuseStep 2302343 = 3453515) B3453515
theorem B2302379 : Blo 1534464 2302379 := bstep (se 1 (by rfl) ⟨1726784, by rfl⟩ : syracuseStep 2302379 = 3453569) B3453569
theorem B2302409 : Blo 1534464 2302409 := bstep (se 2 (by rfl) ⟨863403, by rfl⟩ : syracuseStep 2302409 = 1726807) B1726807
theorem B11657681 : Blo 1534464 11657681 := bstep (se 2 (by rfl) ⟨4371630, by rfl⟩ : syracuseStep 11657681 = 8743261) B8743261
theorem B2335289 : Blo 1534464 2335289 := bstep (se 2 (by rfl) ⟨875733, by rfl⟩ : syracuseStep 2335289 = 1751467) B1751467
theorem B2458171 : Blo 1534464 2458171 := bstep (se 1 (by rfl) ⟨1843628, by rfl⟩ : syracuseStep 2458171 = 3687257) B3687257
theorem B2302523 : Blo 1534464 2302523 := bstep (se 1 (by rfl) ⟨1726892, by rfl⟩ : syracuseStep 2302523 = 3453785) B3453785
theorem B1843831 : Blo 1534464 1843831 := bstep (se 1 (by rfl) ⟨1382873, by rfl⟩ : syracuseStep 1843831 = 2765747) B2765747
theorem B2302583 : Blo 1534464 2302583 := bstep (se 1 (by rfl) ⟨1726937, by rfl⟩ : syracuseStep 2302583 = 3453875) B3453875
theorem B1557127 : Blo 1534464 1557127 := bstep (se 1 (by rfl) ⟨1167845, by rfl⟩ : syracuseStep 1557127 = 2335691) B2335691
theorem B2302607 : Blo 1534464 2302607 := bstep (se 1 (by rfl) ⟨1726955, by rfl⟩ : syracuseStep 2302607 = 3453911) B3453911
theorem B3277459 : Blo 1534464 3277459 := bstep (se 1 (by rfl) ⟨2458094, by rfl⟩ : syracuseStep 3277459 = 4916189) B4916189
theorem B2302649 : Blo 1534464 2302649 := bstep (se 2 (by rfl) ⟨863493, by rfl⟩ : syracuseStep 2302649 = 1726987) B1726987
theorem B2302727 : Blo 1534464 2302727 := bstep (se 1 (by rfl) ⟨1727045, by rfl⟩ : syracuseStep 2302727 = 3454091) B3454091
theorem B2589455 : Blo 1534464 2589455 := bstep (se 1 (by rfl) ⟨1942091, by rfl⟩ : syracuseStep 2589455 = 3884183) B3884183
theorem B17498915 : Blo 1534464 17498915 := bstep (se 1 (by rfl) ⟨13124186, by rfl⟩ : syracuseStep 17498915 = 26248373) B26248373
theorem B2302763 : Blo 1534464 2302763 := bstep (se 1 (by rfl) ⟨1727072, by rfl⟩ : syracuseStep 2302763 = 3454145) B3454145
theorem B7775027 : Blo 1534464 7775027 := bstep (se 1 (by rfl) ⟨5831270, by rfl⟩ : syracuseStep 7775027 = 11662541) B11662541
theorem B2302793 : Blo 1534464 2302793 := bstep (se 2 (by rfl) ⟨863547, by rfl⟩ : syracuseStep 2302793 = 1727095) B1727095
theorem B2302907 : Blo 1534464 2302907 := bstep (se 1 (by rfl) ⟨1727180, by rfl⟩ : syracuseStep 2302907 = 3454361) B3454361
theorem B2302967 : Blo 1534464 2302967 := bstep (se 1 (by rfl) ⟨1727225, by rfl⟩ : syracuseStep 2302967 = 3454451) B3454451
theorem B2302991 : Blo 1534464 2302991 := bstep (se 1 (by rfl) ⟨1727243, by rfl⟩ : syracuseStep 2302991 = 3454487) B3454487
theorem B2303033 : Blo 1534464 2303033 := bstep (se 2 (by rfl) ⟨863637, by rfl⟩ : syracuseStep 2303033 = 1727275) B1727275
theorem B7775351 : Blo 1534464 7775351 := bstep (se 1 (by rfl) ⟨5831513, by rfl⟩ : syracuseStep 7775351 = 11663027) B11663027
theorem B2303111 : Blo 1534464 2303111 := bstep (se 1 (by rfl) ⟨1727333, by rfl⟩ : syracuseStep 2303111 = 3454667) B3454667
theorem B1942699 : Blo 1534464 1942699 := bstep (se 1 (by rfl) ⟨1457024, by rfl⟩ : syracuseStep 1942699 = 2914049) B2914049
theorem B2303147 : Blo 1534464 2303147 := bstep (se 1 (by rfl) ⟨1727360, by rfl⟩ : syracuseStep 2303147 = 3454721) B3454721
theorem B3884233 : Blo 1534464 3884233 := bstep (se 2 (by rfl) ⟨1456587, by rfl⟩ : syracuseStep 3884233 = 2913175) B2913175
theorem B2303177 : Blo 1534464 2303177 := bstep (se 2 (by rfl) ⟨863691, by rfl⟩ : syracuseStep 2303177 = 1727383) B1727383
theorem B8750369 : Blo 1534464 8750369 := bstep (se 2 (by rfl) ⟨3281388, by rfl⟩ : syracuseStep 8750369 = 6562777) B6562777
theorem B2589995 : Blo 1534464 2589995 := bstep (se 1 (by rfl) ⟨1942496, by rfl⟩ : syracuseStep 2589995 = 3884993) B3884993
theorem B2303291 : Blo 1534464 2303291 := bstep (se 1 (by rfl) ⟨1727468, by rfl⟩ : syracuseStep 2303291 = 3454937) B3454937
theorem B3884375 : Blo 1534464 3884375 := bstep (se 1 (by rfl) ⟨2913281, by rfl⟩ : syracuseStep 3884375 = 5826563) B5826563
theorem B2303351 : Blo 1534464 2303351 := bstep (se 1 (by rfl) ⟨1727513, by rfl⟩ : syracuseStep 2303351 = 3455027) B3455027
theorem B2303375 : Blo 1534464 2303375 := bstep (se 1 (by rfl) ⟨1727531, by rfl⟩ : syracuseStep 2303375 = 3455063) B3455063
theorem B1639823 : Blo 1534464 1639823 := bstep (se 1 (by rfl) ⟨1229867, by rfl⟩ : syracuseStep 1639823 = 2459735) B2459735
theorem B7480721 : Blo 1534464 7480721 := bstep (se 2 (by rfl) ⟨2805270, by rfl⟩ : syracuseStep 7480721 = 5610541) B5610541
theorem B11986321 : Blo 1534464 11986321 := bstep (se 2 (by rfl) ⟨4494870, by rfl⟩ : syracuseStep 11986321 = 8989741) B8989741
theorem B8742329 : Blo 1534464 8742329 := bstep (se 2 (by rfl) ⟨3278373, by rfl⟩ : syracuseStep 8742329 = 6556747) B6556747
theorem B2303417 : Blo 1534464 2303417 := bstep (se 2 (by rfl) ⟨863781, by rfl⟩ : syracuseStep 2303417 = 1727563) B1727563
theorem B2303495 : Blo 1534464 2303495 := bstep (se 1 (by rfl) ⟨1727621, by rfl⟩ : syracuseStep 2303495 = 3455243) B3455243
theorem B7374359 : Blo 1534464 7374359 := bstep (se 1 (by rfl) ⟨5530769, by rfl⟩ : syracuseStep 7374359 = 11061539) B11061539
theorem B5178923 : Blo 1534464 5178923 := bstep (se 1 (by rfl) ⟨3884192, by rfl⟩ : syracuseStep 5178923 = 7768385) B7768385
theorem B5252651 : Blo 1534464 5252651 := bstep (se 1 (by rfl) ⟨3939488, by rfl⟩ : syracuseStep 5252651 = 7878977) B7878977
theorem B2303531 : Blo 1534464 2303531 := bstep (se 1 (by rfl) ⟨1727648, by rfl⟩ : syracuseStep 2303531 = 3455297) B3455297
theorem B68257349 : Blo 1534464 68257349 := bstep (se 4 (by rfl) ⟨6399126, by rfl⟩ : syracuseStep 68257349 = 12798253) B12798253
theorem B2303561 : Blo 1534464 2303561 := bstep (se 2 (by rfl) ⟨863835, by rfl⟩ : syracuseStep 2303561 = 1727671) B1727671
theorem B4916855 : Blo 1534464 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B2590393 : Blo 1534464 2590393 := bstep (se 2 (by rfl) ⟨971397, by rfl⟩ : syracuseStep 2590393 = 1942795) B1942795
theorem B2303675 : Blo 1534464 2303675 := bstep (se 1 (by rfl) ⟨1727756, by rfl⟩ : syracuseStep 2303675 = 3455513) B3455513
theorem B5686985 : Blo 1534464 5686985 := bstep (se 2 (by rfl) ⟨2132619, by rfl⟩ : syracuseStep 5686985 = 4265239) B4265239
theorem B2303735 : Blo 1534464 2303735 := bstep (se 1 (by rfl) ⟨1727801, by rfl⟩ : syracuseStep 2303735 = 3455603) B3455603
theorem B2303759 : Blo 1534464 2303759 := bstep (se 1 (by rfl) ⟨1727819, by rfl⟩ : syracuseStep 2303759 = 3455639) B3455639
theorem B18671411 : Blo 1534464 18671411 := bstep (se 1 (by rfl) ⟨14003558, by rfl⟩ : syracuseStep 18671411 = 28007117) B28007117
theorem B2303801 : Blo 1534464 2303801 := bstep (se 2 (by rfl) ⟨863925, by rfl⟩ : syracuseStep 2303801 = 1727851) B1727851
theorem B2303879 : Blo 1534464 2303879 := bstep (se 1 (by rfl) ⟨1727909, by rfl⟩ : syracuseStep 2303879 = 3455819) B3455819
theorem B2303915 : Blo 1534464 2303915 := bstep (se 1 (by rfl) ⟨1727936, by rfl⟩ : syracuseStep 2303915 = 3455873) B3455873
theorem B2303945 : Blo 1534464 2303945 := bstep (se 2 (by rfl) ⟨863979, by rfl⟩ : syracuseStep 2303945 = 1727959) B1727959
theorem B1640455 : Blo 1534464 1640455 := bstep (se 1 (by rfl) ⟨1230341, by rfl⟩ : syracuseStep 1640455 = 2460683) B2460683
theorem B3688507 : Blo 1534464 3688507 := bstep (se 1 (by rfl) ⟨2766380, by rfl⟩ : syracuseStep 3688507 = 5532761) B5532761
theorem B2304059 : Blo 1534464 2304059 := bstep (se 1 (by rfl) ⟨1728044, by rfl⟩ : syracuseStep 2304059 = 3456089) B3456089
theorem B7776323 : Blo 1534464 7776323 := bstep (se 1 (by rfl) ⟨5832242, by rfl⟩ : syracuseStep 7776323 = 11664485) B11664485
theorem B1943671 : Blo 1534464 1943671 := bstep (se 1 (by rfl) ⟨1457753, by rfl⟩ : syracuseStep 1943671 = 2915507) B2915507
theorem B2304119 : Blo 1534464 2304119 := bstep (se 1 (by rfl) ⟨1728089, by rfl⟩ : syracuseStep 2304119 = 3456179) B3456179
theorem B2304143 : Blo 1534464 2304143 := bstep (se 1 (by rfl) ⟨1728107, by rfl⟩ : syracuseStep 2304143 = 3456215) B3456215
theorem B2304185 : Blo 1534464 2304185 := bstep (se 2 (by rfl) ⟨864069, by rfl⟩ : syracuseStep 2304185 = 1728139) B1728139
theorem B5826761 : Blo 1534464 5826761 := bstep (se 2 (by rfl) ⟨2185035, by rfl⟩ : syracuseStep 5826761 = 4370071) B4370071
theorem B2304263 : Blo 1534464 2304263 := bstep (se 1 (by rfl) ⟨1728197, by rfl⟩ : syracuseStep 2304263 = 3456395) B3456395
theorem B11069729 : Blo 1534464 11069729 := bstep (se 2 (by rfl) ⟨4151148, by rfl⟩ : syracuseStep 11069729 = 8302297) B8302297
theorem B2304299 : Blo 1534464 2304299 := bstep (se 1 (by rfl) ⟨1728224, by rfl⟩ : syracuseStep 2304299 = 3456449) B3456449
theorem B2304329 : Blo 1534464 2304329 := bstep (se 2 (by rfl) ⟨864123, by rfl⟩ : syracuseStep 2304329 = 1728247) B1728247
theorem B2591095 : Blo 1534464 2591095 := bstep (se 1 (by rfl) ⟨1943321, by rfl⟩ : syracuseStep 2591095 = 3886643) B3886643
theorem B1845623 : Blo 1534464 1845623 := bstep (se 1 (by rfl) ⟨1384217, by rfl⟩ : syracuseStep 1845623 = 2768435) B2768435
theorem B7776647 : Blo 1534464 7776647 := bstep (se 1 (by rfl) ⟨5832485, by rfl⟩ : syracuseStep 7776647 = 11664971) B11664971
theorem B9832889 : Blo 1534464 9832889 := bstep (se 2 (by rfl) ⟨3687333, by rfl⟩ : syracuseStep 9832889 = 7374667) B7374667
theorem B1943995 : Blo 1534464 1943995 := bstep (se 1 (by rfl) ⟨1457996, by rfl⟩ : syracuseStep 1943995 = 2915993) B2915993
theorem B2304443 : Blo 1534464 2304443 := bstep (se 1 (by rfl) ⟨1728332, by rfl⟩ : syracuseStep 2304443 = 3456665) B3456665
theorem B3279305 : Blo 1534464 3279305 := bstep (se 2 (by rfl) ⟨1229739, by rfl⟩ : syracuseStep 3279305 = 2459479) B2459479
theorem B2304503 : Blo 1534464 2304503 := bstep (se 1 (by rfl) ⟨1728377, by rfl⟩ : syracuseStep 2304503 = 3456755) B3456755
theorem B1534471 : Blo 1534464 1534471 := bstep (se 1 (by rfl) ⟨1150853, by rfl⟩ : syracuseStep 1534471 = 2301707) B2301707
theorem B1534479 : Blo 1534464 1534479 := bstep (se 1 (by rfl) ⟨1150859, by rfl⟩ : syracuseStep 1534479 = 2301719) B2301719
theorem B2304527 : Blo 1534464 2304527 := bstep (se 1 (by rfl) ⟨1728395, by rfl⟩ : syracuseStep 2304527 = 3456791) B3456791
theorem B2304569 : Blo 1534464 2304569 := bstep (se 2 (by rfl) ⟨864213, by rfl⟩ : syracuseStep 2304569 = 1728427) B1728427
theorem B1534523 : Blo 1534464 1534523 := bstep (se 1 (by rfl) ⟨1150892, by rfl⟩ : syracuseStep 1534523 = 2301785) B2301785
theorem B2591291 : Blo 1534464 2591291 := bstep (se 1 (by rfl) ⟨1943468, by rfl⟩ : syracuseStep 2591291 = 3886937) B3886937
theorem B5327479 : Blo 1534464 5327479 := bstep (se 1 (by rfl) ⟨3995609, by rfl⟩ : syracuseStep 5327479 = 7991219) B7991219
theorem B1534599 : Blo 1534464 1534599 := bstep (se 1 (by rfl) ⟨1150949, by rfl⟩ : syracuseStep 1534599 = 2301899) B2301899
theorem B2304647 : Blo 1534464 2304647 := bstep (se 1 (by rfl) ⟨1728485, by rfl⟩ : syracuseStep 2304647 = 3456971) B3456971
theorem B1534607 : Blo 1534464 1534607 := bstep (se 1 (by rfl) ⟨1150955, by rfl⟩ : syracuseStep 1534607 = 2301911) B2301911
theorem B2304683 : Blo 1534464 2304683 := bstep (se 1 (by rfl) ⟨1728512, by rfl⟩ : syracuseStep 2304683 = 3457025) B3457025
theorem B1534651 : Blo 1534464 1534651 := bstep (se 1 (by rfl) ⟨1150988, by rfl⟩ : syracuseStep 1534651 = 2301977) B2301977
theorem B6228737 : Blo 1534464 6228737 := bstep (se 2 (by rfl) ⟨2335776, by rfl⟩ : syracuseStep 6228737 = 4671553) B4671553
theorem B1534727 : Blo 1534464 1534727 := bstep (se 1 (by rfl) ⟨1151045, by rfl⟩ : syracuseStep 1534727 = 2302091) B2302091
theorem B1534735 : Blo 1534464 1534735 := bstep (se 1 (by rfl) ⟨1151051, by rfl⟩ : syracuseStep 1534735 = 2302103) B2302103
theorem B31591205 : Blo 1534464 31591205 := bstep (se 4 (by rfl) ⟨2961675, by rfl⟩ : syracuseStep 31591205 = 5923351) B5923351
theorem B1534779 : Blo 1534464 1534779 := bstep (se 1 (by rfl) ⟨1151084, by rfl⟩ : syracuseStep 1534779 = 2302169) B2302169
theorem B5180219 : Blo 1534464 5180219 := bstep (se 1 (by rfl) ⟨3885164, by rfl⟩ : syracuseStep 5180219 = 7770329) B7770329
theorem B16599923 : Blo 1534464 16599923 := bstep (se 1 (by rfl) ⟨12449942, by rfl⟩ : syracuseStep 16599923 = 24899885) B24899885
theorem B1534855 : Blo 1534464 1534855 := bstep (se 1 (by rfl) ⟨1151141, by rfl⟩ : syracuseStep 1534855 = 2302283) B2302283
theorem B1534863 : Blo 1534464 1534863 := bstep (se 1 (by rfl) ⟨1151147, by rfl⟩ : syracuseStep 1534863 = 2302295) B2302295
theorem B3689401 : Blo 1534464 3689401 := bstep (se 2 (by rfl) ⟨1383525, by rfl⟩ : syracuseStep 3689401 = 2767051) B2767051
theorem B1534907 : Blo 1534464 1534907 := bstep (se 1 (by rfl) ⟨1151180, by rfl⟩ : syracuseStep 1534907 = 2302361) B2302361
theorem B2591689 : Blo 1534464 2591689 := bstep (se 2 (by rfl) ⟨971883, by rfl⟩ : syracuseStep 2591689 = 1943767) B1943767
theorem B1534983 : Blo 1534464 1534983 := bstep (se 1 (by rfl) ⟨1151237, by rfl⟩ : syracuseStep 1534983 = 2302475) B2302475
theorem B1534991 : Blo 1534464 1534991 := bstep (se 1 (by rfl) ⟨1151243, by rfl⟩ : syracuseStep 1534991 = 2302487) B2302487
theorem B1535035 : Blo 1534464 1535035 := bstep (se 1 (by rfl) ⟨1151276, by rfl⟩ : syracuseStep 1535035 = 2302553) B2302553
theorem B25578629 : Blo 1534464 25578629 := bstep (se 4 (by rfl) ⟨2397996, by rfl⟩ : syracuseStep 25578629 = 4795993) B4795993
theorem B1535111 : Blo 1534464 1535111 := bstep (se 1 (by rfl) ⟨1151333, by rfl⟩ : syracuseStep 1535111 = 2302667) B2302667
theorem B1535119 : Blo 1534464 1535119 := bstep (se 1 (by rfl) ⟨1151339, by rfl⟩ : syracuseStep 1535119 = 2302679) B2302679
theorem B1535163 : Blo 1534464 1535163 := bstep (se 1 (by rfl) ⟨1151372, by rfl⟩ : syracuseStep 1535163 = 2302745) B2302745
theorem B7376129 : Blo 1534464 7376129 := bstep (se 2 (by rfl) ⟨2766048, by rfl⟩ : syracuseStep 7376129 = 5532097) B5532097
theorem B1535239 : Blo 1534464 1535239 := bstep (se 1 (by rfl) ⟨1151429, by rfl⟩ : syracuseStep 1535239 = 2302859) B2302859
theorem B1535247 : Blo 1534464 1535247 := bstep (se 1 (by rfl) ⟨1151435, by rfl⟩ : syracuseStep 1535247 = 2302871) B2302871
theorem B5180705 : Blo 1534464 5180705 := bstep (se 2 (by rfl) ⟨1942764, by rfl⟩ : syracuseStep 5180705 = 3885529) B3885529
theorem B1535291 : Blo 1534464 1535291 := bstep (se 1 (by rfl) ⟨1151468, by rfl⟩ : syracuseStep 1535291 = 2302937) B2302937
theorem B33221987 : Blo 1534464 33221987 := bstep (se 1 (by rfl) ⟨24916490, by rfl⟩ : syracuseStep 33221987 = 49832981) B49832981
theorem B3886451 : Blo 1534464 3886451 := bstep (se 1 (by rfl) ⟨2914838, by rfl⟩ : syracuseStep 3886451 = 5829677) B5829677
theorem B1535367 : Blo 1534464 1535367 := bstep (se 1 (by rfl) ⟨1151525, by rfl⟩ : syracuseStep 1535367 = 2303051) B2303051
theorem B1535375 : Blo 1534464 1535375 := bstep (se 1 (by rfl) ⟨1151531, by rfl⟩ : syracuseStep 1535375 = 2303063) B2303063
theorem B3280313 : Blo 1534464 3280313 := bstep (se 2 (by rfl) ⟨1230117, by rfl⟩ : syracuseStep 3280313 = 2460235) B2460235
theorem B1535419 : Blo 1534464 1535419 := bstep (se 1 (by rfl) ⟨1151564, by rfl⟩ : syracuseStep 1535419 = 2303129) B2303129
theorem B2993609 : Blo 1534464 2993609 := bstep (se 2 (by rfl) ⟨1122603, by rfl⟩ : syracuseStep 2993609 = 2245207) B2245207
theorem B14757329 : Blo 1534464 14757329 := bstep (se 2 (by rfl) ⟨5533998, by rfl⟩ : syracuseStep 14757329 = 11067997) B11067997
theorem B16829905 : Blo 1534464 16829905 := bstep (se 2 (by rfl) ⟨6311214, by rfl⟩ : syracuseStep 16829905 = 12622429) B12622429
theorem B7876061 : Blo 1534464 7876061 := bstep (se 3 (by rfl) ⟨1476761, by rfl⟩ : syracuseStep 7876061 = 2953523) B2953523
theorem B1535495 : Blo 1534464 1535495 := bstep (se 1 (by rfl) ⟨1151621, by rfl⟩ : syracuseStep 1535495 = 2303243) B2303243
theorem B1535503 : Blo 1534464 1535503 := bstep (se 1 (by rfl) ⟨1151627, by rfl⟩ : syracuseStep 1535503 = 2303255) B2303255
theorem B9842219 : Blo 1534464 9842219 := bstep (se 1 (by rfl) ⟨7381664, by rfl⟩ : syracuseStep 9842219 = 14763329) B14763329
theorem B1535547 : Blo 1534464 1535547 := bstep (se 1 (by rfl) ⟨1151660, by rfl⟩ : syracuseStep 1535547 = 2303321) B2303321
theorem B1535623 : Blo 1534464 1535623 := bstep (se 1 (by rfl) ⟨1151717, by rfl⟩ : syracuseStep 1535623 = 2303435) B2303435
theorem B2592391 : Blo 1534464 2592391 := bstep (se 1 (by rfl) ⟨1944293, by rfl⟩ : syracuseStep 2592391 = 3888587) B3888587
theorem B1535631 : Blo 1534464 1535631 := bstep (se 1 (by rfl) ⟨1151723, by rfl⟩ : syracuseStep 1535631 = 2303447) B2303447
theorem B4370105 : Blo 1534464 4370105 := bstep (se 2 (by rfl) ⟨1638789, by rfl⟩ : syracuseStep 4370105 = 3277579) B3277579
theorem B1535675 : Blo 1534464 1535675 := bstep (se 1 (by rfl) ⟨1151756, by rfl⟩ : syracuseStep 1535675 = 2303513) B2303513
theorem B1535751 : Blo 1534464 1535751 := bstep (se 1 (by rfl) ⟨1151813, by rfl⟩ : syracuseStep 1535751 = 2303627) B2303627
theorem B3452687 : Blo 1534464 3452687 := bstep (se 1 (by rfl) ⟨2589515, by rfl⟩ : syracuseStep 3452687 = 5179031) B5179031
theorem B8744719 : Blo 1534464 8744719 := bstep (se 1 (by rfl) ⟨6558539, by rfl⟩ : syracuseStep 8744719 = 13117079) B13117079
theorem B1535759 : Blo 1534464 1535759 := bstep (se 1 (by rfl) ⟨1151819, by rfl⟩ : syracuseStep 1535759 = 2303639) B2303639
theorem B3280655 : Blo 1534464 3280655 := bstep (se 1 (by rfl) ⟨2460491, by rfl⟩ : syracuseStep 3280655 = 4920983) B4920983
theorem B3452705 : Blo 1534464 3452705 := bstep (se 2 (by rfl) ⟨1294764, by rfl⟩ : syracuseStep 3452705 = 2589529) B2589529
theorem B4370219 : Blo 1534464 4370219 := bstep (se 1 (by rfl) ⟨3277664, by rfl⟩ : syracuseStep 4370219 = 6555329) B6555329
theorem B1535803 : Blo 1534464 1535803 := bstep (se 1 (by rfl) ⟨1151852, by rfl⟩ : syracuseStep 1535803 = 2303705) B2303705
theorem B5181299 : Blo 1534464 5181299 := bstep (se 1 (by rfl) ⟨3885974, by rfl⟩ : syracuseStep 5181299 = 7771949) B7771949
theorem B3886967 : Blo 1534464 3886967 := bstep (se 1 (by rfl) ⟨2915225, by rfl⟩ : syracuseStep 3886967 = 5830451) B5830451
theorem B1535879 : Blo 1534464 1535879 := bstep (se 1 (by rfl) ⟨1151909, by rfl⟩ : syracuseStep 1535879 = 2303819) B2303819
theorem B1535887 : Blo 1534464 1535887 := bstep (se 1 (by rfl) ⟨1151915, by rfl⟩ : syracuseStep 1535887 = 2303831) B2303831
theorem B5828537 : Blo 1534464 5828537 := bstep (se 2 (by rfl) ⟨2185701, by rfl⟩ : syracuseStep 5828537 = 4371403) B4371403
theorem B1535931 : Blo 1534464 1535931 := bstep (se 1 (by rfl) ⟨1151948, by rfl⟩ : syracuseStep 1535931 = 2303897) B2303897
theorem B22147019 : Blo 1534464 22147019 := bstep (se 1 (by rfl) ⟨16610264, by rfl⟩ : syracuseStep 22147019 = 33220529) B33220529
theorem B1536007 : Blo 1534464 1536007 := bstep (se 1 (by rfl) ⟨1152005, by rfl⟩ : syracuseStep 1536007 = 2304011) B2304011
theorem B13111307 : Blo 1534464 13111307 := bstep (se 1 (by rfl) ⟨9833480, by rfl⟩ : syracuseStep 13111307 = 19666961) B19666961
theorem B1536015 : Blo 1534464 1536015 := bstep (se 1 (by rfl) ⟨1152011, by rfl⟩ : syracuseStep 1536015 = 2304023) B2304023
theorem B1536059 : Blo 1534464 1536059 := bstep (se 1 (by rfl) ⟨1152044, by rfl⟩ : syracuseStep 1536059 = 2304089) B2304089
theorem B7376957 : Blo 1534464 7376957 := bstep (se 3 (by rfl) ⟨1383179, by rfl⟩ : syracuseStep 7376957 = 2766359) B2766359
theorem B3453047 : Blo 1534464 3453047 := bstep (se 1 (by rfl) ⟨2589785, by rfl⟩ : syracuseStep 3453047 = 5179571) B5179571
theorem B3690631 : Blo 1534464 3690631 := bstep (se 1 (by rfl) ⟨2767973, by rfl⟩ : syracuseStep 3690631 = 5535947) B5535947
theorem B1536135 : Blo 1534464 1536135 := bstep (se 1 (by rfl) ⟨1152101, by rfl⟩ : syracuseStep 1536135 = 2304203) B2304203
theorem B1536143 : Blo 1534464 1536143 := bstep (se 1 (by rfl) ⟨1152107, by rfl⟩ : syracuseStep 1536143 = 2304215) B2304215
theorem B1536187 : Blo 1534464 1536187 := bstep (se 1 (by rfl) ⟨1152140, by rfl⟩ : syracuseStep 1536187 = 2304281) B2304281
theorem B1536263 : Blo 1534464 1536263 := bstep (se 1 (by rfl) ⟨1152197, by rfl⟩ : syracuseStep 1536263 = 2304395) B2304395
theorem B1536271 : Blo 1534464 1536271 := bstep (se 1 (by rfl) ⟨1152203, by rfl⟩ : syracuseStep 1536271 = 2304407) B2304407
theorem B3690785 : Blo 1534464 3690785 := bstep (se 2 (by rfl) ⟨1384044, by rfl⟩ : syracuseStep 3690785 = 2768089) B2768089
theorem B3453227 : Blo 1534464 3453227 := bstep (se 1 (by rfl) ⟨2589920, by rfl⟩ : syracuseStep 3453227 = 5179841) B5179841
theorem B4919611 : Blo 1534464 4919611 := bstep (se 1 (by rfl) ⟨3689708, by rfl⟩ : syracuseStep 4919611 = 7379417) B7379417
theorem B1536315 : Blo 1534464 1536315 := bstep (se 1 (by rfl) ⟨1152236, by rfl⟩ : syracuseStep 1536315 = 2304473) B2304473
theorem B1536391 : Blo 1534464 1536391 := bstep (se 1 (by rfl) ⟨1152293, by rfl⟩ : syracuseStep 1536391 = 2304587) B2304587
theorem B1536399 : Blo 1534464 1536399 := bstep (se 1 (by rfl) ⟨1152299, by rfl⟩ : syracuseStep 1536399 = 2304599) B2304599
theorem B1536443 : Blo 1534464 1536443 := bstep (se 1 (by rfl) ⟨1152332, by rfl⟩ : syracuseStep 1536443 = 2304665) B2304665
theorem B7377419 : Blo 1534464 7377419 := bstep (se 1 (by rfl) ⟨5533064, by rfl⟩ : syracuseStep 7377419 = 11066129) B11066129
theorem B16593437 : Blo 1534464 16593437 := bstep (se 3 (by rfl) ⟨3111269, by rfl⟩ : syracuseStep 16593437 = 6222539) B6222539
theorem B7770653 : Blo 1534464 7770653 := bstep (se 3 (by rfl) ⟨1456997, by rfl⟩ : syracuseStep 7770653 = 2913995) B2913995
theorem B3453587 : Blo 1534464 3453587 := bstep (se 1 (by rfl) ⟨2590190, by rfl⟩ : syracuseStep 3453587 = 5180381) B5180381
theorem B3453641 : Blo 1534464 3453641 := bstep (se 2 (by rfl) ⟨1295115, by rfl⟩ : syracuseStep 3453641 = 2590231) B2590231
theorem B15971107 : Blo 1534464 15971107 := bstep (se 1 (by rfl) ⟨11978330, by rfl⟩ : syracuseStep 15971107 = 23956661) B23956661
theorem B3887959 : Blo 1534464 3887959 := bstep (se 1 (by rfl) ⟨2915969, by rfl⟩ : syracuseStep 3887959 = 5831939) B5831939
theorem B4371347 : Blo 1534464 4371347 := bstep (se 1 (by rfl) ⟨3278510, by rfl⟩ : syracuseStep 4371347 = 6557021) B6557021
theorem B7771139 : Blo 1534464 7771139 := bstep (se 1 (by rfl) ⟨5828354, by rfl⟩ : syracuseStep 7771139 = 11656709) B11656709
theorem B8745995 : Blo 1534464 8745995 := bstep (se 1 (by rfl) ⟨6559496, by rfl⟩ : syracuseStep 8745995 = 13118993) B13118993
theorem B9835607 : Blo 1534464 9835607 := bstep (se 1 (by rfl) ⟨7376705, by rfl⟩ : syracuseStep 9835607 = 14753411) B14753411
theorem B3691639 : Blo 1534464 3691639 := bstep (se 1 (by rfl) ⟨2768729, by rfl⟩ : syracuseStep 3691639 = 5537459) B5537459
theorem B3888263 : Blo 1534464 3888263 := bstep (se 1 (by rfl) ⟨2916197, by rfl⟩ : syracuseStep 3888263 = 5832395) B5832395
theorem B4150457 : Blo 1534464 4150457 := bstep (se 2 (by rfl) ⟨1556421, by rfl⟩ : syracuseStep 4150457 = 3112843) B3112843
theorem B8746177 : Blo 1534464 8746177 := bstep (se 2 (by rfl) ⟨3279816, by rfl⟩ : syracuseStep 8746177 = 6559633) B6559633
theorem B3888395 : Blo 1534464 3888395 := bstep (se 1 (by rfl) ⟨2916296, by rfl⟩ : syracuseStep 3888395 = 5832593) B5832593
theorem B4371745 : Blo 1534464 4371745 := bstep (se 2 (by rfl) ⟨1639404, by rfl⟩ : syracuseStep 4371745 = 3278809) B3278809
theorem B3454343 : Blo 1534464 3454343 := bstep (se 1 (by rfl) ⟨2590757, by rfl⟩ : syracuseStep 3454343 = 5181515) B5181515
theorem B17487251 : Blo 1534464 17487251 := bstep (se 1 (by rfl) ⟨13115438, by rfl⟩ : syracuseStep 17487251 = 26230877) B26230877
theorem B21018041 : Blo 1534464 21018041 := bstep (se 2 (by rfl) ⟨7881765, by rfl⟩ : syracuseStep 21018041 = 15763531) B15763531
theorem B8295965 : Blo 1534464 8295965 := bstep (se 3 (by rfl) ⟨1555493, by rfl⟩ : syracuseStep 8295965 = 3110987) B3110987
theorem B3454523 : Blo 1534464 3454523 := bstep (se 1 (by rfl) ⟨2590892, by rfl⟩ : syracuseStep 3454523 = 5181785) B5181785
theorem B3454649 : Blo 1534464 3454649 := bstep (se 2 (by rfl) ⟨1295493, by rfl⟩ : syracuseStep 3454649 = 2590987) B2590987
theorem B3888911 : Blo 1534464 3888911 := bstep (se 1 (by rfl) ⟨2916683, by rfl⟩ : syracuseStep 3888911 = 5833367) B5833367
theorem B3889043 : Blo 1534464 3889043 := bstep (se 1 (by rfl) ⟨2916782, by rfl⟩ : syracuseStep 3889043 = 5833565) B5833565
theorem B4667321 : Blo 1534464 4667321 := bstep (se 2 (by rfl) ⟨1750245, by rfl⟩ : syracuseStep 4667321 = 3500491) B3500491
theorem B7378897 : Blo 1534464 7378897 := bstep (se 2 (by rfl) ⟨2767086, by rfl⟩ : syracuseStep 7378897 = 5534173) B5534173
theorem B2185223 : Blo 1534464 2185223 := bstep (se 1 (by rfl) ⟨1638917, by rfl⟩ : syracuseStep 2185223 = 3277835) B3277835
theorem B3454991 : Blo 1534464 3454991 := bstep (se 1 (by rfl) ⟨2591243, by rfl⟩ : syracuseStep 3454991 = 5182487) B5182487
theorem B3455009 : Blo 1534464 3455009 := bstep (se 2 (by rfl) ⟨1295628, by rfl⟩ : syracuseStep 3455009 = 2591257) B2591257
theorem B6559805 : Blo 1534464 6559805 := bstep (se 3 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 6559805 = 2459927) B2459927
theorem B16595077 : Blo 1534464 16595077 := bstep (se 4 (by rfl) ⟨1555788, by rfl⟩ : syracuseStep 16595077 = 3111577) B3111577
theorem B2914451 : Blo 1534464 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B4372633 : Blo 1534464 4372633 := bstep (se 2 (by rfl) ⟨1639737, by rfl⟩ : syracuseStep 4372633 = 3279475) B3279475
theorem B2185417 : Blo 1534464 2185417 := bstep (se 2 (by rfl) ⟨819531, by rfl⟩ : syracuseStep 2185417 = 1639063) B1639063
theorem B1726735 : Blo 1534464 1726735 := bstep (se 1 (by rfl) ⟨1295051, by rfl⟩ : syracuseStep 1726735 = 2590103) B2590103
theorem B2914679 : Blo 1534464 2914679 := bstep (se 1 (by rfl) ⟨2186009, by rfl⟩ : syracuseStep 2914679 = 4372019) B4372019
theorem B3455351 : Blo 1534464 3455351 := bstep (se 1 (by rfl) ⟨2591513, by rfl⟩ : syracuseStep 3455351 = 5183027) B5183027
theorem B18667907 : Blo 1534464 18667907 := bstep (se 1 (by rfl) ⟨14000930, by rfl⟩ : syracuseStep 18667907 = 28001861) B28001861
theorem B5183891 : Blo 1534464 5183891 := bstep (se 1 (by rfl) ⟨3887918, by rfl⟩ : syracuseStep 5183891 = 7775837) B7775837
theorem B2365967 : Blo 1534464 2365967 := bstep (se 1 (by rfl) ⟨1774475, by rfl⟩ : syracuseStep 2365967 = 3548951) B3548951
theorem B2767375 : Blo 1534464 2767375 := bstep (se 1 (by rfl) ⟨2075531, by rfl⟩ : syracuseStep 2767375 = 4151063) B4151063
theorem B4373021 : Blo 1534464 4373021 := bstep (se 3 (by rfl) ⟨819941, by rfl⟩ : syracuseStep 4373021 = 1639883) B1639883
theorem B3455531 : Blo 1534464 3455531 := bstep (se 1 (by rfl) ⟨2591648, by rfl⟩ : syracuseStep 3455531 = 5183297) B5183297
theorem B7772759 : Blo 1534464 7772759 := bstep (se 1 (by rfl) ⟨5829569, by rfl⟩ : syracuseStep 7772759 = 11659139) B11659139
theorem B2185975 : Blo 1534464 2185975 := bstep (se 1 (by rfl) ⟨1639481, by rfl⟩ : syracuseStep 2185975 = 3278963) B3278963
theorem B1727239 : Blo 1534464 1727239 := bstep (se 1 (by rfl) ⟨1295429, by rfl⟩ : syracuseStep 1727239 = 2590859) B2590859
theorem B3455891 : Blo 1534464 3455891 := bstep (se 1 (by rfl) ⟨2591918, by rfl⟩ : syracuseStep 3455891 = 5183837) B5183837
theorem B1727419 : Blo 1534464 1727419 := bstep (se 1 (by rfl) ⟨1295564, by rfl⟩ : syracuseStep 1727419 = 2591129) B2591129
theorem B3455945 : Blo 1534464 3455945 := bstep (se 2 (by rfl) ⟨1295979, by rfl⟩ : syracuseStep 3455945 = 2591959) B2591959
theorem B7773245 : Blo 1534464 7773245 := bstep (se 3 (by rfl) ⟨1457483, by rfl⟩ : syracuseStep 7773245 = 2914967) B2914967
theorem B33668227 : Blo 1534464 33668227 := bstep (se 1 (by rfl) ⟨25251170, by rfl⟩ : syracuseStep 33668227 = 50502341) B50502341
theorem B1555643 : Blo 1534464 1555643 := bstep (se 1 (by rfl) ⟨1166732, by rfl⟩ : syracuseStep 1555643 = 2333465) B2333465
theorem B1727887 : Blo 1534464 1727887 := bstep (se 1 (by rfl) ⟨1295915, by rfl⟩ : syracuseStep 1727887 = 2591831) B2591831
theorem B2186681 : Blo 1534464 2186681 := bstep (se 2 (by rfl) ⟨820005, by rfl⟩ : syracuseStep 2186681 = 1640011) B1640011
theorem B5832121 : Blo 1534464 5832121 := bstep (se 2 (by rfl) ⟨2187045, by rfl⟩ : syracuseStep 5832121 = 4374091) B4374091
theorem B2186767 : Blo 1534464 2186767 := bstep (se 1 (by rfl) ⟨1640075, by rfl⟩ : syracuseStep 2186767 = 3280151) B3280151
theorem B2186795 : Blo 1534464 2186795 := bstep (se 1 (by rfl) ⟨1640096, by rfl⟩ : syracuseStep 2186795 = 3280193) B3280193
theorem B17727041 : Blo 1534464 17727041 := bstep (se 2 (by rfl) ⟨6647640, by rfl⟩ : syracuseStep 17727041 = 13295281) B13295281
theorem B21290597 : Blo 1534464 21290597 := bstep (se 4 (by rfl) ⟨1995993, by rfl⟩ : syracuseStep 21290597 = 3991987) B3991987
theorem B3456647 : Blo 1534464 3456647 := bstep (se 1 (by rfl) ⟨2592485, by rfl⟩ : syracuseStep 3456647 = 5184971) B5184971
theorem B5185295 : Blo 1534464 5185295 := bstep (se 1 (by rfl) ⟨3888971, by rfl⟩ : syracuseStep 5185295 = 7777943) B7777943
theorem B2301755 : Blo 1534464 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B3456827 : Blo 1534464 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B2301815 : Blo 1534464 2301815 := bstep (se 1 (by rfl) ⟨1726361, by rfl⟩ : syracuseStep 2301815 = 3452723) B3452723
theorem B1728391 : Blo 1534464 1728391 := bstep (se 1 (by rfl) ⟨1296293, by rfl⟩ : syracuseStep 1728391 = 2592587) B2592587
theorem B2301839 : Blo 1534464 2301839 := bstep (se 1 (by rfl) ⟨1726379, by rfl⟩ : syracuseStep 2301839 = 3452759) B3452759
theorem B67297177 : Blo 1534464 67297177 := bstep (se 2 (by rfl) ⟨25236441, by rfl⟩ : syracuseStep 67297177 = 50472883) B50472883
theorem B2301881 : Blo 1534464 2301881 := bstep (se 2 (by rfl) ⟨863205, by rfl⟩ : syracuseStep 2301881 = 1726411) B1726411
theorem B3456953 : Blo 1534464 3456953 := bstep (se 2 (by rfl) ⟨1296357, by rfl⟩ : syracuseStep 3456953 = 2592715) B2592715
theorem B8740871 : Blo 1534464 8740871 := bstep (se 1 (by rfl) ⟨6555653, by rfl⟩ : syracuseStep 8740871 = 13111307) B13111307
theorem B3457043 : Blo 1534464 3457043 := bstep (se 1 (by rfl) ⟨2592782, by rfl⟩ : syracuseStep 3457043 = 5185565) B5185565
theorem B8749093 : Blo 1534464 8749093 := bstep (se 4 (by rfl) ⟨820227, by rfl⟩ : syracuseStep 8749093 = 1640455) B1640455
theorem B2302031 : Blo 1534464 2302031 := bstep (se 1 (by rfl) ⟨1726523, by rfl⟩ : syracuseStep 2302031 = 3453047) B3453047
theorem B22126769 : Blo 1534464 22126769 := bstep (se 2 (by rfl) ⟨8297538, by rfl⟩ : syracuseStep 22126769 = 16595077) B16595077
theorem B2302151 : Blo 1534464 2302151 := bstep (se 1 (by rfl) ⟨1726613, by rfl⟩ : syracuseStep 2302151 = 3453227) B3453227
theorem B2302313 : Blo 1534464 2302313 := bstep (se 2 (by rfl) ⟨863367, by rfl⟩ : syracuseStep 2302313 = 1726735) B1726735
theorem B2302391 : Blo 1534464 2302391 := bstep (se 1 (by rfl) ⟨1726793, by rfl⟩ : syracuseStep 2302391 = 3453587) B3453587
theorem B2302427 : Blo 1534464 2302427 := bstep (se 1 (by rfl) ⟨1726820, by rfl⟩ : syracuseStep 2302427 = 3453641) B3453641
theorem B11665943 : Blo 1534464 11665943 := bstep (se 1 (by rfl) ⟨8749457, by rfl⟩ : syracuseStep 11665943 = 17498915) B17498915
theorem B2458441 : Blo 1534464 2458441 := bstep (se 2 (by rfl) ⟨921915, by rfl⟩ : syracuseStep 2458441 = 1843831) B1843831
theorem B7103305 : Blo 1534464 7103305 := bstep (se 2 (by rfl) ⟨2663739, by rfl⟩ : syracuseStep 7103305 = 5327479) B5327479
theorem B5833579 : Blo 1534464 5833579 := bstep (se 1 (by rfl) ⟨4375184, by rfl⟩ : syracuseStep 5833579 = 8750369) B8750369
theorem B2589583 : Blo 1534464 2589583 := bstep (se 1 (by rfl) ⟨1942187, by rfl⟩ : syracuseStep 2589583 = 3884375) B3884375
theorem B2302895 : Blo 1534464 2302895 := bstep (se 1 (by rfl) ⟨1727171, by rfl⟩ : syracuseStep 2302895 = 3454343) B3454343
theorem B11658167 : Blo 1534464 11658167 := bstep (se 1 (by rfl) ⟨8743625, by rfl⟩ : syracuseStep 11658167 = 17487251) B17487251
theorem B2302985 : Blo 1534464 2302985 := bstep (se 2 (by rfl) ⟨863619, by rfl⟩ : syracuseStep 2302985 = 1727239) B1727239
theorem B5530643 : Blo 1534464 5530643 := bstep (se 1 (by rfl) ⟨4147982, by rfl⟩ : syracuseStep 5530643 = 8295965) B8295965
theorem B2303015 : Blo 1534464 2303015 := bstep (se 1 (by rfl) ⟨1727261, by rfl⟩ : syracuseStep 2303015 = 3454523) B3454523
theorem B19948589 : Blo 1534464 19948589 := bstep (se 3 (by rfl) ⟨3740360, by rfl⟩ : syracuseStep 19948589 = 7480721) B7480721
theorem B3277903 : Blo 1534464 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B2303099 : Blo 1534464 2303099 := bstep (se 1 (by rfl) ⟨1727324, by rfl⟩ : syracuseStep 2303099 = 3454649) B3454649
theorem B2303225 : Blo 1534464 2303225 := bstep (se 2 (by rfl) ⟨863709, by rfl⟩ : syracuseStep 2303225 = 1727419) B1727419
theorem B2303327 : Blo 1534464 2303327 := bstep (se 1 (by rfl) ⟨1727495, by rfl⟩ : syracuseStep 2303327 = 3454991) B3454991
theorem B2303339 : Blo 1534464 2303339 := bstep (se 1 (by rfl) ⟨1727504, by rfl⟩ : syracuseStep 2303339 = 3455009) B3455009
theorem B6309245 : Blo 1534464 6309245 := bstep (se 3 (by rfl) ⟨1182983, by rfl⟩ : syracuseStep 6309245 = 2365967) B2365967
theorem B1942967 : Blo 1534464 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B3884507 : Blo 1534464 3884507 := bstep (se 1 (by rfl) ⟨2913380, by rfl⟩ : syracuseStep 3884507 = 5826761) B5826761
theorem B6227437 : Blo 1534464 6227437 := bstep (se 3 (by rfl) ⟨1167644, by rfl⟩ : syracuseStep 6227437 = 2335289) B2335289
theorem B2590265 : Blo 1534464 2590265 := bstep (se 2 (by rfl) ⟨971349, by rfl⟩ : syracuseStep 2590265 = 1942699) B1942699
theorem B1943119 : Blo 1534464 1943119 := bstep (se 1 (by rfl) ⟨1457339, by rfl⟩ : syracuseStep 1943119 = 2914679) B2914679
theorem B2303567 : Blo 1534464 2303567 := bstep (se 1 (by rfl) ⟨1727675, by rfl⟩ : syracuseStep 2303567 = 3455351) B3455351
theorem B12445271 : Blo 1534464 12445271 := bstep (se 1 (by rfl) ⟨9333953, by rfl⟩ : syracuseStep 12445271 = 18667907) B18667907
theorem B5178977 : Blo 1534464 5178977 := bstep (se 2 (by rfl) ⟨1942116, by rfl⟩ : syracuseStep 5178977 = 3884233) B3884233
theorem B6555259 : Blo 1534464 6555259 := bstep (se 1 (by rfl) ⟨4916444, by rfl⟩ : syracuseStep 6555259 = 9832889) B9832889
theorem B2303687 : Blo 1534464 2303687 := bstep (se 1 (by rfl) ⟨1727765, by rfl⟩ : syracuseStep 2303687 = 3455531) B3455531
theorem B2303849 : Blo 1534464 2303849 := bstep (se 2 (by rfl) ⟨863943, by rfl⟩ : syracuseStep 2303849 = 1727887) B1727887
theorem B7776161 : Blo 1534464 7776161 := bstep (se 2 (by rfl) ⟨2916060, by rfl⟩ : syracuseStep 7776161 = 5832121) B5832121
theorem B2303927 : Blo 1534464 2303927 := bstep (se 1 (by rfl) ⟨1727945, by rfl⟩ : syracuseStep 2303927 = 3455891) B3455891
theorem B22439873 : Blo 1534464 22439873 := bstep (se 2 (by rfl) ⟨8414952, by rfl⟩ : syracuseStep 22439873 = 16829905) B16829905
theorem B2303963 : Blo 1534464 2303963 := bstep (se 1 (by rfl) ⟨1727972, by rfl⟩ : syracuseStep 2303963 = 3455945) B3455945
theorem B4917419 : Blo 1534464 4917419 := bstep (se 1 (by rfl) ⟨3688064, by rfl⟩ : syracuseStep 4917419 = 7376129) B7376129
theorem B2590967 : Blo 1534464 2590967 := bstep (se 1 (by rfl) ⟨1943225, by rfl⟩ : syracuseStep 2590967 = 3886451) B3886451
theorem B11659625 : Blo 1534464 11659625 := bstep (se 2 (by rfl) ⟨4372359, by rfl⟩ : syracuseStep 11659625 = 8744719) B8744719
theorem B2304431 : Blo 1534464 2304431 := bstep (se 1 (by rfl) ⟨1728323, by rfl⟩ : syracuseStep 2304431 = 3456647) B3456647
theorem B2304521 : Blo 1534464 2304521 := bstep (se 2 (by rfl) ⟨864195, by rfl⟩ : syracuseStep 2304521 = 1728391) B1728391
theorem B89729569 : Blo 1534464 89729569 := bstep (se 2 (by rfl) ⟨33648588, by rfl⟩ : syracuseStep 89729569 = 67297177) B67297177
theorem B1534503 : Blo 1534464 1534503 := bstep (se 1 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 1534503 = 2301755) B2301755
theorem B2304551 : Blo 1534464 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B1534543 : Blo 1534464 1534543 := bstep (se 1 (by rfl) ⟨1150907, by rfl⟩ : syracuseStep 1534543 = 2301815) B2301815
theorem B2591311 : Blo 1534464 2591311 := bstep (se 1 (by rfl) ⟨1943483, by rfl⟩ : syracuseStep 2591311 = 3886967) B3886967
theorem B1534559 : Blo 1534464 1534559 := bstep (se 1 (by rfl) ⟨1150919, by rfl⟩ : syracuseStep 1534559 = 2301839) B2301839
theorem B1534587 : Blo 1534464 1534587 := bstep (se 1 (by rfl) ⟨1150940, by rfl⟩ : syracuseStep 1534587 = 2301881) B2301881
theorem B3885691 : Blo 1534464 3885691 := bstep (se 1 (by rfl) ⟨2914268, by rfl⟩ : syracuseStep 3885691 = 5828537) B5828537
theorem B2304635 : Blo 1534464 2304635 := bstep (se 1 (by rfl) ⟨1728476, by rfl⟩ : syracuseStep 2304635 = 3456953) B3456953
theorem B14764679 : Blo 1534464 14764679 := bstep (se 1 (by rfl) ⟨11073509, by rfl⟩ : syracuseStep 14764679 = 22147019) B22147019
theorem B1534639 : Blo 1534464 1534639 := bstep (se 1 (by rfl) ⟨1150979, by rfl⟩ : syracuseStep 1534639 = 2301959) B2301959
theorem B5827261 : Blo 1534464 5827261 := bstep (se 3 (by rfl) ⟨1092611, by rfl⟩ : syracuseStep 5827261 = 2185223) B2185223
theorem B1534663 : Blo 1534464 1534663 := bstep (se 1 (by rfl) ⟨1150997, by rfl⟩ : syracuseStep 1534663 = 2301995) B2301995
theorem B1944263 : Blo 1534464 1944263 := bstep (se 1 (by rfl) ⟨1458197, by rfl⟩ : syracuseStep 1944263 = 2916395) B2916395
theorem B4917971 : Blo 1534464 4917971 := bstep (se 1 (by rfl) ⟨3688478, by rfl⟩ : syracuseStep 4917971 = 7376957) B7376957
theorem B1534683 : Blo 1534464 1534683 := bstep (se 1 (by rfl) ⟨1151012, by rfl⟩ : syracuseStep 1534683 = 2302025) B2302025
theorem B3156727 : Blo 1534464 3156727 := bstep (se 1 (by rfl) ⟨2367545, by rfl⟩ : syracuseStep 3156727 = 4735091) B4735091
theorem B4918009 : Blo 1534464 4918009 := bstep (se 2 (by rfl) ⟨1844253, by rfl⟩ : syracuseStep 4918009 = 3688507) B3688507
theorem B1534759 : Blo 1534464 1534759 := bstep (se 1 (by rfl) ⟨1151069, by rfl⟩ : syracuseStep 1534759 = 2302139) B2302139
theorem B2591561 : Blo 1534464 2591561 := bstep (se 2 (by rfl) ⟨971835, by rfl⟩ : syracuseStep 2591561 = 1943671) B1943671
theorem B1534799 : Blo 1534464 1534799 := bstep (se 1 (by rfl) ⟨1151099, by rfl⟩ : syracuseStep 1534799 = 2302199) B2302199
theorem B1534815 : Blo 1534464 1534815 := bstep (se 1 (by rfl) ⟨1151111, by rfl⟩ : syracuseStep 1534815 = 2302223) B2302223
theorem B1944415 : Blo 1534464 1944415 := bstep (se 1 (by rfl) ⟨1458311, by rfl⟩ : syracuseStep 1944415 = 2916623) B2916623
theorem B8743787 : Blo 1534464 8743787 := bstep (se 1 (by rfl) ⟨6557840, by rfl⟩ : syracuseStep 8743787 = 13115681) B13115681
theorem B1534843 : Blo 1534464 1534843 := bstep (se 1 (by rfl) ⟨1151132, by rfl⟩ : syracuseStep 1534843 = 2302265) B2302265
theorem B1534895 : Blo 1534464 1534895 := bstep (se 1 (by rfl) ⟨1151171, by rfl⟩ : syracuseStep 1534895 = 2302343) B2302343
theorem B1534919 : Blo 1534464 1534919 := bstep (se 1 (by rfl) ⟨1151189, by rfl⟩ : syracuseStep 1534919 = 2302379) B2302379
theorem B1534939 : Blo 1534464 1534939 := bstep (se 1 (by rfl) ⟨1151204, by rfl⟩ : syracuseStep 1534939 = 2302409) B2302409
theorem B13110245 : Blo 1534464 13110245 := bstep (se 4 (by rfl) ⟨1229085, by rfl⟩ : syracuseStep 13110245 = 2458171) B2458171
theorem B4918279 : Blo 1534464 4918279 := bstep (se 1 (by rfl) ⟨3688709, by rfl⟩ : syracuseStep 4918279 = 7377419) B7377419
theorem B11062291 : Blo 1534464 11062291 := bstep (se 1 (by rfl) ⟨8296718, by rfl⟩ : syracuseStep 11062291 = 16593437) B16593437
theorem B5180435 : Blo 1534464 5180435 := bstep (se 1 (by rfl) ⟨3885326, by rfl⟩ : syracuseStep 5180435 = 7770653) B7770653
theorem B1535015 : Blo 1534464 1535015 := bstep (se 1 (by rfl) ⟨1151261, by rfl⟩ : syracuseStep 1535015 = 2302523) B2302523
theorem B1535055 : Blo 1534464 1535055 := bstep (se 1 (by rfl) ⟨1151291, by rfl⟩ : syracuseStep 1535055 = 2302583) B2302583
theorem B1535071 : Blo 1534464 1535071 := bstep (se 1 (by rfl) ⟨1151303, by rfl⟩ : syracuseStep 1535071 = 2302607) B2302607
theorem B1535099 : Blo 1534464 1535099 := bstep (se 1 (by rfl) ⟨1151324, by rfl⟩ : syracuseStep 1535099 = 2302649) B2302649
theorem B4148381 : Blo 1534464 4148381 := bstep (se 3 (by rfl) ⟨777821, by rfl⟩ : syracuseStep 4148381 = 1555643) B1555643
theorem B1535151 : Blo 1534464 1535151 := bstep (se 1 (by rfl) ⟨1151363, by rfl⟩ : syracuseStep 1535151 = 2302727) B2302727
theorem B1535175 : Blo 1534464 1535175 := bstep (se 1 (by rfl) ⟨1151381, by rfl⟩ : syracuseStep 1535175 = 2302763) B2302763
theorem B1535195 : Blo 1534464 1535195 := bstep (se 1 (by rfl) ⟨1151396, by rfl⟩ : syracuseStep 1535195 = 2302793) B2302793
theorem B2591993 : Blo 1534464 2591993 := bstep (se 2 (by rfl) ⟨971997, by rfl⟩ : syracuseStep 2591993 = 1943995) B1943995
theorem B19688741 : Blo 1534464 19688741 := bstep (se 4 (by rfl) ⟨1845819, by rfl⟩ : syracuseStep 19688741 = 3691639) B3691639
theorem B1535271 : Blo 1534464 1535271 := bstep (se 1 (by rfl) ⟨1151453, by rfl⟩ : syracuseStep 1535271 = 2302907) B2302907
theorem B1535311 : Blo 1534464 1535311 := bstep (se 1 (by rfl) ⟨1151483, by rfl⟩ : syracuseStep 1535311 = 2302967) B2302967
theorem B5180759 : Blo 1534464 5180759 := bstep (se 1 (by rfl) ⟨3885569, by rfl⟩ : syracuseStep 5180759 = 7771139) B7771139
theorem B1535327 : Blo 1534464 1535327 := bstep (se 1 (by rfl) ⟨1151495, by rfl⟩ : syracuseStep 1535327 = 2302991) B2302991
theorem B179563877 : Blo 1534464 179563877 := bstep (se 4 (by rfl) ⟨16834113, by rfl⟩ : syracuseStep 179563877 = 33668227) B33668227
theorem B1535355 : Blo 1534464 1535355 := bstep (se 1 (by rfl) ⟨1151516, by rfl⟩ : syracuseStep 1535355 = 2303033) B2303033
theorem B6557071 : Blo 1534464 6557071 := bstep (se 1 (by rfl) ⟨4917803, by rfl⟩ : syracuseStep 6557071 = 9835607) B9835607
theorem B9842093 : Blo 1534464 9842093 := bstep (se 3 (by rfl) ⟨1845392, by rfl⟩ : syracuseStep 9842093 = 3690785) B3690785
theorem B1535407 : Blo 1534464 1535407 := bstep (se 1 (by rfl) ⟨1151555, by rfl⟩ : syracuseStep 1535407 = 2303111) B2303111
theorem B2592175 : Blo 1534464 2592175 := bstep (se 1 (by rfl) ⟨1944131, by rfl⟩ : syracuseStep 2592175 = 3888263) B3888263
theorem B1535431 : Blo 1534464 1535431 := bstep (se 1 (by rfl) ⟨1151573, by rfl⟩ : syracuseStep 1535431 = 2303147) B2303147
theorem B1535451 : Blo 1534464 1535451 := bstep (se 1 (by rfl) ⟨1151588, by rfl⟩ : syracuseStep 1535451 = 2303177) B2303177
theorem B2592263 : Blo 1534464 2592263 := bstep (se 1 (by rfl) ⟨1944197, by rfl⟩ : syracuseStep 2592263 = 3888395) B3888395
theorem B4369945 : Blo 1534464 4369945 := bstep (se 2 (by rfl) ⟨1638729, by rfl⟩ : syracuseStep 4369945 = 3277459) B3277459
theorem B1535527 : Blo 1534464 1535527 := bstep (se 1 (by rfl) ⟨1151645, by rfl⟩ : syracuseStep 1535527 = 2303291) B2303291
theorem B1535567 : Blo 1534464 1535567 := bstep (se 1 (by rfl) ⟨1151675, by rfl⟩ : syracuseStep 1535567 = 2303351) B2303351
theorem B1535583 : Blo 1534464 1535583 := bstep (se 1 (by rfl) ⟨1151687, by rfl⟩ : syracuseStep 1535583 = 2303375) B2303375
theorem B5828219 : Blo 1534464 5828219 := bstep (se 1 (by rfl) ⟨4371164, by rfl⟩ : syracuseStep 5828219 = 8742329) B8742329
theorem B1535611 : Blo 1534464 1535611 := bstep (se 1 (by rfl) ⟨1151708, by rfl⟩ : syracuseStep 1535611 = 2303417) B2303417
theorem B14012027 : Blo 1534464 14012027 := bstep (se 1 (by rfl) ⟨10509020, by rfl⟩ : syracuseStep 14012027 = 21018041) B21018041
theorem B1535663 : Blo 1534464 1535663 := bstep (se 1 (by rfl) ⟨1151747, by rfl⟩ : syracuseStep 1535663 = 2303495) B2303495
theorem B3452615 : Blo 1534464 3452615 := bstep (se 1 (by rfl) ⟨2589461, by rfl⟩ : syracuseStep 3452615 = 5178923) B5178923
theorem B3501767 : Blo 1534464 3501767 := bstep (se 1 (by rfl) ⟨2626325, by rfl⟩ : syracuseStep 3501767 = 5252651) B5252651
theorem B1535687 : Blo 1534464 1535687 := bstep (se 1 (by rfl) ⟨1151765, by rfl⟩ : syracuseStep 1535687 = 2303531) B2303531
theorem B21294809 : Blo 1534464 21294809 := bstep (se 2 (by rfl) ⟨7985553, by rfl⟩ : syracuseStep 21294809 = 15971107) B15971107
theorem B1535707 : Blo 1534464 1535707 := bstep (se 1 (by rfl) ⟨1151780, by rfl⟩ : syracuseStep 1535707 = 2303561) B2303561
theorem B1535783 : Blo 1534464 1535783 := bstep (se 1 (by rfl) ⟨1151837, by rfl⟩ : syracuseStep 1535783 = 2303675) B2303675
theorem B1535823 : Blo 1534464 1535823 := bstep (se 1 (by rfl) ⟨1151867, by rfl⟩ : syracuseStep 1535823 = 2303735) B2303735
theorem B1535839 : Blo 1534464 1535839 := bstep (se 1 (by rfl) ⟨1151879, by rfl⟩ : syracuseStep 1535839 = 2303759) B2303759
theorem B2592607 : Blo 1534464 2592607 := bstep (se 1 (by rfl) ⟨1944455, by rfl⟩ : syracuseStep 2592607 = 3888911) B3888911
theorem B7982957 : Blo 1534464 7982957 := bstep (se 3 (by rfl) ⟨1496804, by rfl⟩ : syracuseStep 7982957 = 2993609) B2993609
theorem B12447607 : Blo 1534464 12447607 := bstep (se 1 (by rfl) ⟨9335705, by rfl⟩ : syracuseStep 12447607 = 18671411) B18671411
theorem B1535867 : Blo 1534464 1535867 := bstep (se 1 (by rfl) ⟨1151900, by rfl⟩ : syracuseStep 1535867 = 2303801) B2303801
theorem B4919201 : Blo 1534464 4919201 := bstep (se 2 (by rfl) ⟨1844700, by rfl⟩ : syracuseStep 4919201 = 3689401) B3689401
theorem B1535919 : Blo 1534464 1535919 := bstep (se 1 (by rfl) ⟨1151939, by rfl⟩ : syracuseStep 1535919 = 2303879) B2303879
theorem B2592695 : Blo 1534464 2592695 := bstep (se 1 (by rfl) ⟨1944521, by rfl⟩ : syracuseStep 2592695 = 3889043) B3889043
theorem B1535943 : Blo 1534464 1535943 := bstep (se 1 (by rfl) ⟨1151957, by rfl⟩ : syracuseStep 1535943 = 2303915) B2303915
theorem B1535963 : Blo 1534464 1535963 := bstep (se 1 (by rfl) ⟨1151972, by rfl⟩ : syracuseStep 1535963 = 2303945) B2303945
theorem B1536039 : Blo 1534464 1536039 := bstep (se 1 (by rfl) ⟨1152029, by rfl⟩ : syracuseStep 1536039 = 2304059) B2304059
theorem B19664957 : Blo 1534464 19664957 := bstep (se 3 (by rfl) ⟨3687179, by rfl⟩ : syracuseStep 19664957 = 7374359) B7374359
theorem B1536079 : Blo 1534464 1536079 := bstep (se 1 (by rfl) ⟨1152059, by rfl⟩ : syracuseStep 1536079 = 2304119) B2304119
theorem B1536095 : Blo 1534464 1536095 := bstep (se 1 (by rfl) ⟨1152071, by rfl⟩ : syracuseStep 1536095 = 2304143) B2304143
theorem B1536123 : Blo 1534464 1536123 := bstep (se 1 (by rfl) ⟨1152092, by rfl⟩ : syracuseStep 1536123 = 2304185) B2304185
theorem B1536175 : Blo 1534464 1536175 := bstep (se 1 (by rfl) ⟨1152131, by rfl⟩ : syracuseStep 1536175 = 2304263) B2304263
theorem B1536199 : Blo 1534464 1536199 := bstep (se 1 (by rfl) ⟨1152149, by rfl⟩ : syracuseStep 1536199 = 2304299) B2304299
theorem B1536219 : Blo 1534464 1536219 := bstep (se 1 (by rfl) ⟨1152164, by rfl⟩ : syracuseStep 1536219 = 2304329) B2304329
theorem B11661569 : Blo 1534464 11661569 := bstep (se 2 (by rfl) ⟨4373088, by rfl⟩ : syracuseStep 11661569 = 8746177) B8746177
theorem B1536295 : Blo 1534464 1536295 := bstep (se 1 (by rfl) ⟨1152221, by rfl⟩ : syracuseStep 1536295 = 2304443) B2304443
theorem B1536335 : Blo 1534464 1536335 := bstep (se 1 (by rfl) ⟨1152251, by rfl⟩ : syracuseStep 1536335 = 2304503) B2304503
theorem B1536351 : Blo 1534464 1536351 := bstep (se 1 (by rfl) ⟨1152263, by rfl⟩ : syracuseStep 1536351 = 2304527) B2304527
theorem B1536379 : Blo 1534464 1536379 := bstep (se 1 (by rfl) ⟨1152284, by rfl⟩ : syracuseStep 1536379 = 2304569) B2304569
theorem B5828993 : Blo 1534464 5828993 := bstep (se 2 (by rfl) ⟨2185872, by rfl⟩ : syracuseStep 5828993 = 4371745) B4371745
theorem B5181839 : Blo 1534464 5181839 := bstep (se 1 (by rfl) ⟨3886379, by rfl⟩ : syracuseStep 5181839 = 7772759) B7772759
theorem B1536431 : Blo 1534464 1536431 := bstep (se 1 (by rfl) ⟨1152323, by rfl⟩ : syracuseStep 1536431 = 2304647) B2304647
theorem B1536455 : Blo 1534464 1536455 := bstep (se 1 (by rfl) ⟨1152341, by rfl⟩ : syracuseStep 1536455 = 2304683) B2304683
theorem B3453479 : Blo 1534464 3453479 := bstep (se 1 (by rfl) ⟨2590109, by rfl⟩ : syracuseStep 3453479 = 5180219) B5180219
theorem B5182163 : Blo 1534464 5182163 := bstep (se 1 (by rfl) ⟨3886622, by rfl⟩ : syracuseStep 5182163 = 7773245) B7773245
theorem B17052419 : Blo 1534464 17052419 := bstep (se 1 (by rfl) ⟨12789314, by rfl⟩ : syracuseStep 17052419 = 25578629) B25578629
theorem B3453803 : Blo 1534464 3453803 := bstep (se 1 (by rfl) ⟨2590352, by rfl⟩ : syracuseStep 3453803 = 5180705) B5180705
theorem B22147991 : Blo 1534464 22147991 := bstep (se 1 (by rfl) ⟨16610993, by rfl⟩ : syracuseStep 22147991 = 33221987) B33221987
theorem B3453857 : Blo 1534464 3453857 := bstep (se 2 (by rfl) ⟨1295196, by rfl⟩ : syracuseStep 3453857 = 2590393) B2590393
theorem B11818027 : Blo 1534464 11818027 := bstep (se 1 (by rfl) ⟨8863520, by rfl⟩ : syracuseStep 11818027 = 17727041) B17727041
theorem B14193731 : Blo 1534464 14193731 := bstep (se 1 (by rfl) ⟨10645298, by rfl⟩ : syracuseStep 14193731 = 21290597) B21290597
theorem B2913403 : Blo 1534464 2913403 := bstep (se 1 (by rfl) ⟨2185052, by rfl⟩ : syracuseStep 2913403 = 4370105) B4370105
theorem B2913479 : Blo 1534464 2913479 := bstep (se 1 (by rfl) ⟨2185109, by rfl⟩ : syracuseStep 2913479 = 4370219) B4370219
theorem B3454199 : Blo 1534464 3454199 := bstep (se 1 (by rfl) ⟨2590649, by rfl⟩ : syracuseStep 3454199 = 5181299) B5181299
theorem B14759333 : Blo 1534464 14759333 := bstep (se 4 (by rfl) ⟨1383687, by rfl⟩ : syracuseStep 14759333 = 2767375) B2767375
theorem B4920841 : Blo 1534464 4920841 := bstep (se 2 (by rfl) ⟨1845315, by rfl⟩ : syracuseStep 4920841 = 3690631) B3690631
theorem B5830177 : Blo 1534464 5830177 := bstep (se 2 (by rfl) ⟨2186316, by rfl⟩ : syracuseStep 5830177 = 4372633) B4372633
theorem B2913889 : Blo 1534464 2913889 := bstep (se 2 (by rfl) ⟨1092708, by rfl⟩ : syracuseStep 2913889 = 2185417) B2185417
theorem B7771787 : Blo 1534464 7771787 := bstep (se 1 (by rfl) ⟨5828840, by rfl⟩ : syracuseStep 7771787 = 11657681) B11657681
theorem B6559481 : Blo 1534464 6559481 := bstep (se 2 (by rfl) ⟨2459805, by rfl⟩ : syracuseStep 6559481 = 4919611) B4919611
theorem B3454793 : Blo 1534464 3454793 := bstep (se 2 (by rfl) ⟨1295547, by rfl⟩ : syracuseStep 3454793 = 2591095) B2591095
theorem B1726303 : Blo 1534464 1726303 := bstep (se 1 (by rfl) ⟨1294727, by rfl⟩ : syracuseStep 1726303 = 2589455) B2589455
theorem B5183351 : Blo 1534464 5183351 := bstep (se 1 (by rfl) ⟨3887513, by rfl⟩ : syracuseStep 5183351 = 7775027) B7775027
theorem B2914231 : Blo 1534464 2914231 := bstep (se 1 (by rfl) ⟨2185673, by rfl⟩ : syracuseStep 2914231 = 4371347) B4371347
theorem B5830663 : Blo 1534464 5830663 := bstep (se 1 (by rfl) ⟨4372997, by rfl⟩ : syracuseStep 5830663 = 8745995) B8745995
theorem B8304677 : Blo 1534464 8304677 := bstep (se 4 (by rfl) ⟨778563, by rfl⟩ : syracuseStep 8304677 = 1557127) B1557127
theorem B5183567 : Blo 1534464 5183567 := bstep (se 1 (by rfl) ⟨3887675, by rfl⟩ : syracuseStep 5183567 = 7775351) B7775351
theorem B2766971 : Blo 1534464 2766971 := bstep (se 1 (by rfl) ⟨2075228, by rfl⟩ : syracuseStep 2766971 = 4150457) B4150457
theorem B1726663 : Blo 1534464 1726663 := bstep (se 1 (by rfl) ⟨1294997, by rfl⟩ : syracuseStep 1726663 = 2589995) B2589995
theorem B4921661 : Blo 1534464 4921661 := bstep (se 3 (by rfl) ⟨922811, by rfl⟩ : syracuseStep 4921661 = 1845623) B1845623
theorem B2914633 : Blo 1534464 2914633 := bstep (se 2 (by rfl) ⟨1092987, by rfl⟩ : syracuseStep 2914633 = 2185975) B2185975
theorem B4372861 : Blo 1534464 4372861 := bstep (se 3 (by rfl) ⟨819911, by rfl⟩ : syracuseStep 4372861 = 1639823) B1639823
theorem B45504899 : Blo 1534464 45504899 := bstep (se 1 (by rfl) ⟨34128674, by rfl⟩ : syracuseStep 45504899 = 68257349) B68257349
theorem B5183945 : Blo 1534464 5183945 := bstep (se 2 (by rfl) ⟨1943979, by rfl⟩ : syracuseStep 5183945 = 3887959) B3887959
theorem B3791323 : Blo 1534464 3791323 := bstep (se 1 (by rfl) ⟨2843492, by rfl⟩ : syracuseStep 3791323 = 5686985) B5686985
theorem B5831149 : Blo 1534464 5831149 := bstep (se 3 (by rfl) ⟨1093340, by rfl⟩ : syracuseStep 5831149 = 2186681) B2186681
theorem B39352877 : Blo 1534464 39352877 := bstep (se 3 (by rfl) ⟨7378664, by rfl⟩ : syracuseStep 39352877 = 14757329) B14757329
theorem B3455585 : Blo 1534464 3455585 := bstep (se 2 (by rfl) ⟨1295844, by rfl⟩ : syracuseStep 3455585 = 2591689) B2591689
theorem B3111547 : Blo 1534464 3111547 := bstep (se 1 (by rfl) ⟨2333660, by rfl⟩ : syracuseStep 3111547 = 4667321) B4667321
theorem B4373203 : Blo 1534464 4373203 := bstep (se 1 (by rfl) ⟨3279902, by rfl⟩ : syracuseStep 4373203 = 6559805) B6559805
theorem B5184215 : Blo 1534464 5184215 := bstep (se 1 (by rfl) ⟨3888161, by rfl⟩ : syracuseStep 5184215 = 7776323) B7776323
theorem B5831453 : Blo 1534464 5831453 := bstep (se 3 (by rfl) ⟨1093397, by rfl⟩ : syracuseStep 5831453 = 2186795) B2186795
theorem B7379819 : Blo 1534464 7379819 := bstep (se 1 (by rfl) ⟨5534864, by rfl⟩ : syracuseStep 7379819 = 11069729) B11069729
theorem B5184431 : Blo 1534464 5184431 := bstep (se 1 (by rfl) ⟨3888323, by rfl⟩ : syracuseStep 5184431 = 7776647) B7776647
theorem B3455927 : Blo 1534464 3455927 := bstep (se 1 (by rfl) ⟨2591945, by rfl⟩ : syracuseStep 3455927 = 5183891) B5183891
theorem B2186203 : Blo 1534464 2186203 := bstep (se 1 (by rfl) ⟨1639652, by rfl⟩ : syracuseStep 2186203 = 3279305) B3279305
theorem B2915347 : Blo 1534464 2915347 := bstep (se 1 (by rfl) ⟨2186510, by rfl⟩ : syracuseStep 2915347 = 4373021) B4373021
theorem B1727527 : Blo 1534464 1727527 := bstep (se 1 (by rfl) ⟨1295645, by rfl⟩ : syracuseStep 1727527 = 2591291) B2591291
theorem B4152491 : Blo 1534464 4152491 := bstep (se 1 (by rfl) ⟨3114368, by rfl⟩ : syracuseStep 4152491 = 6228737) B6228737
theorem B15981761 : Blo 1534464 15981761 := bstep (se 2 (by rfl) ⟨5993160, by rfl⟩ : syracuseStep 15981761 = 11986321) B11986321
theorem B21060803 : Blo 1534464 21060803 := bstep (se 1 (by rfl) ⟨15795602, by rfl⟩ : syracuseStep 21060803 = 31591205) B31591205
theorem B11066615 : Blo 1534464 11066615 := bstep (se 1 (by rfl) ⟨8299961, by rfl⟩ : syracuseStep 11066615 = 16599923) B16599923
theorem B2915689 : Blo 1534464 2915689 := bstep (se 2 (by rfl) ⟨1093383, by rfl⟩ : syracuseStep 2915689 = 2186767) B2186767
theorem B3456521 : Blo 1534464 3456521 := bstep (se 2 (by rfl) ⟨1296195, by rfl⟩ : syracuseStep 3456521 = 2592391) B2592391
theorem B2186875 : Blo 1534464 2186875 := bstep (se 1 (by rfl) ⟨1640156, by rfl⟩ : syracuseStep 2186875 = 3280313) B3280313
theorem B5250707 : Blo 1534464 5250707 := bstep (se 1 (by rfl) ⟨3938030, by rfl⟩ : syracuseStep 5250707 = 7876061) B7876061
theorem B6561479 : Blo 1534464 6561479 := bstep (se 1 (by rfl) ⟨4921109, by rfl⟩ : syracuseStep 6561479 = 9842219) B9842219
theorem B2301791 : Blo 1534464 2301791 := bstep (se 1 (by rfl) ⟨1726343, by rfl⟩ : syracuseStep 2301791 = 3452687) B3452687
theorem B2187103 : Blo 1534464 2187103 := bstep (se 1 (by rfl) ⟨1640327, by rfl⟩ : syracuseStep 2187103 = 3280655) B3280655
theorem B3456863 : Blo 1534464 3456863 := bstep (se 1 (by rfl) ⟨2592647, by rfl⟩ : syracuseStep 3456863 = 5185295) B5185295
theorem B2301803 : Blo 1534464 2301803 := bstep (se 1 (by rfl) ⟨1726352, by rfl⟩ : syracuseStep 2301803 = 3452705) B3452705
theorem B9838529 : Blo 1534464 9838529 := bstep (se 2 (by rfl) ⟨3689448, by rfl⟩ : syracuseStep 9838529 = 7378897) B7378897
theorem B7774217 : Blo 1534464 7774217 := bstep (se 2 (by rfl) ⟨2915331, by rfl⟩ : syracuseStep 7774217 = 5830663) B5830663
theorem B11665457 : Blo 1534464 11665457 := bstep (se 2 (by rfl) ⟨4374546, by rfl⟩ : syracuseStep 11665457 = 8749093) B8749093
theorem B7774379 : Blo 1534464 7774379 := bstep (se 1 (by rfl) ⟨5830784, by rfl⟩ : syracuseStep 7774379 = 11661569) B11661569
theorem B63029477 : Blo 1534464 63029477 := bstep (se 4 (by rfl) ⟨5909013, by rfl⟩ : syracuseStep 63029477 = 11818027) B11818027
theorem B2302217 : Blo 1534464 2302217 := bstep (se 2 (by rfl) ⟨863331, by rfl⟩ : syracuseStep 2302217 = 1726663) B1726663
theorem B2302319 : Blo 1534464 2302319 := bstep (se 1 (by rfl) ⟨1726739, by rfl⟩ : syracuseStep 2302319 = 3453479) B3453479
theorem B2302535 : Blo 1534464 2302535 := bstep (se 1 (by rfl) ⟨1726901, by rfl⟩ : syracuseStep 2302535 = 3453803) B3453803
theorem B2302571 : Blo 1534464 2302571 := bstep (se 1 (by rfl) ⟨1726928, by rfl⟩ : syracuseStep 2302571 = 3453857) B3453857
theorem B5055097 : Blo 1534464 5055097 := bstep (se 2 (by rfl) ⟨1895661, by rfl⟩ : syracuseStep 5055097 = 3791323) B3791323
theorem B7774865 : Blo 1534464 7774865 := bstep (se 2 (by rfl) ⟨2915574, by rfl⟩ : syracuseStep 7774865 = 5831149) B5831149
theorem B3687095 : Blo 1534464 3687095 := bstep (se 1 (by rfl) ⟨2765321, by rfl⟩ : syracuseStep 3687095 = 5530643) B5530643
theorem B1942319 : Blo 1534464 1942319 := bstep (se 1 (by rfl) ⟨1456739, by rfl⟩ : syracuseStep 1942319 = 2913479) B2913479
theorem B13124429 : Blo 1534464 13124429 := bstep (se 3 (by rfl) ⟨2460830, by rfl⟩ : syracuseStep 13124429 = 4921661) B4921661
theorem B2302799 : Blo 1534464 2302799 := bstep (se 1 (by rfl) ⟨1727099, by rfl⟩ : syracuseStep 2302799 = 3454199) B3454199
theorem B9839555 : Blo 1534464 9839555 := bstep (se 1 (by rfl) ⟨7379666, by rfl⟩ : syracuseStep 9839555 = 14759333) B14759333
theorem B2589671 : Blo 1534464 2589671 := bstep (se 1 (by rfl) ⟨1942253, by rfl⟩ : syracuseStep 2589671 = 3884507) B3884507
theorem B3277921 : Blo 1534464 3277921 := bstep (se 2 (by rfl) ⟨1229220, by rfl⟩ : syracuseStep 3277921 = 2458441) B2458441
theorem B2303195 : Blo 1534464 2303195 := bstep (se 1 (by rfl) ⟨1727396, by rfl⟩ : syracuseStep 2303195 = 3454793) B3454793
theorem B2303369 : Blo 1534464 2303369 := bstep (se 2 (by rfl) ⟨863763, by rfl⟩ : syracuseStep 2303369 = 1727527) B1727527
theorem B3278279 : Blo 1534464 3278279 := bstep (se 1 (by rfl) ⟨2458709, by rfl⟩ : syracuseStep 3278279 = 4917419) B4917419
theorem B3884537 : Blo 1534464 3884537 := bstep (se 2 (by rfl) ⟨1456701, by rfl⟩ : syracuseStep 3884537 = 2913403) B2913403
theorem B30336599 : Blo 1534464 30336599 := bstep (se 1 (by rfl) ⟨22752449, by rfl⟩ : syracuseStep 30336599 = 45504899) B45504899
theorem B2303723 : Blo 1534464 2303723 := bstep (se 1 (by rfl) ⟨1727792, by rfl⟩ : syracuseStep 2303723 = 3455585) B3455585
theorem B3278647 : Blo 1534464 3278647 := bstep (se 1 (by rfl) ⟨2458985, by rfl⟩ : syracuseStep 3278647 = 4917971) B4917971
theorem B8742761 : Blo 1534464 8742761 := bstep (se 2 (by rfl) ⟨3278535, by rfl⟩ : syracuseStep 8742761 = 6557071) B6557071
theorem B2303951 : Blo 1534464 2303951 := bstep (se 1 (by rfl) ⟨1727963, by rfl⟩ : syracuseStep 2303951 = 3455927) B3455927
theorem B5826593 : Blo 1534464 5826593 := bstep (se 2 (by rfl) ⟨2184972, by rfl⟩ : syracuseStep 5826593 = 4369945) B4369945
theorem B2590825 : Blo 1534464 2590825 := bstep (se 2 (by rfl) ⟨971559, by rfl⟩ : syracuseStep 2590825 = 1943119) B1943119
theorem B3885185 : Blo 1534464 3885185 := bstep (se 2 (by rfl) ⟨1456944, by rfl⟩ : syracuseStep 3885185 = 2913889) B2913889
theorem B13125827 : Blo 1534464 13125827 := bstep (se 1 (by rfl) ⟨9844370, by rfl⟩ : syracuseStep 13125827 = 19688741) B19688741
theorem B2304347 : Blo 1534464 2304347 := bstep (se 1 (by rfl) ⟨1728260, by rfl⟩ : syracuseStep 2304347 = 3456521) B3456521
theorem B3885479 : Blo 1534464 3885479 := bstep (se 1 (by rfl) ⟨2914109, by rfl⟩ : syracuseStep 3885479 = 5828219) B5828219
theorem B9341351 : Blo 1534464 9341351 := bstep (se 1 (by rfl) ⟨7006013, by rfl⟩ : syracuseStep 9341351 = 14012027) B14012027
theorem B3500471 : Blo 1534464 3500471 := bstep (se 1 (by rfl) ⟨2625353, by rfl⟩ : syracuseStep 3500471 = 5250707) B5250707
theorem B1534527 : Blo 1534464 1534527 := bstep (se 1 (by rfl) ⟨1150895, by rfl⟩ : syracuseStep 1534527 = 2301791) B2301791
theorem B2304575 : Blo 1534464 2304575 := bstep (se 1 (by rfl) ⟨1728431, by rfl⟩ : syracuseStep 2304575 = 3456863) B3456863
theorem B1534535 : Blo 1534464 1534535 := bstep (se 1 (by rfl) ⟨1150901, by rfl⟩ : syracuseStep 1534535 = 2301803) B2301803
theorem B3885641 : Blo 1534464 3885641 := bstep (se 2 (by rfl) ⟨1457115, by rfl⟩ : syracuseStep 3885641 = 2914231) B2914231
theorem B3279467 : Blo 1534464 3279467 := bstep (se 1 (by rfl) ⟨2459600, by rfl⟩ : syracuseStep 3279467 = 4919201) B4919201
theorem B5827247 : Blo 1534464 5827247 := bstep (se 1 (by rfl) ⟨4370435, by rfl⟩ : syracuseStep 5827247 = 8740871) B8740871
theorem B2304695 : Blo 1534464 2304695 := bstep (se 1 (by rfl) ⟨1728521, by rfl⟩ : syracuseStep 2304695 = 3457043) B3457043
theorem B13109971 : Blo 1534464 13109971 := bstep (se 1 (by rfl) ⟨9832478, by rfl⟩ : syracuseStep 13109971 = 19664957) B19664957
theorem B1534687 : Blo 1534464 1534687 := bstep (se 1 (by rfl) ⟨1151015, by rfl⟩ : syracuseStep 1534687 = 2302031) B2302031
theorem B1534767 : Blo 1534464 1534767 := bstep (se 1 (by rfl) ⟨1151075, by rfl⟩ : syracuseStep 1534767 = 2302151) B2302151
theorem B37849949 : Blo 1534464 37849949 := bstep (se 3 (by rfl) ⟨7096865, by rfl⟩ : syracuseStep 37849949 = 14193731) B14193731
theorem B1534875 : Blo 1534464 1534875 := bstep (se 1 (by rfl) ⟨1151156, by rfl⟩ : syracuseStep 1534875 = 2302313) B2302313
theorem B3885995 : Blo 1534464 3885995 := bstep (se 1 (by rfl) ⟨2914496, by rfl⟩ : syracuseStep 3885995 = 5828993) B5828993
theorem B1534927 : Blo 1534464 1534927 := bstep (se 1 (by rfl) ⟨1151195, by rfl⟩ : syracuseStep 1534927 = 2302391) B2302391
theorem B1534951 : Blo 1534464 1534951 := bstep (se 1 (by rfl) ⟨1151213, by rfl⟩ : syracuseStep 1534951 = 2302427) B2302427
theorem B7777295 : Blo 1534464 7777295 := bstep (se 1 (by rfl) ⟨5832971, by rfl⟩ : syracuseStep 7777295 = 11665943) B11665943
theorem B3886177 : Blo 1534464 3886177 := bstep (se 2 (by rfl) ⟨1457316, by rfl⟩ : syracuseStep 3886177 = 2914633) B2914633
theorem B14765327 : Blo 1534464 14765327 := bstep (se 1 (by rfl) ⟨11073995, by rfl⟩ : syracuseStep 14765327 = 22147991) B22147991
theorem B1535263 : Blo 1534464 1535263 := bstep (se 1 (by rfl) ⟨1151447, by rfl⟩ : syracuseStep 1535263 = 2302895) B2302895
theorem B1535323 : Blo 1534464 1535323 := bstep (se 1 (by rfl) ⟨1151492, by rfl⟩ : syracuseStep 1535323 = 2302985) B2302985
theorem B1535343 : Blo 1534464 1535343 := bstep (se 1 (by rfl) ⟨1151507, by rfl⟩ : syracuseStep 1535343 = 2303015) B2303015
theorem B13299059 : Blo 1534464 13299059 := bstep (se 1 (by rfl) ⟨9974294, by rfl⟩ : syracuseStep 13299059 = 19948589) B19948589
theorem B119639425 : Blo 1534464 119639425 := bstep (se 2 (by rfl) ⟨44864784, by rfl⟩ : syracuseStep 119639425 = 89729569) B89729569
theorem B1535399 : Blo 1534464 1535399 := bstep (se 1 (by rfl) ⟨1151549, by rfl⟩ : syracuseStep 1535399 = 2303099) B2303099
theorem B4148729 : Blo 1534464 4148729 := bstep (se 2 (by rfl) ⟨1555773, by rfl⟩ : syracuseStep 4148729 = 3111547) B3111547
theorem B5180921 : Blo 1534464 5180921 := bstep (se 2 (by rfl) ⟨1942845, by rfl⟩ : syracuseStep 5180921 = 3885691) B3885691
theorem B1535483 : Blo 1534464 1535483 := bstep (se 1 (by rfl) ⟨1151612, by rfl⟩ : syracuseStep 1535483 = 2303225) B2303225
theorem B1535551 : Blo 1534464 1535551 := bstep (se 1 (by rfl) ⟨1151663, by rfl⟩ : syracuseStep 1535551 = 2303327) B2303327
theorem B1535559 : Blo 1534464 1535559 := bstep (se 1 (by rfl) ⟨1151669, by rfl⟩ : syracuseStep 1535559 = 2303339) B2303339
theorem B7769681 : Blo 1534464 7769681 := bstep (se 2 (by rfl) ⟨2913630, by rfl⟩ : syracuseStep 7769681 = 5827261) B5827261
theorem B4206163 : Blo 1534464 4206163 := bstep (se 1 (by rfl) ⟨3154622, by rfl⟩ : syracuseStep 4206163 = 6309245) B6309245
theorem B6557345 : Blo 1534464 6557345 := bstep (se 2 (by rfl) ⟨2459004, by rfl⟩ : syracuseStep 6557345 = 4918009) B4918009
theorem B1535711 : Blo 1534464 1535711 := bstep (se 1 (by rfl) ⟨1151783, by rfl⟩ : syracuseStep 1535711 = 2303567) B2303567
theorem B3452651 : Blo 1534464 3452651 := bstep (se 1 (by rfl) ⟨2589488, by rfl⟩ : syracuseStep 3452651 = 5178977) B5178977
theorem B5181191 : Blo 1534464 5181191 := bstep (se 1 (by rfl) ⟨3885893, by rfl⟩ : syracuseStep 5181191 = 7771787) B7771787
theorem B2592553 : Blo 1534464 2592553 := bstep (se 2 (by rfl) ⟨972207, by rfl⟩ : syracuseStep 2592553 = 1944415) B1944415
theorem B1535791 : Blo 1534464 1535791 := bstep (se 1 (by rfl) ⟨1151843, by rfl⟩ : syracuseStep 1535791 = 2303687) B2303687
theorem B7778105 : Blo 1534464 7778105 := bstep (se 2 (by rfl) ⟨2916789, by rfl⟩ : syracuseStep 7778105 = 5833579) B5833579
theorem B5181245 : Blo 1534464 5181245 := bstep (se 3 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 5181245 = 1942967) B1942967
theorem B3452777 : Blo 1534464 3452777 := bstep (se 2 (by rfl) ⟨1294791, by rfl⟩ : syracuseStep 3452777 = 2589583) B2589583
theorem B1535899 : Blo 1534464 1535899 := bstep (se 1 (by rfl) ⟨1151924, by rfl⟩ : syracuseStep 1535899 = 2303849) B2303849
theorem B1535951 : Blo 1534464 1535951 := bstep (se 1 (by rfl) ⟨1151963, by rfl⟩ : syracuseStep 1535951 = 2303927) B2303927
theorem B1535975 : Blo 1534464 1535975 := bstep (se 1 (by rfl) ⟨1151981, by rfl⟩ : syracuseStep 1535975 = 2303963) B2303963
theorem B6557705 : Blo 1534464 6557705 := bstep (se 2 (by rfl) ⟨2459139, by rfl⟩ : syracuseStep 6557705 = 4918279) B4918279
theorem B14749721 : Blo 1534464 14749721 := bstep (se 2 (by rfl) ⟨5531145, by rfl⟩ : syracuseStep 14749721 = 11062291) B11062291
theorem B3887129 : Blo 1534464 3887129 := bstep (se 2 (by rfl) ⟨1457673, by rfl⟩ : syracuseStep 3887129 = 2915347) B2915347
theorem B4370537 : Blo 1534464 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B1536287 : Blo 1534464 1536287 := bstep (se 1 (by rfl) ⟨1152215, by rfl⟩ : syracuseStep 1536287 = 2304431) B2304431
theorem B1536347 : Blo 1534464 1536347 := bstep (se 1 (by rfl) ⟨1152260, by rfl⟩ : syracuseStep 1536347 = 2304521) B2304521
theorem B1536367 : Blo 1534464 1536367 := bstep (se 1 (by rfl) ⟨1152275, by rfl⟩ : syracuseStep 1536367 = 2304551) B2304551
theorem B26235251 : Blo 1534464 26235251 := bstep (se 1 (by rfl) ⟨19676438, by rfl⟩ : syracuseStep 26235251 = 39352877) B39352877
theorem B37884293 : Blo 1534464 37884293 := bstep (se 4 (by rfl) ⟨3551652, by rfl⟩ : syracuseStep 37884293 = 7103305) B7103305
theorem B1536423 : Blo 1534464 1536423 := bstep (se 1 (by rfl) ⟨1152317, by rfl⟩ : syracuseStep 1536423 = 2304635) B2304635
theorem B9843119 : Blo 1534464 9843119 := bstep (se 1 (by rfl) ⟨7382339, by rfl⟩ : syracuseStep 9843119 = 14764679) B14764679
theorem B3887585 : Blo 1534464 3887585 := bstep (se 2 (by rfl) ⟨1457844, by rfl⟩ : syracuseStep 3887585 = 2915689) B2915689
theorem B3887635 : Blo 1534464 3887635 := bstep (se 1 (by rfl) ⟨2915726, by rfl⟩ : syracuseStep 3887635 = 5831453) B5831453
theorem B5829191 : Blo 1534464 5829191 := bstep (se 1 (by rfl) ⟨4371893, by rfl⟩ : syracuseStep 5829191 = 8743787) B8743787
theorem B4919879 : Blo 1534464 4919879 := bstep (se 1 (by rfl) ⟨3689909, by rfl⟩ : syracuseStep 4919879 = 7379819) B7379819
theorem B8303249 : Blo 1534464 8303249 := bstep (se 2 (by rfl) ⟨3113718, by rfl⟩ : syracuseStep 8303249 = 6227437) B6227437
theorem B3453623 : Blo 1534464 3453623 := bstep (se 1 (by rfl) ⟨2590217, by rfl⟩ : syracuseStep 3453623 = 5180435) B5180435
theorem B2765587 : Blo 1534464 2765587 := bstep (se 1 (by rfl) ⟨2074190, by rfl⟩ : syracuseStep 2765587 = 4148381) B4148381
theorem B10654507 : Blo 1534464 10654507 := bstep (se 1 (by rfl) ⟨7990880, by rfl⟩ : syracuseStep 10654507 = 15981761) B15981761
theorem B7377743 : Blo 1534464 7377743 := bstep (se 1 (by rfl) ⟨5533307, by rfl⟩ : syracuseStep 7377743 = 11066615) B11066615
theorem B3453839 : Blo 1534464 3453839 := bstep (se 1 (by rfl) ⟨2590379, by rfl⟩ : syracuseStep 3453839 = 5180759) B5180759
theorem B59839661 : Blo 1534464 59839661 := bstep (se 3 (by rfl) ⟨11219936, by rfl⟩ : syracuseStep 59839661 = 22439873) B22439873
theorem B5321971 : Blo 1534464 5321971 := bstep (se 1 (by rfl) ⟨3991478, by rfl⟩ : syracuseStep 5321971 = 7982957) B7982957
theorem B6559019 : Blo 1534464 6559019 := bstep (se 1 (by rfl) ⟨4919264, by rfl⟩ : syracuseStep 6559019 = 9838529) B9838529
theorem B14751179 : Blo 1534464 14751179 := bstep (se 1 (by rfl) ⟨11063384, by rfl⟩ : syracuseStep 14751179 = 22126769) B22126769
theorem B3454559 : Blo 1534464 3454559 := bstep (se 1 (by rfl) ⟨2590919, by rfl⟩ : syracuseStep 3454559 = 5181839) B5181839
theorem B7378589 : Blo 1534464 7378589 := bstep (se 3 (by rfl) ⟨1383485, by rfl⟩ : syracuseStep 7378589 = 2766971) B2766971
theorem B3454775 : Blo 1534464 3454775 := bstep (se 1 (by rfl) ⟨2591081, by rfl⟩ : syracuseStep 3454775 = 5182163) B5182163
theorem B5830481 : Blo 1534464 5830481 := bstep (se 2 (by rfl) ⟨2186430, by rfl⟩ : syracuseStep 5830481 = 4372861) B4372861
theorem B11368279 : Blo 1534464 11368279 := bstep (se 1 (by rfl) ⟨8526209, by rfl⟩ : syracuseStep 11368279 = 17052419) B17052419
theorem B7772111 : Blo 1534464 7772111 := bstep (se 1 (by rfl) ⟨5829083, by rfl⟩ : syracuseStep 7772111 = 11658167) B11658167
theorem B3455081 : Blo 1534464 3455081 := bstep (se 2 (by rfl) ⟨1295655, by rfl⟩ : syracuseStep 3455081 = 2591311) B2591311
theorem B5830937 : Blo 1534464 5830937 := bstep (se 2 (by rfl) ⟨2186601, by rfl⟩ : syracuseStep 5830937 = 4373203) B4373203
theorem B4208969 : Blo 1534464 4208969 := bstep (se 2 (by rfl) ⟨1578363, by rfl⟩ : syracuseStep 4208969 = 3156727) B3156727
theorem B1726843 : Blo 1534464 1726843 := bstep (se 1 (by rfl) ⟨1295132, by rfl⟩ : syracuseStep 1726843 = 2590265) B2590265
theorem B8296847 : Blo 1534464 8296847 := bstep (se 1 (by rfl) ⟨6222635, by rfl⟩ : syracuseStep 8296847 = 12445271) B12445271
theorem B4372987 : Blo 1534464 4372987 := bstep (se 1 (by rfl) ⟨3279740, by rfl⟩ : syracuseStep 4372987 = 6559481) B6559481
theorem B3455567 : Blo 1534464 3455567 := bstep (se 1 (by rfl) ⟨2591675, by rfl⟩ : syracuseStep 3455567 = 5183351) B5183351
theorem B5184107 : Blo 1534464 5184107 := bstep (se 1 (by rfl) ⟨3888080, by rfl⟩ : syracuseStep 5184107 = 7776161) B7776161
theorem B2914937 : Blo 1534464 2914937 := bstep (se 2 (by rfl) ⟨1093101, by rfl⟩ : syracuseStep 2914937 = 2186203) B2186203
theorem B5536451 : Blo 1534464 5536451 := bstep (se 1 (by rfl) ⟨4152338, by rfl⟩ : syracuseStep 5536451 = 8304677) B8304677
theorem B3455711 : Blo 1534464 3455711 := bstep (se 1 (by rfl) ⟨2591783, by rfl⟩ : syracuseStep 3455711 = 5183567) B5183567
theorem B1727311 : Blo 1534464 1727311 := bstep (se 1 (by rfl) ⟨1295483, by rfl⟩ : syracuseStep 1727311 = 2590967) B2590967
theorem B7773083 : Blo 1534464 7773083 := bstep (se 1 (by rfl) ⟨5829812, by rfl⟩ : syracuseStep 7773083 = 11659625) B11659625
theorem B3455963 : Blo 1534464 3455963 := bstep (se 1 (by rfl) ⟨2591972, by rfl⟩ : syracuseStep 3455963 = 5183945) B5183945
theorem B3456143 : Blo 1534464 3456143 := bstep (se 1 (by rfl) ⟨2592107, by rfl⟩ : syracuseStep 3456143 = 5184215) B5184215
theorem B5184701 : Blo 1534464 5184701 := bstep (se 3 (by rfl) ⟨972131, by rfl⟩ : syracuseStep 5184701 = 1944263) B1944263
theorem B1727707 : Blo 1534464 1727707 := bstep (se 1 (by rfl) ⟨1295780, by rfl⟩ : syracuseStep 1727707 = 2591561) B2591561
theorem B3456233 : Blo 1534464 3456233 := bstep (se 2 (by rfl) ⟨1296087, by rfl⟩ : syracuseStep 3456233 = 2592175) B2592175
theorem B3456287 : Blo 1534464 3456287 := bstep (se 1 (by rfl) ⟨2592215, by rfl⟩ : syracuseStep 3456287 = 5184431) B5184431
theorem B8740163 : Blo 1534464 8740163 := bstep (se 1 (by rfl) ⟨6555122, by rfl⟩ : syracuseStep 8740163 = 13110245) B13110245
theorem B6561121 : Blo 1534464 6561121 := bstep (se 2 (by rfl) ⟨2460420, by rfl⟩ : syracuseStep 6561121 = 4920841) B4920841
theorem B7773569 : Blo 1534464 7773569 := bstep (se 2 (by rfl) ⟨2915088, by rfl⟩ : syracuseStep 7773569 = 5830177) B5830177
theorem B2768327 : Blo 1534464 2768327 := bstep (se 1 (by rfl) ⟨2076245, by rfl⟩ : syracuseStep 2768327 = 4152491) B4152491
theorem B14040535 : Blo 1534464 14040535 := bstep (se 1 (by rfl) ⟨10530401, by rfl⟩ : syracuseStep 14040535 = 21060803) B21060803
theorem B8740345 : Blo 1534464 8740345 := bstep (se 2 (by rfl) ⟨3277629, by rfl⟩ : syracuseStep 8740345 = 6555259) B6555259
theorem B2915833 : Blo 1534464 2915833 := bstep (se 2 (by rfl) ⟨1093437, by rfl⟩ : syracuseStep 2915833 = 2186875) B2186875
theorem B1727995 : Blo 1534464 1727995 := bstep (se 1 (by rfl) ⟨1295996, by rfl⟩ : syracuseStep 1727995 = 2591993) B2591993
theorem B119709251 : Blo 1534464 119709251 := bstep (se 1 (by rfl) ⟨89781938, by rfl⟩ : syracuseStep 119709251 = 179563877) B179563877
theorem B6561395 : Blo 1534464 6561395 := bstep (se 1 (by rfl) ⟨4921046, by rfl⟩ : syracuseStep 6561395 = 9842093) B9842093
theorem B1728175 : Blo 1534464 1728175 := bstep (se 1 (by rfl) ⟨1296131, by rfl⟩ : syracuseStep 1728175 = 2592263) B2592263
theorem B2301737 : Blo 1534464 2301737 := bstep (se 2 (by rfl) ⟨863151, by rfl⟩ : syracuseStep 2301737 = 1726303) B1726303
theorem B2916137 : Blo 1534464 2916137 := bstep (se 2 (by rfl) ⟨1093551, by rfl⟩ : syracuseStep 2916137 = 2187103) B2187103
theorem B3456809 : Blo 1534464 3456809 := bstep (se 2 (by rfl) ⟨1296303, by rfl⟩ : syracuseStep 3456809 = 2592607) B2592607
theorem B2301743 : Blo 1534464 2301743 := bstep (se 1 (by rfl) ⟨1726307, by rfl⟩ : syracuseStep 2301743 = 3452615) B3452615
theorem B2334511 : Blo 1534464 2334511 := bstep (se 1 (by rfl) ⟨1750883, by rfl⟩ : syracuseStep 2334511 = 3501767) B3501767
theorem B4374319 : Blo 1534464 4374319 := bstep (se 1 (by rfl) ⟨3280739, by rfl⟩ : syracuseStep 4374319 = 6561479) B6561479
theorem B14196539 : Blo 1534464 14196539 := bstep (se 1 (by rfl) ⟨10647404, by rfl⟩ : syracuseStep 14196539 = 21294809) B21294809
theorem B16596809 : Blo 1534464 16596809 := bstep (se 2 (by rfl) ⟨6223803, by rfl⟩ : syracuseStep 16596809 = 12447607) B12447607
theorem B1728463 : Blo 1534464 1728463 := bstep (se 1 (by rfl) ⟨1296347, by rfl⟩ : syracuseStep 1728463 = 2592695) B2592695
theorem B17490167 : Blo 1534464 17490167 := bstep (se 1 (by rfl) ⟨13117625, by rfl⟩ : syracuseStep 17490167 = 26235251) B26235251
theorem B25256195 : Blo 1534464 25256195 := bstep (se 1 (by rfl) ⟨18942146, by rfl⟩ : syracuseStep 25256195 = 37884293) B37884293
theorem B6562079 : Blo 1534464 6562079 := bstep (se 1 (by rfl) ⟨4921559, by rfl⟩ : syracuseStep 6562079 = 9843119) B9843119
theorem B159572429 : Blo 1534464 159572429 := bstep (se 3 (by rfl) ⟨29919830, by rfl⟩ : syracuseStep 159572429 = 59839661) B59839661
theorem B2458063 : Blo 1534464 2458063 := bstep (se 1 (by rfl) ⟨1843547, by rfl⟩ : syracuseStep 2458063 = 3687095) B3687095
theorem B2302415 : Blo 1534464 2302415 := bstep (se 1 (by rfl) ⟨1726811, by rfl⟩ : syracuseStep 2302415 = 3453623) B3453623
theorem B2302457 : Blo 1534464 2302457 := bstep (se 2 (by rfl) ⟨863421, by rfl⟩ : syracuseStep 2302457 = 1726843) B1726843
theorem B8749619 : Blo 1534464 8749619 := bstep (se 1 (by rfl) ⟨6562214, by rfl⟩ : syracuseStep 8749619 = 13124429) B13124429
theorem B2302559 : Blo 1534464 2302559 := bstep (se 1 (by rfl) ⟨1726919, by rfl⟩ : syracuseStep 2302559 = 3453839) B3453839
theorem B11223917 : Blo 1534464 11223917 := bstep (se 3 (by rfl) ⟨2104484, by rfl⟩ : syracuseStep 11223917 = 4208969) B4208969
theorem B2589691 : Blo 1534464 2589691 := bstep (se 1 (by rfl) ⟨1942268, by rfl⟩ : syracuseStep 2589691 = 3884537) B3884537
theorem B3687449 : Blo 1534464 3687449 := bstep (se 2 (by rfl) ⟨1382793, by rfl⟩ : syracuseStep 3687449 = 2765587) B2765587
theorem B2303039 : Blo 1534464 2303039 := bstep (se 1 (by rfl) ⟨1727279, by rfl⟩ : syracuseStep 2303039 = 3454559) B3454559
theorem B2303081 : Blo 1534464 2303081 := bstep (se 2 (by rfl) ⟨863655, by rfl⟩ : syracuseStep 2303081 = 1727311) B1727311
theorem B8742077 : Blo 1534464 8742077 := bstep (se 3 (by rfl) ⟨1639139, by rfl⟩ : syracuseStep 8742077 = 3278279) B3278279
theorem B2303183 : Blo 1534464 2303183 := bstep (se 1 (by rfl) ⟨1727387, by rfl⟩ : syracuseStep 2303183 = 3454775) B3454775
theorem B3884395 : Blo 1534464 3884395 := bstep (se 1 (by rfl) ⟨2913296, by rfl⟩ : syracuseStep 3884395 = 5826593) B5826593
theorem B2303387 : Blo 1534464 2303387 := bstep (se 1 (by rfl) ⟨1727540, by rfl⟩ : syracuseStep 2303387 = 3455081) B3455081
theorem B2590123 : Blo 1534464 2590123 := bstep (se 1 (by rfl) ⟨1942592, by rfl⟩ : syracuseStep 2590123 = 3885185) B3885185
theorem B8750551 : Blo 1534464 8750551 := bstep (se 1 (by rfl) ⟨6562913, by rfl⟩ : syracuseStep 8750551 = 13125827) B13125827
theorem B5531231 : Blo 1534464 5531231 := bstep (se 1 (by rfl) ⟨4148423, by rfl⟩ : syracuseStep 5531231 = 8296847) B8296847
theorem B2590319 : Blo 1534464 2590319 := bstep (se 1 (by rfl) ⟨1942739, by rfl⟩ : syracuseStep 2590319 = 3885479) B3885479
theorem B6227567 : Blo 1534464 6227567 := bstep (se 1 (by rfl) ⟨4670675, by rfl⟩ : syracuseStep 6227567 = 9341351) B9341351
theorem B2303609 : Blo 1534464 2303609 := bstep (se 2 (by rfl) ⟨863853, by rfl⟩ : syracuseStep 2303609 = 1727707) B1727707
theorem B7095961 : Blo 1534464 7095961 := bstep (se 2 (by rfl) ⟨2660985, by rfl⟩ : syracuseStep 7095961 = 5321971) B5321971
theorem B2590427 : Blo 1534464 2590427 := bstep (se 1 (by rfl) ⟨1942820, by rfl⟩ : syracuseStep 2590427 = 3885641) B3885641
theorem B2303711 : Blo 1534464 2303711 := bstep (se 1 (by rfl) ⟨1727783, by rfl⟩ : syracuseStep 2303711 = 3455567) B3455567
theorem B1943291 : Blo 1534464 1943291 := bstep (se 1 (by rfl) ⟨1457468, by rfl⟩ : syracuseStep 1943291 = 2914937) B2914937
theorem B3884831 : Blo 1534464 3884831 := bstep (se 1 (by rfl) ⟨2913623, by rfl⟩ : syracuseStep 3884831 = 5827247) B5827247
theorem B2303807 : Blo 1534464 2303807 := bstep (se 1 (by rfl) ⟨1727855, by rfl⟩ : syracuseStep 2303807 = 3455711) B3455711
theorem B14763869 : Blo 1534464 14763869 := bstep (se 3 (by rfl) ⟨2768225, by rfl⟩ : syracuseStep 14763869 = 5536451) B5536451
theorem B25233299 : Blo 1534464 25233299 := bstep (se 1 (by rfl) ⟨18924974, by rfl⟩ : syracuseStep 25233299 = 37849949) B37849949
theorem B2590663 : Blo 1534464 2590663 := bstep (se 1 (by rfl) ⟨1942997, by rfl⟩ : syracuseStep 2590663 = 3885995) B3885995
theorem B18720713 : Blo 1534464 18720713 := bstep (se 2 (by rfl) ⟨7020267, by rfl⟩ : syracuseStep 18720713 = 14040535) B14040535
theorem B2303975 : Blo 1534464 2303975 := bstep (se 1 (by rfl) ⟨1727981, by rfl⟩ : syracuseStep 2303975 = 3455963) B3455963
theorem B2303993 : Blo 1534464 2303993 := bstep (se 2 (by rfl) ⟨863997, by rfl⟩ : syracuseStep 2303993 = 1727995) B1727995
theorem B2304095 : Blo 1534464 2304095 := bstep (se 1 (by rfl) ⟨1728071, by rfl⟩ : syracuseStep 2304095 = 3456143) B3456143
theorem B5179517 : Blo 1534464 5179517 := bstep (se 3 (by rfl) ⟨971159, by rfl⟩ : syracuseStep 5179517 = 1942319) B1942319
theorem B2304155 : Blo 1534464 2304155 := bstep (se 1 (by rfl) ⟨1728116, by rfl⟩ : syracuseStep 2304155 = 3456233) B3456233
theorem B2304191 : Blo 1534464 2304191 := bstep (se 1 (by rfl) ⟨1728143, by rfl⟩ : syracuseStep 2304191 = 3456287) B3456287
theorem B5826775 : Blo 1534464 5826775 := bstep (se 1 (by rfl) ⟨4370081, by rfl⟩ : syracuseStep 5826775 = 8740163) B8740163
theorem B2304233 : Blo 1534464 2304233 := bstep (se 2 (by rfl) ⟨864087, by rfl⟩ : syracuseStep 2304233 = 1728175) B1728175
theorem B8866039 : Blo 1534464 8866039 := bstep (se 1 (by rfl) ⟨6649529, by rfl⟩ : syracuseStep 8866039 = 13299059) B13299059
theorem B1845551 : Blo 1534464 1845551 := bstep (se 1 (by rfl) ⟨1384163, by rfl⟩ : syracuseStep 1845551 = 2768327) B2768327
theorem B5179787 : Blo 1534464 5179787 := bstep (se 1 (by rfl) ⟨3884840, by rfl⟩ : syracuseStep 5179787 = 7769681) B7769681
theorem B15157705 : Blo 1534464 15157705 := bstep (se 2 (by rfl) ⟨5684139, by rfl⟩ : syracuseStep 15157705 = 11368279) B11368279
theorem B1534491 : Blo 1534464 1534491 := bstep (se 1 (by rfl) ⟨1150868, by rfl⟩ : syracuseStep 1534491 = 2301737) B2301737
theorem B1944091 : Blo 1534464 1944091 := bstep (se 1 (by rfl) ⟨1458068, by rfl⟩ : syracuseStep 1944091 = 2916137) B2916137
theorem B2304539 : Blo 1534464 2304539 := bstep (se 1 (by rfl) ⟨1728404, by rfl⟩ : syracuseStep 2304539 = 3456809) B3456809
theorem B1534495 : Blo 1534464 1534495 := bstep (se 1 (by rfl) ⟨1150871, by rfl⟩ : syracuseStep 1534495 = 2301743) B2301743
theorem B9464359 : Blo 1534464 9464359 := bstep (se 1 (by rfl) ⟨7098269, by rfl⟩ : syracuseStep 9464359 = 14196539) B14196539
theorem B2304617 : Blo 1534464 2304617 := bstep (se 2 (by rfl) ⟨864231, by rfl⟩ : syracuseStep 2304617 = 1728463) B1728463
theorem B9833147 : Blo 1534464 9833147 := bstep (se 1 (by rfl) ⟨7374860, by rfl⟩ : syracuseStep 9833147 = 14749721) B14749721
theorem B2591419 : Blo 1534464 2591419 := bstep (se 1 (by rfl) ⟨1943564, by rfl⟩ : syracuseStep 2591419 = 3887129) B3887129
theorem B7776971 : Blo 1534464 7776971 := bstep (se 1 (by rfl) ⟨5832728, by rfl⟩ : syracuseStep 7776971 = 11665457) B11665457
theorem B42019651 : Blo 1534464 42019651 := bstep (se 1 (by rfl) ⟨31514738, by rfl⟩ : syracuseStep 42019651 = 63029477) B63029477
theorem B1534811 : Blo 1534464 1534811 := bstep (se 1 (by rfl) ⟨1151108, by rfl⟩ : syracuseStep 1534811 = 2302217) B2302217
theorem B1534879 : Blo 1534464 1534879 := bstep (se 1 (by rfl) ⟨1151159, by rfl⟩ : syracuseStep 1534879 = 2302319) B2302319
theorem B2591723 : Blo 1534464 2591723 := bstep (se 1 (by rfl) ⟨1943792, by rfl⟩ : syracuseStep 2591723 = 3887585) B3887585
theorem B1535023 : Blo 1534464 1535023 := bstep (se 1 (by rfl) ⟨1151267, by rfl⟩ : syracuseStep 1535023 = 2302535) B2302535
theorem B3886127 : Blo 1534464 3886127 := bstep (se 1 (by rfl) ⟨2914595, by rfl⟩ : syracuseStep 3886127 = 5829191) B5829191
theorem B1535047 : Blo 1534464 1535047 := bstep (se 1 (by rfl) ⟨1151285, by rfl⟩ : syracuseStep 1535047 = 2302571) B2302571
theorem B1535199 : Blo 1534464 1535199 := bstep (se 1 (by rfl) ⟨1151399, by rfl⟩ : syracuseStep 1535199 = 2302799) B2302799
theorem B4918495 : Blo 1534464 4918495 := bstep (se 1 (by rfl) ⟨3688871, by rfl⟩ : syracuseStep 4918495 = 7377743) B7377743
theorem B1535463 : Blo 1534464 1535463 := bstep (se 1 (by rfl) ⟨1151597, by rfl⟩ : syracuseStep 1535463 = 2303195) B2303195
theorem B1535579 : Blo 1534464 1535579 := bstep (se 1 (by rfl) ⟨1151684, by rfl⟩ : syracuseStep 1535579 = 2303369) B2303369
theorem B9834119 : Blo 1534464 9834119 := bstep (se 1 (by rfl) ⟨7375589, by rfl⟩ : syracuseStep 9834119 = 14751179) B14751179
theorem B4919059 : Blo 1534464 4919059 := bstep (se 1 (by rfl) ⟨3689294, by rfl⟩ : syracuseStep 4919059 = 7378589) B7378589
theorem B1535815 : Blo 1534464 1535815 := bstep (se 1 (by rfl) ⟨1151861, by rfl⟩ : syracuseStep 1535815 = 2303723) B2303723
theorem B3886987 : Blo 1534464 3886987 := bstep (se 1 (by rfl) ⟨2915240, by rfl⟩ : syracuseStep 3886987 = 5830481) B5830481
theorem B5828507 : Blo 1534464 5828507 := bstep (se 1 (by rfl) ⟨4371380, by rfl⟩ : syracuseStep 5828507 = 8742761) B8742761
theorem B5181407 : Blo 1534464 5181407 := bstep (se 1 (by rfl) ⟨3886055, by rfl⟩ : syracuseStep 5181407 = 7772111) B7772111
theorem B1535967 : Blo 1534464 1535967 := bstep (se 1 (by rfl) ⟨1151975, by rfl⟩ : syracuseStep 1535967 = 2303951) B2303951
theorem B4370561 : Blo 1534464 4370561 := bstep (se 2 (by rfl) ⟨1638960, by rfl⟩ : syracuseStep 4370561 = 3277921) B3277921
theorem B5181569 : Blo 1534464 5181569 := bstep (se 2 (by rfl) ⟨1943088, by rfl⟩ : syracuseStep 5181569 = 3886177) B3886177
theorem B3887291 : Blo 1534464 3887291 := bstep (se 1 (by rfl) ⟨2915468, by rfl⟩ : syracuseStep 3887291 = 5830937) B5830937
theorem B13119677 : Blo 1534464 13119677 := bstep (se 3 (by rfl) ⟨2459939, by rfl⟩ : syracuseStep 13119677 = 4919879) B4919879
theorem B56824037 : Blo 1534464 56824037 := bstep (se 4 (by rfl) ⟨5327253, by rfl⟩ : syracuseStep 56824037 = 10654507) B10654507
theorem B1536231 : Blo 1534464 1536231 := bstep (se 1 (by rfl) ⟨1152173, by rfl⟩ : syracuseStep 1536231 = 2304347) B2304347
theorem B8745245 : Blo 1534464 8745245 := bstep (se 3 (by rfl) ⟨1639733, by rfl⟩ : syracuseStep 8745245 = 3279467) B3279467
theorem B1536383 : Blo 1534464 1536383 := bstep (se 1 (by rfl) ⟨1152287, by rfl⟩ : syracuseStep 1536383 = 2304575) B2304575
theorem B1536463 : Blo 1534464 1536463 := bstep (se 1 (by rfl) ⟨1152347, by rfl⟩ : syracuseStep 1536463 = 2304695) B2304695
theorem B159519233 : Blo 1534464 159519233 := bstep (se 2 (by rfl) ⟨59819712, by rfl⟩ : syracuseStep 159519233 = 119639425) B119639425
theorem B5182055 : Blo 1534464 5182055 := bstep (se 1 (by rfl) ⟨3886541, by rfl⟩ : syracuseStep 5182055 = 7773083) B7773083
theorem B11653793 : Blo 1534464 11653793 := bstep (se 2 (by rfl) ⟨4370172, by rfl⟩ : syracuseStep 11653793 = 8740345) B8740345
theorem B3887777 : Blo 1534464 3887777 := bstep (se 2 (by rfl) ⟨1457916, by rfl⟩ : syracuseStep 3887777 = 2915833) B2915833
theorem B5608217 : Blo 1534464 5608217 := bstep (se 2 (by rfl) ⟨2103081, by rfl⟩ : syracuseStep 5608217 = 4206163) B4206163
theorem B9843551 : Blo 1534464 9843551 := bstep (se 1 (by rfl) ⟨7382663, by rfl⟩ : syracuseStep 9843551 = 14765327) B14765327
theorem B5182379 : Blo 1534464 5182379 := bstep (se 1 (by rfl) ⟨3886784, by rfl⟩ : syracuseStep 5182379 = 7773569) B7773569
theorem B2765819 : Blo 1534464 2765819 := bstep (se 1 (by rfl) ⟨2074364, by rfl⟩ : syracuseStep 2765819 = 4148729) B4148729
theorem B3453947 : Blo 1534464 3453947 := bstep (se 1 (by rfl) ⟨2590460, by rfl⟩ : syracuseStep 3453947 = 5180921) B5180921
theorem B4371529 : Blo 1534464 4371529 := bstep (se 2 (by rfl) ⟨1639323, by rfl⟩ : syracuseStep 4371529 = 3278647) B3278647
theorem B4371563 : Blo 1534464 4371563 := bstep (se 1 (by rfl) ⟨3278672, by rfl⟩ : syracuseStep 4371563 = 6557345) B6557345
theorem B3454127 : Blo 1534464 3454127 := bstep (se 1 (by rfl) ⟨2590595, by rfl⟩ : syracuseStep 3454127 = 5181191) B5181191
theorem B3454163 : Blo 1534464 3454163 := bstep (se 1 (by rfl) ⟨2590622, by rfl⟩ : syracuseStep 3454163 = 5181245) B5181245
theorem B11064539 : Blo 1534464 11064539 := bstep (se 1 (by rfl) ⟨8298404, by rfl⟩ : syracuseStep 11064539 = 16596809) B16596809
theorem B4371803 : Blo 1534464 4371803 := bstep (se 1 (by rfl) ⟨3278852, by rfl⟩ : syracuseStep 4371803 = 6557705) B6557705
theorem B5182811 : Blo 1534464 5182811 := bstep (se 1 (by rfl) ⟨3887108, by rfl⟩ : syracuseStep 5182811 = 7774217) B7774217
theorem B5182919 : Blo 1534464 5182919 := bstep (se 1 (by rfl) ⟨3887189, by rfl⟩ : syracuseStep 5182919 = 7774379) B7774379
theorem B3454433 : Blo 1534464 3454433 := bstep (se 2 (by rfl) ⟨1295412, by rfl⟩ : syracuseStep 3454433 = 2590825) B2590825
theorem B11654765 : Blo 1534464 11654765 := bstep (se 3 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 11654765 = 4370537) B4370537
theorem B5183243 : Blo 1534464 5183243 := bstep (se 1 (by rfl) ⟨3887432, by rfl⟩ : syracuseStep 5183243 = 7774865) B7774865
theorem B5535499 : Blo 1534464 5535499 := bstep (se 1 (by rfl) ⟨4151624, by rfl⟩ : syracuseStep 5535499 = 8303249) B8303249
theorem B6559703 : Blo 1534464 6559703 := bstep (se 1 (by rfl) ⟨4919777, by rfl⟩ : syracuseStep 6559703 = 9839555) B9839555
theorem B1726447 : Blo 1534464 1726447 := bstep (se 1 (by rfl) ⟨1294835, by rfl⟩ : syracuseStep 1726447 = 2589671) B2589671
theorem B5830649 : Blo 1534464 5830649 := bstep (se 2 (by rfl) ⟨2186493, by rfl⟩ : syracuseStep 5830649 = 4372987) B4372987
theorem B5183513 : Blo 1534464 5183513 := bstep (se 2 (by rfl) ⟨1943817, by rfl⟩ : syracuseStep 5183513 = 3887635) B3887635
theorem B6740129 : Blo 1534464 6740129 := bstep (se 2 (by rfl) ⟨2527548, by rfl⟩ : syracuseStep 6740129 = 5055097) B5055097
theorem B4372679 : Blo 1534464 4372679 := bstep (se 1 (by rfl) ⟨3279509, by rfl⟩ : syracuseStep 4372679 = 6559019) B6559019
theorem B17479961 : Blo 1534464 17479961 := bstep (se 2 (by rfl) ⟨6554985, by rfl⟩ : syracuseStep 17479961 = 13109971) B13109971
theorem B20224399 : Blo 1534464 20224399 := bstep (se 1 (by rfl) ⟨15168299, by rfl⟩ : syracuseStep 20224399 = 30336599) B30336599
theorem B2333647 : Blo 1534464 2333647 := bstep (se 1 (by rfl) ⟨1750235, by rfl⟩ : syracuseStep 2333647 = 3500471) B3500471
theorem B3456071 : Blo 1534464 3456071 := bstep (se 1 (by rfl) ⟨2592053, by rfl⟩ : syracuseStep 3456071 = 5184107) B5184107
theorem B8748161 : Blo 1534464 8748161 := bstep (se 2 (by rfl) ⟨3280560, by rfl⟩ : syracuseStep 8748161 = 6561121) B6561121
theorem B5184863 : Blo 1534464 5184863 := bstep (se 1 (by rfl) ⟨3888647, by rfl⟩ : syracuseStep 5184863 = 7777295) B7777295
theorem B3456467 : Blo 1534464 3456467 := bstep (se 1 (by rfl) ⟨2592350, by rfl⟩ : syracuseStep 3456467 = 5184701) B5184701
theorem B79806167 : Blo 1534464 79806167 := bstep (se 1 (by rfl) ⟨59854625, by rfl⟩ : syracuseStep 79806167 = 119709251) B119709251
theorem B3456737 : Blo 1534464 3456737 := bstep (se 2 (by rfl) ⟨1296276, by rfl⟩ : syracuseStep 3456737 = 2592553) B2592553
theorem B3112681 : Blo 1534464 3112681 := bstep (se 2 (by rfl) ⟨1167255, by rfl⟩ : syracuseStep 3112681 = 2334511) B2334511
theorem B5832425 : Blo 1534464 5832425 := bstep (se 2 (by rfl) ⟨2187159, by rfl⟩ : syracuseStep 5832425 = 4374319) B4374319
theorem B4374263 : Blo 1534464 4374263 := bstep (se 1 (by rfl) ⟨3280697, by rfl⟩ : syracuseStep 4374263 = 6561395) B6561395
theorem B2301767 : Blo 1534464 2301767 := bstep (se 1 (by rfl) ⟨1726325, by rfl⟩ : syracuseStep 2301767 = 3452651) B3452651
theorem B5185403 : Blo 1534464 5185403 := bstep (se 1 (by rfl) ⟨3889052, by rfl⟩ : syracuseStep 5185403 = 7778105) B7778105
theorem B2301851 : Blo 1534464 2301851 := bstep (se 1 (by rfl) ⟨1726388, by rfl⟩ : syracuseStep 2301851 = 3452777) B3452777
theorem B4374719 : Blo 1534464 4374719 := bstep (se 1 (by rfl) ⟨3281039, by rfl⟩ : syracuseStep 4374719 = 6562079) B6562079
theorem B106381619 : Blo 1534464 106381619 := bstep (se 1 (by rfl) ⟨79786214, by rfl⟩ : syracuseStep 106381619 = 159572429) B159572429
theorem B11821385 : Blo 1534464 11821385 := bstep (se 2 (by rfl) ⟨4433019, by rfl⟩ : syracuseStep 11821385 = 8866039) B8866039
theorem B5833079 : Blo 1534464 5833079 := bstep (se 1 (by rfl) ⟨4374809, by rfl⟩ : syracuseStep 5833079 = 8749619) B8749619
theorem B17973677 : Blo 1534464 17973677 := bstep (se 3 (by rfl) ⟨3370064, by rfl⟩ : syracuseStep 17973677 = 6740129) B6740129
theorem B6562367 : Blo 1534464 6562367 := bstep (se 1 (by rfl) ⟨4921775, by rfl⟩ : syracuseStep 6562367 = 9843551) B9843551
theorem B20210273 : Blo 1534464 20210273 := bstep (se 2 (by rfl) ⟨7578852, by rfl⟩ : syracuseStep 20210273 = 15157705) B15157705
theorem B3277417 : Blo 1534464 3277417 := bstep (se 2 (by rfl) ⟨1229031, by rfl⟩ : syracuseStep 3277417 = 2458063) B2458063
theorem B1843879 : Blo 1534464 1843879 := bstep (se 1 (by rfl) ⟨1382909, by rfl⟩ : syracuseStep 1843879 = 2765819) B2765819
theorem B2302631 : Blo 1534464 2302631 := bstep (se 1 (by rfl) ⟨1726973, by rfl⟩ : syracuseStep 2302631 = 3453947) B3453947
theorem B2302751 : Blo 1534464 2302751 := bstep (se 1 (by rfl) ⟨1727063, by rfl⟩ : syracuseStep 2302751 = 3454127) B3454127
theorem B2302775 : Blo 1534464 2302775 := bstep (se 1 (by rfl) ⟨1727081, by rfl⟩ : syracuseStep 2302775 = 3454163) B3454163
theorem B2302955 : Blo 1534464 2302955 := bstep (se 1 (by rfl) ⟨1727216, by rfl⟩ : syracuseStep 2302955 = 3454433) B3454433
theorem B3687487 : Blo 1534464 3687487 := bstep (se 1 (by rfl) ⟨2765615, by rfl⟩ : syracuseStep 3687487 = 5531231) B5531231
theorem B56026201 : Blo 1534464 56026201 := bstep (se 2 (by rfl) ⟨21009825, by rfl⟩ : syracuseStep 56026201 = 42019651) B42019651
theorem B2589887 : Blo 1534464 2589887 := bstep (se 1 (by rfl) ⟨1942415, by rfl⟩ : syracuseStep 2589887 = 3884831) B3884831
theorem B6555431 : Blo 1534464 6555431 := bstep (se 1 (by rfl) ⟨4916573, by rfl⟩ : syracuseStep 6555431 = 9833147) B9833147
theorem B5179193 : Blo 1534464 5179193 := bstep (se 2 (by rfl) ⟨1942197, by rfl⟩ : syracuseStep 5179193 = 3884395) B3884395
theorem B11667401 : Blo 1534464 11667401 := bstep (se 2 (by rfl) ⟨4375275, by rfl⟩ : syracuseStep 11667401 = 8750551) B8750551
theorem B2590751 : Blo 1534464 2590751 := bstep (se 1 (by rfl) ⟨1943063, by rfl⟩ : syracuseStep 2590751 = 3886127) B3886127
theorem B2304047 : Blo 1534464 2304047 := bstep (se 1 (by rfl) ⟨1728035, by rfl⟩ : syracuseStep 2304047 = 3456071) B3456071
theorem B2304311 : Blo 1534464 2304311 := bstep (se 1 (by rfl) ⟨1728233, by rfl⟩ : syracuseStep 2304311 = 3456467) B3456467
theorem B6556079 : Blo 1534464 6556079 := bstep (se 1 (by rfl) ⟨4917059, by rfl⟩ : syracuseStep 6556079 = 9834119) B9834119
theorem B2304491 : Blo 1534464 2304491 := bstep (se 1 (by rfl) ⟨1728368, by rfl⟩ : syracuseStep 2304491 = 3456737) B3456737
theorem B1534511 : Blo 1534464 1534511 := bstep (se 1 (by rfl) ⟨1150883, by rfl⟩ : syracuseStep 1534511 = 2301767) B2301767
theorem B1534567 : Blo 1534464 1534567 := bstep (se 1 (by rfl) ⟨1150925, by rfl⟩ : syracuseStep 1534567 = 2301851) B2301851
theorem B3885671 : Blo 1534464 3885671 := bstep (se 1 (by rfl) ⟨2914253, by rfl⟩ : syracuseStep 3885671 = 5828507) B5828507
theorem B9833197 : Blo 1534464 9833197 := bstep (se 3 (by rfl) ⟨1843724, by rfl⟩ : syracuseStep 9833197 = 3687449) B3687449
theorem B2591527 : Blo 1534464 2591527 := bstep (se 1 (by rfl) ⟨1943645, by rfl⟩ : syracuseStep 2591527 = 3887291) B3887291
theorem B37882691 : Blo 1534464 37882691 := bstep (se 1 (by rfl) ⟨28412018, by rfl⟩ : syracuseStep 37882691 = 56824037) B56824037
theorem B11660111 : Blo 1534464 11660111 := bstep (se 1 (by rfl) ⟨8745083, by rfl⟩ : syracuseStep 11660111 = 17490167) B17490167
theorem B16837463 : Blo 1534464 16837463 := bstep (se 1 (by rfl) ⟨12628097, by rfl⟩ : syracuseStep 16837463 = 25256195) B25256195
theorem B7769033 : Blo 1534464 7769033 := bstep (se 2 (by rfl) ⟨2913387, by rfl⟩ : syracuseStep 7769033 = 5826775) B5826775
theorem B1534943 : Blo 1534464 1534943 := bstep (se 1 (by rfl) ⟨1151207, by rfl⟩ : syracuseStep 1534943 = 2302415) B2302415
theorem B1534971 : Blo 1534464 1534971 := bstep (se 1 (by rfl) ⟨1151228, by rfl⟩ : syracuseStep 1534971 = 2302457) B2302457
theorem B1535039 : Blo 1534464 1535039 := bstep (se 1 (by rfl) ⟨1151279, by rfl⟩ : syracuseStep 1535039 = 2302559) B2302559
theorem B7769195 : Blo 1534464 7769195 := bstep (se 1 (by rfl) ⟨5826896, by rfl⟩ : syracuseStep 7769195 = 11653793) B11653793
theorem B2591851 : Blo 1534464 2591851 := bstep (se 1 (by rfl) ⟨1943888, by rfl⟩ : syracuseStep 2591851 = 3887777) B3887777
theorem B3738811 : Blo 1534464 3738811 := bstep (se 1 (by rfl) ⟨2804108, by rfl⟩ : syracuseStep 3738811 = 5608217) B5608217
theorem B7482611 : Blo 1534464 7482611 := bstep (se 1 (by rfl) ⟨5611958, by rfl⟩ : syracuseStep 7482611 = 11223917) B11223917
theorem B2592121 : Blo 1534464 2592121 := bstep (se 2 (by rfl) ⟨972045, by rfl⟩ : syracuseStep 2592121 = 1944091) B1944091
theorem B1535359 : Blo 1534464 1535359 := bstep (se 1 (by rfl) ⟨1151519, by rfl⟩ : syracuseStep 1535359 = 2303039) B2303039
theorem B12619145 : Blo 1534464 12619145 := bstep (se 2 (by rfl) ⟨4732179, by rfl⟩ : syracuseStep 12619145 = 9464359) B9464359
theorem B1535387 : Blo 1534464 1535387 := bstep (se 1 (by rfl) ⟨1151540, by rfl⟩ : syracuseStep 1535387 = 2303081) B2303081
theorem B5828051 : Blo 1534464 5828051 := bstep (se 1 (by rfl) ⟨4371038, by rfl⟩ : syracuseStep 5828051 = 8742077) B8742077
theorem B1535455 : Blo 1534464 1535455 := bstep (se 1 (by rfl) ⟨1151591, by rfl⟩ : syracuseStep 1535455 = 2303183) B2303183
theorem B7376359 : Blo 1534464 7376359 := bstep (se 1 (by rfl) ⟨5532269, by rfl⟩ : syracuseStep 7376359 = 11064539) B11064539
theorem B1535591 : Blo 1534464 1535591 := bstep (se 1 (by rfl) ⟨1151693, by rfl⟩ : syracuseStep 1535591 = 2303387) B2303387
theorem B7769843 : Blo 1534464 7769843 := bstep (se 1 (by rfl) ⟨5827382, by rfl⟩ : syracuseStep 7769843 = 11654765) B11654765
theorem B1535739 : Blo 1534464 1535739 := bstep (se 1 (by rfl) ⟨1151804, by rfl⟩ : syracuseStep 1535739 = 2303609) B2303609
theorem B1535807 : Blo 1534464 1535807 := bstep (se 1 (by rfl) ⟨1151855, by rfl⟩ : syracuseStep 1535807 = 2303711) B2303711
theorem B1535871 : Blo 1534464 1535871 := bstep (se 1 (by rfl) ⟨1151903, by rfl⟩ : syracuseStep 1535871 = 2303807) B2303807
theorem B9842579 : Blo 1534464 9842579 := bstep (se 1 (by rfl) ⟨7381934, by rfl⟩ : syracuseStep 9842579 = 14763869) B14763869
theorem B16822199 : Blo 1534464 16822199 := bstep (se 1 (by rfl) ⟨12616649, by rfl⟩ : syracuseStep 16822199 = 25233299) B25233299
theorem B12480475 : Blo 1534464 12480475 := bstep (se 1 (by rfl) ⟨9360356, by rfl⟩ : syracuseStep 12480475 = 18720713) B18720713
theorem B1535983 : Blo 1534464 1535983 := bstep (se 1 (by rfl) ⟨1151987, by rfl⟩ : syracuseStep 1535983 = 2303975) B2303975
theorem B3452921 : Blo 1534464 3452921 := bstep (se 2 (by rfl) ⟨1294845, by rfl⟩ : syracuseStep 3452921 = 2589691) B2589691
theorem B3887099 : Blo 1534464 3887099 := bstep (se 1 (by rfl) ⟨2915324, by rfl⟩ : syracuseStep 3887099 = 5830649) B5830649
theorem B1535995 : Blo 1534464 1535995 := bstep (se 1 (by rfl) ⟨1151996, by rfl⟩ : syracuseStep 1535995 = 2303993) B2303993
theorem B1536063 : Blo 1534464 1536063 := bstep (se 1 (by rfl) ⟨1152047, by rfl⟩ : syracuseStep 1536063 = 2304095) B2304095
theorem B3453011 : Blo 1534464 3453011 := bstep (se 1 (by rfl) ⟨2589758, by rfl⟩ : syracuseStep 3453011 = 5179517) B5179517
theorem B5828705 : Blo 1534464 5828705 := bstep (se 2 (by rfl) ⟨2185764, by rfl⟩ : syracuseStep 5828705 = 4371529) B4371529
theorem B1536103 : Blo 1534464 1536103 := bstep (se 1 (by rfl) ⟨1152077, by rfl⟩ : syracuseStep 1536103 = 2304155) B2304155
theorem B1536127 : Blo 1534464 1536127 := bstep (se 1 (by rfl) ⟨1152095, by rfl⟩ : syracuseStep 1536127 = 2304191) B2304191
theorem B1536155 : Blo 1534464 1536155 := bstep (se 1 (by rfl) ⟨1152116, by rfl⟩ : syracuseStep 1536155 = 2304233) B2304233
theorem B11653307 : Blo 1534464 11653307 := bstep (se 1 (by rfl) ⟨8739980, by rfl⟩ : syracuseStep 11653307 = 17479961) B17479961
theorem B3453191 : Blo 1534464 3453191 := bstep (se 1 (by rfl) ⟨2589893, by rfl⟩ : syracuseStep 3453191 = 5179787) B5179787
theorem B6557993 : Blo 1534464 6557993 := bstep (se 2 (by rfl) ⟨2459247, by rfl⟩ : syracuseStep 6557993 = 4918495) B4918495
theorem B1536359 : Blo 1534464 1536359 := bstep (se 1 (by rfl) ⟨1152269, by rfl⟩ : syracuseStep 1536359 = 2304539) B2304539
theorem B1536411 : Blo 1534464 1536411 := bstep (se 1 (by rfl) ⟨1152308, by rfl⟩ : syracuseStep 1536411 = 2304617) B2304617
theorem B3453497 : Blo 1534464 3453497 := bstep (se 2 (by rfl) ⟨1295061, by rfl⟩ : syracuseStep 3453497 = 2590123) B2590123
theorem B5182109 : Blo 1534464 5182109 := bstep (se 3 (by rfl) ⟨971645, by rfl⟩ : syracuseStep 5182109 = 1943291) B1943291
theorem B4150241 : Blo 1534464 4150241 := bstep (se 2 (by rfl) ⟨1556340, by rfl⟩ : syracuseStep 4150241 = 3112681) B3112681
theorem B6558745 : Blo 1534464 6558745 := bstep (se 2 (by rfl) ⟨2459529, by rfl⟩ : syracuseStep 6558745 = 4919059) B4919059
theorem B53204111 : Blo 1534464 53204111 := bstep (se 1 (by rfl) ⟨39903083, by rfl⟩ : syracuseStep 53204111 = 79806167) B79806167
theorem B3888283 : Blo 1534464 3888283 := bstep (se 1 (by rfl) ⟨2916212, by rfl⟩ : syracuseStep 3888283 = 5832425) B5832425
theorem B5182649 : Blo 1534464 5182649 := bstep (se 2 (by rfl) ⟨1943493, by rfl⟩ : syracuseStep 5182649 = 3886987) B3886987
theorem B3454217 : Blo 1534464 3454217 := bstep (se 2 (by rfl) ⟨1295331, by rfl⟩ : syracuseStep 3454217 = 2590663) B2590663
theorem B3454271 : Blo 1534464 3454271 := bstep (se 1 (by rfl) ⟨2590703, by rfl⟩ : syracuseStep 3454271 = 5181407) B5181407
theorem B2913707 : Blo 1534464 2913707 := bstep (se 1 (by rfl) ⟨2185280, by rfl⟩ : syracuseStep 2913707 = 4370561) B4370561
theorem B3454379 : Blo 1534464 3454379 := bstep (se 1 (by rfl) ⟨2590784, by rfl⟩ : syracuseStep 3454379 = 5181569) B5181569
theorem B8746451 : Blo 1534464 8746451 := bstep (se 1 (by rfl) ⟨6559838, by rfl⟩ : syracuseStep 8746451 = 13119677) B13119677
theorem B5830163 : Blo 1534464 5830163 := bstep (se 1 (by rfl) ⟨4372622, by rfl⟩ : syracuseStep 5830163 = 8745245) B8745245
theorem B3454703 : Blo 1534464 3454703 := bstep (se 1 (by rfl) ⟨2591027, by rfl⟩ : syracuseStep 3454703 = 5182055) B5182055
theorem B26965865 : Blo 1534464 26965865 := bstep (se 2 (by rfl) ⟨10112199, by rfl⟩ : syracuseStep 26965865 = 20224399) B20224399
theorem B3454919 : Blo 1534464 3454919 := bstep (se 1 (by rfl) ⟨2591189, by rfl⟩ : syracuseStep 3454919 = 5182379) B5182379
theorem B2914375 : Blo 1534464 2914375 := bstep (se 1 (by rfl) ⟨2185781, by rfl⟩ : syracuseStep 2914375 = 4371563) B4371563
theorem B4921469 : Blo 1534464 4921469 := bstep (se 3 (by rfl) ⟨922775, by rfl⟩ : syracuseStep 4921469 = 1845551) B1845551
theorem B2914535 : Blo 1534464 2914535 := bstep (se 1 (by rfl) ⟨2185901, by rfl⟩ : syracuseStep 2914535 = 4371803) B4371803
theorem B3455207 : Blo 1534464 3455207 := bstep (se 1 (by rfl) ⟨2591405, by rfl⟩ : syracuseStep 3455207 = 5182811) B5182811
theorem B3455225 : Blo 1534464 3455225 := bstep (se 2 (by rfl) ⟨1295709, by rfl⟩ : syracuseStep 3455225 = 2591419) B2591419
theorem B3455279 : Blo 1534464 3455279 := bstep (se 1 (by rfl) ⟨2591459, by rfl⟩ : syracuseStep 3455279 = 5182919) B5182919
theorem B1726879 : Blo 1534464 1726879 := bstep (se 1 (by rfl) ⟨1295159, by rfl⟩ : syracuseStep 1726879 = 2590319) B2590319
theorem B4151711 : Blo 1534464 4151711 := bstep (se 1 (by rfl) ⟨3113783, by rfl⟩ : syracuseStep 4151711 = 6227567) B6227567
theorem B1726951 : Blo 1534464 1726951 := bstep (se 1 (by rfl) ⟨1295213, by rfl⟩ : syracuseStep 1726951 = 2590427) B2590427
theorem B3455495 : Blo 1534464 3455495 := bstep (se 1 (by rfl) ⟨2591621, by rfl⟩ : syracuseStep 3455495 = 5183243) B5183243
theorem B3111529 : Blo 1534464 3111529 := bstep (se 2 (by rfl) ⟨1166823, by rfl⟩ : syracuseStep 3111529 = 2333647) B2333647
theorem B4373135 : Blo 1534464 4373135 := bstep (se 1 (by rfl) ⟨3279851, by rfl⟩ : syracuseStep 4373135 = 6559703) B6559703
theorem B425384621 : Blo 1534464 425384621 := bstep (se 3 (by rfl) ⟨79759616, by rfl⟩ : syracuseStep 425384621 = 159519233) B159519233
theorem B3455675 : Blo 1534464 3455675 := bstep (se 1 (by rfl) ⟨2591756, by rfl⟩ : syracuseStep 3455675 = 5183513) B5183513
theorem B2915119 : Blo 1534464 2915119 := bstep (se 1 (by rfl) ⟨2186339, by rfl⟩ : syracuseStep 2915119 = 4372679) B4372679
theorem B5184647 : Blo 1534464 5184647 := bstep (se 1 (by rfl) ⟨3888485, by rfl⟩ : syracuseStep 5184647 = 7776971) B7776971
theorem B1727815 : Blo 1534464 1727815 := bstep (se 1 (by rfl) ⟨1295861, by rfl⟩ : syracuseStep 1727815 = 2591723) B2591723
theorem B5832107 : Blo 1534464 5832107 := bstep (se 1 (by rfl) ⟨4374080, by rfl⟩ : syracuseStep 5832107 = 8748161) B8748161
theorem B9461281 : Blo 1534464 9461281 := bstep (se 2 (by rfl) ⟨3547980, by rfl⟩ : syracuseStep 9461281 = 7095961) B7095961
theorem B3456575 : Blo 1534464 3456575 := bstep (se 1 (by rfl) ⟨2592431, by rfl⟩ : syracuseStep 3456575 = 5184863) B5184863
theorem B7380665 : Blo 1534464 7380665 := bstep (se 2 (by rfl) ⟨2767749, by rfl⟩ : syracuseStep 7380665 = 5535499) B5535499
theorem B2916175 : Blo 1534464 2916175 := bstep (se 1 (by rfl) ⟨2187131, by rfl⟩ : syracuseStep 2916175 = 4374263) B4374263
theorem B3456935 : Blo 1534464 3456935 := bstep (se 1 (by rfl) ⟨2592701, by rfl⟩ : syracuseStep 3456935 = 5185403) B5185403
theorem B2301929 : Blo 1534464 2301929 := bstep (se 2 (by rfl) ⟨863223, by rfl⟩ : syracuseStep 2301929 = 1726447) B1726447
theorem B2302007 : Blo 1534464 2302007 := bstep (se 1 (by rfl) ⟨1726505, by rfl⟩ : syracuseStep 2302007 = 3453011) B3453011
theorem B2916479 : Blo 1534464 2916479 := bstep (se 1 (by rfl) ⟨2187359, by rfl⟩ : syracuseStep 2916479 = 4374719) B4374719
theorem B2302127 : Blo 1534464 2302127 := bstep (se 1 (by rfl) ⟨1726595, by rfl⟩ : syracuseStep 2302127 = 3453191) B3453191
theorem B7880923 : Blo 1534464 7880923 := bstep (se 1 (by rfl) ⟨5910692, by rfl⟩ : syracuseStep 7880923 = 11821385) B11821385
theorem B2302331 : Blo 1534464 2302331 := bstep (se 1 (by rfl) ⟨1726748, by rfl⟩ : syracuseStep 2302331 = 3453497) B3453497
theorem B4374911 : Blo 1534464 4374911 := bstep (se 1 (by rfl) ⟨3281183, by rfl⟩ : syracuseStep 4374911 = 6562367) B6562367
theorem B2302505 : Blo 1534464 2302505 := bstep (se 2 (by rfl) ⟨863439, by rfl⟩ : syracuseStep 2302505 = 1726879) B1726879
theorem B2302601 : Blo 1534464 2302601 := bstep (se 2 (by rfl) ⟨863475, by rfl⟩ : syracuseStep 2302601 = 1726951) B1726951
theorem B2302811 : Blo 1534464 2302811 := bstep (se 1 (by rfl) ⟨1727108, by rfl⟩ : syracuseStep 2302811 = 3454217) B3454217
theorem B2302847 : Blo 1534464 2302847 := bstep (se 1 (by rfl) ⟨1727135, by rfl⟩ : syracuseStep 2302847 = 3454271) B3454271
theorem B2458505 : Blo 1534464 2458505 := bstep (se 2 (by rfl) ⟨921939, by rfl⟩ : syracuseStep 2458505 = 1843879) B1843879
theorem B1942471 : Blo 1534464 1942471 := bstep (se 1 (by rfl) ⟨1456853, by rfl⟩ : syracuseStep 1942471 = 2913707) B2913707
theorem B2302919 : Blo 1534464 2302919 := bstep (se 1 (by rfl) ⟨1727189, by rfl⟩ : syracuseStep 2302919 = 3454379) B3454379
theorem B17482877 : Blo 1534464 17482877 := bstep (se 3 (by rfl) ⟨3278039, by rfl⟩ : syracuseStep 17482877 = 6556079) B6556079
theorem B2303135 : Blo 1534464 2303135 := bstep (se 1 (by rfl) ⟨1727351, by rfl⟩ : syracuseStep 2303135 = 3454703) B3454703
theorem B2303279 : Blo 1534464 2303279 := bstep (se 1 (by rfl) ⟨1727459, by rfl⟩ : syracuseStep 2303279 = 3454919) B3454919
theorem B1943023 : Blo 1534464 1943023 := bstep (se 1 (by rfl) ⟨1457267, by rfl⟩ : syracuseStep 1943023 = 2914535) B2914535
theorem B2303471 : Blo 1534464 2303471 := bstep (se 1 (by rfl) ⟨1727603, by rfl⟩ : syracuseStep 2303471 = 3455207) B3455207
theorem B2303483 : Blo 1534464 2303483 := bstep (se 1 (by rfl) ⟨1727612, by rfl⟩ : syracuseStep 2303483 = 3455225) B3455225
theorem B2303519 : Blo 1534464 2303519 := bstep (se 1 (by rfl) ⟨1727639, by rfl⟩ : syracuseStep 2303519 = 3455279) B3455279
theorem B2303663 : Blo 1534464 2303663 := bstep (se 1 (by rfl) ⟨1727747, by rfl⟩ : syracuseStep 2303663 = 3455495) B3455495
theorem B2590447 : Blo 1534464 2590447 := bstep (se 1 (by rfl) ⟨1942835, by rfl⟩ : syracuseStep 2590447 = 3885671) B3885671
theorem B2303753 : Blo 1534464 2303753 := bstep (se 2 (by rfl) ⟨863907, by rfl⟩ : syracuseStep 2303753 = 1727815) B1727815
theorem B2303783 : Blo 1534464 2303783 := bstep (se 1 (by rfl) ⟨1727837, by rfl⟩ : syracuseStep 2303783 = 3455675) B3455675
theorem B11224975 : Blo 1534464 11224975 := bstep (se 1 (by rfl) ⟨8418731, by rfl⟩ : syracuseStep 11224975 = 16837463) B16837463
theorem B5179355 : Blo 1534464 5179355 := bstep (se 1 (by rfl) ⟨3884516, by rfl⟩ : syracuseStep 5179355 = 7769033) B7769033
theorem B5179463 : Blo 1534464 5179463 := bstep (se 1 (by rfl) ⟨3884597, by rfl⟩ : syracuseStep 5179463 = 7769195) B7769195
theorem B3885367 : Blo 1534464 3885367 := bstep (se 1 (by rfl) ⟨2914025, by rfl⟩ : syracuseStep 3885367 = 5828051) B5828051
theorem B2304383 : Blo 1534464 2304383 := bstep (se 1 (by rfl) ⟨1728287, by rfl⟩ : syracuseStep 2304383 = 3456575) B3456575
theorem B5179895 : Blo 1534464 5179895 := bstep (se 1 (by rfl) ⟨3884921, by rfl⟩ : syracuseStep 5179895 = 7769843) B7769843
theorem B2304623 : Blo 1534464 2304623 := bstep (se 1 (by rfl) ⟨1728467, by rfl⟩ : syracuseStep 2304623 = 3456935) B3456935
theorem B16640633 : Blo 1534464 16640633 := bstep (se 2 (by rfl) ⟨6240237, by rfl⟩ : syracuseStep 16640633 = 12480475) B12480475
theorem B1534619 : Blo 1534464 1534619 := bstep (se 1 (by rfl) ⟨1150964, by rfl⟩ : syracuseStep 1534619 = 2301929) B2301929
theorem B2591399 : Blo 1534464 2591399 := bstep (se 1 (by rfl) ⟨1943549, by rfl⟩ : syracuseStep 2591399 = 3887099) B3887099
theorem B3885803 : Blo 1534464 3885803 := bstep (se 1 (by rfl) ⟨2914352, by rfl⟩ : syracuseStep 3885803 = 5828705) B5828705
theorem B3885833 : Blo 1534464 3885833 := bstep (se 2 (by rfl) ⟨1457187, by rfl⟩ : syracuseStep 3885833 = 2914375) B2914375
theorem B7768871 : Blo 1534464 7768871 := bstep (se 1 (by rfl) ⟨5826653, by rfl⟩ : syracuseStep 7768871 = 11653307) B11653307
theorem B70921079 : Blo 1534464 70921079 := bstep (se 1 (by rfl) ⟨53190809, by rfl⟩ : syracuseStep 70921079 = 106381619) B106381619
theorem B1535087 : Blo 1534464 1535087 := bstep (se 1 (by rfl) ⟨1151315, by rfl⟩ : syracuseStep 1535087 = 2302631) B2302631
theorem B1535167 : Blo 1534464 1535167 := bstep (se 1 (by rfl) ⟨1151375, by rfl⟩ : syracuseStep 1535167 = 2302751) B2302751
theorem B1535183 : Blo 1534464 1535183 := bstep (se 1 (by rfl) ⟨1151387, by rfl⟩ : syracuseStep 1535183 = 2302775) B2302775
theorem B1535303 : Blo 1534464 1535303 := bstep (se 1 (by rfl) ⟨1151477, by rfl⟩ : syracuseStep 1535303 = 2302955) B2302955
theorem B4369889 : Blo 1534464 4369889 := bstep (se 2 (by rfl) ⟨1638708, by rfl⟩ : syracuseStep 4369889 = 3277417) B3277417
theorem B4148705 : Blo 1534464 4148705 := bstep (se 2 (by rfl) ⟨1555764, by rfl⟩ : syracuseStep 4148705 = 3111529) B3111529
theorem B13110929 : Blo 1534464 13110929 := bstep (se 2 (by rfl) ⟨4916598, by rfl⟩ : syracuseStep 13110929 = 9833197) B9833197
theorem B3886775 : Blo 1534464 3886775 := bstep (se 1 (by rfl) ⟨2915081, by rfl⟩ : syracuseStep 3886775 = 5830163) B5830163
theorem B3886825 : Blo 1534464 3886825 := bstep (se 2 (by rfl) ⟨1457559, by rfl⟩ : syracuseStep 3886825 = 2915119) B2915119
theorem B4370287 : Blo 1534464 4370287 := bstep (se 1 (by rfl) ⟨3277715, by rfl⟩ : syracuseStep 4370287 = 6555431) B6555431
theorem B3452795 : Blo 1534464 3452795 := bstep (se 1 (by rfl) ⟨2589596, by rfl⟩ : syracuseStep 3452795 = 5179193) B5179193
theorem B17977243 : Blo 1534464 17977243 := bstep (se 1 (by rfl) ⟨13482932, by rfl⟩ : syracuseStep 17977243 = 26965865) B26965865
theorem B7778267 : Blo 1534464 7778267 := bstep (se 1 (by rfl) ⟨5833700, by rfl⟩ : syracuseStep 7778267 = 11667401) B11667401
theorem B1536031 : Blo 1534464 1536031 := bstep (se 1 (by rfl) ⟨1152023, by rfl⟩ : syracuseStep 1536031 = 2304047) B2304047
theorem B8744993 : Blo 1534464 8744993 := bstep (se 2 (by rfl) ⟨3279372, by rfl⟩ : syracuseStep 8744993 = 6558745) B6558745
theorem B3280979 : Blo 1534464 3280979 := bstep (se 1 (by rfl) ⟨2460734, by rfl⟩ : syracuseStep 3280979 = 4921469) B4921469
theorem B1536207 : Blo 1534464 1536207 := bstep (se 1 (by rfl) ⟨1152155, by rfl⟩ : syracuseStep 1536207 = 2304311) B2304311
theorem B4985081 : Blo 1534464 4985081 := bstep (se 2 (by rfl) ⟨1869405, by rfl⟩ : syracuseStep 4985081 = 3738811) B3738811
theorem B1536327 : Blo 1534464 1536327 := bstep (se 1 (by rfl) ⟨1152245, by rfl⟩ : syracuseStep 1536327 = 2304491) B2304491
theorem B9835145 : Blo 1534464 9835145 := bstep (se 2 (by rfl) ⟨3688179, by rfl⟩ : syracuseStep 9835145 = 7376359) B7376359
theorem B3888071 : Blo 1534464 3888071 := bstep (se 1 (by rfl) ⟨2916053, by rfl⟩ : syracuseStep 3888071 = 5832107) B5832107
theorem B3888233 : Blo 1534464 3888233 := bstep (se 2 (by rfl) ⟨1458087, by rfl⟩ : syracuseStep 3888233 = 2916175) B2916175
theorem B4920443 : Blo 1534464 4920443 := bstep (se 1 (by rfl) ⟨3690332, by rfl⟩ : syracuseStep 4920443 = 7380665) B7380665
theorem B4371995 : Blo 1534464 4371995 := bstep (se 1 (by rfl) ⟨3278996, by rfl⟩ : syracuseStep 4371995 = 6557993) B6557993
theorem B3888719 : Blo 1534464 3888719 := bstep (se 1 (by rfl) ⟨2916539, by rfl⟩ : syracuseStep 3888719 = 5833079) B5833079
theorem B11982451 : Blo 1534464 11982451 := bstep (se 1 (by rfl) ⟨8986838, by rfl⟩ : syracuseStep 11982451 = 17973677) B17973677
theorem B19666597 : Blo 1534464 19666597 := bstep (se 4 (by rfl) ⟨1843743, by rfl⟩ : syracuseStep 19666597 = 3687487) B3687487
theorem B13473515 : Blo 1534464 13473515 := bstep (se 1 (by rfl) ⟨10105136, by rfl⟩ : syracuseStep 13473515 = 20210273) B20210273
theorem B3454739 : Blo 1534464 3454739 := bstep (se 1 (by rfl) ⟨2591054, by rfl⟩ : syracuseStep 3454739 = 5182109) B5182109
theorem B2766827 : Blo 1534464 2766827 := bstep (se 1 (by rfl) ⟨2075120, by rfl⟩ : syracuseStep 2766827 = 4150241) B4150241
theorem B35469407 : Blo 1534464 35469407 := bstep (se 1 (by rfl) ⟨26602055, by rfl⟩ : syracuseStep 35469407 = 53204111) B53204111
theorem B3455099 : Blo 1534464 3455099 := bstep (se 1 (by rfl) ⟨2591324, by rfl⟩ : syracuseStep 3455099 = 5182649) B5182649
theorem B1726591 : Blo 1534464 1726591 := bstep (se 1 (by rfl) ⟨1294943, by rfl⟩ : syracuseStep 1726591 = 2589887) B2589887
theorem B5830967 : Blo 1534464 5830967 := bstep (se 1 (by rfl) ⟨4373225, by rfl⟩ : syracuseStep 5830967 = 8746451) B8746451
theorem B3455369 : Blo 1534464 3455369 := bstep (se 2 (by rfl) ⟨1295763, by rfl⟩ : syracuseStep 3455369 = 2591527) B2591527
theorem B1727167 : Blo 1534464 1727167 := bstep (se 1 (by rfl) ⟨1295375, by rfl⟩ : syracuseStep 1727167 = 2590751) B2590751
theorem B74701601 : Blo 1534464 74701601 := bstep (se 2 (by rfl) ⟨28013100, by rfl⟩ : syracuseStep 74701601 = 56026201) B56026201
theorem B3455801 : Blo 1534464 3455801 := bstep (se 2 (by rfl) ⟨1295925, by rfl⟩ : syracuseStep 3455801 = 2591851) B2591851
theorem B5184377 : Blo 1534464 5184377 := bstep (se 2 (by rfl) ⟨1944141, by rfl⟩ : syracuseStep 5184377 = 3888283) B3888283
theorem B2767807 : Blo 1534464 2767807 := bstep (se 1 (by rfl) ⟨2075855, by rfl⟩ : syracuseStep 2767807 = 4151711) B4151711
theorem B2915423 : Blo 1534464 2915423 := bstep (se 1 (by rfl) ⟨2186567, by rfl⟩ : syracuseStep 2915423 = 4373135) B4373135
theorem B283589747 : Blo 1534464 283589747 := bstep (se 1 (by rfl) ⟨212692310, by rfl⟩ : syracuseStep 283589747 = 425384621) B425384621
theorem B3456161 : Blo 1534464 3456161 := bstep (se 2 (by rfl) ⟨1296060, by rfl⟩ : syracuseStep 3456161 = 2592121) B2592121
theorem B25255127 : Blo 1534464 25255127 := bstep (se 1 (by rfl) ⟨18941345, by rfl⟩ : syracuseStep 25255127 = 37882691) B37882691
theorem B7773407 : Blo 1534464 7773407 := bstep (se 1 (by rfl) ⟨5830055, by rfl⟩ : syracuseStep 7773407 = 11660111) B11660111
theorem B12615041 : Blo 1534464 12615041 := bstep (se 2 (by rfl) ⟨4730640, by rfl⟩ : syracuseStep 12615041 = 9461281) B9461281
theorem B3456431 : Blo 1534464 3456431 := bstep (se 1 (by rfl) ⟨2592323, by rfl⟩ : syracuseStep 3456431 = 5184647) B5184647
theorem B4988407 : Blo 1534464 4988407 := bstep (se 1 (by rfl) ⟨3741305, by rfl⟩ : syracuseStep 4988407 = 7482611) B7482611
theorem B8412763 : Blo 1534464 8412763 := bstep (se 1 (by rfl) ⟨6309572, by rfl⟩ : syracuseStep 8412763 = 12619145) B12619145
theorem B44859197 : Blo 1534464 44859197 := bstep (se 3 (by rfl) ⟨8411099, by rfl⟩ : syracuseStep 44859197 = 16822199) B16822199
theorem B6561719 : Blo 1534464 6561719 := bstep (se 1 (by rfl) ⟨4921289, by rfl⟩ : syracuseStep 6561719 = 9842579) B9842579
theorem B2301947 : Blo 1534464 2301947 := bstep (se 1 (by rfl) ⟨1726460, by rfl⟩ : syracuseStep 2301947 = 3452921) B3452921
theorem B2187319 : Blo 1534464 2187319 := bstep (se 1 (by rfl) ⟨1640489, by rfl⟩ : syracuseStep 2187319 = 3280979) B3280979
theorem B2302121 : Blo 1534464 2302121 := bstep (se 2 (by rfl) ⟨863295, by rfl⟩ : syracuseStep 2302121 = 1726591) B1726591
theorem B1639003 : Blo 1534464 1639003 := bstep (se 1 (by rfl) ⟨1229252, by rfl⟩ : syracuseStep 1639003 = 2458505) B2458505
theorem B2302889 : Blo 1534464 2302889 := bstep (se 2 (by rfl) ⟨863583, by rfl⟩ : syracuseStep 2302889 = 1727167) B1727167
theorem B11666429 : Blo 1534464 11666429 := bstep (se 3 (by rfl) ⟨2187455, by rfl⟩ : syracuseStep 11666429 = 4374911) B4374911
theorem B2303159 : Blo 1534464 2303159 := bstep (se 1 (by rfl) ⟨1727369, by rfl⟩ : syracuseStep 2303159 = 3454739) B3454739
theorem B2589961 : Blo 1534464 2589961 := bstep (se 2 (by rfl) ⟨971235, by rfl⟩ : syracuseStep 2589961 = 1942471) B1942471
theorem B1844551 : Blo 1534464 1844551 := bstep (se 1 (by rfl) ⟨1383413, by rfl⟩ : syracuseStep 1844551 = 2766827) B2766827
theorem B11658653 : Blo 1534464 11658653 := bstep (se 3 (by rfl) ⟨2185997, by rfl⟩ : syracuseStep 11658653 = 4371995) B4371995
theorem B2303399 : Blo 1534464 2303399 := bstep (se 1 (by rfl) ⟨1727549, by rfl⟩ : syracuseStep 2303399 = 3455099) B3455099
theorem B2303579 : Blo 1534464 2303579 := bstep (se 1 (by rfl) ⟨1727684, by rfl⟩ : syracuseStep 2303579 = 3455369) B3455369
theorem B11093755 : Blo 1534464 11093755 := bstep (se 1 (by rfl) ⟨8320316, by rfl⟩ : syracuseStep 11093755 = 16640633) B16640633
theorem B2590535 : Blo 1534464 2590535 := bstep (se 1 (by rfl) ⟨1942901, by rfl⟩ : syracuseStep 2590535 = 3885803) B3885803
theorem B2590555 : Blo 1534464 2590555 := bstep (se 1 (by rfl) ⟨1942916, by rfl⟩ : syracuseStep 2590555 = 3885833) B3885833
theorem B49801067 : Blo 1534464 49801067 := bstep (se 1 (by rfl) ⟨37350800, by rfl⟩ : syracuseStep 49801067 = 74701601) B74701601
theorem B5179247 : Blo 1534464 5179247 := bstep (se 1 (by rfl) ⟨3884435, by rfl⟩ : syracuseStep 5179247 = 7768871) B7768871
theorem B2303867 : Blo 1534464 2303867 := bstep (se 1 (by rfl) ⟨1727900, by rfl⟩ : syracuseStep 2303867 = 3455801) B3455801
theorem B2590697 : Blo 1534464 2590697 := bstep (se 2 (by rfl) ⟨971511, by rfl⟩ : syracuseStep 2590697 = 1943023) B1943023
theorem B1943615 : Blo 1534464 1943615 := bstep (se 1 (by rfl) ⟨1457711, by rfl⟩ : syracuseStep 1943615 = 2915423) B2915423
theorem B2304107 : Blo 1534464 2304107 := bstep (se 1 (by rfl) ⟨1728080, by rfl⟩ : syracuseStep 2304107 = 3456161) B3456161
theorem B11217017 : Blo 1534464 11217017 := bstep (se 2 (by rfl) ⟨4206381, by rfl⟩ : syracuseStep 11217017 = 8412763) B8412763
theorem B16836751 : Blo 1534464 16836751 := bstep (se 1 (by rfl) ⟨12627563, by rfl⟩ : syracuseStep 16836751 = 25255127) B25255127
theorem B15976601 : Blo 1534464 15976601 := bstep (se 2 (by rfl) ⟨5991225, by rfl⟩ : syracuseStep 15976601 = 11982451) B11982451
theorem B2304287 : Blo 1534464 2304287 := bstep (se 1 (by rfl) ⟨1728215, by rfl⟩ : syracuseStep 2304287 = 3456431) B3456431
theorem B2591183 : Blo 1534464 2591183 := bstep (se 1 (by rfl) ⟨1943387, by rfl⟩ : syracuseStep 2591183 = 3886775) B3886775
theorem B5827049 : Blo 1534464 5827049 := bstep (se 2 (by rfl) ⟨2185143, by rfl⟩ : syracuseStep 5827049 = 4370287) B4370287
theorem B1534631 : Blo 1534464 1534631 := bstep (se 1 (by rfl) ⟨1150973, by rfl⟩ : syracuseStep 1534631 = 2301947) B2301947
theorem B1534671 : Blo 1534464 1534671 := bstep (se 1 (by rfl) ⟨1151003, by rfl⟩ : syracuseStep 1534671 = 2302007) B2302007
theorem B1944319 : Blo 1534464 1944319 := bstep (se 1 (by rfl) ⟨1458239, by rfl⟩ : syracuseStep 1944319 = 2916479) B2916479
theorem B1534751 : Blo 1534464 1534751 := bstep (se 1 (by rfl) ⟨1151063, by rfl⟩ : syracuseStep 1534751 = 2302127) B2302127
theorem B1534887 : Blo 1534464 1534887 := bstep (se 1 (by rfl) ⟨1151165, by rfl⟩ : syracuseStep 1534887 = 2302331) B2302331
theorem B1535003 : Blo 1534464 1535003 := bstep (se 1 (by rfl) ⟨1151252, by rfl⟩ : syracuseStep 1535003 = 2302505) B2302505
theorem B5180489 : Blo 1534464 5180489 := bstep (se 2 (by rfl) ⟨1942683, by rfl⟩ : syracuseStep 5180489 = 3885367) B3885367
theorem B6556763 : Blo 1534464 6556763 := bstep (se 1 (by rfl) ⟨4917572, by rfl⟩ : syracuseStep 6556763 = 9835145) B9835145
theorem B1535067 : Blo 1534464 1535067 := bstep (se 1 (by rfl) ⟨1151300, by rfl⟩ : syracuseStep 1535067 = 2302601) B2302601
theorem B1535207 : Blo 1534464 1535207 := bstep (se 1 (by rfl) ⟨1151405, by rfl⟩ : syracuseStep 1535207 = 2302811) B2302811
theorem B1535231 : Blo 1534464 1535231 := bstep (se 1 (by rfl) ⟨1151423, by rfl⟩ : syracuseStep 1535231 = 2302847) B2302847
theorem B1535279 : Blo 1534464 1535279 := bstep (se 1 (by rfl) ⟨1151459, by rfl⟩ : syracuseStep 1535279 = 2302919) B2302919
theorem B2592047 : Blo 1534464 2592047 := bstep (se 1 (by rfl) ⟨1944035, by rfl⟩ : syracuseStep 2592047 = 3888071) B3888071
theorem B2592155 : Blo 1534464 2592155 := bstep (se 1 (by rfl) ⟨1944116, by rfl⟩ : syracuseStep 2592155 = 3888233) B3888233
theorem B3280295 : Blo 1534464 3280295 := bstep (se 1 (by rfl) ⟨2460221, by rfl⟩ : syracuseStep 3280295 = 4920443) B4920443
theorem B1535423 : Blo 1534464 1535423 := bstep (se 1 (by rfl) ⟨1151567, by rfl⟩ : syracuseStep 1535423 = 2303135) B2303135
theorem B1535519 : Blo 1534464 1535519 := bstep (se 1 (by rfl) ⟨1151639, by rfl⟩ : syracuseStep 1535519 = 2303279) B2303279
theorem B1535647 : Blo 1534464 1535647 := bstep (se 1 (by rfl) ⟨1151735, by rfl⟩ : syracuseStep 1535647 = 2303471) B2303471
theorem B1535655 : Blo 1534464 1535655 := bstep (se 1 (by rfl) ⟨1151741, by rfl⟩ : syracuseStep 1535655 = 2303483) B2303483
theorem B33640109 : Blo 1534464 33640109 := bstep (se 3 (by rfl) ⟨6307520, by rfl⟩ : syracuseStep 33640109 = 12615041) B12615041
theorem B1535679 : Blo 1534464 1535679 := bstep (se 1 (by rfl) ⟨1151759, by rfl⟩ : syracuseStep 1535679 = 2303519) B2303519
theorem B2592479 : Blo 1534464 2592479 := bstep (se 1 (by rfl) ⟨1944359, by rfl⟩ : syracuseStep 2592479 = 3888719) B3888719
theorem B1535775 : Blo 1534464 1535775 := bstep (se 1 (by rfl) ⟨1151831, by rfl⟩ : syracuseStep 1535775 = 2303663) B2303663
theorem B8982343 : Blo 1534464 8982343 := bstep (se 1 (by rfl) ⟨6736757, by rfl⟩ : syracuseStep 8982343 = 13473515) B13473515
theorem B1535835 : Blo 1534464 1535835 := bstep (se 1 (by rfl) ⟨1151876, by rfl⟩ : syracuseStep 1535835 = 2303753) B2303753
theorem B1535855 : Blo 1534464 1535855 := bstep (se 1 (by rfl) ⟨1151891, by rfl⟩ : syracuseStep 1535855 = 2303783) B2303783
theorem B3690409 : Blo 1534464 3690409 := bstep (se 2 (by rfl) ⟨1383903, by rfl⟩ : syracuseStep 3690409 = 2767807) B2767807
theorem B11063213 : Blo 1534464 11063213 := bstep (se 3 (by rfl) ⟨2074352, by rfl⟩ : syracuseStep 11063213 = 4148705) B4148705
theorem B3452903 : Blo 1534464 3452903 := bstep (se 1 (by rfl) ⟨2589677, by rfl⟩ : syracuseStep 3452903 = 5179355) B5179355
theorem B3452975 : Blo 1534464 3452975 := bstep (se 1 (by rfl) ⟨2589731, by rfl⟩ : syracuseStep 3452975 = 5179463) B5179463
theorem B23646271 : Blo 1534464 23646271 := bstep (se 1 (by rfl) ⟨17734703, by rfl⟩ : syracuseStep 23646271 = 35469407) B35469407
theorem B3887311 : Blo 1534464 3887311 := bstep (se 1 (by rfl) ⟨2915483, by rfl⟩ : syracuseStep 3887311 = 5830967) B5830967
theorem B1536255 : Blo 1534464 1536255 := bstep (se 1 (by rfl) ⟨1152191, by rfl⟩ : syracuseStep 1536255 = 2304383) B2304383
theorem B3453263 : Blo 1534464 3453263 := bstep (se 1 (by rfl) ⟨2589947, by rfl⟩ : syracuseStep 3453263 = 5179895) B5179895
theorem B1536415 : Blo 1534464 1536415 := bstep (se 1 (by rfl) ⟨1152311, by rfl⟩ : syracuseStep 1536415 = 2304623) B2304623
theorem B47280719 : Blo 1534464 47280719 := bstep (se 1 (by rfl) ⟨35460539, by rfl⟩ : syracuseStep 47280719 = 70921079) B70921079
theorem B189059831 : Blo 1534464 189059831 := bstep (se 1 (by rfl) ⟨141794873, by rfl⟩ : syracuseStep 189059831 = 283589747) B283589747
theorem B5182271 : Blo 1534464 5182271 := bstep (se 1 (by rfl) ⟨3886703, by rfl⟩ : syracuseStep 5182271 = 7773407) B7773407
theorem B5182433 : Blo 1534464 5182433 := bstep (se 2 (by rfl) ⟨1943412, by rfl⟩ : syracuseStep 5182433 = 3886825) B3886825
theorem B3453929 : Blo 1534464 3453929 := bstep (se 2 (by rfl) ⟨1295223, by rfl⟩ : syracuseStep 3453929 = 2590447) B2590447
theorem B2913259 : Blo 1534464 2913259 := bstep (se 1 (by rfl) ⟨2184944, by rfl⟩ : syracuseStep 2913259 = 4369889) B4369889
theorem B29906131 : Blo 1534464 29906131 := bstep (se 1 (by rfl) ⟨22429598, by rfl⟩ : syracuseStep 29906131 = 44859197) B44859197
theorem B5829995 : Blo 1534464 5829995 := bstep (se 1 (by rfl) ⟨4372496, by rfl⟩ : syracuseStep 5829995 = 8744993) B8744993
theorem B3323387 : Blo 1534464 3323387 := bstep (se 1 (by rfl) ⟨2492540, by rfl⟩ : syracuseStep 3323387 = 4985081) B4985081
theorem B10507897 : Blo 1534464 10507897 := bstep (se 2 (by rfl) ⟨3940461, by rfl⟩ : syracuseStep 10507897 = 7880923) B7880923
theorem B11655251 : Blo 1534464 11655251 := bstep (se 1 (by rfl) ⟨8741438, by rfl⟩ : syracuseStep 11655251 = 17482877) B17482877
theorem B1727599 : Blo 1534464 1727599 := bstep (se 1 (by rfl) ⟨1295699, by rfl⟩ : syracuseStep 1727599 = 2591399) B2591399
theorem B3456251 : Blo 1534464 3456251 := bstep (se 1 (by rfl) ⟨2592188, by rfl⟩ : syracuseStep 3456251 = 5184377) B5184377
theorem B6651209 : Blo 1534464 6651209 := bstep (se 2 (by rfl) ⟨2494203, by rfl⟩ : syracuseStep 6651209 = 4988407) B4988407
theorem B26222129 : Blo 1534464 26222129 := bstep (se 2 (by rfl) ⟨9833298, by rfl⟩ : syracuseStep 26222129 = 19666597) B19666597
theorem B8740619 : Blo 1534464 8740619 := bstep (se 1 (by rfl) ⟨6555464, by rfl⟩ : syracuseStep 8740619 = 13110929) B13110929
theorem B14966633 : Blo 1534464 14966633 := bstep (se 2 (by rfl) ⟨5612487, by rfl⟩ : syracuseStep 14966633 = 11224975) B11224975
theorem B23969657 : Blo 1534464 23969657 := bstep (se 2 (by rfl) ⟨8988621, by rfl⟩ : syracuseStep 23969657 = 17977243) B17977243
theorem B2301863 : Blo 1534464 2301863 := bstep (se 1 (by rfl) ⟨1726397, by rfl⟩ : syracuseStep 2301863 = 3452795) B3452795
theorem B4374479 : Blo 1534464 4374479 := bstep (se 1 (by rfl) ⟨3280859, by rfl⟩ : syracuseStep 4374479 = 6561719) B6561719
theorem B5185511 : Blo 1534464 5185511 := bstep (se 1 (by rfl) ⟨3889133, by rfl⟩ : syracuseStep 5185511 = 7778267) B7778267
theorem B2301983 : Blo 1534464 2301983 := bstep (se 1 (by rfl) ⟨1726487, by rfl⟩ : syracuseStep 2301983 = 3452975) B3452975
theorem B2916425 : Blo 1534464 2916425 := bstep (se 2 (by rfl) ⟨1093659, by rfl⟩ : syracuseStep 2916425 = 2187319) B2187319
theorem B2302175 : Blo 1534464 2302175 := bstep (se 1 (by rfl) ⟨1726631, by rfl⟩ : syracuseStep 2302175 = 3453263) B3453263
theorem B56042117 : Blo 1534464 56042117 := bstep (se 4 (by rfl) ⟨5253948, by rfl⟩ : syracuseStep 56042117 = 10507897) B10507897
theorem B2302619 : Blo 1534464 2302619 := bstep (se 1 (by rfl) ⟨1726964, by rfl⟩ : syracuseStep 2302619 = 3453929) B3453929
theorem B3884345 : Blo 1534464 3884345 := bstep (se 2 (by rfl) ⟨1456629, by rfl⟩ : syracuseStep 3884345 = 2913259) B2913259
theorem B10651067 : Blo 1534464 10651067 := bstep (se 1 (by rfl) ⟨7988300, by rfl⟩ : syracuseStep 10651067 = 15976601) B15976601
theorem B2303465 : Blo 1534464 2303465 := bstep (se 2 (by rfl) ⟨863799, by rfl⟩ : syracuseStep 2303465 = 1727599) B1727599
theorem B3884699 : Blo 1534464 3884699 := bstep (se 1 (by rfl) ⟨2913524, by rfl⟩ : syracuseStep 3884699 = 5827049) B5827049
theorem B2304167 : Blo 1534464 2304167 := bstep (se 1 (by rfl) ⟨1728125, by rfl⟩ : syracuseStep 2304167 = 3456251) B3456251
theorem B4434139 : Blo 1534464 4434139 := bstep (se 1 (by rfl) ⟨3325604, by rfl⟩ : syracuseStep 4434139 = 6651209) B6651209
theorem B5827079 : Blo 1534464 5827079 := bstep (se 1 (by rfl) ⟨4370309, by rfl⟩ : syracuseStep 5827079 = 8740619) B8740619
theorem B1534575 : Blo 1534464 1534575 := bstep (se 1 (by rfl) ⟨1150931, by rfl⟩ : syracuseStep 1534575 = 2301863) B2301863
theorem B7375475 : Blo 1534464 7375475 := bstep (se 1 (by rfl) ⟨5531606, by rfl⟩ : syracuseStep 7375475 = 11063213) B11063213
theorem B1534747 : Blo 1534464 1534747 := bstep (se 1 (by rfl) ⟨1151060, by rfl⟩ : syracuseStep 1534747 = 2302121) B2302121
theorem B22449001 : Blo 1534464 22449001 := bstep (se 2 (by rfl) ⟨8418375, by rfl⟩ : syracuseStep 22449001 = 16836751) B16836751
theorem B1535259 : Blo 1534464 1535259 := bstep (se 1 (by rfl) ⟨1151444, by rfl⟩ : syracuseStep 1535259 = 2302889) B2302889
theorem B7777619 : Blo 1534464 7777619 := bstep (se 1 (by rfl) ⟨5833214, by rfl⟩ : syracuseStep 7777619 = 11666429) B11666429
theorem B1535439 : Blo 1534464 1535439 := bstep (se 1 (by rfl) ⟨1151579, by rfl⟩ : syracuseStep 1535439 = 2303159) B2303159
theorem B3886663 : Blo 1534464 3886663 := bstep (se 1 (by rfl) ⟨2914997, by rfl⟩ : syracuseStep 3886663 = 5829995) B5829995
theorem B1535599 : Blo 1534464 1535599 := bstep (se 1 (by rfl) ⟨1151699, by rfl⟩ : syracuseStep 1535599 = 2303399) B2303399
theorem B2592425 : Blo 1534464 2592425 := bstep (se 2 (by rfl) ⟨972159, by rfl⟩ : syracuseStep 2592425 = 1944319) B1944319
theorem B1535719 : Blo 1534464 1535719 := bstep (se 1 (by rfl) ⟨1151789, by rfl⟩ : syracuseStep 1535719 = 2303579) B2303579
theorem B3452831 : Blo 1534464 3452831 := bstep (se 1 (by rfl) ⟨2589623, by rfl⟩ : syracuseStep 3452831 = 5179247) B5179247
theorem B1535911 : Blo 1534464 1535911 := bstep (se 1 (by rfl) ⟨1151933, by rfl⟩ : syracuseStep 1535911 = 2303867) B2303867
theorem B7770167 : Blo 1534464 7770167 := bstep (se 1 (by rfl) ⟨5827625, by rfl⟩ : syracuseStep 7770167 = 11655251) B11655251
theorem B1536071 : Blo 1534464 1536071 := bstep (se 1 (by rfl) ⟨1152053, by rfl⟩ : syracuseStep 1536071 = 2304107) B2304107
theorem B1536191 : Blo 1534464 1536191 := bstep (se 1 (by rfl) ⟨1152143, by rfl⟩ : syracuseStep 1536191 = 2304287) B2304287
theorem B39874841 : Blo 1534464 39874841 := bstep (se 2 (by rfl) ⟨14953065, by rfl⟩ : syracuseStep 39874841 = 29906131) B29906131
theorem B3453281 : Blo 1534464 3453281 := bstep (se 2 (by rfl) ⟨1294980, by rfl⟩ : syracuseStep 3453281 = 2589961) B2589961
theorem B3453659 : Blo 1534464 3453659 := bstep (se 1 (by rfl) ⟨2590244, by rfl⟩ : syracuseStep 3453659 = 5180489) B5180489
theorem B4371175 : Blo 1534464 4371175 := bstep (se 1 (by rfl) ⟨3278381, by rfl⟩ : syracuseStep 4371175 = 6556763) B6556763
theorem B14791673 : Blo 1534464 14791673 := bstep (se 2 (by rfl) ⟨5546877, by rfl⟩ : syracuseStep 14791673 = 11093755) B11093755
theorem B22426739 : Blo 1534464 22426739 := bstep (se 1 (by rfl) ⟨16820054, by rfl⟩ : syracuseStep 22426739 = 33640109) B33640109
theorem B3454073 : Blo 1534464 3454073 := bstep (se 2 (by rfl) ⟨1295277, by rfl⟩ : syracuseStep 3454073 = 2590555) B2590555
theorem B4920545 : Blo 1534464 4920545 := bstep (se 2 (by rfl) ⟨1845204, by rfl⟩ : syracuseStep 4920545 = 3690409) B3690409
theorem B15979771 : Blo 1534464 15979771 := bstep (se 1 (by rfl) ⟨11984828, by rfl⟩ : syracuseStep 15979771 = 23969657) B23969657
theorem B31528361 : Blo 1534464 31528361 := bstep (se 2 (by rfl) ⟨11823135, by rfl⟩ : syracuseStep 31528361 = 23646271) B23646271
theorem B5182973 : Blo 1534464 5182973 := bstep (se 3 (by rfl) ⟨971807, by rfl⟩ : syracuseStep 5182973 = 1943615) B1943615
theorem B5183081 : Blo 1534464 5183081 := bstep (se 2 (by rfl) ⟨1943655, by rfl⟩ : syracuseStep 5183081 = 3887311) B3887311
theorem B126039887 : Blo 1534464 126039887 := bstep (se 1 (by rfl) ⟨94529915, by rfl⟩ : syracuseStep 126039887 = 189059831) B189059831
theorem B3454847 : Blo 1534464 3454847 := bstep (se 1 (by rfl) ⟨2591135, by rfl⟩ : syracuseStep 3454847 = 5182271) B5182271
theorem B3454955 : Blo 1534464 3454955 := bstep (se 1 (by rfl) ⟨2591216, by rfl⟩ : syracuseStep 3454955 = 5182433) B5182433
theorem B2185337 : Blo 1534464 2185337 := bstep (se 2 (by rfl) ⟨819501, by rfl⟩ : syracuseStep 2185337 = 1639003) B1639003
theorem B7772435 : Blo 1534464 7772435 := bstep (se 1 (by rfl) ⟨5829326, by rfl⟩ : syracuseStep 7772435 = 11658653) B11658653
theorem B8747453 : Blo 1534464 8747453 := bstep (se 3 (by rfl) ⟨1640147, by rfl⟩ : syracuseStep 8747453 = 3280295) B3280295
theorem B1727023 : Blo 1534464 1727023 := bstep (se 1 (by rfl) ⟨1295267, by rfl⟩ : syracuseStep 1727023 = 2590535) B2590535
theorem B33200711 : Blo 1534464 33200711 := bstep (se 1 (by rfl) ⟨24900533, by rfl⟩ : syracuseStep 33200711 = 49801067) B49801067
theorem B1727131 : Blo 1534464 1727131 := bstep (se 1 (by rfl) ⟨1295348, by rfl⟩ : syracuseStep 1727131 = 2590697) B2590697
theorem B8862365 : Blo 1534464 8862365 := bstep (se 3 (by rfl) ⟨1661693, by rfl⟩ : syracuseStep 8862365 = 3323387) B3323387
theorem B7478011 : Blo 1534464 7478011 := bstep (se 1 (by rfl) ⟨5608508, by rfl⟩ : syracuseStep 7478011 = 11217017) B11217017
theorem B126081917 : Blo 1534464 126081917 := bstep (se 3 (by rfl) ⟨23640359, by rfl⟩ : syracuseStep 126081917 = 47280719) B47280719
theorem B1727455 : Blo 1534464 1727455 := bstep (se 1 (by rfl) ⟨1295591, by rfl⟩ : syracuseStep 1727455 = 2591183) B2591183
theorem B9837605 : Blo 1534464 9837605 := bstep (se 4 (by rfl) ⟨922275, by rfl⟩ : syracuseStep 9837605 = 1844551) B1844551
theorem B1728031 : Blo 1534464 1728031 := bstep (se 1 (by rfl) ⟨1296023, by rfl⟩ : syracuseStep 1728031 = 2592047) B2592047
theorem B1728103 : Blo 1534464 1728103 := bstep (se 1 (by rfl) ⟨1296077, by rfl⟩ : syracuseStep 1728103 = 2592155) B2592155
theorem B17481419 : Blo 1534464 17481419 := bstep (se 1 (by rfl) ⟨13111064, by rfl⟩ : syracuseStep 17481419 = 26222129) B26222129
theorem B11976457 : Blo 1534464 11976457 := bstep (se 2 (by rfl) ⟨4491171, by rfl⟩ : syracuseStep 11976457 = 8982343) B8982343
theorem B1728319 : Blo 1534464 1728319 := bstep (se 1 (by rfl) ⟨1296239, by rfl⟩ : syracuseStep 1728319 = 2592479) B2592479
theorem B9977755 : Blo 1534464 9977755 := bstep (se 1 (by rfl) ⟨7483316, by rfl⟩ : syracuseStep 9977755 = 14966633) B14966633
theorem B2916319 : Blo 1534464 2916319 := bstep (se 1 (by rfl) ⟨2187239, by rfl⟩ : syracuseStep 2916319 = 4374479) B4374479
theorem B2301935 : Blo 1534464 2301935 := bstep (se 1 (by rfl) ⟨1726451, by rfl⟩ : syracuseStep 2301935 = 3452903) B3452903
theorem B3457007 : Blo 1534464 3457007 := bstep (se 1 (by rfl) ⟨2592755, by rfl⟩ : syracuseStep 3457007 = 5185511) B5185511
theorem B26583227 : Blo 1534464 26583227 := bstep (se 1 (by rfl) ⟨19937420, by rfl⟩ : syracuseStep 26583227 = 39874841) B39874841
theorem B2302187 : Blo 1534464 2302187 := bstep (se 1 (by rfl) ⟨1726640, by rfl⟩ : syracuseStep 2302187 = 3453281) B3453281
theorem B2302439 : Blo 1534464 2302439 := bstep (se 1 (by rfl) ⟨1726829, by rfl⟩ : syracuseStep 2302439 = 3453659) B3453659
theorem B2302697 : Blo 1534464 2302697 := bstep (se 2 (by rfl) ⟨863511, by rfl⟩ : syracuseStep 2302697 = 1727023) B1727023
theorem B14951159 : Blo 1534464 14951159 := bstep (se 1 (by rfl) ⟨11213369, by rfl⟩ : syracuseStep 14951159 = 22426739) B22426739
theorem B2302715 : Blo 1534464 2302715 := bstep (se 1 (by rfl) ⟨1727036, by rfl⟩ : syracuseStep 2302715 = 3454073) B3454073
theorem B2302841 : Blo 1534464 2302841 := bstep (se 2 (by rfl) ⟨863565, by rfl⟩ : syracuseStep 2302841 = 1727131) B1727131
theorem B2589563 : Blo 1534464 2589563 := bstep (se 1 (by rfl) ⟨1942172, by rfl⟩ : syracuseStep 2589563 = 3884345) B3884345
theorem B2589799 : Blo 1534464 2589799 := bstep (se 1 (by rfl) ⟨1942349, by rfl⟩ : syracuseStep 2589799 = 3884699) B3884699
theorem B84026591 : Blo 1534464 84026591 := bstep (se 1 (by rfl) ⟨63019943, by rfl⟩ : syracuseStep 84026591 = 126039887) B126039887
theorem B2303231 : Blo 1534464 2303231 := bstep (se 1 (by rfl) ⟨1727423, by rfl⟩ : syracuseStep 2303231 = 3454847) B3454847
theorem B2303273 : Blo 1534464 2303273 := bstep (se 2 (by rfl) ⟨863727, by rfl⟩ : syracuseStep 2303273 = 1727455) B1727455
theorem B2303303 : Blo 1534464 2303303 := bstep (se 1 (by rfl) ⟨1727477, by rfl⟩ : syracuseStep 2303303 = 3454955) B3454955
theorem B3884719 : Blo 1534464 3884719 := bstep (se 1 (by rfl) ⟨2913539, by rfl⟩ : syracuseStep 3884719 = 5827079) B5827079
theorem B2304041 : Blo 1534464 2304041 := bstep (se 2 (by rfl) ⟨864015, by rfl⟩ : syracuseStep 2304041 = 1728031) B1728031
theorem B2304137 : Blo 1534464 2304137 := bstep (se 2 (by rfl) ⟨864051, by rfl⟩ : syracuseStep 2304137 = 1728103) B1728103
theorem B15968609 : Blo 1534464 15968609 := bstep (se 2 (by rfl) ⟨5988228, by rfl⟩ : syracuseStep 15968609 = 11976457) B11976457
theorem B2304425 : Blo 1534464 2304425 := bstep (se 2 (by rfl) ⟨864159, by rfl⟩ : syracuseStep 2304425 = 1728319) B1728319
theorem B1534623 : Blo 1534464 1534623 := bstep (se 1 (by rfl) ⟨1150967, by rfl⟩ : syracuseStep 1534623 = 2301935) B2301935
theorem B2304671 : Blo 1534464 2304671 := bstep (se 1 (by rfl) ⟨1728503, by rfl⟩ : syracuseStep 2304671 = 3457007) B3457007
theorem B1534655 : Blo 1534464 1534655 := bstep (se 1 (by rfl) ⟨1150991, by rfl⟩ : syracuseStep 1534655 = 2301983) B2301983
theorem B5180111 : Blo 1534464 5180111 := bstep (se 1 (by rfl) ⟨3885083, by rfl⟩ : syracuseStep 5180111 = 7770167) B7770167
theorem B1534783 : Blo 1534464 1534783 := bstep (se 1 (by rfl) ⟨1151087, by rfl⟩ : syracuseStep 1534783 = 2302175) B2302175
theorem B7777133 : Blo 1534464 7777133 := bstep (se 3 (by rfl) ⟨1458212, by rfl⟩ : syracuseStep 7777133 = 2916425) B2916425
theorem B5827565 : Blo 1534464 5827565 := bstep (se 3 (by rfl) ⟨1092668, by rfl⟩ : syracuseStep 5827565 = 2185337) B2185337
theorem B1535079 : Blo 1534464 1535079 := bstep (se 1 (by rfl) ⟨1151309, by rfl⟩ : syracuseStep 1535079 = 2302619) B2302619
theorem B5828233 : Blo 1534464 5828233 := bstep (se 2 (by rfl) ⟨2185587, by rfl⟩ : syracuseStep 5828233 = 4371175) B4371175
theorem B1535643 : Blo 1534464 1535643 := bstep (se 1 (by rfl) ⟨1151732, by rfl⟩ : syracuseStep 1535643 = 2303465) B2303465
theorem B39882725 : Blo 1534464 39882725 := bstep (se 4 (by rfl) ⟨3739005, by rfl⟩ : syracuseStep 39882725 = 7478011) B7478011
theorem B85225445 : Blo 1534464 85225445 := bstep (se 4 (by rfl) ⟨7989885, by rfl⟩ : syracuseStep 85225445 = 15979771) B15979771
theorem B1536111 : Blo 1534464 1536111 := bstep (se 1 (by rfl) ⟨1152083, by rfl⟩ : syracuseStep 1536111 = 2304167) B2304167
theorem B5181623 : Blo 1534464 5181623 := bstep (se 1 (by rfl) ⟨3886217, by rfl⟩ : syracuseStep 5181623 = 7772435) B7772435
theorem B84054611 : Blo 1534464 84054611 := bstep (se 1 (by rfl) ⟨63040958, by rfl⟩ : syracuseStep 84054611 = 126081917) B126081917
theorem B6558403 : Blo 1534464 6558403 := bstep (se 1 (by rfl) ⟨4918802, by rfl⟩ : syracuseStep 6558403 = 9837605) B9837605
theorem B5182217 : Blo 1534464 5182217 := bstep (se 2 (by rfl) ⟨1943331, by rfl⟩ : syracuseStep 5182217 = 3886663) B3886663
theorem B11654279 : Blo 1534464 11654279 := bstep (se 1 (by rfl) ⟨8740709, by rfl⟩ : syracuseStep 11654279 = 17481419) B17481419
theorem B3888425 : Blo 1534464 3888425 := bstep (se 2 (by rfl) ⟨1458159, by rfl⟩ : syracuseStep 3888425 = 2916319) B2916319
theorem B5912185 : Blo 1534464 5912185 := bstep (se 2 (by rfl) ⟨2217069, by rfl⟩ : syracuseStep 5912185 = 4434139) B4434139
theorem B37361411 : Blo 1534464 37361411 := bstep (se 1 (by rfl) ⟨28021058, by rfl⟩ : syracuseStep 37361411 = 56042117) B56042117
theorem B13121453 : Blo 1534464 13121453 := bstep (se 3 (by rfl) ⟨2460272, by rfl⟩ : syracuseStep 13121453 = 4920545) B4920545
theorem B9861115 : Blo 1534464 9861115 := bstep (se 1 (by rfl) ⟨7395836, by rfl⟩ : syracuseStep 9861115 = 14791673) B14791673
theorem B21018907 : Blo 1534464 21018907 := bstep (se 1 (by rfl) ⟨15764180, by rfl⟩ : syracuseStep 21018907 = 31528361) B31528361
theorem B7100711 : Blo 1534464 7100711 := bstep (se 1 (by rfl) ⟨5325533, by rfl⟩ : syracuseStep 7100711 = 10651067) B10651067
theorem B3455315 : Blo 1534464 3455315 := bstep (se 1 (by rfl) ⟨2591486, by rfl⟩ : syracuseStep 3455315 = 5182973) B5182973
theorem B3455387 : Blo 1534464 3455387 := bstep (se 1 (by rfl) ⟨2591540, by rfl⟩ : syracuseStep 3455387 = 5183081) B5183081
theorem B29932001 : Blo 1534464 29932001 := bstep (se 2 (by rfl) ⟨11224500, by rfl⟩ : syracuseStep 29932001 = 22449001) B22449001
theorem B5831635 : Blo 1534464 5831635 := bstep (se 1 (by rfl) ⟨4373726, by rfl⟩ : syracuseStep 5831635 = 8747453) B8747453
theorem B19667933 : Blo 1534464 19667933 := bstep (se 3 (by rfl) ⟨3687737, by rfl⟩ : syracuseStep 19667933 = 7375475) B7375475
theorem B22133807 : Blo 1534464 22133807 := bstep (se 1 (by rfl) ⟨16600355, by rfl⟩ : syracuseStep 22133807 = 33200711) B33200711
theorem B23632973 : Blo 1534464 23632973 := bstep (se 3 (by rfl) ⟨4431182, by rfl⟩ : syracuseStep 23632973 = 8862365) B8862365
theorem B5185079 : Blo 1534464 5185079 := bstep (se 1 (by rfl) ⟨3888809, by rfl⟩ : syracuseStep 5185079 = 7777619) B7777619
theorem B1728283 : Blo 1534464 1728283 := bstep (se 1 (by rfl) ⟨1296212, by rfl⟩ : syracuseStep 1728283 = 2592425) B2592425
theorem B13303673 : Blo 1534464 13303673 := bstep (se 2 (by rfl) ⟨4988877, by rfl⟩ : syracuseStep 13303673 = 9977755) B9977755
theorem B2301887 : Blo 1534464 2301887 := bstep (se 1 (by rfl) ⟨1726415, by rfl⟩ : syracuseStep 2301887 = 3452831) B3452831
theorem B28025209 : Blo 1534464 28025209 := bstep (se 2 (by rfl) ⟨10509453, by rfl⟩ : syracuseStep 28025209 = 21018907) B21018907
theorem B56017727 : Blo 1534464 56017727 := bstep (se 1 (by rfl) ⟨42013295, by rfl⟩ : syracuseStep 56017727 = 84026591) B84026591
theorem B7775513 : Blo 1534464 7775513 := bstep (se 2 (by rfl) ⟨2915817, by rfl⟩ : syracuseStep 7775513 = 5831635) B5831635
theorem B2303543 : Blo 1534464 2303543 := bstep (se 1 (by rfl) ⟨1727657, by rfl⟩ : syracuseStep 2303543 = 3455315) B3455315
theorem B2303591 : Blo 1534464 2303591 := bstep (se 1 (by rfl) ⟨1727693, by rfl⟩ : syracuseStep 2303591 = 3455387) B3455387
theorem B3885043 : Blo 1534464 3885043 := bstep (se 1 (by rfl) ⟨2913782, by rfl⟩ : syracuseStep 3885043 = 5827565) B5827565
theorem B14755871 : Blo 1534464 14755871 := bstep (se 1 (by rfl) ⟨11066903, by rfl⟩ : syracuseStep 14755871 = 22133807) B22133807
theorem B15755315 : Blo 1534464 15755315 := bstep (se 1 (by rfl) ⟨11816486, by rfl⟩ : syracuseStep 15755315 = 23632973) B23632973
theorem B7882913 : Blo 1534464 7882913 := bstep (se 2 (by rfl) ⟨2956092, by rfl⟩ : syracuseStep 7882913 = 5912185) B5912185
theorem B5179625 : Blo 1534464 5179625 := bstep (se 2 (by rfl) ⟨1942359, by rfl⟩ : syracuseStep 5179625 = 3884719) B3884719
theorem B2304377 : Blo 1534464 2304377 := bstep (se 2 (by rfl) ⟨864141, by rfl⟩ : syracuseStep 2304377 = 1728283) B1728283
theorem B1534591 : Blo 1534464 1534591 := bstep (se 1 (by rfl) ⟨1150943, by rfl⟩ : syracuseStep 1534591 = 2301887) B2301887
theorem B17722151 : Blo 1534464 17722151 := bstep (se 1 (by rfl) ⟨13291613, by rfl⟩ : syracuseStep 17722151 = 26583227) B26583227
theorem B1534791 : Blo 1534464 1534791 := bstep (se 1 (by rfl) ⟨1151093, by rfl⟩ : syracuseStep 1534791 = 2302187) B2302187
theorem B1534959 : Blo 1534464 1534959 := bstep (se 1 (by rfl) ⟨1151219, by rfl⟩ : syracuseStep 1534959 = 2302439) B2302439
theorem B1535131 : Blo 1534464 1535131 := bstep (se 1 (by rfl) ⟨1151348, by rfl⟩ : syracuseStep 1535131 = 2302697) B2302697
theorem B1535143 : Blo 1534464 1535143 := bstep (se 1 (by rfl) ⟨1151357, by rfl⟩ : syracuseStep 1535143 = 2302715) B2302715
theorem B1535227 : Blo 1534464 1535227 := bstep (se 1 (by rfl) ⟨1151420, by rfl⟩ : syracuseStep 1535227 = 2302841) B2302841
theorem B7769519 : Blo 1534464 7769519 := bstep (se 1 (by rfl) ⟨5827139, by rfl⟩ : syracuseStep 7769519 = 11654279) B11654279
theorem B1535487 : Blo 1534464 1535487 := bstep (se 1 (by rfl) ⟨1151615, by rfl⟩ : syracuseStep 1535487 = 2303231) B2303231
theorem B1535515 : Blo 1534464 1535515 := bstep (se 1 (by rfl) ⟨1151636, by rfl⟩ : syracuseStep 1535515 = 2303273) B2303273
theorem B2592283 : Blo 1534464 2592283 := bstep (se 1 (by rfl) ⟨1944212, by rfl⟩ : syracuseStep 2592283 = 3888425) B3888425
theorem B1535535 : Blo 1534464 1535535 := bstep (se 1 (by rfl) ⟨1151651, by rfl⟩ : syracuseStep 1535535 = 2303303) B2303303
theorem B8744537 : Blo 1534464 8744537 := bstep (se 2 (by rfl) ⟨3279201, by rfl⟩ : syracuseStep 8744537 = 6558403) B6558403
theorem B24907607 : Blo 1534464 24907607 := bstep (se 1 (by rfl) ⟨18680705, by rfl⟩ : syracuseStep 24907607 = 37361411) B37361411
theorem B1536027 : Blo 1534464 1536027 := bstep (se 1 (by rfl) ⟨1152020, by rfl⟩ : syracuseStep 1536027 = 2304041) B2304041
theorem B1536091 : Blo 1534464 1536091 := bstep (se 1 (by rfl) ⟨1152068, by rfl⟩ : syracuseStep 1536091 = 2304137) B2304137
theorem B3453065 : Blo 1534464 3453065 := bstep (se 2 (by rfl) ⟨1294899, by rfl⟩ : syracuseStep 3453065 = 2589799) B2589799
theorem B224145629 : Blo 1534464 224145629 := bstep (se 3 (by rfl) ⟨42027305, by rfl⟩ : syracuseStep 224145629 = 84054611) B84054611
theorem B10645739 : Blo 1534464 10645739 := bstep (se 1 (by rfl) ⟨7984304, by rfl⟩ : syracuseStep 10645739 = 15968609) B15968609
theorem B1536283 : Blo 1534464 1536283 := bstep (se 1 (by rfl) ⟨1152212, by rfl⟩ : syracuseStep 1536283 = 2304425) B2304425
theorem B1536447 : Blo 1534464 1536447 := bstep (se 1 (by rfl) ⟨1152335, by rfl⟩ : syracuseStep 1536447 = 2304671) B2304671
theorem B3453407 : Blo 1534464 3453407 := bstep (se 1 (by rfl) ⟨2590055, by rfl⟩ : syracuseStep 3453407 = 5180111) B5180111
theorem B13111955 : Blo 1534464 13111955 := bstep (se 1 (by rfl) ⟨9833966, by rfl⟩ : syracuseStep 13111955 = 19667933) B19667933
theorem B7770977 : Blo 1534464 7770977 := bstep (se 2 (by rfl) ⟨2914116, by rfl⟩ : syracuseStep 7770977 = 5828233) B5828233
theorem B8869115 : Blo 1534464 8869115 := bstep (se 1 (by rfl) ⟨6651836, by rfl⟩ : syracuseStep 8869115 = 13303673) B13303673
theorem B26588483 : Blo 1534464 26588483 := bstep (se 1 (by rfl) ⟨19941362, by rfl⟩ : syracuseStep 26588483 = 39882725) B39882725
theorem B56816963 : Blo 1534464 56816963 := bstep (se 1 (by rfl) ⟨42612722, by rfl⟩ : syracuseStep 56816963 = 85225445) B85225445
theorem B3454415 : Blo 1534464 3454415 := bstep (se 1 (by rfl) ⟨2590811, by rfl⟩ : syracuseStep 3454415 = 5181623) B5181623
theorem B9967439 : Blo 1534464 9967439 := bstep (se 1 (by rfl) ⟨7475579, by rfl⟩ : syracuseStep 9967439 = 14951159) B14951159
theorem B3454811 : Blo 1534464 3454811 := bstep (se 1 (by rfl) ⟨2591108, by rfl⟩ : syracuseStep 3454811 = 5182217) B5182217
theorem B1726375 : Blo 1534464 1726375 := bstep (se 1 (by rfl) ⟨1294781, by rfl⟩ : syracuseStep 1726375 = 2589563) B2589563
theorem B8747635 : Blo 1534464 8747635 := bstep (se 1 (by rfl) ⟨6560726, by rfl⟩ : syracuseStep 8747635 = 13121453) B13121453
theorem B4733807 : Blo 1534464 4733807 := bstep (se 1 (by rfl) ⟨3550355, by rfl⟩ : syracuseStep 4733807 = 7100711) B7100711
theorem B19954667 : Blo 1534464 19954667 := bstep (se 1 (by rfl) ⟨14966000, by rfl⟩ : syracuseStep 19954667 = 29932001) B29932001
theorem B5184755 : Blo 1534464 5184755 := bstep (se 1 (by rfl) ⟨3888566, by rfl⟩ : syracuseStep 5184755 = 7777133) B7777133
theorem B3456719 : Blo 1534464 3456719 := bstep (se 1 (by rfl) ⟨2592539, by rfl⟩ : syracuseStep 3456719 = 5185079) B5185079
theorem B13148153 : Blo 1534464 13148153 := bstep (se 2 (by rfl) ⟨4930557, by rfl⟩ : syracuseStep 13148153 = 9861115) B9861115
theorem B2302043 : Blo 1534464 2302043 := bstep (se 1 (by rfl) ⟨1726532, by rfl⟩ : syracuseStep 2302043 = 3453065) B3453065
theorem B149430419 : Blo 1534464 149430419 := bstep (se 1 (by rfl) ⟨112072814, by rfl⟩ : syracuseStep 149430419 = 224145629) B224145629
theorem B2302271 : Blo 1534464 2302271 := bstep (se 1 (by rfl) ⟨1726703, by rfl⟩ : syracuseStep 2302271 = 3453407) B3453407
theorem B8741303 : Blo 1534464 8741303 := bstep (se 1 (by rfl) ⟨6555977, by rfl⟩ : syracuseStep 8741303 = 13111955) B13111955
theorem B2302943 : Blo 1534464 2302943 := bstep (se 1 (by rfl) ⟨1727207, by rfl⟩ : syracuseStep 2302943 = 3454415) B3454415
theorem B6644959 : Blo 1534464 6644959 := bstep (se 1 (by rfl) ⟨4983719, by rfl⟩ : syracuseStep 6644959 = 9967439) B9967439
theorem B2303207 : Blo 1534464 2303207 := bstep (se 1 (by rfl) ⟨1727405, by rfl⟩ : syracuseStep 2303207 = 3454811) B3454811
theorem B11814767 : Blo 1534464 11814767 := bstep (se 1 (by rfl) ⟨8861075, by rfl⟩ : syracuseStep 11814767 = 17722151) B17722151
theorem B5179679 : Blo 1534464 5179679 := bstep (se 1 (by rfl) ⟨3884759, by rfl⟩ : syracuseStep 5179679 = 7769519) B7769519
theorem B2304479 : Blo 1534464 2304479 := bstep (se 1 (by rfl) ⟨1728359, by rfl⟩ : syracuseStep 2304479 = 3456719) B3456719
theorem B5180057 : Blo 1534464 5180057 := bstep (se 2 (by rfl) ⟨1942521, by rfl⟩ : syracuseStep 5180057 = 3885043) B3885043
theorem B7097159 : Blo 1534464 7097159 := bstep (se 1 (by rfl) ⟨5322869, by rfl⟩ : syracuseStep 7097159 = 10645739) B10645739
theorem B5180651 : Blo 1534464 5180651 := bstep (se 1 (by rfl) ⟨3885488, by rfl⟩ : syracuseStep 5180651 = 7770977) B7770977
theorem B8765435 : Blo 1534464 8765435 := bstep (se 1 (by rfl) ⟨6574076, by rfl⟩ : syracuseStep 8765435 = 13148153) B13148153
theorem B1535695 : Blo 1534464 1535695 := bstep (se 1 (by rfl) ⟨1151771, by rfl⟩ : syracuseStep 1535695 = 2303543) B2303543
theorem B1535727 : Blo 1534464 1535727 := bstep (se 1 (by rfl) ⟨1151795, by rfl⟩ : syracuseStep 1535727 = 2303591) B2303591
theorem B5255275 : Blo 1534464 5255275 := bstep (se 1 (by rfl) ⟨3941456, by rfl⟩ : syracuseStep 5255275 = 7882913) B7882913
theorem B3453083 : Blo 1534464 3453083 := bstep (se 1 (by rfl) ⟨2589812, by rfl⟩ : syracuseStep 3453083 = 5179625) B5179625
theorem B1536251 : Blo 1534464 1536251 := bstep (se 1 (by rfl) ⟨1152188, by rfl⟩ : syracuseStep 1536251 = 2304377) B2304377
theorem B149467781 : Blo 1534464 149467781 := bstep (se 4 (by rfl) ⟨14012604, by rfl⟩ : syracuseStep 149467781 = 28025209) B28025209
theorem B5829691 : Blo 1534464 5829691 := bstep (se 1 (by rfl) ⟨4372268, by rfl⟩ : syracuseStep 5829691 = 8744537) B8744537
theorem B42014173 : Blo 1534464 42014173 := bstep (se 3 (by rfl) ⟨7877657, by rfl⟩ : syracuseStep 42014173 = 15755315) B15755315
theorem B37345151 : Blo 1534464 37345151 := bstep (se 1 (by rfl) ⟨28008863, by rfl⟩ : syracuseStep 37345151 = 56017727) B56017727
theorem B11663513 : Blo 1534464 11663513 := bstep (se 2 (by rfl) ⟨4373817, by rfl⟩ : syracuseStep 11663513 = 8747635) B8747635
theorem B5912743 : Blo 1534464 5912743 := bstep (se 1 (by rfl) ⟨4434557, by rfl⟩ : syracuseStep 5912743 = 8869115) B8869115
theorem B5183675 : Blo 1534464 5183675 := bstep (se 1 (by rfl) ⟨3887756, by rfl⟩ : syracuseStep 5183675 = 7775513) B7775513
theorem B17725655 : Blo 1534464 17725655 := bstep (se 1 (by rfl) ⟨13294241, by rfl⟩ : syracuseStep 17725655 = 26588483) B26588483
theorem B37877975 : Blo 1534464 37877975 := bstep (se 1 (by rfl) ⟨28408481, by rfl⟩ : syracuseStep 37877975 = 56816963) B56816963
theorem B9837247 : Blo 1534464 9837247 := bstep (se 1 (by rfl) ⟨7377935, by rfl⟩ : syracuseStep 9837247 = 14755871) B14755871
theorem B13303111 : Blo 1534464 13303111 := bstep (se 1 (by rfl) ⟨9977333, by rfl⟩ : syracuseStep 13303111 = 19954667) B19954667
theorem B3456377 : Blo 1534464 3456377 := bstep (se 2 (by rfl) ⟨1296141, by rfl⟩ : syracuseStep 3456377 = 2592283) B2592283
theorem B3456503 : Blo 1534464 3456503 := bstep (se 1 (by rfl) ⟨2592377, by rfl⟩ : syracuseStep 3456503 = 5184755) B5184755
theorem B12623485 : Blo 1534464 12623485 := bstep (se 3 (by rfl) ⟨2366903, by rfl⟩ : syracuseStep 12623485 = 4733807) B4733807
theorem B2301833 : Blo 1534464 2301833 := bstep (se 2 (by rfl) ⟨863187, by rfl⟩ : syracuseStep 2301833 = 1726375) B1726375
theorem B16605071 : Blo 1534464 16605071 := bstep (se 1 (by rfl) ⟨12453803, by rfl⟩ : syracuseStep 16605071 = 24907607) B24907607
theorem B2302055 : Blo 1534464 2302055 := bstep (se 1 (by rfl) ⟨1726541, by rfl⟩ : syracuseStep 2302055 = 3453083) B3453083
theorem B13116329 : Blo 1534464 13116329 := bstep (se 2 (by rfl) ⟨4918623, by rfl⟩ : syracuseStep 13116329 = 9837247) B9837247
theorem B35439781 : Blo 1534464 35439781 := bstep (se 4 (by rfl) ⟨3322479, by rfl⟩ : syracuseStep 35439781 = 6644959) B6644959
theorem B24896767 : Blo 1534464 24896767 := bstep (se 1 (by rfl) ⟨18672575, by rfl⟩ : syracuseStep 24896767 = 37345151) B37345151
theorem B7775675 : Blo 1534464 7775675 := bstep (se 1 (by rfl) ⟨5831756, by rfl⟩ : syracuseStep 7775675 = 11663513) B11663513
theorem B17737481 : Blo 1534464 17737481 := bstep (se 2 (by rfl) ⟨6651555, by rfl⟩ : syracuseStep 17737481 = 13303111) B13303111
theorem B56018897 : Blo 1534464 56018897 := bstep (se 2 (by rfl) ⟨21007086, by rfl⟩ : syracuseStep 56018897 = 42014173) B42014173
theorem B2304251 : Blo 1534464 2304251 := bstep (se 1 (by rfl) ⟨1728188, by rfl⟩ : syracuseStep 2304251 = 3456377) B3456377
theorem B2304335 : Blo 1534464 2304335 := bstep (se 1 (by rfl) ⟨1728251, by rfl⟩ : syracuseStep 2304335 = 3456503) B3456503
theorem B1534555 : Blo 1534464 1534555 := bstep (se 1 (by rfl) ⟨1150916, by rfl⟩ : syracuseStep 1534555 = 2301833) B2301833
theorem B11070047 : Blo 1534464 11070047 := bstep (se 1 (by rfl) ⟨8302535, by rfl⟩ : syracuseStep 11070047 = 16605071) B16605071
theorem B5843623 : Blo 1534464 5843623 := bstep (se 1 (by rfl) ⟨4382717, by rfl⟩ : syracuseStep 5843623 = 8765435) B8765435
theorem B1534695 : Blo 1534464 1534695 := bstep (se 1 (by rfl) ⟨1151021, by rfl⟩ : syracuseStep 1534695 = 2302043) B2302043
theorem B7007033 : Blo 1534464 7007033 := bstep (se 2 (by rfl) ⟨2627637, by rfl⟩ : syracuseStep 7007033 = 5255275) B5255275
theorem B1534847 : Blo 1534464 1534847 := bstep (se 1 (by rfl) ⟨1151135, by rfl⟩ : syracuseStep 1534847 = 2302271) B2302271
theorem B7883657 : Blo 1534464 7883657 := bstep (se 2 (by rfl) ⟨2956371, by rfl⟩ : syracuseStep 7883657 = 5912743) B5912743
theorem B5827535 : Blo 1534464 5827535 := bstep (se 1 (by rfl) ⟨4370651, by rfl⟩ : syracuseStep 5827535 = 8741303) B8741303
theorem B1535295 : Blo 1534464 1535295 := bstep (se 1 (by rfl) ⟨1151471, by rfl⟩ : syracuseStep 1535295 = 2302943) B2302943
theorem B1535471 : Blo 1534464 1535471 := bstep (se 1 (by rfl) ⟨1151603, by rfl⟩ : syracuseStep 1535471 = 2303207) B2303207
theorem B7876511 : Blo 1534464 7876511 := bstep (se 1 (by rfl) ⟨5907383, by rfl⟩ : syracuseStep 7876511 = 11814767) B11814767
theorem B11817103 : Blo 1534464 11817103 := bstep (se 1 (by rfl) ⟨8862827, by rfl⟩ : syracuseStep 11817103 = 17725655) B17725655
theorem B25251983 : Blo 1534464 25251983 := bstep (se 1 (by rfl) ⟨18938987, by rfl⟩ : syracuseStep 25251983 = 37877975) B37877975
theorem B3453119 : Blo 1534464 3453119 := bstep (se 1 (by rfl) ⟨2589839, by rfl⟩ : syracuseStep 3453119 = 5179679) B5179679
theorem B1536319 : Blo 1534464 1536319 := bstep (se 1 (by rfl) ⟨1152239, by rfl⟩ : syracuseStep 1536319 = 2304479) B2304479
theorem B3453371 : Blo 1534464 3453371 := bstep (se 1 (by rfl) ⟨2590028, by rfl⟩ : syracuseStep 3453371 = 5180057) B5180057
theorem B4731439 : Blo 1534464 4731439 := bstep (se 1 (by rfl) ⟨3548579, by rfl⟩ : syracuseStep 4731439 = 7097159) B7097159
theorem B3453767 : Blo 1534464 3453767 := bstep (se 1 (by rfl) ⟨2590325, by rfl⟩ : syracuseStep 3453767 = 5180651) B5180651
theorem B16831313 : Blo 1534464 16831313 := bstep (se 2 (by rfl) ⟨6311742, by rfl⟩ : syracuseStep 16831313 = 12623485) B12623485
theorem B99620279 : Blo 1534464 99620279 := bstep (se 1 (by rfl) ⟨74715209, by rfl⟩ : syracuseStep 99620279 = 149430419) B149430419
theorem B99645187 : Blo 1534464 99645187 := bstep (se 1 (by rfl) ⟨74733890, by rfl⟩ : syracuseStep 99645187 = 149467781) B149467781
theorem B7772921 : Blo 1534464 7772921 := bstep (se 2 (by rfl) ⟨2914845, by rfl⟩ : syracuseStep 7772921 = 5829691) B5829691
theorem B3455783 : Blo 1534464 3455783 := bstep (se 1 (by rfl) ⟨2591837, by rfl⟩ : syracuseStep 3455783 = 5183675) B5183675
theorem B16834655 : Blo 1534464 16834655 := bstep (se 1 (by rfl) ⟨12625991, by rfl⟩ : syracuseStep 16834655 = 25251983) B25251983
theorem B2302079 : Blo 1534464 2302079 := bstep (se 1 (by rfl) ⟨1726559, by rfl⟩ : syracuseStep 2302079 = 3453119) B3453119
theorem B2302247 : Blo 1534464 2302247 := bstep (se 1 (by rfl) ⟨1726685, by rfl⟩ : syracuseStep 2302247 = 3453371) B3453371
theorem B2302511 : Blo 1534464 2302511 := bstep (se 1 (by rfl) ⟨1726883, by rfl⟩ : syracuseStep 2302511 = 3453767) B3453767
theorem B6308585 : Blo 1534464 6308585 := bstep (se 2 (by rfl) ⟨2365719, by rfl⟩ : syracuseStep 6308585 = 4731439) B4731439
theorem B7791497 : Blo 1534464 7791497 := bstep (se 2 (by rfl) ⟨2921811, by rfl⟩ : syracuseStep 7791497 = 5843623) B5843623
theorem B66413519 : Blo 1534464 66413519 := bstep (se 1 (by rfl) ⟨49810139, by rfl⟩ : syracuseStep 66413519 = 99620279) B99620279
theorem B47253041 : Blo 1534464 47253041 := bstep (se 2 (by rfl) ⟨17719890, by rfl⟩ : syracuseStep 47253041 = 35439781) B35439781
theorem B33195689 : Blo 1534464 33195689 := bstep (se 2 (by rfl) ⟨12448383, by rfl⟩ : syracuseStep 33195689 = 24896767) B24896767
theorem B2303855 : Blo 1534464 2303855 := bstep (se 1 (by rfl) ⟨1727891, by rfl⟩ : syracuseStep 2303855 = 3455783) B3455783
theorem B3885023 : Blo 1534464 3885023 := bstep (se 1 (by rfl) ⟨2913767, by rfl⟩ : syracuseStep 3885023 = 5827535) B5827535
theorem B132860249 : Blo 1534464 132860249 := bstep (se 2 (by rfl) ⟨49822593, by rfl⟩ : syracuseStep 132860249 = 99645187) B99645187
theorem B1534703 : Blo 1534464 1534703 := bstep (se 1 (by rfl) ⟨1151027, by rfl⟩ : syracuseStep 1534703 = 2302055) B2302055
theorem B15756137 : Blo 1534464 15756137 := bstep (se 2 (by rfl) ⟨5908551, by rfl⟩ : syracuseStep 15756137 = 11817103) B11817103
theorem B8744219 : Blo 1534464 8744219 := bstep (se 1 (by rfl) ⟨6558164, by rfl⟩ : syracuseStep 8744219 = 13116329) B13116329
theorem B11824987 : Blo 1534464 11824987 := bstep (se 1 (by rfl) ⟨8868740, by rfl⟩ : syracuseStep 11824987 = 17737481) B17737481
theorem B1536167 : Blo 1534464 1536167 := bstep (se 1 (by rfl) ⟨1152125, by rfl⟩ : syracuseStep 1536167 = 2304251) B2304251
theorem B1536223 : Blo 1534464 1536223 := bstep (se 1 (by rfl) ⟨1152167, by rfl⟩ : syracuseStep 1536223 = 2304335) B2304335
theorem B29520125 : Blo 1534464 29520125 := bstep (se 3 (by rfl) ⟨5535023, by rfl⟩ : syracuseStep 29520125 = 11070047) B11070047
theorem B5181947 : Blo 1534464 5181947 := bstep (se 1 (by rfl) ⟨3886460, by rfl⟩ : syracuseStep 5181947 = 7772921) B7772921
theorem B5255771 : Blo 1534464 5255771 := bstep (se 1 (by rfl) ⟨3941828, by rfl⟩ : syracuseStep 5255771 = 7883657) B7883657
theorem B11220875 : Blo 1534464 11220875 := bstep (se 1 (by rfl) ⟨8415656, by rfl⟩ : syracuseStep 11220875 = 16831313) B16831313
theorem B5183783 : Blo 1534464 5183783 := bstep (se 1 (by rfl) ⟨3887837, by rfl⟩ : syracuseStep 5183783 = 7775675) B7775675
theorem B37345931 : Blo 1534464 37345931 := bstep (se 1 (by rfl) ⟨28009448, by rfl⟩ : syracuseStep 37345931 = 56018897) B56018897
theorem B18685421 : Blo 1534464 18685421 := bstep (se 3 (by rfl) ⟨3503516, by rfl⟩ : syracuseStep 18685421 = 7007033) B7007033
theorem B5251007 : Blo 1534464 5251007 := bstep (se 1 (by rfl) ⟨3938255, by rfl⟩ : syracuseStep 5251007 = 7876511) B7876511
theorem B44892413 : Blo 1534464 44892413 := bstep (se 3 (by rfl) ⟨8417327, by rfl⟩ : syracuseStep 44892413 = 16834655) B16834655
theorem B5194331 : Blo 1534464 5194331 := bstep (se 1 (by rfl) ⟨3895748, by rfl⟩ : syracuseStep 5194331 = 7791497) B7791497
theorem B7480583 : Blo 1534464 7480583 := bstep (se 1 (by rfl) ⟨5610437, by rfl⟩ : syracuseStep 7480583 = 11220875) B11220875
theorem B2590015 : Blo 1534464 2590015 := bstep (se 1 (by rfl) ⟨1942511, by rfl⟩ : syracuseStep 2590015 = 3885023) B3885023
theorem B88573499 : Blo 1534464 88573499 := bstep (se 1 (by rfl) ⟨66430124, by rfl⟩ : syracuseStep 88573499 = 132860249) B132860249
theorem B24897287 : Blo 1534464 24897287 := bstep (se 1 (by rfl) ⟨18672965, by rfl⟩ : syracuseStep 24897287 = 37345931) B37345931
theorem B10504091 : Blo 1534464 10504091 := bstep (se 1 (by rfl) ⟨7878068, by rfl⟩ : syracuseStep 10504091 = 15756137) B15756137
theorem B3500671 : Blo 1534464 3500671 := bstep (se 1 (by rfl) ⟨2625503, by rfl⟩ : syracuseStep 3500671 = 5251007) B5251007
theorem B1534719 : Blo 1534464 1534719 := bstep (se 1 (by rfl) ⟨1151039, by rfl⟩ : syracuseStep 1534719 = 2302079) B2302079
theorem B19680083 : Blo 1534464 19680083 := bstep (se 1 (by rfl) ⟨14760062, by rfl⟩ : syracuseStep 19680083 = 29520125) B29520125
theorem B1534831 : Blo 1534464 1534831 := bstep (se 1 (by rfl) ⟨1151123, by rfl⟩ : syracuseStep 1534831 = 2302247) B2302247
theorem B1535007 : Blo 1534464 1535007 := bstep (se 1 (by rfl) ⟨1151255, by rfl⟩ : syracuseStep 1535007 = 2302511) B2302511
theorem B4205723 : Blo 1534464 4205723 := bstep (se 1 (by rfl) ⟨3154292, by rfl⟩ : syracuseStep 4205723 = 6308585) B6308585
theorem B31502027 : Blo 1534464 31502027 := bstep (se 1 (by rfl) ⟨23626520, by rfl⟩ : syracuseStep 31502027 = 47253041) B47253041
theorem B22130459 : Blo 1534464 22130459 := bstep (se 1 (by rfl) ⟨16597844, by rfl⟩ : syracuseStep 22130459 = 33195689) B33195689
theorem B1535903 : Blo 1534464 1535903 := bstep (se 1 (by rfl) ⟨1151927, by rfl⟩ : syracuseStep 1535903 = 2303855) B2303855
theorem B5829479 : Blo 1534464 5829479 := bstep (se 1 (by rfl) ⟨4372109, by rfl⟩ : syracuseStep 5829479 = 8744219) B8744219
theorem B12456947 : Blo 1534464 12456947 := bstep (se 1 (by rfl) ⟨9342710, by rfl⟩ : syracuseStep 12456947 = 18685421) B18685421
theorem B15766649 : Blo 1534464 15766649 := bstep (se 2 (by rfl) ⟨5912493, by rfl⟩ : syracuseStep 15766649 = 11824987) B11824987
theorem B3454631 : Blo 1534464 3454631 := bstep (se 1 (by rfl) ⟨2590973, by rfl⟩ : syracuseStep 3454631 = 5181947) B5181947
theorem B44275679 : Blo 1534464 44275679 := bstep (se 1 (by rfl) ⟨33206759, by rfl⟩ : syracuseStep 44275679 = 66413519) B66413519
theorem B3455855 : Blo 1534464 3455855 := bstep (se 1 (by rfl) ⟨2591891, by rfl⟩ : syracuseStep 3455855 = 5183783) B5183783
theorem B14015389 : Blo 1534464 14015389 := bstep (se 3 (by rfl) ⟨2627885, by rfl⟩ : syracuseStep 14015389 = 5255771) B5255771
theorem B11215261 : Blo 1534464 11215261 := bstep (se 3 (by rfl) ⟨2102861, by rfl⟩ : syracuseStep 11215261 = 4205723) B4205723
theorem B10511099 : Blo 1534464 10511099 := bstep (se 1 (by rfl) ⟨7883324, by rfl⟩ : syracuseStep 10511099 = 15766649) B15766649
theorem B59048999 : Blo 1534464 59048999 := bstep (se 1 (by rfl) ⟨44286749, by rfl⟩ : syracuseStep 59048999 = 88573499) B88573499
theorem B2303087 : Blo 1534464 2303087 := bstep (se 1 (by rfl) ⟨1727315, by rfl⟩ : syracuseStep 2303087 = 3454631) B3454631
theorem B16598191 : Blo 1534464 16598191 := bstep (se 1 (by rfl) ⟨12448643, by rfl⟩ : syracuseStep 16598191 = 24897287) B24897287
theorem B18687185 : Blo 1534464 18687185 := bstep (se 2 (by rfl) ⟨7007694, by rfl⟩ : syracuseStep 18687185 = 14015389) B14015389
theorem B29517119 : Blo 1534464 29517119 := bstep (se 1 (by rfl) ⟨22137839, by rfl⟩ : syracuseStep 29517119 = 44275679) B44275679
theorem B2303903 : Blo 1534464 2303903 := bstep (se 1 (by rfl) ⟨1727927, by rfl⟩ : syracuseStep 2303903 = 3455855) B3455855
theorem B28010909 : Blo 1534464 28010909 := bstep (se 3 (by rfl) ⟨5252045, by rfl⟩ : syracuseStep 28010909 = 10504091) B10504091
theorem B29928275 : Blo 1534464 29928275 := bstep (se 1 (by rfl) ⟨22446206, by rfl⟩ : syracuseStep 29928275 = 44892413) B44892413
theorem B3886319 : Blo 1534464 3886319 := bstep (se 1 (by rfl) ⟨2914739, by rfl⟩ : syracuseStep 3886319 = 5829479) B5829479
theorem B3453353 : Blo 1534464 3453353 := bstep (se 2 (by rfl) ⟨1295007, by rfl⟩ : syracuseStep 3453353 = 2590015) B2590015
theorem B13120055 : Blo 1534464 13120055 := bstep (se 1 (by rfl) ⟨9840041, by rfl⟩ : syracuseStep 13120055 = 19680083) B19680083
theorem B21001351 : Blo 1534464 21001351 := bstep (se 1 (by rfl) ⟨15751013, by rfl⟩ : syracuseStep 21001351 = 31502027) B31502027
theorem B3462887 : Blo 1534464 3462887 := bstep (se 1 (by rfl) ⟨2597165, by rfl⟩ : syracuseStep 3462887 = 5194331) B5194331
theorem B4667561 : Blo 1534464 4667561 := bstep (se 2 (by rfl) ⟨1750335, by rfl⟩ : syracuseStep 4667561 = 3500671) B3500671
theorem B4987055 : Blo 1534464 4987055 := bstep (se 1 (by rfl) ⟨3740291, by rfl⟩ : syracuseStep 4987055 = 7480583) B7480583
theorem B14753639 : Blo 1534464 14753639 := bstep (se 1 (by rfl) ⟨11065229, by rfl⟩ : syracuseStep 14753639 = 22130459) B22130459
theorem B33218525 : Blo 1534464 33218525 := bstep (se 3 (by rfl) ⟨6228473, by rfl⟩ : syracuseStep 33218525 = 12456947) B12456947
theorem B2302235 : Blo 1534464 2302235 := bstep (se 1 (by rfl) ⟨1726676, by rfl⟩ : syracuseStep 2302235 = 3453353) B3453353
theorem B19678079 : Blo 1534464 19678079 := bstep (se 1 (by rfl) ⟨14758559, by rfl⟩ : syracuseStep 19678079 = 29517119) B29517119
theorem B28001801 : Blo 1534464 28001801 := bstep (se 2 (by rfl) ⟨10500675, by rfl⟩ : syracuseStep 28001801 = 21001351) B21001351
theorem B2590879 : Blo 1534464 2590879 := bstep (se 1 (by rfl) ⟨1943159, by rfl⟩ : syracuseStep 2590879 = 3886319) B3886319
theorem B22145683 : Blo 1534464 22145683 := bstep (se 1 (by rfl) ⟨16609262, by rfl⟩ : syracuseStep 22145683 = 33218525) B33218525
theorem B7007399 : Blo 1534464 7007399 := bstep (se 1 (by rfl) ⟨5255549, by rfl⟩ : syracuseStep 7007399 = 10511099) B10511099
theorem B14953681 : Blo 1534464 14953681 := bstep (se 2 (by rfl) ⟨5607630, by rfl⟩ : syracuseStep 14953681 = 11215261) B11215261
theorem B39365999 : Blo 1534464 39365999 := bstep (se 1 (by rfl) ⟨29524499, by rfl⟩ : syracuseStep 39365999 = 59048999) B59048999
theorem B1535391 : Blo 1534464 1535391 := bstep (se 1 (by rfl) ⟨1151543, by rfl⟩ : syracuseStep 1535391 = 2303087) B2303087
theorem B1535935 : Blo 1534464 1535935 := bstep (se 1 (by rfl) ⟨1151951, by rfl⟩ : syracuseStep 1535935 = 2303903) B2303903
theorem B22130921 : Blo 1534464 22130921 := bstep (se 2 (by rfl) ⟨8299095, by rfl⟩ : syracuseStep 22130921 = 16598191) B16598191
theorem B18673939 : Blo 1534464 18673939 := bstep (se 1 (by rfl) ⟨14005454, by rfl⟩ : syracuseStep 18673939 = 28010909) B28010909
theorem B19952183 : Blo 1534464 19952183 := bstep (se 1 (by rfl) ⟨14964137, by rfl⟩ : syracuseStep 19952183 = 29928275) B29928275
theorem B9835759 : Blo 1534464 9835759 := bstep (se 1 (by rfl) ⟨7376819, by rfl⟩ : syracuseStep 9835759 = 14753639) B14753639
theorem B8746703 : Blo 1534464 8746703 := bstep (se 1 (by rfl) ⟨6560027, by rfl⟩ : syracuseStep 8746703 = 13120055) B13120055
theorem B12458123 : Blo 1534464 12458123 := bstep (se 1 (by rfl) ⟨9343592, by rfl⟩ : syracuseStep 12458123 = 18687185) B18687185
theorem B2308591 : Blo 1534464 2308591 := bstep (se 1 (by rfl) ⟨1731443, by rfl⟩ : syracuseStep 2308591 = 3462887) B3462887
theorem B3111707 : Blo 1534464 3111707 := bstep (se 1 (by rfl) ⟨2333780, by rfl⟩ : syracuseStep 3111707 = 4667561) B4667561
theorem B3324703 : Blo 1534464 3324703 := bstep (se 1 (by rfl) ⟨2493527, by rfl⟩ : syracuseStep 3324703 = 4987055) B4987055
theorem B14753947 : Blo 1534464 14753947 := bstep (se 1 (by rfl) ⟨11065460, by rfl⟩ : syracuseStep 14753947 = 22130921) B22130921
theorem B4432937 : Blo 1534464 4432937 := bstep (se 2 (by rfl) ⟨1662351, by rfl⟩ : syracuseStep 4432937 = 3324703) B3324703
theorem B4671599 : Blo 1534464 4671599 := bstep (se 1 (by rfl) ⟨3503699, by rfl⟩ : syracuseStep 4671599 = 7007399) B7007399
theorem B1534823 : Blo 1534464 1534823 := bstep (se 1 (by rfl) ⟨1151117, by rfl⟩ : syracuseStep 1534823 = 2302235) B2302235
theorem B24898585 : Blo 1534464 24898585 := bstep (se 2 (by rfl) ⟨9336969, by rfl⟩ : syracuseStep 24898585 = 18673939) B18673939
theorem B13118719 : Blo 1534464 13118719 := bstep (se 1 (by rfl) ⟨9839039, by rfl⟩ : syracuseStep 13118719 = 19678079) B19678079
theorem B29527577 : Blo 1534464 29527577 := bstep (se 2 (by rfl) ⟨11072841, by rfl⟩ : syracuseStep 29527577 = 22145683) B22145683
theorem B26243999 : Blo 1534464 26243999 := bstep (se 1 (by rfl) ⟨19682999, by rfl⟩ : syracuseStep 26243999 = 39365999) B39365999
theorem B3454505 : Blo 1534464 3454505 := bstep (se 2 (by rfl) ⟨1295439, by rfl⟩ : syracuseStep 3454505 = 2590879) B2590879
theorem B13301455 : Blo 1534464 13301455 := bstep (se 1 (by rfl) ⟨9976091, by rfl⟩ : syracuseStep 13301455 = 19952183) B19952183
theorem B18667867 : Blo 1534464 18667867 := bstep (se 1 (by rfl) ⟨14000900, by rfl⟩ : syracuseStep 18667867 = 28001801) B28001801
theorem B5831135 : Blo 1534464 5831135 := bstep (se 1 (by rfl) ⟨4373351, by rfl⟩ : syracuseStep 5831135 = 8746703) B8746703
theorem B8305415 : Blo 1534464 8305415 := bstep (se 1 (by rfl) ⟨6229061, by rfl⟩ : syracuseStep 8305415 = 12458123) B12458123
theorem B19938241 : Blo 1534464 19938241 := bstep (se 2 (by rfl) ⟨7476840, by rfl⟩ : syracuseStep 19938241 = 14953681) B14953681
theorem B13114345 : Blo 1534464 13114345 := bstep (se 2 (by rfl) ⟨4917879, by rfl⟩ : syracuseStep 13114345 = 9835759) B9835759
theorem B8297885 : Blo 1534464 8297885 := bstep (se 3 (by rfl) ⟨1555853, by rfl⟩ : syracuseStep 8297885 = 3111707) B3111707
theorem B12312485 : Blo 1534464 12312485 := bstep (se 4 (by rfl) ⟨1154295, by rfl⟩ : syracuseStep 12312485 = 2308591) B2308591
theorem B47284661 : Blo 1534464 47284661 := bstep (se 5 (by rfl) ⟨2216468, by rfl⟩ : syracuseStep 47284661 = 4432937) B4432937
theorem B2303003 : Blo 1534464 2303003 := bstep (se 1 (by rfl) ⟨1727252, by rfl⟩ : syracuseStep 2303003 = 3454505) B3454505
theorem B17491625 : Blo 1534464 17491625 := bstep (se 2 (by rfl) ⟨6559359, by rfl⟩ : syracuseStep 17491625 = 13118719) B13118719
theorem B5531923 : Blo 1534464 5531923 := bstep (se 1 (by rfl) ⟨4148942, by rfl⟩ : syracuseStep 5531923 = 8297885) B8297885
theorem B19671929 : Blo 1534464 19671929 := bstep (se 2 (by rfl) ⟨7376973, by rfl⟩ : syracuseStep 19671929 = 14753947) B14753947
theorem B24890489 : Blo 1534464 24890489 := bstep (se 2 (by rfl) ⟨9333933, by rfl⟩ : syracuseStep 24890489 = 18667867) B18667867
theorem B17485793 : Blo 1534464 17485793 := bstep (se 2 (by rfl) ⟨6557172, by rfl⟩ : syracuseStep 17485793 = 13114345) B13114345
theorem B33198113 : Blo 1534464 33198113 := bstep (se 2 (by rfl) ⟨12449292, by rfl⟩ : syracuseStep 33198113 = 24898585) B24898585
theorem B3887423 : Blo 1534464 3887423 := bstep (se 1 (by rfl) ⟨2915567, by rfl⟩ : syracuseStep 3887423 = 5831135) B5831135
theorem B106337285 : Blo 1534464 106337285 := bstep (se 4 (by rfl) ⟨9969120, by rfl⟩ : syracuseStep 106337285 = 19938241) B19938241
theorem B12457597 : Blo 1534464 12457597 := bstep (se 3 (by rfl) ⟨2335799, by rfl⟩ : syracuseStep 12457597 = 4671599) B4671599
theorem B17495999 : Blo 1534464 17495999 := bstep (se 1 (by rfl) ⟨13121999, by rfl⟩ : syracuseStep 17495999 = 26243999) B26243999
theorem B5536943 : Blo 1534464 5536943 := bstep (se 1 (by rfl) ⟨4152707, by rfl⟩ : syracuseStep 5536943 = 8305415) B8305415
theorem B17735273 : Blo 1534464 17735273 := bstep (se 2 (by rfl) ⟨6650727, by rfl⟩ : syracuseStep 17735273 = 13301455) B13301455
theorem B19685051 : Blo 1534464 19685051 := bstep (se 1 (by rfl) ⟨14763788, by rfl⟩ : syracuseStep 19685051 = 29527577) B29527577
theorem B8208323 : Blo 1534464 8208323 := bstep (se 1 (by rfl) ⟨6156242, by rfl⟩ : syracuseStep 8208323 = 12312485) B12312485
theorem B31523107 : Blo 1534464 31523107 := bstep (se 1 (by rfl) ⟨23642330, by rfl⟩ : syracuseStep 31523107 = 47284661) B47284661
theorem B11823515 : Blo 1534464 11823515 := bstep (se 1 (by rfl) ⟨8867636, by rfl⟩ : syracuseStep 11823515 = 17735273) B17735273
theorem B2591615 : Blo 1534464 2591615 := bstep (se 1 (by rfl) ⟨1943711, by rfl⟩ : syracuseStep 2591615 = 3887423) B3887423
theorem B7375897 : Blo 1534464 7375897 := bstep (se 2 (by rfl) ⟨2765961, by rfl⟩ : syracuseStep 7375897 = 5531923) B5531923
theorem B1535335 : Blo 1534464 1535335 := bstep (se 1 (by rfl) ⟨1151501, by rfl⟩ : syracuseStep 1535335 = 2303003) B2303003
theorem B11661083 : Blo 1534464 11661083 := bstep (se 1 (by rfl) ⟨8745812, by rfl⟩ : syracuseStep 11661083 = 17491625) B17491625
theorem B16593659 : Blo 1534464 16593659 := bstep (se 1 (by rfl) ⟨12445244, by rfl⟩ : syracuseStep 16593659 = 24890489) B24890489
theorem B3691295 : Blo 1534464 3691295 := bstep (se 1 (by rfl) ⟨2768471, by rfl⟩ : syracuseStep 3691295 = 5536943) B5536943
theorem B16610129 : Blo 1534464 16610129 := bstep (se 2 (by rfl) ⟨6228798, by rfl⟩ : syracuseStep 16610129 = 12457597) B12457597
theorem B22132075 : Blo 1534464 22132075 := bstep (se 1 (by rfl) ⟨16599056, by rfl⟩ : syracuseStep 22132075 = 33198113) B33198113
theorem B70891523 : Blo 1534464 70891523 := bstep (se 1 (by rfl) ⟨53168642, by rfl⟩ : syracuseStep 70891523 = 106337285) B106337285
theorem B11663999 : Blo 1534464 11663999 := bstep (se 1 (by rfl) ⟨8747999, by rfl⟩ : syracuseStep 11663999 = 17495999) B17495999
theorem B13114619 : Blo 1534464 13114619 := bstep (se 1 (by rfl) ⟨9835964, by rfl⟩ : syracuseStep 13114619 = 19671929) B19671929
theorem B13123367 : Blo 1534464 13123367 := bstep (se 1 (by rfl) ⟨9842525, by rfl⟩ : syracuseStep 13123367 = 19685051) B19685051
theorem B5472215 : Blo 1534464 5472215 := bstep (se 1 (by rfl) ⟨4104161, by rfl⟩ : syracuseStep 5472215 = 8208323) B8208323
theorem B11657195 : Blo 1534464 11657195 := bstep (se 1 (by rfl) ⟨8742896, by rfl⟩ : syracuseStep 11657195 = 17485793) B17485793
theorem B47261015 : Blo 1534464 47261015 := bstep (se 1 (by rfl) ⟨35445761, by rfl⟩ : syracuseStep 47261015 = 70891523) B70891523
theorem B7882343 : Blo 1534464 7882343 := bstep (se 1 (by rfl) ⟨5911757, by rfl⟩ : syracuseStep 7882343 = 11823515) B11823515
theorem B7775999 : Blo 1534464 7775999 := bstep (se 1 (by rfl) ⟨5831999, by rfl⟩ : syracuseStep 7775999 = 11663999) B11663999
theorem B29509433 : Blo 1534464 29509433 := bstep (se 2 (by rfl) ⟨11066037, by rfl⟩ : syracuseStep 29509433 = 22132075) B22132075
theorem B8743079 : Blo 1534464 8743079 := bstep (se 1 (by rfl) ⟨6557309, by rfl⟩ : syracuseStep 8743079 = 13114619) B13114619
theorem B3648143 : Blo 1534464 3648143 := bstep (se 1 (by rfl) ⟨2736107, by rfl⟩ : syracuseStep 3648143 = 5472215) B5472215
theorem B11062439 : Blo 1534464 11062439 := bstep (se 1 (by rfl) ⟨8296829, by rfl⟩ : syracuseStep 11062439 = 16593659) B16593659
theorem B2460863 : Blo 1534464 2460863 := bstep (se 1 (by rfl) ⟨1845647, by rfl⟩ : syracuseStep 2460863 = 3691295) B3691295
theorem B9834529 : Blo 1534464 9834529 := bstep (se 2 (by rfl) ⟨3687948, by rfl⟩ : syracuseStep 9834529 = 7375897) B7375897
theorem B7771463 : Blo 1534464 7771463 := bstep (se 1 (by rfl) ⟨5828597, by rfl⟩ : syracuseStep 7771463 = 11657195) B11657195
theorem B42030809 : Blo 1534464 42030809 := bstep (se 2 (by rfl) ⟨15761553, by rfl⟩ : syracuseStep 42030809 = 31523107) B31523107
theorem B11073419 : Blo 1534464 11073419 := bstep (se 1 (by rfl) ⟨8305064, by rfl⟩ : syracuseStep 11073419 = 16610129) B16610129
theorem B1727743 : Blo 1534464 1727743 := bstep (se 1 (by rfl) ⟨1295807, by rfl⟩ : syracuseStep 1727743 = 2591615) B2591615
theorem B7774055 : Blo 1534464 7774055 := bstep (se 1 (by rfl) ⟨5830541, by rfl⟩ : syracuseStep 7774055 = 11661083) B11661083
theorem B8748911 : Blo 1534464 8748911 := bstep (se 1 (by rfl) ⟨6561683, by rfl⟩ : syracuseStep 8748911 = 13123367) B13123367
theorem B31507343 : Blo 1534464 31507343 := bstep (se 1 (by rfl) ⟨23630507, by rfl⟩ : syracuseStep 31507343 = 47261015) B47261015
theorem B7382279 : Blo 1534464 7382279 := bstep (se 1 (by rfl) ⟨5536709, by rfl⟩ : syracuseStep 7382279 = 11073419) B11073419
theorem B2303657 : Blo 1534464 2303657 := bstep (se 2 (by rfl) ⟨863871, by rfl⟩ : syracuseStep 2303657 = 1727743) B1727743
theorem B7374959 : Blo 1534464 7374959 := bstep (se 1 (by rfl) ⟨5531219, by rfl⟩ : syracuseStep 7374959 = 11062439) B11062439
theorem B1640575 : Blo 1534464 1640575 := bstep (se 1 (by rfl) ⟨1230431, by rfl⟩ : syracuseStep 1640575 = 2460863) B2460863
theorem B5180975 : Blo 1534464 5180975 := bstep (se 1 (by rfl) ⟨3885731, by rfl⟩ : syracuseStep 5180975 = 7771463) B7771463
theorem B5254895 : Blo 1534464 5254895 := bstep (se 1 (by rfl) ⟨3941171, by rfl⟩ : syracuseStep 5254895 = 7882343) B7882343
theorem B28020539 : Blo 1534464 28020539 := bstep (se 1 (by rfl) ⟨21015404, by rfl⟩ : syracuseStep 28020539 = 42030809) B42030809
theorem B19672955 : Blo 1534464 19672955 := bstep (se 1 (by rfl) ⟨14754716, by rfl⟩ : syracuseStep 19672955 = 29509433) B29509433
theorem B5828719 : Blo 1534464 5828719 := bstep (se 1 (by rfl) ⟨4371539, by rfl⟩ : syracuseStep 5828719 = 8743079) B8743079
theorem B9728381 : Blo 1534464 9728381 := bstep (se 3 (by rfl) ⟨1824071, by rfl⟩ : syracuseStep 9728381 = 3648143) B3648143
theorem B5182703 : Blo 1534464 5182703 := bstep (se 1 (by rfl) ⟨3887027, by rfl⟩ : syracuseStep 5182703 = 7774055) B7774055
theorem B13112705 : Blo 1534464 13112705 := bstep (se 2 (by rfl) ⟨4917264, by rfl⟩ : syracuseStep 13112705 = 9834529) B9834529
theorem B5183999 : Blo 1534464 5183999 := bstep (se 1 (by rfl) ⟨3887999, by rfl⟩ : syracuseStep 5183999 = 7775999) B7775999
theorem B5832607 : Blo 1534464 5832607 := bstep (se 1 (by rfl) ⟨4374455, by rfl⟩ : syracuseStep 5832607 = 8748911) B8748911
theorem B2187433 : Blo 1534464 2187433 := bstep (se 2 (by rfl) ⟨820287, by rfl⟩ : syracuseStep 2187433 = 1640575) B1640575
theorem B21004895 : Blo 1534464 21004895 := bstep (se 1 (by rfl) ⟨15753671, by rfl⟩ : syracuseStep 21004895 = 31507343) B31507343
theorem B19686077 : Blo 1534464 19686077 := bstep (se 3 (by rfl) ⟨3691139, by rfl⟩ : syracuseStep 19686077 = 7382279) B7382279
theorem B8741803 : Blo 1534464 8741803 := bstep (se 1 (by rfl) ⟨6556352, by rfl⟩ : syracuseStep 8741803 = 13112705) B13112705
theorem B4916639 : Blo 1534464 4916639 := bstep (se 1 (by rfl) ⟨3687479, by rfl⟩ : syracuseStep 4916639 = 7374959) B7374959
theorem B74721437 : Blo 1534464 74721437 := bstep (se 3 (by rfl) ⟨14010269, by rfl⟩ : syracuseStep 74721437 = 28020539) B28020539
theorem B7776809 : Blo 1534464 7776809 := bstep (se 2 (by rfl) ⟨2916303, by rfl⟩ : syracuseStep 7776809 = 5832607) B5832607
theorem B1535771 : Blo 1534464 1535771 := bstep (se 1 (by rfl) ⟨1151828, by rfl⟩ : syracuseStep 1535771 = 2303657) B2303657
theorem B3453983 : Blo 1534464 3453983 := bstep (se 1 (by rfl) ⟨2590487, by rfl⟩ : syracuseStep 3453983 = 5180975) B5180975
theorem B3503263 : Blo 1534464 3503263 := bstep (se 1 (by rfl) ⟨2627447, by rfl⟩ : syracuseStep 3503263 = 5254895) B5254895
theorem B7771625 : Blo 1534464 7771625 := bstep (se 2 (by rfl) ⟨2914359, by rfl⟩ : syracuseStep 7771625 = 5828719) B5828719
theorem B3455135 : Blo 1534464 3455135 := bstep (se 1 (by rfl) ⟨2591351, by rfl⟩ : syracuseStep 3455135 = 5182703) B5182703
theorem B25942349 : Blo 1534464 25942349 := bstep (se 3 (by rfl) ⟨4864190, by rfl⟩ : syracuseStep 25942349 = 9728381) B9728381
theorem B3455999 : Blo 1534464 3455999 := bstep (se 1 (by rfl) ⟨2591999, by rfl⟩ : syracuseStep 3455999 = 5183999) B5183999
theorem B13115303 : Blo 1534464 13115303 := bstep (se 1 (by rfl) ⟨9836477, by rfl⟩ : syracuseStep 13115303 = 19672955) B19672955
theorem B2916577 : Blo 1534464 2916577 := bstep (se 2 (by rfl) ⟨1093716, by rfl⟩ : syracuseStep 2916577 = 2187433) B2187433
theorem B13124051 : Blo 1534464 13124051 := bstep (se 1 (by rfl) ⟨9843038, by rfl⟩ : syracuseStep 13124051 = 19686077) B19686077
theorem B2302655 : Blo 1534464 2302655 := bstep (se 1 (by rfl) ⟨1726991, by rfl⟩ : syracuseStep 2302655 = 3453983) B3453983
theorem B3277759 : Blo 1534464 3277759 := bstep (se 1 (by rfl) ⟨2458319, by rfl⟩ : syracuseStep 3277759 = 4916639) B4916639
theorem B2303423 : Blo 1534464 2303423 := bstep (se 1 (by rfl) ⟨1727567, by rfl⟩ : syracuseStep 2303423 = 3455135) B3455135
theorem B4671017 : Blo 1534464 4671017 := bstep (se 2 (by rfl) ⟨1751631, by rfl⟩ : syracuseStep 4671017 = 3503263) B3503263
theorem B17294899 : Blo 1534464 17294899 := bstep (se 1 (by rfl) ⟨12971174, by rfl⟩ : syracuseStep 17294899 = 25942349) B25942349
theorem B2303999 : Blo 1534464 2303999 := bstep (se 1 (by rfl) ⟨1727999, by rfl⟩ : syracuseStep 2303999 = 3455999) B3455999
theorem B8743535 : Blo 1534464 8743535 := bstep (se 1 (by rfl) ⟨6557651, by rfl⟩ : syracuseStep 8743535 = 13115303) B13115303
theorem B14003263 : Blo 1534464 14003263 := bstep (se 1 (by rfl) ⟨10502447, by rfl⟩ : syracuseStep 14003263 = 21004895) B21004895
theorem B5181083 : Blo 1534464 5181083 := bstep (se 1 (by rfl) ⟨3885812, by rfl⟩ : syracuseStep 5181083 = 7771625) B7771625
theorem B11655737 : Blo 1534464 11655737 := bstep (se 2 (by rfl) ⟨4370901, by rfl⟩ : syracuseStep 11655737 = 8741803) B8741803
theorem B49814291 : Blo 1534464 49814291 := bstep (se 1 (by rfl) ⟨37360718, by rfl⟩ : syracuseStep 49814291 = 74721437) B74721437
theorem B5184539 : Blo 1534464 5184539 := bstep (se 1 (by rfl) ⟨3888404, by rfl⟩ : syracuseStep 5184539 = 7776809) B7776809
theorem B8749367 : Blo 1534464 8749367 := bstep (se 1 (by rfl) ⟨6562025, by rfl⟩ : syracuseStep 8749367 = 13124051) B13124051
theorem B3114011 : Blo 1534464 3114011 := bstep (se 1 (by rfl) ⟨2335508, by rfl⟩ : syracuseStep 3114011 = 4671017) B4671017
theorem B1535103 : Blo 1534464 1535103 := bstep (se 1 (by rfl) ⟨1151327, by rfl⟩ : syracuseStep 1535103 = 2302655) B2302655
theorem B1535615 : Blo 1534464 1535615 := bstep (se 1 (by rfl) ⟨1151711, by rfl⟩ : syracuseStep 1535615 = 2303423) B2303423
theorem B4370345 : Blo 1534464 4370345 := bstep (se 2 (by rfl) ⟨1638879, by rfl⟩ : syracuseStep 4370345 = 3277759) B3277759
theorem B1535999 : Blo 1534464 1535999 := bstep (se 1 (by rfl) ⟨1151999, by rfl⟩ : syracuseStep 1535999 = 2303999) B2303999
theorem B7770491 : Blo 1534464 7770491 := bstep (se 1 (by rfl) ⟨5827868, by rfl⟩ : syracuseStep 7770491 = 11655737) B11655737
theorem B5829023 : Blo 1534464 5829023 := bstep (se 1 (by rfl) ⟨4371767, by rfl⟩ : syracuseStep 5829023 = 8743535) B8743535
theorem B3454055 : Blo 1534464 3454055 := bstep (se 1 (by rfl) ⟨2590541, by rfl⟩ : syracuseStep 3454055 = 5181083) B5181083
theorem B3888769 : Blo 1534464 3888769 := bstep (se 2 (by rfl) ⟨1458288, by rfl⟩ : syracuseStep 3888769 = 2916577) B2916577
theorem B74684069 : Blo 1534464 74684069 := bstep (se 4 (by rfl) ⟨7001631, by rfl⟩ : syracuseStep 74684069 = 14003263) B14003263
theorem B33209527 : Blo 1534464 33209527 := bstep (se 1 (by rfl) ⟨24907145, by rfl⟩ : syracuseStep 33209527 = 49814291) B49814291
theorem B3456359 : Blo 1534464 3456359 := bstep (se 1 (by rfl) ⟨2592269, by rfl⟩ : syracuseStep 3456359 = 5184539) B5184539
theorem B23059865 : Blo 1534464 23059865 := bstep (se 2 (by rfl) ⟨8647449, by rfl⟩ : syracuseStep 23059865 = 17294899) B17294899
theorem B5832911 : Blo 1534464 5832911 := bstep (se 1 (by rfl) ⟨4374683, by rfl⟩ : syracuseStep 5832911 = 8749367) B8749367
theorem B2302703 : Blo 1534464 2302703 := bstep (se 1 (by rfl) ⟨1727027, by rfl⟩ : syracuseStep 2302703 = 3454055) B3454055
theorem B44279369 : Blo 1534464 44279369 := bstep (se 2 (by rfl) ⟨16604763, by rfl⟩ : syracuseStep 44279369 = 33209527) B33209527
theorem B2304239 : Blo 1534464 2304239 := bstep (se 1 (by rfl) ⟨1728179, by rfl⟩ : syracuseStep 2304239 = 3456359) B3456359
theorem B5180327 : Blo 1534464 5180327 := bstep (se 1 (by rfl) ⟨3885245, by rfl⟩ : syracuseStep 5180327 = 7770491) B7770491
theorem B3886015 : Blo 1534464 3886015 := bstep (se 1 (by rfl) ⟨2914511, by rfl⟩ : syracuseStep 3886015 = 5829023) B5829023
theorem B15373243 : Blo 1534464 15373243 := bstep (se 1 (by rfl) ⟨11529932, by rfl⟩ : syracuseStep 15373243 = 23059865) B23059865
theorem B2913563 : Blo 1534464 2913563 := bstep (se 1 (by rfl) ⟨2185172, by rfl⟩ : syracuseStep 2913563 = 4370345) B4370345
theorem B8304029 : Blo 1534464 8304029 := bstep (se 3 (by rfl) ⟨1557005, by rfl⟩ : syracuseStep 8304029 = 3114011) B3114011
theorem B49789379 : Blo 1534464 49789379 := bstep (se 1 (by rfl) ⟨37342034, by rfl⟩ : syracuseStep 49789379 = 74684069) B74684069
theorem B5185025 : Blo 1534464 5185025 := bstep (se 2 (by rfl) ⟨1944384, by rfl⟩ : syracuseStep 5185025 = 3888769) B3888769
theorem B1942375 : Blo 1534464 1942375 := bstep (se 1 (by rfl) ⟨1456781, by rfl⟩ : syracuseStep 1942375 = 2913563) B2913563
theorem B20497657 : Blo 1534464 20497657 := bstep (se 2 (by rfl) ⟨7686621, by rfl⟩ : syracuseStep 20497657 = 15373243) B15373243
theorem B1535135 : Blo 1534464 1535135 := bstep (se 1 (by rfl) ⟨1151351, by rfl⟩ : syracuseStep 1535135 = 2302703) B2302703
theorem B29519579 : Blo 1534464 29519579 := bstep (se 1 (by rfl) ⟨22139684, by rfl⟩ : syracuseStep 29519579 = 44279369) B44279369
theorem B5181353 : Blo 1534464 5181353 := bstep (se 2 (by rfl) ⟨1943007, by rfl⟩ : syracuseStep 5181353 = 3886015) B3886015
theorem B1536159 : Blo 1534464 1536159 := bstep (se 1 (by rfl) ⟨1152119, by rfl⟩ : syracuseStep 1536159 = 2304239) B2304239
theorem B3453551 : Blo 1534464 3453551 := bstep (se 1 (by rfl) ⟨2590163, by rfl⟩ : syracuseStep 3453551 = 5180327) B5180327
theorem B3888607 : Blo 1534464 3888607 := bstep (se 1 (by rfl) ⟨2916455, by rfl⟩ : syracuseStep 3888607 = 5832911) B5832911
theorem B5536019 : Blo 1534464 5536019 := bstep (se 1 (by rfl) ⟨4152014, by rfl⟩ : syracuseStep 5536019 = 8304029) B8304029
theorem B33192919 : Blo 1534464 33192919 := bstep (se 1 (by rfl) ⟨24894689, by rfl⟩ : syracuseStep 33192919 = 49789379) B49789379
theorem B3456683 : Blo 1534464 3456683 := bstep (se 1 (by rfl) ⟨2592512, by rfl⟩ : syracuseStep 3456683 = 5185025) B5185025
theorem B2302367 : Blo 1534464 2302367 := bstep (se 1 (by rfl) ⟨1726775, by rfl⟩ : syracuseStep 2302367 = 3453551) B3453551
theorem B2589833 : Blo 1534464 2589833 := bstep (se 2 (by rfl) ⟨971187, by rfl⟩ : syracuseStep 2589833 = 1942375) B1942375
theorem B27330209 : Blo 1534464 27330209 := bstep (se 2 (by rfl) ⟨10248828, by rfl⟩ : syracuseStep 27330209 = 20497657) B20497657
theorem B2304455 : Blo 1534464 2304455 := bstep (se 1 (by rfl) ⟨1728341, by rfl⟩ : syracuseStep 2304455 = 3456683) B3456683
theorem B19679719 : Blo 1534464 19679719 := bstep (se 1 (by rfl) ⟨14759789, by rfl⟩ : syracuseStep 19679719 = 29519579) B29519579
theorem B44257225 : Blo 1534464 44257225 := bstep (se 2 (by rfl) ⟨16596459, by rfl⟩ : syracuseStep 44257225 = 33192919) B33192919
theorem B3690679 : Blo 1534464 3690679 := bstep (se 1 (by rfl) ⟨2768009, by rfl⟩ : syracuseStep 3690679 = 5536019) B5536019
theorem B3454235 : Blo 1534464 3454235 := bstep (se 1 (by rfl) ⟨2590676, by rfl⟩ : syracuseStep 3454235 = 5181353) B5181353
theorem B5184809 : Blo 1534464 5184809 := bstep (se 2 (by rfl) ⟨1944303, by rfl⟩ : syracuseStep 5184809 = 3888607) B3888607
theorem B26239625 : Blo 1534464 26239625 := bstep (se 2 (by rfl) ⟨9839859, by rfl⟩ : syracuseStep 26239625 = 19679719) B19679719
theorem B2302823 : Blo 1534464 2302823 := bstep (se 1 (by rfl) ⟨1727117, by rfl⟩ : syracuseStep 2302823 = 3454235) B3454235
theorem B18220139 : Blo 1534464 18220139 := bstep (se 1 (by rfl) ⟨13665104, by rfl⟩ : syracuseStep 18220139 = 27330209) B27330209
theorem B59009633 : Blo 1534464 59009633 := bstep (se 2 (by rfl) ⟨22128612, by rfl⟩ : syracuseStep 59009633 = 44257225) B44257225
theorem B1534911 : Blo 1534464 1534911 := bstep (se 1 (by rfl) ⟨1151183, by rfl⟩ : syracuseStep 1534911 = 2302367) B2302367
theorem B1536303 : Blo 1534464 1536303 := bstep (se 1 (by rfl) ⟨1152227, by rfl⟩ : syracuseStep 1536303 = 2304455) B2304455
theorem B4920905 : Blo 1534464 4920905 := bstep (se 2 (by rfl) ⟨1845339, by rfl⟩ : syracuseStep 4920905 = 3690679) B3690679
theorem B1726555 : Blo 1534464 1726555 := bstep (se 1 (by rfl) ⟨1294916, by rfl⟩ : syracuseStep 1726555 = 2589833) B2589833
theorem B3456539 : Blo 1534464 3456539 := bstep (se 1 (by rfl) ⟨2592404, by rfl⟩ : syracuseStep 3456539 = 5184809) B5184809
theorem B2302073 : Blo 1534464 2302073 := bstep (se 2 (by rfl) ⟨863277, by rfl⟩ : syracuseStep 2302073 = 1726555) B1726555
theorem B39339755 : Blo 1534464 39339755 := bstep (se 1 (by rfl) ⟨29504816, by rfl⟩ : syracuseStep 39339755 = 59009633) B59009633
theorem B2304359 : Blo 1534464 2304359 := bstep (se 1 (by rfl) ⟨1728269, by rfl⟩ : syracuseStep 2304359 = 3456539) B3456539
theorem B17493083 : Blo 1534464 17493083 := bstep (se 1 (by rfl) ⟨13119812, by rfl⟩ : syracuseStep 17493083 = 26239625) B26239625
theorem B1535215 : Blo 1534464 1535215 := bstep (se 1 (by rfl) ⟨1151411, by rfl⟩ : syracuseStep 1535215 = 2302823) B2302823
theorem B3280603 : Blo 1534464 3280603 := bstep (se 1 (by rfl) ⟨2460452, by rfl⟩ : syracuseStep 3280603 = 4920905) B4920905
theorem B12146759 : Blo 1534464 12146759 := bstep (se 1 (by rfl) ⟨9110069, by rfl⟩ : syracuseStep 12146759 = 18220139) B18220139
theorem B1534715 : Blo 1534464 1534715 := bstep (se 1 (by rfl) ⟨1151036, by rfl⟩ : syracuseStep 1534715 = 2302073) B2302073
theorem B26226503 : Blo 1534464 26226503 := bstep (se 1 (by rfl) ⟨19669877, by rfl⟩ : syracuseStep 26226503 = 39339755) B39339755
theorem B8097839 : Blo 1534464 8097839 := bstep (se 1 (by rfl) ⟨6073379, by rfl⟩ : syracuseStep 8097839 = 12146759) B12146759
theorem B1536239 : Blo 1534464 1536239 := bstep (se 1 (by rfl) ⟨1152179, by rfl⟩ : syracuseStep 1536239 = 2304359) B2304359
theorem B11662055 : Blo 1534464 11662055 := bstep (se 1 (by rfl) ⟨8746541, by rfl⟩ : syracuseStep 11662055 = 17493083) B17493083
theorem B4374137 : Blo 1534464 4374137 := bstep (se 2 (by rfl) ⟨1640301, by rfl⟩ : syracuseStep 4374137 = 3280603) B3280603
theorem B5398559 : Blo 1534464 5398559 := bstep (se 1 (by rfl) ⟨4048919, by rfl⟩ : syracuseStep 5398559 = 8097839) B8097839
theorem B7774703 : Blo 1534464 7774703 := bstep (se 1 (by rfl) ⟨5831027, by rfl⟩ : syracuseStep 7774703 = 11662055) B11662055
theorem B17484335 : Blo 1534464 17484335 := bstep (se 1 (by rfl) ⟨13113251, by rfl⟩ : syracuseStep 17484335 = 26226503) B26226503
theorem B2916091 : Blo 1534464 2916091 := bstep (se 1 (by rfl) ⟨2187068, by rfl⟩ : syracuseStep 2916091 = 4374137) B4374137
theorem B3599039 : Blo 1534464 3599039 := bstep (se 1 (by rfl) ⟨2699279, by rfl⟩ : syracuseStep 3599039 = 5398559) B5398559
theorem B3888121 : Blo 1534464 3888121 := bstep (se 2 (by rfl) ⟨1458045, by rfl⟩ : syracuseStep 3888121 = 2916091) B2916091
theorem B5183135 : Blo 1534464 5183135 := bstep (se 1 (by rfl) ⟨3887351, by rfl⟩ : syracuseStep 5183135 = 7774703) B7774703
theorem B11656223 : Blo 1534464 11656223 := bstep (se 1 (by rfl) ⟨8742167, by rfl⟩ : syracuseStep 11656223 = 17484335) B17484335
theorem B9597437 : Blo 1534464 9597437 := bstep (se 3 (by rfl) ⟨1799519, by rfl⟩ : syracuseStep 9597437 = 3599039) B3599039
theorem B7770815 : Blo 1534464 7770815 := bstep (se 1 (by rfl) ⟨5828111, by rfl⟩ : syracuseStep 7770815 = 11656223) B11656223
theorem B3455423 : Blo 1534464 3455423 := bstep (se 1 (by rfl) ⟨2591567, by rfl⟩ : syracuseStep 3455423 = 5183135) B5183135
theorem B5184161 : Blo 1534464 5184161 := bstep (se 2 (by rfl) ⟨1944060, by rfl⟩ : syracuseStep 5184161 = 3888121) B3888121
theorem B6398291 : Blo 1534464 6398291 := bstep (se 1 (by rfl) ⟨4798718, by rfl⟩ : syracuseStep 6398291 = 9597437) B9597437
theorem B2303615 : Blo 1534464 2303615 := bstep (se 1 (by rfl) ⟨1727711, by rfl⟩ : syracuseStep 2303615 = 3455423) B3455423
theorem B5180543 : Blo 1534464 5180543 := bstep (se 1 (by rfl) ⟨3885407, by rfl⟩ : syracuseStep 5180543 = 7770815) B7770815
theorem B3456107 : Blo 1534464 3456107 := bstep (se 1 (by rfl) ⟨2592080, by rfl⟩ : syracuseStep 3456107 = 5184161) B5184161
theorem B2304071 : Blo 1534464 2304071 := bstep (se 1 (by rfl) ⟨1728053, by rfl⟩ : syracuseStep 2304071 = 3456107) B3456107
theorem B1535743 : Blo 1534464 1535743 := bstep (se 1 (by rfl) ⟨1151807, by rfl⟩ : syracuseStep 1535743 = 2303615) B2303615
theorem B3453695 : Blo 1534464 3453695 := bstep (se 1 (by rfl) ⟨2590271, by rfl⟩ : syracuseStep 3453695 = 5180543) B5180543
theorem B17062109 : Blo 1534464 17062109 := bstep (se 3 (by rfl) ⟨3199145, by rfl⟩ : syracuseStep 17062109 = 6398291) B6398291
theorem B2302463 : Blo 1534464 2302463 := bstep (se 1 (by rfl) ⟨1726847, by rfl⟩ : syracuseStep 2302463 = 3453695) B3453695
theorem B1536047 : Blo 1534464 1536047 := bstep (se 1 (by rfl) ⟨1152035, by rfl⟩ : syracuseStep 1536047 = 2304071) B2304071
theorem B11374739 : Blo 1534464 11374739 := bstep (se 1 (by rfl) ⟨8531054, by rfl⟩ : syracuseStep 11374739 = 17062109) B17062109
theorem B1534975 : Blo 1534464 1534975 := bstep (se 1 (by rfl) ⟨1151231, by rfl⟩ : syracuseStep 1534975 = 2302463) B2302463
theorem B7583159 : Blo 1534464 7583159 := bstep (se 1 (by rfl) ⟨5687369, by rfl⟩ : syracuseStep 7583159 = 11374739) B11374739
theorem B5055439 : Blo 1534464 5055439 := bstep (se 1 (by rfl) ⟨3791579, by rfl⟩ : syracuseStep 5055439 = 7583159) B7583159
theorem B6740585 : Blo 1534464 6740585 := bstep (se 2 (by rfl) ⟨2527719, by rfl⟩ : syracuseStep 6740585 = 5055439) B5055439
theorem B4493723 : Blo 1534464 4493723 := bstep (se 1 (by rfl) ⟨3370292, by rfl⟩ : syracuseStep 4493723 = 6740585) B6740585
theorem B11983261 : Blo 1534464 11983261 := bstep (se 3 (by rfl) ⟨2246861, by rfl⟩ : syracuseStep 11983261 = 4493723) B4493723
theorem B15977681 : Blo 1534464 15977681 := bstep (se 2 (by rfl) ⟨5991630, by rfl⟩ : syracuseStep 15977681 = 11983261) B11983261
theorem B10651787 : Blo 1534464 10651787 := bstep (se 1 (by rfl) ⟨7988840, by rfl⟩ : syracuseStep 10651787 = 15977681) B15977681
theorem B7101191 : Blo 1534464 7101191 := bstep (se 1 (by rfl) ⟨5325893, by rfl⟩ : syracuseStep 7101191 = 10651787) B10651787
theorem B4734127 : Blo 1534464 4734127 := bstep (se 1 (by rfl) ⟨3550595, by rfl⟩ : syracuseStep 4734127 = 7101191) B7101191
theorem B6312169 : Blo 1534464 6312169 := bstep (se 2 (by rfl) ⟨2367063, by rfl⟩ : syracuseStep 6312169 = 4734127) B4734127
theorem B33664901 : Blo 1534464 33664901 := bstep (se 4 (by rfl) ⟨3156084, by rfl⟩ : syracuseStep 33664901 = 6312169) B6312169
theorem B359092277 : Blo 1534464 359092277 := bstep (se 5 (by rfl) ⟨16832450, by rfl⟩ : syracuseStep 359092277 = 33664901) B33664901
theorem B239394851 : Blo 1534464 239394851 := bstep (se 1 (by rfl) ⟨179546138, by rfl⟩ : syracuseStep 239394851 = 359092277) B359092277
theorem B159596567 : Blo 1534464 159596567 := bstep (se 1 (by rfl) ⟨119697425, by rfl⟩ : syracuseStep 159596567 = 239394851) B239394851
theorem B106397711 : Blo 1534464 106397711 := bstep (se 1 (by rfl) ⟨79798283, by rfl⟩ : syracuseStep 106397711 = 159596567) B159596567
theorem B70931807 : Blo 1534464 70931807 := bstep (se 1 (by rfl) ⟨53198855, by rfl⟩ : syracuseStep 70931807 = 106397711) B106397711
theorem B47287871 : Blo 1534464 47287871 := bstep (se 1 (by rfl) ⟨35465903, by rfl⟩ : syracuseStep 47287871 = 70931807) B70931807
theorem B31525247 : Blo 1534464 31525247 := bstep (se 1 (by rfl) ⟨23643935, by rfl⟩ : syracuseStep 31525247 = 47287871) B47287871
theorem B21016831 : Blo 1534464 21016831 := bstep (se 1 (by rfl) ⟨15762623, by rfl⟩ : syracuseStep 21016831 = 31525247) B31525247
theorem B28022441 : Blo 1534464 28022441 := bstep (se 2 (by rfl) ⟨10508415, by rfl⟩ : syracuseStep 28022441 = 21016831) B21016831
theorem B74726509 : Blo 1534464 74726509 := bstep (se 3 (by rfl) ⟨14011220, by rfl⟩ : syracuseStep 74726509 = 28022441) B28022441
theorem B99635345 : Blo 1534464 99635345 := bstep (se 2 (by rfl) ⟨37363254, by rfl⟩ : syracuseStep 99635345 = 74726509) B74726509
theorem B66423563 : Blo 1534464 66423563 := bstep (se 1 (by rfl) ⟨49817672, by rfl⟩ : syracuseStep 66423563 = 99635345) B99635345
theorem B44282375 : Blo 1534464 44282375 := bstep (se 1 (by rfl) ⟨33211781, by rfl⟩ : syracuseStep 44282375 = 66423563) B66423563
theorem B29521583 : Blo 1534464 29521583 := bstep (se 1 (by rfl) ⟨22141187, by rfl⟩ : syracuseStep 29521583 = 44282375) B44282375
theorem B19681055 : Blo 1534464 19681055 := bstep (se 1 (by rfl) ⟨14760791, by rfl⟩ : syracuseStep 19681055 = 29521583) B29521583
theorem B13120703 : Blo 1534464 13120703 := bstep (se 1 (by rfl) ⟨9840527, by rfl⟩ : syracuseStep 13120703 = 19681055) B19681055
theorem B8747135 : Blo 1534464 8747135 := bstep (se 1 (by rfl) ⟨6560351, by rfl⟩ : syracuseStep 8747135 = 13120703) B13120703
theorem B5831423 : Blo 1534464 5831423 := bstep (se 1 (by rfl) ⟨4373567, by rfl⟩ : syracuseStep 5831423 = 8747135) B8747135
theorem B3887615 : Blo 1534464 3887615 := bstep (se 1 (by rfl) ⟨2915711, by rfl⟩ : syracuseStep 3887615 = 5831423) B5831423
theorem B2591743 : Blo 1534464 2591743 := bstep (se 1 (by rfl) ⟨1943807, by rfl⟩ : syracuseStep 2591743 = 3887615) B3887615
theorem B3455657 : Blo 1534464 3455657 := bstep (se 2 (by rfl) ⟨1295871, by rfl⟩ : syracuseStep 3455657 = 2591743) B2591743
theorem B2303771 : Blo 1534464 2303771 := bstep (se 1 (by rfl) ⟨1727828, by rfl⟩ : syracuseStep 2303771 = 3455657) B3455657
theorem B1535847 : Blo 1534464 1535847 := bstep (se 1 (by rfl) ⟨1151885, by rfl⟩ : syracuseStep 1535847 = 2303771) B2303771

theorem C0 (j : ℕ) (h1 : 383616 ≤ j) (h2 : j ≤ 384115) : Blo 1534464 (4 * j + 3) := by
  interval_cases j
  · exact B1534467
  · exact B1534471
  · exact B1534475
  · exact B1534479
  · exact B1534483
  · exact B1534487
  · exact B1534491
  · exact B1534495
  · exact B1534499
  · exact B1534503
  · exact B1534507
  · exact B1534511
  · exact B1534515
  · exact B1534519
  · exact B1534523
  · exact B1534527
  · exact B1534531
  · exact B1534535
  · exact B1534539
  · exact B1534543
  · exact B1534547
  · exact B1534551
  · exact B1534555
  · exact B1534559
  · exact B1534563
  · exact B1534567
  · exact B1534571
  · exact B1534575
  · exact B1534579
  · exact B1534583
  · exact B1534587
  · exact B1534591
  · exact B1534595
  · exact B1534599
  · exact B1534603
  · exact B1534607
  · exact B1534611
  · exact B1534615
  · exact B1534619
  · exact B1534623
  · exact B1534627
  · exact B1534631
  · exact B1534635
  · exact B1534639
  · exact B1534643
  · exact B1534647
  · exact B1534651
  · exact B1534655
  · exact B1534659
  · exact B1534663
  · exact B1534667
  · exact B1534671
  · exact B1534675
  · exact B1534679
  · exact B1534683
  · exact B1534687
  · exact B1534691
  · exact B1534695
  · exact B1534699
  · exact B1534703
  · exact B1534707
  · exact B1534711
  · exact B1534715
  · exact B1534719
  · exact B1534723
  · exact B1534727
  · exact B1534731
  · exact B1534735
  · exact B1534739
  · exact B1534743
  · exact B1534747
  · exact B1534751
  · exact B1534755
  · exact B1534759
  · exact B1534763
  · exact B1534767
  · exact B1534771
  · exact B1534775
  · exact B1534779
  · exact B1534783
  · exact B1534787
  · exact B1534791
  · exact B1534795
  · exact B1534799
  · exact B1534803
  · exact B1534807
  · exact B1534811
  · exact B1534815
  · exact B1534819
  · exact B1534823
  · exact B1534827
  · exact B1534831
  · exact B1534835
  · exact B1534839
  · exact B1534843
  · exact B1534847
  · exact B1534851
  · exact B1534855
  · exact B1534859
  · exact B1534863
  · exact B1534867
  · exact B1534871
  · exact B1534875
  · exact B1534879
  · exact B1534883
  · exact B1534887
  · exact B1534891
  · exact B1534895
  · exact B1534899
  · exact B1534903
  · exact B1534907
  · exact B1534911
  · exact B1534915
  · exact B1534919
  · exact B1534923
  · exact B1534927
  · exact B1534931
  · exact B1534935
  · exact B1534939
  · exact B1534943
  · exact B1534947
  · exact B1534951
  · exact B1534955
  · exact B1534959
  · exact B1534963
  · exact B1534967
  · exact B1534971
  · exact B1534975
  · exact B1534979
  · exact B1534983
  · exact B1534987
  · exact B1534991
  · exact B1534995
  · exact B1534999
  · exact B1535003
  · exact B1535007
  · exact B1535011
  · exact B1535015
  · exact B1535019
  · exact B1535023
  · exact B1535027
  · exact B1535031
  · exact B1535035
  · exact B1535039
  · exact B1535043
  · exact B1535047
  · exact B1535051
  · exact B1535055
  · exact B1535059
  · exact B1535063
  · exact B1535067
  · exact B1535071
  · exact B1535075
  · exact B1535079
  · exact B1535083
  · exact B1535087
  · exact B1535091
  · exact B1535095
  · exact B1535099
  · exact B1535103
  · exact B1535107
  · exact B1535111
  · exact B1535115
  · exact B1535119
  · exact B1535123
  · exact B1535127
  · exact B1535131
  · exact B1535135
  · exact B1535139
  · exact B1535143
  · exact B1535147
  · exact B1535151
  · exact B1535155
  · exact B1535159
  · exact B1535163
  · exact B1535167
  · exact B1535171
  · exact B1535175
  · exact B1535179
  · exact B1535183
  · exact B1535187
  · exact B1535191
  · exact B1535195
  · exact B1535199
  · exact B1535203
  · exact B1535207
  · exact B1535211
  · exact B1535215
  · exact B1535219
  · exact B1535223
  · exact B1535227
  · exact B1535231
  · exact B1535235
  · exact B1535239
  · exact B1535243
  · exact B1535247
  · exact B1535251
  · exact B1535255
  · exact B1535259
  · exact B1535263
  · exact B1535267
  · exact B1535271
  · exact B1535275
  · exact B1535279
  · exact B1535283
  · exact B1535287
  · exact B1535291
  · exact B1535295
  · exact B1535299
  · exact B1535303
  · exact B1535307
  · exact B1535311
  · exact B1535315
  · exact B1535319
  · exact B1535323
  · exact B1535327
  · exact B1535331
  · exact B1535335
  · exact B1535339
  · exact B1535343
  · exact B1535347
  · exact B1535351
  · exact B1535355
  · exact B1535359
  · exact B1535363
  · exact B1535367
  · exact B1535371
  · exact B1535375
  · exact B1535379
  · exact B1535383
  · exact B1535387
  · exact B1535391
  · exact B1535395
  · exact B1535399
  · exact B1535403
  · exact B1535407
  · exact B1535411
  · exact B1535415
  · exact B1535419
  · exact B1535423
  · exact B1535427
  · exact B1535431
  · exact B1535435
  · exact B1535439
  · exact B1535443
  · exact B1535447
  · exact B1535451
  · exact B1535455
  · exact B1535459
  · exact B1535463
  · exact B1535467
  · exact B1535471
  · exact B1535475
  · exact B1535479
  · exact B1535483
  · exact B1535487
  · exact B1535491
  · exact B1535495
  · exact B1535499
  · exact B1535503
  · exact B1535507
  · exact B1535511
  · exact B1535515
  · exact B1535519
  · exact B1535523
  · exact B1535527
  · exact B1535531
  · exact B1535535
  · exact B1535539
  · exact B1535543
  · exact B1535547
  · exact B1535551
  · exact B1535555
  · exact B1535559
  · exact B1535563
  · exact B1535567
  · exact B1535571
  · exact B1535575
  · exact B1535579
  · exact B1535583
  · exact B1535587
  · exact B1535591
  · exact B1535595
  · exact B1535599
  · exact B1535603
  · exact B1535607
  · exact B1535611
  · exact B1535615
  · exact B1535619
  · exact B1535623
  · exact B1535627
  · exact B1535631
  · exact B1535635
  · exact B1535639
  · exact B1535643
  · exact B1535647
  · exact B1535651
  · exact B1535655
  · exact B1535659
  · exact B1535663
  · exact B1535667
  · exact B1535671
  · exact B1535675
  · exact B1535679
  · exact B1535683
  · exact B1535687
  · exact B1535691
  · exact B1535695
  · exact B1535699
  · exact B1535703
  · exact B1535707
  · exact B1535711
  · exact B1535715
  · exact B1535719
  · exact B1535723
  · exact B1535727
  · exact B1535731
  · exact B1535735
  · exact B1535739
  · exact B1535743
  · exact B1535747
  · exact B1535751
  · exact B1535755
  · exact B1535759
  · exact B1535763
  · exact B1535767
  · exact B1535771
  · exact B1535775
  · exact B1535779
  · exact B1535783
  · exact B1535787
  · exact B1535791
  · exact B1535795
  · exact B1535799
  · exact B1535803
  · exact B1535807
  · exact B1535811
  · exact B1535815
  · exact B1535819
  · exact B1535823
  · exact B1535827
  · exact B1535831
  · exact B1535835
  · exact B1535839
  · exact B1535843
  · exact B1535847
  · exact B1535851
  · exact B1535855
  · exact B1535859
  · exact B1535863
  · exact B1535867
  · exact B1535871
  · exact B1535875
  · exact B1535879
  · exact B1535883
  · exact B1535887
  · exact B1535891
  · exact B1535895
  · exact B1535899
  · exact B1535903
  · exact B1535907
  · exact B1535911
  · exact B1535915
  · exact B1535919
  · exact B1535923
  · exact B1535927
  · exact B1535931
  · exact B1535935
  · exact B1535939
  · exact B1535943
  · exact B1535947
  · exact B1535951
  · exact B1535955
  · exact B1535959
  · exact B1535963
  · exact B1535967
  · exact B1535971
  · exact B1535975
  · exact B1535979
  · exact B1535983
  · exact B1535987
  · exact B1535991
  · exact B1535995
  · exact B1535999
  · exact B1536003
  · exact B1536007
  · exact B1536011
  · exact B1536015
  · exact B1536019
  · exact B1536023
  · exact B1536027
  · exact B1536031
  · exact B1536035
  · exact B1536039
  · exact B1536043
  · exact B1536047
  · exact B1536051
  · exact B1536055
  · exact B1536059
  · exact B1536063
  · exact B1536067
  · exact B1536071
  · exact B1536075
  · exact B1536079
  · exact B1536083
  · exact B1536087
  · exact B1536091
  · exact B1536095
  · exact B1536099
  · exact B1536103
  · exact B1536107
  · exact B1536111
  · exact B1536115
  · exact B1536119
  · exact B1536123
  · exact B1536127
  · exact B1536131
  · exact B1536135
  · exact B1536139
  · exact B1536143
  · exact B1536147
  · exact B1536151
  · exact B1536155
  · exact B1536159
  · exact B1536163
  · exact B1536167
  · exact B1536171
  · exact B1536175
  · exact B1536179
  · exact B1536183
  · exact B1536187
  · exact B1536191
  · exact B1536195
  · exact B1536199
  · exact B1536203
  · exact B1536207
  · exact B1536211
  · exact B1536215
  · exact B1536219
  · exact B1536223
  · exact B1536227
  · exact B1536231
  · exact B1536235
  · exact B1536239
  · exact B1536243
  · exact B1536247
  · exact B1536251
  · exact B1536255
  · exact B1536259
  · exact B1536263
  · exact B1536267
  · exact B1536271
  · exact B1536275
  · exact B1536279
  · exact B1536283
  · exact B1536287
  · exact B1536291
  · exact B1536295
  · exact B1536299
  · exact B1536303
  · exact B1536307
  · exact B1536311
  · exact B1536315
  · exact B1536319
  · exact B1536323
  · exact B1536327
  · exact B1536331
  · exact B1536335
  · exact B1536339
  · exact B1536343
  · exact B1536347
  · exact B1536351
  · exact B1536355
  · exact B1536359
  · exact B1536363
  · exact B1536367
  · exact B1536371
  · exact B1536375
  · exact B1536379
  · exact B1536383
  · exact B1536387
  · exact B1536391
  · exact B1536395
  · exact B1536399
  · exact B1536403
  · exact B1536407
  · exact B1536411
  · exact B1536415
  · exact B1536419
  · exact B1536423
  · exact B1536427
  · exact B1536431
  · exact B1536435
  · exact B1536439
  · exact B1536443
  · exact B1536447
  · exact B1536451
  · exact B1536455
  · exact B1536459
  · exact B1536463

theorem solution (m : ℕ) (hlo : 1534464 ≤ m) (hhi : m ≤ 1536464) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 383616 ≤ j := by omega
    have hj2 : j ≤ 384115 := by omega
    have hb : Blo 1534464 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
